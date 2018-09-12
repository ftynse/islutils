#include <isl/cpp.h>

#include <algorithm>
#include <functional>
#include <vector>

#include "islutils/locus.h"

namespace matchers {

template <typename Container> size_t containerSize(Container &&c) {
  return std::distance(c.cbegin(), c.cend());
}

// All placeholders should get different assignments, except those that belong
// to the same fold which should get equal assignments modulo matched map.
template <typename CandidatePayload, typename PatternPayload>
bool hasNoDuplicateAssignments(
    const std::vector<DimCandidate<CandidatePayload>> &combination,
    const PlaceholderSet<CandidatePayload, PatternPayload> &ps) {
  // Algorithmically not the most efficient way of finding duplicates, but
  // removes the need to include hash-tables and/or perform additional
  // allocations.
  size_t size = combination.size();
  if (containerSize(ps) != ps.placeholderFolds_.size()) {
    ISLUTILS_DIE("placeholder folds are not properly set up");
  }

  for (size_t i = 0; i < size; ++i) {
    for (size_t j = i + 1; j < size; ++j) {
      if (ps.placeholderFolds_[i] == ps.placeholderFolds_[j]) {
        if (!combination.at(i).isEqualModuloMap(combination.at(j))) {
          return false;
        } else {
          continue;
        }
      }
      if (combination.at(i).isEqualModuloMap(combination.at(j))) {
        return false;
      }
    }
  }
  return true;
}

// All placeholders in a group are either not yet matched, or matched the same
// map.  A map matched in the group is not matched in any previous group.
template <typename CandidatePayload, typename PatternPayload>
bool groupsAreProperlyFormed(
    const std::vector<DimCandidate<CandidatePayload>> &combination,
    const PlaceholderSet<CandidatePayload, PatternPayload> &ps) {
  std::vector<isl::space> previouslyMatchedSpaces;
  for (const auto &group : ps.placeholderGroups_) {
    isl::space matchedSpace;
    // Ignore parts that are not yet matched.
    for (size_t pos : group) {
      if (pos >= combination.size()) {
        continue;
      }
      auto candidateSpace = combination.at(pos).candidateMapSpace_;
      if (matchedSpace) { // A group has already matched a map.
        // If matched a different map, groups are not a match.
        if (!matchedSpace.is_equal(candidateSpace)) {
          return false;
        }
      } else { // First time a map is matched in the group.
        matchedSpace = candidateSpace;
        auto it = std::find(previouslyMatchedSpaces.begin(),
                            previouslyMatchedSpaces.end(), matchedSpace);
        // If the same map as one of the previously considered groups, groups
        // are not a match.
        if (it != previouslyMatchedSpaces.end()) {
          return false;
        }
        previouslyMatchedSpaces.push_back(matchedSpace);
      }
    }
  }
  return true;
}

template <typename CandidatePayload, typename PatternPayload>
Match<CandidatePayload, PatternPayload>::Match(
    const PlaceholderSet<CandidatePayload, PatternPayload> &ps,
    const std::vector<DimCandidate<CandidatePayload>> &combination) {
  if (containerSize(ps) != combination.size()) {
    ISLUTILS_DIE("expected the same number of placeholders and candidates");
  }

  size_t idx = 0;
  for (const auto &candidate : combination) {
    placeholderValues_.emplace_back(ps.placeholders_[idx++].id_, candidate);
  }
}

template <typename CandidatePayload, typename PatternPayload, typename FilterTy>
void recursivelyCheckCombinations(
    const PlaceholderSet<CandidatePayload, PatternPayload> &ps,
    std::vector<DimCandidate<CandidatePayload>> partialCombination,
    FilterTy filter,
    Matches<CandidatePayload, PatternPayload> &suitableCandidates) {
  static_assert(
      std::is_same<
          decltype(filter(
              std::declval<std::vector<DimCandidate<CandidatePayload>>>())),
          bool>::value,
      "unexpected type of the callable filter");

  if (!filter(partialCombination)) {
    return;
  }

  // At this point, the partialCombination is full and has been checked to pass
  // the filter.
  if (partialCombination.size() == containerSize(ps)) {
    suitableCandidates.emplace_back(ps, partialCombination);
    return;
  }

  auto pos = partialCombination.size();
  for (const auto &candidate : ps.placeholders_[pos].candidates_) {
    partialCombination.push_back(candidate);
    recursivelyCheckCombinations(ps, partialCombination, filter,
                                 suitableCandidates);
    partialCombination.pop_back();
  }
}

template <typename CandidatePayload, typename PatternPayload, typename FilterTy>
Matches<CandidatePayload, PatternPayload>
suitableCombinations(const PlaceholderSet<CandidatePayload, PatternPayload> &ps,
                     FilterTy filter) {
  Matches<CandidatePayload, PatternPayload> result;
  recursivelyCheckCombinations(ps, {}, filter, result);
  return result;
}

template <typename CandidatePayload, typename PatternPayload>
Matches<CandidatePayload, PatternPayload>
match(isl::union_map access,
      PlaceholderSet<CandidatePayload, PatternPayload> ps) {
  std::vector<isl::map> accesses;
  access.foreach_map([&accesses](isl::map m) { accesses.push_back(m); });

  // If there is a lot of placeholders with the same coefficient, we want
  // to group placeholders by coefficient and only call the
  // aff-matching computation once per coefficient.  Punting for now.

  // Stage 1: fill in the candidate lists for all placeholders.
  for (auto &ph : ps) {
    for (auto acc : accesses) {
      for (auto &&c : CandidatePayload::candidates(acc, ph.pattern_)) {
        ph.candidates_.emplace_back(c, acc.get_space());
      }
    }
    // Early exit if one of the placeholders has no candidates.
    if (ph.candidates_.empty()) {
      return {};
    }
  }

  // Stage 2: generate all combinations of values replacing the placeholders
  // while filtering incompatible ones immediately.
  // TODO: customize the filter for acceptable combinations.
  // Note that the filter must work on incomplete candidates for the
  // branch-and-cut to work.  It can return "true" for incomplete candidates
  // and only actually check complete candidates, but would require enumerating
  // them all.
  // Note also that the filter might be doing duplicate work: in the
  // hasNoDuplicateAssignments example, there is not need to check all pairs in
  // the N-element list if we know that elements of (N-1) array are unique.
  // This algorithmic optimization requires some API changes and is left for
  // future work.
  return suitableCombinations<CandidatePayload, PatternPayload>(
      ps, [ps](const std::vector<DimCandidate<CandidatePayload>> &candidate) {
        return hasNoDuplicateAssignments(candidate, ps) &&
               groupsAreProperlyFormed(candidate, ps);
      });
}

template <typename CandidatePayload, typename PatternPayload, typename... Args>
isl::map transformOneMap(
    isl::map map, const Match<CandidatePayload, PatternPayload> &oneMatch,
    Replacement<CandidatePayload, PatternPayload> arg, Args... args) {
  static_assert(
      std::is_same<
          typename std::common_type<
              Replacement<CandidatePayload, PatternPayload>, Args...>::type,
          Replacement<CandidatePayload, PatternPayload>>::value,
      "");

  isl::map result;
  for (const auto &rep : {arg, args...}) {
    // separability of matches is important!
    // if we match here something that we would not have matched with the whole
    // set, it's bad!  But here we know that the map has already matched with
    // one of the groups in the set, we just don't know which one.  If it
    // matches two groups, this means the transformation would happen twice,
    // which we expicitly disallow.
    if (match(isl::union_map(map), allOf(rep.pattern)).empty()) {
      continue;
    }
    if (!result.is_null()) {
      ISLUTILS_DIE("one relation matched multiple patterns\n"
                   "the transformation is undefined");
    }
    // Actual transformation.
    result = map;
    for (const auto &plh : rep.replacement) {
      result = CandidatePayload::transformMap(result, oneMatch[plh].payload(),
                                              plh.pattern_);
    }
  }
  return result;
}

template <typename CandidatePayload, typename PatternPayload, typename... Args>
isl::union_map findAndReplace(isl::union_map umap,
                              Replacement<CandidatePayload, PatternPayload> arg,
                              Args... args) {
  static_assert(
      std::is_same<
          typename std::common_type<
              Replacement<CandidatePayload, PatternPayload>, Args...>::type,
          Replacement<CandidatePayload, PatternPayload>>::value,
      "");

  // make a vector of maps
  // for each match,
  //   find all corresponding maps,
  //     if not found, the map was deleted already meaning there was an attempt
  //     of double transformation
  //   remove them from vector,
  //   transform them and
  //   add them to the resulting vector
  // finally, copy all the remaining original maps as is into result

  std::vector<isl::map> originalMaps, transformedMaps;
  umap.foreach_map([&originalMaps](isl::map m) { originalMaps.push_back(m); });

  auto getPattern =
      [](const Replacement<CandidatePayload, PatternPayload> &replacement) {
        return replacement.pattern;
      };

  auto ps = allOf(getPattern(arg), getPattern(args)...);
  auto matches = match(umap, ps);

  for (const auto &m : matches) {
    std::vector<isl::map> toTransform;
    for (const auto &plh : ps.placeholders_) {
      auto spaces = m[plh].candidateSpaces();
      for (auto candidate : spaces) {
        auto found = std::find_if(toTransform.begin(), toTransform.end(),
                                  [candidate](isl::map map) {
                                    return map.get_space().is_equal(candidate);
                                  });
        if (found != toTransform.end()) {
          continue;
        }
        toTransform.push_back(umap.extract_map(candidate));
      }
    }

    for (const auto &candidate : toTransform) {
      auto found = std::find_if(
          originalMaps.begin(), originalMaps.end(),
          [candidate](isl::map map) { return map.is_equal(candidate); });
      if (found == originalMaps.end()) {
        ISLUTILS_DIE("could not find the matched map\n"
                     "this typically means a map was matched more than once\n"
                     "in which case the transformation is undefined");
        continue;
      }
      originalMaps.erase(found);

      auto r = transformOneMap<CandidatePayload, PatternPayload>(candidate, m,
                                                                 arg, args...);
      transformedMaps.push_back(r);
    }
  }

  for (const auto &map : originalMaps) {
    transformedMaps.push_back(map);
  }

  if (transformedMaps.empty()) {
    return isl::union_map::empty(umap.get_space());
  }
  auto result = isl::union_map(transformedMaps.front());
  for (const auto &map : transformedMaps) {
    result = result.unite(isl::union_map(map));
  }
  return result;
}

template <typename TargetPatternPayload, typename CandidatePayload,
          typename SourcePatternPayload>
Placeholder<CandidatePayload, TargetPatternPayload>
pattern_cast(Placeholder<CandidatePayload, SourcePatternPayload> placeholder) {
  return Placeholder<CandidatePayload, TargetPatternPayload>(
      static_cast<TargetPatternPayload>(placeholder.pattern_), placeholder.id_);
}

/// Counter used to create per-thread unique-ish placeholder ids for the
/// purpose of folding.
template <typename CandidatePayload, typename PatternPayload>
thread_local size_t Placeholder<CandidatePayload, PatternPayload>::nextId_ = 0;

/// Build an object used to match all of the access patterns provided as
/// arguments. Individual patterns can be constructed by calling "access(...)".
template <typename CandidatePayload, typename PatternPayload, typename... Args>
PlaceholderSet<CandidatePayload, PatternPayload>
allOf(PlaceholderList<CandidatePayload, PatternPayload> arg, Args... args) {
  static_assert(all_are<PlaceholderList<CandidatePayload, PatternPayload>,
                        PlaceholderList<CandidatePayload, PatternPayload>,
                        Args...>::value,
                "can only make PlaceholderSet from PlaceholderLists "
                "with the same payload types");

  std::vector<PlaceholderList<CandidatePayload, PatternPayload>>
      placeholderLists = {arg, args...};
  std::vector<std::pair<size_t, size_t>> knownIds;
  PlaceholderSet<CandidatePayload, PatternPayload> ps;
  for (const auto &pl : placeholderLists) {
    if (pl.empty()) {
      continue;
    }

    size_t index = containerSize(ps);
    ps.placeholderGroups_.emplace_back();
    for (const auto &p : pl) {
      ps.placeholders_.push_back(p);
      ps.placeholderGroups_.back().push_back(index);
      auto namePos = std::find_if(knownIds.begin(), knownIds.end(),
                                  [p](const std::pair<size_t, size_t> &pair) {
                                    return pair.first == p.id_;
                                  });
      if (namePos == knownIds.end()) {
        knownIds.emplace_back(p.id_, index);
        ps.placeholderFolds_.emplace_back(index);
      } else {
        ps.placeholderFolds_.emplace_back(namePos->second);
      }
      ++index;
    }
  }

  return ps;
}

template <typename CandidatePayload, typename PatternPayload>
template <typename PPayload>
MatchCandidates<CandidatePayload> Match<CandidatePayload, PatternPayload>::
operator[](const Placeholder<CandidatePayload, PPayload> &pl) const {
  // If pattern_cast from PatterPayload to PPayload cannot be instantiated,
  // Placeholder<CandidatePayload, PPayload> cannot be a valid key to lookup
  // match results.
  static_assert(
      std::is_same<
          decltype(pattern_cast<PPayload>(
              std::declval<Placeholder<CandidatePayload, PatternPayload>>())),
          Placeholder<CandidatePayload, PPayload>>::value,
      "incompatible pattern types");

  auto result = MatchCandidates<CandidatePayload>();

  for (const auto &kvp : placeholderValues_) {
    if (kvp.first == pl.id_) {
      if (result.candidateSpaces_.empty()) {
        result.payload_ = kvp.second.payload_;
      } else if (!(result.payload_ == kvp.second.payload_)) {
        ISLUTILS_DIE("different payloads for the same placeholder");
      }
      if (std::find(
              result.candidateSpaces_.begin(), result.candidateSpaces_.end(),
              kvp.second.candidateMapSpace_) != result.candidateSpaces_.end()) {
        continue;
      }
      result.candidateSpaces_.push_back(kvp.second.candidateMapSpace_);
    }
  }

  if (result.candidateSpaces_.empty()) {
    ISLUTILS_DIE("no match for the placeholder although matches found");
  }
  return result;
}

} // namespace matchers
