#include "islutils/matchers.h"

#include <iostream>
using namespace std;

namespace matchers {

/*
void RelationMatcher::printMatcher(raw_ostream &OS,
  				   int indent) const {
  switch (type_) {
    case RelationKind::read:
      OS.indent(indent) << "Read access\n";
      break;
    case RelationKind::write:
      OS.indent(indent) << "Write access\n";
      break;
    case RelationKind::readOrWrite:
      OS.indent(indent) << "ReadOrWrite\n";
      break;
    default:
      OS.indent(indent) << "ND\n";
    }

  int n_children_ = indexes_.size();
  for(int i=0; i < n_children_; ++i) {
    OS.indent(indent) << indexes_[i] << "\n";
  }

  int n_dims_ = setDim_.size();
  OS.indent(indent) << "Number of dims: =" << n_dims_ << "\n";

  for(size_t i=0; i<n_dims_; ++i) {
    auto payload = setDim_[i];
    for(size_t j=0; j<payload.size(); ++j) {
      OS.indent(indent +2) << payload[j] << "\n";
    }
  }
}
*/

void RelationMatcher::setDims(constraints::MultipleConstraints &mc) {
  std::vector<isl::pw_aff> tmp;
  for(std::size_t i=0; i<indexes_.size(); ++i) {
    for(std::size_t j=0; j<mc.size(); ++j) {
      if(indexes_[i] == std::get<0>(mc[j])) {
        tmp.push_back(std::get<1>(mc[j]));
      }
    }
    setDim_.push_back(tmp);
    tmp.erase(tmp.begin(), tmp.end());
  }
}


// returns the number of literals assigned to the matcher.
unsigned RelationMatcher::getIndexesSize() const {
  return indexes_.size();
}

// returns literal at position i
char RelationMatcher::getIndex(unsigned i) const {
  return indexes_[i];
}

// is a write matcher?
bool RelationMatcher::isWrite() const {
  if((type_ == RelationKind::write) ||
     (type_ == RelationKind::readAndWrite))
    return true;
  else return false;
}

// is a read matcher?
bool RelationMatcher::isRead() const {
  if((type_ == RelationKind::read) ||
     (type_ == RelationKind::readAndWrite))
    return true;
  else return false;
}

// return matcher type
// 0 for read, 1 for write and 2 readandWrite
int RelationMatcher::getType() const {
  if(type_ == RelationKind::read)
    return 0;
  if(type_ == RelationKind::write)
    return 1;
  else return 2;
}

// return fixed dim at index i
std::vector<isl::pw_aff> RelationMatcher::getDims(int i) const {
  return setDim_[i];
}

// check if the dimension statisfies the matcer.
static bool checkDimension(isl::pw_aff &pw, std::vector<isl::pw_aff> &dims) {
  bool result = false;
  for(size_t i = 0; i<dims.size(); ++i) {
    if(dims[i].is_equal(pw))
      result = true;
  }
  return result;
}
// return the accesses matched
std::vector<isl::map> RelationMatcher::getAccesses(isl::union_map &accesses) {
  std::vector<isl::map> res;
  accesses.foreach_map([&](isl::map access) -> isl_stat {
    isl::space Space = access.get_space();
    
    if(Space.dim(isl::dim::out) != indexes_.size())
      return isl_stat_ok;

    isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
    bool equalDims = true;

    for(size_t i=0; i<setDim_.size(); ++i) {
      isl::pw_aff PwAff = MultiAff.get_pw_aff(i);
      bool check = checkDimension(PwAff, setDim_[i]);
      equalDims = equalDims && check;
    }

    if(equalDims) {
      res.push_back(access);
    }
    
    return isl_stat_ok;
    
  });
  return res;
}

bool ScheduleNodeMatcher::isMatching(const ScheduleNodeMatcher &matcher,
                                     isl::schedule_node node) {
  if (!node.get()) {
    return false;
  }

  if (matcher.current_ == ScheduleNodeType::Any) {
    matcher.capture_ = node;
    return true;
  }

  if (toIslType(matcher.current_) != isl_schedule_node_get_type(node.get())) {
    return false;
  }

  if (matcher.nodeCallback_ && !matcher.nodeCallback_(node)) {
    return false;
  }

  size_t nChildren =
      static_cast<size_t>(isl_schedule_node_n_children(node.get()));
  if (matcher.children_.size() != nChildren) {
    return false;
  }

  for (size_t i = 0; i < nChildren; ++i) {
    if (!isMatching(matcher.children_.at(i), node.child(i))) {
      return false;
    }
  }
  matcher.capture_ = node;
  return true;
}

static bool hasPreviousSiblingImpl(isl::schedule_node node,
                                   const ScheduleNodeMatcher &siblingMatcher) {
  while (isl_schedule_node_has_previous_sibling(node.get()) == isl_bool_true) {
    node = isl::manage(isl_schedule_node_previous_sibling(node.release()));
    if (ScheduleNodeMatcher::isMatching(siblingMatcher, node)) {
      return true;
    }
  }
  return false;
}

static bool hasNextSiblingImpl(isl::schedule_node node,
                               const ScheduleNodeMatcher &siblingMatcher) {
  while (isl_schedule_node_has_next_sibling(node.get()) == isl_bool_true) {
    node = isl::manage(isl_schedule_node_next_sibling(node.release()));
    if (ScheduleNodeMatcher::isMatching(siblingMatcher, node)) {
      return true;
    }
  }
  return false;
}

std::function<bool(isl::schedule_node)>
hasPreviousSibling(const ScheduleNodeMatcher &siblingMatcher) {
  return std::bind(hasPreviousSiblingImpl, std::placeholders::_1,
                   siblingMatcher);
}

std::function<bool(isl::schedule_node)>
hasNextSibling(const ScheduleNodeMatcher &siblingMatcher) {
  return std::bind(hasNextSiblingImpl, std::placeholders::_1, siblingMatcher);
}

std::function<bool(isl::schedule_node)>
hasSibling(const ScheduleNodeMatcher &siblingMatcher) {
  return [siblingMatcher](isl::schedule_node node) {
    return hasPreviousSiblingImpl(node, siblingMatcher) ||
           hasNextSiblingImpl(node, siblingMatcher);
  };
}

std::function<bool(isl::schedule_node)>
hasDescendant(const ScheduleNodeMatcher &descendantMatcher) {
  isl::schedule_node n;
  return [descendantMatcher](isl::schedule_node node) {
    // Cannot use capturing lambdas as C function pointers.
    struct Data {
      bool found;
      const ScheduleNodeMatcher &descendantMatcher;
    };
    Data data{false, descendantMatcher};

    auto r = isl_schedule_node_foreach_descendant_top_down(
        node.get(),
        [](__isl_keep isl_schedule_node *cn, void *user) -> isl_bool {
          auto data = static_cast<Data *>(user);
          if (data->found) {
            return isl_bool_false;
          }

          auto n = isl::manage_copy(cn);
          data->found =
              ScheduleNodeMatcher::isMatching(data->descendantMatcher, n);
          return data->found ? isl_bool_false : isl_bool_true;
        },
        &data);
    return r == isl_stat_ok && data.found;
  };
}

} // namespace matchers


namespace constraints {

// check if two single constraint are equal.
bool isEqual(singleConstraint &a, singleConstraint &b) {
  if((std::get<0>(a) == std::get<0>(b)) &&
     (std::get<1>(a).is_equal(std::get<1>(a)))) 
    return true;
  else return false;
}

// remove possible dumpicates
void removeDuplicate(MultipleConstraints &constraints) {
  for(unsigned i=0; i<constraints.size(); ++i) {
    for(unsigned j=i+1; j<constraints.size(); ++j) {
      if(isEqual(constraints[i],constraints[j])) {
        constraints.erase(constraints.begin()+j);
      }
    }
  }
}

// create a new constraints list.
void createNewConstraintsList(
		int i,
		int j,
		const ConstraintsList &listOne,
		const ConstraintsList &listTwo,
  		ConstraintsList &res) {
  MultipleConstraints newConstraints;
  
  for(int ii=i; ii<listOne.dimsInvolved+i; ++ii) {
    auto t = std::make_tuple(std::get<0>(listOne.constraints[ii]),
			     std::get<1>(listOne.constraints[ii]));
    newConstraints.push_back(t);
  }

  for(int jj=j; jj<listTwo.dimsInvolved+j; ++jj) {
    auto t = std::make_tuple(std::get<0>(listTwo.constraints[jj]),
			     std::get<1>(listTwo.constraints[jj]));
    newConstraints.push_back(t);
  }

  // remove possible duplicates.
  removeDuplicate(newConstraints);

  res.constraints = newConstraints;
  res.dimsInvolved = newConstraints.size();
}

// given two constraints lists compare them and
// return a new constraint list. 
// for now we just compare all the possible tuples
// and check if they do not conflict.
// For example:
// 1. (B, i1) and (C, i1) [this should be rejected since i1 is assigned both to B and C]
// 2. (A, i0) and (A, i2) [this should be rejected since A is assigned both to i0 and i2]
ConstraintsList compareLists(
		ConstraintsList &listOne,
  		ConstraintsList &listTwo) {
  ConstraintsList res;
  int sizeListOne = listOne.constraints.size();
  int sizeListTwo = listTwo.constraints.size();
  for(int i=0; i<sizeListOne; i+=listOne.dimsInvolved) {
    for(int j=0; j<sizeListTwo; j+=listTwo.dimsInvolved) {
    bool isPossible = true;
      for(int ii=i; ii<i+listOne.dimsInvolved; ++ii) {
        for(int jj=j; jj<j+listTwo.dimsInvolved; ++jj) {
          if((std::get<0>(listOne.constraints[ii]) != std::get<0>(listTwo.constraints[jj]) &&
             (std::get<1>(listOne.constraints[ii]).is_equal(std::get<1>(listTwo.constraints[jj])) == 1)) ||
             (std::get<0>(listOne.constraints[ii]) == std::get<0>(listTwo.constraints[jj]) &&
 	     (std::get<1>(listOne.constraints[ii]).is_equal(std::get<1>(listTwo.constraints[jj])) == 0))) {
            isPossible = false;
          }
          else {
          }
        }
      }
      if(isPossible) {
        createNewConstraintsList(i,j,listOne,listTwo,res);
      }
    }
  }
  return res;
}

// create the constraints list for reads.
ConstraintsList buildMatcherConstraintsReads(
			matchers::RelationMatcher &matcher,
			isl::union_map &accessesReads) {
  ConstraintsList list;
  accessesReads.foreach_map([&list, matcher](isl::map access) -> isl_stat {
    isl::space Space = access.get_space();
    if(Space.dim(isl::dim::out) == matcher.getIndexesSize()) {
      isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
      for(unsigned u=0; u<access.dim(isl::dim::out); ++u) {
        isl::pw_aff PwAff = MultiAff.get_pw_aff(u);
        auto t = std::make_tuple(matcher.getIndex(u), PwAff);
	list.constraints.push_back(t);
      }
    }
    return isl_stat_ok;
  });
  list.dimsInvolved = matcher.getIndexesSize();
  return list;
}

// create the constraints for writes.
ConstraintsList buildMatcherConstraintsWrites(
			matchers::RelationMatcher &matcher,
			isl::union_map &accessesWrites) {
  ConstraintsList list;
  accessesWrites.foreach_map([&list, matcher](isl::map access) -> isl_stat {
    isl::space Space = access.get_space();
    if(Space.dim(isl::dim::out) == matcher.getIndexesSize()) {
      isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
      for(unsigned u=0; u<access.dim(isl::dim::out); ++u) {
        isl::pw_aff PwAff = MultiAff.get_pw_aff(u);
        auto t = std::make_tuple(matcher.getIndex(u), PwAff);
        list.constraints.push_back(t);
      }
    }
    return isl_stat_ok;
  });
  list.dimsInvolved = matcher.getIndexesSize();
  return list;
}
 
} // namespace constraints

