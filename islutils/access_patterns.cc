#include "islutils/access_patterns.h"
#include "islutils/access.h"

namespace matchers {

std::vector<SingleInputDim>
SingleInputDim::candidates(isl::map singleOutDimMap, const SimpleAff &pattern) {
  std::vector<SingleInputDim> result = {};
  singleOutDimMap = singleOutDimMap.coalesce();
  if (!singleOutDimMap.is_single_valued()) {
    return {};
  }

  auto pma = isl::pw_multi_aff::from_map(singleOutDimMap);
  // Truly piece-wise access is not a single variable.
  if (pma.n_piece() != 1) {
    return {};
  }
  auto pa = pma.get_pw_aff(0);
  isl::aff a;
  pa.foreach_piece([&a](isl::set, isl::aff aff) {
    if (!a.is_null()) {
      ISLUTILS_DIE("unexpected second piece");
    }
    a = aff;
  });

  int dim = singleOutDimMap.dim(isl::dim::in);
  auto space = singleOutDimMap.get_space();
  auto lspace = isl::local_space(space.domain());
  for (int i = 0; i < dim; ++i) {
    auto candidateAff = isl::aff::var_on_domain(lspace, isl::dim::set, i);
    candidateAff = candidateAff.scale(pattern.coefficient_);
    candidateAff = candidateAff.add_constant_val(pattern.constant_);
    auto candidatePwAff =
        isl::pw_aff(candidateAff).intersect_domain(pa.domain());
    if (pa.is_equal(candidatePwAff)) {
      result.emplace_back(SingleInputDim{i});
    }
  }

  return result;
}

isl::map SingleInputDim::transformMap(isl::map map,
                                      const SingleInputDim &candidate,
                                      const SimpleAff &pattern) {
  auto space = map.get_space();
  auto lhs = isl::aff::var_on_domain(isl::local_space(space.domain()),
                                     isl::dim::set, candidate.inputDimPos_);
  lhs = lhs.scale(pattern.coefficient_).add_constant_val(pattern.constant_);
  auto rhs = isl::aff::var_on_domain(isl::local_space(space.range()),
                                     isl::dim::set, 0);
  using map_maker::operator==;
  return lhs == rhs;
}

///////////////////////////////

static isl::map mapToNext(isl::space space) {

  space = space.map_from_set();
  isl::map map = isl::map::universe(space);
  unsigned lastDimension = map.dim(isl::dim::in) - 1;

  // Set all but the last dimension to be equal for the input and output
  //
  //   input[i0, i1, ..., iX] -> output[o0, o1, ..., oX]
  //     : i0 = o0, i1 = o1, ..., i(X-1) = o(X-1)
  for (unsigned i = 0; i < lastDimension; ++i)
    map = map.equate(isl::dim::in, i, isl::dim::out, i);

  // Set the last dimension of the input to be strict smaller than the
  // last dimension of the output.
  //
  //   input[?,?,?,...,iX] -> output[?,?,?,...,oX] : iX < oX
  map = map.order_lt(isl::dim::in, lastDimension, isl::dim::out, lastDimension);
  return map;
}

static inline isl::set getZeroSet(isl::space space) {
  isl::set zeroSet = isl::set::universe(space);
  for (size_t i = 0; i < zeroSet.dim(isl::dim::set); ++i) {
    zeroSet = zeroSet.fix_si(isl::dim::set, i, 0);
  }
  return zeroSet;
}

std::vector<StrideCandidate>
StrideCandidate::candidates(isl::map singleOutDimMap,
                            const StridePattern &pattern) {
  auto map = mapToNext(singleOutDimMap.get_space().domain());
  auto delta =
      map.apply_domain(singleOutDimMap).apply_range(singleOutDimMap).deltas();
  // TODO: also match parametric strides

  if (delta.is_equal(getZeroSet(delta.get_space()))) {
    return {};
  }
  isl::aff strideAff =
      isl::aff(isl::local_space(delta.get_space()), pattern.stride);
  isl::val strideX = isl::manage(isl_set_get_stride(delta.get(), 0));
  isl::val stride = strideAff.get_constant_val();

  if (strideX.eq(stride)) {
    return {StrideCandidate{}};
  }

  return {};
}

///////////////////
// Utility functions for FixedOutDimPattern::transformMap

std::vector<isl::map> listOf1DMaps(isl::map map) {
  std::vector<isl::map> result;
  for (int dim = map.dim(isl::dim::out); dim > 0; --dim) {
    result.push_back(map.project_out(isl::dim::out, 1, dim - 1));
    map = map.project_out(isl::dim::out, 0, 1);
  }
  return result;
}

isl::space addEmptyRange(isl::space space) {
  return space.product(space.params().set_from_params()).unwrap();
}

isl::map mapFrom1DMaps(isl::space space, const std::vector<isl::map> &list) {
  auto zeroSpace = addEmptyRange(space.domain());
  auto result = isl::map::universe(zeroSpace);
  for (const auto &m : list) {
    result = result.flat_range_product(m);
  }
  result =
      result.set_tuple_id(isl::dim::out, space.get_tuple_id(isl::dim::out));
  return result;
}

} // namespace matchers
