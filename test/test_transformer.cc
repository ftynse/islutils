#include <islutils/access_patterns.h>
#include <islutils/aff_op.h>
#include <islutils/builders.h>
#include <islutils/ctx.h>
#include <islutils/locus.h>
#include <islutils/matchers.h>
#include <islutils/pet_wrapper.h>

#include "gtest/gtest.h"

using util::ScopedCtx;

TEST(Transformer, Capture) {
  isl::schedule_node bandNode, filterNode1, filterNode2, filterSubtree;
  auto ctx = isl::ctx(isl_ctx_alloc());

  auto matcher = [&]() {
    using namespace matchers;
    // clang-format off
    return
      band(bandNode,
        sequence(
          filter(filterNode1,
            leaf()),
          filter(filterNode2,
            anyTree(filterSubtree))));
    // clang-format on
  }();

  auto node = [ctx]() {
    using namespace builders;
    auto iterationDomain = isl::union_set(
        ctx, "{S1[i,j]: 0 <= i,j < 10; S2[i,j,k]: 0 <= i,j,k < 42}");
    auto sched =
        isl::multi_union_pw_aff(ctx, "[{S1[i,j]->[(i)]; S2[i,j]->[(i)]}, "
                                     "{S1[i,j]->[(j)]; S2[i,j]->[(j)]}]");
    auto filterS1 = isl::union_set(ctx, "{S1[i,j]}");
    auto filterS2 = isl::union_set(ctx, "{S2[i,j]}");
    auto innerSched = isl::multi_union_pw_aff(ctx, "[{S2[i,j,k]->[(k)]}]");

    // clang-format off
    auto builder =
      domain(iterationDomain,
        band(sched,
          sequence(
            filter(filterS1),
            filter(filterS2,
              band(innerSched)))));
    // clang-format on

    return builder.build();
  }();

  // Let's find a node.
  // We don't have matcher-based lookups, so lets just use node.child(0) for
  // now.
  ASSERT_TRUE(
      matchers::ScheduleNodeMatcher::isMatching(matcher, node.child(0)));
  node.dump();

  // Let's transform!
  auto transformedBuilder = [&]() {
    auto filter1 = filterNode1.filter_get_filter();
    auto filter2 = filterNode2.filter_get_filter();
    auto schedule = bandNode.band_get_partial_schedule();

    using namespace builders;
    // clang-format off
    return
      sequence(
        filter(filter1,
          band(schedule.intersect_domain(filter1))),
        filter(filter2,
          band(schedule.intersect_domain(filter2),
            subtree(filterSubtree))));
    // clang-format on
  }();
  node = node.child(0);
  node = node.cut();
  node = transformedBuilder.insertAt(node);
  node = node.parent();

  node.dump();
}

struct Schedule : public ::testing::Test {
  virtual void SetUp() override {
    scop_ = pet::Scop::parseFile(ctx_, "inputs/nested.c").getScop();
  }

  isl::schedule_node topmostBand() {
    return scop_.schedule.get_root().child(0);
  }

  void expectSingleBand(isl::schedule_node node) {
    using namespace matchers;
    EXPECT_TRUE(ScheduleNodeMatcher::isMatching(band(leaf()), node));
  }

  Scop scop_;
  ScopedCtx ctx_ = ScopedCtx(pet::allocCtx());
};

TEST_F(Schedule, MergeBandsCallLambda) {
  isl::schedule_node parent, child, grandchild;
  auto matcher = [&]() {
    using namespace matchers;
    // clang-format off
    return band(parent,
             band(child,
               anyTree(grandchild)));
    // clang-format on
  }();

  // Capturing the matched nodes by-reference since they don't have any values
  // until the matcher was called on a tree.
  // Note that we don't call the lambda yet.
  auto merger = [&]() {
    using namespace builders;
    auto schedule = parent.band_get_partial_schedule().flat_range_product(
        child.band_get_partial_schedule());
    // clang-format off
    return band(schedule,
             subtree(grandchild));
    // clang-format on
  };

  // Keep transforming the tree while possible.
  // Call the builder lambda each time to construct a new builder based on the
  // currently matched nodes (captured by-reference above).
  auto node = topmostBand();
  while (matchers::ScheduleNodeMatcher::isMatching(matcher, node)) {
    node = node.cut();
    node = merger().insertAt(node);
  }

  expectSingleBand(node);
}

TEST_F(Schedule, MergeBandsDeclarative) {
  isl::schedule_node parent, child, grandchild;
  // Note that the lambda is called immediately and is only necessary for
  // compound initialization (matchers are not copyable).
  auto matcher = [&]() {
    using namespace matchers;
    // clang-format off
    return band(parent,
             band(child,
               anyTree(grandchild)));
    // clang-format on
  }();

  // Use lambdas to lazily initialize the builder with the nodes and values yet
  // to be captured by the matcher.
  auto declarativeMerger = builders::ScheduleNodeBuilder();
  {
    using namespace builders;
    auto schedule = [&]() {
      return parent.band_get_partial_schedule().flat_range_product(
          child.band_get_partial_schedule());
    };
    auto st = [&]() { return subtreeBuilder(grandchild); };
    declarativeMerger = band(schedule, subtree(st));
  }

  // Keep transforming the tree while possible.
  auto node = topmostBand();
  while (matchers::ScheduleNodeMatcher::isMatching(matcher, node)) {
    node = node.cut();
    node = declarativeMerger.insertAt(node);
  }

  expectSingleBand(node);
}

static isl::union_map computeAllDependences(const Scop &scop) {
  // For the simplest possible dependence analysis, get rid of reference tags.
  auto reads = scop.reads.domain_factor_domain();
  auto mayWrites = scop.mayWrites.domain_factor_domain();
  auto mustWrites = scop.mustWrites.domain_factor_domain();

  // False dependences (output and anti).
  // Sinks are writes, sources are reads and writes.
  auto falseDepsFlow = isl::union_access_info(mayWrites.unite(mustWrites))
                           .set_may_source(mayWrites.unite(reads))
                           .set_must_source(mustWrites)
                           .set_schedule(scop.schedule)
                           .compute_flow();

  isl::union_map falseDeps = falseDepsFlow.get_may_dependence();

  // Flow dependences.
  // Sinks are reads and sources are writes.
  auto flowDepsFlow = isl::union_access_info(reads)
                          .set_may_source(mayWrites)
                          .set_must_source(mustWrites)
                          .set_schedule(scop.schedule)
                          .compute_flow();

  isl::union_map flowDeps = flowDepsFlow.get_may_dependence();

  return flowDeps.unite(falseDeps);
}

// The partial schedule is only defined for those domain elements that passed
// through filters until "node".  Therefore, there is no need to explicitly
// introduce auxiliary dimensions for the filters.
static inline isl::union_map
filterOutCarriedDependences(isl::union_map dependences,
                            isl::schedule_node node) {
  auto partialSchedule = node.get_prefix_schedule_multi_union_pw_aff();
  return dependences.eq_at(partialSchedule);
}

static bool canMerge(isl::schedule_node parentBand,
                     isl::union_map dependences) {
  // Permutability condition: there are no negative distances along the
  // dimensions that are not carried until now by any of dimensions.
  auto t1 = parentBand.band_get_partial_schedule();
  auto t2 = parentBand.child(0).band_get_partial_schedule();
  auto schedule = isl::union_map::from(t1.flat_range_product(t2));
  auto scheduleSpace = isl::set(schedule.range()).get_space();
  auto positiveOrthant =
      isl::set(isl::basic_set::positive_orthant(scheduleSpace));
  dependences = filterOutCarriedDependences(dependences, parentBand);
  return dependences.apply_domain(schedule)
      .apply_range(schedule)
      .deltas()
      .is_subset(positiveOrthant);
}

static inline isl::schedule_node
rebuild(isl::schedule_node node,
        const builders::ScheduleNodeBuilder &replacement) {
  // this may not be always legal...
  node = node.cut();
  node = replacement.insertAt(node);
  return node;
}

isl::schedule_node
replaceOnce(isl::schedule_node node,
            const matchers::ScheduleNodeMatcher &pattern,
            const builders::ScheduleNodeBuilder &replacement) {
  if (matchers::ScheduleNodeMatcher::isMatching(pattern, node)) {
    node = rebuild(node, replacement);
  }
  return node;
}

isl::schedule_node
replaceRepeatedly(isl::schedule_node node,
                  const matchers::ScheduleNodeMatcher &pattern,
                  const builders::ScheduleNodeBuilder &replacement) {
  while (matchers::ScheduleNodeMatcher::isMatching(pattern, node)) {
    node = rebuild(node, replacement);
  }
  return node;
}

isl::schedule_node
replaceDFSPreorderRepeatedly(isl::schedule_node node,
                             const matchers::ScheduleNodeMatcher &pattern,
                             const builders::ScheduleNodeBuilder &replacement) {
  node = replaceRepeatedly(node, pattern, replacement);
  for (int i = 0; i < node.n_children(); ++i) {
    node = replaceDFSPreorderRepeatedly(node.child(i), pattern, replacement)
               .parent();
  }
  return node;
}

isl::schedule_node
replaceDFSPreorderOnce(isl::schedule_node node,
                       const matchers::ScheduleNodeMatcher &pattern,
                       const builders::ScheduleNodeBuilder &replacement) {
  node = replaceOnce(node, pattern, replacement);
  for (int i = 0; i < node.n_children(); ++i) {
    node = replaceDFSPreorderOnce(node.child(i), pattern, replacement).parent();
  }
  return node;
}

isl::schedule_node
replaceDFSPostorderOnce(isl::schedule_node node,
                        const matchers::ScheduleNodeMatcher &pattern,
                        const builders::ScheduleNodeBuilder &replacement) {
  for (int i = 0; i < node.n_children(); ++i) {
    node =
        replaceDFSPostorderOnce(node.child(i), pattern, replacement).parent();
  }
  return replaceOnce(node, pattern, replacement);
}

isl::schedule_node mergeIfTilable(isl::schedule_node node,
                                  isl::union_map dependences) {
  isl::schedule_node parent, child, grandchild;

  auto canMergeCaptureChild = [&child, dependences](isl::schedule_node node) {
    if (canMerge(node.parent(), dependences)) {
      child = node;
      return true;
    }
    return false;
  };

  auto matcher = [&]() {
    using namespace matchers;
    // clang-format off
    return band(parent,
             band(canMergeCaptureChild,
               anyTree(grandchild)));
    // clang-format on
  }();

  // Use lambdas to lazily initialize the builder with the nodes and values yet
  // to be captured by the matcher.
  auto declarativeMerger = builders::ScheduleNodeBuilder();
  {
    using namespace builders;
    auto schedule = [&]() {
      auto descr =
          BandDescriptor(parent.band_get_partial_schedule().flat_range_product(
              child.band_get_partial_schedule()));
      descr.permutable = 1;
      return descr;
    };
    auto st = [&]() { return subtreeBuilder(grandchild); };
    declarativeMerger = band(schedule, subtree(st));
  }

  return replaceDFSPreorderRepeatedly(node, matcher, declarativeMerger);
}

TEST_F(Schedule, MergeBandsIfTilable) {
  auto dependences = computeAllDependences(scop_);
  auto node = mergeIfTilable(topmostBand(), dependences);
  expectSingleBand(node);
  EXPECT_EQ(isl_schedule_node_band_get_permutable(node.get()), isl_bool_true);
}

static std::vector<bool> detectCoincidence(isl::schedule_node band,
                                           isl::union_map dependences) {
  std::vector<bool> result;
  auto schedule = band.band_get_partial_schedule();
  int dim = schedule.dim(isl::dim::set);
  if (dependences.is_empty()) {
    result.resize(dim, true);
    return result;
  }
  for (int i = 0; i < dim; ++i) {
    auto upa = schedule.get_union_pw_aff(i);
    auto partialSchedule = isl::union_map::from_union_pw_aff(upa);
    auto deltas = isl::set(dependences.apply_domain(partialSchedule)
                               .apply_range(partialSchedule)
                               .deltas());
    auto zeroSet = [&]() {
      auto lspace = isl::local_space(deltas.get_space());
      auto aff = isl::aff::var_on_domain(lspace, isl::dim::set, 0);
      auto zeroAff = isl::aff(lspace);
      using set_maker::operator==;
      return isl::set(aff == zeroAff);
    }();
    result.push_back(deltas.is_subset(zeroSet));
  }
  return result;
}

isl::schedule_node markCoincident(isl::schedule_node root,
                                  isl::union_map dependences) {
  isl::schedule_node node, child;
  auto matcher = [&]() {
    using namespace matchers;
    return band(node, anyTree(child));
  }();

  auto marker = [&]() {
    auto descr = builders::BandDescriptor(node.band_get_partial_schedule());
    descr.coincident = detectCoincidence(node, dependences);
    return descr;
  };

  auto builder = [&]() {
    using namespace builders;
    return band(marker, subtree(child));
  }();

  return replaceDFSPreorderOnce(root, matcher, builder);
}

TEST_F(Schedule, MarkCoincident) {
  auto dependences = computeAllDependences(scop_);
  markCoincident(scop_.schedule.get_root(), dependences).dump();
}

static bool canSink(isl::schedule_node band) {
  auto dim = band.band_get_partial_schedule().dim(isl::dim::set);
  if (dim < 2) {
    return false;
  }

  auto permutable =
      isl_schedule_node_band_get_permutable(band.get()) == isl_bool_true;
  if (!permutable) {
    return false;
  }

  return true;
}

// pluto-style sinking
// assuming access relations with tags in the range
static int findSinkable(isl::union_map accesses, isl::schedule_node band) {
  auto schedule = band.band_get_partial_schedule();
  auto nDim = schedule.dim(isl::dim::set);
  auto ctx = accesses.get_ctx();

  std::vector<int64_t> weights;
  weights.reserve(nDim);
  for (unsigned i = 0; i < nDim; ++i) {

    auto schedule1D = schedule.get_union_pw_aff(i);
    auto scheduleMap1D = isl::union_map::from_union_pw_aff(schedule1D);
    auto scheduledAccess = accesses.apply_domain(scheduleMap1D);

    using namespace matchers;
    int nRepeated =
        match(scheduledAccess, allOf(access(dim(-1, stride(ctx, 0))))).size();
    int nLocal = 0;
    for (int s = 1; s <= 4; ++s) {
      nLocal +=
          match(scheduledAccess, allOf(access(dim(-1, stride(ctx, s))))).size();
    }
    int nAccesses = scheduledAccess.n_map();
    int nNonLocal = nAccesses - nRepeated - nLocal;
    bool isVectorizable = nNonLocal == 0;

    // count # of stride-zero (+4 per access)
    // count # of stride-one (+2 per access)
    // is vectorizable <= # of stride-zero + # of stride-one = # of accesses
    // (bonus 8) all other strides (-16 per access)
    weights.push_back(2 * nLocal + 4 * nRepeated + 8 * isVectorizable -
                      16 * nNonLocal);
  }

  auto maxWeightIter = std::max_element(weights.begin(), weights.end());
  return std::distance(weights.begin(), maxWeightIter);
}

TEST(Transformer, SinkLocal) {
  auto ctx = ScopedCtx(pet::allocCtx());
  auto scop = pet::Scop::parseFile(ctx, "inputs/1mm_fused.c").getScop();

  auto dependences = computeAllDependences(scop);
  scop.schedule =
      mergeIfTilable(scop.schedule.get_root(), dependences).get_schedule();

  isl::schedule_node node, child;
  auto matcher = matchers::band(
      [&node](isl::schedule_node n) {
        if (canSink(n)) {
          node = n;
          return true;
        }
        return false;
      },
      matchers::anyTree(child));

  isl::union_map accesses =
      scop.reads.unite(scop.mayWrites).unite(scop.mustWrites).curry();

  builders::ScheduleNodeBuilder builder = builders::band(
      [&node, &accesses]() {
        int pos = findSinkable(accesses, node);
        auto schedule = node.band_get_partial_schedule();
        auto scheduleAtPos = schedule.get_union_pw_aff(pos);
        schedule = schedule.drop_dims(isl::dim::set, pos, 1);
        schedule =
            schedule.flat_range_product(isl::multi_union_pw_aff(scheduleAtPos));

        builders::BandDescriptor descriptor(node);
        descriptor.partialSchedule = schedule;
        auto isCoincident = descriptor.coincident.at(pos);
        descriptor.coincident.erase(descriptor.coincident.begin() + pos);
        descriptor.coincident.push_back(isCoincident);
        return descriptor;
      },
      builders::subtree(child));

  node = replaceDFSPreorderOnce(scop.schedule.get_root(), matcher, builder);

  // Check that we indeed sink the "j" loop.
  // clang-format off
  auto expected = isl::union_map(ctx,
      "{ S_0[i, j, k] -> [o0, o1, o2, o3] : o0 = i and o1 = k and o2 = j and o3 = 0;"
        "S_1[i, j, k] -> [o0, o1, o2, o3] : o0 = i and o1 = k and o2 = j and o3 = 1 }");
  // clang-format on
  EXPECT_TRUE(node.get_schedule().get_map().is_subset(expected));
}

// Check that all relevant parts of the code (loops and transformed statements)
// are correctly generated.  In particular, check that loops are generated in
// the right order.  Whitespace is ignored.
TEST(Transformer, Codegen) {
  auto ctx = ScopedCtx(pet::allocCtx());
  auto petScop = pet::Scop::parseFile(ctx, "inputs/nested.c");

  std::string loop1 = "for (int c0 = 0; c0 <= min(1023, n - 2); c0 += 1)";
  std::string loop2 = "for (int c1 = 0; c1 < n - c0 - 1; c1 += 1)";
  std::string loop3 = "for (int c2 = n - 1; c2 <= n + 41; c2 += 1)";
  std::string loop4 = "for (int c3 = c0 + 1; c3 < n - c1; c3 += 1)";
  std::string stmt = "foo((c0), (c1), (c2), (c3));";
  auto result = petScop.codegen();

  auto loop1pos = result.find(loop1);
  auto loop2pos = result.find(loop2, loop1pos + loop1.length());
  auto loop3pos = result.find(loop3, loop2pos + loop2.length());
  auto loop4pos = result.find(loop4, loop3pos + loop3.length());
  auto stmtpos = result.find(stmt, loop4pos + loop4.length());

  // Note that we don't care about the particular positions in the string, only
  // that the relation between them holds. Therefore we use ASSERT_TRUE on
  // relations to avoid useless and potentially large (npos) numbers output in
  // case an assertion fails.
  ASSERT_TRUE(loop1pos != std::string::npos);
  ASSERT_TRUE(loop2pos != std::string::npos);
  ASSERT_TRUE(loop3pos != std::string::npos);
  ASSERT_TRUE(loop4pos != std::string::npos);
  ASSERT_TRUE(stmtpos != std::string::npos);

  ASSERT_TRUE(loop2pos > loop1pos);
  ASSERT_TRUE(loop3pos > loop2pos);
  ASSERT_TRUE(loop4pos > loop3pos);
  ASSERT_TRUE(stmtpos > loop4pos);
}

TEST(Transformer, InjectStatement) {
  auto ctx = ScopedCtx(pet::allocCtx());
  auto petScop = pet::Scop::parseFile(ctx, "inputs/stencil.c");

  isl::schedule_node node;
  auto matcher = [&]() {
    using namespace matchers;
    return anyTree(node);
  }();

  matchers::ScheduleNodeMatcher::isMatching(
      matcher, petScop.getScop().schedule.get_root().child(0));

  auto builder = [&]() {
    using namespace builders;
    return extension(
        isl::union_map(ctx, "[] -> {[]->someLongAndHopefullyUniqueName[]:}"),
        sequence(filter(isl::union_set(
                     ctx, "[] -> {someLongAndHopefullyUniqueName[]:}")),
                 filter(petScop.getScop().domain().universe(), subtree(node))));
  }();

  auto sched = builder.insertAt(petScop.getScop().schedule.get_root().child(0))
                   .get_schedule();
  petScop.schedule() = sched;
  auto code = petScop.codegen();
  EXPECT_TRUE(code.find("someLongAndHopefullyUniqueName") != std::string::npos);
}

isl::union_map addRangeId(isl::union_map umap, const std::string &tag) {
  auto id =
      isl::manage(isl_id_alloc(umap.get_ctx().get(), tag.c_str(), nullptr));
  // TODO: make this possible with matchers as well
  auto result = isl::union_map::empty(umap.get_space());
  umap.foreach_map([id, &result](isl::map m) {
    result = result.add_map(m.set_tuple_id(isl::dim::out, id));
  });
  return result;
}

// expecting scheduled access
isl::map make1dDLT(isl::map access, int size) {
  using namespace aff_op;
  access = access.coalesce();
  auto allPoints =
      isl::map::from_domain_and_range(access.range(), access.range());
  isl::pw_aff min = allPoints.dim_min(0);
  isl::pw_aff dist = allPoints.dim_max(0) - min + 1;
  // TODO: cut off: o0 > size * (dist / size)

  auto dlt = isl::map::empty(access.range().get_space().map_from_set());
  auto a = isl::aff::var_on_domain(isl::local_space(access.range().get_space()),
                                   isl::dim::set, 0);
  auto _i = isl::pw_aff(a);
  for (long s = 0; s < size; ++s) {
    auto lhs = s + size * (_i - min - s * dist / size);
    using namespace map_maker;
    dlt = dlt.unite((lhs == _i)
                        .intersect(_i >= min + s * dist / size)
                        .intersect(_i < min + (s + 1) * dist / size));
  }
  std::string arrayName = dlt.range().get_tuple_id().get_name();
  isl::id dltArrayId =
      isl::id::alloc(dlt.get_ctx(), "_dlt_" + arrayName, nullptr);
  return dlt.set_tuple_id(isl::dim::out, dltArrayId);
}

static __isl_give isl_multi_pw_aff *
transformSubscriptsDLT(__isl_take isl_multi_pw_aff *subscript,
                       __isl_keep isl_id *, void *user) {
  auto access = isl::manage(subscript);
  auto iteratorMap = isl::manage_copy(static_cast<isl_pw_multi_aff *>(user));
  auto scheduledAccess = access.pullback(iteratorMap);

  int dim = scheduledAccess.dim(isl::dim::set);
  for (int i = 0; i < dim; ++i) {
    auto pa = scheduledAccess.get_pw_aff(i);
    auto result = isl::pw_aff(isl::set::empty(pa.domain().get_space()),
                              isl::val::zero(pa.get_ctx()));
    pa.foreach_piece([&result](isl::set domain, isl::aff aff) {
      auto cst = aff.get_constant_val();
      auto partial = isl::pw_aff(aff.set_constant_val(cst.mul_ui(4)))
                         .intersect_domain(domain);
      result = result.union_add(partial);
    });
    scheduledAccess = scheduledAccess.set_pw_aff(i, result);
  }
  return scheduledAccess.release();
}

static std::string codegenDLTCopies(isl::ast_build astBuild, isl::ast_node node,
                                    pet_stmt *stmt) {
  if (stmt) {
    using namespace pet;
    auto schedule = isl::map::from_union_map(astBuild.get_schedule());
    auto iteratorMap = isl::pw_multi_aff::from_map(schedule.reverse());
    return printPetStmt(stmt,
                        buildRef2Expr(stmt, astBuild, transformSubscriptsDLT,
                                      iteratorMap.get()));
  }

  auto schedule = astBuild.get_schedule();
  auto original = schedule.reverse().range_factor_domain();
  auto dlt = schedule.reverse().range_factor_range();
  auto originalExpr = astBuild.access_from(
      isl::pw_multi_aff::from_map(isl::map::from_union_map(original)));
  auto dltExpr = astBuild.access_from(
      isl::pw_multi_aff::from_map(isl::map::from_union_map(dlt)));

  std::stringstream ss;
  auto direction = isl::set(schedule.domain()).get_tuple_id().get_name();
  if (direction == "from") {
    ss << originalExpr.to_C_str() << " = " << dltExpr.to_C_str() << ";";
  } else if (direction == "to") {
    ss << dltExpr.to_C_str() << " = " << originalExpr.to_C_str() << ";";
  } else {
    ISLUTILS_DIE("unknown copy direction");
  }

  return ss.str();
}

TEST(Transformer, HenrettyDLTJacobi) {
  auto ctx = ScopedCtx(pet::allocCtx());
  auto petScop = pet::Scop::parseFile(ctx, "inputs/stencil.c");
  auto scop = petScop.getScop();

  auto dependences = computeAllDependences(scop);
  isl::schedule_node node;

  auto is3Dstencil = [&](isl::schedule_node band) {
    using namespace matchers;
    // A band node always have a child (may be a leaf), and the prefix schedule
    // of that child includes the partial schedule of the node.
    auto prefixSchedule = band.child(0).get_prefix_schedule_union_map();
    auto scheduledReads = scop.reads.curry().apply_domain(prefixSchedule);
    auto arr = arrayPlaceholder();
    auto i = placeholder(ctx);

    auto matches =
        match(scheduledReads, allOf(access(dim(-1, i - 1)), access(dim(-1, i)),
                                    access(dim(-1, i + 1))));
    node = band;
    return matches.size() == 1;
  };

  auto DLTbuilder = [&]() {
    using namespace builders;

    auto dltExtensionBuilder = [&]() {
      auto prefixSchedule = node.get_prefix_schedule_union_map();
      auto scheduledReads =
          scop.reads.domain_factor_domain().apply_domain(prefixSchedule);
      // Because of the matcher, we know that only one array is accessed, so
      // untagged accesses live in the same space.
      isl::map dltMap = make1dDLT(isl::map::from_union_map(scheduledReads), 4);
      auto dlt = isl::union_map(dltMap);

      // FIXME: what if there is a dependence on schedule?
      return prefixSchedule.range().product(dlt.wrap()).unwrap();
#if 0
      auto scheduledDLT = scheduledReads.apply_range(dlt);
      return scheduledReads.range_product(scheduledDLT);
#endif
    };

    auto extensionBuilder = [dltExtensionBuilder]() {
      auto DLTExtension = dltExtensionBuilder();
      return addRangeId(DLTExtension, "to")
          .unite(addRangeId(DLTExtension, "from"));
    };

    auto toFilterBuilder = [dltExtensionBuilder]() {
      return addRangeId(dltExtensionBuilder(), "to").range().universe();
    };

    auto fromFilterBuilder = [dltExtensionBuilder]() {
      return addRangeId(dltExtensionBuilder(), "from").range().universe();
    };

    auto toBandBuilder = [dltExtensionBuilder]() {
      return isl::multi_union_pw_aff::from_union_map(
                 addRangeId(dltExtensionBuilder(), "to")
                     .range()
                     .affine_hull()
                     .wrapped_domain_map())
          .reset_tuple_id(isl::dim::set);
    };

    auto fromBandBuilder = [dltExtensionBuilder]() {
      return isl::multi_union_pw_aff::from_union_map(
                 addRangeId(dltExtensionBuilder(), "from")
                     .range()
                     .affine_hull()
                     .wrapped_domain_map())
          .reset_tuple_id(isl::dim::set);
    };

    auto coreFitlerBuilder = [&node]() { return node.get_domain(); };

    return extension(
        extensionBuilder,
        sequence(filter(toFilterBuilder, band(toBandBuilder)),
                 filter(coreFitlerBuilder, subtree([&]() {
                          return subtreeBuilder(node);
                        })), // TODO: transform the actual computation
                 filter(fromFilterBuilder, band(fromBandBuilder))));
  }();

  auto matcher = matchers::band(is3Dstencil, matchers::anyTree());
  EXPECT_TRUE(matchers::ScheduleNodeMatcher::isMatching(
      matcher, scop.schedule.get_root().child(0).child(0).child(0).child(0)));
  EXPECT_TRUE(matchers::ScheduleNodeMatcher::isMatching(
      matcher, scop.schedule.get_root().child(0).child(0).child(1).child(0)));

  scop.schedule =
      replaceDFSPostorderOnce(scop.schedule.get_root(), matcher, DLTbuilder)
          .get_schedule();
  petScop.schedule() = scop.schedule;
  static_cast<isl::schedule>(petScop.schedule()).dump();

  auto result = isl::union_map::empty(scop.reads.get_space());
  scop.reads.foreach_map([&result](isl::map m) {
    if (m.get_tuple_id(isl::dim::out).get_name() == "A") {
      m.set_tuple_name(isl::dim::out, "TEST");
    }
    result = result.add_map(m);
  });
  scop.reads = result;

  std::cout << petScop.codegen(codegenDLTCopies) << std::endl;
}
