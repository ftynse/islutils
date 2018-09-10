#include "islutils/access.h"
#include "islutils/access_patterns.h"
#include "islutils/ctx.h"
#include "islutils/parser.h"
#include "islutils/matchers.h"
#include "islutils/builders.h"

#include "gtest/gtest.h"

using util::ScopedCtx;
using namespace matchers;

static int walkScheduleTree(const ScheduleNodeMatcher &matcher,
                                isl::schedule schedule) {
  using namespace matchers;
  auto root = schedule.get_root();
  if(!root)
    return false;

  struct Payload {
    int counter;
    const ScheduleNodeMatcher* m;
  }payload;

  payload.counter = 0;
  payload.m = &matcher;

  isl_schedule_node_foreach_descendant_top_down(
  root.get(),
  [](__isl_keep isl_schedule_node *nodePtr, void *user) -> isl_bool {
    isl::schedule_node node = isl::manage_copy(nodePtr);
    Payload& payloadPtr = *static_cast<Payload*>(user);
    bool res = false;
    res = matchers::ScheduleNodeMatcher::isMatching(*payloadPtr.m, node);
    if(res) {
      payloadPtr.counter++;
    }
    return isl_bool_true;
  }, &payload);

  return payload.counter;
}


TEST(Integration, 1mm) {
  using namespace matchers;
  using namespace builders;
  
  auto ctx = ScopedCtx();
  auto scop = Parser("inputs/1mm.c").getScop();
  ASSERT_FALSE(scop.schedule.is_null());

  scop.schedule =
    scop.schedule.intersect_domain(scop.domain());
  auto root = scop.schedule.get_root();

  // accesses
  isl::union_map reads = scop.reads.curry();
  isl::union_map writes = scop.mustWrites.curry();

  std::vector<isl::schedule_node> bandTarget(3);

  auto matcher = [&]() {
    using namespace matchers;
    // clang-format off
    return
      band(bandTarget[0],
        band(bandTarget[1],
          sequence(
            filter(leaf()),
            filter(
              band(bandTarget[2], leaf())))));
    // clang-format on
  }();

  int numberOfMatches =
    walkScheduleTree(matcher, scop.schedule);

  EXPECT_EQ(numberOfMatches, 1);
 
  // check accesses
  auto _1 = placeholder(ctx);
  auto _2 = placeholder(ctx);
  auto _3 = placeholder(ctx); 
 
  auto psRead = allOf(access(dim(0, _1), dim(1, _2)),
                      access(dim(0, _3), dim(1, _2)),
                      access(dim(0, _1), dim(1, _3)));

  auto psWrite = allOf(access(dim(0, _1), dim(1, _2)));

  auto matches = match(reads, psRead);
  EXPECT_EQ(matches.size(), 1);
  matches = match(writes, psWrite);
  EXPECT_EQ(matches.size(), 2);

  // check stride.
  EXPECT_EQ(match(reads, allOf(access(dim(1, stride(ctx,2))))).size(), 1);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
