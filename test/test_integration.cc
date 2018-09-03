#include "islutils/access.h"
#include "islutils/access_patterns.h"
#include "islutils/matchers.h"
#include "islutils/builders.h"
#include "islutils/ctx.h"
#include "islutils/parser.h"
#include <cstdarg>
#include "gtest/gtest.h"

using util::ScopedCtx;
using namespace matchers;

// print simple C code pretty printer
static void printAST(__isl_keep isl_ast_node *ast, __isl_keep isl_ctx *ctx) {
  isl_ast_print_options *options =
    isl_ast_print_options_alloc(ctx);
  isl_printer *p = isl_printer_to_str(ctx);
  p = isl_printer_set_output_format(p, ISL_FORMAT_C);
  p = isl_printer_indent(p,1);
  p = isl_ast_node_print(ast, p, options);
  char *ASTStr = isl_printer_get_str(p);
  std::cout << "AST Code Gen" << std::endl;
  std::cout << ASTStr << std::endl;
  free(ASTStr);
  isl_printer_free(p);
}

// walk the AST
static void walkASTTree(__isl_keep isl_ast_node *ast) {
  isl_ast_node_foreach_descendant_top_down(
  ast,
  [](__isl_keep isl_ast_node *node, void *user) -> isl_bool {
    // code 
    return isl_bool_true;
  }, nullptr);
}

// Simple function to generate and print AST.
static void simpleASTGen(Scop scop, isl::schedule_node root) {

  auto CTX = ScopedCtx();

  isl_options_set_ast_build_atomic_upper_bound(CTX, true);
  isl_options_set_ast_build_detect_min_max(CTX, true);
  isl_ast_build *build;
  build = isl_ast_build_from_context(scop.context.release());
  isl::schedule schedule = root.get_schedule();
  auto rootAST =
    isl_ast_build_node_from_schedule(build, schedule.release());
  walkASTTree(rootAST);

  /// print AST.
  printAST(rootAST, CTX);

  isl_ast_build_free(build);

}

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

namespace builders{

class Tile{

  public:
    static isl::schedule_node tileNode(isl::schedule_node node, int tileSize);
};

isl::schedule_node Tile::tileNode(isl::schedule_node node, int tileSize) {
  assert(isl_schedule_node_get_type(node.get()) == isl_schedule_node_band &&
         "expect band node");
  isl::ctx ctx = node.get_ctx();
  isl::space space =
      isl::manage(isl_schedule_node_band_get_space(node.get()));
  isl::multi_val sizes = isl::multi_val::zero(space);

  for(size_t i=0; i<space.dim(isl::dim::set); ++i)
    sizes = sizes.set_val(i, isl::val(ctx,tileSize));

  isl::schedule_node tiledNode =
    isl::manage(isl_schedule_node_band_tile(node.release(), sizes.release()));

  return tiledNode;
}

class TileNode: private Tile{

  public:

    TileNode() : tileSize(32) {}

    TileNode(int x) : tileSize(x) {}

    virtual isl::schedule_node operator() (isl::schedule_node band);

  private:
    int tileSize;
    isl::schedule_node insertPointMarker(isl::schedule_node);
    isl::schedule_node insertTileMarker(isl::schedule_node);
    void numberConsecutiveBand(isl::schedule_node, int&);
    isl::schedule_node tileConsecutiveBand(isl::schedule_node, int, int);
};

isl::schedule_node TileNode::tileConsecutiveBand(isl::schedule_node band,
						 int tileSize,
                                                 int numberOfBands) {
  assert(isl_schedule_node_get_type(band.get()) == isl_schedule_node_band);
  std::vector<isl::schedule_node> involvedBands;

  for(int i = 0; i < numberOfBands; ++i) {
    auto space = isl::manage(isl_schedule_node_band_get_space(band.get()));
    auto dims = space.dim(isl::dim::set);
    assert(dims == 1);
    band = tileNode(band, tileSize);
    involvedBands.push_back(band);
    band = band.child(0);
    band = band.child(0);
  }

  isl::schedule_node capture;
  // use the matcher to capture the entire sub-tree
  // before re-building.

  //clang-format off
  matchers::ScheduleNodeMatcher matcher =   
    matchers::anyTree(capture);
  //clang-format on

  bool res =
    ScheduleNodeMatcher::isMatching(matcher, band);
  assert(res && "should match");

  // move back "band" to original position.
  for(int i = 0; i < numberOfBands*2; ++i) {
    band = band.parent();
  }

  // TODO: here for now we assume just 2 consecutive
  // band nodes. We need to extend the builder to multiple consecutive
  // band nodes.
  //clang-format on
  builders::ScheduleNodeBuilder builder = 
    builders::band(involvedBands[0].band_get_partial_schedule(),
      builders::band(involvedBands[1].band_get_partial_schedule(),
        builders::band(involvedBands[0].child(0).band_get_partial_schedule(),
	  builders::band(involvedBands[1].child(0).band_get_partial_schedule(),
	    builders::subtree(capture)))));
  //clang-format off

  band = band.cut();
  band = builder.insertAt(band);

  return band;
}

void TileNode::numberConsecutiveBand(isl::schedule_node band, int& n) {
  if(!band.has_children())
    return;
  if(band.n_children() > 1)
    return;
  band = band.child(0);
  if(!isl_schedule_node_get_type(band.get()) ==
	isl_schedule_node_band)
    return; 
  return numberConsecutiveBand(band, ++n);
}

isl::schedule_node TileNode::insertPointMarker(isl::schedule_node band) {
  isl::ctx ctx = band.get_ctx();
  std::string marker = "tiling -tiles";
  isl::id markerTile =
    isl::id::alloc(ctx, marker, nullptr);
  band.insert_mark(markerTile);
  band = band.child(0);
  return band;
}

isl::schedule_node TileNode::insertTileMarker(isl::schedule_node band) {
  isl::ctx ctx = band.get_ctx();
  std::string marker = "tiling -points";
  isl::id markerPoint =
    isl::id::alloc(ctx, marker, nullptr);
  band.insert_mark(markerPoint);
  band = band.child(0);
  return band;
}

isl::schedule_node TileNode::operator() (isl::schedule_node band) {

  assert(isl_schedule_node_get_type(band.get()) == isl_schedule_node_band &&
        "expect band node");

  // check if the band dominates some consecutive bands,
  // if this is the case we tile also the dominated bands.
  int numberBand = 1;
  numberConsecutiveBand(band, numberBand);
  if(numberBand != 1) {
    band = tileConsecutiveBand(band, tileSize, numberBand);
  }
  else {  
    band = tileNode(band, tileSize);
  }
  return band.child(0);
}

/*
ScheduleNodeBuilder tileAndUnroll(isl::schedule_node node, int tileSize) {
  std::cout << "tile and unroll\n"; 
  assert(isl_schedule_node_get_type(node.get()) == isl_schedule_node_band &&
         "expect band node");
 
  isl::schedule_node tiledNode = tileNode(node, tileSize);
  isl::ctx ctx = tiledNode.get_ctx();
  isl::union_set astOptions = isl::union_set(ctx, "{unroll[x]}");
  
  //clang-format off
  return
    band(tiledNode.band_get_partial_schedule(),
      band(tiledNode.child(0).band_get_partial_schedule(), astOptions));
  //clang-format on 
}

static isl::schedule_node transform(isl::schedule_node t,
           std::function<ScheduleNodeBuilder(isl::schedule_node,int)>) {
  return t;
}
*/

// check if two band nodes are the same. 
static bool isSameBand(isl::schedule_node node, isl::schedule_node target) {
  isl::union_map nodeSchedule = node.get_prefix_schedule_relation();
  isl::union_map targetSchedule = target.get_prefix_schedule_relation();
  if(nodeSchedule.is_equal(targetSchedule))
    return true;
  else return false;
}

// DFS search.
static isl::schedule_node dfsFirst(isl::schedule_node node, 
					isl::schedule_node target) {

  if(isSameBand(node, target)) {
    return node;
  }

  isl::schedule_node res;
  for(int i = 0, e = node.n_children(); i < e; ++i) {
    node = node.child(i);
    res = dfsFirst(node, target);
    if(!res.is_null()) {
      return res;
    }
    node = node.parent();
  }

  return nullptr;
}

template <typename Func>
static isl::schedule_node transform(isl::schedule_node root, Func tile,
				    isl::schedule_node band) {
  isl::schedule_node target = dfsFirst(root, band); 
  assert(!target.is_null() && "band node not found");
  target = tile(target);
  return target.root();
}

} // end namespace builders

////////////////////////////////////
/// tests
////////////////////////////////////

TEST(Integration, 1mmF) {
  using namespace matchers;
  using namespace builders;
  
  auto ctx = ScopedCtx();
  auto scop = Parser("inputs/1mmF.c").getScop();
  ASSERT_FALSE(scop.schedule.is_null());

  scop.schedule =
    scop.schedule.intersect_domain(scop.nonKillDomain);
  auto root = scop.schedule.get_root();

  // accesses
  isl::union_map reads = scop.reads.curry();
  isl::union_map writes = scop.mustWrites.curry();

  // code gen not opt.
  simpleASTGen(scop,root);

  std::vector<isl::schedule_node> bandTarget(3);
  std::vector<isl::schedule_node> filterTarget(2);
  std::vector<isl::schedule_node> leafTarget(2);

  auto matcher = [&]() {
    using namespace matchers;
    // clang-format off
    return
      band(bandTarget[0],
        band(bandTarget[1],
          sequence(
            filter(filterTarget[0], leaf(leafTarget[0])),
            filter(filterTarget[1],
              band(bandTarget[2], leaf(leafTarget[1]))))));
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
  EXPECT_EQ(match(reads, allOf(access(dim(1, stride(ctx,1))))).size(), 1);

  // Ideas for transformation:
  // 1. completely change a give subtree (i.e. matmul) in one shot.
  // 2. we can apply to each captured node a given transformation.

  // NOTE: if a band node X is followed by another band node Y
  // and we tile X also Y will be tiled.
  // For example, tile(band[0]) will tile also band[1]
  // while tile(band[1]) will tile *only* band[1] 
 
  // create a copy for root.
  isl::schedule_node rootCopy1 = root;
  TileNode tileNode = TileNode(32); 
  rootCopy1 = transform(rootCopy1, tileNode, bandTarget[2]);
  rootCopy1 = transform(rootCopy1, tileNode, bandTarget[0]);
  // code gen not opt.
  simpleASTGen(scop,rootCopy1);

  // create a copy for root.
  //isl::schedule_node rootCopy2 = root;
  //rootCopy2 = transform(rootCopy2, tileNode, 2, bandTarget[0], bandTarget[1]);
  
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
