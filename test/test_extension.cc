#include <islutils/builders.h>
#include <islutils/matchers.h>
#include <islutils/parser.h>
#include <string>
#include <vector>
#include "gtest/gtest.h"
#include "pet.h"
#include "test_extension.h"

static char *concat(isl_ctx *ctx, const char *a, const char *b)
{
        isl_printer *p;
        char *s;

        p = isl_printer_to_str(ctx);
        p = isl_printer_print_str(p, a);
        p = isl_printer_print_str(p, "_");
        p = isl_printer_print_str(p, b);
        s = isl_printer_get_str(p);
        isl_printer_free(p);

        return s;
}

template <class ... Args>
static void annotateStatement(std::string st, Args... args) 
{
  std::string annotation = strAnnotation(args...);
  annotationMap.insert({st, annotation});
}

//static void markLoop()
//{
//
//}
/*
static isl::schedule_node traverse_check(Scop* S, isl::schedule_node node)
{
   if (isl_schedule_node_get_type(node.get()) == isl_schedule_node_band) {
        if (isl_schedule_node_band_member_get_coincident(node.get(), 0)) {
          isl_id* id = isl_id_alloc(S->mustWrites.get_ctx().get(), "kernel code", NULL);
          using namespace builders;
          auto insertKernelMarker = mark(id);
          node = insertKernelMarker.insertAt(node);
          node = node.child(0); // as we need to proceed to actual band node
        } else {
          isl_id* id = isl_id_alloc(S->mustWrites.get_ctx().get(), "host code", NULL);
          using namespace builders;
          auto insertHostMarker = mark(id);
          node = insertHostMarker.insertAt(node);
          node = node.child(0); // as we need to proceed to actual band node
        }
    }
    size_t nChildren = static_cast<size_t>(isl_schedule_node_n_children(node.get()));
    for (size_t i = 0; i < nChildren; ++i) {
       auto child_node = node.child(i);
       child_node = detect_band_node(S, child_node);
       node = child_node.parent();
    }

    if (isl_schedule_node_get_type(node.get()) == isl_schedule_node_band) {
        return node.parent();
    }
    return node;
}
*/

//void parseMatcherLibrary(std::vector<ScheduleNodeMatcher>* matchers)
//{
//   auto matcher =
//    band(any());
//}

/*
 Currently suggested to construct extension nodes if copy is required
 Not sure if we can write like this:
  extension(which, any())
 
 We can use this function : isl_schedule_tree/node_from_extension
 
 Extention is a union map
 
 band(leaf(isColumn()) -> extention(local, kernel(band(leaf())))
void constructExtensionNode()

*/


static void compute_flow_dep(struct Scop *S)
{
  isl_union_access_info *access;
  isl_union_flow *flow; 
  isl_union_map *kills, *must_writes;

  access = isl_union_access_info_from_sink(isl_union_map_copy(S->reads.get()));
  must_writes = isl_union_map_copy(S->mustWrites.get());
  access = isl_union_access_info_set_kill(access, must_writes);
  access = isl_union_access_info_set_may_source(access,
                            isl_union_map_copy(S->mayWrites.get()));
  access = isl_union_access_info_set_schedule(access,
                            isl_schedule_copy(S->schedule.get()));
  flow = isl_union_access_info_compute_flow(access);
  
  auto may_dependence = isl::manage(isl_union_flow_get_may_dependence(flow)); 
  S->depFlow = may_dependence;
  auto live_in = isl::manage(isl_union_flow_get_may_no_source(flow));
  S->liveIn = live_in;
}

static void compute_dependencies(struct Scop *S)
{
  isl_union_map *may_source, *dep_false;
  isl_union_access_info *access;
  isl_union_flow *flow;

  compute_flow_dep(S);
  
  may_source = isl_union_map_union(isl_union_map_copy(S->mayWrites.get()),
                               isl_union_map_copy(S->reads.get()));  
  access = isl_union_access_info_from_sink(
                               isl_union_map_copy(S->mayWrites.get()));
  access = isl_union_access_info_set_kill(access,
                                isl_union_map_copy(S->mustWrites.get()));
  access = isl_union_access_info_set_may_source(access, may_source);
  access = isl_union_access_info_set_schedule(access,
                               isl_schedule_copy(S->schedule.get()));
  
  flow = isl_union_access_info_compute_flow(access);
  
  dep_false = isl_union_flow_get_may_dependence(flow);
  dep_false = isl_union_map_coalesce(dep_false);
  auto final_dep_false = isl::manage(dep_false);
  S->depFalse = final_dep_false; 
}

static isl_schedule_constraints* compute_schedule_constraints(isl_schedule_constraints *sc, isl_union_map *validity,
					 isl_union_map *coincidence, isl_union_map *dep_raw, isl_union_map *dep, 
                                         isl_union_map *proximity, Scop* S)
{
  sc = isl_schedule_constraints_on_domain(isl_union_set_copy(S->domain().get()));
  dep_raw = isl_union_map_copy(S->depFlow.get());
  dep = isl_union_map_copy(S->depFalse.get());
  dep = isl_union_map_union(dep, dep_raw);
  dep = isl_union_map_coalesce(dep);

  proximity = isl_union_map_copy(dep);
  coincidence = isl_union_map_copy(dep);
  validity = dep;

  sc = isl_schedule_constraints_set_validity(sc, validity);
  sc = isl_schedule_constraints_set_coincidence(sc, coincidence);
  sc = isl_schedule_constraints_set_proximity(sc, proximity);

  return sc;
}


bool isKernel(isl::schedule_node node) 
{
  if (isl_schedule_node_get_type(node.get()) == isl_schedule_node_band && 
      isl_schedule_node_band_member_get_coincident(node.get(), 0)) {
    return true;
  }
}

static isl_schedule_node* differentiateSchedule(isl_schedule_node* Node, void *User)
{

  Scop* S = static_cast<Scop*>(User);
  //std::vector<isl::schedule_node>* kernel_nodes = static_cast<std::vector<isl::schedule_node>*>(User);
  using namespace matchers;
  auto matcher = band(isKernel, any());
  
  if (ScheduleNodeMatcher::isMatching(matcher, isl::manage_copy(Node))) {
    //kernel_nodes->push_back(isl::manage_copy(Node));    

     isl_id* id = isl_id_alloc(S->mustWrites.get_ctx().get(), "kernel code", nullptr);
     using namespace builders;
     auto insertKernelMarker = mark(id);
     auto cpp_node = isl::manage(Node);
     auto new_node =  insertKernelMarker.insertAt(cpp_node);
     isl_schedule_node_dump(new_node.get());
     return new_node.release();
  }
  
  return Node;
}

static isl_schedule_node* standardMarker(isl_schedule_node* Node, void *User)
{
  Scop* S = static_cast<Scop*>(User);
  using namespace matchers;
  auto matcher = band(isKernel, any());
  // hard: replace on sequence(filter(band()), filter(mark(band(any()))), filter(band()))
  // easy: replace on filter(mark(band(any())))
  
  if (ScheduleNodeMatcher::isMatching(matcher, isl::manage_copy(Node))) {
    // replace with builder
    // at first we need to generate a payload for every type of the builder
    isl_id* id = isl_id_alloc(S->mustWrites.get_ctx().get(),
			      strAnnotation("xcl_array_partition", 1).c_str(), nullptr);
    isl_id_dump(id);
    using namespace builders;
    auto insertKernelMarker = mark(id);
    auto cpp_node = isl::manage(Node);
    auto new_node =  insertKernelMarker.insertAt(cpp_node);
    isl_schedule_node_dump(new_node.get());
    return new_node.release();
  }
  
  return Node;
}

static isl_union_map* createCopyNode(bool direction, isl_union_set* setCopy, isl_schedule_node* node, TestContext* context)
{

  isl_union_set_list *filters;
  filters = isl_union_set_list_alloc(context->ctx_, 0);

  for (int i = 0; i < context->petScop_->n_array; ++i) {
    isl_space *space;
    isl_set *accessed_i;
    int empty;
    const char *name;
    const char *array_name;
    isl_id *id;
    isl_union_set *uset;
    struct pet_array* pa = context->petScop_->arrays[i];

    space = isl_set_get_space(pa->extent);

    accessed_i = isl_union_set_extract_set(setCopy, space);

    empty = isl_set_plain_is_empty(accessed_i);

    if (empty) continue;
     
    if (empty < 0) break;
    
    array_name = isl_set_get_tuple_name(pa->extent);
    name = concat(context->ctx_, direction ? "to_device" : "from_device", array_name);
    id = name ? isl_id_alloc(context->ctx_, name, pa) : NULL;

    space = isl_space_set_alloc(context->ctx_, 0, 0);
    space = isl_space_set_tuple_id(space, isl_dim_set, id);
    uset = isl_union_set_from_set(isl_set_universe(space));
    filters = isl_union_set_list_add(filters, uset);
  }

  isl::schedule_node cpp_node = isl::manage(node);
  cpp_node = cpp_node.child(0);

  isl_union_set* all = isl_union_set_list_union(isl_union_set_list_copy(filters));
  int depth = isl_schedule_node_get_schedule_depth(cpp_node.copy());
  auto space = depth < 0 ? NULL : isl_space_set_alloc(context->ctx_, 0, depth);
  isl_union_set* domain = isl_union_set_from_set(isl_set_universe(space));

  isl_union_map* extension = isl_union_map_from_domain_and_range(domain, all);

  return extension; 
}

static isl_schedule_node* insertCopyBackForwardMarkNodes(isl_schedule_node* Node, void* User)
{
  if (isl_schedule_node_get_type(Node) == isl_schedule_node_mark) {
    
    //create graft node at first
    TestContext* context = static_cast<TestContext*>(User);
    isl_union_set* setCopy = isl_union_map_range(context->s_->reads.copy());
    
    isl_union_map* extensionForwardNode = createCopyNode(1, setCopy, isl_schedule_node_copy(Node), context); 
    isl_union_map* extensionBackwardNode = createCopyNode(0, setCopy, isl_schedule_node_copy(Node), context);
    using namespace builders;
    auto cpp_node = isl::manage(Node);

    auto insertCopyForwardNode = extension(isl::manage(extensionForwardNode), 1);
    auto new_node =  insertCopyForwardNode.insertAt(cpp_node);
    auto insertCopyBackwardNode = extension(isl::manage(extensionBackwardNode), 0);
    auto new_node_2 = insertCopyBackwardNode.insertAt(new_node); 

    return new_node_2.parent().parent().parent().release();
  }
  return Node;
}

static isl_schedule_node* insertCopyForwardMarkNodes(isl_schedule_node* Node, void* User)
{
  if (isl_schedule_node_get_type(Node) == isl_schedule_node_mark) {

    //create graft node at first
    TestContext* context = static_cast<TestContext*>(User);
    isl_union_set* setCopy = isl_union_map_range(context->s_->reads.copy());

    isl_union_map* extensionForwardNode = createCopyNode(1, setCopy, isl_schedule_node_copy(Node), context);
    using namespace builders;
    auto cpp_node = isl::manage(Node);

    auto insertCopyForwardNode = extension(isl::manage(extensionForwardNode), 1);
    auto new_node =  insertCopyForwardNode.insertAt(cpp_node);

    return new_node.parent().parent().parent().release();
  }
  return Node;
}

static void generateCopySchedule(isl_schedule_node* node, TestContext* context)
{
  struct pet_array* pa = context->petScop_->arrays[0];
 
  isl_multi_pw_aff *mpa;
  isl_multi_union_pw_aff *mupa;
 
  isl_space* space = isl_set_get_space(pa->extent);
  space = isl_space_from_range(space);
  space = isl_space_add_dims(space, isl_dim_in, 1);
  space = isl_space_wrap(space);
  space = isl_space_map_from_set(space);
  isl_id* id = isl_id_alloc(context->ctx_, read ? "read" : "write", context);
  space = isl_space_set_tuple_id(space, isl_dim_in, id);

  isl_multi_aff *from_access = isl_multi_aff_identity(space);
  printf("from_access\n");
  isl_multi_aff_dump(from_access);

  isl_map* from_access_map = isl_map_from_multi_aff(isl_multi_aff_copy(from_access));
  printf("from access map\n");
  isl_map_dump(from_access_map);

  isl_union_map* from_access_union_map = isl_union_map_from_map(from_access_map);
  printf("from access union map\n");
  isl_union_map_dump(from_access_union_map);
  
  printf("space\n");
  isl_space_dump(space);

  isl_space* space2 = isl_space_domain(isl_multi_aff_get_space(from_access));

  printf("space\n");
  isl_space_dump(space2);

  isl_union_map *access = isl_union_map_copy(context->s_->mustWrites.get());
  //access = isl_union_map_preimage_range_multi_aff(access, from_access);
  //printf("access\n");
  isl_union_map_dump(access);
  isl_union_set* filter = isl_union_set_empty(space2);
  printf("filter\n");
  isl_union_set_dump(filter);
  filter = isl_union_set_apply(filter, isl_union_map_copy(access));
  isl_union_set_dump(filter);
  
  space2 = isl_space_map_from_set(space2);
  mpa = isl_multi_pw_aff_identity(space);
  mpa = isl_multi_pw_aff_range_factor_range(mpa);
  mupa = isl_multi_union_pw_aff_from_multi_pw_aff(mpa);

  printf("mupa\n");
  isl_multi_union_pw_aff_dump(mupa);

  isl_union_set* domain = isl_union_map_domain(from_access_union_map);
  printf("domain\n");
  isl_union_set_dump(domain);
  access = isl_union_set_wrapped_domain_map(domain);
  printf("new access\n");
  isl_union_map_dump(access);
  access = isl_union_map_reverse(access);
  printf("new access1\n");
  isl_union_map_dump(access);
  access = isl_union_map_coalesce(access);
  printf("new access2\n");
  isl_union_map_dump(access);

  isl_schedule_node* graft = isl_schedule_node_from_extension(access);
  graft = isl_schedule_node_child(graft, 0);
  graft = isl_schedule_node_insert_partial_schedule(graft, mupa);
  graft = isl_schedule_node_insert_filter(graft, filter);
  printf("\ngraft node\n");
  isl_schedule_node_dump(graft);
  
}

/* totally copied from ppcg just to have hier also for additional check*/
static __isl_give isl_union_map *get_local_coincidence(
        __isl_keep isl_schedule_node *node,
        __isl_keep isl_schedule_constraints *sc)
{
        isl_union_map *coincidence;
        isl_multi_union_pw_aff *prefix;
        isl_union_pw_multi_aff *contraction;

        coincidence = isl_schedule_constraints_get_coincidence(sc);
        contraction = isl_schedule_node_get_subtree_contraction(node);
        if (isl_schedule_node_get_schedule_depth(node) == 0) {
                isl_union_set *domain;

                domain = isl_schedule_node_get_domain(node);
                domain = isl_union_set_preimage_union_pw_multi_aff(domain,
                                                    contraction);
                coincidence = isl_union_map_intersect_domain(coincidence,
                                                    isl_union_set_copy(domain));
                coincidence = isl_union_map_intersect_range(coincidence,
                                                    domain);
                return coincidence;
        }

        prefix = isl_schedule_node_get_prefix_schedule_multi_union_pw_aff(node);
        prefix = isl_multi_union_pw_aff_pullback_union_pw_multi_aff(prefix,
                                                                contraction);
        return isl_union_map_eq_at_multi_union_pw_aff(coincidence, prefix);
}

/* totally copied from ppcg just to have hier also for additional check*/
static __isl_give isl_schedule_node *band_set_permutable(
        __isl_take isl_schedule_node *node,
        __isl_keep isl_schedule_constraints *sc)
{
        if (isl_schedule_node_band_n_member(node) == 1)
                node = isl_schedule_node_band_set_permutable(node, 1);

        return node;
}

/* totally copied from ppcg just to have hier also for additional check*/
static __isl_give isl_schedule_node *band_set_coincident(
        __isl_take isl_schedule_node *node,
        __isl_keep isl_schedule_constraints *sc)
{
        isl_union_map *coincidence;
        isl_union_pw_multi_aff *contraction;
        isl_multi_union_pw_aff *partial;
        int i, n;

        coincidence = get_local_coincidence(node, sc);

        partial = isl_schedule_node_band_get_partial_schedule(node);
        contraction = isl_schedule_node_get_subtree_contraction(node);
        partial = isl_multi_union_pw_aff_pullback_union_pw_multi_aff(partial,
                                                                contraction);
        n = isl_schedule_node_band_n_member(node);
        for (i = 0; i < n; ++i) {
                isl_union_map *coincidence_i;
                isl_union_pw_aff *upa; 
                isl_multi_union_pw_aff *partial_i;
                int subset;

                upa = isl_multi_union_pw_aff_get_union_pw_aff(partial, i);
                partial_i = isl_multi_union_pw_aff_from_union_pw_aff(upa);
                coincidence_i = isl_union_map_copy(coincidence);
                coincidence_i = isl_union_map_eq_at_multi_union_pw_aff(
                                                    coincidence_i, partial_i);
                subset = isl_union_map_is_subset(coincidence, coincidence_i);
                isl_union_map_free(coincidence_i);

                if (subset < 0)
                        break;
                node = isl_schedule_node_band_member_set_coincident(node, i,
                                                                    subset);
        }
        if (i < n)
                node = isl_schedule_node_free(node);
        isl_multi_union_pw_aff_free(partial);
        isl_union_map_free(coincidence);

        return node;
}

/* totally copied from ppcg just to have hier also for additional check*/
static __isl_give isl_schedule_node *set_band_properties(
        __isl_take isl_schedule_node *node, void *user)
{
        isl_schedule_constraints *sc =  static_cast<isl_schedule_constraints*>(user);

        if (isl_schedule_node_get_type(node) != isl_schedule_node_band)
                return node;
        if (isl_schedule_node_band_n_member(node) == 0)
                return node;
        
        node = band_set_permutable(node, sc);
        node = band_set_coincident(node, sc);

        return node;
}

/*static void annotateArraysAndKernel(TestContext* context)
{
  for (int i = 0; i < context->petScop_->n_array; i++) {
    struct pet_array* pa = context->petScop_->arrays[i];
    const char *array_name = isl_set_get_tuple_name(pa->extent);
    std::string localName = "local_"+std::string(array_name);
    std::string annotation = annotateStatement(localName, "xcl_array_partition", "cyclic", 256, 1); 
  }
  // suppose we have number of present kernels
  for (int i = 0; i < kernelNumber; i++) {
    //annotate
  }
  }*/
void runAllFlow(std::string fileName, bool computeSchedule) {

  //implement function which parses matcher library 
  //currently just add one matcher there
  //std::vector<ScheduleNodeMatcher> matchers;
  //parseMatcherLibrary(&matchers);
 
  // if kernel is marked already once, we should not mark it as a kernel again

  std::vector<isl::schedule_node> kernel_nodes;
  Scop S = Parser(fileName).getScop();
  pet_scop *scop_pet = pet_scop_extract_from_C_source(S.mustWrites.get_ctx().get(), fileName.c_str(), NULL);  
  /* construct common info Class*/

  isl_schedule_node_dump(isl_schedule_get_root(S.schedule.get()));
  TestContext* context = new TestContext(&S, scop_pet, fileName, S.mustWrites.get_ctx().get());
  /* set options */
  isl_options_set_ast_build_detect_min_max(S.mustWrites.get_ctx().get(), 1);
  isl_options_set_ast_print_macro_once(S.mustWrites.get_ctx().get(), 1);
  isl_options_set_schedule_whole_component(S.mustWrites.get_ctx().get(), 0);
  isl_options_set_schedule_maximize_band_depth(S.mustWrites.get_ctx().get(), 1);
  isl_options_set_schedule_maximize_coincidence(S.mustWrites.get_ctx().get(), 1);
  isl_options_set_schedule_outer_coincidence(S.mustWrites.get_ctx().get(), 1);
  /* compute flow and dependencies */

  compute_dependencies(&S); 

  /* compute schedule constraints */
  isl_schedule_constraints *sc;
  isl_union_map *validity, *coincidence, *proximity;
  isl_union_map *dep_raw, *dep;
  isl_schedule* new_schedule;

  if (computeSchedule) {
    sc = compute_schedule_constraints(sc, validity, coincidence, dep_raw, dep, proximity, &S);
    new_schedule = isl_schedule_constraints_compute_schedule(sc);
  } else {

    /* determine properties of original schedule */
    new_schedule = isl_schedule_copy(S.schedule.get());
    sc = compute_schedule_constraints(sc, validity, coincidence, dep_raw, dep, proximity, &S);
    new_schedule = isl_schedule_map_schedule_node_bottom_up(new_schedule,
                                               &set_band_properties, sc);
  } 
  
  printf("\ndump new schedule\n\n"); 
  isl_schedule_node* node = isl_schedule_get_root(new_schedule);
  isl_schedule_node_dump(node);

  node = isl_schedule_node_map_descendant_bottom_up(node, differentiateSchedule,
                                             (static_cast<void *>(&S)));  
  printf("vector length %i\n", kernel_nodes.size());

  printf("\ndump_schedule_with_mark_nodes\n");
  isl_schedule_node_dump(node);
  
  /* try to insert smth before mark node */
  printf("try to find mark nodes\n");

  node = isl_schedule_node_map_descendant_bottom_up(node, insertCopyBackForwardMarkNodes,
                                             (static_cast<void *>(context)));
  isl_schedule_node_dump(node);

  node = isl_schedule_node_map_descendant_bottom_up(node, standardMarker,
                                             (static_cast<void *>(&S)));
  //annotateArraysAndKernel(context);
  //auto newcpp = isl::manage(node);
  //isl_schedule_node_dump(newcpp.child(0).child(0).child(0).child(0).get());
  //generateCopySchedule(newcpp.copy(), context);
  /* general flow for first test */
  /* find for band(any())
   * mark nodes with annotation
   * print
   */
  // for example insert every array type with annotation
  //for (int i = 0; i < N; i++) {
  //  struct pet_array* pa = context->petScop_->arrays[i];
  //}
  // we should remember to mark our extrension nodes to transfer to device wuith different ddr banks
}

int main(int argc, char **argv) {
  bool computeSchedule = true;
  if (argc > 2 && !argv[2]) {
    computeSchedule = false;
  }
  runAllFlow(argv[1], computeSchedule);
}


