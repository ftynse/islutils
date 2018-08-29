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

  TestContext* context = static_cast<TestContext*>(User);
  //std::vector<isl::schedule_node>* kernel_nodes = static_cast<std::vector<isl::schedule_node>*>(User);
  using namespace matchers;
  auto matcher = band(isKernel, any());
  
  if (ScheduleNodeMatcher::isMatching(matcher, isl::manage_copy(Node))) {
    //kernel_nodes->push_back(isl::manage_copy(Node));    

     isl_id* id = isl_id_alloc(context->ctx_, "kernel code", nullptr);
     using namespace builders;
     auto insertKernelMarker = mark(id);
     auto cpp_node = isl::manage(Node);
     auto new_node =  insertKernelMarker.insertAt(cpp_node);
     context->matched_nodes_.push_back(isl_schedule_node_copy(new_node.get()));
     //isl_schedule_node_dump(new_node.get());
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
  auto space = depth < 0 ? NULL : isl_space_set_alloc(context->ctx_, 0, 0);
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


static  std::tuple<isl_union_map*, isl_union_set*, isl_multi_union_pw_aff*>
generateCopyScheduleClean(TestContext* context, bool forward)
{
  struct pet_array* pa = context->petScop_->arrays[0];
  isl_multi_pw_aff *mpa;
  isl_multi_union_pw_aff *mupa;
  
  isl_space* space = isl_set_get_space(pa->extent);
  space = isl_space_from_range(space);
  space = isl_space_add_dims(space, isl_dim_in, 0);
  space = isl_space_wrap(space);
  space = isl_space_map_from_set(space);
  isl_id* id = isl_id_alloc(context->ctx_, forward ? "read" : "write", nullptr);
  space = isl_space_set_tuple_id(space, isl_dim_in, id);
  space = isl_space_domain(space);

  space = isl_space_map_from_set(space);
  mpa = isl_multi_pw_aff_identity(space);
  mpa = isl_multi_pw_aff_range_factor_range(mpa);
  mupa = isl_multi_union_pw_aff_from_multi_pw_aff(mpa);

  isl_union_map *access = isl_union_map_copy(context->s_->reads.get());
  isl_union_set* range = isl_union_map_range(access);


  isl_map* extentMap = isl_map_from_range(isl_set_copy(pa->extent));
  isl_union_map* extentUnionMap = isl_union_map_from_map(extentMap);
  
  isl_union_map* intersection = isl_union_map_intersect_range(isl_union_map_copy(extentUnionMap), isl_union_set_copy(range));
  isl_union_set* wrapped_union_map = isl_union_map_wrap(intersection);

  isl_union_map* union_wrapped_map_from_set = isl_union_map_from_range(wrapped_union_map);

  isl_map* wrapped_map_from_set = isl_map_from_union_map(union_wrapped_map_from_set);
  wrapped_map_from_set = isl_map_set_tuple_id(wrapped_map_from_set, isl_dim_out, id);

  isl_union_map* final_map = isl_union_map_from_map(wrapped_map_from_set);

  isl_union_set* filter = isl_union_map_range(isl_union_map_copy(final_map));
  filter = isl_union_set_coalesce(filter);

  isl_union_set* domain = isl_union_map_range(final_map);
  access = isl_union_set_wrapped_domain_map(domain);
  access = isl_union_map_reverse(access);
  access = isl_union_map_coalesce(access);

  return std::make_tuple(access, filter, mupa);
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

static void transform(isl_schedule_node* node, TestContext* context)
{
  //1) Match and transform for kernel code
  
  
  //2) Basic transformation
  // Match for :
  // mark (isKernel,
  //   filter(
  //     band(
  //       leaf())))

  // Change THIS part to :
  // kernelAnnotation() -> mark node ?
  // toDeviceAnnotation(DDRMapping) -> definitely not a mark node
  // extension(fromDevice, toDevice
  //   sequence(
  //     filter(toDevice
  //       leaf()))
  //     filter(<the same> 
  //       extensionAnnotation() -> mark node ?
  //       extension(readArray, writeArray
  //         sequence(
  //           filter(readArray
  //             scheduleAnnotation() -> mark node ?
  //               band(partialScheduleCopy()
  //                 leaf()))
  //           filter(<the same>
  //             scheduleAnnotation() -> mark node ?
  //               band(<the same>
  //                leaf()))
  //           filter(writeArray
  //             scheduleAnnotation() -> mark node ?   
  //             band(partialScheduleCopy()
  //               leaf()))
  //      filter(fromDevice
  //        leaf())
  //   )
  // )

  // assert node type is domain type

  // 1) get all nodes we want to modify
  
  node = isl_schedule_node_map_descendant_bottom_up(node, differentiateSchedule,
                                              (static_cast<void *>(context)));
  // construct annotations to insert
  // we don't need a special structure for kernel
  // maybe we need just set a "kernel"+number
  
  // matched nodes point to marker nodes

  // 2) Determine the list of what we want to copy
  isl_union_set_list* listToTransfer = isl_union_set_list_alloc(context->ctx_, 0);
  isl_union_set* readSet = isl_union_map_range(isl_union_map_copy(context->s_->reads.copy()));
  isl_union_set* writeSet = isl_union_map_range(isl_union_map_copy(context->s_->mayWrites.copy()));
  listToTransfer = isl_union_set_list_add(listToTransfer, readSet);
  listToTransfer = isl_union_set_list_add(listToTransfer, writeSet);
  isl_union_set* arraysToTransfer = isl_union_set_list_union(isl_union_set_list_copy(listToTransfer));
  arraysToTransfer = isl_union_set_detect_equalities(arraysToTransfer);

  isl_union_set_dump(arraysToTransfer);
  // 3) Iterate through all found nodes
  for (int i = 0; i < 1; i++) {
    printf("MATCHED NODE\n");
    isl_schedule_node_dump(context->matched_nodes_.at(i));
    
    // generate annotations
    annotateStatement("kernel" + toString(i), "reqd_work_group_size", 1, 1, 1);
    annotateStatement("extension", "xcl_array_partition", "cyclic", 2, 1);
    annotateStatement("band1", "xcl_pipeline_loop");
    annotateStatement("band2", "xcl_pipeline_loop");
    annotateStatement("band3", "xcl_pipeline_loop");
    std::tuple<isl_union_map*, isl_union_set*, isl_multi_union_pw_aff*> forCopyForward =
      generateCopyScheduleClean(context, 1);
    std::tuple<isl_union_map*, isl_union_set*, isl_multi_union_pw_aff*> forCopyBackward =
      generateCopyScheduleClean(context, 0);

    //isl_union_map_union();
    
    isl_union_map* transferForward = createCopyNode(1, arraysToTransfer,isl_schedule_node_copy(context->matched_nodes_.at(i)), context);
    isl_union_map* transferBackward = createCopyNode(0, arraysToTransfer, isl_schedule_node_copy(context->matched_nodes_.at(i)), context);
    isl_union_set* transferForwardFilter = isl_union_map_range(isl_union_map_copy(transferForward));
    isl_union_set* transferBackwardFilter = isl_union_map_range(isl_union_map_copy(transferBackward));

    

    isl_union_map* unionTransfer = isl_union_map_union(transferForward, transferBackward);
    isl_union_map_dump(unionTransfer);

    
    isl_union_map* unionCopy = isl_union_map_union(std::get<0>(forCopyForward), std::get<0>(forCopyBackward));
    isl_union_map_dump(unionCopy);

    isl_schedule_node* previousFilterNode = isl_schedule_node_parent(isl_schedule_node_copy(context->matched_nodes_.at(i)));
    printf("%i\n", isl_schedule_node_get_type(previousFilterNode));
    isl_union_set* previousFilter = isl_schedule_node_filter_get_filter(isl_schedule_node_copy(previousFilterNode));

    isl_schedule_node* previousBandNode = isl_schedule_node_child(isl_schedule_node_copy(context->matched_nodes_.at(i)), 0);
    isl_multi_union_pw_aff* previousBandNodeSchedule = isl_schedule_node_get_prefix_schedule_multi_union_pw_aff(previousBandNode);


    /*   create cpp objects */
    isl::union_map cppUnionTransfer = isl::manage(unionTransfer);
    isl::union_set cppTransferForwardFilter = isl::manage(transferForwardFilter);
    isl::union_set cppPreviousFilter = isl::manage(previousFilter);
    isl::union_map cppUnionCopy = isl::manage(unionCopy);

    isl::union_set cppCopyForward1 = isl::manage(std::get<1>(forCopyForward));
    isl::multi_union_pw_aff cppCopyForward2 = isl::manage(std::get<2>(forCopyForward));

    isl::union_set cppPreviousFilter2 = isl::manage(previousFilter);
    isl::multi_union_pw_aff cppPreviousBandNodeSchedule = isl::manage(previousBandNodeSchedule);

    isl::union_set cppCopyBackward1 = isl::manage(std::get<1>(forCopyBackward));
    isl::multi_union_pw_aff cppCopyBackward2 = isl::manage(std::get<2>(forCopyBackward));

    isl::union_set cppTransferBackwardFilter = isl::manage(transferBackwardFilter);
    
    
    using namespace builders;
    auto builder = extension(cppUnionTransfer,
		     sequence(
		       filter(cppTransferForwardFilter),
		       filter(cppPreviousFilter,
			 extension(cppUnionCopy,
		       	   sequence(
			     filter(cppCopyForward1,
		       	       band(cppCopyForward2
		       	       )
		       	     ),
		             filter(cppPreviousFilter2,
			       band(cppPreviousBandNodeSchedule
                               )
			     ),
			     filter(cppCopyBackward1,
			       band(cppCopyBackward2
			       )
                             )
                           )
		         )
		       ),
		       filter(cppTransferBackwardFilter)
		     )
		   );
    
    
      //isl_schedule_node* after_cut = isl_schedule_node_cut(context->matched_nodes_.at(i));
      //isl_schedule_node_dump(after_cut);
    //root = transformedBuilder.insertAt(root);
    //root = root.parent();
    
    }
}
void runAllFlow(std::string fileName, bool computeSchedule) {

  //implement function which parses matcher library 
  //currently just add one matcher there
  //std::vector<ScheduleNodeMatcher> matchers;
  //parseMatcherLibrary(&matchers);
 
  // if kernel is marked already once, we should not mark it as a kernel again

  std::vector<isl::schedule_node> kernel_nodes;
  Scop S = Parser(fileName).getScop();

  /* to test the access ranges */

  isl_union_map *access = isl_union_map_copy(S.reads.get());
  isl_union_set* range = isl_union_map_range(access);
  printf("range of read accesses before reschedule\n");
  isl_union_set_dump(range);

  printf("\ndump all schedule\n\n"); 
  isl_schedule_node* oldNode = isl_schedule_get_root(S.schedule.get());
  isl_schedule_node_dump(oldNode);
  /*----*/
  
  
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

  sc = compute_schedule_constraints(sc, validity, coincidence, dep_raw, dep, proximity, &S);
  new_schedule = isl_schedule_constraints_compute_schedule(sc);

    //} else {
    /* determine properties of original schedule */
    // new_schedule = isl_schedule_copy(S.schedule.get());
    //  sc = compute_schedule_constraints(sc, validity, coincidence, dep_raw, dep, proximity, &S);
    // new_schedule = isl_schedule_map_schedule_node_bottom_up(new_schedule,
    //                                           &set_band_properties, sc);
  
  // printf("\ndump new schedule\n\n"); 
  isl_schedule_node* node = isl_schedule_get_root(new_schedule);
  //isl_schedule_node_dump(node);

  //node = isl_schedule_node_map_descendant_bottom_up(node, differentiateSchedule,
  //                                           (static_cast<void *>(&S)));  
  //printf("vector length %i\n", kernel_nodes.size());

  //printf("\ndump_schedule_with_mark_nodes\n");
  //isl_schedule_node_dump(node);

  transform(node, context);
  
  /* try to insert smth before mark node */
  printf("try to find mark nodes\n");

  //node = isl_schedule_node_map_descendant_bottom_up(node, insertCopyBackForwardMarkNodes,
  //                                            (static_cast<void *>(context)));
  //isl_schedule_node_dump(node);

  ///node = isl_schedule_node_map_descendant_bottom_up(node, standardMarker,
  //                                           (static_cast<void *>(&S)));
  //annotateArraysAndKernel(context);
  //auto newcpp = isl::manage(node).child(0);
  //isl_schedule_node_dump(newcpp.get());
  // generateCopyScheduleClean(newcpp.copy(), context);
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
  /*isl_union_set* set1 = isl_union_set_read_from_str(context->ctx_, "{ read[[] -> A[i0, i1]] : (i0 > 0 and i1 >= i0 and i1 <= 399) or (i0 >= 0 and i1 > i0 and i1 <= 398) or (i0 >= 0 and i1 > i0 and i1 <= 399) or (i0 <= 399 and i1 > 0 and i1 < i0) or (i0 <= 399 and i1 >= 0 and i1 <= -2 + i0) or (i0 <= 399 and i1 >= 0 and i1 < i0) or (i0 <= 399 and i1 >= 0 and i1 < i0) or (i1 = i0 and i0 >= 0 and i0 <= 398) }");
  set1 = isl_union_set_coalesce(set1);
  isl_union_set_dump(set1);
  
  isl_union_set* set2 = isl_union_set_read_from_str(context->ctx_, "{ read[[] -> A[i0, i1]] : (i0 >= 0 and i1 > i0 and i1 <= 398) or (i0 <= 399 and i1 > 0 and i1 < i0) or (i0 <= 399 and i1 >= 0 and i1 <= -2 + i0) or (i0 <= 399 and i1 >= 0 and i1 < i0) or (i1 = i0 and i0 >= 0 and i0 <= 398) or (i0 > 0 and i1 >= i0 and i1 <= 399) or (i0 >= 0 and i1 > i0 and i1 <= 399) or (i0 <= 399 and i1 >= 0 and i1 < i0) }");
  set2 = isl_union_set_coalesce(set2);
  isl_union_set_dump(set2);
  printf("%i\n", isl_union_set_is_equal(set1, set2));

  isl_union_map* map1 = isl_union_map_read_from_str(context->ctx_, "{ [] -> read[[] -> A[o0, o1]] : (o0 >= 0 and o1 > o0 and o1 <= 398) or (o0 <= 399 and o1 > 0 and o1 < o0) or (o0 <= 399 and o1 >= 0 and o1 <= -2 + o0) or (o0 <= 399 and o1 >= 0 and o1 < o0) or (o1 = o0 and o0 >= 0 and o0 <= 398) or (o0 > 0 and o1 >= o0 and o1 <= 399) or (o0 >= 0 and o1 > o0 and o1 <= 399) or (o0 <= 399 and o1 >= 0 and o1 < o0) }");
  isl_union_map* map2 = isl_union_map_read_from_str(context->ctx_, "{ [] -> read[[] -> A[o0, o1]] : o0 >= 0 and o1 <= 399 and o0 <= 399 and o1 >= 0 }");
  printf("result 2 : %i\n", isl_union_map_is_equal(map1, map2));*/
  
}

int main(int argc, char **argv) {
  bool computeSchedule = true;
  if (argc > 2 && !argv[2]) {
    computeSchedule = false;
  }
  runAllFlow(argv[1], computeSchedule);
}


