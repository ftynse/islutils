#include <islutils/builders.h>
#include <islutils/matchers.h>
#include <islutils/parser.h>
#include <string>
#include <vector>
#include "gtest/gtest.h"


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
     auto cpp_node = isl::manage_copy(Node);
     auto new_node =  insertKernelMarker.insertAt(cpp_node);
     isl_schedule_node_dump(new_node.get());
     return isl_schedule_node_copy(new_node.get());
  }
  
  return Node;
}

static isl_schedule_node* insertCopyBeforeMarkNodes(isl_schedule_node* Node, void* User)
{
  isl_union_map* test_map = static_cast<isl_union_map*>(User);
  if (isl_schedule_node_get_type(Node) == isl_schedule_node_mark) {
    using namespace builders;
    auto insertCopyNode = extension(isl::manage(test_map));
    auto cpp_node = isl::manage(Node);
    auto new_node =  insertCopyNode.insertAt(cpp_node);
    isl_schedule_node_dump(new_node.get());
    return isl_schedule_node_copy(new_node.parent().parent().parent().get());
  }
  return Node;
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

void runAllFlow(std::string fileName, bool computeSchedule) {

  //implement function which parses matcher library 
  //currently just add one matcher there
  //std::vector<ScheduleNodeMatcher> matchers;
  //parseMatcherLibrary(&matchers);
 

  std::vector<isl::schedule_node> kernel_nodes;
  Scop S = Parser(fileName).getScop();

  isl_schedule_node_dump(isl_schedule_get_root(S.schedule.get()));

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

  isl_union_map* test_map = isl_union_map_copy(S.mustWrites.get());
  auto cpp_map = isl::manage(test_map);
  isl_schedule_node_map_descendant_bottom_up(node, insertCopyBeforeMarkNodes,
                                             (static_cast<void *>(test_map)));
  
  /* this is how to insert extension */
  //auto cpp_node = isl::manage(node);
  //cpp_node = cpp_node.child(0);
  //isl_schedule_node *graft;
  //graft = isl_schedule_node_from_extension(test_map);
  //node = isl_schedule_node_graft_before(cpp_node.get(), graft);  
  //isl_schedule_node_dump(node);
 
  /* this is how to insert it with builders */
  //using namespace builders;
  //auto insertCopyNode = extension(cpp_map);
  //auto cpp_node = isl::manage(node);
  //cpp_node = cpp_node.child(0).child(0).child(0).child(0);
  //cpp_node = insertCopyNode.insertAt(cpp_node);
  //isl_schedule_node_dump(cpp_node.parent().parent().parent().get());
}



int main(int argc, char **argv) {
  bool computeSchedule = true;
  if (argc > 2 && !argv[2]) {
    computeSchedule = false;
  }
  runAllFlow(argv[1], computeSchedule);
}


