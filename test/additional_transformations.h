#ifndef ADDITIONAL_TRANSFORMATIONS_H
#define ADDITIONAL_TRANSFORMATIONS_H

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

#endif TEST_EXTENSION_H
