#ifndef TEST_DEPENDENCIES_H
#define TEST_DEPENDENCIES_H

static void compute_flow_dep(struct Scop *S) {
  isl_union_access_info *access;
  isl_union_flow *flow;
  isl_union_map *must_writes;

  access = isl_union_access_info_from_sink(isl_union_map_copy(S->reads.get()));
  must_writes = isl_union_map_copy(S->mustWrites.get());
  access = isl_union_access_info_set_kill(access, must_writes);
  access = isl_union_access_info_set_may_source(
      access, isl_union_map_copy(S->mayWrites.get()));
  access = isl_union_access_info_set_schedule(
      access, isl_schedule_copy(S->schedule.get()));
  flow = isl_union_access_info_compute_flow(access);

  auto may_dependence = isl::manage(isl_union_flow_get_may_dependence(flow));
  S->depFlow = may_dependence;
  auto live_in = isl::manage(isl_union_flow_get_may_no_source(flow));
  S->liveIn = live_in;
}

static void compute_dependencies(struct Scop *S) {
  isl_union_map *may_source, *dep_false;
  isl_union_access_info *access;
  isl_union_flow *flow;

  compute_flow_dep(S);

  may_source = isl_union_map_union(isl_union_map_copy(S->mayWrites.get()),
                                   isl_union_map_copy(S->reads.get()));
  access =
      isl_union_access_info_from_sink(isl_union_map_copy(S->mayWrites.get()));
  access = isl_union_access_info_set_kill(
      access, isl_union_map_copy(S->mustWrites.get()));
  access = isl_union_access_info_set_may_source(access, may_source);
  access = isl_union_access_info_set_schedule(
      access, isl_schedule_copy(S->schedule.get()));

  flow = isl_union_access_info_compute_flow(access);

  dep_false = isl_union_flow_get_may_dependence(flow);
  dep_false = isl_union_map_coalesce(dep_false);
  auto final_dep_false = isl::manage(dep_false);
  S->depFalse = final_dep_false;
}

static isl_schedule_constraints *compute_schedule_constraints(
    isl_schedule_constraints *sc, isl_union_map *validity,
    isl_union_map *coincidence, isl_union_map *dep_raw, isl_union_map *dep,
    isl_union_map *proximity, Scop *S) {
  sc =
      isl_schedule_constraints_on_domain(isl_union_set_copy(S->domain().get()));
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
#endif // TEST_DEPENDENSIES_H
