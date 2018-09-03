#ifndef TEST_DEPENDENCIES_H
#define TEST_DEPENDENCIES_H

static void compute_nontagged_flow_dep(struct Scop *S) {
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

static void compute_tagger(struct Scop* S)
{
  isl_union_map *tagged; 
  isl_union_pw_multi_aff *tagger;

  tagged = isl_union_map_copy(S->reads.get());
  tagged = isl_union_map_union(tagged,
                          isl_union_map_copy(S->mayWrites.get()));
  //tagged = isl_union_map_union(tagged,
  //                        isl_union_map_copy(ps->tagged_must_kills));
  tagged = isl_union_map_universe(tagged);
  tagged = isl_union_set_unwrap(isl_union_map_domain(tagged));

  tagger = isl_union_map_domain_map_union_pw_multi_aff(tagged);

  S->tagger = tagger;
}


static void compute_tagged_flow_dep(struct Scop *S) {
  isl_union_pw_multi_aff *tagger;
  isl_schedule *schedule;
  isl_union_map *live_in;
  isl_union_access_info *access;
  isl_union_flow *flow;
  isl_union_map *must_source;
  isl_union_map *kills;
  isl_union_map *tagged_flow;

  tagger = S->tagger;
  schedule = isl_schedule_copy(S->schedule.get());
  schedule = isl_schedule_pullback_union_pw_multi_aff(schedule, tagger);
  //kills = isl_union_map_copy(ps->tagged_must_kills);
  must_source = isl_union_map_copy(S->mustWrites.get());
  //kills = isl_union_map_union(kills, must_source);
  access = isl_union_access_info_from_sink(
                          isl_union_map_copy(S->reads.get()));
  access = isl_union_access_info_set_kill(access, must_source/*kills*/);
  access = isl_union_access_info_set_may_source(access,
                          isl_union_map_copy(S->mayWrites.get()));
  access = isl_union_access_info_set_schedule(access, schedule);
  flow = isl_union_access_info_compute_flow(access);
  tagged_flow = isl_union_flow_get_may_dependence(flow);
  isl::union_map cpp_tagged_flow = isl::manage(tagged_flow);
  S->depFlow = cpp_tagged_flow;
  live_in = isl_union_flow_get_may_no_source(flow);
  isl::union_map cpp_live_in = isl::manage(isl_union_map_domain_factor_domain(live_in));
  S->liveIn = cpp_live_in;
}

static void derive_flow_dep_from_tagged_flow_dep(struct Scop* S)
{
  isl_union_map* dep_flow = S->depFlow.get();
  dep_flow = isl_union_map_factor_domain(isl_union_map_copy(dep_flow));
  S->depFlow = isl::manage(dep_flow);
}

static void compute_dependencies(struct Scop *S) {
  isl_union_map *may_source, *dep_false;
  isl_union_access_info *access;
  isl_union_flow *flow;

  compute_tagger(S);
  compute_tagged_flow_dep(S);
  derive_flow_dep_from_tagged_flow_dep(S);

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

  printf("coincidence\n");
  isl_union_map_dump(coincidence);
  printf("validity\n");
  isl_union_map_dump(validity);
  printf("proximity\n");
  isl_union_map_dump(proximity);
  sc = isl_schedule_constraints_set_validity(sc, validity);
  sc = isl_schedule_constraints_set_coincidence(sc, coincidence);
  sc = isl_schedule_constraints_set_proximity(sc, proximity);

  return sc;
}
#endif // TEST_DEPENDENSIES_H
