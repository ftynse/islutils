#include "parser.h"
#include "pet.h"

Parser::Parser(std::string Filename) : Filename(Filename) {}

Scop Parser::getScop() {
  Scop S;

  isl_ctx *ctx = isl_ctx_alloc_with_pet_options();

  //isl_options_set_ast_build_detect_min_max(ctx, 1);
  //isl_options_set_ast_print_macro_once(ctx, 1);
  //isl_options_set_schedule_whole_component(ctx, 0);
  //isl_options_set_schedule_maximize_band_depth(ctx, 1);
  //isl_options_set_schedule_maximize_coincidence(ctx, 1);

  pet_scop *scop = pet_scop_extract_from_C_source(ctx, Filename.c_str(), NULL);
  S.schedule = isl::manage(pet_scop_get_schedule(scop));
  S.taggedReads = isl::manage(pet_scop_get_tagged_may_reads(scop));
  S.taggedMayWrites = isl::manage(pet_scop_get_tagged_may_writes(scop));
  S.taggedMustWrites = isl::manage(pet_scop_get_tagged_must_writes(scop));
  S.reads = isl::manage(pet_scop_get_may_reads(scop)); 
  S.mayWrites = isl::manage(pet_scop_get_may_writes(scop));
  S.mustWrites = isl::manage(pet_scop_get_must_writes(scop));
  return S;
}
