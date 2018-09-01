#include "parser.h"
#include "pet.h"

Parser::Parser(std::string Filename) : Filename(Filename) {}

/* Is "stmt" not a kill statement?
 */
static int is_not_kill(struct pet_stmt *stmt)
{
        return !pet_stmt_is_kill(stmt);
}


/* Collect the iteration domains of the statements in "scop" that
 * satisfy "pred".
 */
static __isl_give isl_union_set *collect_domains(struct pet_scop *scop,
        int (*pred)(struct pet_stmt *stmt))
{
        int i;
        isl_set *domain_i;
        isl_union_set *domain;

        if (!scop)
                return NULL;

        domain = isl_union_set_empty(isl_set_get_space(scop->context));

        for (i = 0; i < scop->n_stmt; ++i) {
                struct pet_stmt *stmt = scop->stmts[i];

                if (!pred(stmt))
                        continue;

                if (stmt->n_arg > 0)
                        isl_die(isl_union_set_get_ctx(domain),
                                isl_error_unsupported,
                                "data dependent conditions not supported",
                                return isl_union_set_free(domain));

                domain_i = isl_set_copy(scop->stmts[i]->domain);
                domain = isl_union_set_add_set(domain, domain_i);
        }

        return domain;
}


/* Collect the iteration domains of the statements in "scop",
 * skipping kill statements.
 */
static __isl_give isl_union_set *collect_non_kill_domains(struct pet_scop *scop)
{
        return collect_domains(scop, &is_not_kill);
}

Scop Parser::getScop() {
  Scop S;

  isl_ctx *ctx = isl_ctx_alloc_with_pet_options();
  pet_scop *scop = pet_scop_extract_from_C_source(ctx, Filename.c_str(), NULL);
  S.schedule = isl::manage(pet_scop_get_schedule(scop));
  S.reads = isl::manage(pet_scop_get_tagged_may_reads(scop));
  S.mayWrites = isl::manage(pet_scop_get_tagged_may_writes(scop));
  S.mustWrites = isl::manage(pet_scop_get_tagged_must_writes(scop));
  S.context = isl::manage(pet_scop_get_context(scop));
  S.kills = isl::manage(pet_scop_get_must_kills(scop));
  S.nonKillDomain = isl::manage(collect_non_kill_domains(scop));

  return S;
}
