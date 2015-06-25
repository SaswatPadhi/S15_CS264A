#include <ctype.h>
#include <unistd.h>

#include "sat_api.h"

/******************************************************************************
 * We explain here the functions you need to implement
 *
 * Rules:
 * --You cannot change any parts of the function signatures
 * --You can/should define auxiliary functions to help implementation
 * --You can implement the functions in different files if you wish
 * --That is, you do not need to put everything in a single file
 * --You should carefully read the descriptions and must follow each requirement
 ******************************************************************************/


/******************************************************************************
 * Constructors & destructors
 ******************************************************************************/

void init_Var(Var*, c2dSize);
void free_Var(Var*);

void init_Lit(Lit*, c2dLiteral, Var*);
void free_Lit(Lit*);

void init_Clause(Clause*, c2dSize, c2dSize);
void free_Clause(Clause*);

LitListNode* init_LLN(Lit*);
void free_LLN(LitListNode*);

ClauseListNode* init_CLN(Clause*);
void free_CLN(ClauseListNode*);


/******************************************************************************
 * Variables
 ******************************************************************************/

const int pos = true;
const int neg = false;

void init_Var(Var* var, c2dSize id) {
  var->id = id;
  var->mark = false;
  var->decision.level = 0;
  init_Lit((var->lit) + pos, id, var);
  init_Lit((var->lit) + neg, -(c2dLiteral)id, var);
}

void free_Var(Var* var) {
  free_Lit((var->lit) + pos);
  free_Lit((var->lit) + neg);
}

void set_Var_Decision(Var *var, c2dSize level, BOOLEAN value, Clause* implier) {
  var->decision.level = level;
  var->decision.value = value;
  var->decision.implied_by = implier;
}

void unset_Var_Decision(Var* var) {
  var->decision.level = 0;
}

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize index, const SatState* sat_state) {
  return (sat_state->vars.item + index - 1);
}

//returns the index of a variable
c2dSize sat_var_index(const Var* var) {
  return var->id;
}

//returns the variable of a literal
Var* sat_literal_var(const Lit* lit) {
  return lit->var;
}

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var* var) {
  return var->decision.level > 0;
}

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var) {
  for(Clause** clause = ARRAY_BEGIN(var->lit[pos].appears_in); clause < ARRAY_S_END(var->lit[pos].appears_in); ++clause)
    if(!sat_subsumed_clause(*clause)) return false;
  for(Clause** clause = ARRAY_BEGIN(var->lit[neg].appears_in); clause < ARRAY_S_END(var->lit[neg].appears_in); ++clause)
    if(!sat_subsumed_clause(*clause)) return false;

  return true;
}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {
  return sat_state->vars.count;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {
  return var->lit[pos].appears_in.count + var->lit[neg].appears_in.count;
}

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var) {
  if(index < var->lit[pos].appears_in.count)
    return var->lit[pos].appears_in.item[index];
  else
    return var->lit[neg].appears_in.item[index - var->lit[pos].appears_in.count];
}

/******************************************************************************
 * Literals
 ******************************************************************************/

void init_Lit(Lit* lit, c2dLiteral id, Var* var) {
  lit->id = id;
  lit->var = var;
  lit->appears_in.size = 0;
  lit->appears_in.item = NULL;
  LIST_INIT(&(lit->watch_list));
  LIST_INIT(&(lit->learned_list));
}

void free_Lit(Lit* lit) {
  FREE_ARRAY(lit->appears_in);

  ClauseListNode* cln;
  while(cln = lit->watch_list.lh_first) {
    LIST_REMOVE(cln, link);
    free_CLN(cln);
  }

  while(cln = lit->learned_list.lh_first) {
    LIST_REMOVE(cln, link);
    free_CLN(cln);
  }
}

LitListNode* init_LLN(Lit* lit) {
  LitListNode* lln = malloc(sizeof(LitListNode));
    lln->lit = lit;
  return lln;
}

void free_LLN(LitListNode* lln) {
  free(lln);
}

void pprint_Lit(Lit* lit, BOOLEAN decision_info) {
  fprintf(stderr, "  %ld", lit->id);
  if(!decision_info) fprintf(stderr, "  ");
  else {
    fprintf(stderr, " (l%lu, c%lu) --- ", lit->var->decision.level,
            (lit->var->decision.level && lit->var->decision.implied_by)
              ? lit->var->decision.implied_by->id : 0);
    fprintf(stderr, " [");
    for(ClauseListNode* cln = lit->watch_list.lh_first; cln != NULL; cln = cln->link.le_next)
      fprintf(stderr, " %lu ", cln->clause->id);
    fprintf(stderr, "]\n");
  }
}

Lit* sat_unwatched_literal(Clause* clause, SatState* sat_state) {
  Lit** l = ARRAY_BEGIN(clause->lits);
  for(; l < ARRAY_S_END(clause->lits); ++l) {
    if(sat_instantiated_var((*l)->var)) {
      if(sat_implied_literal(*l)) {
        sat_subsume_clause(clause, sat_state);
        return NULL;
      }
      continue;
    }
    if(*l == clause->watch_a || *l == clause->watch_b)  continue;
    break;
  }
  return (l < ARRAY_S_END(clause->lits) ? *l : NULL);
}

BOOLEAN sat_contradiction(Clause* implier, SatState* sat_state) {
  set_Var_Decision(&(sat_state->contradiction), sat_state->level, true, implier);
  sat_state->decided_literals.item[sat_state->decided_literals.count++] = (sat_state->contradiction.lit)+pos;
  return false;
}

BOOLEAN set_Lit_Decision(Lit* lit, Clause* implier, SatState* sat_state) {
  if(!sat_instantiated_var(lit->var)) {
    set_Var_Decision(lit->var, sat_state->level, lit->id > 0, implier);
    sat_state->decided_literals.item[sat_state->decided_literals.count++] = lit;
  } else if(!(sat_implied_literal(lit)))
    return sat_contradiction(implier, sat_state);
  else
    sat_subsume_clause(implier, sat_state);
  return true;
}

BOOLEAN propagate_lit_decision(Lit* lit, SatState* sat_state) {
  Var* var = lit->var;

  for(Clause** clause = ARRAY_BEGIN(lit->appears_in); clause < ARRAY_S_END(lit->appears_in); ++clause)
    sat_subsume_clause(*clause, sat_state);
  for(ClauseListNode* cln = lit->learned_list.lh_first; cln != NULL; cln = cln->link.le_next)
    sat_subsume_clause(cln->clause, sat_state);

  BOOLEAN delta = false;
  Lit* clit = (var->lit) + (lit->id < 0);
  for(ClauseListNode* cln = clit->watch_list.lh_first; cln != NULL; cln = delta ? cln : cln->link.le_next, delta = false) {
    Clause* clause = cln->clause;
    if(sat_subsumed_clause(clause)) continue;

    Lit* l = sat_unwatched_literal(clause, sat_state);
    if(sat_subsumed_clause(clause)) continue;

    if(l) {
      if(clit == clause->watch_a)     clause->watch_a = l;
      else                            clause->watch_b = l;

      ClauseListNode* ncln = cln->link.le_next;
      LIST_REMOVE(cln, link);
      LIST_INSERT_HEAD(&(l->watch_list), cln, link);

      delta = true;
      cln = ncln;
    } else {
      Lit* other_lit = (clit == clause->watch_a ? clause->watch_b : clause->watch_a);
      if(other_lit == NULL || sat_instantiated_var(other_lit->var)) {
        if(other_lit && sat_implied_literal(other_lit))
          sat_subsume_clause(clause, sat_state);
        else
          return sat_contradiction(clause, sat_state);
      } else {
        if(!set_Lit_Decision(other_lit, clause, sat_state)) return false;
        sat_state->propagate_literals.item[sat_state->propagate_literals.count++] = other_lit;
      }
    }
  }

  return true;
}

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state) {
  return (sat_state->vars.item[abs(index)-1].lit) + (index > 0);
}

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit) {
  return lit->id;
}

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var) {
  return (((Var*) var)->lit) + pos;
}

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var) {
  return (((Var*) var)->lit) + neg;
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {
  return sat_instantiated_var(lit->var) && (lit->id < 0 ^ lit->var->decision.value);
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {
  ++sat_state->level;

  ClauseListNode* cln = init_CLN(NULL);
  LIST_INSERT_HEAD(&(sat_state->subsumed_clauses), cln, link);

  BOOLEAN passed = false;
  if(passed = set_Lit_Decision(lit, NULL, sat_state)) {
    sat_state->propagate_literals.item[sat_state->propagate_literals.count++] = lit;
    passed = sat_unit_resolution(sat_state);
  }

  if(!passed)
    return sat_build_asserting_clause(sat_state);

  return NULL;
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
  sat_undo_unit_resolution(sat_state);
  --sat_state->level;
}

/******************************************************************************
 * Clauses
 ******************************************************************************/

void init_Clause(Clause* clause, c2dSize id, c2dSize lit_count) {
  clause->id = id;
  clause->mark = false;
  clause->is_subsumed = false;
  clause->watch_a = clause->watch_b = NULL;
  INIT_ARRAY(clause->lits, Lit*, lit_count);
}

void free_Clause(Clause* clause) {
  FREE_ARRAY(clause->lits);
}

void pprint_Clause(Clause* clause, BOOLEAN all_info) {
  fprintf(stderr, "    %lu ", clause->id);
  if(all_info)
    fprintf(stderr, "{%c} [%ld,%ld] ", sat_subsumed_clause(clause) ? 'Y' : 'N',
                    clause->watch_a ? clause->watch_a->id : 0,
                    clause->watch_b ? clause->watch_b->id : 0);
  fprintf(stderr, "===> ");
  for(Lit** lit = ARRAY_BEGIN(clause->lits); lit < ARRAY_S_END(clause->lits); ++lit)
    pprint_Lit(*lit, false);
  fprintf(stderr, "\n");
}

ClauseListNode* init_CLN(Clause* clause) {
  ClauseListNode* cln = malloc(sizeof(ClauseListNode));
    cln->clause = clause;
  return cln;
}

void free_CLN(ClauseListNode* cln) {
  free(cln);
}

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {
  return sat_state->clauses.item + (index-1);
}

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause) {
  return clause->id;
}

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause) {
  return ARRAY_BEGIN(clause->lits);
}

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause) {
  return clause->lits.count;
}

void sat_subsume_clause(Clause* clause, SatState* sat_state) {
  if(!clause->is_subsumed) {
    clause->is_subsumed = true;
    ClauseListNode* cln = init_CLN(clause);
    LIST_INSERT_HEAD(&(sat_state->subsumed_clauses), cln, link);
  }
}

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause) {
  return clause->is_subsumed;
}

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state) {
  return sat_state->clauses.count;
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {
  return sat_state->learned_clauses.lh_first ? sat_state->learned_clauses.lh_first->clause->id - sat_state->clauses.count : 0;
}

Var* dominator(Var* var1, Var* var2) {
  while(var1 != var2) {
    while(var1->decision.order < var2->decision.order)
      var2 = var2->decision.dominator;
    while(var2->decision.order < var1->decision.order)
      var1 = var1->decision.dominator;
  }
  return var1;
}

Var* sat_compute_UIP(SatState* sat_state) {
  c2dSize last_decision = sat_state->decided_literals.count - 1;
  while(sat_state->decided_literals.item[last_decision]->var->decision.implied_by) {
    sat_state->decided_literals.item[last_decision]->var->decision.order = last_decision;
    sat_state->decided_literals.item[last_decision]->var->decision.dominator = NULL;
    --last_decision;
  }

  Lit** lit = ARRAY_BEGIN(sat_state->decided_literals) + last_decision;
  (*lit)->var->decision.dominator = (*lit)->var;
  (*lit)->var->decision.order = last_decision;

  for(++lit; lit < ARRAY_C_END(sat_state->decided_literals); ++lit) {
    for(Lit** pred = ARRAY_BEGIN((*lit)->var->decision.implied_by->lits); pred < ARRAY_S_END((*lit)->var->decision.implied_by->lits); ++pred) {
      if((*pred)->var->decision.level != sat_state->level || (*pred) == (*lit))
        continue;

      if((*lit)->var->decision.dominator == NULL)   (*lit)->var->decision.dominator = (*pred)->var;
      else                                          (*lit)->var->decision.dominator = dominator((*pred)->var, (*lit)->var->decision.dominator);
    }
  }

  return sat_state->contradiction.decision.dominator;
}

//builds an asserting clause from current SatState
Clause* sat_build_asserting_clause(SatState* sat_state) {
  Clause* clause = malloc(sizeof(Clause));

  Var* uip = sat_compute_UIP(sat_state);
  c2dSize clause_size = 1;

  Lit* dlit;
  c2dSize post_uip = sat_state->decided_literals.count - 1;
  while((dlit = sat_state->decided_literals.item[post_uip])->var != uip) {
    if(dominator(uip, dlit->var->decision.dominator) == uip) {
      for(Lit** lit = ARRAY_BEGIN(dlit->var->decision.implied_by->lits); lit < ARRAY_S_END(dlit->var->decision.implied_by->lits); ++lit) {
        if((*lit)->var->decision.level < sat_state->level && !sat_state->marks[(*lit)->var->id]) {
          sat_state->marks[(*lit)->var->id] = true;
          ++clause_size;
        }
      }
    }
    --post_uip;
  }

  init_Clause(clause, (sat_state->learned_clauses.lh_first ? sat_state->learned_clauses.lh_first->clause->id : sat_state->clauses.size) + 1, clause_size);
  clause->assertion_level = 1;

  if(clause_size > 1) {
    clause->lits.item[clause->lits.count++] = (uip->lit) + (!(uip->decision.value));

    for(Lit** lit = ARRAY_BEGIN(sat_state->decided_literals); (*lit)->var->decision.level < sat_state->level; ++lit) {
      if(sat_state->marks[(*lit)->var->id]) {
        sat_state->marks[(*lit)->var->id] = false;
        clause->lits.item[clause->lits.count++] = ((*lit)->var->lit) +(!((*lit)->var->decision.value));
        clause->assertion_level = ((*lit)->var->decision.level > clause->assertion_level) ? (*lit)->var->decision.level : clause->assertion_level;
      }
    }
  } else
    clause->lits.item[clause->lits.count++] = (uip->lit) + (!(uip->decision.value));

  return clause;
}

c2dSize cnt = 0;

//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {
  ClauseListNode* cln = init_CLN(clause);
  LIST_INSERT_HEAD(&(sat_state->learned_clauses), cln, link);

  for(Lit** lit = ARRAY_BEGIN(clause->lits); lit < ARRAY_S_END(clause->lits); ++lit) {
    ClauseListNode* cln = init_CLN(clause);
    LIST_INSERT_HEAD(&((*lit)->learned_list), cln, link);
  }

  clause->watch_a = clause->lits.item[0];
  clause->watch_b = clause->lits.item[clause->lits.size-1];

  BOOLEAN passed = true;
  if(passed = set_Lit_Decision(clause->watch_a, clause, sat_state)) {
    sat_state->propagate_literals.item[sat_state->propagate_literals.count++] = clause->watch_a;

    cln = init_CLN(clause);
    LIST_INSERT_HEAD(&(clause->watch_a->watch_list), cln, link);
    cln = init_CLN(clause);
    LIST_INSERT_HEAD(&(clause->watch_b->watch_list), cln, link);

    passed = sat_unit_resolution(sat_state);
  }

  if(!passed) {
    if(sat_state->level > 1)
      return sat_build_asserting_clause(sat_state);
    else
      return &(sat_state->false_clause);
  }

  return NULL;
}

/******************************************************************************
 * A SatState should keep track of pretty much everything you will need to
 * condition/uncondition variables, perform unit resolution, and do clause learning
 *
 * Given an input cnf file you should construct a SatState
 *
 * This construction will depend on how you define a SatState
 * Still, you should at least do the following:
 * --read a cnf (in DIMACS format, possible with weights) from the file
 * --initialize variables (n of them)
 * --initialize literals  (2n of them)
 * --initialize clauses   (m of them)
 *
 * Once a SatState is constructed, all of the functions that work on a SatState
 * should be ready to use
 *
 * You should also write a function that frees the memory allocated by a
 * SatState (sat_state_free)
 ******************************************************************************/

void skip_comments(FILE *fp) {
  char ignore[1024], cursor = fgetc(fp);
  while(cursor == 'c' || cursor == '%' || cursor == '\n') {
    fgets(ignore, sizeof(ignore), fp);
    cursor = fgetc(fp);
  }
  if(cursor != EOF) ungetc(cursor, fp);
}

void read_clause(Clause* clause, SatState* sat_state, FILE* fp) {
  char line[32767];
  c2dLiteral val;
  BOOLEAN end = false;

  do {
    skip_comments(fp);
    fgets(line, sizeof(line), fp);

    char* token = strtok(line, " \t\n");
    while(token) {
      val = strtol(token, NULL, 10);
      if(!val) {
        end = true;
        break;
      }

      Var* var = sat_state->vars.item + (abs(val)-1);
      var->lit[val>0].appears_in.size++;
      sat_state->decided_literals.item[sat_state->decided_literals.count++] = (var->lit) + (val>0);
      token = strtok(NULL, " \t\n");
    }
  } while(!end);

  init_Clause(clause, ++sat_state->clauses.count, sat_state->decided_literals.count);

  for(Lit** lit = ARRAY_BEGIN(sat_state->decided_literals); lit < ARRAY_C_END(sat_state->decided_literals); ++lit)
    clause->lits.item[clause->lits.count++] = *lit;

  sat_state->decided_literals.count = 0;
}

SatState* read_sat_cnf(SatState* sat_state, FILE *fp) {
  skip_comments(fp);
  fscanf(fp, "p cnf %lu %lu\n", &sat_state->vars.size, &sat_state->clauses.size);

  INIT_ARRAY(sat_state->vars, Var, sat_state->vars.size);
  for(Var* v = ARRAY_BEGIN(sat_state->vars); v < ARRAY_S_END(sat_state->vars); ++v)
    init_Var(v, ++sat_state->vars.count);

  LIST_INIT(&(sat_state->learned_clauses));
  LIST_INIT(&(sat_state->subsumed_clauses));

  INIT_ARRAY(sat_state->propagate_literals, Lit*, sat_state->vars.size);
  INIT_ARRAY(sat_state->decided_literals, Lit*, sat_state->vars.size + 1);

  INIT_ARRAY(sat_state->clauses, Clause, sat_state->clauses.size);
  for(Clause* clause = ARRAY_BEGIN(sat_state->clauses); clause < ARRAY_S_END(sat_state->clauses); ++clause) {
    read_clause(clause, sat_state, fp);

    clause->watch_a = *(clause->lits.item);
    ClauseListNode* cln = init_CLN(clause);
    LIST_INSERT_HEAD(&(clause->watch_a->watch_list), cln, link);

    if(clause->lits.count == 1) {
      clause->watch_b = NULL;
    } else {
      clause->watch_b = *(clause->lits.item + 1);
      cln = init_CLN(clause);
      LIST_INSERT_HEAD(&(clause->watch_b->watch_list), cln, link);
    }
  }

  for(Var* var = ARRAY_BEGIN(sat_state->vars); var < ARRAY_S_END(sat_state->vars); ++var) {
    if(var->lit[pos].appears_in.size)  INIT_ARRAY(var->lit[pos].appears_in, Clause*, var->lit[pos].appears_in.size);
    if(var->lit[neg].appears_in.size)  INIT_ARRAY(var->lit[neg].appears_in, Clause*, var->lit[neg].appears_in.size);
  }

  BOOLEAN passed = true;
  for(Clause* clause = ARRAY_BEGIN(sat_state->clauses); clause < ARRAY_S_END(sat_state->clauses); ++clause) {
    if(clause->lits.count > 1 || !passed) {
      for(Lit** lit = ARRAY_BEGIN(clause->lits); lit < ARRAY_S_END(clause->lits); ++lit)
        (*lit)->appears_in.item[(*lit)->appears_in.count++] = clause;
      continue;
    }

    clause->watch_a->appears_in.item[clause->watch_a->appears_in.count++] = clause;
    if(!(passed = set_Lit_Decision(clause->watch_a, clause, sat_state))) {
      --sat_state->decided_literals.count;
      clause->is_subsumed = false;
    }
    sat_state->propagate_literals.item[sat_state->propagate_literals.count++] = clause->watch_a;
  }

  return sat_state;
}

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* cnf_fname) {
  FILE* fp = fopen(cnf_fname, "r");

  SatState* sat_state = malloc(sizeof(SatState));
  sat_state->level = 1;
  init_Lit(sat_state->contradiction.lit + pos, 0, &(sat_state->contradiction));
  init_Clause(&(sat_state->false_clause), 0, 0);
  sat_state->false_clause.assertion_level = 0;

  read_sat_cnf(sat_state, fp);
  sat_state->marks = calloc(sat_state->vars.size + 1, sizeof(BOOLEAN));

  fclose(fp);
  return sat_state;
}

//frees the SatState
void sat_state_free(SatState* sat_state) {
  free_Clause(&(sat_state->false_clause));
  free_Lit(sat_state->contradiction.lit + pos);

  ClauseListNode* cln;
  while(cln = sat_state->subsumed_clauses.lh_first) {
    LIST_REMOVE(cln, link);
    free_CLN(cln);
  }

  while(cln = sat_state->learned_clauses.lh_first) {
    free_Clause(cln->clause);
    free(cln->clause);
    LIST_REMOVE(cln, link);
    free_CLN(cln);
  }

  for(Clause* clause = ARRAY_BEGIN(sat_state->clauses); clause < ARRAY_S_END(sat_state->clauses); ++clause)
    free_Clause(clause);
  FREE_ARRAY(sat_state->clauses);

  FREE_ARRAY(sat_state->decided_literals);

  for(Var* var = ARRAY_BEGIN(sat_state->vars); var < ARRAY_S_END(sat_state->vars); ++var)
    free_Var(var);
  FREE_ARRAY(sat_state->vars);

  FREE_ARRAY(sat_state->propagate_literals);

  free(sat_state->marks);

  free(sat_state);
}

void pprint_SatState(SatState* sat_state, BOOLEAN print_clauses) {
  fprintf(stderr, "STATE(%lu, %lu) @ %lu :\n", sat_state->vars.count, sat_state->clauses.count, sat_state->level);
  fprintf(stderr, "  Variables = \n");
  for(Var* var = ARRAY_BEGIN(sat_state->vars); var < ARRAY_S_END(sat_state->vars); ++var) {
    pprint_Lit(var->lit + pos, true);
    pprint_Lit(var->lit + neg, true);
  }
  fprintf(stderr, "  Decisions = ");
  for(Lit** lit = ARRAY_BEGIN(sat_state->decided_literals); lit < ARRAY_C_END(sat_state->decided_literals); ++lit) {
    if((*lit)->var->decision.implied_by == NULL) fprintf(stderr, "\n");
    pprint_Lit(*lit, false);
  }
  fprintf(stderr, "\n");
  if(print_clauses) {
    fprintf(stderr, "  Original Clauses : \n");
    for(Clause* clause = ARRAY_BEGIN(sat_state->clauses); clause < ARRAY_S_END(sat_state->clauses); ++clause)
      pprint_Clause(clause, true);
    fprintf(stderr, "  Learned Clauses : \n");
    for(ClauseListNode* cln = sat_state->learned_clauses.lh_first; cln != NULL; cln = cln->link.le_next)
      pprint_Clause(cln->clause, true);
    fprintf(stderr, "  Current Pending Propagations : \n");
    for(Lit** unit = ARRAY_BEGIN(sat_state->propagate_literals); unit < ARRAY_C_END(sat_state->propagate_literals); ++unit)
      pprint_Lit(*unit, false);
  }
}


/******************************************************************************
 * Given a SatState, which should contain data related to the current setting
 * (i.e., decided literals, subsumed clauses, decision level, etc.), this function
 * should perform unit resolution at the current decision level
 *
 * It returns 1 if succeeds, 0 otherwise (after constructing an asserting
 * clause)
 *
 * There are three possible places where you should perform unit resolution:
 * (1) after deciding on a new literal (i.e., in sat_decide_literal())
 * (2) after adding an asserting clause (i.e., in sat_assert_clause(...))
 * (3) neither the above, which would imply literals appearing in unit clauses
 *
 * (3) would typically happen only once and before the other two cases
 * It may be useful to distinguish between the above three cases
 *
 * Note if the current decision level is L, then the literals implied by unit
 * resolution must have decision level L
 *
 * This implies that there must be a start level S, which will be the level
 * where the decision sequence would be empty
 *
 * We require you to choose S as 1, then literals implied by (3) would have 1 as
 * their decision level (this level will also be the assertion level of unit
 * clauses)
 *
 * Yet, the first decided literal must have 2 as its decision level
 ******************************************************************************/

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
  for(Lit** unit = ARRAY_BEGIN(sat_state->propagate_literals); unit < ARRAY_C_END(sat_state->propagate_literals); ++unit)
    if(!propagate_lit_decision(*unit, sat_state))
      return false;

  sat_state->propagate_literals.count = 0;

  return true;
}

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {
  Lit* lit;

  while(sat_state->decided_literals.count
    && (lit = *(ARRAY_C_END(sat_state->decided_literals) - 1))->var->decision.level == sat_state->level) {
    --sat_state->decided_literals.count;
    unset_Var_Decision(lit->var);
  }

  ClauseListNode* cln;
  while(cln = sat_state->subsumed_clauses.lh_first) {
    Clause* clause = cln->clause;
    LIST_REMOVE(cln, link);
    free_CLN(cln);
    if(clause == NULL) break;
    clause->is_subsumed = false;
  }

  sat_state->propagate_literals.count = 0;
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {
  return clause->assertion_level == sat_state->level;
}


/******************************************************************************
 ******************************************************************************
 * The functions below are already implemented for you and MUST STAY AS IS
 ******************************************************************************/

//returns the weight of a literal (which is 1 for our purposes)
c2dWmc sat_literal_weight(const Lit* lit) {
  return 1;
}

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var* var) {
  return var->mark;
}

//marks a variable (which is not marked already)
void sat_mark_var(Var* var) {
  var->mark = 1;
}

//unmarks a variable (which is marked already)
void sat_unmark_var(Var* var) {
  var->mark = 0;
}

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause* clause) {
  return clause->mark;
}

//marks a clause (which is not marked already)
void sat_mark_clause(Clause* clause) {
  clause->mark = 1;
}
//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause* clause) {
  clause->mark = 0;
}

/******************************************************************************
 * end
 ******************************************************************************/
