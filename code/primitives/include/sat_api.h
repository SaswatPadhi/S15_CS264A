#ifndef SATAPI_H_
#define SATAPI_H_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdbool.h>

#include <sys/queue.h>

/******************************************************************************
 * sat_api.h shows the function prototypes you should implement to create libsat.a
 *
 * To use the sat library, a sat state should be constructed from an input cnf file
 *
 * The sat state supports functions that are usually used to implement a sat solver,
 * such as deciding variables and learning clauses. It also supports functions for
 * obtaining stats about the input cnf, such as the number of variables and clauses.
 *
 * The functions supported by a sat state are sufficient to implement a modern sat
 * solver (also known as CDC solver).
 *
 * A sat state has a "decision level", which is incremented when a literal is
 * decided, and decremented when a literal is undecided. Hence, each decided
 * literal is associated with a decision level. Similarly, literals which are implied
 * by unit resolution are also associated with a decision level.
 *
 * A learned clause is associated with an "assertion level". The clause can be
 * asserted (added) to a state state only when the decision level of the sat
 * state equals to the clause's assertion level.
 ******************************************************************************/

/******************************************************************************
 * typedefs
 ******************************************************************************/

typedef char BOOLEAN; //signed

typedef unsigned long c2dSize;  //for variables, clauses, and various things
typedef signed long c2dLiteral; //for literals
typedef double c2dWmc;          //for (weighted) model count

/******************************************************************************
 * Basic structures
 ******************************************************************************/

#define ARRAY(type) \
  struct { \
    type* item; \
    c2dSize size, count; \
  }

#define INIT_ARRAY(name, type, length) do { \
  (name).count = 0; \
  (name).size = length; \
  (name).item = (type*) malloc((length) * sizeof(type)); \
} while(0)

#define FREE_ARRAY(name) do { \
  free((name).item); \
} while(0)

#define ARRAY_BEGIN(name)   ((name).item)
#define ARRAY_S_END(name)   ((name).item + (name).size)
#define ARRAY_C_END(name)   ((name).item + (name).count)

typedef struct var Var;
typedef struct literal Lit;
typedef struct clause Clause;
typedef struct sat_state_t SatState;

/******************************************************************************
 * Literals:
 * --You must represent literals using the following struct
 * --Positive literals' indices range from 1 to n (n is the number of cnf variables)
 * --Negative literals' indices range from -n to -1 (n is the number of cnf variables)
 * --Index of a literal must be of type "c2dLiteral"
 ******************************************************************************/

typedef struct literal {
  c2dLiteral id;

  Var* var;                                         // NOT owner

  ARRAY(Clause*) appears_in;                        // NOT owner

  LIST_HEAD(, ClauseListNode) watch_list;           // NOT owner
  LIST_HEAD(, ClauseListNode) learned_list;         // NOT owner
} Lit;

typedef struct LitListNode {
  Lit* lit;                                         // NOT owner
  LIST_ENTRY(LitListNode) link;
} LitListNode;

/******************************************************************************
 * Variables:
 * --You must represent variables using the following struct
 * --Variable index must start at 1, and is no greater than the number of cnf variables
 * --Index of a variable must be of type "c2dSize"
 * --The field "mark" below and its related functions should not be changed
 ******************************************************************************/

typedef struct var {
  c2dSize id;
  Lit lit[2];                                      // owner

  struct {
    BOOLEAN value;
    c2dSize level, order;
    Clause* implied_by;                             // NOT owner
    Var* dominator;                                 // NOT owner
  } decision;

  BOOLEAN mark;                                     //THIS FIELD MUST STAY AS IS
} Var;

/******************************************************************************
 * Clauses:
 * --You must represent clauses using the following struct
 * --Clause index must start at 1, and is no greater than the number of cnf clauses
 * --Index of a clause must be of type "c2dSize"
 * --A clause must have an array consisting of its literals
 * --The index of literal array must start at 0, and is less than the clause size
 * --The field "mark" below and its related functions should not be changed
 ******************************************************************************/

typedef struct clause {
  c2dSize id, assertion_level;

  ARRAY(Lit*) lits;                                 // NOT owner
  Lit* watch_a, * watch_b;

  BOOLEAN is_subsumed;
  BOOLEAN mark;                                     //THIS FIELD MUST STAY AS IS
} Clause;

typedef struct ClauseListNode {
  Clause* clause;                                   // NOT owner
  LIST_ENTRY(ClauseListNode) link;
} ClauseListNode;

/******************************************************************************
 * SatState:
 * --The following structure will keep track of the data needed to
 * condition/uncondition variables, perform unit resolution, and so on ...
 ******************************************************************************/

typedef struct sat_state_t {
  c2dSize level;

  Var contradiction;
  Clause false_clause;

  BOOLEAN* marks;

  ARRAY(Var) vars;                                  // owner
  ARRAY(Clause) clauses;                            // owner

  ARRAY(Lit*) decided_literals;                     // NOT owner
  ARRAY(Lit*) propagate_literals;                   // NOT owner

  LIST_HEAD(, ClauseListNode) learned_clauses;      // owner
  LIST_HEAD(, ClauseListNode) subsumed_clauses;     // owner
} SatState;

/******************************************************************************
 * API:
 * --Using the above structures you must implement the following functions
 * --Incomplete implementations of the functions can be found in sat_api.c
 * --These functions are all you need for the knowledge compiler
 * --You must implement each function below
 * --Note that most of the functions can be implemented in 1 line or so
 ******************************************************************************/

/******************************************************************************
 * function prototypes
 ******************************************************************************/

void pprint_Lit(Lit*, BOOLEAN);
void pprint_Clause(Clause*, BOOLEAN);
void pprint_SatState(SatState*, BOOLEAN);

/******************************************************************************
 * Variables
 ******************************************************************************/

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize, const SatState*);

//returns the index of a variable
c2dSize sat_var_index(const Var*);

//returns the variable of a literal
Var* sat_literal_var(const Lit*);

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var*);

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var*);

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState*);

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var*);

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize, const Var*);

/******************************************************************************
 * Literals
 ******************************************************************************/

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral, const SatState*);

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit*);

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var*);

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var*);

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit*);

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
Clause* sat_decide_literal(Lit* lit, SatState*);

//undoes the last literal decision and the corresponding implications obtained by unit resolution
void sat_undo_decide_literal(SatState*);

/******************************************************************************
 * Clauses
 ******************************************************************************/

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize, const SatState*);

//returns the index of a clause
c2dSize sat_clause_index(const Clause*);

//returns the literals of a clause
Lit** sat_clause_literals(const Clause*);

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause*);

void sat_subsume_clause(Clause*, SatState*);
//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause*);

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState*);

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState*);

//builds an asserting clause from current SatState
Clause* sat_build_asserting_clause(SatState* sat_state);

//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause*, SatState*);

/******************************************************************************
 * SatState
 ******************************************************************************/

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char*);

//frees the SatState
void sat_state_free(SatState*);

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState*);

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState*);

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause*, const SatState*);

/******************************************************************************
 * The functions below are already implemented for you and MUST STAY AS IS
 ******************************************************************************/

//returns the weight of a literal (which is simply 1 for our purposes)
c2dWmc sat_literal_weight(const Lit*);

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var*);

//marks a variable (which is not marked already)
void sat_mark_var(Var*);

//unmarks a variable (which is marked already)
void sat_unmark_var(Var*);

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause*);

//marks a clause (which is not marked already)
void sat_mark_clause(Clause*);

//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause*);

//Errors
void exit_with_error(const char*, const char*);

#endif //SATAPI_H_

/******************************************************************************
 * end
 ******************************************************************************/
