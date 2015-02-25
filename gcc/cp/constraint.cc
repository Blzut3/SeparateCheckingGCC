/* Processing rules for constraints.
   Copyright (C) 2013-2014 Free Software Foundation, Inc.
   Contributed by Andrew Sutton (andrew.n.sutton@gmail.com)

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "print-tree.h"
#include "cp-tree.h"
#include "c-family/c-common.h"
#include "c-family/c-objc.h"
#include "tree-inline.h"
#include "intl.h"
#include "toplev.h"
#include "flags.h"
#include "timevar.h"
#include "diagnostic.h"
#include "tree-iterator.h"
#include "vec.h"
#include "target.h"

/* Returns true if T is a constraint. */
static bool
is_constraint(tree t)
{
  switch (TREE_CODE(t))
    {
    case PRED_CONSTR:
    case EXPR_CONSTR:
    case TYPE_CONSTR:
    case ICONV_CONSTR:
    case DEDUCT_CONSTR:
    case EXCEPT_CONSTR:
    case PARM_CONSTR:
    case CONJ_CONSTR:
    case DISJ_CONSTR:
      return true;
    default:
      return false;
    }
}


// -------------------------------------------------------------------------- //
// Requirement Construction
//
// Facilities for building and manipulating template requirements.
//
// TODO: Simply assigning boolean_type_node to the result type of the
// expression seems right for constraints, but in the long-term we might want
// to be more flexible (i.e., allow some form of overload resolution?).

// Create a new logical node joining the subexpressions a and b.
static inline tree
join_requirements (tree_code c, tree a, tree b)
{
  gcc_assert (a != NULL_TREE && b != NULL_TREE);
  gcc_assert (c == TRUTH_ANDIF_EXPR || c == TRUTH_ORIF_EXPR);
  return build_min (c, boolean_type_node, a, b);
}

// Returns the conjunction of two requirements A and B, where A and B are
// reduced terms in the constraints language. Note that conjoining a non-null
// expression with  NULL_TREE is an identity operation. That is, for
// non-null A,
//
//    conjoin_constraints(a, NULL_TREE) == a
//
// If both A and B are NULL_TREE, the result is also NULL_TREE.
tree
conjoin_constraints (tree a, tree b)
{
  if (a)
    return b ? join_requirements (TRUTH_ANDIF_EXPR, a, b) : a;
  else if (b)
    return b;
  else
    return NULL_TREE;
}

// Transform the list of expressions in the T into a conjunction
// of requirements. T must be a TREE_VEC.
tree
conjoin_constraints (tree t)
{
  gcc_assert (TREE_CODE (t) == TREE_VEC);
  tree r = NULL_TREE;
  for (int i = 0; i < TREE_VEC_LENGTH (t); ++i)
    r = conjoin_constraints (r, TREE_VEC_ELT (t, i));
  return r;
}


// -------------------------------------------------------------------------- //
// Constraint Resolution
//
// This facility is used to resolve constraint checks from requirement
// expressions. A constraint check is a call to a function template declared
// with the keyword 'concept'.
//
// The result of resolution is a pair (a TREE_LIST) whose value is the
// matched declaration, and whose purpose contains the coerced template
// arguments that can be substituted into the call.


// Given an overload set OVL, try to find a unique definition that can be
// instantiated by the template arguments ARGS.
//
// This function is not called for arbitrary call expressions. In particular,
// the call expression must be written with explicit template arguments
// and no function arguments. For example:
//
//      f<T, U>()
//
// If a single match is found, this returns a TREE_LIST whose VALUE
// is the constraint function (not the template), and its PURPOSE is
// the complete set of arguments substituted into the parameter list.
static tree
resolve_constraint_check (tree ovl, tree args)
{
  tree cands = NULL_TREE;
  for (tree p = ovl; p != NULL_TREE; p = OVL_NEXT (p))
    {
      // Get the next template overload.
      tree tmpl = OVL_CURRENT (p);
      if (TREE_CODE (tmpl) != TEMPLATE_DECL)
        continue;

      // Don't try to deduce checks for non-concept-like. We often
      // end up trying to resolve constraints in functional casts
      // as part of a post-fix expression. We can save time and
      // headaches by not instantiating those declarations.
      //
      // NOTE: This masks a potential error, caused by instantiating
      // non-deduced contexts using placeholder arguments.
      tree fn = DECL_TEMPLATE_RESULT (tmpl);
      if (DECL_ARGUMENTS (fn))
        continue;
      if (!DECL_DECLARED_CONCEPT_P (fn))
        continue;

      // Remember the candidate if we can deduce a substitution.
      ++processing_template_decl;
      tree parms = TREE_VALUE (DECL_TEMPLATE_PARMS (tmpl));
      if (tree subst = coerce_template_parms (parms, args, tmpl))
        if (subst != error_mark_node)
          cands = tree_cons (subst, fn, cands);
      --processing_template_decl;
    }

  // If we didn't find a unique candidate, then this is
  // not a constraint check.
  if (!cands || TREE_CHAIN (cands))
    return NULL_TREE;

  // Constraints must be declared concepts.
  tree decl = TREE_VALUE (cands);
  if (!DECL_DECLARED_CONCEPT_P (decl))
    return NULL_TREE;

  return cands;
}

// Determine if the the call expression CALL is a constraint check, and
// return the concept declaration and arguments being checked. If CALL
// does not denote a constraint check, return NULL.
tree
resolve_constraint_check (tree call)
{
  gcc_assert (TREE_CODE (call) == CALL_EXPR);

  // A constraint check must be only a template-id expression. If
  // it's a call to a base-link, its function(s) should be a
  // template-id expression. If this is not a template-id, then it
  // cannot be a concept-check.
  tree target = CALL_EXPR_FN (call);
  if (BASELINK_P (target))
    target = BASELINK_FUNCTIONS (target);
  if (TREE_CODE (target) != TEMPLATE_ID_EXPR)
    return NULL_TREE;

  // Get the overload set and template arguments and try to
  // resolve the target.
  tree ovl = TREE_OPERAND (target, 0);
  tree args = TREE_OPERAND (target, 1);
  return resolve_constraint_check (ovl, args);
}

// Given a call expression or template-id expression to a concept, EXPR,
// possibly including a placeholder argument, deduce the concept being checked
// and the prototype paraemter.  Returns true if the constraint and prototype
// can be deduced and false otherwise. Note that the CHECK and PROTO arguments
// are set to NULL_TREE if this returns false.
bool
deduce_constrained_parameter (tree expr, tree& check, tree& proto)
{
  if (TREE_CODE (expr) == TEMPLATE_ID_EXPR)
    {
      // Get the check and prototype parameter from the variable template.
      tree decl = TREE_OPERAND (expr, 0);
      tree parms = DECL_TEMPLATE_PARMS (decl);

      check = DECL_TEMPLATE_RESULT (decl);
      proto = TREE_VALUE (TREE_VEC_ELT (TREE_VALUE (parms), 0));
      return true;
    }
  else if (TREE_CODE (expr) == CALL_EXPR)
    {
      // Resolve the constraint check to deduce the prototype parameter.
      if (tree info = resolve_constraint_check (expr))
        {
          // Get function and argument from the resolved check expression and
          // the prototype parameter. Note that if the first argument was a
          // pack, we need to extract the first element ot get the prototype.
          check = TREE_VALUE (info);
          tree arg = TREE_VEC_ELT (TREE_PURPOSE (info), 0);
          if (ARGUMENT_PACK_P (arg))
            arg = TREE_VEC_ELT (ARGUMENT_PACK_ARGS (arg), 0);
          proto = TREE_TYPE (arg);
          return true;
        }
      check = proto = NULL_TREE;
      return false;
    }
  else
    gcc_unreachable ();
}

// Given a call expression or template-id expression to a concept, EXPR,
// deduce the concept being checked and return the template arguments.
// Returns NULL_TREE if deduction fails.
static tree
deduce_concept_introduction (tree expr)
{
  if (TREE_CODE (expr) == TEMPLATE_ID_EXPR)
    {
      // Get the parameters from the template expression.
      tree decl = TREE_OPERAND (expr, 0);
      tree args = TREE_OPERAND (expr, 1);
      tree var = DECL_TEMPLATE_RESULT (decl);
      tree parms = TREE_VALUE (DECL_TEMPLATE_PARMS (decl));

      parms = coerce_template_parms (parms, args, var);      
      // Check that we are returned a proper set of arguments.
      if (parms == error_mark_node)
        return NULL_TREE;
      return parms;
    }
  else if (TREE_CODE (expr) == CALL_EXPR)
    {
      // Resolve the constraint check and return arguments.
      if (tree info = resolve_constraint_check (expr))
        return TREE_PURPOSE (info);
      return NULL_TREE;
    }
  else
    gcc_unreachable ();
}


// -------------------------------------------------------------------------- //
// Declarations

// Check that FN satisfies the structural requirements of a
// function concept definition.
tree
check_function_concept (tree fn)
{
  location_t loc = DECL_SOURCE_LOCATION (fn);

  // Check that the function is comprised of only a single
  // return statement.
  tree body = DECL_SAVED_TREE (fn);
  if (TREE_CODE (body) == BIND_EXPR)
    body = BIND_EXPR_BODY (body);

  // Sometimes a function call results in the creation of clean up
  // points. Allow these to be preserved in the body of the
  // constraint, as we might actually need them for some constexpr
  // evaluations.
  if (TREE_CODE (body) == CLEANUP_POINT_EXPR)
    body = TREE_OPERAND (body, 0);

  if (TREE_CODE (body) != RETURN_EXPR)
    error_at (loc, "function concept definition %qD has multiple statements",
              fn);

  return NULL_TREE;
}



namespace {

/*---------------------------------------------------------------------------
                       Lifting of concept definitions
---------------------------------------------------------------------------*/

tree lift_constraints (tree);

/* If the tree T has operands, then lift any concepts out of them.  */
tree
lift_operands (tree t)
{
  if (int n = tree_operand_length (t))
    {
      t = copy_node (t);
      for (int i = 0; i < n; ++i)
	TREE_OPERAND (t, i) = lift_constraints (TREE_OPERAND (t, i));
    }
  return t;
}

/* Inline a reference to a function concept.  */
tree
lift_call (tree t)
{
  /* Try to resolve this function call as a concept.  If not, then it can be
     returned as-is.  */
  tree check = resolve_constraint_check (t);
  if (!check)
      return lift_operands (t);

  tree fn = TREE_VALUE (check);
  tree args = TREE_PURPOSE (check);

  /* Extract the body of the function minus the return expression.  */
  tree body = DECL_SAVED_TREE (fn);
  if (!body)
    return error_mark_node;
  if (TREE_CODE (body) == BIND_EXPR)
    body = BIND_EXPR_BODY (body);
  gcc_assert (TREE_CODE (body) == RETURN_EXPR);
  body = TREE_OPERAND (body, 0);

  /* Substitute template arguments to produce our inline expression.  */
  tree result = tsubst_expr (body, args,  tf_none, NULL_TREE, false);
  if (result == error_mark_node)
    return error_mark_node;

  return lift_constraints (result);
}

/* Inline a refernece to a variable concept.  */
tree
lift_var (tree t)
{
  tree decl = DECL_TEMPLATE_RESULT (TREE_OPERAND (t, 0));
  if (!DECL_DECLARED_CONCEPT_P (decl))
    return t;

  /* Extract the body from the variable initializer.  */
  tree body = DECL_INITIAL (decl);
  if (!body)
    return error_mark_node;

  /* Subsitute the arguments to form our new inline expression.  */
  tree result = tsubst_expr (body, TREE_OPERAND (t, 1),  tf_none, NULL_TREE, false);
  if (result == error_mark_node)
    return error_mark_node;

  return lift_constraints (result);
}

/* Determine if a template-id is a variable concept and inline.  */
tree
lift_template_id (tree t)
{
  if (variable_concept_p (TREE_OPERAND (t, 0)))
    return lift_var (t);
  return t;
}

/* Inline references to specializations of concepts.  */
tree 
lift_constraints (tree t)
{
  if (t == NULL_TREE)
    return NULL_TREE;
  if (t == error_mark_node)
    return error_mark_node;

  /* Concepts can be referred to by call or variable.  The rest of the nodes
     of an expression are to be passed through.  */
  switch (TREE_CODE (t))
    {
    case CALL_EXPR:
      return lift_call (t);
    case TEMPLATE_ID_EXPR:
      return lift_template_id (t);

    case TREE_LIST:
      {
	t = copy_node (t);
	TREE_VALUE (t) = lift_constraints (TREE_VALUE (t));
	TREE_CHAIN (t) = lift_constraints (TREE_CHAIN (t));
	return t;
      }
    default:
      return lift_operands (t);
    }
}

/*---------------------------------------------------------------------------
                        Constraint normalization
---------------------------------------------------------------------------*/

tree transform_expression (tree);

/* Check that the logical-or or logical-and expression does
   not result in a call to a user-defined user-defined operator 
   (temp.constr.op). Returns true if the logical operator is 
   admissible and false otherwise. */
bool
check_logical_expr (tree t) 
{
  /* We can't do much for type dependent expressions. */
  if (type_dependent_expression_p (t) || value_dependent_expression_p (t))
    return true;

  /* Resolve the logical operator. Note that template processing is
     disabled so we get the actual call or target expression back.
     not_processing_template_sentinel sentinel. */
  tree arg1 = TREE_OPERAND (t, 0);
  tree arg2 = TREE_OPERAND (t, 1);
  tree ovl = NULL_TREE;
  tree expr = build_new_op (input_location, TREE_CODE (t), LOOKUP_NORMAL, 
                            arg1, arg2, /*arg3*/NULL_TREE, 
                            &ovl, tf_none);
  if (TREE_CODE (expr) != TREE_CODE (t))
    {
      error ("user-defined operator %qs in constraint %qE",
             operator_name_info[TREE_CODE (t)].name, t);
      ;
      return false;
    }
  return true;
}

/* Transform a logical-or or logical-and expression into either
   a conjunction or disjunction. */
tree
xform_logical (tree t, tree_code c)
{
  if (!check_logical_expr (t))
    return error_mark_node;
  tree t0 = transform_expression (TREE_OPERAND (t, 0));
  tree t1 = transform_expression (TREE_OPERAND (t, 1));
  return build_nt (c, t0, t1);
}

/* Transform a requires-expression into a parameterized constraint. 

   FIXME: Implement me! */
tree
xform_requires (tree t)
{
  /*
  for (tree l = TREE_OPERAND (t, 1); l; l = TREE_CHAIN (l))
    TREE_VALUE (l) = normalize_expr (TREE_VALUE (l));
  return t;
  */
  (void)t;
  return error_mark_node;
}

/* Transform an expression into an atomic predicate constraint. 
    After substitution, the expression of a predicate constraint shall 
    have type bool (temp.constr.pred). For non-type- dependent 
    expressions, we can check that now. */
tree
xform_atomic (tree t) 
{
  if (!type_dependent_expression_p (t)) 
    if (!same_type_p (TREE_TYPE (t), boolean_type_node))
      {
        error ("predicate constraint %qE does not have type %<bool%>", t);
        return error_mark_node;
      }
  return t;
}

/* Transform an expression into a constraint. */
tree
xform_expr (tree t)
{
  switch (TREE_CODE (t))
    {
    case TRUTH_ANDIF_EXPR:
      return xform_logical (t, CONJ_CONSTR);
    case TRUTH_ORIF_EXPR:
      return xform_logical (t, DISJ_CONSTR);
    case REQUIRES_EXPR:
      return xform_requires (t);
    case BIND_EXPR:        
      return transform_expression (BIND_EXPR_BODY (t));
    case TAG_DEFN:
      /* TODO: When does this actually show up? */
      return NULL_TREE;
    default:
      /* All other constraints are atomic. */ 
      return xform_atomic (t);
    }
}

/* Transform a statement into an expression. */
tree
xform_stmt (tree t)
{
  switch (TREE_CODE (t))
    {
    case RETURN_EXPR:
      return transform_expression (TREE_OPERAND (t, 0));
    default:
      gcc_unreachable ();
    }
  return error_mark_node;
}

// Reduction rules for the declaration T.
tree
xform_decl (tree t)
{
  switch (TREE_CODE (t))
    {
    case VAR_DECL:
      return xform_atomic (t);
    default:
      gcc_unreachable ();
    }
  return error_mark_node;
}

/* Transform an exceptional node into a constraint. */
tree
xform_misc (tree t)
{
  switch (TREE_CODE (t))
    {
    case TRAIT_EXPR:
      return xform_atomic (t);
    case CONSTRUCTOR:
      return xform_atomic (t);
    default:
      gcc_unreachable ();
    }
  return error_mark_node;
}


/* Transform a lifted expression into a constraint. This either
   returns a constraint, or it returns error_mark_node when
   a constraint cannot be formed. */
tree
transform_expression (tree t)
{
  if (!t) 
    return NULL_TREE;
  if (t == error_mark_node)
    return t;

  switch (TREE_CODE_CLASS (TREE_CODE (t))) 
    {
    case tcc_unary:
    case tcc_binary:
    case tcc_expression:
    case tcc_vl_exp:
      return xform_expr (t);
    
    case tcc_statement:   
      return xform_stmt (t);
    
    case tcc_declaration: 
      return xform_decl (t);
    
    case tcc_exceptional: 
      return xform_misc (t);
    
    case tcc_constant:
    case tcc_reference:
    case tcc_comparison:
      /* These are atomic predicate constraints. */
      return build_nt (PRED_CONSTR, t);

    default:
      /* Unhandled node kind. */
      gcc_unreachable ();
    }
  return error_mark_node;
}

/*---------------------------------------------------------------------------
                        Constraint normalization
---------------------------------------------------------------------------*/

tree normalize_constraint (tree);

/* The normal form of the disjunction T0 /\ T1 is the conjunction
   of the normal form of T0 and the normal form of T1 */
inline tree
normalize_conjunction (tree constr)
{
  tree t0 = normalize_constraint (TREE_OPERAND (constr, 0));
  tree t1 = normalize_constraint (TREE_OPERAND (constr, 1));
  return build_nt (CONJ_CONSTR, t0, t1);
}

/* The normal form of the disjunction T0 \/ T1 is the disjunction 
   of the normal form of T0 and the normal form of T1 */
inline tree
normalize_disjunction (tree constr)
{
  tree t0 = normalize_constraint (TREE_OPERAND (constr, 0));
  tree t1 = normalize_constraint (TREE_OPERAND (constr, 1));
  return build_nt (DISJ_CONSTR, t0, t1);
}

/* A predicate constraint is normalized in two stages. First all
   references specializations of concepts are replaced by their
   substituted definitions. Then, the resulting expression is
   transformed into a constraint by transforming && expressions
   into conjunctions and || into disjunctions. */
tree 
normalize_predicate_constraint (tree constr)
{
  tree pred = lift_constraints (PRED_CONSTR_EXPR (constr));
  return transform_expression (pred);
}

/* The normal form of a parameterized constraint is the normal
   form of its operand. */
tree
normalize_parameterized_constraint (tree constr)
{
  tree parms = PARM_CONSTR_PARMS (constr);
  tree operand = normalize_constraint (PARM_CONSTR_OPERAND (constr));
  return build_nt (PARM_CONSTR, parms, operand);
}

/* Normalize the constraint CONSTR by reducing it so that it is
   comprised of only conjunctions and disjunctions. */
tree
normalize_constraint (tree constr)
{
  if (!constr)
    return NULL_TREE;
  
  switch (TREE_CODE (constr))
    {
      case CONJ_CONSTR:
        return normalize_conjunction (constr);
      case DISJ_CONSTR:
        return normalize_disjunction (constr);
      case PRED_CONSTR:
        return normalize_predicate_constraint (constr);
      case PARM_CONSTR:
        return normalize_parameterized_constraint (constr);
      case EXPR_CONSTR:
      case TYPE_CONSTR:
      case ICONV_CONSTR:
      case DEDUCT_CONSTR:
      case EXCEPT_CONSTR:
        /* These constraints are defined to be atomic. */
        return constr;
      
      default:
        /* CONSTR was not a constraint. */
        gcc_unreachable();
    }
  return error_mark_node;
}

} // end namespace


// -------------------------------------------------------------------------- //
// Constraint Semantic Processing
//
// The following functions are called by the parser and substitution rules
// to create and evaluate constraint-related nodes.

// A mapping from declarations to constraint information. Note that 
// both templates and their underlying declarations are mapped to the 
// same constraint information.
static hash_map<tree, tree> decl_constraints;

// Returns the template constraints of declaration T. If T is not
// constrained, return NULL_TREE. Note that T must be non-null.
tree
get_constraints (tree t)
{
  gcc_assert (DECL_P (t));
  if (TREE_CODE (t) == TEMPLATE_DECL)
    t = DECL_TEMPLATE_RESULT (t);
  if (tree *r = decl_constraints.get (t))
    return *r;
  else
    return NULL_TREE;
}

// Associate the given constraint information with the declaration. Don't
// build associations if ci is NULL_TREE.
void
set_constraints (tree t, tree ci)
{
  gcc_assert (t && DECL_P (t) && TREE_CODE (t) != TEMPLATE_DECL);
  if (!ci)
    return;

  gcc_assert (!decl_constraints.get (t));
  gcc_assert (check_constraint_info (ci));
  decl_constraints.put (t, ci);
}

// Remove the associated constraints of the declaration T. 
//
// FIXME: What if T is a template? What if it's a non-template? we
// should remove both associations.
void
remove_constraints (tree t)
{
  gcc_assert (DECL_P (t));
  if (TREE_CODE (t) == TEMPLATE_DECL)
    t = DECL_TEMPLATE_RESULT (t);

  if (decl_constraints.get (t))
    decl_constraints.remove (t);
}

// If the recently parsed TYPE declares or defines a template or template
// specialization, get its corresponding constraints from the current
// template parameters and bind them to TYPE's declaration.
tree
associate_classtype_constraints (tree type)
{
  if (!type || type == error_mark_node || TREE_CODE (type) != RECORD_TYPE)
    return type;

  // An explicit class template specialization has no template
  // parameters.
  if (!current_template_parms)
    return type;

  if (CLASSTYPE_IS_TEMPLATE (type) || CLASSTYPE_TEMPLATE_SPECIALIZATION (type))
    {
      tree decl = TYPE_STUB_DECL (type);
      tree reqs = TEMPLATE_PARMS_CONSTRAINTS (current_template_parms);
      tree ci = build_constraints (reqs, NULL_TREE);

      // An implicitly instantiated member template declaration already
      // has associated constraints. If it is defined outside of its
      // class, then we need match these constraints against those of
      // original declaration.
      if (tree orig_ci = get_constraints (decl))
        {
          if (!equivalent_constraints (ci, orig_ci))
            {
              // FIXME: Improve diagnostics.
              error ("%qT does not match any declaration", type);
              return error_mark_node;
            }
          return type;
        }
      set_constraints (decl, ci);
    }
  return type;
}

// Returns a conjunction of shorthand requirements for the template
// parameter list PARMS. Note that the requirements are stored in
// the TYPE of each tree node.
tree
get_shorthand_constraints (tree parms)
{
  tree reqs = NULL_TREE;
  parms = INNERMOST_TEMPLATE_PARMS (parms);
  for (int i = 0; i < TREE_VEC_LENGTH (parms); ++i)
    {
      tree parm = TREE_VEC_ELT (parms, i);
      reqs = conjoin_constraints (reqs, TEMPLATE_PARM_CONSTRAINTS (parm));
    }
  return reqs;
}

namespace {

// Create an empty constraint info block.
inline tree_constraint_info*
build_constraint_info ()
{
  return (tree_constraint_info *)make_node (CONSTRAINT_INFO);
}

} // namespace

// Build a constraint-info object that contains the associated requirements
// of a declaration. This also includes the declaration's template
// requirements TR (if any) and declaration requirements DR (if any).
//
// If the declaration has neither template nor declaration requirements
// this returns NULL_TREE, indicating an unconstrained declaration.
tree
build_constraints (tree tr, tree dr)
{
  if (!tr && !dr)
    return NULL_TREE;
  tree_constraint_info* ci = build_constraint_info ();
  ci->template_reqs = tr;
  ci->declarator_reqs = dr;
  ci->associated_constr = conjoin_constraints (tr, dr);
  ci->normalized_constr = normalize_constraint (ci->associated_constr);
  ci->assumptions = decompose_assumptions (ci->normalized_constr);
  return (tree)ci;
}

// Returns true iff cinfo contains a valid constraint expression.
// This is the case when the associated requirements can be successfully
// decomposed into lists of atomic constraints.
bool
valid_requirements_p (tree cinfo)
{
  gcc_assert (cinfo);
  return CI_ASSUMPTIONS (cinfo) != error_mark_node;
}

// Constructs a REQUIRES_EXPR with parameters, PARMS, and requirements, REQS,
// that can be evaluated as a constant expression.
tree
build_requires_expr (tree parms, tree reqs)
{
  // Modify the declared parameters by removing their context (so they
  // don't refer to the enclosing scope), and marking them constant (so
  // we can actually check constexpr properties).
  for (tree p = parms; p && !VOID_TYPE_P (TREE_VALUE (p)); p = TREE_CHAIN (p))
    {
      tree parm = TREE_VALUE (p);
      DECL_CONTEXT (parm) = NULL_TREE;
      TREE_CONSTANT (parm) = true;
    }

  // Build the node.
  tree r = build_min (REQUIRES_EXPR, boolean_type_node, parms, reqs);
  TREE_SIDE_EFFECTS (r) = false;
  TREE_CONSTANT (r) = true;
  return r;
}

// Evaluate an instantiated requires expr, returning the true node
// only when all sub-requirements have evaluated to true.
tree
eval_requires_expr (tree reqs)
{
  for (tree t = reqs ; t; t = TREE_CHAIN (t))
    {
      tree r = TREE_VALUE (t);
      r = fold_non_dependent_expr (r);
      r = maybe_constant_value (r);
      if (r != boolean_true_node)
	return boolean_false_node;
    }
  return boolean_true_node;
}

// Finish a requires expression, returning a node wrapping the parameters,
// PARMS, and the list of requirements REQS.
tree
finish_requires_expr (tree parms, tree reqs)
{
  if (processing_template_decl)
    return build_requires_expr (parms, reqs);
  else
    return eval_requires_expr (reqs);
}

// Construct a unary expression that evaluates properties of the
// expression or type T, and has a boolean result type.
static inline tree
build_check_expr (tree_code c, tree t)
{
  tree r = build_min (c, boolean_type_node, t);
  TREE_SIDE_EFFECTS (r) = false;
  TREE_READONLY (r) = true;
  TREE_CONSTANT (r) = true;
  return r;
}

// Finish a syntax requirement, constructing a list embodying a sequence
// of checks for the validity of EXPR and TYPE, the convertibility of
// EXPR to TYPE, and the expression properties specified in SPECS.
tree
finish_expr_requirement (tree expr, tree type, tree specs)
{
  gcc_assert (processing_template_decl);

  // Build a list of checks, starting with the valid expression.
  tree result = tree_cons (NULL_TREE, finish_validexpr_expr (expr), NULL_TREE);

  // If a type requirement was provided, build the result type checks.
  if (type)
    {
      // If the type is dependent, ensure that it can be validly
      // instantiated.
      //
      // NOTE: We can also disregard checks that result in the template
      // parameter.
      if (dependent_type_p (type))
        {
          tree treq = finish_type_requirement (type);
          result = tree_cons (NULL_TREE, treq, result);
        }

      // Ensure that the result of the expression can be converted to
      // the result type.
      tree decl_type = finish_decltype_type (expr, false, tf_none);
      tree creq = finish_trait_expr (CPTK_IS_CONVERTIBLE_TO, decl_type, type);
      result = tree_cons (NULL_TREE, creq, result);
    }

  // If constraint specifiers are present, make them part of the
  // list of constraints.
  if (specs)
    {
      TREE_CHAIN (tree_last (specs)) = result;
      result = specs;
    }

  // Finally, construct the syntactic requirement.
  return build_check_expr (EXPR_REQ, nreverse (result));
}

// Finish a simple syntax requirement, returning a node representing
// a check that EXPR is a valid expression.
tree
finish_expr_requirement (tree expr)
{
  gcc_assert (processing_template_decl);
  tree req = finish_validexpr_expr (expr);
  tree reqs = tree_cons (NULL_TREE, req, NULL_TREE);
  return build_check_expr (EXPR_REQ, reqs);
}

// Finish a type requirement, returning a node representing a check
// that TYPE will result in a valid type when instantiated.
tree
finish_type_requirement (tree type)
{
  gcc_assert (processing_template_decl);
  tree req = finish_validtype_expr (type);
  return build_check_expr (TYPE_REQ, req);
}

tree
finish_nested_requirement (tree expr)
{
  gcc_assert (processing_template_decl);
  return build_check_expr (NESTED_REQ, expr);
}

// Finish a constexpr requirement, returning a node representing a
// check that EXPR, when instantiated, may be evaluated at compile time.
tree
finish_constexpr_requirement (tree expr)
{
  gcc_assert (processing_template_decl);
  return finish_constexpr_expr (expr);
}

// Finish the noexcept requirement by constructing a noexcept
// expression evaluating EXPR.
tree
finish_noexcept_requirement (tree expr)
{
  gcc_assert (processing_template_decl);
  return finish_noexcept_expr (expr, tf_none);
}

// Returns the true or false node depending on the truth value of B.
static inline tree
truth_node (bool b)
{
  return b ? boolean_true_node : boolean_false_node;
}

// Returns a finished validexpr-expr. Returns the true or false node
// depending on whether EXPR denotes a valid expression. This is the case
// when the expression has been successfully type checked.
//
// When processing a template declaration, the result is an expression
// representing the check.
tree
finish_validexpr_expr (tree expr)
{
  if (processing_template_decl)
    return build_check_expr (VALIDEXPR_EXPR, expr);
  return truth_node (expr && expr != error_mark_node);
}

// Returns a finished validtype-expr. Returns the true or false node
// depending on whether T denotes a valid type name.
//
// When processing a template declaration, the result is an expression
// representing the check.
//
// FIXME: Semantics need to be aligned with the new version of the
// specification (i.e., we must be able to invent a function and
// perform argument deduction against it).
tree
finish_validtype_expr (tree type)
{
  if (is_auto (type))
    {
      sorry ("%<auto%> not supported in result type constraints");
      return error_mark_node;
    }

  if (processing_template_decl)
    return build_check_expr (VALIDTYPE_EXPR, type);
  return truth_node (type && TYPE_P (type));
}

// Returns a finished constexpr-expr. Returns the true or false node
// depending on whether the expression T may be evaluated at compile
// time.
//
// When processing a template declaration, the result is an expression
// representing the check.
tree
finish_constexpr_expr (tree expr)
{
  if (processing_template_decl)
    return build_check_expr (CONSTEXPR_EXPR, expr);

  // TODO: Actually check that the expression can be constexpr
  // evaluated.
  //
  // return truth_node (potential_constant_expression (expr));
  sorry ("constexpr requirement");
  return NULL_TREE;
}

// Check that a constrained friend declaration function declaration,
// FN, is admissable. This is the case only when the declaration depends
// on template parameters and does not declare a specialization.
void
check_constrained_friend (tree fn, tree reqs)
{
  if (fn == error_mark_node)
    return;
  gcc_assert (TREE_CODE (fn) == FUNCTION_DECL);

  // If there are not constraints, this cannot be an error.
  if (!reqs)
    return;

  // Constrained friend functions that don't depend on template
  // arguments are effectively meaningless.
  tree parms = DECL_ARGUMENTS (fn);
  tree result = TREE_TYPE (TREE_TYPE (fn));
  if (!(parms && uses_template_parms (parms)) && !uses_template_parms (result))
    {
      error ("constrained friend does not depend on template parameters");
      return;
    }
}

namespace {
// Build a new call expression, but don't actually generate a new
// function call. We just want the tree, not the semantics.
inline tree
build_call_check (tree id)
{
  ++processing_template_decl;
  vec<tree, va_gc> *fargs = make_tree_vector();
  tree call = finish_call_expr (id, &fargs, false, false, tf_none);
  --processing_template_decl;
  return call;
}
} // namespace

// Construct a concept check for the given TARGET. The target may be
// an overload set or a baselink referring to an overload set. Template
// arguments to the target are given by ARG and REST. If the target is
// a function (overload set or baselink reffering to an overload set),
// then this builds the call expression  TARGET<ARG, REST>(). If REST is
// NULL_TREE, then the resulting check is just TARGET<ARG>(). If ARG is
// NULL_TREE, then the resulting check is TARGET<REST>().
tree
build_concept_check (tree target, tree arg, tree rest)
{
  gcc_assert (rest ? TREE_CODE (rest) == TREE_VEC : true);

  // Build a template-id that acts as the call target using TARGET as
  // the template and ARG as the only explicit argument.
  int n = rest ? TREE_VEC_LENGTH (rest) : 0;
  tree targs;
  if (arg)
    {
      targs = make_tree_vec (n + 1);
      TREE_VEC_ELT (targs, 0) = arg;
      if (rest)
        for (int i = 0; i < n; ++i)
          TREE_VEC_ELT (targs, i + 1) = TREE_VEC_ELT (rest, i);
      SET_NON_DEFAULT_TEMPLATE_ARGS_COUNT (targs, n + 1);
    }
  else
    {
      gcc_assert (rest != NULL_TREE);
      targs = rest;
    }

  if (variable_template_p (target))
    return lookup_template_variable (target, targs);
  else
    return build_call_check (lookup_template_function (target, targs));
}

// Returns a TYPE_DECL that contains sufficient information to build
// a template parameter of the same kind as PROTO and constrained
// by the concept declaration FN. PROTO is saved as the initializer of
// the new type decl, and the constraining function is saved in
// DECL_SIZE_UNIT.
//
// If specified, ARGS provides additional arguments to the constraint
// check. These are stored in the DECL_SIZE field.
tree
build_constrained_parameter (tree fn, tree proto, tree args)
{
  tree name = DECL_NAME (fn);
  tree type = TREE_TYPE (proto);
  tree decl = build_decl (input_location, TYPE_DECL, name, type);
  DECL_INITIAL (decl) = proto;  // Describing parameter
  DECL_SIZE_UNIT (decl) = fn;   // Constraining function declaration
  DECL_SIZE (decl) = args;      // Extra template arguments.
  return decl;
}

// Create a constraint expression for the given DECL that evaluates the
// requirements specified by CONSTR, a TYPE_DECL that contains all the
// information necessary to build the requirements (see finish_concept_name
// for the layout of that TYPE_DECL).
//
// Note that the constraints are neither reduced nor decomposed. That is
// done only after the requires clause has been parsed (or not).
tree
finish_shorthand_constraint (tree decl, tree constr)
{
  // No requirements means no constraints.
  if (!constr)
    return NULL_TREE;

  tree proto = DECL_INITIAL (constr); // The prototype declaration
  tree con = DECL_SIZE_UNIT (constr); // The concept declaration
  tree args = DECL_SIZE (constr);     // Extra template arguments

  // If the parameter declaration is variadic, but the concept is not
  // then we need to apply the concept to every element in the pack.
  bool is_proto_pack = template_parameter_pack_p (proto);
  bool is_decl_pack = template_parameter_pack_p (decl);
  bool apply_to_all_p = is_decl_pack && !is_proto_pack;

  // Get the argument and overload used for the requirement. Adjust
  // if we're going to expand later.
  tree arg = template_parm_to_arg (build_tree_list (NULL_TREE, decl));
  if (apply_to_all_p)
    arg = PACK_EXPANSION_PATTERN (TREE_VEC_ELT (ARGUMENT_PACK_ARGS (arg), 0));

  // Build the concept check. If it the constraint needs to be applied
  // to all elements of the parameter pack, then make the constraint
  // an expansion.
  tree check;
  if (TREE_CODE (con) == VAR_DECL)
    {
      check = build_concept_check (DECL_TI_TEMPLATE (con), arg, args);
    }
  else
    {
      tree ovl = build_overload (DECL_TI_TEMPLATE (con), NULL_TREE);
      check = build_concept_check (ovl, arg, args);
    }
  if (apply_to_all_p)
    {
      check = make_pack_expansion (check);

      // Set the type to indicate that this expansion will get special
      // treatment during instantiation.
      //
      // TODO: Maybe this should be a different kind of node... one that
      // has all the same properties as a pack expansion, but has a definite
      // expansion when instantiated as part of an expression.
      //
      // As of now, this is a hack.
      TREE_TYPE (check) = boolean_type_node;
    }

  return check;
}

// Returns and chains a new parameter for PARAMETER_LIST which will conform
// to the prototype given by SRC_PARM.  The new parameter will have its
// identifier and location set according to IDENT and PARM_LOC respectively.
static tree
process_introduction_parm (tree parameter_list, tree src_parm)
{
  // If we have a pack, we should have a single pack argument which is the
  // placeholder we want to look at.
  bool is_parameter_pack = ARGUMENT_PACK_P (src_parm);
  if (is_parameter_pack)
      src_parm = TREE_VEC_ELT (ARGUMENT_PACK_ARGS (src_parm), 0);

  // At this point we should have a INTRODUCED_PARM_DECL, but we want to grab
  // the associated decl from it.  Also grab the stored identifier and location
  // that should be chained to it in a PARM_DECL.
  gcc_assert (TREE_CODE (src_parm) == INTRODUCED_PARM_DECL);

  tree ident = DECL_NAME (src_parm);
  location_t parm_loc = DECL_SOURCE_LOCATION (src_parm);

  // If we expect a pack and the deduced template is not a pack, or if the
  // template is using a pack and we didn't declare a pack, throw an error.
  if (is_parameter_pack != INTRODUCED_PACK_P (src_parm))
    {
      error_at (parm_loc, "can not match pack for introduced parameter");
      tree err_parm = build_tree_list (error_mark_node, error_mark_node);
      return chainon (parameter_list, err_parm);
    }

  src_parm = TREE_TYPE (src_parm);

  tree parm;
  bool is_non_type;
  if (TREE_CODE (src_parm) == TYPE_DECL)
    {
      is_non_type = false;
      parm = finish_template_type_parm (class_type_node, ident);
    }
  else if (TREE_CODE (src_parm) == TEMPLATE_DECL)
    {
      is_non_type = false;
      current_template_parms = DECL_TEMPLATE_PARMS (src_parm);
      parm = finish_template_template_parm (class_type_node, ident);
    }
  else
    {
      is_non_type = true;

      // Since we don't have a declarator, so we can copy the source
      // parameter and change the name and eventually the location.
      parm = copy_decl (src_parm);
      DECL_NAME (parm) = ident;
    }

  // Wrap in a TREE_LIST for process_template_parm.  Introductions do not
  // retain the defaults from the source template.
  parm = build_tree_list (NULL_TREE, parm);

  return process_template_parm (parameter_list, parm_loc, parm,
                                is_non_type, is_parameter_pack);
}

// Associates a constraint check to the current template based on the
// introduction parameters.  INTRO_LIST should be a TREE_VEC of
// INTRODUCED_PARM_DECLs containing a chained PARM_DECL which contains the
// identifier as well as the source location.  TMPL_DECL is the decl for the
// concept being used.  If we take some concept, C, this will form a check in
// the form of C<INTRO_LIST> filling in any extra arguments needed by the
// defaults deduced.
//
// Returns the template parameters as given from end_template_parm_list or
// NULL_TREE if the process fails.
tree
finish_concept_introduction (tree tmpl_decl, tree intro_list)
{
  // Deduce the concept check.
  tree expr = build_concept_check (tmpl_decl, NULL_TREE, intro_list);
  if (expr == error_mark_node)
    return NULL_TREE;

  tree parms = deduce_concept_introduction (expr);
  if (!parms)
    return NULL_TREE;

  // Build template parameter scope for introduction.
  tree parm_list = NULL_TREE;
  begin_template_parm_list ();

  // Produce a parameter for each introduction argument according to the
  // deduced form.
  int nargs = MIN (TREE_VEC_LENGTH (parms), TREE_VEC_LENGTH (intro_list));
  for (int n = 0; n < nargs; ++n)
    parm_list = process_introduction_parm (parm_list, TREE_VEC_ELT (parms, n));

  parm_list = end_template_parm_list (parm_list);
  for (int i = 0; i < TREE_VEC_LENGTH (parm_list); ++i)
    if (TREE_VALUE (TREE_VEC_ELT (parm_list, i)) == error_mark_node)
      {
        end_template_decl ();
        return error_mark_node;
      }

  // Build a concept check for our constraint.
  tree check_args = make_tree_vec (TREE_VEC_LENGTH (parms));

  // Start with introduction parameters.
  int n = 0;
  for (; n < TREE_VEC_LENGTH (parm_list); ++n)
    {
      tree parm = TREE_VEC_ELT (parm_list, n);
      TREE_VEC_ELT (check_args, n) = template_parm_to_arg (parm);
    }

  // If the template expects more parameters we should be able to use the
  // defaults from our deduced form.
  for (; n < TREE_VEC_LENGTH (parms); ++n)
    TREE_VEC_ELT (check_args, n) = TREE_VEC_ELT (parms, n);

  // Associate the constraint.
  tree reqs = build_concept_check (tmpl_decl, NULL_TREE, check_args);
  TEMPLATE_PARMS_CONSTRAINTS (current_template_parms) = reqs;

  return parm_list;
}

/*---------------------------------------------------------------------------
                        Constraint satisfaction 
---------------------------------------------------------------------------*/

/* The following functions determine if a constraint, when
   substituting template arguments, is satisfied. For convenience,
   satisfaction reduces a constraint to either true or false (and
   nothing else). */

namespace {

tree check_constraint (tree, tree, tsubst_flags_t, tree);

/* A predicate constraint is satisfied if its expression evaluates
   to true. If substitution into that node fails, the constraint
   is not satisfied ([temp.constr.pred]).

   Note that a predicate constraint is a constraint expression
   of type bool. If neither of those are true, the program is
   ill-formed; they are not SFINAE'able errors. */
tree
check_predicate_constraint (tree t, tree args, 
                             tsubst_flags_t complain, tree in_decl)
{
  tree expr = tsubst_expr (t, args, complain, in_decl, false);
  if (expr == error_mark_node)
    return boolean_false_node;

  tree result = fold_non_dependent_expr (expr);
  if (result == error_mark_node)
    return boolean_false_node;
  
  if (TREE_TYPE (result) != boolean_type_node)
    {
      error ("constraint %qE does not have type %qT", result, boolean_type_node);
      return boolean_false_node;
    }
  return result;
}

/* Check an expression constraint. The constraint is satisfied if
   substitution succeeds ([temp.constr.expr]). 

   Note that the expression is unevaluated. */
tree
check_expression_constraint (tree t, tree args, 
                             tsubst_flags_t complain, tree in_decl)
{
  cp_unevaluated guard;
  tree expr = EXPR_CONSTR_EXPR (t);
  tree check = tsubst_expr (expr, args, complain, in_decl, false);
  if (check == error_mark_node)
    return boolean_false_node;
  return boolean_true_node;
}

/* Check a type constraint. The constraint is satisfied if
   substitution succeeds. */
inline tree
check_type_constraint (tree t, tree args, 
                       tsubst_flags_t complain, tree in_decl)
{
  tree type = TYPE_CONSTR_TYPE (t);
  tree check = tsubst (type, args, complain, in_decl);
  if (check == error_mark_node)
    return boolean_false_node;
  return boolean_true_node;
}

/* Check an implicit conversion constraint. */
tree
check_implicit_conversion_constraint (tree t, tree args, 
                                      tsubst_flags_t complain, tree in_decl)
{
  tree expr = ICONV_CONSTR_EXPR (t);
  tree arg = tsubst_expr (expr, args, complain, in_decl, false);
  if (arg == error_mark_node)
    return boolean_false_node;
  tree from = TREE_TYPE (arg);

  tree type = ICONV_CONSTR_TYPE (t);
  tree to = tsubst (type, args, complain, in_decl);
  if (to == error_mark_node)
    return boolean_false_node;

  if (can_convert_arg (to, from, arg, LOOKUP_IMPLICIT, complain))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Check an argument deduction constraint.

   TODO: Implement me. We need generalized auto for this to work. */
inline tree
check_argument_deduction_constraint (tree /*t*/, tree /*args*/, 
                                     tsubst_flags_t /*complain*/, 
                                     tree /*in_decl*/)
{
  gcc_unreachable ();
  return boolean_false_node;
}

/* Check an exception constraint. An exception constraint for an
   expression e is satisfied when noexcept(e) is true. */
inline tree
check_exception_constraint (tree t, tree args, 
                             tsubst_flags_t complain, tree in_decl)
{
  tree expr = EXCEPT_CONSTR_EXPR (t);
  tree check = tsubst_expr (expr, args, complain, in_decl, false);
  if (check == error_mark_node)
    return boolean_false_node;

  if (expr_noexcept_p (check, complain))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* In an unevaluated context, the substitution of PARM_DECLs are not
   properly chained during substitution. Do that here. */
tree
fixup_constraint_vars (tree parms)
{
  if (!parms)
    return parms;

  tree p = TREE_CHAIN (parms);
  tree q = parms;
  while (p && TREE_VALUE (p) != void_type_node)
    {
      DECL_CHAIN (TREE_VALUE (q)) = TREE_VALUE (p);
      q = p;
      p = TREE_CHAIN (p);
    }
  return parms;
}

/* Register local specializations for each of parameter in
   PARMS and its corresponding substituted constraint variable
   in VARS. Returns VARS. */
tree
declare_constraint_vars (tree parms, tree vars)
{
  tree s = TREE_VALUE (vars);
  for (tree p = parms; p && !VOID_TYPE_P (TREE_VALUE (p)); p = TREE_CHAIN (p))
    {
      tree t = TREE_VALUE (p);
      if (DECL_PACK_P (t))
        {
          tree pack = extract_fnparm_pack (t, &s);
          register_local_specialization (pack, t);
        }
      else
        {
          register_local_specialization (s, t);
          s = TREE_CHAIN (s);
        }
    }
  return vars;
}

/* Substitute ARGS into the parameter list T, producing a sequence of
   constraint variables, declared in the current scope. If */
tree
tsubst_constraint_variables (tree t, tree args,
                             tsubst_flags_t complain, tree in_decl)
{
  tree vars = tsubst (t, args, complain, in_decl);
  if (vars == error_mark_node)
    return error_mark_node;
  return declare_constraint_vars (t, fixup_constraint_vars (vars));
}

/* Check a parameterized constraint. */
inline tree
check_parameterized_constraint (tree t, tree args, 
                                tsubst_flags_t complain, tree in_decl)
{
  local_specialization_stack stack;
  tree parms = PARM_CONSTR_PARMS (t);
  tree vars = tsubst_constraint_variables (parms, args, complain, in_decl);
  if (vars == error_mark_node)
    return boolean_false_node;
  
  tree constr = PARM_CONSTR_OPERAND (t);
  return check_constraint (constr, args, complain, in_decl);
}

/* Check that the conjunction of constraints is satisfied. Note
   that if left operand is not satisfied, the right operand
   is not checked. */
tree
check_conjunction (tree t, tree args, tsubst_flags_t complain, tree in_decl)
{
  tree t0 = check_constraint (TREE_OPERAND (t, 0), args, complain, in_decl);
  if (t0 == boolean_false_node)
    return t0;
  tree t1 = check_constraint (TREE_OPERAND (t, 1), args, complain, in_decl);
  if (t1 == boolean_false_node)
    return t1;
  return boolean_true_node;
}

/* Check that the disjunction of constraints is satisfied. Note
   that if the left operand is satisfied, the right operand is not
   checked. */
tree
check_disjunction (tree t, tree args, tsubst_flags_t complain, tree in_decl)
{
  tree t0 = check_constraint (TREE_OPERAND (t, 0), args, complain, in_decl);
  if (t0 == boolean_true_node)
    return t0;
  tree t1 = check_constraint (TREE_OPERAND (t, 1), args, complain, in_decl);
  if (t1 == boolean_true_node)
    return t0;
  return boolean_false_node;
}

/* Check that the constraint is satisfied, according to the rules 
   for that constraint. Note that each check_* function returns
   true or false, depending on whether it is satisfied or not. */
tree 
check_constraint (tree t, tree args, tsubst_flags_t complain, tree in_decl)
{
  if (!t)
    return boolean_false_node;
  switch (TREE_CODE (t))
  {
  case PRED_CONSTR:
    return check_predicate_constraint (t, args, complain, in_decl);
  case EXPR_CONSTR:
    return check_expression_constraint (t, args, complain, in_decl);
  case TYPE_CONSTR:
    return check_type_constraint (t, args, complain, in_decl);
  case ICONV_CONSTR:
    return check_implicit_conversion_constraint (t, args, complain, in_decl);
  case DEDUCT_CONSTR:
    return check_argument_deduction_constraint (t, args, complain, in_decl);
  case EXCEPT_CONSTR:
    return check_exception_constraint (t, args, complain, in_decl);
  case PARM_CONSTR:
    return check_parameterized_constraint (t, args, complain, in_decl);
  case CONJ_CONSTR:
    return check_conjunction (t, args, complain, in_decl);
  case DISJ_CONSTR:
    return check_disjunction (t, args, complain, in_decl);
  default:
    gcc_unreachable ();
    return boolean_false_node;
  }
}


// Substitute ARGS into the requirement body (list of requirements), T.
// Note that if any substitutions fail, then this is equivalent to
// returning false.
tree
tsubst_requirement_body (tree t, tree args, tree in_decl)
{
  tree r = NULL_TREE;
  while (t)
    {
      tree e = tsubst_expr (TREE_VALUE (t), args, tf_none, in_decl, false);
      if (e == error_mark_node)
        e = boolean_false_node;
      r = tree_cons (NULL_TREE, e, r);
      t = TREE_CHAIN (t);
    }
  return r;
}
} // namespace

// Substitute ARGS into the requires expression T.
tree
tsubst_requires_expr (tree /*t*/, tree /*args*/, 
                      tsubst_flags_t /*complain*/, tree /*in_decl*/)
{
  /* 
  local_specialization_stack stack;
  tree p = tsubst_local_parms (TREE_OPERAND (t, 0), args, complain, in_decl);
  tree r = tsubst_requirement_body (TREE_OPERAND (t, 1), args, in_decl);
  return finish_requires_expr (p, r);
  */
  return error_mark_node;
}

// Substitute ARGS into the valid-expr expression T.
tree
tsubst_validexpr_expr (tree t, tree args, tree in_decl)
{
  tree r = tsubst_expr (TREE_OPERAND (t, 0), args, tf_none, in_decl, false);
  return finish_validexpr_expr (r);
}

// Substitute ARGS into the valid-type expression T.
tree
tsubst_validtype_expr (tree t, tree args, tree in_decl)
{
  tree r = tsubst (TREE_OPERAND (t, 0), args, tf_none, in_decl);
  return finish_validtype_expr (r);
}

// Substitute ARGS into the constexpr expression T.
tree
tsubst_constexpr_expr (tree t, tree args, tree in_decl)
{
  tree r = tsubst_expr (TREE_OPERAND (t, 0), args, tf_none, in_decl, false);
  return finish_constexpr_expr (r);
}

// Substitute ARGS into the expr requirement T. Note that a requirement
// node is instantiated from a non-reduced context (e.g., static_assert).
tree
tsubst_expr_req (tree t, tree args, tree in_decl)
{
  tree r = NULL_TREE;
  for (tree l = TREE_OPERAND (t, 0); l; l = TREE_CHAIN (l))
    {
      tree e = tsubst_expr (TREE_VALUE (l), args, tf_none, in_decl, false);
      r = conjoin_constraints (r, e);
    }
  return r;
}

// Substitute ARGS into the type requirement T. Note that a requirement
// node is instantiated from a non-reduced context (e.g., static_assert).
tree
tsubst_type_req (tree t, tree args, tree in_decl)
{
  return tsubst_expr (TREE_OPERAND (t, 0), args, tf_none, in_decl, false);
}

// Substitute ARGS into the nested requirement T. Note that a requirement
// node is instantiated from a non-reduced context (e.g., static_assert).
tree
tsubst_nested_req (tree t, tree args, tree in_decl)
{
  return tsubst_expr (TREE_OPERAND (t, 0), args, tf_none, in_decl, false);
}

// Used in various contexts to control substitution. In particular, when
// non-zero, the substitution of NULL arguments into a type will still
// process the type as if passing non-NULL arguments, allowing type
// expressions to be fully elaborated during substitution.
int processing_constraint;

// Substitute the template arguments ARGS into the requirement
// expression REQS. Errors resulting from substitution are not
// diagnosed.
//
// If DO_NOT_FOLD is true, then the requirements are substituted as
// if parsing a template declaration, which causes the resulting expression
// to not be folded.
tree
tsubst_constraint_expr (tree reqs, tree args, bool do_not_fold)
{
  cp_unevaluated guard;
  ++processing_constraint;
  if (do_not_fold)
    ++processing_template_decl;
  tree r = tsubst_expr (reqs, args, tf_none, NULL_TREE, false);
  if (do_not_fold)
    --processing_template_decl;
  --processing_constraint;
  return r;
}

// Substitute into the constraint information, producing a new constraint
// record.
tree
tsubst_constraint_info (tree ci, tree args)
{
  if (!ci || ci == error_mark_node || !check_constraint_info (ci))
    return NULL_TREE;

  tree tr = NULL_TREE;
  if (tree r = CI_TEMPLATE_REQS (ci))
    tr = tsubst_constraint_expr (r, args, true);

  tree dr = NULL_TREE;
  if (tree r = CI_DECLARATOR_REQS (ci))
    dr = tsubst_constraint_expr (r, args, true);

  // TODO: This is re-normalizing and re-decomposing. We probably
  // don't need to do this.
  return build_constraints (tr, dr);
}

// -------------------------------------------------------------------------- //
// Constraint Satisfaction
//
// The following functions are responsible for the instantiation and
// evaluation of constraints.

namespace {
// Returns true iff the atomic constraint, REQ, is satisfied. This
// is the case when substitution succeeds and the resulting expression
// evaluates to true.
static bool
check_satisfied (tree req, tree args)
{
  // If any arguments are dependent, then we can't check the
  // requirements. Just return true.
  if (args && uses_template_parms (args))
    return true;

  // Instantiate and evaluate the requirements.
  req = tsubst_constraint_expr (req, args, false);
  if (req == error_mark_node)
    return false;

  // Reduce any remaining TRAIT_EXPR nodes before evaluating.
  req = fold_non_dependent_expr (req);

  // Requirements are satisfied when REQS evaluates to true.
  tree result = cxx_constant_value (req);
  return result == boolean_true_node;
}

} // namespace

// Check the instantiated declaration constraints.
bool
check_constraints (tree cinfo)
{
  // No constraints? Satisfied.
  if (!cinfo)
    return true;
  // Invalid constraints, not satisfied.
  else if (!valid_requirements_p (cinfo))
    return false;
  // Funnel back into the dependent checking branch. This forces
  // one more substitution through the constraints, which removes
  // all remaining expressions that are not constant expressions
  // (e.g., template-id expressions).
  else
    return check_satisfied (CI_NORMALIZED_CONSTRAINTS (cinfo), NULL_TREE);
}

// Check the constraints in CINFO against the given ARGS, returning
// true when the constraints are satisfied and false otherwise.
bool
check_constraints (tree cinfo, tree args)
{
  // If there are no constraints then this is trivally satisfied.
  if (!cinfo)
    return true;
  // Invlaid requirements cannot be satisfied.
  else if (!valid_requirements_p (cinfo))
    return false;
  else {
    return check_satisfied (CI_NORMALIZED_CONSTRAINTS (cinfo), args);
  }
}

// Check the constraints of the declaration or type T, against
// the specified arguments. Returns true if the constraints are
// satisfied and false otherwise.
bool
check_template_constraints (tree t, tree args)
{
  return check_constraints (get_constraints (t), args);
}

// -------------------------------------------------------------------------- //
// Constraint Relations
//
// Interfaces for determining equivalency and ordering of constraints.

// Returns true when A and B are equivalent constraints.
bool
equivalent_constraints (tree a, tree b)
{
  gcc_assert (!a || TREE_CODE (a) == CONSTRAINT_INFO);
  gcc_assert (!b || TREE_CODE (b) == CONSTRAINT_INFO);
  return cp_tree_equal (a, b);
}

// Returns true if the template declarations A and B have equivalent
// constraints. This is the case when A's constraints subsume B's and
// when B's also constrain A's.
bool
equivalently_constrained (tree d1, tree d2)
{
  gcc_assert (TREE_CODE (d1) == TREE_CODE (d2));
  return equivalent_constraints (get_constraints (d1), get_constraints (d2));
}

// Returns true when the the constraints in A subsume those in B.
bool
subsumes_constraints (tree a, tree b)
{
  gcc_assert (!a || TREE_CODE (a) == CONSTRAINT_INFO);
  gcc_assert (!b || TREE_CODE (b) == CONSTRAINT_INFO);
  return subsumes (a, b);
}

// Determines which of the declarations, A or B, is more constrained.
// That is, which declaration's constraints subsume but are not subsumed
// by the other's?
//
// Returns 1 if A is more constrained than B, -1 if B is more constrained
// than A, and 0 otherwise.
int
more_constrained (tree d1, tree d2)
{
  tree c1 = get_constraints (d1);
  tree c2 = get_constraints (d2);
  int winner = 0;
  if (subsumes_constraints (c1, c2))
    ++winner;
  if (subsumes_constraints (c2, c1))
    --winner;
  return winner;
}

// Returns true if d1 is at least as constrained as d2. That is, the
// associated constraints of d1 subsume those of d2, or both declarations
// are unconstrained.
bool
at_least_as_constrained (tree d1, tree d2)
{
  tree c1 = get_constraints (d1);
  tree c2 = get_constraints (d2);
  return subsumes_constraints (c1, c2);
}


// -------------------------------------------------------------------------- //
// Constraint Diagnostics

namespace {

// Given an arbitrary constraint expression, normalize it and
// then check it. We have to normalize so we don't accidentally
// instantiate concept declarations.
inline bool
check_diagnostic_constraints (tree reqs, tree args)
{
  return check_satisfied (normalize_constraint (reqs), args);
}

void diagnose_node (location_t, tree, tree);

// Diagnose a constraint failure for type trait expressions.
void
diagnose_trait (location_t loc, tree t, tree args)
{
  if (check_diagnostic_constraints (t, args))
    return;

  tree subst = tsubst_constraint_expr (t, args, true);

  if (subst == error_mark_node)
    {
      inform (input_location, "  substitution failure in %qE", t);
      return;
    }

  tree t1 = TRAIT_EXPR_TYPE1 (subst);
  tree t2 = TRAIT_EXPR_TYPE2 (subst);
  switch (TRAIT_EXPR_KIND (t))
    {
      case CPTK_HAS_NOTHROW_ASSIGN:
        inform (loc, "  %qT is not nothrow copy assignable", t1);
        break;
      case CPTK_HAS_NOTHROW_CONSTRUCTOR:
        inform (loc, "  %qT is not nothrow default constructible", t1);
        break;
      case CPTK_HAS_NOTHROW_COPY:
        inform (loc, "  %qT is not nothrow copy constructible", t1);
        break;
      case CPTK_HAS_TRIVIAL_ASSIGN:
        inform (loc, "  %qT is not trivially copy assignable", t1);
        break;
      case CPTK_HAS_TRIVIAL_CONSTRUCTOR:
        inform (loc, "  %qT is not trivially default constructible", t1);
        break;
      case CPTK_HAS_TRIVIAL_COPY:
        inform (loc, "  %qT is not trivially copy constructible", t1);
        break;
      case CPTK_HAS_TRIVIAL_DESTRUCTOR:
        inform (loc, "  %qT is not trivially destructible", t1);
        break;
      case CPTK_HAS_VIRTUAL_DESTRUCTOR:
        inform (loc, "  %qT does not have a virtual destructor", t1);
        break;
      case CPTK_IS_ABSTRACT:
        inform (loc, "  %qT is not an abstract class", t1);
        break;
      case CPTK_IS_BASE_OF:
        inform (loc, "  %qT is not a base of %qT", t1, t2);
        break;
      case CPTK_IS_CLASS:
        inform (loc, "  %qT is not a class", t1);
        break;
      case CPTK_IS_CONVERTIBLE_TO:
        inform (loc, "  %qT is not convertible to %qT", t1, t2);
        break;
      case CPTK_IS_EMPTY:
        inform (loc, "  %qT is not an empty class", t1);
        break;
      case CPTK_IS_ENUM:
        inform (loc, "  %qT is not an enum", t1);
        break;
      case CPTK_IS_FINAL:
        inform (loc, "  %qT is not a final class", t1);
        break;
      case CPTK_IS_LITERAL_TYPE:
        inform (loc, "  %qT is not a literal type", t1);
        break;
      case CPTK_IS_POD:
        inform (loc, "  %qT is not a POD type", t1);
        break;
      case CPTK_IS_POLYMORPHIC:
        inform (loc, "  %qT is not a polymorphic type", t1);
        break;
      case CPTK_IS_SAME_AS:
        inform (loc, "  %qT is not the same as %qT", t1, t2);
        break;
      case CPTK_IS_STD_LAYOUT:
        inform (loc, "  %qT is not an standard layout type", t1);
        break;
      case CPTK_IS_TRIVIAL:
        inform (loc, "  %qT is not a trivial type", t1);
        break;
      case CPTK_IS_UNION:
        inform (loc, "  %qT is not a union", t1);
        break;
      default:
        gcc_unreachable ();
    }
}

// Diagnose a failed concept check in concept indicated by T, where
// T is the result of resolve_constraint_check. Recursively analyze
// the nested requiremets for details.
void
diagnose_check (location_t loc, tree t, tree args)
{
  tree fn = TREE_VALUE (t);
  tree targs = TREE_PURPOSE (t);
  tree body = DECL_SAVED_TREE (fn);
  if (!body)
    return;

  inform (loc, "  failure in constraint %q#D", DECL_TI_TEMPLATE (fn));

  // Perform a mini-reduction on the constraint.
  if (TREE_CODE (body) == BIND_EXPR)
    body = BIND_EXPR_BODY (body);
  if (TREE_CODE (body) == RETURN_EXPR)
    body = TREE_OPERAND (body, 0);

  // Locally instantiate the body with the call's template args,
  // and recursively diagnose.
  body = tsubst_constraint_expr (body, targs, true);

  diagnose_node (loc, body, args);
}

// Diagnose constraint failures from the call expression T.
void
diagnose_call (location_t loc, tree t, tree args)
{
  if (check_diagnostic_constraints (t, args))
    return;

  // If this is a concept, we're going to recurse.
  // If it's just a call, then we can emit a simple message.
  if (tree check = resolve_constraint_check (t))
    diagnose_check (loc, check, args);
  else
    inform (loc, "  %qE evaluated to false", t);
}

// Diagnose constraint failures in a variable template-id T.
void
diagnose_var (location_t loc, tree t, tree args)
{
  // If the template-id isn't a variable template, it can't be a
  // valid constraint.
  if (!variable_template_p (TREE_OPERAND (t, 0)))
    {
      inform (loc, "  invalid constraint %qE", t);
      return;
    }

  if (check_diagnostic_constraints (t, args))
    return;

  tree var = DECL_TEMPLATE_RESULT (TREE_OPERAND (t, 0));
  tree body = DECL_INITIAL (var);
  tree targs = TREE_OPERAND (t, 1);
  tree subst = tsubst_constraint_expr (body, targs, true);

  inform (loc, "  failure in constraint %q#D", DECL_TI_TEMPLATE (var));

  diagnose_node (loc, subst, args);
}

// Diagnose specific constraint failures.
void
diagnose_requires (location_t loc, tree t, tree args)
{
  if (check_diagnostic_constraints (t, args))
    return;

  tree subst = tsubst_constraint_expr (t, args, true);

  // Print the header for the requires expression.
  tree parms = TREE_OPERAND (subst, 0);
  if (!VOID_TYPE_P (TREE_VALUE (parms)))
    inform (loc, "  requiring syntax with values %Z", TREE_OPERAND (subst, 0));

  // Create a new local specialization binding for the arguments.
  // This lets us instantiate sub-expressions separately from the
  // requires clause.
  local_specialization_stack locals;
  declare_constraint_vars (TREE_OPERAND (t, 0), TREE_OPERAND (subst, 0));

  // Iterate over the sub-requirements and try instantiating each.
  for (tree l = TREE_OPERAND (t, 1); l; l = TREE_CHAIN (l))
    diagnose_node (loc, TREE_VALUE (l), args);
}

static void
diagnose_validexpr (location_t loc, tree t, tree args)
{
  if (check_diagnostic_constraints (t, args))
    return;
  inform (loc, "    %qE is not a valid expression", TREE_OPERAND (t, 0));
}

static void
diagnose_validtype (location_t loc, tree t, tree args)
{
  if (check_diagnostic_constraints (t, args))
    return;

  // Substitute into the qualified name.
  tree name = TREE_OPERAND (t, 0);
  if (tree cxt = TYPE_CONTEXT (name))
    {
      tree id = TYPE_IDENTIFIER (name);
      cxt = tsubst (cxt, args, tf_none, NULL_TREE);
      name = build_qualified_name (NULL_TREE, cxt, id, false);
      inform (loc, "    %qE does not name a valid type", name);
    }
  else
    {
      inform (loc, "    %qT does not name a valid type", name);
    }
}

static void
diagnose_constexpr (location_t loc, tree t, tree args)
{
  if (check_diagnostic_constraints (t, args))
    return;
  inform (loc, "    %qE is not a constant expression", TREE_OPERAND (t, 0));
}

static void
diagnose_noexcept (location_t loc, tree t, tree args)
{
  if (check_diagnostic_constraints (t, args))
    return;
  inform (loc, "    %qE propagates exceptions", TREE_OPERAND (t, 0));
}

// Diagnose a constraint failure in the expression T.
void
diagnose_other (location_t loc, tree t, tree args)
{
  if (check_diagnostic_constraints (t, args))
    return;
  inform (loc, "  %qE evaluated to false", t);
}

// Diagnose a constraint failure in the subtree T.
void
diagnose_node (location_t loc, tree t, tree args)
{
  switch (TREE_CODE (t))
    {
    case TRUTH_ANDIF_EXPR:
      diagnose_node (loc, TREE_OPERAND (t, 0), args);
      diagnose_node (loc, TREE_OPERAND (t, 1), args);
      break;

    case TRUTH_ORIF_EXPR:
      // TODO: Design better diagnostics for dijunctions.
      diagnose_other (loc, t, args);
      break;

    case TRAIT_EXPR:
      diagnose_trait (loc, t, args);
      break;

    case CALL_EXPR:
      diagnose_call (loc, t, args);
      break;

    case REQUIRES_EXPR:
      diagnose_requires (loc, t, args);
      break;

    case VALIDEXPR_EXPR:
      diagnose_validexpr (loc, t, args);
      break;

    case VALIDTYPE_EXPR:
      diagnose_validtype (loc, t, args);
      break;

    case CONSTEXPR_EXPR:
      diagnose_constexpr (loc, t, args);
      break;

    case NOEXCEPT_EXPR:
      diagnose_noexcept (loc, t, args);
      break;

    case TEMPLATE_ID_EXPR:
      diagnose_var (loc, t, args);
      break;

    default:
      diagnose_other (loc, t, args);
      break;
    }
}

// Diagnose a constraint failure in the requirements expression REQS.
inline void
diagnose_requirements (location_t loc, tree reqs, tree args)
{
  diagnose_node (loc, reqs, args);
}

// Create a tree node representing the substitution of ARGS into
// the parameters of TMPL. The resulting structure is passed as an
// for diagnosing substitutions.
inline tree
make_subst (tree tmpl, tree args)
{
  tree subst = tree_cons (NULL_TREE, args, NULL_TREE);
  TREE_TYPE (subst) = DECL_TEMPLATE_PARMS (tmpl);
  return subst;
}

} // namespace

// Emit diagnostics detailing the failure ARGS to satisfy the constraints
// of the template declaration, TMPL.
void
diagnose_constraints (location_t loc, tree decl, tree args)
{
  tree ci = get_constraints (decl);

  // If the constraints could not be reduced, then we can't diagnose them.
  if (!valid_requirements_p (ci))
    {
      inform (loc, "  invalid constraints");
      return;
    }

  // FIXME: Re-think how we recurse through the expression to emit
  // diagnostics.

  // If this is a specialization of a template, we want to diagnose
  // the dependent constraints. Also update the template arguments.
  // if (DECL_USE_TEMPLATE (decl))
  //   {
  //     args = DECL_TI_ARGS (decl);
  //     decl = DECL_TI_TEMPLATE (decl);
  //   }

  // // Otherwise, diagnose the actual failed constraints.
  // if (TREE_CODE (decl) == TEMPLATE_DECL)
  //   inform (loc, "  constraints not satisfied %S", make_subst (decl, args));
  // else
  //   inform (loc, "  constraints not satisfied");

  inform (loc, "  constraints not satisfied");

  // Diagnose the constraints by recursively decomposing and
  // evaluating the template requirements.
  tree reqs = CI_ASSOCIATED_CONSTRAINTS (get_constraints (decl));
  diagnose_requirements (loc, reqs, args);
}
