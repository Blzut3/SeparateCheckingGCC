/* IPA reference lists.
   Copyright (C) 2010-2014 Free Software Foundation, Inc.
   Contributed by Jan Hubicka

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

struct cgraph_node;
class varpool_node;
class symtab_node;


/* How the reference is done.  */
enum GTY(()) ipa_ref_use
{
  IPA_REF_LOAD,
  IPA_REF_STORE,
  IPA_REF_ADDR,
  IPA_REF_ALIAS
};

/* Record of reference in callgraph or varpool.  */
struct GTY(()) ipa_ref
{
public:
  /* Remove reference.  */
  void remove_reference ();

  /* Return true when execution of reference can lead to return from
     function.  */
  bool cannot_lead_to_return ();

  /* Return reference list this reference is in.  */
  struct ipa_ref_list * referring_ref_list (void);

  /* Return reference list this reference is in.  */
  struct ipa_ref_list * referred_ref_list (void);

  symtab_node *referring;
  symtab_node *referred;
  gimple stmt;
  unsigned int lto_stmt_uid;
  unsigned int referred_index;
  ENUM_BITFIELD (ipa_ref_use) use:2;
  unsigned int speculative:1;
};

typedef struct ipa_ref ipa_ref_t;
typedef struct ipa_ref *ipa_ref_ptr;


/* List of references.  This is stored in both callgraph and varpool nodes.  */
struct GTY(()) ipa_ref_list
{
public:
  /* Return first reference in list or NULL if empty.  */
  struct ipa_ref *first_reference (void)
  {
    if (!vec_safe_length (references))
      return NULL;
    return &(*references)[0];
  }

  /* Return first referring ref in list or NULL if empty.  */
  struct ipa_ref *first_referring (void)
  {
    if (!referring.length ())
      return NULL;
    return referring[0];
  }

  /* Clear reference list.  */
  void clear (void)
  {
    referring.create (0);
    references = NULL;
  }

  /* Return number of references.  */
  unsigned int nreferences (void)
  {
    return vec_safe_length (references);
  }

  /* Store actual references in references vector.  */
  vec<ipa_ref_t, va_gc> *references;
  /* Referring is vector of pointers to references.  It must not live in GGC space
     or GGC will try to mark middle of references vectors.  */
  vec<ipa_ref_ptr>  GTY((skip)) referring;
};
