/* Definitions for branch prediction routines in the GNU compiler.
   Copyright (C) 2001-2014 Free Software Foundation, Inc.

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

#ifndef GCC_PREDICT_H
#define GCC_PREDICT_H

/* Random guesstimation given names.
   PROB_VERY_UNLIKELY should be small enough so basic block predicted
   by it gets below HOT_BB_FREQUENCY_FRACTION.  */
#define PROB_VERY_UNLIKELY	(REG_BR_PROB_BASE / 2000 - 1)
#define PROB_EVEN		(REG_BR_PROB_BASE / 2)
#define PROB_VERY_LIKELY	(REG_BR_PROB_BASE - PROB_VERY_UNLIKELY)
#define PROB_ALWAYS		(REG_BR_PROB_BASE)
#define PROB_UNLIKELY           (REG_BR_PROB_BASE / 5 - 1)
#define PROB_LIKELY             (REG_BR_PROB_BASE - PROB_UNLIKELY)

#define DEF_PREDICTOR(ENUM, NAME, HITRATE, FLAGS) ENUM,
enum br_predictor
{
#include "predict.def"

  /* Upper bound on non-language-specific builtins.  */
  END_PREDICTORS
};
#undef DEF_PREDICTOR
enum prediction
{
   NOT_TAKEN,
   TAKEN
};

extern void predict_insn_def (rtx_insn *, enum br_predictor, enum prediction);
extern int counts_to_freqs (void);
extern void handle_missing_profiles (void);
extern void estimate_bb_frequencies (bool);
extern const char *predictor_name (enum br_predictor);
extern tree build_predict_expr (enum br_predictor, enum prediction);
extern void tree_estimate_probability (void);
extern void compute_function_frequency (void);
extern void rebuild_frequencies (void);

#endif  /* GCC_PREDICT_H */
