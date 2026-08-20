/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.DedekindZeroFree.Basic

/-!
# Nonvanishing of the Dedekind zeta function on `Re s = 1`

This file packages the de la Vallée Poussin boundary theorem both for the meromorphic
continuation of the raw Dedekind zeta function and for AINTLIB's entire completion.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Complex NumberField
open ContinuedZeta

noncomputable section

/-- The meromorphic continuation of a Dedekind zeta function has no zero on the line
`Re s = 1`, away from its pole at `s = 1`. -/
theorem continuedDedekindZeta_ne_zero_of_re_eq_one
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s.re = 1) (hs1 : s ≠ 1) :
    continuedDedekindZeta K s ≠ 0 :=
  DedekindZeroFree.continuedDedekindZeta_ne_zero_of_re_eq_one K hs hs1

/-- The meromorphic continuation of a Dedekind zeta function is nonzero on the closed
half-plane `Re s ≥ 1`, except at the pole `s = 1`. -/
theorem continuedDedekindZeta_ne_zero_of_one_le_re
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    continuedDedekindZeta K s ≠ 0 := by
  rcases hs.eq_or_lt with hseq | hslt
  · exact continuedDedekindZeta_ne_zero_of_re_eq_one K hseq.symm hs1
  · rw [continuedDedekindZeta_eq_dedekindZeta K hslt]
    exact DedekindResidue.dedekindZeta_ne_zero_of_one_lt_re K hslt

/-- AINTLIB's entire function extending `s * (s - 1) * Λₖ(s)` has no zero on the
closed half-plane `Re s ≥ 1`. -/
theorem completedDedekindZetaEntire_ne_zero_of_one_le_re
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 ≤ s.re) :
    DedekindResidue.completedDedekindZetaEntire K s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · exact DedekindResidue.completedDedekindZetaEntire_one_ne_zero K
  · have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num at hs
    intro hH
    have hcont := continuedDedekindZeta_ne_zero_of_one_le_re K hs hs1
    apply hcont
    rw [continuedDedekindZeta, hH, zero_div, zero_mul]

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
