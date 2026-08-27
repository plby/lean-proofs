/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialRetainedVortexLaw
import ErdosProblems.Erdos207.SourceAugmentedCoefficientPower
import ErdosProblems.Erdos207.RetainedVortexPowerGeometry

/-! # One exact coefficient interface for the zero and positive retained prefixes -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourcePrefixRawY (q i : ℕ) : ℝ≥0 :=
  if i = 0 then 2*exactBankVortexOrderCoefficient q 0 else
    ((2 : ℝ≥0)^(12*(q+2)^2)+1)*exactBankVortexOrderCoefficient q i

def sourcePrefixY (q i : ℕ) : ℝ≥0 := max 1 (sourcePrefixRawY q i)

def sourcePrefixZ {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (bank : TripleSystemOn V) (i j : ℕ) : ℝ≥0 :=
  max 1 (if i = 0 then
    2*((subsetsUpToCard bank q).card*(exactBankVortexOrderCoefficient q 0 : ℝ≥0))+
      exactBankVortexCoefficient j 0 else
    2*sourcePrefixRawY q i+exactBankVortexCoefficient j i)

def sourcePrefixFixedZ (q i j : ℕ) : ℝ≥0 :=
  if i = 0 then 2*(exactBankVortexOrderCoefficient q 0 : ℝ≥0)+exactBankVortexCoefficient j 0 else
    2*sourcePrefixRawY q i+exactBankVortexCoefficient j i

theorem one_le_sourcePrefixY (q i : ℕ) : 1 ≤ sourcePrefixY q i := le_max_left _ _

theorem one_le_sourcePrefixZ {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (bank : TripleSystemOn V) (i j : ℕ) : 1 ≤ sourcePrefixZ q bank i j := le_max_left _ _

theorem HasAbsorberSourcePrefixBounds.at_stage
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    {bank : TripleSystemOn V} {W : Vortex V ell}
    (hsource : HasAbsorberSourcePrefixBounds q bank W) (i : Fin (ell+1))
    (j : ℕ) (hj : 4 ≤ j) (hjq : j ≤ q) :
    SourceVortexWellSpread (W.prefix i) j (absorberInducedConfigurationsOn q j bank)
      (sourcePrefixY q i.val) (sourcePrefixZ q bank i.val j) := by
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simpa only [Fin.val_zero, sourcePrefixY, sourcePrefixRawY, sourcePrefixZ, if_pos rfl, ite_true]
      using (hsource.2 j hj hjq).mono (le_max_right 1 _) (le_max_right 1 _)
  · have hk : k.val+1 ≠ 0 := by omega
    simpa only [Fin.val_succ, sourcePrefixY, sourcePrefixRawY, sourcePrefixZ, if_neg hk]
      using (hsource.1 k j hj hjq).mono (le_max_right 1 _) (le_max_right 1 _)

theorem InitialPowerVortexPackage.sourcePrefixZ_power
    {q h n ell t rootPower step Rfixed : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hbank : powerBankSubsetCoefficient q ≤ t)
    (hfixed : powerBankSubsetExponent q rootPower+2 ≤ Rfixed)
    (i j : ℕ) (hconstant : sourcePrefixFixedZ q i j ≤ t) :
    sourcePrefixZ q P.B i j ≤ (t : ℝ≥0)^retainedRatioExponent Rfixed step i := by
  have ht : (1 : ℝ≥0) ≤ t := by exact_mod_cast P.base_ge_one
  apply max_le (one_le_pow₀ ht) ?_
  by_cases hi : i = 0
  · subst i
    simp only [retainedRatioExponent, ite_true]
    exact P.zero_prefix_source_coefficient_power hbank hfixed j
      (by simpa only [sourcePrefixFixedZ, if_pos rfl, ite_true] using hconstant)
  · simp only [if_neg hi, retainedRatioExponent]
    have hc : 2*sourcePrefixRawY q i+exactBankVortexCoefficient j i ≤ t := by
      simpa only [sourcePrefixFixedZ, if_neg hi] using hconstant
    have hpow : (t : ℝ≥0) ≤ (t : ℝ≥0)^(2*step+1) := by
      simpa only [pow_one] using (pow_le_pow_right₀ ht (show 1 ≤ 2*step+1 by omega))
    exact hc.trans hpow

theorem sourcePrefixZ_le_base_of_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V] (q i j : ℕ) (bank : TripleSystemOn V)
    (t : ℝ≥0) (ht : 1 ≤ t) (hi : i ≠ 0) (hconstant : sourcePrefixFixedZ q i j ≤ t) :
    sourcePrefixZ q bank i j ≤ t := by
  simpa only [sourcePrefixZ, sourcePrefixFixedZ, if_neg hi, max_le_iff] using And.intro ht hconstant

end

end Erdos207
