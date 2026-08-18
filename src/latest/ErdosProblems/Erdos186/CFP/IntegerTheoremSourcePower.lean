/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.IntegerTheoremAssembly

/-!
# Choosing the preprocessing rank from the source exponents

The CFP preprocessing horizon must dominate the source interval after a
fixed natural power.  These two elementary lemmas choose that power and
transport the real source bounds to the required natural inequality.
-/

namespace Erdos186.CFP.IntegerTheoremAssembly

noncomputable section

set_option autoImplicit false

/-- A natural rank can absorb any fixed source exponent into the positive
scale exponent `eta`. -/
theorem exists_natRank_ge_exponentRatio (beta eta : ℝ) (heta : 0 < eta) :
    ∃ D : ℕ, 2 ≤ D ∧ beta ≤ eta * ((D - 1 : ℕ) : ℝ) := by
  let r : ℝ := max 1 (beta / eta)
  let D : ℕ := Nat.ceil r + 1
  have hrNonneg : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hrOne : 1 ≤ r := le_max_left _ _
  have hrCeil : r ≤ (Nat.ceil r : ℝ) := Nat.le_ceil r
  have hceilOne : 1 ≤ Nat.ceil r := by
    exact_mod_cast hrOne.trans hrCeil
  have hbetaRatio : beta / eta ≤ r := le_max_right _ _
  have hbeta : beta ≤ eta * r := by
    have := (div_le_iff₀ heta).mp hbetaRatio
    simpa only [mul_comm] using this
  refine ⟨D, by dsimp only [D]; omega, ?_⟩
  have hmul : eta * r ≤ eta * (Nat.ceil r : ℝ) :=
    mul_le_mul_of_nonneg_left hrCeil heta.le
  have hcastSub : ((D - 1 : ℕ) : ℝ) = (Nat.ceil r : ℝ) := by
    dsimp only [D]
    rw [Nat.add_sub_cancel]
  rw [hcastSub]
  exact hbeta.trans hmul

/-- The real endpoint and scale hypotheses imply the natural power window
used by the retained Bilu--Freiman preprocessing theorem. -/
theorem sourceEndpoint_le_scale_pow
    {m n s D : ℕ} {beta eta : ℝ}
    (hm : 1 ≤ m) (hD : beta ≤ eta * ((D - 1 : ℕ) : ℝ))
    (hn : (n : ℝ) ≤ Real.rpow (m : ℝ) beta)
    (hs : Real.rpow (m : ℝ) eta ≤ (s : ℝ)) :
    n ≤ s ^ (D - 1) := by
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hpowExponent : Real.rpow (m : ℝ) beta ≤
      Real.rpow (m : ℝ) (eta * (D - 1 : ℕ)) :=
    Real.rpow_le_rpow_of_exponent_le hmReal hD
  have hrewrite : Real.rpow (m : ℝ) (eta * (D - 1 : ℕ)) =
      (Real.rpow (m : ℝ) eta) ^ (D - 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_mul hmNonneg eta ((D - 1 : ℕ) : ℝ)
  have hsPow : (Real.rpow (m : ℝ) eta) ^ (D - 1) ≤
      ((s : ℝ) ^ (D - 1)) := by
    exact pow_le_pow_left₀ (Real.rpow_nonneg hmNonneg eta) hs _
  have hcast : (n : ℝ) ≤ ((s ^ (D - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact hn.trans (hpowExponent.trans (hrewrite.trans_le hsPow))
  exact_mod_cast hcast

end

end Erdos186.CFP.IntegerTheoremAssembly

#print axioms Erdos186.CFP.IntegerTheoremAssembly.exists_natRank_ge_exponentRatio
#print axioms Erdos186.CFP.IntegerTheoremAssembly.sourceEndpoint_le_scale_pow
