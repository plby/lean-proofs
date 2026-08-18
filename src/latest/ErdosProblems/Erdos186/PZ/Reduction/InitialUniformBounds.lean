/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.InitialEstimates
import ErdosProblems.Erdos186.PZ.Reduction.InitialNoDimensionIncrease
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeOneStep

/-!
# Uniform real bounds for the initial selected progression
-/

namespace Erdos186.PZ.Reduction

noncomputable section

/-- A single explicit coefficient dominating both initial Lemma-8 and
initial Lemma-6 constants on a bounded-rank run. -/
def initialUniformCost (D0 D ell : ℕ) : ℝ :=
  (2 : ℝ) ^ D0 * (2 * D + 1 : ℕ) ^ ell *
    ((D : ℝ) ^ D0 + (2 : ℝ) ^ ell)

theorem initialUniformCost_pos {D0 D ell : ℕ} (hD : 0 < D) :
    0 < initialUniformCost D0 D ell := by
  dsimp [initialUniformCost]
  positivity

/-- The exact initial integer estimates, a bounded rank/denominator, and the
strong scale lower bound imply the coarse and high-rank real estimates used
by the quantitative trace. -/
theorem initial_uniform_bounds_of_witness
    {ell s rankBound k loss m D0 D : ℕ} {a : ℝ}
    (B : CFP.IntegerBox ell) {A : Finset (LatticePoint ell)}
    (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    (W : CFP.EnhancedCFPWitness (normalizeSet B A) s rankBound k loss)
    (hrank : W.rank ≤ D0) (hden : W.scaleDen ≤ D)
    (hD : 0 < D) (hm : 0 < m)
    (hscale : Real.rpow (m : ℝ) a ≤ (D : ℝ) * (k : ℝ)) :
    (W.progression.volume : ℝ) ≤
        initialUniformCost D0 D ell * (B.carrier.card : ℝ) ∧
      (ell < W.rank →
        (W.progression.volume : ℝ) ≤
          initialUniformCost D0 D ell *
            (Real.rpow (m : ℝ) (-a)) ^ (W.rank - ell) *
              (B.carrier.card : ℝ)) := by
  have htwoRank : (2 : ℝ) ^ W.rank ≤ (2 : ℝ) ^ D0 :=
    pow_le_pow_right₀ (by norm_num) hrank
  have hdenBase : 2 * W.scaleDen + 1 ≤ 2 * D + 1 := by omega
  have hdenPow : (((2 * W.scaleDen + 1 : ℕ) : ℝ) ^ ell) ≤
      (((2 * D + 1 : ℕ) : ℝ) ^ ell) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdenBase) _
  have hcostHigh :
      (2 : ℝ) ^ W.rank * ((2 * W.scaleDen : ℕ) : ℝ) ^ ell *
          (D : ℝ) ^ D0 ≤
        initialUniformCost D0 D ell := by
    have hdenBase' : 2 * W.scaleDen ≤ 2 * D + 1 := by omega
    have hdenPow' : (((2 * W.scaleDen : ℕ) : ℝ) ^ ell) ≤
        (((2 * D + 1 : ℕ) : ℝ) ^ ell) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdenBase') _
    dsimp [initialUniformCost]
    calc
      (2 : ℝ) ^ W.rank * ((2 * W.scaleDen : ℕ) : ℝ) ^ ell *
          (D : ℝ) ^ D0 ≤
        (2 : ℝ) ^ D0 * ((2 * D + 1 : ℕ) : ℝ) ^ ell *
          (D : ℝ) ^ D0 := by gcongr
      _ ≤ (2 : ℝ) ^ D0 * ((2 * D + 1 : ℕ) : ℝ) ^ ell *
          ((D : ℝ) ^ D0 + (2 : ℝ) ^ ell) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  constructor
  · have hraw := initial_noDimensionIncrease B hA hAB W
    have hrawReal : (W.progression.volume : ℝ) ≤
        (2 : ℝ) ^ W.rank *
          (((2 * W.scaleDen + 1 : ℕ) : ℝ) ^ ell *
            ((2 : ℝ) ^ ell * (B.carrier.card : ℝ))) := by
      exact_mod_cast hraw
    calc
      (W.progression.volume : ℝ) ≤ _ := hrawReal
      _ ≤ (2 : ℝ) ^ D0 * (((2 * D + 1 : ℕ) : ℝ) ^ ell *
          ((2 : ℝ) ^ ell * (B.carrier.card : ℝ))) := by gcongr
      _ ≤ initialUniformCost D0 D ell * (B.carrier.card : ℝ) := by
        dsimp [initialUniformCost]
        have hnonneg : 0 ≤ (B.carrier.card : ℝ) := by positivity
        calc
          (2 : ℝ) ^ D0 * (((2 * D + 1 : ℕ) : ℝ) ^ ell *
              ((2 : ℝ) ^ ell * (B.carrier.card : ℝ))) =
            ((2 : ℝ) ^ D0 * ((2 * D + 1 : ℕ) : ℝ) ^ ell *
              (2 : ℝ) ^ ell) * (B.carrier.card : ℝ) := by ring
          _ ≤ ((2 : ℝ) ^ D0 * ((2 * D + 1 : ℕ) : ℝ) ^ ell *
              ((D : ℝ) ^ D0 + (2 : ℝ) ^ ell)) *
                (B.carrier.card : ℝ) := by
            gcongr
            exact le_add_of_nonneg_left (by positivity)
  · intro hrankHigh
    let q := W.rank - ell
    have hq : q ≤ D0 := by dsimp [q]; omega
    have hk : 0 < k := W.k_pos
    have hinv := inv_pow_dilation_le hm hD hk hq hscale
    have hraw := initial_dimensionIncrease B hA hAB W (Nat.le_of_lt hrankHigh)
    have hrawReal : (k : ℝ) ^ q * (W.progression.volume : ℝ) ≤
        (2 : ℝ) ^ W.rank * ((2 * W.scaleDen : ℕ) : ℝ) ^ ell *
          (B.carrier.card : ℝ) := by
      exact_mod_cast hraw
    have hkpow : 0 < (k : ℝ) ^ q := by positivity
    have hdivide : (W.progression.volume : ℝ) ≤
        ((2 : ℝ) ^ W.rank * ((2 * W.scaleDen : ℕ) : ℝ) ^ ell *
          (B.carrier.card : ℝ)) * (((k : ℝ) ^ q)⁻¹) := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hkpow).2 (by simpa [mul_comm] using hrawReal)
    calc
      (W.progression.volume : ℝ) ≤ _ := hdivide
      _ ≤ ((2 : ℝ) ^ W.rank * ((2 * W.scaleDen : ℕ) : ℝ) ^ ell *
          (B.carrier.card : ℝ)) *
            ((D : ℝ) ^ D0 * (Real.rpow (m : ℝ) (-a)) ^ q) := by gcongr
      _ = ((2 : ℝ) ^ W.rank * ((2 * W.scaleDen : ℕ) : ℝ) ^ ell *
          (D : ℝ) ^ D0) * (Real.rpow (m : ℝ) (-a)) ^ q *
            (B.carrier.card : ℝ) := by ring
      _ ≤ initialUniformCost D0 D ell *
          (Real.rpow (m : ℝ) (-a)) ^ q *
            (B.carrier.card : ℝ) := by
        gcongr
        exact pow_nonneg (Real.rpow_nonneg (by positivity) _) _
      _ = initialUniformCost D0 D ell *
          (Real.rpow (m : ℝ) (-a)) ^ (W.rank - ell) *
            (B.carrier.card : ℝ) := rfl

end

end Erdos186.PZ.Reduction
