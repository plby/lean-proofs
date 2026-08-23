/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities
import ErdosProblems.Erdos240.BakerLemma3Concrete

/-!
# Explicit Hermite-factor budget at the p.52 coprime nodes

The p.52 completion uses the successor radius and only one quarter of the
`Sstep` budget.  Both are smaller than the terminal radius and multiplicity
already paid by the source Lemma-5 explicit-Hermite estimate.  The large
root reserve (`128 <= sqrt k`) also absorbs the extra fifth radius copy in
the arbitrary-node basis bound.
-/

noncomputable section

namespace Erdos240.VDPLParameters

open BakerLemma3Concrete

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  (P : VDPLParameters (Fin oldRank))

/-- The successor coprime radius is much smaller than the terminal
source-Lemma-5 radius; this quantitative form absorbs an extra radius copy. -/
theorem two_mul_R_succ_le_lemmaFiveLocalRadius (J : ℕ) :
    2 * P.R (J + 1) ≤ P.lemmaFiveLocalRadius J := by
  unfold lemmaFiveLocalRadius
  apply Nat.le_floor
  have hroot : (26 : ℝ) ≤ P.k ^ (1 / 2 : ℝ) :=
    (by norm_num : (26 : ℝ) ≤ 128).trans P.oneTwentyEight_le_k_rpow_half
  have hfac : 0 ≤ 16 * (((P.q ^ J : ℕ) : ℝ)) * P.h := by positivity
  calc
    ((2 * P.R (J + 1) : ℕ) : ℝ) =
        (16 * (((P.q ^ J : ℕ) : ℝ)) * P.h) * 26 := by
      simp only [R, q, pow_succ]
      push_cast
      ring
    _ ≤ (16 * (((P.q ^ J : ℕ) : ℝ)) * P.h) *
        P.k ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hroot hfac
    _ = 16 * (((P.q ^ J : ℕ) : ℝ)) * P.h *
        P.k ^ (1 / 2 : ℝ) := by ring

/-- The p.52 multiplicity is bounded by the terminal Lemma-5
multiplicity, including its final `+1`. -/
theorem Sstep_div_four_le_lemmaFiveLocalMultiplicity (J : ℕ) :
    P.Sstep J / 4 ≤ P.lemmaFiveLocalMultiplicity J := by
  unfold lemmaFiveLocalMultiplicity
  rw [P.Sstep_div_four_eq_floor_levelScale_div_thirtySix]
  have hident : ⌊P.levelScale J / 36⌋₊ =
      ⌊P.levelScale J / 6⌋₊ / 6 := by
    rw [show P.levelScale J / 36 = (P.levelScale J / 6) / 6 by ring,
      Nat.floor_div_ofNat]
  rw [hident]
  omega

/-- Exact arbitrary-node Hermite loss needed by the p.52 completion. -/
theorem coprime_explicitHermiteFactor_le_exp_twelfth
    {J : ℕ} (hJ : P.LevelOK J) :
    (P.q : ℝ) ^ (P.Sstep J / 4) *
        (2 : ℝ) ^ ((5 * P.R (J + 1) + 3) * (P.Sstep J / 4)) ≤
      Real.exp
        (sourceExponent P (P.C * Real.log P.OmegaOld) / 12) := by
  let R : ℕ := P.R (J + 1)
  let T : ℕ := P.Sstep J / 4
  let R₅ : ℕ := P.lemmaFiveLocalRadius J
  let T₅ : ℕ := P.lemmaFiveLocalMultiplicity J
  have hR : 5 * R ≤ 4 * R₅ := by
    have htwo := P.two_mul_R_succ_le_lemmaFiveLocalRadius J
    dsimp only [R, R₅] at htwo ⊢
    omega
  have hT : T ≤ T₅ := by
    simpa only [T, T₅] using
      P.Sstep_div_four_le_lemmaFiveLocalMultiplicity J
  have hq : (P.q : ℝ) ^ T ≤ (P.q : ℝ) ^ T₅ := by
    exact pow_le_pow_right₀ (by norm_num [q] : (1 : ℝ) ≤ P.q) hT
  have hindex : (5 * R + 3) * T ≤ (4 * R₅ + 3) * T₅ := by
    exact Nat.mul_le_mul (Nat.add_le_add_right hR 3) hT
  have htwo : (2 : ℝ) ^ ((5 * R + 3) * T) ≤
      (2 : ℝ) ^ ((4 * R₅ + 3) * T₅) :=
    pow_le_pow_right₀ (by norm_num) hindex
  have hfactor :
      (P.q : ℝ) ^ T * (2 : ℝ) ^ ((5 * R + 3) * T) ≤
        (P.q : ℝ) ^ T₅ *
          (2 : ℝ) ^ ((4 * R₅ + 3) * T₅) := by
    exact mul_le_mul hq htwo (by positivity) (by positivity)
  have hterminal := P.lemmaFive_explicitHermiteFactor_le_exp_twelfth hJ
  change (P.q : ℝ) ^ T * (2 : ℝ) ^ ((5 * R + 3) * T) ≤ _
  calc
    (P.q : ℝ) ^ T * (2 : ℝ) ^ ((5 * R + 3) * T) ≤
        (P.q : ℝ) ^ T₅ *
          (2 : ℝ) ^ ((4 * R₅ + 3) * T₅) := hfactor
    _ ≤ Real.exp ((P.C * P.Omega * Real.log P.OmegaOld *
        Real.log (P.Bsrc : ℝ)) / 12) := by
      simpa only [R₅, T₅] using hterminal
    _ = Real.exp
        (sourceExponent P (P.C * Real.log P.OmegaOld) / 12) := by
      congr 1
      unfold sourceExponent VDPLParameters.Omega
      ring

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.two_mul_R_succ_le_lemmaFiveLocalRadius
#print axioms Erdos240.VDPLParameters.Sstep_div_four_le_lemmaFiveLocalMultiplicity
#print axioms Erdos240.VDPLParameters.coprime_explicitHermiteFactor_le_exp_twelfth
