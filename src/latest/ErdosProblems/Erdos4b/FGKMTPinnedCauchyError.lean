/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedModulusGrouping
import BoundedGaps.Maynard.ImprovedGPY.S2TrivialDiscrepancy

/-!
# The pinned prime error reduced to an unweighted progression sum

The existing finite Cauchy--Schwarz and squarefree totient mean are
used with all dimensions explicit. No prime-level witness or analytic
distribution estimate is assumed in this reduction.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

theorem maxProgressionDiscrepancy_mul_le_div {x W D : ℕ}
    (hW : 0 < W) (hD : 0 < D) (hbound : W * D ≤ x + 1) :
    maxProgressionDiscrepancy x (W * D) ≤ 3 * ((x + 1 : ℕ) : ℝ) / D.totient := by
  have hWD := Nat.mul_pos hW hD
  have hphi : D.totient ≤ (W * D).totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr hWD)
      (Nat.totient_dvd_of_dvd (dvd_mul_left D W))
  apply (maxProgressionDiscrepancy_le_three_mul_div hWD hbound).trans
  apply div_le_div₀ (by positivity) le_rfl
  · exact_mod_cast Nat.totient_pos.mpr hD
  · exact_mod_cast hphi

def commonPinnedDiscrepancySum (W M R A B : ℕ) : ℝ :=
  ∑ D ∈ commonPinnedModulusRange M R,
    (maxProgressionDiscrepancy B (W * D) + maxProgressionDiscrepancy A (W * D))

theorem commonPinnedDiscrepancySum_nonneg (W M R A B : ℕ) :
    0 ≤ commonPinnedDiscrepancySum W M R A B := by
  exact Finset.sum_nonneg fun D _ => add_nonneg
    (maxProgressionDiscrepancy_nonneg _ _) (maxProgressionDiscrepancy_nonneg _ _)

def commonPinnedCauchyEnvelope (m W M R A B : ℕ) : ℝ :=
  Real.sqrt (3 * ((A : ℝ) + B + 2) * (1 + Real.log (R ^ 2 : ℕ)) ^ (2 * (3 * m) ^ 2)) *
    Real.sqrt (commonPinnedDiscrepancySum W M R A B)

theorem commonPinnedCauchyEnvelope_nonneg (m W M R A B : ℕ) :
    0 ≤ commonPinnedCauchyEnvelope m W M R A B :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem commonPinnedWeightedDiscrepancy_le_cauchy {m W M R A B : ℕ}
    (hW : 0 < W) (hAB : A ≤ B) (hmod : W * R ^ 2 ≤ A + 1) :
    commonPinnedWeightedDiscrepancy m W M R A B ≤
      commonPinnedCauchyEnvelope m W M R A B := by
  let S := commonPinnedModulusRange M R
  let E := fun D => maxProgressionDiscrepancy B (W * D) + maxProgressionDiscrepancy A (W * D)
  let X : ℝ := 3 * ((A : ℝ) + B + 2)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hE (D : ℕ) (_hD : D ∈ S) : 0 ≤ E D :=
    add_nonneg (maxProgressionDiscrepancy_nonneg _ _) (maxProgressionDiscrepancy_nonneg _ _)
  have hbound (D : ℕ) (hD : D ∈ S) : E D ≤ X / D.totient := by
    obtain ⟨hDpos, hDR, _hsq, _hcop⟩ := mem_commonPinnedModulusRange.mp hD
    have hDA : W * D ≤ A + 1 := (Nat.mul_le_mul_left W hDR).trans hmod
    have hDB : W * D ≤ B + 1 := hDA.trans (by omega)
    calc
      _ ≤ 3 * ((B + 1 : ℕ) : ℝ) / D.totient +
          3 * ((A + 1 : ℕ) : ℝ) / D.totient := add_le_add
        (maxProgressionDiscrepancy_mul_le_div hW hDpos hDB)
        (maxProgressionDiscrepancy_mul_le_div hW hDpos hDA)
      _ = _ := by dsimp [X]; push_cast; ring
  have hcauchy := sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun D => (((3 * m) ^ ω D : ℕ) : ℝ)) E (fun D => (D.totient : ℝ)) X hE hbound
  have htau := sum_tauPow_sq_div_totient_le_one_add_log (3 * m) (R ^ 2) S
    (Finset.filter_subset _ _) (fun D hD => (mem_commonPinnedModulusRange.mp hD).2.2.1)
  apply hcauchy.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htau hX)

theorem exists_commonPinnedProgressionError_cauchy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m W M R A B : ℕ, 1 ≤ m → 1 < R → 0 < W →
      A ≤ B → W * R ^ 2 ≤ A + 1 →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) → ∀ j : Fin (m + 1),
      commonPinnedProgressionError m W M R A B j ≤
        Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
          commonPinnedCauchyEnvelope m W M R A B := by
  obtain ⟨C, hC, hgroup⟩ := exists_commonPinnedProgressionError_grouped_bound
  refine ⟨C, hC, ?_⟩
  intro m W M R A B hm hR hW hAB hmod hsmall j
  exact (hgroup m W M R A B hm hR hsmall j).trans
    (mul_le_mul_of_nonneg_left (commonPinnedWeightedDiscrepancy_le_cauchy hW hAB hmod)
      (Real.exp_pos _).le)

theorem exists_commonPinnedPrimeMass_cauchy_error :
    ∃ C : ℝ, 0 < C ∧ ∀ m W M R Q A B : ℕ, ∀ y : ℝ,
      1 ≤ m → 1 < R → 0 < W → W ∣ M → A ≤ B → W * R ^ 2 ≤ A + 1 →
      Q.Prime → R < Q → (∀ q : ℕ, q.Prime → q ∣ W → q ≤ A) →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      ∀ h : Fin (m + 1) → ℕ, Function.Injective h → (∀ i, h i < 2 * (m + 1) ^ 2) →
      ∀ j : Fin (m + 1), (Q : ℝ) ≤ y → (h j : ℝ) * B ≤ y →
      |commonPinnedPrimeMass m W M R Q A B y h j -
          primePreSieveDensity W Q (fun i => (h i : ℤ)) j *
            (commonPinnedPrimeSet A B).card * commonPinnedQuadratic m M R j| ≤
        (W : ℝ) * Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
          commonPinnedCauchyEnvelope m W M R A B := by
  classical
  obtain ⟨C, hC, herror⟩ := exists_commonPinnedProgressionError_cauchy_bound
  refine ⟨C, hC, ?_⟩
  intro m W M R Q A B y hm hR hW hWM hAB hmod hQ hRQ hWsmall hsmall h hinj hshift j hQy hBy
  have hcard : ((primePreSieveResidues W Q (fun i => (h i : ℤ)) j).card : ℝ) ≤ W := by
    exact_mod_cast (show (primePreSieveResidues W Q (fun i => (h i : ℤ)) j).card ≤ W from
      (Finset.card_filter_le _ _).trans_eq (Finset.card_range W))
  calc
    _ ≤ ((primePreSieveResidues W Q (fun i => (h i : ℤ)) j).card : ℝ) *
        commonPinnedProgressionError m W M R A B j :=
      commonPinnedPrimeMass_quadratic_error hW hWM hAB hQ hRQ hWsmall hsmall h hinj hshift j hQy hBy
    _ ≤ (W : ℝ) * commonPinnedProgressionError m W M R A B j :=
      mul_le_mul_of_nonneg_right hcard (commonPinnedProgressionError_nonneg _ _ _ _ _ _ _)
    _ ≤ (W : ℝ) * (Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
        commonPinnedCauchyEnvelope m W M R A B) :=
      mul_le_mul_of_nonneg_left (herror m W M R A B hm hR hW hAB hmod hsmall j) (Nat.cast_nonneg _)
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedWeightedDiscrepancy_le_cauchy
#print axioms Erdos4b.FGKMT.exists_commonPinnedProgressionError_cauchy_bound
#print axioms Erdos4b.FGKMT.exists_commonPinnedPrimeMass_cauchy_error
