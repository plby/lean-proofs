/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTDimensionMean
import ErdosProblems.Erdos4b.FGKMTVariationalBounds

/-!
# Uniform relative error for the true face energy

The face cutoff has a norm proportional to its squared first mass.
That factor cancels against the proved face-energy lower bound. All
constants are chosen before the dimension and arithmetic parameters.
-/

namespace Erdos4b.FGKMT

noncomputable section

private theorem relative_error_on_face {E P L A B J δ : ℝ} {j : ℕ}
    (hP : 0 < P) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hJ : B * A ^ j / 4 ≤ J) (hδ : 0 ≤ δ)
    (herror : |E| / (P * (L * A) ^ j) ≤ B * δ) :
    |E| / (P * L ^ j * J) ≤ 4 * δ := by
  have hJ0 : 0 < J := lt_of_lt_of_le (by positivity) hJ
  have hmain : 0 < P * L ^ j * J := by positivity
  have htensor : 0 < P * (L * A) ^ j := by positivity
  have hcomp : B * (P * (L * A) ^ j) ≤ 4 * (P * L ^ j * J) := by
    have hj : B * A ^ j ≤ J * 4 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hJ
    calc
      _ = (P * L ^ j) * (B * A ^ j) := by rw [mul_pow]; ring
      _ ≤ (P * L ^ j) * (J * 4) := mul_le_mul_of_nonneg_left hj (by positivity)
      _ = _ := by ring
  apply (div_le_iff₀ hmain).mpr
  calc
    _ ≤ (B * δ) * (P * (L * A) ^ j) := (div_le_iff₀ htensor).mp herror
    _ = δ * (B * (P * (L * A) ^ j)) := by ring
    _ ≤ δ * (4 * (P * L ^ j * J)) := mul_le_mul_of_nonneg_left hcomp hδ
    _ = _ := by ring

theorem exists_dimensionFace_energy_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → j ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      (j : ℝ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ 1 →
      |cutoffSieveSum M (actualSieveDenominator pinned k) R j
          (fun t => dimensionProfileFactor k t ^ 2) (fun t => dimensionFaceCutoff k t ^ 2) 0 -
        multivariateSieveConstant M (actualSieveDenominator pinned k) j * Real.log R ^ j *
          dimensionFaceEnergy k j| /
        (multivariateSieveConstant M (actualSieveDenominator pinned k) j * Real.log R ^ j *
          dimensionFaceEnergy k j) ≤
        (j : ℝ) *
          (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) := by
  obtain ⟨K, hK, hψ⟩ := exists_sieveCutoff_bounded
  obtain ⟨C₀, hC₀, hbound⟩ := exists_actualCutoffSieveSum_relative_error
  obtain ⟨Cq, hCq, hQ⟩ := exists_dimensionFaceCutoff_sq_bounded
  let C : ℝ := (8 * Cq + 1) * C₀ * (4 * K + 6)
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hlog hM hR hj hsmall pinned htotal
  have hk0 : 0 < k := by omega
  have hb := profile_scales_bounds hk0 hlog
  let Ω : ℝ := (4 * K + 6) * sieveProfileScale k ^ 2
  let P := multivariateSieveConstant M (actualSieveDenominator pinned k) j
  let L := Real.log R
  let ε₀ : ℝ := C₀ * Ω * modulusLogScale (M * R ^ k) ^ 3 / L
  let ε : ℝ := C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / L
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hR)
  have hscale : 0 ≤ modulusLogScale (M * R ^ k) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hΩ : 0 ≤ Ω := by dsimp only [Ω]; positivity
  have hε₀ : 0 ≤ ε₀ := by dsimp only [ε₀]; positivity
  have heq : ε = (8 * Cq + 1) * ε₀ := by dsimp only [ε, ε₀, Ω, C]; ring
  have hεle : ε₀ ≤ ε := by rw [heq]; nlinarith
  have htotal₀ : (j : ℝ) * ε₀ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hεle (Nat.cast_nonneg j)).trans htotal
  have hP : 0 < P := multivariateSieveConstant_pos hk0 hM
    (fun p hp hpk => hsmall p hp (by omega)) _
    (actualSieveDenominator_chain hk hj hsmall pinned)
  have h := hbound hk hM hR hj hsmall pinned
    ((dimensionProfileFactor_contDiff k (n := 1)).pow 2)
    (fun t _ht => sq_nonneg (dimensionProfileFactor k t))
    (dimensionProfileMass_pos hk0 hlog) hΩ
    (fun t ht => sieveFactor_sq_deriv_bound (zero_le_one.trans hb.1) hb.2.1 ht.1 hψ)
    (sieveFactor_sq_cost hb.1 hb.2.1 (by linarith [hb.2.2.1])
      (by linarith [hb.2.2.2]) hψ) htotal₀
    (fun t => dimensionFaceCutoff k t ^ 2) (Cq * dimensionProfileFirstMass k ^ 2) (hQ k) 0
  have hfirst := dimensionProfileFirstMass_pos hk0 hlog
  have hrelative := relative_error_on_face hP hL (dimensionProfileMass_pos hk0 hlog)
    (by positivity : 0 < dimensionProfileFirstMass k ^ 2)
    (dimensionFaceEnergy_bounds hk0 hlog hj).1
    (by positivity : 0 ≤ 2 * Cq * (j : ℝ) * ε₀)
    (show _ ≤ dimensionProfileFirstMass k ^ 2 * (2 * Cq * (j : ℝ) * ε₀) from by
      convert h using 1 <;> dsimp only [P, L, dimensionProfileMass, ε₀] <;> ring)
  calc
    _ ≤ 4 * (2 * Cq * (j : ℝ) * ε₀) := hrelative
    _ ≤ (j : ℝ) * ε := by
      rw [heq]
      nlinarith [mul_nonneg (Nat.cast_nonneg j) hε₀]
    _ = _ := by dsimp only [ε, L]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_dimensionFace_energy_relative_error
