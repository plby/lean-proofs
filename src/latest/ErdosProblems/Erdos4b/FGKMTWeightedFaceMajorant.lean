/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTWeightedMajorant
import ErdosProblems.Erdos4b.FGKMTMajorantFaceEnergy

/-!
# The arithmetic face-majorant sum

In positive tail dimension, any one long-factor summand dominates the
short tensor. The exact full positive-ray face integral is consequently
at most five short first masses times the tail majorant. Its arithmetic
square sum has a uniform quadratic-dimensional bound on the true face
energy scale, for both actual denominator families.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem shortTensor_le_oneLongTensor {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (i : Fin j) {t : Fin j → ℝ}
    (ht : ∀ q, 0 ≤ t q) :
    (∏ q, dimensionProfileFactor k (t q)) ≤ oneLongTensor k j i t := by
  unfold oneLongTensor
  apply Finset.prod_le_prod
  · intro q _hq
    exact dimensionProfileFactor_nonneg k (t q)
  · intro q _hq
    unfold oneLongFactor
    split_ifs
    · exact dimensionProfileFactor_le_long hk hlog (ht q)
    · exact le_rfl

theorem shortTensor_le_majorant {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : 0 < j) {t : Fin j → ℝ}
    (ht : ∀ q, 0 ≤ t q) :
    (∏ q, dimensionProfileFactor k (t q)) ≤ sieveProfileMajorant k j t := by
  classical
  let i : Fin j := ⟨0, hj⟩
  exact (shortTensor_le_oneLongTensor hk hlog i ht).trans
    (Finset.single_le_sum (fun q _hq => oneLongTensor_nonneg k j q t) (Finset.mem_univ i))

theorem majorantFaceValue_nonneg (k j : ℕ) (t : Fin j → ℝ) :
    0 ≤ majorantFaceValue k j t := by
  have hd : 0 ≤ dimensionLongFirstMass k :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (dimensionLongFactor_nonneg k)
  exact add_nonneg
    (mul_nonneg hd (Finset.prod_nonneg fun q _hq => dimensionProfileFactor_nonneg k (t q)))
    (mul_nonneg (dimensionProfileFirstMass_nonneg k) (sieveProfileMajorant_nonneg k j t))

theorem majorantFaceValue_le_majorant {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : 0 < j) {t : Fin j → ℝ}
    (ht : ∀ q, 0 ≤ t q) :
    majorantFaceValue k j t ≤
      5 * dimensionProfileFirstMass k * sieveProfileMajorant k j t := by
  have hprod : 0 ≤ ∏ q, dimensionProfileFactor k (t q) :=
    Finset.prod_nonneg fun q _hq => dimensionProfileFactor_nonneg k (t q)
  calc
    _ ≤ (4 * dimensionProfileFirstMass k) * (∏ q, dimensionProfileFactor k (t q)) +
        dimensionProfileFirstMass k * sieveProfileMajorant k j t :=
      add_le_add (mul_le_mul_of_nonneg_right (dimensionLongFirstMass_le_four hk hlog) hprod)
        le_rfl
    _ ≤ (4 * dimensionProfileFirstMass k) * sieveProfileMajorant k j t +
        dimensionProfileFirstMass k * sieveProfileMajorant k j t :=
      add_le_add (mul_le_mul_of_nonneg_left (shortTensor_le_majorant hk hlog hj ht)
        (mul_nonneg (by norm_num) (dimensionProfileFirstMass_nonneg k))) le_rfl
    _ = _ := by ring

theorem majorantFaceValue_sq_le_majorant {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : 0 < j) {t : Fin j → ℝ}
    (ht : ∀ q, 0 ≤ t q) :
    majorantFaceValue k j t ^ 2 ≤
      25 * dimensionProfileFirstMass k ^ 2 * sieveProfileMajorant k j t ^ 2 := by
  calc
    _ ≤ (5 * dimensionProfileFirstMass k * sieveProfileMajorant k j t) ^ 2 :=
      pow_le_pow_left₀ (majorantFaceValue_nonneg k j t)
        (majorantFaceValue_le_majorant hk hlog hj ht) 2
    _ = _ := by ring

def majorantFaceSieveSum (k M : ℕ) (g : ℕ → ℝ) (R j : ℕ) : ℝ :=
  ∑ e : Fin j → Fin (R ^ 2 + 1),
    majorantFaceValue k j (fun q => Real.log (e q).val / Real.log R) ^ 2 *
      roughSieveWeight M g (∏ q, (e q).val)

theorem majorantFaceSieveSum_eq_integral {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (M R j : ℕ) (g : ℕ → ℝ) :
    majorantFaceSieveSum k M g R j =
      ∑ e : Fin j → Fin (R ^ 2 + 1),
        (∫ x in Set.Ioi (0 : ℝ), sieveProfileMajorant k (j + 1)
          (Fin.cons x (fun q => Real.log (e q).val / Real.log R))) ^ 2 *
            roughSieveWeight M g (∏ q, (e q).val) := by
  unfold majorantFaceSieveSum
  simp_rw [majorantFaceValue_eq_integral hk hlog]

theorem majorantFaceSieveSum_le_majorant {k M R j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : 0 < j) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → 0 ≤ g p) :
    majorantFaceSieveSum k M g R j ≤
      25 * dimensionProfileFirstMass k ^ 2 * majorantSieveSum k M g R j := by
  classical
  unfold majorantFaceSieveSum majorantSieveSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _he
  have ht (q : Fin j) : 0 ≤ Real.log (e q).val / Real.log R :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  calc
    _ ≤ (25 * dimensionProfileFirstMass k ^ 2 *
        sieveProfileMajorant k j (fun q => Real.log (e q).val / Real.log R) ^ 2) *
          roughSieveWeight M g (∏ q, (e q).val) :=
      mul_le_mul_of_nonneg_right (majorantFaceValue_sq_le_majorant hk hlog hj ht)
        (roughSieveWeight_nonneg M g hg _)
    _ = _ := by ring

theorem exists_majorantFaceSieveSum_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → j + 1 ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      (j + 1 : ℕ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      majorantFaceSieveSum k M (actualSieveDenominator pinned k) R (j + 1) ≤
        1200 * (j + 1 : ℕ) ^ 2 *
          multivariateSieveConstant M (actualSieveDenominator pinned k) (j + 1) *
          Real.log R ^ (j + 1) * dimensionFaceEnergy k (j + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_majorantSieveSum_energy_bound
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hlog hM hR hj hsmall pinned htotal
  have hk0 : 0 < k := by omega
  let P := multivariateSieveConstant M (actualSieveDenominator pinned k) (j + 1)
  let L := Real.log R
  let a := dimensionProfileMass k
  let b := dimensionProfileFirstMass k
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hR)
  have hchain := actualSieveDenominator_chain hk hj hsmall pinned
  have hP : 0 < P := multivariateSieveConstant_pos hk0 hM
    (fun p hp hpk => hsmall p hp (by omega)) _ hchain
  have hg (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) :
      0 ≤ actualSieveDenominator pinned k p := by
    have h := (hchain 0 (Nat.zero_lt_succ j) p hp hpM).1
    simp only [Nat.cast_zero, add_zero] at h
    exact (half_pos (show (0 : ℝ) < p by exact_mod_cast hp.pos)).le.trans h
  have hI : dimensionProfileEnergy k (j + 1) ≤ a ^ (j + 1) :=
    (dimensionProfileEnergy_bounds hk0 hlog hj).2
  have hJ : b ^ 2 * a ^ (j + 1) ≤ 4 * dimensionFaceEnergy k (j + 1) := by
    have h := (dimensionFaceEnergy_bounds hk0 hlog hj).1
    change b ^ 2 * a ^ (j + 1) / 4 ≤ dimensionFaceEnergy k (j + 1) at h
    linarith
  calc
    _ ≤ (25 * b ^ 2) * majorantSieveSum k M (actualSieveDenominator pinned k) R (j + 1) :=
      majorantFaceSieveSum_le_majorant hk0 hlog (Nat.zero_lt_succ j) _ hg
    _ ≤ (25 * b ^ 2) *
        (12 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1) * dimensionProfileEnergy k (j + 1)) :=
      mul_le_mul_of_nonneg_left (hbound hk hlog hM hR hj hsmall pinned htotal) (by positivity)
    _ ≤ (25 * b ^ 2) * (12 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1) * a ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI (by positivity)) (by positivity)
    _ = (300 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1)) * (b ^ 2 * a ^ (j + 1)) := by ring
    _ ≤ (300 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1)) *
        (4 * dimensionFaceEnergy k (j + 1)) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by dsimp only [P, L]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.majorantFaceValue_sq_le_majorant
#print axioms Erdos4b.FGKMT.majorantFaceSieveSum_eq_integral
#print axioms Erdos4b.FGKMT.exists_majorantFaceSieveSum_energy_bound
