/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFaceProfile
import ErdosProblems.Erdos4b.FGKMTTupleUpperReindex
import ErdosProblems.Erdos4b.FGKMTFaceMean

/-! # Exact arithmetic face diagonal and full-support face majorant -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def commonFaceDiagonal (m M R : ℕ) : ℝ :=
  ∑ r : commonPrimeUniverse M R → Option (Fin m),
    sieveFaceProfile (m + 1) m (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r)) ^ 2 *
      roughSieveWeight M (actualSieveDenominator false (m + 1))
        (assignmentPrimeProduct (fun q => q.val) r)

theorem commonFaceDiagonal_eq_cutoff {m M R : ℕ} (hR : 1 < R) :
    commonFaceDiagonal m M R =
      cutoffSieveSum M (actualSieveDenominator false (m + 1)) R m
        (fun t => dimensionProfileFactor (m + 1) t ^ 2)
        (fun t => dimensionFaceCutoff (m + 1) t ^ 2) 0 := by
  have hsupport (r : Fin m → ℕ) (hr : ∀ i, 0 < r i) (hprod : R ≤ ∏ i, r i) :
      sieveFaceProfile (m + 1) m (sieveLogTuple R r) ^ 2 = 0 := by
    rw [sieveFaceProfile_logTuple_zero_of_product_ge hR r hr hprod]
    norm_num
  calc
    _ = ∑ e : Fin m → Fin (R + 1),
        sieveFaceProfile (m + 1) m (sieveLogTuple R (fun i => (e i).val)) ^ 2 *
          roughSieveWeight M (actualSieveDenominator false (m + 1)) (∏ i, (e i).val) :=
      sum_assignments_eq_sum_box m M R (actualSieveDenominator false (m + 1))
        (fun r => sieveFaceProfile (m + 1) m (sieveLogTuple R r) ^ 2) hsupport
    _ = _ := by
      unfold cutoffSieveSum
      apply Finset.sum_congr rfl
      intro e _he
      simp only [sieveFaceProfile, sieveLogTuple, mul_pow, Finset.prod_pow, zero_add]

theorem exists_commonFaceDiagonal_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      (m : ℝ) * (C * sieveProfileScale (m + 1) ^ 2 *
        modulusLogScale (M * R ^ (m + 1)) ^ 3 / Real.log R) ≤ 1 →
      |commonFaceDiagonal m M R -
        multivariateSieveConstant M (actualSieveDenominator false (m + 1)) m * Real.log R ^ m *
          dimensionFaceEnergy (m + 1) m| /
        (multivariateSieveConstant M (actualSieveDenominator false (m + 1)) m * Real.log R ^ m *
          dimensionFaceEnergy (m + 1) m) ≤
        (m : ℝ) * (C * sieveProfileScale (m + 1) ^ 2 *
          modulusLogScale (M * R ^ (m + 1)) ^ 3 / Real.log R) := by
  obtain ⟨C, hC, hmean⟩ := exists_dimensionFace_energy_relative_error
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall hcost
  rw [commonFaceDiagonal_eq_cutoff hR]
  exact hmean (by omega : 2 ≤ m + 1) hlog hM hR (by omega : m ≤ m + 1) hsmall false hcost

theorem sum_assignment_face_majorant_le_box {α : Type*} [Fintype α] [DecidableEq α]
    {k m M R : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) (hR : 1 < R)
    {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (g : ℕ → ℝ) (hg : ∀ l : ℕ, l.Prime → ¬l ∣ M → 0 ≤ g l) :
    (∑ r : α → Option (Fin m),
      majorantFaceValue k m (sieveLogTuple R (assignmentPrimeTuple p r)) ^ 2 *
        roughSieveWeight M g (assignmentPrimeProduct p r)) ≤ majorantFaceSieveSum k M g R m := by
  apply sum_assignments_le_sum_box_of_coord_support hp hinj m M (R ^ 2) g hg
    (fun t => majorantFaceValue k m (sieveLogTuple R t) ^ 2) (fun _ => sq_nonneg _)
  intro t ht i
  by_contra hi
  have hiR : (R : ℝ) ^ 2 ≤ t i := by exact_mod_cast (by omega : R ^ 2 ≤ t i)
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hcoord : 2 ≤ sieveLogTuple R t i := by
    apply (le_div_iff₀ hlogR).mpr
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (R : ℝ) ^ 2) hiR
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  exact ht (by rw [majorantFaceValue_zero_of_coord_ge_two hk hlog i hcoord]; norm_num)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonFaceDiagonal_eq_cutoff
#print axioms Erdos4b.FGKMT.exists_commonFaceDiagonal_relative_error
#print axioms Erdos4b.FGKMT.sum_assignment_face_majorant_le_box
