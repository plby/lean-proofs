/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteWeightedMajorant
import ErdosProblems.Erdos4b.FGKMTFaceAssignmentMean
import ErdosProblems.Erdos4b.FGKMTFaceAssignmentVariation
import ErdosProblems.Erdos4b.FGKMTPinnedMainTerm

/-! # The pinned absolute-kernel face majorant with dimension-independent normalization -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_absoluteFaceMajorantSieveSum_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j a : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → 1 ≤ a → a ≤ 2 → j + 1 + a ≤ k + 1 →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      (j + 1 : ℕ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      majorantFaceSieveSum k M (absoluteSieveDenominator a k) R (j + 1) ≤
        1200 * Real.exp 4 * (j + 1 : ℕ) ^ 2 *
          multivariateSieveConstant M (fun p => (p : ℝ) - k) (j + 1) *
          Real.log R ^ (j + 1) * dimensionFaceEnergy k (j + 1) := by
  obtain ⟨C, hC, hmean⟩ := exists_absoluteMajorantSieveSum_energy_bound
  refine ⟨C, hC, ?_⟩
  intro k M R j a hk hlog hM hR ha ha2 hj hsmall htotal
  have hk0 : 0 < k := by omega
  have hjk : j + 1 ≤ k := by omega
  let P := multivariateSieveConstant M (fun p => (p : ℝ) - k) (j + 1)
  let L := Real.log R
  let b := dimensionProfileFirstMass k
  have hP : 0 < P := by
    have h := multivariateSieveConstant_pos hk0 hM
      (fun p hp hpk => hsmall p hp (by omega)) _
      (actualSieveDenominator_chain hk hjk hsmall false)
    have hg : actualSieveDenominator false k = (fun p : ℕ => (p : ℝ) - k) := by
      funext p
      simp only [actualSieveDenominator, Bool.false_eq_true, if_false]
    rw [hg] at h
    exact h
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hR)
  have hg (p : ℕ) (hp : p.Prime) (_hpM : ¬p ∣ M) :
      0 ≤ absoluteSieveDenominator a k p := by
    apply div_nonneg (sq_nonneg _)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have haR : (a : ℝ) ≤ 2 := by exact_mod_cast ha2
    linarith
  have hI := (dimensionProfileEnergy_bounds hk0 hlog hjk).2
  have hJ : b ^ 2 * dimensionProfileMass k ^ (j + 1) ≤ 4 * dimensionFaceEnergy k (j + 1) := by
    have h := (dimensionFaceEnergy_bounds hk0 hlog hjk).1
    change b ^ 2 * dimensionProfileMass k ^ (j + 1) / 4 ≤ _ at h
    linarith
  calc
    _ ≤ (25 * b ^ 2) * majorantSieveSum k M (absoluteSieveDenominator a k) R (j + 1) :=
      majorantFaceSieveSum_le_majorant hk0 hlog (Nat.zero_lt_succ j) _ hg
    _ ≤ (25 * b ^ 2) * (12 * Real.exp 4 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1) *
        dimensionProfileEnergy k (j + 1)) :=
      mul_le_mul_of_nonneg_left (hmean hk hlog hM hR ha ha2 hj hsmall htotal) (by positivity)
    _ ≤ (25 * b ^ 2) * (12 * Real.exp 4 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1) *
        dimensionProfileMass k ^ (j + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (300 * Real.exp 4 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1)) *
        (b ^ 2 * dimensionProfileMass k ^ (j + 1)) := by ring
    _ ≤ (300 * Real.exp 4 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1)) *
        (4 * dimensionFaceEnergy k (j + 1)) := mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by dsimp only [P, L]; ring

variable {α : Type*} [Fintype α] [DecidableEq α]

def pinnedCommonKernelWeight (m : ℕ) (p : α → ℕ) (r : α → Option (Fin m)) : ℝ :=
  assignmentScalarWeight (fun q => ((p q : ℝ) - 2) / ((p q : ℝ) - (m + 1)) ^ 2) r

def pinnedMovedKernelWeight (m : ℕ) (p : α → ℕ) (r : α → Option (Fin m)) : ℝ :=
  assignmentScalarWeight (fun q => 1 / ((p q : ℝ) - (m + 1)) ^ 2) r

def absolutePinnedFaceMajorantSum (m R : ℕ) (p : α → ℕ) : ℝ :=
  ∑ r, primeAssignmentFaceMajorant (m + 1) m R p r ^ 2 * pinnedCommonKernelWeight m p r

omit [DecidableEq α] in
theorem pinnedCommonKernelWeight_nonneg {m : ℕ} {p : α → ℕ}
    (hp : ∀ q, 2 ≤ p q) (r : α → Option (Fin m)) : 0 ≤ pinnedCommonKernelWeight m p r :=
  assignmentScalarWeight_nonneg (fun q => div_nonneg
    (sub_nonneg.mpr (by exact_mod_cast hp q)) (sq_nonneg _)) r

theorem absolutePinnedFaceMajorantSum_le_box {m M R : ℕ}
    (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) (hR : 1 < R) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hnot : ∀ q, ¬p q ∣ M) :
    absolutePinnedFaceMajorantSum m R p ≤
      majorantFaceSieveSum (m + 1) M (absoluteSieveDenominator 2 (m + 1)) R m := by
  classical
  have hweight (r : α → Option (Fin m)) : pinnedCommonKernelWeight m p r =
      roughSieveWeight M (absoluteSieveDenominator 2 (m + 1)) (assignmentPrimeProduct p r) := by
    have h := assignmentScalarWeight_eq_rough hp hinj hnot (absoluteSieveDenominator 2 (m + 1)) r
    simpa only [pinnedCommonKernelWeight, absoluteSieveDenominator, one_div_div,
      Nat.cast_add, Nat.cast_one] using h
  unfold absolutePinnedFaceMajorantSum
  simp_rw [hweight]
  have hg (l : ℕ) (hl : l.Prime) (_hlM : ¬l ∣ M) :
      0 ≤ absoluteSieveDenominator 2 (m + 1) l :=
    div_nonneg (sq_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hl.two_le))
  simpa only [primeAssignmentFaceMajorant] using
    sum_assignment_face_majorant_le_box (m := m) (Nat.succ_pos m) hlog hR hp hinj _ hg

omit [Fintype α] [DecidableEq α] in
theorem exists_absolutePinnedFaceMajorantSum_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : Type*) [DecidableEq β] [Fintype β],
      ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) → 0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      (m : ℝ) * (C * sieveProfileScale (m + 1) ^ 2 *
        modulusLogScale (M * R ^ (2 * (m + 1))) ^ 3 / Real.log R) ≤ 1 →
      ∀ (p : β → ℕ), (∀ q, (p q).Prime) → Function.Injective p → (∀ q, ¬p q ∣ M) →
        absolutePinnedFaceMajorantSum m R p ≤
          1200 * Real.exp 4 * (m : ℝ) ^ 2 * commonFaceMainTerm m M R := by
  obtain ⟨C, hC, hmean⟩ := exists_absoluteFaceMajorantSieveSum_energy_bound
  refine ⟨C, hC, ?_⟩
  intro β _ _ m M R hm hlog hM hR hsmall hcost p hp hinj hnot
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h := hmean (k := m + 1) (j := m - 1) (a := 2) (by omega) hlog hM hR
    (by omega) (by omega) (by omega) hsmall (by simpa only [hm'] using hcost)
  rw [hm', Nat.cast_ofNat] at h
  refine (absolutePinnedFaceMajorantSum_le_box hlog hR hp hinj hnot).trans ?_
  have hg : actualSieveDenominator false (m + 1) =
      (fun p : ℕ => (p : ℝ) - (m + 1 : ℕ)) := by
    funext p
    simp only [actualSieveDenominator, Bool.false_eq_true, if_false]
  simpa only [commonFaceMainTerm, hg, mul_assoc] using h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_absoluteFaceMajorantSieveSum_energy_bound
#print axioms Erdos4b.FGKMT.absolutePinnedFaceMajorantSum_le_box
#print axioms Erdos4b.FGKMT.exists_absolutePinnedFaceMajorantSum_energy_bound
