/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedDiagonalReplacement

/-! # Positive finite main term and the arithmetic face-majorant energy bound -/

namespace Erdos4b.FGKMT

noncomputable section

def commonFaceMainTerm (m M R : ℕ) : ℝ :=
  multivariateSieveConstant M (actualSieveDenominator false (m + 1)) m * Real.log R ^ m *
    dimensionFaceEnergy (m + 1) m

def commonPinnedMainTerm (m M R : ℕ) : ℝ :=
  (pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) * Real.log R) ^ 2 *
    commonFaceMainTerm m M R

def commonPinnedQuadratic (m M R : ℕ) (j : Fin (m + 1)) : ℝ :=
  finiteSieveQuadratic (fun q : commonPrimeUniverse M R => (q.val : ℝ) - 1)
    (commonPinnedCoefficient m R (fun q => q.val) j)

theorem commonFaceMainTerm_pos {m M R : ℕ} (hm : 1 ≤ m)
    (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) (hM : 0 < M) (hR : 1 < R)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) :
    0 < commonFaceMainTerm m M R := by
  have hP := multivariateSieveConstant_pos (k := m + 1) (by omega) hM
    (fun p hp hpk => hsmall p hp (by omega)) _
    (actualSieveDenominator_chain (by omega) (by omega : m ≤ m + 1) hsmall false)
  have hJ := dimensionFaceEnergy_pos (Nat.succ_pos m) hlog (by omega : m ≤ m + 1)
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  exact mul_pos (mul_pos hP (pow_pos hL m)) hJ

theorem pinnedGlobalNormalization_pos {α : Type*} [Fintype α] {m M : ℕ}
    (hm : 7 ≤ m) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hnot : ∀ q, ¬p q ∣ M) :
    0 < pinnedGlobalNormalization m M p := by
  have hphi : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  exact (show (0 : ℝ) < ((M.totient : ℝ) / M) / 2 by positivity).trans_le
    (pinnedGlobalNormalization_bounds hm hM hsmall hp hinj hnot).1

theorem commonPinnedMainTerm_pos {m M R : ℕ} (hm : 1 ≤ m)
    (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) (hM : 0 < M) (hR : 1 < R)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) :
    0 < commonPinnedMainTerm m M R := by
  have hB : 0 < pinnedGlobalNormalization m M
      (fun q : commonPrimeUniverse M R => q.val) :=
    pinnedGlobalNormalization_pos (seven_le_of_profile_log hlog) hM hsmall
      commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  exact mul_pos (pow_pos (mul_pos hB hL) 2) (commonFaceMainTerm_pos hm hlog hM hR hsmall)

theorem exists_commonPinnedFaceMajorantSum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      (m : ℝ) * (C * sieveProfileScale (m + 1) ^ 2 *
        modulusLogScale (M * R ^ (2 * (m + 1))) ^ 3 / Real.log R) ≤ 1 →
      commonPinnedFaceMajorantSum m M R ≤ 1200 * (m : ℝ) ^ 2 * commonFaceMainTerm m M R := by
  obtain ⟨C, hC, hmean⟩ := exists_majorantFaceSieveSum_energy_bound
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall hcost
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h := hmean (k := m + 1) (j := m - 1) (by omega) hlog hM hR (by omega) hsmall false
    (by simpa only [hm'] using hcost)
  rw [hm'] at h
  have hchain := actualSieveDenominator_chain (by omega : 2 ≤ m + 1)
    (by omega : 1 ≤ m + 1) hsmall false
  have hg (l : ℕ) (hl : l.Prime) (hlM : ¬l ∣ M) :
      0 ≤ actualSieveDenominator false (m + 1) l := by
    have h := (hchain 0 (by omega) l hl hlM).1
    simp only [Nat.cast_zero, add_zero] at h
    exact (half_pos (show (0 : ℝ) < l by exact_mod_cast hl.pos)).le.trans h
  calc
    _ ≤ majorantFaceSieveSum (m + 1) M (actualSieveDenominator false (m + 1)) R m :=
      sum_assignment_face_majorant_le_box (Nat.succ_pos m) hlog hR
        commonPrimeUniverse_prime Subtype.val_injective _ hg
    _ ≤ 1200 * (m : ℝ) ^ 2 *
        multivariateSieveConstant M (actualSieveDenominator false (m + 1)) m * Real.log R ^ m *
          dimensionFaceEnergy (m + 1) m := h
    _ = _ := by unfold commonFaceMainTerm; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedMainTerm_pos
#print axioms Erdos4b.FGKMT.exists_commonPinnedFaceMajorantSum_bound
