/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMajorantArithmetic
import ErdosProblems.Erdos4b.FGKMTMajorantSliceMean
import ErdosProblems.Erdos4b.FGKMTPinnedNormalizationBounds

/-!
# The actual pinned arithmetic majorant on the global normalization scale

The scalar sum retains its entire `R^2` support. The factor four comes
from its harmonic upper bound and the finite Euler product lower bound;
no face integral is divided out.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem seven_le_of_profile_log {m : ℕ} (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) :
    7 ≤ m := by
  have hm0 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have h := Real.log_le_sub_one_of_pos hm0
  have hmR : (7 : ℝ) ≤ m := by
    push_cast at h hlog
    linarith
  exact_mod_cast hmR

theorem pinned_majorant_scale_bound {J G E S K L V B : ℝ}
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hE : 1 / 2 ≤ E) (hB : (G * E) * K = B)
    (hJ : J ≤ G * S) (hS : S ≤ 2 * K * L * V) :
    J ≤ 4 * B * L * V := by
  calc
    J ≤ G * S := hJ
    _ ≤ G * (2 * K * L * V) := mul_le_mul_of_nonneg_left hS hG
    _ = (2 * G) * (K * L * V) := by ring
    _ ≤ (4 * (G * E)) * (K * L * V) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg (mul_nonneg hK hL) hV)
    _ = 4 * B * L * V := by rw [← hB]; ring

theorem exists_pinnedMajorantValue_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ l : ℕ, l.Prime → l ≤ 2 * (m + 1) ^ 2 → l ∣ M) →
      ∀ (α : Type*) [DecidableEq α] [Fintype α] (p : α → ℕ),
        (∀ q, (p q).Prime) → Function.Injective p → (∀ q, ¬p q ∣ M) →
        ∀ (j : Fin (m + 1)) (r : α → Option (Fin m)),
          C * (m + 1 : ℕ) * sieveProfileScale (m + 1) *
              modulusLogScale (M * assignmentPrimeProduct p r) ^ 3 ≤ Real.log R →
          pinnedMajorantValue m R p j r ≤
            4 * pinnedGlobalNormalization m M p * Real.log R *
              majorantFaceValue (m + 1) m (sieveLogTuple R (assignmentPrimeTuple p r)) := by
  obtain ⟨C, hC, hmean⟩ := exists_majorantSliceSieveSum_upper
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall α _ _ p hp hinj hnot j r hcost
  let t := sieveLogTuple R (assignmentPrimeTuple p r)
  let Mr := M * assignmentPrimeProduct p r
  let g := fun l : ℕ => pinnedLocalDenominator (m + 1) l
  have hMr : 0 < Mr := Nat.mul_pos hM
    (assignmentPrimeProduct_pos (fun q => (hp q).pos) r)
  have hsmallMr (l : ℕ) (hl : l.Prime) (hlk : l ≤ 2 * (m + 1) ^ 2) : l ∣ Mr :=
    dvd_mul_of_dvd_left (hsmall l hl hlk) _
  have hg : actualSieveDenominator true (m + 1) = g := by
    funext l
    simp only [actualSieveDenominator, if_true, g, Nat.cast_add, Nat.cast_one]
  have hS := hmean (by omega : 2 ≤ m + 1) hlog hMr hR hsmallMr hcost true m t
  rw [hg] at hS
  have hchain := actualSieveDenominator_chain (by omega : 2 ≤ m + 1)
    (by omega : 1 ≤ m + 1) hsmallMr true
  rw [hg] at hchain
  have hgp (l : ℕ) (hl : l.Prime) (hlMr : ¬l ∣ Mr) := hchain 0 (by omega) l hl hlMr
  simp only [Nat.cast_zero, add_zero] at hgp
  have hK := sieveMainConstant_pos (k := m + 1) (by omega) hMr
    (fun l hl hlk => hsmallMr l hl (by omega)) g
    (fun l hl hlMr => (hgp l hl hlMr).1) (fun l hl hlMr => (hgp l hl hlMr).2.1)
    (fun l hl hlMr => (hgp l hl hlMr).2.2)
  have hrough (q : α) : 2 * (m + 1) ^ 2 < p q := by
    by_contra hh
    exact hnot q (hsmall (p q) (hp q) (by omega))
  have hnorm : (pinnedBaseFactor p r * pinnedBaseEulerProduct p r) *
      sieveMainConstant Mr g = pinnedGlobalNormalization m M p :=
    pinnedHarmonicNormalization_eq_global hm hM hsmall hp hinj hnot r
  have hJ : pinnedMajorantValue m R p j r ≤
      pinnedBaseFactor p r * majorantSliceSieveSum (m + 1) Mr R m g t :=
    pinnedMajorantValue_le_full_sum hm hlog hR hsmall hp hinj hnot j r
  exact pinned_majorant_scale_bound (pinnedBaseFactor_nonneg (fun q => (hp q).one_le) r)
    hK.le (Real.log_natCast_nonneg R) (majorantFaceValue_nonneg _ _ _)
    (pinnedBaseEulerProduct_ge_half (seven_le_of_profile_log hlog) hinj hrough r) hnorm hJ hS

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinned_majorant_scale_bound
#print axioms Erdos4b.FGKMT.exists_pinnedMajorantValue_upper
