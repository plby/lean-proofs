/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedReindex
import ErdosProblems.Erdos4b.FGKMTTensorDenominators

/-!
# Exact cancellation of the remaining tuple from the pinned normalization

The global constant retains the finite Euler product. Its independence
of the remaining divisor tuple is exact, before estimating any tail.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem pinnedLocalFactor_mul_harmonicMultiplier {k p : ℝ}
    (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    pinnedLocalFactor k p * (1 + 1 / pinnedLocalDenominator k p) = p / (p - 1) := by
  have ha := pinnedLocalFactor_pos hk hp
  have hb := rough_real_bounds hk hp
  have hpk : p - k ≠ 0 := by nlinarith
  have h := pinnedLocalFactor_eq (by linarith : p ≠ 1) (by nlinarith : p ≠ k)
  unfold pinnedLocalDenominator
  field_simp [ha.ne', hpk] at h ⊢
  nlinarith

theorem modulusEulerMultiplier_assignment {ι : Type*} {M : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M)
    (g : ℕ → ℝ) (r : α → Option ι) :
    modulusEulerMultiplier M (assignmentPrimeProduct p r) g =
      assignmentScalarWeight (fun q => 1 + 1 / g (p q)) r := by
  unfold modulusEulerMultiplier
  rw [← assignmentScalarWeight_eq_primeFactors hp hinj
    (fun l => if l ∣ M then 1 else 1 + 1 / g l)]
  simp only [hM, if_false]

theorem pinnedBaseEuler_mul_eq_multiplier {m M : ℕ} (hm : 1 ≤ m) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M)
    (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q) (r : α → Option (Fin m)) :
    pinnedBaseFactor p r * pinnedBaseEulerProduct p r =
      (∏ q, pinnedLocalFactor (m + 1) (p q)) *
        modulusEulerMultiplier M (assignmentPrimeProduct p r)
          (fun l => pinnedLocalDenominator (m + 1) l) := by
  rw [modulusEulerMultiplier_assignment hp hinj hM]
  unfold pinnedBaseFactor pinnedBaseEulerProduct assignmentScalarWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hr : r q = none
  · simp [localPinnedBaseWeight, hr]
  · simp only [localPinnedBaseWeight, if_neg hr, mul_one]
    exact (pinnedLocalFactor_mul_harmonicMultiplier
      (by exact_mod_cast (by omega : 2 ≤ m + 1)) (by exact_mod_cast hrough q)).symm

def pinnedHarmonicNormalization (m M : ℕ) (p : α → ℕ) (r : α → Option (Fin m)) : ℝ :=
  (pinnedBaseFactor p r * pinnedBaseEulerProduct p r) *
    sieveMainConstant (M * assignmentPrimeProduct p r)
      (fun l => pinnedLocalDenominator (m + 1) l)

def pinnedGlobalNormalization (m M : ℕ) (p : α → ℕ) : ℝ :=
  (∏ q, pinnedLocalFactor (m + 1) (p q)) *
    sieveMainConstant M (fun l => pinnedLocalDenominator (m + 1) l)

theorem pinnedHarmonicNormalization_eq_global {m M : ℕ} (hm : 1 ≤ m) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hnot : ∀ q, ¬p q ∣ M)
    (r : α → Option (Fin m)) :
    pinnedHarmonicNormalization m M p r = pinnedGlobalNormalization m M p := by
  have hrough (q : α) : 2 * (m + 1) ^ 2 < p q := by
    by_contra hh
    exact hnot q (hsmall (p q) (hp q) (by omega))
  have hchain := actualSieveDenominator_chain (by omega : 2 ≤ m + 1)
    (by omega : 1 ≤ m + 1) hsmall true
  have hg (l : ℕ) (hl : l.Prime) (hlM : ¬l ∣ M) :
      (l : ℝ) / 2 ≤ pinnedLocalDenominator (m + 1) l ∧
        |pinnedLocalDenominator (m + 1) l - l| ≤ 2 * (m + 1 : ℕ) := by
    simpa only [actualSieveDenominator, if_true, Nat.cast_zero, add_zero,
      Nat.cast_add, Nat.cast_one] using (hchain 0 (by omega) l hl hlM).imp_right And.left
  have hconst := sieveMainConstant_modulus_mul (k := m + 1) (by omega) hM
    (assignmentPrimeProduct_pos (fun q => (hp q).pos) r)
    (fun l hl hlk => hsmall l hl (by omega))
    (fun l => pinnedLocalDenominator (m + 1) l)
    (fun l hl hlM => (hg l hl hlM).1) (fun l hl hlM => (hg l hl hlM).2)
  unfold pinnedHarmonicNormalization pinnedGlobalNormalization
  rw [pinnedBaseEuler_mul_eq_multiplier hm hp hinj hnot hrough, mul_assoc, ← hconst]

theorem pinnedBaseEulerProduct_nonneg {m : ℕ} (hm : 1 ≤ m) {p : α → ℕ}
    (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q) (r : α → Option (Fin m)) :
    0 ≤ pinnedBaseEulerProduct p r := by
  apply Finset.prod_nonneg
  intro q _hq
  split_ifs
  · exact (pinnedLocalFactor_pos (by exact_mod_cast (by omega : 2 ≤ m + 1))
      (by exact_mod_cast hrough q)).le
  · exact zero_le_one

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedBaseEuler_mul_eq_multiplier
#print axioms Erdos4b.FGKMT.pinnedHarmonicNormalization_eq_global
