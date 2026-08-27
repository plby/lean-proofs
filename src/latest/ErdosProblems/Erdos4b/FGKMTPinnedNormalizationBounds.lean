/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedNormalization

/-! # Dimension-independent bounds for the exact finite pinned normalization -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem pinnedLocalProduct_bounds {k : ℕ} (hk : 8 ≤ k) {p : α → ℕ}
    (hinj : Function.Injective p) (hrough : ∀ q, 2 * k ^ 2 < p q) :
    (1 / 2 : ℝ) ≤ (∏ q, pinnedLocalFactor k (p q)) ∧
      (∏ q, pinnedLocalFactor k (p q)) ≤ 1 := by
  classical
  let u := fun q => ((k : ℝ) - 1) * pinnedMovedWeight k (p q)
  have hku : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
  have hu0 (q : α) : 0 ≤ u q := mul_nonneg (by linarith)
    (pinnedMovedWeight_nonneg hku (by exact_mod_cast hrough q))
  have heq (q : α) : pinnedLocalFactor k (p q) = 1 - u q := by
    unfold pinnedLocalFactor u pinnedMovedWeight
    ring
  have hu1 (q : α) : u q ≤ 1 := by
    have h := pinnedLocalFactor_pos (k := (k : ℝ)) (p := (p q : ℝ))
      hku (by exact_mod_cast hrough q)
    rw [heq] at h
    linarith
  have hmass : (∑ q, u q) ≤ 1 / 2 := by
    have h := pinnedMovedPrimeMass_le (by omega : 2 ≤ k) hinj hrough
    have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk
    exact h.trans ((div_le_iff₀ (by linarith : (0 : ℝ) < k)).mpr (by linarith))
  constructor
  · calc
      _ ≤ 1 - ∑ q, u q := by linarith
      _ ≤ ∏ q, (1 - u q) := Erdos4b.one_sub_sum_le_prod_one_sub Finset.univ u
        (fun q _hq => hu0 q) (fun q _hq => hu1 q)
      _ = _ := Finset.prod_congr rfl (fun q _hq => (heq q).symm)
  · apply Finset.prod_le_one
    · intro q _hq
      exact (pinnedLocalFactor_pos hku (by exact_mod_cast hrough q)).le
    · intro q _hq
      exact (pinnedLocalFactor_lt_one hku (by exact_mod_cast hrough q)).le

theorem pinnedBaseEulerProduct_ge_half {m : ℕ} (hm : 7 ≤ m) {p : α → ℕ}
    (hinj : Function.Injective p) (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q)
    (r : α → Option (Fin m)) : (1 / 2 : ℝ) ≤ pinnedBaseEulerProduct p r := by
  have hprod := (pinnedLocalProduct_bounds (by omega : 8 ≤ m + 1) hinj hrough).1
  simp only [Nat.cast_add, Nat.cast_one] at hprod
  apply hprod.trans
  unfold pinnedBaseEulerProduct
  apply Finset.prod_le_prod
  · intro q _hq
    exact (pinnedLocalFactor_pos (by exact_mod_cast (by omega : 2 ≤ m + 1))
      (by exact_mod_cast hrough q)).le
  · intro q _hq
    split_ifs
    · exact le_rfl
    · exact (pinnedLocalFactor_lt_one (k := (m : ℝ) + 1) (p := (p q : ℝ))
        (by exact_mod_cast (by omega : 2 ≤ m + 1))
        (by exact_mod_cast hrough q)).le

theorem pinnedGlobalNormalization_bounds {m M : ℕ} (hm : 7 ≤ m) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hnot : ∀ q, ¬p q ∣ M) :
    ((M.totient : ℝ) / M) / 2 ≤ pinnedGlobalNormalization m M p ∧
      pinnedGlobalNormalization m M p ≤ Real.exp 12 * ((M.totient : ℝ) / M) := by
  have hrough (q : α) : 2 * (m + 1) ^ 2 < p q := by
    by_contra hh
    exact hnot q (hsmall (p q) (hp q) (by omega))
  have hprod := pinnedLocalProduct_bounds (by omega : 8 ≤ m + 1) hinj hrough
  simp only [Nat.cast_add, Nat.cast_one] at hprod
  have hchain := actualSieveDenominator_chain (by omega : 2 ≤ m + 1)
    (by omega : 1 ≤ m + 1) hsmall true
  have hg (l : ℕ) (hl : l.Prime) (hlM : ¬l ∣ M) := hchain 0 (by omega) l hl hlM
  simp only [actualSieveDenominator, if_true, Nat.cast_zero, add_zero,
    Nat.cast_add, Nat.cast_one] at hg
  have hconst := sieveMainConstant_bounds (k := m + 1) (by omega) hM
    (fun l hl hlk => hsmall l hl (by omega))
    (fun l => pinnedLocalDenominator (m + 1) l)
    (fun l hl hlM => (hg l hl hlM).1) (fun l hl hlM => by
      simpa only [Nat.cast_add, Nat.cast_one] using (hg l hl hlM).2.1)
    (fun l hl hlM => (hg l hl hlM).2.2)
  have hb : (0 : ℝ) ≤ (M.totient : ℝ) / M := by positivity
  have hK := hb.trans hconst.1
  have hP : 0 ≤ ∏ q, pinnedLocalFactor (m + 1) (p q) :=
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hprod.1
  constructor
  · have h := mul_le_mul hprod.1 hconst.1 hb hP
    simpa only [pinnedGlobalNormalization, one_div, div_eq_mul_inv, one_mul, mul_comm] using h
  · have h := mul_le_mul hprod.2 hconst.2 hK zero_le_one
    simpa only [pinnedGlobalNormalization, one_mul] using h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedBaseEulerProduct_ge_half
#print axioms Erdos4b.FGKMT.pinnedGlobalNormalization_bounds
