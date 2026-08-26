import ErdosProblems.Erdos394.MixedRatio

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Counting label pairs on one exact rational line
-/

open Nat Finset

namespace Erdos394

/-- Nonzero label pairs lying on the exact line of slope `(s,t)`. -/
def compatibleRatioLabels (K s t : ℕ) : Finset (ℕ × ℕ) :=
  (nonzeroLabelPairs K).filter (fun ab ↦ ab.1 * t = ab.2 * s)

/-- For a nonzero slope vector below `K`, at most `K-1` label pairs lie on its
exact rational line. -/
theorem card_compatibleRatioLabels_le {K s t : ℕ} (hK : 0 < K)
    (hst : s ≠ 0 ∨ t ≠ 0) :
    (compatibleRatioLabels K s t).card ≤ K - 1 := by
  classical
  by_cases hs : s = 0
  · have ht : t ≠ 0 := hst.resolve_left (fun hsne ↦ hsne hs)
    let target := Icc 1 (K - 1)
    have hmap : Set.MapsTo (fun ab : ℕ × ℕ ↦ ab.2)
        (↑(compatibleRatioLabels K s t)) (↑target) := by
      intro ab habmem
      have hmem := Finset.mem_filter.mp habmem
      have hab := hmem.1
      have heq := hmem.2
      simp only [nonzeroLabelPairs, Finset.mem_erase, ne_eq,
        Finset.mem_product, Finset.mem_range] at hab
      have ha0 : ab.1 = 0 := by
        subst s
        simp only [mul_zero] at heq
        exact (Nat.mul_eq_zero.mp heq).resolve_right ht
      have hb0 : ab.2 ≠ 0 := by
        intro hb0
        apply hab.1
        ext <;> simp_all
      have hbK : ab.2 < K := hab.2.2
      apply Finset.mem_Icc.mpr
      change 1 ≤ ab.2 ∧ ab.2 ≤ K - 1
      exact ⟨Nat.one_le_iff_ne_zero.mpr hb0, Nat.le_pred_of_lt hbK⟩
    have hinj : Set.InjOn (fun ab : ℕ × ℕ ↦ ab.2)
        (↑(compatibleRatioLabels K s t)) := by
      intro a ha b hb heq
      have harel := (Finset.mem_filter.mp ha).2
      have hbrel := (Finset.mem_filter.mp hb).2
      subst s
      simp only [mul_zero] at harel hbrel
      have ha0 : a.1 = 0 := (Nat.mul_eq_zero.mp harel).resolve_right ht
      have hb0 : b.1 = 0 := (Nat.mul_eq_zero.mp hbrel).resolve_right ht
      apply Prod.ext
      · rw [ha0, hb0]
      · exact heq
    calc
      (compatibleRatioLabels K s t).card ≤ target.card :=
        Finset.card_le_card_of_injOn _ hmap hinj
      _ = K - 1 := by simp [target, Nat.card_Icc]
  · let target := Icc 1 (K - 1)
    have hmap : Set.MapsTo (fun ab : ℕ × ℕ ↦ ab.1)
        (↑(compatibleRatioLabels K s t)) (↑target) := by
      intro ab habmem
      have hmem := Finset.mem_filter.mp habmem
      have hab := hmem.1
      have heq := hmem.2
      simp only [nonzeroLabelPairs, Finset.mem_erase, ne_eq,
        Finset.mem_product, Finset.mem_range] at hab
      have ha0 : ab.1 ≠ 0 := by
        intro ha0
        have hb0 : ab.2 = 0 := by
          rw [ha0, zero_mul] at heq
          exact (Nat.mul_eq_zero.mp heq.symm).resolve_right hs
        apply hab.1
        ext <;> simp_all
      have haK : ab.1 < K := hab.2.1
      apply Finset.mem_Icc.mpr
      change 1 ≤ ab.1 ∧ ab.1 ≤ K - 1
      exact ⟨Nat.one_le_iff_ne_zero.mpr ha0, Nat.le_pred_of_lt haK⟩
    have hinj : Set.InjOn (fun ab : ℕ × ℕ ↦ ab.1)
        (↑(compatibleRatioLabels K s t)) := by
      intro a ha b hb heq
      have harel := (Finset.mem_filter.mp ha).2
      have hbrel := (Finset.mem_filter.mp hb).2
      have hfirst : a.1 = b.1 := heq
      apply Prod.ext
      · exact hfirst
      · have hsecond : a.2 * s = b.2 * s := by
          rw [← harel, ← hbrel, hfirst]
        exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hs) hsecond
    calc
      (compatibleRatioLabels K s t).card ≤ target.card :=
        Finset.card_le_card_of_injOn _ hmap hinj
      _ = K - 1 := by simp [target, Nat.card_Icc]

/-- If `p>K²`, congruence to a small-label slope is already exact over the
integers. -/
theorem compatible_label_mod_prime_iff_exact {p K s t A B : ℕ}
    (hK : 0 < K) (hs : s < K) (ht : t < K)
    (hA : A < K) (hB : B < K) (hp : K * K < p) :
    p ∣ Nat.dist (A * t) (B * s) ↔ A * t = B * s := by
  constructor
  · intro hdiv
    have hdist : Nat.dist (A * t) (B * s) < p := by
      have hAt : A * t < K * K := by
        by_cases ht0 : t = 0
        · subst t
          simp [hK]
        · exact (Nat.mul_lt_mul_of_pos_right hA (Nat.pos_of_ne_zero ht0)).trans
            (Nat.mul_lt_mul_of_pos_left ht (by omega))
      have hBs : B * s < K * K := by
        by_cases hs0 : s = 0
        · subst s
          simp [hK]
        · exact (Nat.mul_lt_mul_of_pos_right hB (Nat.pos_of_ne_zero hs0)).trans
            (Nat.mul_lt_mul_of_pos_left hs (by omega))
      have hle : Nat.dist (A * t) (B * s) < K * K := by
        rw [Nat.dist_eq_max_sub_min]
        omega
      exact hle.trans hp
    have hz : Nat.dist (A * t) (B * s) = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdiv hdist
    rw [Nat.dist_eq_max_sub_min] at hz
    omega
  · intro heq
    rw [heq, Nat.dist_self]
    exact dvd_zero p

end Erdos394
