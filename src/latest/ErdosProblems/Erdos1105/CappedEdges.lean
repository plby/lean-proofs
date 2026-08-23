import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open Finset

/-- The sharp edge bound for a `d`-degenerate graph. -/
def cappedEdgeBound (n d : ℕ) : ℕ := ∑ i ∈ range n, min i d

@[simp] lemma cappedEdgeBound_zero (d : ℕ) : cappedEdgeBound 0 d = 0 := by
  simp [cappedEdgeBound]

lemma cappedEdgeBound_succ (n d : ℕ) :
    cappedEdgeBound (n + 1) d = cappedEdgeBound n d + min n d := by
  simp [cappedEdgeBound, sum_range_succ]

lemma cappedEdgeBound_eq_choose {n d : ℕ} (hnd : n ≤ d) :
    cappedEdgeBound n d = n.choose 2 := by
  calc
    _ = ∑ i ∈ range n, i := sum_congr rfl fun i hi ↦ min_eq_left (by
      have := mem_range.mp hi
      omega)
    _ = _ := by rw [sum_range_id, Nat.choose_two_right]

lemma cappedEdgeBound_eq_linear {n d : ℕ} (hdn : d ≤ n) :
    cappedEdgeBound n d = d.choose 2 + d * (n - d) := by
  have h (t : ℕ) : cappedEdgeBound (d + t) d = d.choose 2 + d * t := by
    induction t with
    | zero => simpa using (cappedEdgeBound_eq_choose (n := d) le_rfl)
    | succ t ih =>
      rw [show d + (t + 1) = d + t + 1 by omega, cappedEdgeBound_succ, ih,
        min_eq_right (by omega : d ≤ d + t)]
      ring
  simpa only [Nat.add_sub_of_le hdn] using h (n - d)

lemma cappedEdgeBound_merge {a b d : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    cappedEdgeBound a d + cappedEdgeBound b d + 1 ≤ cappedEdgeBound (a + b) d := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb₀ : b = 0
    · subst b
      rw [cappedEdgeBound_succ, cappedEdgeBound_zero]
      simp only [Nat.zero_min, add_zero, zero_add]
      rw [cappedEdgeBound_succ]
      have hmin : 1 ≤ min a d := le_min ha hd
      omega
    · have hind := ih (by omega)
      rw [cappedEdgeBound_succ, show a + (b + 1) = a + b + 1 by omega,
        cappedEdgeBound_succ]
      have hm : min b d ≤ min (a + b) d := min_le_min_right d (by omega)
      omega

lemma cappedEdgeBound_sum {I : Type*} (S : Finset I) (n : I → ℕ) {d : ℕ} (hd : 0 < d)
    (hpos : ∀ i ∈ S, 0 < n i) :
    (∑ i ∈ S, cappedEdgeBound (n i) d) + S.card ≤ cappedEdgeBound (∑ i ∈ S, n i) d + 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hni := hpos i (mem_insert_self _ _)
    have hrest : ∀ j ∈ S, 0 < n j := fun j hj ↦ hpos j (mem_insert_of_mem hj)
    by_cases hS : S = ∅
    · subst S
      simp
    · have hsum : 0 < ∑ j ∈ S, n j := by
        obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.mpr hS
        exact (hrest j hj).trans_le (single_le_sum (fun _ _ ↦ Nat.zero_le _) hj)
      have hm := cappedEdgeBound_merge hni hsum hd
      have hind := ih hrest
      rw [sum_insert hi, card_insert_of_notMem hi, sum_insert hi]
      omega

lemma cappedEdgeBound_mono {n m : ℕ} (hnm : n ≤ m) (d : ℕ) :
    cappedEdgeBound n d ≤ cappedEdgeBound m d := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono hnm) (by intros; omega)

lemma cappedEdgeBound_le_mul_pred {m d a : ℕ} (hm : 1 ≤ m)
    (hcap : min (m - 1) d ≤ a) : cappedEdgeBound m d ≤ a * (m - 1) := by
  have heq : m = m - 1 + 1 := by omega
  rw [heq, cappedEdgeBound, sum_range_succ']
  simp only [Nat.zero_min, add_zero, Nat.add_sub_cancel]
  calc
    _ ≤ ∑ _i ∈ range (m - 1), a := sum_le_sum fun i hi ↦
      (min_le_min_right d (by have := mem_range.mp hi; omega)).trans hcap
    _ = _ := by simp [Nat.mul_comm]

lemma cappedEdgeBound_add_lower (m t d a : ℕ) (ha : a ≤ min m d) :
    cappedEdgeBound m d + a * t ≤ cappedEdgeBound (m + t) d := by
  simp only [cappedEdgeBound, sum_range_add]
  change cappedEdgeBound m d + a * t ≤ cappedEdgeBound m d + ∑ i ∈ range t, min (m + i) d
  apply Nat.add_le_add_left
  calc
    a * t = ∑ _i ∈ range t, a := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum fun i _ ↦ ha.trans (min_le_min_right d (by omega))

/-- A linear function plus the capped edge bound attains its maximum at
an endpoint. This discrete convexity statement avoids division. -/
lemma cappedEdgeBound_affine_max {m M d a : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    cappedEdgeBound m d + a * (M - m) ≤ max (a * (M - 1)) (cappedEdgeBound M d) := by
  by_cases hcap : min (m - 1) d ≤ a
  · apply le_trans ?_ (le_max_left _ _)
    have h := cappedEdgeBound_le_mul_pred hm hcap
    have heq : m - 1 + (M - m) = M - 1 := by omega
    calc
      _ ≤ a * (m - 1) + a * (M - m) := Nat.add_le_add_right h _
      _ = _ := by rw [← Nat.mul_add, heq]
  · apply le_trans ?_ (le_max_right _ _)
    have ha : a ≤ min m d := by
      have hmono : min (m - 1) d ≤ min m d := min_le_min_right d (by omega)
      omega
    simpa only [Nat.add_sub_of_le hmM] using cappedEdgeBound_add_lower m (M - m) d a ha

end Erdos1105

#print axioms Erdos1105.cappedEdgeBound_sum
