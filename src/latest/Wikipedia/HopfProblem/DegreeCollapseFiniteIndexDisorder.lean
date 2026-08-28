import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# A finite natural-valued disorder decreased by adjacent inverted exchanges

Weight each point's index by the number of values strictly above it.
For consecutive distinct values, exchanging an inverted pair lowers this
sum strictly. The proof uses an exact rank difference and the two-term
transposition identity, with no asymptotic or computational search.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {X : Type*} [Fintype X]

open Classical in
def upperValueRank (h : X → ℝ) (x : X) : ℕ :=
  (Finset.univ.filter (fun y => h x < h y)).card

def finiteIndexDisorder (h : X → ℝ) (w : X → ℕ) : ℕ :=
  ∑ x, w x * upperValueRank h x

theorem upperValueRank_comp_equiv {Y : Type*} [Fintype Y] (h : Y → ℝ) (e : X ≃ Y) (x : X) :
    upperValueRank (h ∘ e) x = upperValueRank h (e x) := by
  classical
  unfold upperValueRank
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem finiteIndexDisorder_comp_equiv {Y : Type*} [Fintype Y]
    (h : Y → ℝ) (w : Y → ℕ) (e : X ≃ Y) :
    finiteIndexDisorder (h ∘ e) (w ∘ e) = finiteIndexDisorder h w := by
  classical
  unfold finiteIndexDisorder
  calc
    _ = ∑ x, w (e x) * upperValueRank h (e x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [upperValueRank_comp_equiv]
      rfl
    _ = _ := e.sum_comp (fun y => w y * upperValueRank h y)

theorem upperValueRank_consecutive {h : X → ℝ} (hi : Injective h) {p q : X}
    (hpq : h p < h q) (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) :
    upperValueRank h p = upperValueRank h q + 1 := by
  classical
  have hset : Finset.univ.filter (fun x => h p < h x) =
      insert q (Finset.univ.filter (fun x => h q < h x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hx
      by_cases hxq : x = q
      · exact Or.inl hxq
      · apply Or.inr
        by_contra hnot
        have hlt : h x < h q := lt_of_le_of_ne (le_of_not_gt hnot) (fun heq => hxq (hi heq))
        exact hconsecutive x ⟨hx, hlt⟩
    · rintro (rfl | hx)
      · exact hpq
      · exact hpq.trans hx
  unfold upperValueRank
  rw [hset, Finset.card_insert_of_notMem (by simp)]

open Classical in
theorem sum_erase_two_nat (v : X → ℕ) {p q : X} (hpq : p ≠ q) :
    ∑ x, v x = (∑ x ∈ (Finset.univ.erase p).erase q, v x) + v p + v q := by
  classical
  have hp := Finset.sum_erase_add (s := Finset.univ) v (Finset.mem_univ p)
  have hq := Finset.sum_erase_add (s := Finset.univ.erase p) v
    (by simp [Ne.symm hpq] : q ∈ Finset.univ.erase p)
  omega

open Classical in
theorem weighted_sum_swap_identity (w v : X → ℕ) {p q : X} (hpq : p ≠ q) :
    (∑ x, w x * v (Equiv.swap p q x)) + w p * v p + w q * v q =
      (∑ x, w x * v x) + w p * v q + w q * v p := by
  classical
  have hnew := sum_erase_two_nat (fun x => w x * v (Equiv.swap p q x)) hpq
  have hold := sum_erase_two_nat (fun x => w x * v x) hpq
  have hrest : (∑ x ∈ (Finset.univ.erase p).erase q, w x * v (Equiv.swap p q x)) =
      ∑ x ∈ (Finset.univ.erase p).erase q, w x * v x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxq := (Finset.mem_erase.mp hx).1
    have hxp := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq]
  rw [hrest] at hnew
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hnew
  omega

open Classical in
theorem finiteIndexDisorder_swap_lt {h : X → ℝ} (hi : Injective h) (w : X → ℕ)
    {p q : X} (hpq : h p < h q) (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q))
    (hw : w q < w p) : finiteIndexDisorder (h ∘ Equiv.swap p q) w < finiteIndexDisorder h w := by
  classical
  have hne : p ≠ q := fun heq => (ne_of_lt hpq) (congrArg h heq)
  have hrank := upperValueRank_consecutive hi hpq hconsecutive
  have hid := weighted_sum_swap_identity w (upperValueRank h) hne
  have hnew : finiteIndexDisorder (h ∘ Equiv.swap p q) w =
      ∑ x, w x * upperValueRank h (Equiv.swap p q x) := by
    unfold finiteIndexDisorder
    apply Finset.sum_congr rfl
    intro x _
    rw [upperValueRank_comp_equiv]
  rw [hrank] at hid
  simp only [Nat.mul_add, Nat.mul_one] at hid
  change _ < ∑ x, w x * upperValueRank h x
  rw [hnew]
  omega

theorem exists_adjacent_index_inversion {h : X → ℝ} (hi : Injective h) (w : X → ℕ)
    (hnot : ¬∀ x y, h x < h y → w x ≤ w y) :
    ∃ p q, h p < h q ∧ (∀ x, ¬(h p < h x ∧ h x < h q)) ∧ w q < w p := by
  classical
  let _ : LinearOrder X := LinearOrder.lift' h hi
  let _ : LocallyFiniteOrder X := Fintype.toLocallyFiniteOrder
  have hnotmono : ¬Monotone w := by
    intro hm
    apply hnot
    intro x y hxy
    exact hm (show x ≤ y from hxy.le)
  have hnotadj : ¬∀ x y : X, x ⋖ y → w x ≤ w y := by
    intro hadj
    exact hnotmono ((monotone_iff_forall_covBy w).mpr hadj)
  simp only [not_forall, _root_.not_imp, not_le] at hnotadj
  obtain ⟨p, q, hcover, hweights⟩ := hnotadj
  exact ⟨p, q, hcover.lt, fun x hx => hcover.2 hx.1 hx.2, hweights⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
