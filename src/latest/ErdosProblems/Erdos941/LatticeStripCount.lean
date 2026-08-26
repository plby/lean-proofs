import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # An elementary finite lattice-point bound in two strips -/

namespace Erdos941

theorem int_finset_card_le_length (s : Finset ℤ) {l u : ℝ} (hlu : l ≤ u)
    (hs : ∀ x ∈ s, l ≤ (x : ℝ) ∧ (x : ℝ) ≤ u) :
    (s.card : ℝ) ≤ u - l + 1 := by
  classical
  by_cases hempty : s = ∅
  · simp only [hempty, Finset.card_empty, Nat.cast_zero]
    linarith
  · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let a := s.min' hne
    let b := s.max' hne
    have ha : a ∈ s := s.min'_mem hne
    have hb : b ∈ s := s.max'_mem hne
    have hab : a ≤ b := s.min'_le _ hb
    have hsub : s ⊆ Finset.Icc a b := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨s.min'_le _ hx, s.le_max' _ hx⟩
    have hcard := Finset.card_le_card hsub
    rw [Int.card_Icc] at hcard
    have hcast : ((b + 1 - a).toNat : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      push_cast
      rfl
    have hbound : (s.card : ℝ) ≤ (b : ℝ) + 1 - (a : ℝ) := by
      rw [← hcast]
      exact_mod_cast hcard
    have hal := (hs a ha).1
    have hbu := (hs b hb).2
    linarith

theorem integer_strip_count (s : Finset (ℤ × ℤ)) {U V c : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hs : ∀ z ∈ s, |(z.2 : ℝ)| ≤ V ∧ |(z.1 : ℝ) + c * (z.2 : ℝ)| ≤ U) :
    (s.card : ℝ) ≤ (2 * U + 1) * (2 * V + 1) := by
  classical
  have hy : ((s.image Prod.snd).card : ℝ) ≤ 2 * V + 1 := by
    have hh := int_finset_card_le_length (s.image Prod.snd) (l := -V) (u := V)
      (by linarith) (by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact abs_le.mp (hs z hz).1)
    linarith
  have hf (y : ℤ) : ((s.filter fun z => z.2 = y).card : ℝ) ≤ 2 * U + 1 := by
    let t := s.filter fun z => z.2 = y
    have hinj : Set.InjOn Prod.fst (t : Set (ℤ × ℤ)) := by
      intro z hz w hw hzw
      have hz' := (Finset.mem_filter.mp hz).2
      have hw' := (Finset.mem_filter.mp hw).2
      exact Prod.ext hzw (hz'.trans hw'.symm)
    have ht : (t.image Prod.fst).card = t.card := Finset.card_image_iff.mpr hinj
    have hh := int_finset_card_le_length (t.image Prod.fst)
      (l := -U - c * y) (u := U - c * y) (by linarith) (by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have hz' := Finset.mem_filter.mp hz
        have hzx := abs_le.mp (hs z hz'.1).2
        rw [hz'.2] at hzx
        constructor <;> linarith)
    rw [ht] at hh
    dsimp [t] at hh
    linarith
  have hcard : (s.card : ℝ) =
      ∑ y ∈ s.image Prod.snd, ((s.filter fun z => z.2 = y).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image Prod.snd s
  rw [hcard]
  calc
    _ ≤ ∑ _y ∈ s.image Prod.snd, (2 * U + 1) :=
      Finset.sum_le_sum fun y _ => hf y
    _ = ((s.image Prod.snd).card : ℝ) * (2 * U + 1) := by simp; ring
    _ ≤ (2 * U + 1) * (2 * V + 1) := by
      nlinarith

end Erdos941
