/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# The nonproper-progression bound in the CFP argument

This file proves the finite-box estimate used in Lemma 2.19 of
Conlon--Fox--Pham.  If a GAP presentation is not proper, two distinct points
of its coefficient box have the same image.  Adding either of these points
to the original coefficient box gives two translates inside the doubled
coefficient box.  In a coordinate on which the colliding points differ, one
translate always gives a strictly smaller representative of the same fiber.
Consequently a minimal representative of every fiber avoids an entire
translate of the original box.  Counting the remaining points gives

`|(2P).carrier| + vol(P) <= product_i (2 * width_i - 1)`.

The final theorem records the usual coarser strict estimate
`|(2P).carrier| < (2^rank - 1) * vol(P)`.
-/

namespace Erdos186

open scoped BigOperators

variable {d r : ℕ}

/-! ## A finite descent counting lemma -/

/-- If every point of `t` has a strictly smaller point in the same `f`-fiber,
then a minimum-measure representative of every fiber of `s` lies in `s \ t`.
Thus the image of `s` has at most `|s| - |t|` elements. -/
theorem card_image_add_card_le_of_fiber_descent
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s t : Finset α) (f : α → β) (measure : α → ℕ)
    (hts : t ⊆ s)
    (hdesc : ∀ x ∈ t, ∃ y ∈ s, f y = f x ∧ measure y < measure x) :
    (s.image f).card + t.card ≤ s.card := by
  classical
  have hminimal (z : β) (hz : z ∈ s.image f) :
      ∃ x ∈ s, f x = z ∧
        ∀ y ∈ s, f y = z → measure x ≤ measure y := by
    let fiber : Finset α := s.filter fun x ↦ f x = z
    have hfiber : fiber.Nonempty := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨x, by simp [fiber, hx]⟩
    let values : Finset ℕ := fiber.image measure
    have hvalues : values.Nonempty := hfiber.image _
    let m : ℕ := values.min' hvalues
    have hm : m ∈ values := Finset.min'_mem values hvalues
    obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm
    have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
    have hfx : f x = z := (Finset.mem_filter.mp hx).2
    refine ⟨x, hxs, hfx, ?_⟩
    intro y hy hfy
    have hymem : measure y ∈ values := by
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hfy⟩, rfl⟩
    have hmle : m ≤ measure y := Finset.min'_le values _ hymem
    simpa [hxm] using hmle
  have himage : s.image f ⊆ (s \ t).image f := by
    intro z hz
    obtain ⟨x, hxs, hfx, hmin⟩ := hminimal z hz
    have hxt : x ∉ t := by
      intro hxin
      obtain ⟨y, hys, hfy, hylt⟩ := hdesc x hxin
      exact (not_lt_of_ge (hmin y hys (hfy.trans hfx))) hylt
    exact Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hxs, hxt⟩, hfx⟩
  have hcard : (s.image f).card ≤ (s \ t).card :=
    (Finset.card_le_card himage).trans Finset.card_image_le
  calc
    (s.image f).card + t.card ≤ (s \ t).card + t.card :=
      Nat.add_le_add_right hcard _
    _ = s.card := Finset.card_sdiff_add_card_eq_card hts

/-! ## Translates of the coefficient box -/

namespace GAP

/-- Coordinatewise addition of two coordinates of `P`, regarded as a point
of the doubled coefficient box. -/
def addCoordToDouble (P : Erdos186.GAP d r) (a n : P.Coord) :
    (P.dilate 2).Coord :=
  fun i ↦ ⟨(n i : ℕ) + (a i : ℕ), by
    have hn := (n i).isLt
    have ha := (a i).isLt
    have hw := P.width_pos i
    simp only [Erdos186.GAP.dilate_widths]
    omega⟩

/-- Translation by a fixed coefficient vector embeds the original
coefficient box into the doubled box. -/
theorem addCoordToDouble_injective (P : Erdos186.GAP d r) (a : P.Coord) :
    Function.Injective (P.addCoordToDouble a) := by
  intro n m hnm
  funext i
  apply Fin.ext
  have hi : (n i : ℕ) + (a i : ℕ) = (m i : ℕ) + (a i : ℕ) := by
    simpa only [addCoordToDouble] using congrArg Fin.val (congrFun hnm i)
  omega

/-- Translating by two colliding coefficient vectors gives the same point in
the doubled GAP. -/
theorem coordPoint_addCoordToDouble_eq_of_coordPoint_eq
    (P : Erdos186.GAP d r) {a b : P.Coord}
    (hab : P.coordPoint a = P.coordPoint b) (n : P.Coord) :
    (P.dilate 2).coordPoint (P.addCoordToDouble a n) =
      (P.dilate 2).coordPoint (P.addCoordToDouble b n) := by
  funext j
  have habj := congrFun hab j
  have hsums :
      (∑ i, (a i : ℤ) * P.steps i j) =
        ∑ i, (b i : ℤ) * P.steps i j := by
    change P.offset j + (∑ i, (a i : ℤ) * P.steps i j) =
      P.offset j + ∑ i, (b i : ℤ) * P.steps i j at habj
    exact add_left_cancel habj
  change
    (2 : ℤ) * P.offset j +
          ∑ i, (((n i : ℕ) + (a i : ℕ) : ℕ) : ℤ) * P.steps i j =
      (2 : ℤ) * P.offset j +
          ∑ i, (((n i : ℕ) + (b i : ℕ) : ℕ) : ℤ) * P.steps i j
  simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [hsums]

/-- The sharp finite-box estimate, assuming the collision is oriented to
increase coordinate `i`. -/
theorem card_dilate_two_add_volume_le_box_of_collision
    (P : Erdos186.GAP d r) {a b : P.Coord} {i : Fin r}
    (hab : P.coordPoint a = P.coordPoint b)
    (hi : (a i : ℕ) < (b i : ℕ)) :
    (P.dilate 2).carrier.card + P.volume ≤
      ∏ j, (2 * P.widths j - 1) := by
  classical
  let outer : Finset (P.dilate 2).Coord := Finset.univ
  let omitted : Finset (P.dilate 2).Coord :=
    Finset.univ.image (P.addCoordToDouble b)
  have homitted_outer : omitted ⊆ outer := by
    intro x hx
    simp [outer]
  have hdesc : ∀ x ∈ omitted, ∃ y ∈ outer,
      (P.dilate 2).coordPoint y = (P.dilate 2).coordPoint x ∧
        (y i : ℕ) < (x i : ℕ) := by
    intro x hx
    obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨P.addCoordToDouble a n, by simp [outer], ?_, ?_⟩
    · exact P.coordPoint_addCoordToDouble_eq_of_coordPoint_eq hab n
    · change (n i : ℕ) + (a i : ℕ) < (n i : ℕ) + (b i : ℕ)
      omega
  have hcount := card_image_add_card_le_of_fiber_descent
    outer omitted (P.dilate 2).coordPoint (fun n ↦ (n i : ℕ))
    homitted_outer hdesc
  have homitted_card : omitted.card = P.volume := by
    change (Finset.univ.image (P.addCoordToDouble b)).card = P.volume
    rw [Finset.card_image_of_injective _ (P.addCoordToDouble_injective b)]
    simp [Erdos186.GAP.volume]
  have houter_card : outer.card = ∏ j, (2 * P.widths j - 1) := by
    change (Finset.univ : Finset (P.dilate 2).Coord).card =
      ∏ j, (2 * P.widths j - 1)
    rw [Finset.card_univ, Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro j _hj
    rw [Fintype.card_fin]
    change 2 * (P.widths j - 1) + 1 = 2 * P.widths j - 1
    have hw := P.width_pos j
    omega
  simpa only [outer, Erdos186.GAP.carrier, homitted_card, houter_card] using hcount

/-- **CFP Lemma 2.19, sharp form.**  A nonproper GAP misses at least one
translate of its original coefficient box inside the doubled coefficient
box. -/
theorem card_dilate_two_add_volume_le_box_of_not_proper
    (P : Erdos186.GAP d r) (hP : ¬ P.Proper) :
    (P.dilate 2).carrier.card + P.volume ≤
      ∏ i, (2 * P.widths i - 1) := by
  rw [Erdos186.GAP.Proper, Function.Injective] at hP
  push_neg at hP
  obtain ⟨a, b, hab, hne⟩ := hP
  have hdiff : ∃ i, a i ≠ b i := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hdiff
  by_cases hablt : (a i : ℕ) < (b i : ℕ)
  · exact P.card_dilate_two_add_volume_le_box_of_collision hab hablt
  · have hbalt : (b i : ℕ) < (a i : ℕ) := by
      have : (a i : ℕ) ≠ (b i : ℕ) := by
        exact fun h ↦ hi (Fin.ext h)
      omega
    exact P.card_dilate_two_add_volume_le_box_of_collision hab.symm hbalt

/-- The product of the shortened doubled widths is strictly smaller than
the full doubled box whenever the rank is positive. -/
theorem prod_two_width_sub_one_lt_pow_two_mul_volume
    (P : Erdos186.GAP d r) (i : Fin r) :
    (∏ j, (2 * P.widths j - 1)) < 2 ^ r * P.volume := by
  calc
    (∏ j, (2 * P.widths j - 1)) < ∏ j, 2 * P.widths j := by
      apply Finset.prod_lt_prod
      · intro j _hj
        have hw := P.width_pos j
        omega
      · intro j _hj
        omega
      · exact ⟨i, Finset.mem_univ i, by
          have hw := P.width_pos i
          omega⟩
    _ = 2 ^ r * P.volume := by
      rw [Erdos186.GAP.volume, Finset.prod_mul_distrib]
      simp

/-- **CFP Lemma 2.19, coarse form.**  The actual doubled carrier of a
nonproper rank-`r` GAP has size strictly below `(2^r - 1) vol(P)`. -/
theorem card_dilate_two_lt_pow_sub_one_mul_volume_of_not_proper
    (P : Erdos186.GAP d r) (hP : ¬ P.Proper) :
    (P.dilate 2).carrier.card < (2 ^ r - 1) * P.volume := by
  rw [Erdos186.GAP.Proper, Function.Injective] at hP
  push_neg at hP
  obtain ⟨a, b, _hab, hne⟩ := hP
  have hdiff : ∃ i, a i ≠ b i := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨i, _hi⟩ := hdiff
  have hsum : (P.dilate 2).carrier.card + P.volume < 2 ^ r * P.volume :=
    lt_of_le_of_lt (P.card_dilate_two_add_volume_le_box_of_not_proper (by
      rw [Erdos186.GAP.Proper, Function.Injective]
      push_neg
      exact ⟨a, b, _hab, hne⟩))
      (P.prod_two_width_sub_one_lt_pow_two_mul_volume i)
  have hpow : 1 ≤ 2 ^ r := by simpa using Nat.one_le_pow' r 1
  have hrewrite : 2 ^ r * P.volume = (2 ^ r - 1) * P.volume + P.volume := by
    conv_lhs => rw [← Nat.sub_add_cancel hpow]
    rw [Nat.add_mul, one_mul]
  rw [hrewrite] at hsum
  exact Nat.add_lt_add_iff_right.mp hsum

end GAP

end Erdos186
