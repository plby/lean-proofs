/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import Mathlib

/-!
# Cyclic-group estimates for Erdős Problem 55

This file formalizes the elementary cyclic-group part of the
Conlon--Fox--Pham argument.  The definitions retain the indices of a finite
sequence, so repeated terms still represent distinct subset-sum choices.

The principal counting lemma below is CFP Lemma 2.6: a finite set in a
finite abelian group has few translations which enlarge it by at most `d`.
We record the conclusion without division, which is the exact integral form
used later in the probabilistic growth argument.
-/

open scoped BigOperators

namespace Erdos55

section IndexedSubsetSums

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- Subset sums of an indexed finite family.  Unlike `Finset.subsetSum`, this
definition retains repeated values at different indices. -/
def indexedSubsetSums {ι : Type*} [Fintype ι] (f : ι → G) : Finset G :=
  Finset.univ.powerset.image fun s ↦ ∑ i ∈ s, f i

@[simp]
theorem mem_indexedSubsetSums {ι : Type*} [Fintype ι] {f : ι → G} {x : G} :
    x ∈ indexedSubsetSums f ↔ ∃ s : Finset ι, (∑ i ∈ s, f i) = x := by
  simp [indexedSubsetSums]

@[simp]
theorem zero_mem_indexedSubsetSums {ι : Type*} [Fintype ι] (f : ι → G) :
    0 ∈ indexedSubsetSums f := by
  exact mem_indexedSubsetSums.mpr ⟨∅, by simp⟩

/-- Restricting an indexed family can only remove subset sums. -/
theorem indexedSubsetSums_restrict_subset {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) (f : ι → G) :
    indexedSubsetSums (f ∘ e) ⊆ indexedSubsetSums f := by
  intro x hx
  obtain ⟨s, rfl⟩ := mem_indexedSubsetSums.mp hx
  refine mem_indexedSubsetSums.mpr ⟨s.map e, ?_⟩
  rw [Finset.sum_map]
  rfl

end IndexedSubsetSums

section AlmostPeriods

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Translation of a finite set in an additive group. -/
def translateFinset (x : G) (D : Finset G) : Finset G :=
  D.image fun a ↦ x + a

@[simp]
theorem mem_translateFinset {x y : G} {D : Finset G} :
    y ∈ translateFinset x D ↔ y - x ∈ D := by
  constructor
  · intro hy
    obtain ⟨a, ha, hya⟩ := Finset.mem_image.mp hy
    subst y
    simpa [add_comm] using ha
  · intro hy
    apply Finset.mem_image.mpr
    refine ⟨y - x, hy, ?_⟩
    abel

@[simp]
theorem card_translateFinset (x : G) (D : Finset G) :
    (translateFinset x D).card = D.card := by
  exact Finset.card_image_of_injective D fun _ _ h ↦ add_left_cancel h

/-- New points created when `D` is translated by `x`. -/
def translationGrowth (D : Finset G) (x : G) : ℕ :=
  (translateFinset x D \ D).card

/-- The translations which create at most `d` new points. -/
def almostPeriods (D : Finset G) (d : ℕ) : Finset G :=
  Finset.univ.filter fun x ↦ translationGrowth D x ≤ d

@[simp]
theorem mem_almostPeriods {D : Finset G} {d : ℕ} {x : G} :
    x ∈ almostPeriods D d ↔ translationGrowth D x ≤ d := by
  simp [almostPeriods]

theorem translationGrowth_le_card (D : Finset G) (x : G) :
    translationGrowth D x ≤ D.card := by
  rw [translationGrowth]
  exact (Finset.card_le_card (Finset.sdiff_subset : translateFinset x D \ D ⊆ _)).trans_eq
    (card_translateFinset x D)

@[simp]
theorem zero_mem_almostPeriods (D : Finset G) (d : ℕ) :
    0 ∈ almostPeriods D d := by
  simp [translationGrowth, translateFinset]

/-- New translated points are in bijection with old points whose translate
leaves `D`. -/
theorem translationGrowth_eq_card_filter (D : Finset G) (x : G) :
    translationGrowth D x = (D.filter fun a ↦ x + a ∉ D).card := by
  let e : G ↪ G := ⟨fun a ↦ x + a, fun _ _ h ↦ add_left_cancel h⟩
  have himage : translateFinset x D \ D =
      (D.filter fun a ↦ x + a ∉ D).map e := by
    ext y
    simp only [Finset.mem_sdiff, mem_translateFinset, Finset.mem_map,
      Finset.mem_filter]
    constructor
    · rintro ⟨hyx, hyD⟩
      refine ⟨y - x, ⟨hyx, ?_⟩, ?_⟩
      · simpa [add_comm] using hyD
      · change x + (y - x) = y
        abel
    · rintro ⟨a, ⟨haD, hxaD⟩, rfl⟩
      refine ⟨?_, hxaD⟩
      convert haD using 1
      change x + a - x = a
      abel
  rw [translationGrowth, himage, Finset.card_map]

/-- For a fixed point `a`, exactly the complement of `D` many translations
move `a` outside `D`. -/
theorem card_translations_leaving (D : Finset G) (a : G) :
    (Finset.univ.filter fun x : G ↦ x + a ∉ D).card = Fintype.card G - D.card := by
  let e : G ≃ G := Equiv.addRight a
  have hmap : (Finset.univ.filter fun x : G ↦ x + a ∉ D).map e.toEmbedding = Dᶜ := by
    ext y
    simp [e]
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map] at hcard
  rw [Finset.card_compl] at hcard
  exact hcard

/-- Double counting the pairs `(x,a)` for which translating `a ∈ D` by `x`
leaves `D`. -/
theorem sum_translationGrowth (D : Finset G) :
    (∑ x : G, translationGrowth D x) = D.card * (Fintype.card G - D.card) := by
  simp_rw [translationGrowth_eq_card_filter]
  change (∑ x ∈ (Finset.univ : Finset G),
    (D.bipartiteAbove (fun x a : G ↦ x + a ∉ D) x).card) = _
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Finset.univ : Finset G)) (t := D)
    (r := fun x a : G ↦ x + a ∉ D)]
  simp_rw [Finset.bipartiteBelow, card_translations_leaving]
  simp

/-- **CFP Lemma 2.6 (integral form).**  If `d < |D|`, then the number of
translations which enlarge `D` by at most `d` satisfies

`(|D| - d) |G_d| ≤ |D|²`.

This avoids introducing floor divisions and is exactly the estimate needed
for both growth regimes of the cyclic random-walk argument. -/
theorem card_almostPeriods_mul_sub_le_sq (D : Finset G) {d : ℕ}
    (hd : d < D.card) :
    (almostPeriods D d).card * (D.card - d) ≤ D.card ^ 2 := by
  let q := D.card
  let M := Fintype.card G
  let g := (almostPeriods D d).card
  have hqM : q ≤ M := by
    dsimp [q, M]
    exact Finset.card_le_univ D
  have hgM : g ≤ M := by
    dsimp [g, M]
    exact Finset.card_le_univ (almostPeriods D d)
  have hdq : d ≤ q := by omega
  have hpoint : ∀ x : G,
      translationGrowth D x ≤ if x ∈ almostPeriods D d then d else q := by
    intro x
    split_ifs with hx
    · exact mem_almostPeriods.mp hx
    · simpa [q] using translationGrowth_le_card D x
  have hsum_le : q * (M - q) ≤ g * d + (M - g) * q := by
    rw [← sum_translationGrowth D]
    calc
      (∑ x : G, translationGrowth D x)
          ≤ ∑ x : G, if x ∈ almostPeriods D d then d else q := by
            exact Finset.sum_le_sum fun x _ ↦ hpoint x
      _ = g * d + (M - g) * q := by
        have hbad : (Finset.univ.filter fun x : G ↦ x ∉ almostPeriods D d) =
            (almostPeriods D d)ᶜ := by
          ext x
          simp
        simp only [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul]
        rw [hbad, Finset.card_compl]
        simp [g, M]
  have htotal_left : q * (M - q) + q ^ 2 = M * q := by
    calc
      q * (M - q) + q ^ 2 = q * (M - q) + q * q := by rw [pow_two]
      _ = q * ((M - q) + q) := by rw [Nat.mul_add]
      _ = q * M := by rw [Nat.sub_add_cancel hqM]
      _ = M * q := Nat.mul_comm _ _
  have htotal_right :
      g * d + (M - g) * q + g * (q - d) = M * q := by
    calc
      g * d + (M - g) * q + g * (q - d)
          = (M - g) * q + g * (d + (q - d)) := by ring
      _ = (M - g) * q + g * q := by rw [Nat.add_sub_of_le hdq]
      _ = M * q := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hgM]
  have haux : q * (M - q) + g * (q - d) ≤
      q * (M - q) + q ^ 2 := by
    calc
      q * (M - q) + g * (q - d)
        ≤ (g * d + (M - g) * q) + g * (q - d) :=
          Nat.add_le_add_right hsum_le _
      _ = M * q := htotal_right
      _ = q * (M - q) + q ^ 2 := htotal_left.symm
  exact Nat.le_of_add_le_add_left haux

/-- Monotonicity in the permitted growth. -/
theorem almostPeriods_mono (D : Finset G) {d e : ℕ} (hde : d ≤ e) :
    almostPeriods D d ⊆ almostPeriods D e := by
  intro x hx
  rw [mem_almostPeriods] at hx ⊢
  exact hx.trans hde

/-- Translating twice is the same as translating by the sum. -/
theorem translateFinset_add (x y : G) (D : Finset G) :
    translateFinset x (translateFinset y D) = translateFinset (x + y) D := by
  ext z
  simp only [mem_translateFinset]
  constructor <;> intro hz
  · convert hz using 1 <;> abel
  · convert hz using 1 <;> abel

/-- Translation growth is subadditive.  This is the pointwise form of CFP
Lemma 2.7. -/
theorem translationGrowth_add_le (D : Finset G) (x y : G) :
    translationGrowth D (x + y) ≤ translationGrowth D x + translationGrowth D y := by
  have hsub : translateFinset (x + y) D \ D ⊆
      (translateFinset x D \ D) ∪ translateFinset x (translateFinset y D \ D) := by
    intro z hz
    rcases Finset.mem_sdiff.mp hz with ⟨hztrans, hzD⟩
    have hzxy : z - (x + y) ∈ D := mem_translateFinset.mp hztrans
    by_cases hzxD : z - x ∈ D
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨mem_translateFinset.mpr hzxD, hzD⟩
    · apply Finset.mem_union_right
      apply mem_translateFinset.mpr
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hzxD⟩
      apply mem_translateFinset.mpr
      rw [show z - x - y = z - (x + y) by abel]
      exact hzxy
  rw [translationGrowth]
  calc
    (translateFinset (x + y) D \ D).card
        ≤ ((translateFinset x D \ D) ∪
            translateFinset x (translateFinset y D \ D)).card :=
          Finset.card_le_card hsub
    _ ≤ (translateFinset x D \ D).card +
          (translateFinset x (translateFinset y D \ D)).card :=
          Finset.card_union_le _ _
    _ = translationGrowth D x + translationGrowth D y := by
      rw [card_translateFinset]
      rfl

/-- The growth of a sum of translations is bounded by the sum of their
individual growths. -/
theorem translationGrowth_list_sum_le (D : Finset G) (l : List G) :
    translationGrowth D l.sum ≤ (l.map (translationGrowth D)).sum := by
  induction l with
  | nil => simp [translationGrowth, translateFinset]
  | cons x l ih =>
      simp only [List.sum_cons, List.map_cons, List.sum_cons]
      exact (translationGrowth_add_le D x l.sum).trans (Nat.add_le_add_left ih _)

/-- **CFP Lemma 2.7.**  A sum of `k` `d`-almost-periods is a
`(k*d)`-almost-period.  Repetitions are permitted, as in the paper's iterated
sumset notation. -/
theorem list_sum_mem_almostPeriods (D : Finset G) {d : ℕ} (l : List G)
    (hl : ∀ x ∈ l, x ∈ almostPeriods D d) :
    l.sum ∈ almostPeriods D (l.length * d) := by
  rw [mem_almostPeriods]
  apply (translationGrowth_list_sum_le D l).trans
  induction l with
  | nil => simp
  | cons x l ih =>
      have hx : translationGrowth D x ≤ d :=
        mem_almostPeriods.mp (hl x (by simp))
      have htail : (l.map (translationGrowth D)).sum ≤ l.length * d := by
        apply ih
        intro y hy
        exact hl y (by simp [hy])
      simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hx htail

end AlmostPeriods

end Erdos55
