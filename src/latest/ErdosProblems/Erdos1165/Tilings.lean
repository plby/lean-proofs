/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# The six domino tilings in the planar favorite-site argument

This file proves the finite combinatorial observation used in the upper bound
of Hao--Li--Okada--Zheng.  Their four pairings `X_j` pair every checkerboard-even
site with its neighbor in one of the four cardinal directions.  Their pairings
`Y` and `Y'` pair horizontal neighbors according as the first coordinate of the
left endpoint is even or odd.  Among these six tilings, one separates every set
of at most four lattice sites.

The proof is not an exhaustive search.  If all four `X_j` collide, their four
oriented edges inject into the product of the checkerboard-even and odd parts
of the site set.  Since there are at most four sites, both parts have size two
and those four edges form a complete `K_{2,2}`.  Elementary lattice geometry
then shows that `Y` and `Y'` cannot both collide.

Reference: C. Hao, X. Li, I. Okada, and Y. Zheng, *Favorite Sites for Simple
Random Walk in Two and More Dimensions*, arXiv:2409.00995, equations
(4.4), (4.29), (4.30), and the combinatorial argument after Proposition 4.7.
-/

namespace Erdos1165.Tilings

/-- A lattice site in `ℤ²`. -/
abbrev Point := ℤ × ℤ

/-- The four directions indexing the HLOZ checkerboard pairings `X_j`. -/
abbrev CheckerDirection := Fin 4

/-- The four cardinal unit vectors, in east, west, north, south order. -/
def directionVector : CheckerDirection → Point
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | 3 => (0, -1)

lemma directionVector_injective : Function.Injective directionVector := by
  intro d e h
  fin_cases d <;> fin_cases e <;> simp_all [directionVector]

/-- Translation of a lattice site by a lattice vector. -/
def shift (x d : Point) : Point := (x.1 + d.1, x.2 + d.2)

lemma shift_left_injective (x : Point) : Function.Injective (shift x) := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only [shift, Prod.mk.injEq] at h ⊢
  omega

/-- Checkerboard parity: `true` exactly when the coordinate sum is even. -/
def checkerEven (x : Point) : Bool := (x.1 + x.2) % 2 == 0

/-- Column parity: `true` exactly when the first coordinate is even. -/
def columnEven (x : Point) : Bool := x.1 % 2 == 0

lemma checkerEven_shift_direction_eq_false (x : Point) (d : CheckerDirection)
    (hx : checkerEven x = true) : checkerEven (shift x (directionVector d)) = false := by
  rcases x with ⟨x₁, x₂⟩
  fin_cases d <;>
    simp only [checkerEven, shift, directionVector, beq_iff_eq,
      beq_eq_false_iff_ne] at hx ⊢ <;>
    omega

/-- A collision in the HLOZ checkerboard tiling oriented in direction `d`.
The canonical representative of a domino is its checkerboard-even endpoint. -/
def checkerCollision (S : Finset Point) (d : CheckerDirection) : Prop :=
  ∃ x ∈ S, checkerEven x = true ∧ shift x (directionVector d) ∈ S

/-- A collision in the horizontal tiling whose left endpoints have the selected
first-coordinate parity. -/
def columnCollision (S : Finset Point) (evenLeft : Bool) : Prop :=
  ∃ x ∈ S, columnEven x = evenLeft ∧ shift x (1, 0) ∈ S

/-- Cardinal adjacency, oriented from its first argument. -/
def cardinalAdjacent (x y : Point) : Prop :=
  ∃ d : CheckerDirection, y = shift x (directionVector d)

private lemma four_checker_collisions_force_all_cross_edges (S : Finset Point)
    (hcard : S.card ≤ 4) (hall : ∀ d, checkerCollision S d) :
    (∀ x ∈ S, checkerEven x = true →
      ∀ y ∈ S, checkerEven y = false → cardinalAdjacent x y) ∧
    (S.filter fun x ↦ checkerEven x = true).card = 2 ∧
    (S.filter fun x ↦ checkerEven x = false).card = 2 := by
  classical
  let E := S.filter fun x ↦ checkerEven x = true
  let O := S.filter fun x ↦ checkerEven x = false
  let base : CheckerDirection → Point := fun d ↦ (hall d).choose
  let edge : CheckerDirection → Point × Point :=
    fun d ↦ (base d, shift (base d) (directionVector d))
  have hbase (d : CheckerDirection) :
      base d ∈ S ∧ checkerEven (base d) = true ∧
        shift (base d) (directionVector d) ∈ S := by
    exact (hall d).choose_spec
  have hedge_inj : Function.Injective edge := by
    intro d e hde
    have hbase_eq : base d = base e := congrArg Prod.fst hde
    have hshift_eq : shift (base d) (directionVector d) =
        shift (base e) (directionVector e) := congrArg Prod.snd hde
    rw [hbase_eq] at hshift_eq
    exact directionVector_injective (shift_left_injective (base e) hshift_eq)
  let A : Finset (Point × Point) := Finset.univ.image edge
  have hAcard : A.card = 4 := by
    rw [show A = Finset.univ.image edge from rfl,
      Finset.card_image_of_injective _ hedge_inj]
    decide
  have hAsub : A ⊆ E ×ˢ O := by
    intro z hz
    simp only [A, Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨d, rfl⟩ := hz
    simp only [edge, Finset.mem_product, E, O, Finset.mem_filter]
    exact ⟨⟨(hbase d).1, (hbase d).2.1⟩,
      ⟨(hbase d).2.2, checkerEven_shift_direction_eq_false _ _ (hbase d).2.1⟩⟩
  have hprod_ge : 4 ≤ E.card * O.card := by
    rw [← Finset.card_product]
    rw [← hAcard]
    exact Finset.card_le_card hAsub
  have hsum : E.card + O.card = S.card := by
    simpa only [E, O, Bool.not_eq_true] using
      (Finset.card_filter_add_card_filter_not (s := S)
        (p := fun x ↦ checkerEven x = true))
  have hcounts : E.card = 2 ∧ O.card = 2 := by
    have hEle : E.card ≤ 4 := by omega
    interval_cases hE : E.card <;> norm_num [hE] at hprod_ge <;> try omega
    all_goals
      have hOpos : 0 < O.card := Finset.card_pos.mpr hprod_ge
      omega
  have hproductCard : (E ×ˢ O).card = 4 := by
    rw [Finset.card_product, hcounts.1, hcounts.2]
  have hAeq : A = E ×ˢ O := by
    apply Finset.eq_of_subset_of_card_le hAsub
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro x hxS hxEven y hyS hyOdd
    have hxy : (x, y) ∈ E ×ˢ O := by
      simp only [Finset.mem_product, E, O, Finset.mem_filter]
      exact ⟨⟨hxS, hxEven⟩, ⟨hyS, hyOdd⟩⟩
    rw [← hAeq] at hxy
    simp only [A, Finset.mem_image, Finset.mem_univ, true_and] at hxy
    obtain ⟨d, hd⟩ := hxy
    have hfirst : base d = x := congrArg Prod.fst hd
    have hsecond : shift (base d) (directionVector d) = y := congrArg Prod.snd hd
    exact ⟨d, by rw [← hfirst]; exact hsecond.symm⟩
  · simpa only [E] using hcounts.1
  · simpa only [O] using hcounts.2

private lemma exists_other_of_card_eq_two {S : Finset Point} (hcard : S.card = 2)
    {x : Point} (hx : x ∈ S) : ∃ y ∈ S, y ≠ x := by
  have htwo : 1 < S.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  by_cases hax : a = x
  · exact ⟨b, hb, by rintro rfl; exact hab hax⟩
  · exact ⟨a, ha, hax⟩

private lemma not_both_column_collisions_of_all_cross_edges (S : Finset Point)
    (hcross : ∀ x ∈ S, checkerEven x = true →
      ∀ y ∈ S, checkerEven y = false → cardinalAdjacent x y)
    (hEcard : (S.filter fun x ↦ checkerEven x = true).card = 2)
    (hOcard : (S.filter fun x ↦ checkerEven x = false).card = 2) :
    ¬ (columnCollision S true ∧ columnCollision S false) := by
  rintro ⟨heven, hodd⟩
  obtain ⟨x, hxS, hxcol, hxright⟩ := heven
  obtain ⟨u, huS, hucol, huright⟩ := hodd
  let y := shift x (1, 0)
  let v := shift u (1, 0)
  have hyS : y ∈ S := hxright
  have hvS : v ∈ S := huright
  rcases x with ⟨x₁, x₂⟩
  rcases u with ⟨u₁, u₂⟩
  simp only [columnEven, beq_iff_eq] at hxcol
  simp only [columnEven, beq_eq_false_iff_ne] at hucol
  simp only [y, v, shift] at hyS hvS ⊢
  by_cases hxpar : checkerEven (x₁, x₂) = true
  · have hypar : checkerEven (x₁ + 1, x₂ + 0) = false :=
      checkerEven_shift_direction_eq_false (x₁, x₂) 0 hxpar
    by_cases hupar : checkerEven (u₁, u₂) = true
    · have hvpar : checkerEven (u₁ + 1, u₂ + 0) = false :=
        checkerEven_shift_direction_eq_false (u₁, u₂) 0 hupar
      obtain ⟨d₁, hd₁⟩ := hcross _ hxS hxpar _ hvS hvpar
      obtain ⟨d₂, hd₂⟩ := hcross _ huS hupar _ hyS hypar
      fin_cases d₁ <;> fin_cases d₂ <;>
        simp only [shift, directionVector, Prod.mk.injEq] at hd₁ hd₂ <;>
        omega
    · have hupar' : checkerEven (u₁, u₂) = false := Bool.eq_false_of_not_eq_true hupar
      have hvpar : checkerEven (u₁ + 1, u₂ + 0) = true := by
        unfold checkerEven at hupar' ⊢
        simp only [beq_eq_false_iff_ne, beq_iff_eq] at hupar' ⊢
        omega
      by_cases hyu : (x₁ + 1, x₂ + 0) = (u₁, u₂)
      · have hyO : (x₁ + 1, x₂ + 0) ∈ S.filter fun z ↦ checkerEven z = false := by
          simp only [Finset.mem_filter]
          exact ⟨hyS, hypar⟩
        obtain ⟨w, hwO, hwne⟩ := exists_other_of_card_eq_two hOcard hyO
        have hwS := (Finset.mem_filter.mp hwO).1
        have hwpar := (Finset.mem_filter.mp hwO).2
        obtain ⟨d₁, hd₁⟩ := hcross _ hxS hxpar _ hwS hwpar
        obtain ⟨d₂, hd₂⟩ := hcross _ hvS hvpar _ hwS hwpar
        rcases w with ⟨w₁, w₂⟩
        fin_cases d₁ <;> fin_cases d₂ <;>
          simp only [shift, directionVector, Prod.mk.injEq] at hd₁ hd₂ hyu <;>
          apply hwne <;> apply Prod.ext <;> omega
      · by_cases hxv : (x₁, x₂) = (u₁ + 1, u₂ + 0)
        · have hxE : (x₁, x₂) ∈ S.filter fun z ↦ checkerEven z = true := by
            simp only [Finset.mem_filter]
            exact ⟨hxS, hxpar⟩
          obtain ⟨w, hwE, hwne⟩ := exists_other_of_card_eq_two hEcard hxE
          have hwS := (Finset.mem_filter.mp hwE).1
          have hwpar := (Finset.mem_filter.mp hwE).2
          obtain ⟨d₁, hd₁⟩ := hcross _ hwS hwpar _ huS hupar'
          obtain ⟨d₂, hd₂⟩ := hcross _ hwS hwpar _ hyS hypar
          rcases w with ⟨w₁, w₂⟩
          fin_cases d₁ <;> fin_cases d₂ <;>
            simp only [shift, directionVector, Prod.mk.injEq] at hd₁ hd₂ hxv <;>
            apply hwne <;> apply Prod.ext <;> omega
        · obtain ⟨d₁, hd₁⟩ := hcross _ hxS hxpar _ huS hupar'
          obtain ⟨d₂, hd₂⟩ := hcross _ hvS hvpar _ hyS hypar
          fin_cases d₁ <;> fin_cases d₂ <;>
            simp only [shift, directionVector, Prod.mk.injEq] at hd₁ hd₂ hyu hxv <;>
            omega
  · have hxpar' : checkerEven (x₁, x₂) = false := Bool.eq_false_of_not_eq_true hxpar
    have hypar : checkerEven (x₁ + 1, x₂ + 0) = true := by
      unfold checkerEven at hxpar' ⊢
      simp only [beq_eq_false_iff_ne, beq_iff_eq] at hxpar' ⊢
      omega
    by_cases hupar : checkerEven (u₁, u₂) = true
    · have hvpar : checkerEven (u₁ + 1, u₂ + 0) = false :=
        checkerEven_shift_direction_eq_false (u₁, u₂) 0 hupar
      by_cases hyu : (x₁ + 1, x₂ + 0) = (u₁, u₂)
      · have hyE : (x₁ + 1, x₂ + 0) ∈ S.filter fun z ↦ checkerEven z = true := by
          simp only [Finset.mem_filter]
          exact ⟨hyS, hypar⟩
        obtain ⟨w, hwE, hwne⟩ := exists_other_of_card_eq_two hEcard hyE
        have hwS := (Finset.mem_filter.mp hwE).1
        have hwpar := (Finset.mem_filter.mp hwE).2
        obtain ⟨d₁, hd₁⟩ := hcross _ hwS hwpar _ hxS hxpar'
        obtain ⟨d₂, hd₂⟩ := hcross _ hwS hwpar _ hvS hvpar
        rcases w with ⟨w₁, w₂⟩
        fin_cases d₁ <;> fin_cases d₂ <;>
          simp only [shift, directionVector, Prod.mk.injEq] at hd₁ hd₂ hyu <;>
          apply hwne <;> apply Prod.ext <;> omega
      · by_cases hxv : (x₁, x₂) = (u₁ + 1, u₂ + 0)
        · have hxO : (x₁, x₂) ∈ S.filter fun z ↦ checkerEven z = false := by
            simp only [Finset.mem_filter]
            exact ⟨hxS, hxpar'⟩
          obtain ⟨w, hwO, hwne⟩ := exists_other_of_card_eq_two hOcard hxO
          have hwS := (Finset.mem_filter.mp hwO).1
          have hwpar := (Finset.mem_filter.mp hwO).2
          obtain ⟨d₁, hd₁⟩ := hcross _ hyS hypar _ hwS hwpar
          obtain ⟨d₂, hd₂⟩ := hcross _ huS hupar _ hwS hwpar
          rcases w with ⟨w₁, w₂⟩
          fin_cases d₁ <;> fin_cases d₂ <;>
            simp only [shift, directionVector, Prod.mk.injEq] at hd₁ hd₂ hxv <;>
            apply hwne <;> apply Prod.ext <;> omega
        · obtain ⟨d₁, hd₁⟩ := hcross _ huS hupar _ hxS hxpar'
          obtain ⟨d₂, hd₂⟩ := hcross _ hyS hypar _ hvS hvpar
          fin_cases d₁ <;> fin_cases d₂ <;>
            simp only [shift, directionVector, Prod.mk.injEq] at hd₁ hd₂ hyu hxv <;>
            omega
    · have hupar' : checkerEven (u₁, u₂) = false := Bool.eq_false_of_not_eq_true hupar
      have hvpar : checkerEven (u₁ + 1, u₂ + 0) = true := by
        unfold checkerEven at hupar' ⊢
        simp only [beq_eq_false_iff_ne, beq_iff_eq] at hupar' ⊢
        omega
      obtain ⟨d₁, hd₁⟩ := hcross _ hyS hypar _ huS hupar'
      obtain ⟨d₂, hd₂⟩ := hcross _ hvS hvpar _ hxS hxpar'
      fin_cases d₁ <;> fin_cases d₂ <;>
        simp only [shift, directionVector, Prod.mk.injEq] at hd₁ hd₂ <;>
        omega

/-- Among the four HLOZ checkerboard-oriented tilings and the two horizontal
column-parity tilings, some tiling has no domino containing two points of `S`. -/
theorem six_tilings (S : Finset Point) (hcard : S.card ≤ 4) :
    (∃ d, ¬ checkerCollision S d) ∨
      ¬ columnCollision S true ∨ ¬ columnCollision S false := by
  by_cases hchecker : ∃ d, ¬ checkerCollision S d
  · exact Or.inl hchecker
  · right
    have hall : ∀ d, checkerCollision S d := by simpa only [not_exists, not_not] using hchecker
    have hdata := four_checker_collisions_force_all_cross_edges S hcard hall
    have hnotboth :=
      not_both_column_collisions_of_all_cross_edges S hdata.1 hdata.2.1 hdata.2.2
    tauto

/-- The six tilings used in HLOZ: four checkerboard-oriented matchings and two
horizontal matchings selected by the parity of the left endpoint's column. -/
inductive Tiling
  | checker (direction : CheckerDirection)
  | evenColumns
  | oddColumns
  deriving DecidableEq, Fintype

/-- Two sites lie in one domino of a selected HLOZ tiling. -/
def sameDomino : Tiling → Point → Point → Prop
  | .checker d, x, y =>
      (checkerEven x = true ∧ y = shift x (directionVector d)) ∨
      (checkerEven y = true ∧ x = shift y (directionVector d))
  | .evenColumns, x, y =>
      (columnEven x = true ∧ y = shift x (1, 0)) ∨
      (columnEven y = true ∧ x = shift y (1, 0))
  | .oddColumns, x, y =>
      (columnEven x = false ∧ y = shift x (1, 0)) ∨
      (columnEven y = false ∧ x = shift y (1, 0))

lemma sameDomino_comm (t : Tiling) (x y : Point) :
    sameDomino t x y ↔ sameDomino t y x := by
  cases t <;> simp only [sameDomino, or_comm]

/-- A finite set collides with a tiling when one of its dominoes contains both
endpoints. -/
def collision (S : Finset Point) : Tiling → Prop
  | .checker d => checkerCollision S d
  | .evenColumns => columnCollision S true
  | .oddColumns => columnCollision S false

lemma not_sameDomino_of_not_collision {S : Finset Point} {t : Tiling}
    (ht : ¬ collision S t) {x y : Point} (hx : x ∈ S) (hy : y ∈ S) :
    ¬ sameDomino t x y := by
  intro hxy
  cases t with
  | checker d =>
      apply ht
      unfold collision checkerCollision
      rcases hxy with ⟨hxe, rfl⟩ | ⟨hye, rfl⟩
      · exact ⟨x, hx, hxe, hy⟩
      · exact ⟨y, hy, hye, hx⟩
  | evenColumns =>
      apply ht
      unfold collision columnCollision
      rcases hxy with ⟨hxe, rfl⟩ | ⟨hye, rfl⟩
      · exact ⟨x, hx, hxe, hy⟩
      · exact ⟨y, hy, hye, hx⟩
  | oddColumns =>
      apply ht
      unfold collision columnCollision
      rcases hxy with ⟨hxe, rfl⟩ | ⟨hye, rfl⟩
      · exact ⟨x, hx, hxe, hy⟩
      · exact ⟨y, hy, hye, hx⟩

/-- A set of at most four lattice sites is collision-free for one of HLOZ's
six domino tilings. -/
theorem exists_collisionFree_tiling (S : Finset Point) (hcard : S.card ≤ 4) :
    ∃ t : Tiling, ¬ collision S t := by
  rcases six_tilings S hcard with ⟨d, hd⟩ | heven | hodd
  · exact ⟨Tiling.checker d, by simpa only [collision] using hd⟩
  · exact ⟨Tiling.evenColumns, by simpa only [collision] using heven⟩
  · exact ⟨Tiling.oddColumns, by simpa only [collision] using hodd⟩

/-- The set of sites in a four-entry tuple. -/
def fourPointSet (p : Fin 4 → Point) : Finset Point := Finset.univ.image p

lemma fourPointSet_card_le (p : Fin 4 → Point) : (fourPointSet p).card ≤ 4 := by
  rw [fourPointSet]
  calc
    (Finset.univ.image p).card ≤ Finset.univ.card := Finset.card_image_le
    _ = 4 := by decide

/-- Point-indexed form of the six-tiling lemma. The injectivity hypothesis says
that the four inputs really are four distinct sites. -/
theorem exists_tiling_separating_four_distinct_points (p : Fin 4 → Point)
    (_hp : Function.Injective p) :
    ∃ t : Tiling, ∀ i j : Fin 4, i ≠ j → ¬ sameDomino t (p i) (p j) := by
  obtain ⟨t, ht⟩ := exists_collisionFree_tiling (fourPointSet p) (fourPointSet_card_le p)
  refine ⟨t, ?_⟩
  intro i j _hij
  apply not_sameDomino_of_not_collision ht
  · simp [fourPointSet]
  · simp [fourPointSet]

end Erdos1165.Tilings
