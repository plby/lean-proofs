/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition74Construction
import Mathlib.Combinatorics.Pigeonhole

/-!
# Bilu Section 7.1: the residue-cell Freiman map

This file formalizes Bilu's map

`x ↦ (x, (⌊⟨x,aᵢ⟫-bᵢ⌋)ᵢ)`

and the partition of the integer lattice according to which half of the
unit interval contains every fractional part.  On each common cell the map
is an `F₂`-isomorphism: equality of two pair sums is equivalent before and
after applying the map.
-/

namespace Erdos186.CFP.Bilu.Section7FreimanMap

open scoped BigOperators RealInnerProductSpace
open Proposition74Construction SubspaceLattice

noncomputable section

/-- Integral product coordinates used by Bilu's map before the Euclidean
embedding in Proposition 7.4. -/
abbrev IntegralProduct (m r : ℕ) :=
  Mahler.IntegralPoint m × Mahler.IntegralPoint r

/-- The real phase whose floor is adjoined as a new coordinate. -/
def phase {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) (i : Fin r) : ℝ :=
  ⟪integralReal x, a i⟫ - b i

/-- Bilu's floor-valued Freiman map. -/
def freimanMap {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) : IntegralProduct m r :=
  (x, fun i ↦ ⌊phase a b x i⌋)

@[simp]
theorem freimanMap_fst {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) :
    (freimanMap a b x).1 = x := rfl

@[simp]
theorem freimanMap_snd_apply {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) (i : Fin r) :
    (freimanMap a b x).2 i = ⌊phase a b x i⌋ := rfl

/-- The map is injective because it retains every original coordinate. -/
theorem freimanMap_injective {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ) :
    Function.Injective (freimanMap a b) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

/-- A residue color records the lower or upper half of the unit interval. -/
def residueColor {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) : Fin r → Fin 2 :=
  fun i ↦ if Int.fract (phase a b x i) < 1 / 2 then 0 else 1

/-- Membership in the half-open residue cell indexed by `alpha`. -/
def InResidueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (x : Mahler.IntegralPoint m) : Prop :=
  ∀ i, ((alpha i : ℕ) : ℝ) / 2 ≤ Int.fract (phase a b x i) ∧
    Int.fract (phase a b x i) < (((alpha i : ℕ) : ℝ) + 1) / 2

/-- The canonical color places every lattice point in a residue cell. -/
theorem inResidueCell_residueColor {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) :
    InResidueCell a b (residueColor a b x) x := by
  intro i
  by_cases hhalf : Int.fract (phase a b x i) < 1 / 2
  · simp only [residueColor, hhalf, ↓reduceIte, Fin.val_zero,
      Nat.cast_zero, zero_div, zero_add]
    exact ⟨Int.fract_nonneg _, trivial⟩
  · have hge : 1 / 2 ≤ Int.fract (phase a b x i) := le_of_not_gt hhalf
    have hlt : Int.fract (phase a b x i) < 1 := Int.fract_lt_one _
    simp only [residueColor, hhalf, ↓reduceIte, Fin.val_one, Nat.cast_one]
    constructor
    · exact hge
    · norm_num
      exact hlt

/-- A point belongs to exactly the cell indexed by its canonical color. -/
theorem inResidueCell_iff_residueColor_eq {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (x : Mahler.IntegralPoint m) :
    InResidueCell a b alpha x ↔ residueColor a b x = alpha := by
  constructor
  · intro hx
    funext i
    by_cases hhalf : Int.fract (phase a b x i) < 1 / 2
    · have halpha : alpha i = 0 := by
        apply Fin.ext
        have hlt := (alpha i).isLt
        have hlo := (hx i).1
        interval_cases hval : (alpha i : ℕ)
        · rfl
        · norm_num [hval] at hlo
          linarith
      change (if Int.fract (phase a b x i) < 1 / 2 then 0 else 1) = alpha i
      rw [if_pos hhalf]
      exact halpha.symm
    · have hge : 1 / 2 ≤ Int.fract (phase a b x i) := le_of_not_gt hhalf
      have halpha : alpha i = 1 := by
        apply Fin.ext
        have hlt := (alpha i).isLt
        have hhi := (hx i).2
        interval_cases hval : (alpha i : ℕ)
        · norm_num [hval] at hhi
          linarith
        · rfl
      change (if Int.fract (phase a b x i) < 1 / 2 then 0 else 1) = alpha i
      rw [if_neg hhalf]
      exact halpha.symm
  · rintro rfl
    exact inResidueCell_residueColor a b x

/-- The part of a finite lattice set lying in one residue cell. -/
def residueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m)) :
    Finset (Mahler.IntegralPoint m) := by
  classical
  exact K.filter (InResidueCell a b alpha)

@[simp]
theorem mem_residueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m))
    (x : Mahler.IntegralPoint m) :
    x ∈ residueCell a b alpha K ↔ x ∈ K ∧ InResidueCell a b alpha x := by
  simp [residueCell]

/-- The residue cells are exactly the fibers of `residueColor`. -/
theorem residueCell_eq_filter_color {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m)) :
    residueCell a b alpha K = K.filter (fun x ↦ residueColor a b x = alpha) := by
  ext x
  simp [inResidueCell_iff_residueColor_eq]

/-- The finite set is the disjoint union of its `2^r` residue cells. -/
theorem card_eq_sum_card_residueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (K : Finset (Mahler.IntegralPoint m)) :
    K.card = ∑ alpha : Fin r → Fin 2, (residueCell a b alpha K).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := residueColor a b) (s := K)
    (t := Finset.univ) (by simp)]
  apply Finset.sum_congr rfl
  intro alpha _
  rw [residueCell_eq_filter_color]

/-- Bilu's residue-cell pigeonhole estimate: among the `2^r` cells one
contains at least the reciprocal `2^r` proportion, in division-free form. -/
theorem exists_large_residueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (K : Finset (Mahler.IntegralPoint m)) :
    ∃ alpha : Fin r → Fin 2,
      K.card ≤ 2 ^ r * (residueCell a b alpha K).card := by
  let values : Finset ℕ :=
    Finset.univ.image fun alpha : Fin r → Fin 2 ↦
      (residueCell a b alpha K).card
  have hvalues : values.Nonempty := by
    refine ⟨(residueCell a b (fun _ ↦ 0) K).card, ?_⟩
    exact Finset.mem_image.mpr ⟨fun _ ↦ 0, Finset.mem_univ _, rfl⟩
  let M : ℕ := values.max' hvalues
  have hMmem : M ∈ values := by
    exact Finset.max'_mem values hvalues
  obtain ⟨alpha, _halpha, hAlpha⟩ := Finset.mem_image.mp hMmem
  refine ⟨alpha, ?_⟩
  have hcell_le : ∀ beta : Fin r → Fin 2,
      (residueCell a b beta K).card ≤ M := by
    intro beta
    exact Finset.le_max' values _
      (Finset.mem_image.mpr ⟨beta, Finset.mem_univ _, rfl⟩)
  have hsum_le := Finset.sum_le_card_nsmul
    (Finset.univ : Finset (Fin r → Fin 2))
    (fun beta ↦ (residueCell a b beta K).card) M
    (fun beta _ ↦ hcell_le beta)
  rw [← card_eq_sum_card_residueCell a b K] at hsum_le
  have hcardColors : Fintype.card (Fin r → Fin 2) = 2 ^ r := by
    simp
  rw [Finset.card_univ, hcardColors, nsmul_eq_mul] at hsum_le
  simpa [hAlpha, mul_comm] using hsum_le

/-- The image of a residue cell under Bilu's injective map. -/
def mappedResidueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m)) :
    Finset (IntegralProduct m r) :=
  (residueCell a b alpha K).image (freimanMap a b)

/-- The floor-coordinate map preserves the cardinality of every cell. -/
@[simp]
theorem card_mappedResidueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m)) :
    (mappedResidueCell a b alpha K).card =
      (residueCell a b alpha K).card := by
  exact Finset.card_image_of_injective _ (freimanMap_injective a b)

/-- A finite double sumset, presented as the image of ordered pairs. -/
def pairSumset {G : Type*} [Add G] [DecidableEq G] (S : Finset G) : Finset G :=
  (S.product S).image fun p ↦ p.1 + p.2

@[simp]
theorem mem_pairSumset {G : Type*} [Add G] [DecidableEq G]
    (S : Finset G) (z : G) :
    z ∈ pairSumset S ↔ ∃ x ∈ S, ∃ y ∈ S, x + y = z := by
  simp only [pairSumset, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' := Finset.mem_product.mp hp
    exact ⟨p.1, hp'.1, p.2, hp'.2, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

/-- Two maps on the same finite set with exactly the same collision relation
have images of the same cardinality. -/
theorem card_image_eq_card_image_of_eq_iff
    {X Y Z : Type*} [Inhabited X] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z]
    (P : Finset X) (f : X → Y) (g : X → Z)
    (hker : ∀ x ∈ P, ∀ y ∈ P, f x = f y ↔ g x = g y) :
    (P.image f).card = (P.image g).card := by
  classical
  let repF : Y → X := fun z ↦
    if hz : z ∈ P.image f then (Finset.mem_image.mp hz).choose else default
  have hrepF : ∀ z ∈ P.image f, repF z ∈ P ∧ f (repF z) = z := by
    intro z hz
    dsimp only [repF]
    rw [dif_pos hz]
    exact (Finset.mem_image.mp hz).choose_spec
  let transferF : Y → Z := fun z ↦ g (repF z)
  have hmapF : Set.MapsTo transferF (P.image f : Set Y) (P.image g : Set Z) := by
    intro z hz
    exact Finset.mem_image.mpr ⟨repF z, (hrepF z hz).1, rfl⟩
  have hinjF : Set.InjOn transferF (P.image f : Set Y) := by
    intro z hz w hw hzw
    have hfg : f (repF z) = f (repF w) :=
      (hker (repF z) (hrepF z hz).1 (repF w) (hrepF w hw).1).mpr hzw
    rw [(hrepF z hz).2, (hrepF w hw).2] at hfg
    exact hfg
  have hle : (P.image f).card ≤ (P.image g).card :=
    Finset.card_le_card_of_injOn transferF hmapF hinjF
  let repG : Z → X := fun z ↦
    if hz : z ∈ P.image g then (Finset.mem_image.mp hz).choose else default
  have hrepG : ∀ z ∈ P.image g, repG z ∈ P ∧ g (repG z) = z := by
    intro z hz
    dsimp only [repG]
    rw [dif_pos hz]
    exact (Finset.mem_image.mp hz).choose_spec
  let transferG : Z → Y := fun z ↦ f (repG z)
  have hmapG : Set.MapsTo transferG (P.image g : Set Z) (P.image f : Set Y) := by
    intro z hz
    exact Finset.mem_image.mpr ⟨repG z, (hrepG z hz).1, rfl⟩
  have hinjG : Set.InjOn transferG (P.image g : Set Z) := by
    intro z hz w hw hzw
    have hgf : g (repG z) = g (repG w) :=
      (hker (repG z) (hrepG z hz).1 (repG w) (hrepG w hw).1).mp hzw
    rw [(hrepG z hz).2, (hrepG w hw).2] at hgf
    exact hgf
  have hge : (P.image g).card ≤ (P.image f).card :=
    Finset.card_le_card_of_injOn transferG hmapG hinjG
  omega

/-- Four numbers whose fractional parts lie in one interval of length
`1/2` have matching sums of floors whenever their real pair sums match. -/
theorem floor_add_eq_floor_add_of_common_half
    {x₁ x₂ y₁ y₂ c : ℝ}
    (hx₁ : c ≤ Int.fract x₁) (hx₁' : Int.fract x₁ < c + 1 / 2)
    (hx₂ : c ≤ Int.fract x₂) (hx₂' : Int.fract x₂ < c + 1 / 2)
    (hy₁ : c ≤ Int.fract y₁) (hy₁' : Int.fract y₁ < c + 1 / 2)
    (hy₂ : c ≤ Int.fract y₂) (hy₂' : Int.fract y₂ < c + 1 / 2)
    (hsum : x₁ + x₂ = y₁ + y₂) :
    ⌊x₁⌋ + ⌊x₂⌋ = ⌊y₁⌋ + ⌊y₂⌋ := by
  let z : ℤ := ⌊x₁⌋ + ⌊x₂⌋ - (⌊y₁⌋ + ⌊y₂⌋)
  have hzcast : (z : ℝ) =
      (Int.fract y₁ + Int.fract y₂) -
        (Int.fract x₁ + Int.fract x₂) := by
    dsimp only [z]
    rw [Int.cast_sub, Int.cast_add, Int.cast_add]
    rw [Int.fract, Int.fract, Int.fract, Int.fract]
    linarith
  have hzlower : (-1 : ℝ) < (z : ℝ) := by
    rw [hzcast]
    linarith
  have hzupper : (z : ℝ) < 1 := by
    rw [hzcast]
    linarith
  have hzlower' : (-1 : ℤ) < z := by exact_mod_cast hzlower
  have hzupper' : z < (1 : ℤ) := by exact_mod_cast hzupper
  have hz : z = 0 := by omega
  dsimp only [z] at hz
  omega

/-- The phase is affine-linear in exactly the way needed for pair sums:
the shift `b` occurs twice on both sides. -/
theorem phase_pair_sum_eq {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    {x₁ x₂ y₁ y₂ : Mahler.IntegralPoint m}
    (hsum : x₁ + x₂ = y₁ + y₂) (i : Fin r) :
    phase a b x₁ i + phase a b x₂ i =
      phase a b y₁ i + phase a b y₂ i := by
  have hreal' : integralReal x₁ + integralReal x₂ =
      integralReal y₁ + integralReal y₂ := by
    ext q
    have hq := congrFun hsum q
    change ((x₁ q : ℤ) : ℝ) + ((x₂ q : ℤ) : ℝ) =
      ((y₁ q : ℤ) : ℝ) + ((y₂ q : ℤ) : ℝ)
    exact_mod_cast hq
  dsimp only [phase]
  calc
    ⟪integralReal x₁, a i⟫ - b i +
          (⟪integralReal x₂, a i⟫ - b i) =
        ⟪integralReal x₁ + integralReal x₂, a i⟫ - 2 * b i := by
          rw [inner_add_left]
          ring
    _ = ⟪integralReal y₁ + integralReal y₂, a i⟫ - 2 * b i := by
      rw [hreal']
    _ = ⟪integralReal y₁, a i⟫ - b i +
          (⟪integralReal y₂, a i⟫ - b i) := by
          rw [inner_add_left]
          ring

/-- Forward `F₂` law on one residue cell. -/
theorem freimanMap_add_eq_of_inResidueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2)
    {x₁ x₂ y₁ y₂ : Mahler.IntegralPoint m}
    (hx₁ : InResidueCell a b alpha x₁)
    (hx₂ : InResidueCell a b alpha x₂)
    (hy₁ : InResidueCell a b alpha y₁)
    (hy₂ : InResidueCell a b alpha y₂)
    (hsum : x₁ + x₂ = y₁ + y₂) :
    freimanMap a b x₁ + freimanMap a b x₂ =
      freimanMap a b y₁ + freimanMap a b y₂ := by
  apply Prod.ext
  · exact hsum
  · funext i
    simp only [Prod.snd_add, Pi.add_apply, freimanMap_snd_apply]
    let c : ℝ := ((alpha i : ℕ) : ℝ) / 2
    have hx₁lo : c ≤ Int.fract (phase a b x₁ i) := by
      simpa [c] using (hx₁ i).1
    have hx₁hi : Int.fract (phase a b x₁ i) < c + 1 / 2 := by
      convert (hx₁ i).2 using 1 <;> dsimp [c] <;> ring
    have hx₂lo : c ≤ Int.fract (phase a b x₂ i) := by
      simpa [c] using (hx₂ i).1
    have hx₂hi : Int.fract (phase a b x₂ i) < c + 1 / 2 := by
      convert (hx₂ i).2 using 1 <;> dsimp [c] <;> ring
    have hy₁lo : c ≤ Int.fract (phase a b y₁ i) := by
      simpa [c] using (hy₁ i).1
    have hy₁hi : Int.fract (phase a b y₁ i) < c + 1 / 2 := by
      convert (hy₁ i).2 using 1 <;> dsimp [c] <;> ring
    have hy₂lo : c ≤ Int.fract (phase a b y₂ i) := by
      simpa [c] using (hy₂ i).1
    have hy₂hi : Int.fract (phase a b y₂ i) < c + 1 / 2 := by
      convert (hy₂ i).2 using 1 <;> dsimp [c] <;> ring
    apply floor_add_eq_floor_add_of_common_half
      (c := c) hx₁lo hx₁hi hx₂lo hx₂hi hy₁lo hy₁hi hy₂lo hy₂hi
      (phase_pair_sum_eq a b hsum i)

/-- Reflection of pair-sum equalities is immediate from the retained first
coordinates. -/
theorem add_eq_of_freimanMap_add_eq {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    {x₁ x₂ y₁ y₂ : Mahler.IntegralPoint m}
    (hsum : freimanMap a b x₁ + freimanMap a b x₂ =
      freimanMap a b y₁ + freimanMap a b y₂) :
    x₁ + x₂ = y₁ + y₂ :=
  congrArg Prod.fst hsum

/-- Bilu Proposition 7.1: exact `F₂` equivalence on a common cell. -/
theorem freimanMap_pair_sum_iff {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2)
    {x₁ x₂ y₁ y₂ : Mahler.IntegralPoint m}
    (hx₁ : InResidueCell a b alpha x₁)
    (hx₂ : InResidueCell a b alpha x₂)
    (hy₁ : InResidueCell a b alpha y₁)
    (hy₂ : InResidueCell a b alpha y₂) :
    x₁ + x₂ = y₁ + y₂ ↔
      freimanMap a b x₁ + freimanMap a b x₂ =
        freimanMap a b y₁ + freimanMap a b y₂ :=
  ⟨freimanMap_add_eq_of_inResidueCell a b alpha hx₁ hx₂ hy₁ hy₂,
    add_eq_of_freimanMap_add_eq a b⟩

/-- Proposition 7.1, equation (7.4): on a residue cell the Freiman map
preserves the exact cardinality of the double sumset. -/
theorem card_pairSumset_mappedResidueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m)) :
    (pairSumset (mappedResidueCell a b alpha K)).card =
      (pairSumset (residueCell a b alpha K)).card := by
  let S := residueCell a b alpha K
  let P := S.product S
  have hkernel : ∀ x ∈ P, ∀ y ∈ P,
      x.1 + x.2 = y.1 + y.2 ↔
        freimanMap a b x.1 + freimanMap a b x.2 =
          freimanMap a b y.1 + freimanMap a b y.2 := by
    rintro ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ hy
    dsimp only [P] at hx hy
    have hx' := Finset.mem_product.mp hx
    have hy' := Finset.mem_product.mp hy
    exact freimanMap_pair_sum_iff a b alpha
      (mem_residueCell a b alpha K x₁ |>.mp hx'.1).2
      (mem_residueCell a b alpha K x₂ |>.mp hx'.2).2
      (mem_residueCell a b alpha K y₁ |>.mp hy'.1).2
      (mem_residueCell a b alpha K y₂ |>.mp hy'.2).2
  have hcard := card_image_eq_card_image_of_eq_iff P
    (fun p ↦ p.1 + p.2)
    (fun p ↦ freimanMap a b p.1 + freimanMap a b p.2) hkernel
  have himage :
      P.image (fun p ↦ freimanMap a b p.1 + freimanMap a b p.2) =
        ((S.image (freimanMap a b)).product
          (S.image (freimanMap a b))).image (fun p ↦ p.1 + p.2) := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      have hxy' := Finset.mem_product.mp (show (x, y) ∈ S.product S from hxy)
      exact ⟨(freimanMap a b x, freimanMap a b y),
        Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨x, hxy'.1, rfl⟩,
            Finset.mem_image.mpr ⟨y, hxy'.2, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨u, v⟩, huv, rfl⟩
      have huv' := Finset.mem_product.mp huv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp huv'.1
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp huv'.2
      exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  change
    (((S.image (freimanMap a b)).product
        (S.image (freimanMap a b))).image (fun p ↦ p.1 + p.2)).card =
      ((S.product S).image (fun p ↦ p.1 + p.2)).card
  rw [← himage]
  simpa only [P] using hcard.symm

end

end Erdos186.CFP.Bilu.Section7FreimanMap

#print axioms Erdos186.CFP.Bilu.Section7FreimanMap.freimanMap_pair_sum_iff
