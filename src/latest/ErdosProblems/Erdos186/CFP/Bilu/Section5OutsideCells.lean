/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5CubeLemma

/-!
# Outside cells in Bilu's proof of the `2n` theorem

The complement of a full-dimensional closed affine cube is split into the
`3^n - 1` coordinate cells used in Section 5.  This file proves the key
separation facts: distinct cells have disjoint self-sumsets, and every
outside-cell self-sumset is disjoint from the sums of an interior point and
a cube vertex.
-/

namespace Erdos186.CFP.Bilu.Section5OutsideCells

open Set Module Submodule
open Section7FreimanMap Section5CubeGeometry Section5CubeLemma

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

/-- The three coordinate regions `(-∞,-1]`, `(-1,1)`, `[1,∞)`. -/
def coordinateCell (u : ℝ) : Fin 3 :=
  if u ≤ -1 then 0 else if u < 1 then 1 else 2

@[simp] theorem coordinateCell_eq_zero_iff (u : ℝ) :
    coordinateCell u = 0 ↔ u ≤ -1 := by
  simp only [coordinateCell]
  by_cases hlow : u ≤ -1
  · simp [hlow]
  · by_cases hhigh : u < 1 <;> simp [hlow, hhigh]

@[simp] theorem coordinateCell_eq_one_iff (u : ℝ) :
    coordinateCell u = 1 ↔ -1 < u ∧ u < 1 := by
  simp only [coordinateCell]
  by_cases hlow : u ≤ -1
  · simp [hlow]
  · by_cases hhigh : u < 1
    · simp [hlow, hhigh, lt_of_not_ge hlow]
    · simp [hlow, hhigh]

@[simp] theorem coordinateCell_eq_two_iff (u : ℝ) :
    coordinateCell u = 2 ↔ 1 ≤ u := by
  simp only [coordinateCell]
  by_cases hlow : u ≤ -1
  · simp [hlow]
    linarith
  · by_cases hhigh : u < 1
    · simp [hlow, hhigh]
    · simp [hlow, hhigh, not_lt.mp hhigh]

/-- The `{- ,0,+}` cell index of a point in affine cube coordinates. -/
def cubeCellIndex {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] V)
    (center x : V) : Fin n → Fin 3 :=
  fun i ↦ coordinateCell (e.symm (x - center) i)

/-- The central index, corresponding to the open cube. -/
def middleCellIndex (n : ℕ) : Fin n → Fin 3 := fun _ ↦ 1

/-- Points of `S` in one of the `3^n` coordinate cells. -/
def cubeCell {n : ℕ} (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V)
    (center : V) (alpha : Fin n → Fin 3) : Finset V :=
  S.filter fun x ↦ cubeCellIndex e center x = alpha

@[simp] theorem mem_cubeCell {n : ℕ} {S : Finset V}
    {e : (Fin n → ℝ) ≃ₗ[ℝ] V} {center : V}
    {alpha : Fin n → Fin 3} {x : V} :
    x ∈ cubeCell S e center alpha ↔
      x ∈ S ∧ cubeCellIndex e center x = alpha := by
  simp [cubeCell]

/-- The middle cell is exactly the open-cube part. -/
theorem cubeCell_middle_eq_interiorPart {n : ℕ} (S : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) :
    cubeCell S e center (middleCellIndex n) =
      affineCubeInteriorPart S e center := by
  ext x
  simp only [mem_cubeCell, affineCubeInteriorPart, Finset.mem_filter,
    affineCubeInterior, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxS, hxindex⟩
    refine ⟨hxS, ?_⟩
    intro i
    have hi := congrFun hxindex i
    exact (coordinateCell_eq_one_iff _).mp (by simpa [cubeCellIndex,
      middleCellIndex] using hi)
  · rintro ⟨hxS, hxinterior⟩
    refine ⟨hxS, ?_⟩
    funext i
    exact (coordinateCell_eq_one_iff _).mpr (hxinterior i)

/-- Equality of two vector sums forces equality of the corresponding sums
of affine cube coordinates. -/
theorem cubeCoordinate_add_eq {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center x₁ x₂ y₁ y₂ : V)
    (h : x₁ + x₂ = y₁ + y₂) (i : Fin n) :
    e.symm (x₁ - center) i + e.symm (x₂ - center) i =
      e.symm (y₁ - center) i + e.symm (y₂ - center) i := by
  have h' := congrArg (fun z ↦ e.symm z i) h
  simp only [map_add, Pi.add_apply] at h'
  simp only [map_sub, Pi.sub_apply]
  linarith

/-- The double intervals belonging to two distinct coordinate regions are
disjoint. -/
theorem coordinate_pair_sum_ne_of_cell_ne
    {u₁ u₂ v₁ v₂ : ℝ} {a b : Fin 3}
    (hu₁ : coordinateCell u₁ = a) (hu₂ : coordinateCell u₂ = a)
    (hv₁ : coordinateCell v₁ = b) (hv₂ : coordinateCell v₂ = b)
    (hab : a ≠ b) : u₁ + u₂ ≠ v₁ + v₂ := by
  intro hsum
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals simp_all only [coordinateCell_eq_zero_iff,
    coordinateCell_eq_one_iff, coordinateCell_eq_two_iff]
  all_goals try { exact (hab rfl).elim }
  all_goals linarith

/-- Two pairs of points from different coordinate cells cannot have the
same sum. -/
theorem add_ne_of_cubeCellIndex_ne {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center x₁ x₂ y₁ y₂ : V)
    {alpha beta : Fin n → Fin 3}
    (hx₁ : cubeCellIndex e center x₁ = alpha)
    (hx₂ : cubeCellIndex e center x₂ = alpha)
    (hy₁ : cubeCellIndex e center y₁ = beta)
    (hy₂ : cubeCellIndex e center y₂ = beta)
    (hab : alpha ≠ beta) :
    x₁ + x₂ ≠ y₁ + y₂ := by
  intro hsum
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  have hcoord := cubeCoordinate_add_eq e center x₁ x₂ y₁ y₂ hsum i
  have hx₁i := congrFun hx₁ i
  have hx₂i := congrFun hx₂ i
  have hy₁i := congrFun hy₁ i
  have hy₂i := congrFun hy₂ i
  have ha : coordinateCell (e.symm (x₁ - center) i) = alpha i := by
    simpa [cubeCellIndex] using hx₁i
  have ha₂ : coordinateCell (e.symm (x₂ - center) i) = alpha i := by
    simpa [cubeCellIndex] using hx₂i
  have hb : coordinateCell (e.symm (y₁ - center) i) = beta i := by
    simpa [cubeCellIndex] using hy₁i
  have hb₂ : coordinateCell (e.symm (y₂ - center) i) = beta i := by
    simpa [cubeCellIndex] using hy₂i
  exact coordinate_pair_sum_ne_of_cell_ne ha ha₂ hb hb₂ hi hcoord

/-- Self-sumsets of distinct coordinate cells are disjoint. -/
theorem pairSumset_cubeCell_disjoint {n : ℕ} (S : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    {alpha beta : Fin n → Fin 3} (hab : alpha ≠ beta) :
    Disjoint (pairSumset (cubeCell S e center alpha))
      (pairSumset (cubeCell S e center beta)) := by
  rw [Finset.disjoint_left]
  intro z hzAlpha hzBeta
  obtain ⟨x₁, hx₁, x₂, hx₂, hxsum⟩ :=
    mem_pairSumset (cubeCell S e center alpha) z |>.mp hzAlpha
  obtain ⟨y₁, hy₁, y₂, hy₂, hysum⟩ :=
    mem_pairSumset (cubeCell S e center beta) z |>.mp hzBeta
  have hne := add_ne_of_cubeCellIndex_ne e center x₁ x₂ y₁ y₂
    (mem_cubeCell.mp hx₁).2 (mem_cubeCell.mp hx₂).2
    (mem_cubeCell.mp hy₁).2 (mem_cubeCell.mp hy₂).2 hab
  exact hne (hxsum.trans hysum.symm)

/-- An outside-cell self-sum cannot equal the sum of an interior point and
a cube vertex. -/
theorem add_ne_of_outsideCell_and_interior_vertex {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center x₁ x₂ y : V)
    (s : Fin n → Fin 2) {alpha : Fin n → Fin 3}
    (hx₁ : cubeCellIndex e center x₁ = alpha)
    (hx₂ : cubeCellIndex e center x₂ = alpha)
    (halpha : alpha ≠ middleCellIndex n)
    (hy : y ∈ affineCubeInterior e center) :
    x₁ + x₂ ≠ y + affineCubeVertex e center s := by
  intro hsum
  obtain ⟨i, hi⟩ := Function.ne_iff.mp halpha
  have hai : alpha i ≠ 1 := by
    intro hai
    exact hi (by simpa [middleCellIndex] using hai)
  have hcoord := cubeCoordinate_add_eq e center x₁ x₂ y
    (affineCubeVertex e center s) hsum i
  have hx₁i :
      coordinateCell (e.symm (x₁ - center) i) = alpha i := by
    simpa [cubeCellIndex] using congrFun hx₁ i
  have hx₂i :
      coordinateCell (e.symm (x₂ - center) i) = alpha i := by
    simpa [cubeCellIndex] using congrFun hx₂ i
  have hvertex :
      e.symm (affineCubeVertex e center s - center) i =
        signVector s i := by
    simp [affineCubeVertex]
  have hsignBounds : -(1 : ℝ) ≤ signVector s i ∧ signVector s i ≤ 1 := by
    by_cases hs : s i = 0 <;> simp [signVector, hs]
  have hyi := hy i
  have ha : alpha i = 0 ∨ alpha i = 1 ∨ alpha i = 2 := by omega
  rcases ha with ha | ha | ha
  · have hlow₁ := (coordinateCell_eq_zero_iff _).mp (hx₁i.trans ha)
    have hlow₂ := (coordinateCell_eq_zero_iff _).mp (hx₂i.trans ha)
    rw [hvertex] at hcoord
    linarith
  · exact (hai ha).elim
  · have hhigh₁ := (coordinateCell_eq_two_iff _).mp (hx₁i.trans ha)
    have hhigh₂ := (coordinateCell_eq_two_iff _).mp (hx₂i.trans ha)
    rw [hvertex] at hcoord
    linarith

/-- The affine-cube sumset from equation (5.13) is disjoint from every
outside-cell self-sumset. -/
theorem affineCubeSumFinset_disjoint_pairSumset_cubeCell {n : ℕ}
    (S S₀ : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hS₀ : ∀ x ∈ S₀, x ∈ affineCubeInterior e center)
    {alpha : Fin n → Fin 3} (halpha : alpha ≠ middleCellIndex n) :
    Disjoint (affineCubeSumFinset S₀ e center)
      (pairSumset (cubeCell S e center alpha)) := by
  rw [Finset.disjoint_left]
  intro z hzCube hzCell
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hzCube
  have hp' := Finset.mem_product.mp hp
  obtain ⟨x₁, hx₁, x₂, hx₂, hxz⟩ :=
    mem_pairSumset (cubeCell S e center alpha) z |>.mp hzCell
  have hne := add_ne_of_outsideCell_and_interior_vertex e center x₁ x₂
    p.1 p.2 (mem_cubeCell.mp hx₁).2 (mem_cubeCell.mp hx₂).2
    halpha (hS₀ p.1 hp'.1)
  exact hne (hxz.trans hpz.symm)

/-! ## The disjoint-union cardinal inequality -/

/-- The `3^n - 1` noncentral cell indices. -/
def outsideCellIndices (n : ℕ) : Finset (Fin n → Fin 3) :=
  Finset.univ.erase (middleCellIndex n)

@[simp] theorem card_outsideCellIndices (n : ℕ) :
    (outsideCellIndices n).card = 3 ^ n - 1 := by
  simp [outsideCellIndices]

/-- The cell fibers partition `S`. -/
theorem sum_card_cubeCell {n : ℕ} (S : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) :
    ∑ alpha : Fin n → Fin 3, (cubeCell S e center alpha).card = S.card := by
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (f := cubeCellIndex e center) (s := S)
    (t := (Finset.univ : Finset (Fin n → Fin 3))) (by simp)
  simpa [cubeCell] using hpartition.symm

/-- The open cube together with all outside cells accounts for all
points of `S`. -/
theorem card_interiorPart_add_sum_outsideCells {n : ℕ} (S : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) :
    (affineCubeInteriorPart S e center).card +
        ∑ alpha ∈ outsideCellIndices n, (cubeCell S e center alpha).card =
      S.card := by
  have hsum := sum_card_cubeCell S e center
  have hmem : middleCellIndex n ∈
      (Finset.univ : Finset (Fin n → Fin 3)) := Finset.mem_univ _
  have herase := Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin n → Fin 3)))
    (f := fun alpha ↦ (cubeCell S e center alpha).card) hmem
  rw [← hsum]
  rw [← herase]
  rw [cubeCell_middle_eq_interiorPart]
  simp only [outsideCellIndices]
  omega

/-- Union of the self-sumsets of all outside cells. -/
def outsidePairSumUnion {n : ℕ} (S : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) : Finset V :=
  (outsideCellIndices n).biUnion fun alpha ↦
    pairSumset (cubeCell S e center alpha)

/-- The outside self-sumsets form a genuinely disjoint union. -/
theorem card_outsidePairSumUnion {n : ℕ} (S : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) :
    (outsidePairSumUnion S e center).card =
      ∑ alpha ∈ outsideCellIndices n,
        (pairSumset (cubeCell S e center alpha)).card := by
  apply Finset.card_biUnion
  intro alpha halpha beta hbeta hab
  exact pairSumset_cubeCell_disjoint S e center hab

/-- The complete disjoint family of sums used in Bilu's induction. -/
def cubeAndOutsideSumUnion {n : ℕ} (S S₀ : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) : Finset V :=
  affineCubeSumFinset S₀ e center ∪ outsidePairSumUnion S e center

/-- Exact cardinality of the complete disjoint family. -/
theorem card_cubeAndOutsideSumUnion {n : ℕ} (S S₀ : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hS₀ : ∀ x ∈ S₀, x ∈ affineCubeInterior e center) :
    (cubeAndOutsideSumUnion S S₀ e center).card =
      S₀.card * 2 ^ n +
        ∑ alpha ∈ outsideCellIndices n,
          (pairSumset (cubeCell S e center alpha)).card := by
  rw [cubeAndOutsideSumUnion,
    Finset.card_union_of_disjoint, card_affineCubeSumFinset S₀ e center hS₀,
    card_outsidePairSumUnion]
  rw [outsidePairSumUnion, Finset.disjoint_biUnion_right]
  intro alpha halpha
  exact affineCubeSumFinset_disjoint_pairSumset_cubeCell S S₀ e center
    hS₀ (Finset.ne_of_mem_erase halpha)

/-- Every sum in the disjoint family is a sum of two points of `S`. -/
theorem cubeAndOutsideSumUnion_subset_pairSumset {n : ℕ} (S S₀ : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hS₀S : S₀ ⊆ S)
    (hvertices : ∀ s : Fin n → Fin 2, affineCubeVertex e center s ∈ S) :
    cubeAndOutsideSumUnion S S₀ e center ⊆ pairSumset S := by
  intro z hz
  rcases Finset.mem_union.mp hz with hzCube | hzOutside
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hzCube
    have hp' := Finset.mem_product.mp hp
    exact mem_pairSumset S _ |>.mpr
      ⟨p.1, hS₀S hp'.1, affineCubeVertex e center p.2,
        hvertices p.2, rfl⟩
  · obtain ⟨alpha, _halpha, hzAlpha⟩ :=
      Finset.mem_biUnion.mp hzOutside
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      mem_pairSumset (cubeCell S e center alpha) z |>.mp hzAlpha
    exact mem_pairSumset S _ |>.mpr
      ⟨x, (mem_cubeCell.mp hx).1, y, (mem_cubeCell.mp hy).1, rfl⟩

/-- Master outside-cell inequality: equation (5.13) and all outside-cell
self-sumsets inject disjointly into `S+S`. -/
theorem interior_and_outside_pairSum_card_le {n : ℕ} (S S₀ : Finset V)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hS₀S : S₀ ⊆ S)
    (hS₀ : ∀ x ∈ S₀, x ∈ affineCubeInterior e center)
    (hvertices : ∀ s : Fin n → Fin 2, affineCubeVertex e center s ∈ S) :
    S₀.card * 2 ^ n +
        ∑ alpha ∈ outsideCellIndices n,
          (pairSumset (cubeCell S e center alpha)).card ≤
      (pairSumset S).card := by
  rw [← card_cubeAndOutsideSumUnion S S₀ e center hS₀]
  exact Finset.card_le_card
    (cubeAndOutsideSumUnion_subset_pairSumset S S₀ e center hS₀S hvertices)

end

end Erdos186.CFP.Bilu.Section5OutsideCells

#print axioms Erdos186.CFP.Bilu.Section5OutsideCells.pairSumset_cubeCell_disjoint
#print axioms Erdos186.CFP.Bilu.Section5OutsideCells.interior_and_outside_pairSum_card_le
