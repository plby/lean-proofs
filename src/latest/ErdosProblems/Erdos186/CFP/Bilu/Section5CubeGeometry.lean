/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5TwoN

/-!
# Finite geometry of Bilu's affine cubes

This file isolates equation (5.13) in Bilu's proof of Freiman's `2n`
theorem.  For a full-dimensional affine cube, all sums of an interior point
and a cube vertex are distinct.  Thus a finite set `S₀` in the interior
contributes exactly `2^n * |S₀|` distinct sums.
-/

namespace Erdos186.CFP.Bilu.Section5CubeGeometry

open Set Module Submodule

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The `{-1,1}` vector indexed by a binary sign pattern. -/
def signVector {n : ℕ} (s : Fin n → Fin 2) : Fin n → ℝ :=
  fun i ↦ if s i = 0 then -1 else 1

/-- The vertices of a full-dimensional affine cube described by a linear
coordinate equivalence and a center. -/
def affineCubeVertex {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (s : Fin n → Fin 2) : V :=
  center + e (signVector s)

/-- The open interior of the corresponding affine cube. -/
def affineCubeInterior {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) : Set V :=
  {x | ∀ i, -(1 : ℝ) < e.symm (x - center) i ∧
    e.symm (x - center) i < 1}

/-- The finite set of sums between `S₀` and all indexed cube vertices. -/
def affineCubeSumFinset {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    (S₀ : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) : Finset V := by
  classical
  exact (S₀.product (Finset.univ : Finset (Fin n → Fin 2))).image
    fun p ↦ p.1 + affineCubeVertex e center p.2

/-- Coordinate form of Bilu's observation: an equality between two
interior-point-plus-vertex sums forces the binary sign patterns to agree. -/
theorem sign_eq_of_add_affineCubeVertex_eq
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center x y : V)
    (hx : x ∈ affineCubeInterior e center)
    (hy : y ∈ affineCubeInterior e center)
    (s t : Fin n → Fin 2)
    (h : x + affineCubeVertex e center s =
      y + affineCubeVertex e center t) :
    s = t := by
  have htranslated :
      (x - center) + e (signVector s) =
        (y - center) + e (signVector t) := by
    dsimp [affineCubeVertex] at h
    have hnormalized :
        center + (x + e (signVector s)) =
          center + (y + e (signVector t)) := by
      simpa [add_assoc, add_left_comm, add_comm] using h
    have hcancel : x + e (signVector s) =
        y + e (signVector t) := add_left_cancel hnormalized
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun z ↦ z - center) hcancel
  have hcoordinates := congrArg e.symm htranslated
  simp only [map_add, LinearEquiv.symm_apply_apply] at hcoordinates
  funext i
  have hi := congrFun hcoordinates i
  change e.symm (x - center) i +
      (if s i = 0 then -1 else 1) =
    e.symm (y - center) i +
      (if t i = 0 then -1 else 1) at hi
  have hxi := hx i
  have hyi := hy i
  by_cases hs : s i = 0
  · by_cases ht : t i = 0
    · exact hs.trans ht.symm
    · rw [if_pos hs, if_neg ht] at hi
      linarith
  · by_cases ht : t i = 0
    · rw [if_neg hs, if_pos ht] at hi
      linarith
    · rw [Fin.eq_one_of_ne_zero (s i) hs,
        Fin.eq_one_of_ne_zero (t i) ht]

/-- The indexed addition map is injective on interior points times sign
patterns. -/
theorem affineCube_add_vertex_injOn
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq V]
    (S₀ : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hS₀ : ∀ x ∈ S₀, x ∈ affineCubeInterior e center) :
    Set.InjOn
      (fun p : V × (Fin n → Fin 2) ↦
        p.1 + affineCubeVertex e center p.2)
      (S₀.product (Finset.univ : Finset (Fin n → Fin 2)) :
        Set (V × (Fin n → Fin 2))) := by
  rintro ⟨x, s⟩ hxs ⟨y, t⟩ hyt hsum
  have hxs' := Finset.mem_product.mp hxs
  have hyt' := Finset.mem_product.mp hyt
  have hst : s = t := sign_eq_of_add_affineCubeVertex_eq
    e center x y (hS₀ x hxs'.1) (hS₀ y hyt'.1) s t hsum
  subst t
  have hxy : x = y := add_right_cancel hsum
  subst y
  rfl

/-- Equation (5.13): an interior set and all cube vertices give exactly
`2^n |S₀|` distinct sums. -/
theorem card_affineCubeSumFinset
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq V]
    (S₀ : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hS₀ : ∀ x ∈ S₀, x ∈ affineCubeInterior e center) :
    (affineCubeSumFinset S₀ e center).card = S₀.card * 2 ^ n := by
  classical
  rw [affineCubeSumFinset,
    Finset.card_image_of_injOn
      (affineCube_add_vertex_injOn S₀ e center hS₀)]
  simp

/-- If all indexed cube vertices and all interior points belong to `S`,
equation (5.13) gives a lower bound for the full double sumset. -/
theorem card_mul_two_pow_le_pairSumset
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq V]
    (S S₀ : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hS₀S : S₀ ⊆ S)
    (hS₀ : ∀ x ∈ S₀, x ∈ affineCubeInterior e center)
    (hvertices : ∀ s : Fin n → Fin 2,
      affineCubeVertex e center s ∈ S) :
    S₀.card * 2 ^ n ≤ (Section7FreimanMap.pairSumset S).card := by
  classical
  have hsubset : affineCubeSumFinset S₀ e center ⊆
      Section7FreimanMap.pairSumset S := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hp' := Finset.mem_product.mp hp
    exact Section7FreimanMap.mem_pairSumset S _ |>.mpr
      ⟨p.1, hS₀S hp'.1, affineCubeVertex e center p.2,
        hvertices p.2, rfl⟩
  rw [← card_affineCubeSumFinset S₀ e center hS₀]
  exact Finset.card_le_card hsubset

/-! ## The `2n` face hyperplanes -/

/-- The linear functional extracting one cube coordinate. -/
def cubeCoordinateLinear {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (i : Fin n) : V →ₗ[ℝ] ℝ :=
  (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ).comp e.symm.toLinearMap

/-- A coordinate vector supported at one index. -/
def singleCoordinate {n : ℕ} (i : Fin n) (c : ℝ) : Fin n → ℝ :=
  fun j ↦ if j = i then c else 0

/-- One affine face hyperplane of the cube. -/
def affineCubeFacePlane {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (i : Fin n) (c : ℝ) : AffineSubspace ℝ V :=
  AffineSubspace.mk'
    (center + e (singleCoordinate i c))
    (LinearMap.ker (cubeCoordinateLinear e i))

/-- Membership in a face plane is exactly equality of the corresponding
affine cube coordinate. -/
@[simp]
theorem mem_affineCubeFacePlane_iff
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center x : V)
    (i : Fin n) (c : ℝ) :
    x ∈ affineCubeFacePlane e center i c ↔
      e.symm (x - center) i = c := by
  rw [affineCubeFacePlane, AffineSubspace.mem_mk', LinearMap.mem_ker]
  rw [cubeCoordinateLinear]
  change e.symm (x - (center + e (singleCoordinate i c))) i = 0 ↔ _
  have hcoord : singleCoordinate i c i = c := by simp [singleCoordinate]
  rw [show x - (center + e (singleCoordinate i c)) =
      (x - center) - e (singleCoordinate i c) by abel,
    map_sub, LinearEquiv.symm_apply_apply, Pi.sub_apply, hcoord]
  exact sub_eq_zero

/-- Every face plane is proper: its direction has dimension strictly below
the cube dimension. -/
theorem finrank_direction_affineCubeFacePlane_lt
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (i : Fin n) (c : ℝ) :
    finrank ℝ (affineCubeFacePlane e center i c).direction < n := by
  have hfunctional : cubeCoordinateLinear e i ≠ 0 := by
    intro hzero
    have happly := LinearMap.congr_fun hzero (e (singleCoordinate i 1))
    simp [cubeCoordinateLinear, singleCoordinate] at happly
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hfunctional
  have hefinrank : finrank ℝ V = n := by
    rw [← e.finrank_eq]
    simp
  have hdirection :
      (affineCubeFacePlane e center i c).direction =
        LinearMap.ker (cubeCoordinateLinear e i) := by
    simp [affineCubeFacePlane]
  rw [hdirection]
  rw [hefinrank] at hker
  omega

/-- The closed affine cube. -/
def affineCubeClosed {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) : Set V :=
  {x | ∀ i, -(1 : ℝ) ≤ e.symm (x - center) i ∧
    e.symm (x - center) i ≤ 1}

/-- Every point of the closed cube outside its interior belongs to one of
the `2n` face hyperplanes. -/
theorem exists_face_of_mem_closed_not_mem_interior
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center x : V)
    (hclosed : x ∈ affineCubeClosed e center)
    (hnotInterior : x ∉ affineCubeInterior e center) :
    ∃ i : Fin n, x ∈ affineCubeFacePlane e center i (-1) ∨
      x ∈ affineCubeFacePlane e center i 1 := by
  simp only [affineCubeInterior, Set.mem_setOf_eq, not_forall] at hnotInterior
  obtain ⟨i, hi⟩ := hnotInterior
  refine ⟨i, ?_⟩
  have hb := hclosed i
  rw [mem_affineCubeFacePlane_iff, mem_affineCubeFacePlane_iff]
  rcases not_and_or.mp hi with hleft | hright
  · exact Or.inl (le_antisymm (not_lt.mp hleft) hb.1)
  · exact Or.inr (le_antisymm hb.2 (not_lt.mp hright))

/-- The points of a finite set on the boundary of a closed affine cube. -/
def affineCubeBoundaryPart {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) : Finset V :=
  S.filter fun x ↦ x ∈ affineCubeClosed e center ∧
    x ∉ affineCubeInterior e center

/-- The points of a finite set in the closed cube. -/
def affineCubeClosedPart {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) : Finset V :=
  S.filter fun x ↦ x ∈ affineCubeClosed e center

/-- The points of a finite set in the open cube. -/
def affineCubeInteriorPart {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) : Finset V :=
  S.filter fun x ↦ x ∈ affineCubeInterior e center

/-- The closed cube points split into interior and boundary points. -/
theorem affineCubeClosedPart_eq_union
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) :
    affineCubeClosedPart S e center =
      affineCubeInteriorPart S e center ∪
        affineCubeBoundaryPart S e center := by
  ext x
  simp only [affineCubeClosedPart, affineCubeInteriorPart,
    affineCubeBoundaryPart, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hxS, hxclosed⟩
    by_cases hxint : x ∈ affineCubeInterior e center
    · exact Or.inl ⟨hxS, hxint⟩
    · exact Or.inr ⟨hxS, hxclosed, hxint⟩
  · rintro (⟨hxS, hxint⟩ | ⟨hxS, hxclosed, _hxnot⟩)
    · refine ⟨hxS, ?_⟩
      intro i
      have hi := hxint i
      exact ⟨hi.1.le, hi.2.le⟩
    · exact ⟨hxS, hxclosed⟩

/-- Cardinal form of the interior/boundary decomposition. -/
theorem card_affineCubeClosedPart_le
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) :
    (affineCubeClosedPart S e center).card ≤
      (affineCubeInteriorPart S e center).card +
        (affineCubeBoundaryPart S e center).card := by
  rw [affineCubeClosedPart_eq_union]
  exact Finset.card_union_le _ _

/-- The points of `S` lying on one prescribed face plane. -/
def affineCubeFacePart {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (p : Fin n × Fin 2) : Finset V :=
  S.filter fun x ↦ x ∈ affineCubeFacePlane e center p.1
    (if p.2 = 0 then -1 else 1)

/-- The cube boundary is covered by its `2n` face parts. -/
theorem affineCubeBoundaryPart_subset_biUnion_faces
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V) :
    affineCubeBoundaryPart S e center ⊆
      (Finset.univ : Finset (Fin n × Fin 2)).biUnion
        (affineCubeFacePart S e center) := by
  classical
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  obtain ⟨i, hminus | hplus⟩ :=
    exists_face_of_mem_closed_not_mem_interior e center x hx'.2.1 hx'.2.2
  · apply Finset.mem_biUnion.mpr
    refine ⟨(i, 0), Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hx'.1, by simpa using hminus⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨(i, 1), Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hx'.1, by simpa using hplus⟩

/-- The source estimate that at most `2n * hyperplaneBound` points can lie
on the boundary, provided every proper affine plane contains at most
`hyperplaneBound` points of `S`. -/
theorem card_affineCubeBoundaryPart_le
    {n hyperplaneBound : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hplane : ∀ plane : AffineSubspace ℝ V,
      finrank ℝ plane.direction < n →
        (S.filter fun x ↦ x ∈ plane).card ≤ hyperplaneBound) :
    (affineCubeBoundaryPart S e center).card ≤
      2 * n * hyperplaneBound := by
  classical
  have hface : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin 2)),
      (affineCubeFacePart S e center p).card ≤ hyperplaneBound := by
    intro p _hp
    exact hplane _
      (finrank_direction_affineCubeFacePlane_lt e center p.1
        (if p.2 = 0 then -1 else 1))
  calc
    (affineCubeBoundaryPart S e center).card ≤
        ((Finset.univ : Finset (Fin n × Fin 2)).biUnion
          (affineCubeFacePart S e center)).card :=
      Finset.card_le_card
        (affineCubeBoundaryPart_subset_biUnion_faces S e center)
    _ ≤ (Finset.univ : Finset (Fin n × Fin 2)).card * hyperplaneBound :=
      Finset.card_biUnion_le_card_mul _ _ _ hface
    _ = 2 * n * hyperplaneBound := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- Combined form of (5.10): a lower bound for the number of closed-cube
points and a hyperplane-sparsity bound force many points into the interior. -/
theorem closedCard_le_interiorCard_add_boundaryBound
    {n hyperplaneBound closedCard : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [DecidableEq V]
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (hclosed : closedCard ≤ (affineCubeClosedPart S e center).card)
    (hplane : ∀ plane : AffineSubspace ℝ V,
      finrank ℝ plane.direction < n →
        (S.filter fun x ↦ x ∈ plane).card ≤ hyperplaneBound) :
    closedCard ≤
      (affineCubeInteriorPart S e center).card +
        2 * n * hyperplaneBound := by
  exact hclosed.trans (card_affineCubeClosedPart_le S e center) |>.trans
    (Nat.add_le_add_left
      (card_affineCubeBoundaryPart_le S e center hplane) _)

end

end Erdos186.CFP.Bilu.Section5CubeGeometry

#print axioms Erdos186.CFP.Bilu.Section5CubeGeometry.sign_eq_of_add_affineCubeVertex_eq
#print axioms Erdos186.CFP.Bilu.Section5CubeGeometry.card_affineCubeSumFinset
#print axioms Erdos186.CFP.Bilu.Section5CubeGeometry.card_mul_two_pow_le_pairSumset
#print axioms Erdos186.CFP.Bilu.Section5CubeGeometry.finrank_direction_affineCubeFacePlane_lt
#print axioms Erdos186.CFP.Bilu.Section5CubeGeometry.exists_face_of_mem_closed_not_mem_interior
#print axioms Erdos186.CFP.Bilu.Section5CubeGeometry.card_affineCubeBoundaryPart_le
#print axioms Erdos186.CFP.Bilu.Section5CubeGeometry.closedCard_le_interiorCard_add_boundaryBound
