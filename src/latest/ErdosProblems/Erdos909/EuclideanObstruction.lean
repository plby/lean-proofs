/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import ErdosProblems.Erdos909.CuttingUpper
import ErdosProblems.Erdos909.EuclideanGeometry
import ErdosProblems.Erdos909.RationalSkeleton

/-!
# Euclidean obstruction packages for word lengths one and two

This file is the interface between the geometric cutting hierarchy and the
transfinite Anderson--Keisler selector.

For word length one, terminal spheres are zero-spheres, hence finite; their
countable union is a countable dimension obstruction.  For word length two,
each terminal sphere has finite intersection with every affine translate of
the three pattern directions (left-coordinate, right-coordinate, and
diagonal).  Therefore the terminal union has countable intersection with
every pattern plane.
-/

open Set Topology TopologicalSpace

namespace Erdos909.EuclideanObstruction

open CuttingUpper

/-- The Euclidean letter space used in the Anderson--Keisler construction. -/
abbrev LetterSpace (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The binary word space. -/
abbrev BinaryWordSpace (m : ℕ) := LetterSpace m × LetterSpace m

/-- The three directions in which one common letter can occur in a binary
word. -/
inductive BinaryPatternKind
  | left
  | right
  | diagonal

/-- Every affine translate of a binary pattern direction.  The parameter is
the fixed second coordinate for `left`, the fixed first coordinate for
`right`, and the fixed difference `x - y` for `diagonal`. -/
def binaryPatternPlane {m : ℕ} :
    BinaryPatternKind → LetterSpace m → Set (BinaryWordSpace m)
  | .left, c => {z | z.2 = c}
  | .right, c => {z | z.1 = c}
  | .diagonal, c => {z | z.1 - z.2 = c}

/-- Linear parametrizations of the three pattern directions. -/
def binaryPatternLinearMap {m : ℕ} :
    BinaryPatternKind → LetterSpace m →ₗ[ℝ] BinaryWordSpace m
  | .left => LinearMap.inl ℝ (LetterSpace m) (LetterSpace m)
  | .right => LinearMap.inr ℝ (LetterSpace m) (LetterSpace m)
  | .diagonal => (LinearMap.id : LetterSpace m →ₗ[ℝ] LetterSpace m).prod
      LinearMap.id

/-- The linear direction of a binary pattern plane. -/
def binaryPatternDirection {m : ℕ} (kind : BinaryPatternKind) :
    Submodule ℝ (BinaryWordSpace m) :=
  LinearMap.range (binaryPatternLinearMap kind)

/-- A base point for the chosen affine translate of a pattern direction. -/
def binaryPatternBase {m : ℕ} :
    BinaryPatternKind → LetterSpace m → BinaryWordSpace m
  | .left, c => (0, c)
  | .right, c => (c, 0)
  | .diagonal, c => (c, 0)

/-- Pattern planes bundled as affine subspaces. -/
noncomputable def binaryPatternAffineSubspace {m : ℕ}
    (kind : BinaryPatternKind) (c : LetterSpace m) :
    AffineSubspace ℝ (BinaryWordSpace m) :=
  AffineSubspace.mk' (binaryPatternBase kind c)
    (binaryPatternDirection kind)

theorem binaryPatternLinearMap_injective {m : ℕ}
    (kind : BinaryPatternKind) :
    Function.Injective (binaryPatternLinearMap (m := m) kind) := by
  cases kind <;> intro x y h
  · exact congr_arg Prod.fst h
  · exact congr_arg Prod.snd h
  · exact congr_arg Prod.fst h

/-- Every pattern direction has the dimension of one letter. -/
theorem finrank_binaryPatternDirection {m : ℕ}
    (kind : BinaryPatternKind) :
    Module.finrank ℝ (binaryPatternDirection (m := m) kind) = m := by
  rw [binaryPatternDirection,
    LinearMap.finrank_range_of_inj (binaryPatternLinearMap_injective kind)]
  exact finrank_euclideanSpace_fin

@[simp]
theorem direction_binaryPatternAffineSubspace {m : ℕ}
    (kind : BinaryPatternKind) (c : LetterSpace m) :
    (binaryPatternAffineSubspace kind c).direction =
      binaryPatternDirection kind := by
  simp [binaryPatternAffineSubspace]

/-- The bundled affine subspace has the intended elementary set-theoretic
description. -/
theorem coe_binaryPatternAffineSubspace {m : ℕ}
    (kind : BinaryPatternKind) (c : LetterSpace m) :
    (binaryPatternAffineSubspace kind c : Set (BinaryWordSpace m)) =
      binaryPatternPlane kind c := by
  ext z
  cases kind
  · simp [binaryPatternAffineSubspace, binaryPatternBase,
      AffineSubspace.mem_mk', binaryPatternDirection,
      binaryPatternLinearMap, LinearMap.range_inl, vsub_eq_sub,
      binaryPatternPlane, sub_eq_zero]
  · simp [binaryPatternAffineSubspace, binaryPatternBase,
      AffineSubspace.mem_mk', binaryPatternDirection,
      binaryPatternLinearMap, LinearMap.range_inr, vsub_eq_sub,
      binaryPatternPlane, sub_eq_zero]
  · change z ∈ AffineSubspace.mk' (c, 0)
        (LinearMap.range
          ((LinearMap.id : LetterSpace m →ₗ[ℝ] LetterSpace m).prod
            LinearMap.id)) ↔ z.1 - z.2 = c
    rw [AffineSubspace.mem_mk']
    change (z - (c, 0)) ∈ LinearMap.range
      ((LinearMap.id : LetterSpace m →ₗ[ℝ] LetterSpace m).prod
        LinearMap.id) ↔ z.1 - z.2 = c
    constructor
    · rintro ⟨x, hx⟩
      have h1 := congr_arg Prod.fst hx
      have h2 := congr_arg Prod.snd hx
      have h1' : x = z.1 - c := by
        simpa only [LinearMap.prod_apply, Function.prod_apply,
          LinearMap.id_apply, Prod.fst_sub] using h1
      have h2' : x = z.2 := by
        simpa only [LinearMap.prod_apply, Function.prod_apply,
          LinearMap.id_apply, Prod.snd_sub, sub_zero] using h2
      have hz' : z.2 = z.1 - c := h2'.symm.trans h1'
      exact sub_eq_iff_eq_add.mpr ((eq_sub_iff_add_eq.mp hz').symm.trans
        (add_comm z.2 c))
    · intro hz
      refine ⟨z.2, ?_⟩
      apply Prod.ext
      · simp only [LinearMap.prod_apply, Function.prod_apply,
          LinearMap.id_apply, Prod.fst_sub]
        exact eq_sub_iff_add_eq.mpr ((add_comm z.2 c).trans
          (sub_eq_iff_eq_add.mp hz).symm)
      · simp only [LinearMap.prod_apply, Function.prod_apply,
          LinearMap.id_apply, Prod.snd_sub, sub_zero]

@[simp]
theorem mem_binaryPatternPlane_left {m : ℕ} {c : LetterSpace m}
    {z : BinaryWordSpace m} :
    z ∈ binaryPatternPlane .left c ↔ z.2 = c :=
  Iff.rfl

@[simp]
theorem mem_binaryPatternPlane_right {m : ℕ} {c : LetterSpace m}
    {z : BinaryWordSpace m} :
    z ∈ binaryPatternPlane .right c ↔ z.1 = c :=
  Iff.rfl

@[simp]
theorem mem_binaryPatternPlane_diagonal {m : ℕ} {c : LetterSpace m}
    {z : BinaryWordSpace m} :
    z ∈ binaryPatternPlane .diagonal c ↔ z.1 - z.2 = c :=
  Iff.rfl

/-- A word-length-one obstruction package.  The name is retained from the
sphere-cut presentation; the rational-coordinate construction below supplies
the same public interface directly. -/
structure UnaryTerminalFamily (m : ℕ) where
  obstruction : Set (LetterSpace m)
  forces : IsSmallInductiveDimensionObstruction obstruction m
  countable : obstruction.Countable

/-- A word-length-two obstruction package with the countable pattern traces
needed by the transfinite selector. -/
structure BinaryTerminalFamily (m : ℕ) where
  obstruction : Set (BinaryWordSpace m)
  forces : IsSmallInductiveDimensionObstruction obstruction m
  countable_pattern_inter : ∀ (kind : BinaryPatternKind) (c : LetterSpace m),
    (binaryPatternPlane kind c ∩ obstruction).Countable

/-- A pair of terminal families containing exactly the upper-dimensional
information needed for Problem 909 at word lengths one and two. -/
structure UnaryBinaryObstructions (m : ℕ) where
  unary : UnaryTerminalFamily m
  binary : BinaryTerminalFamily m

section RationalCoordinateConstruction

open RationalCoordinateUpper RationalSkeleton

/-- Pull an obstruction back through a homeomorphism. -/
theorem isSmallInductiveDimensionObstruction_preimage_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {R : Set Y} {n : ℕ}
    (hR : IsSmallInductiveDimensionObstruction R n) :
    IsSmallInductiveDimensionObstruction (e ⁻¹' R) n := by
  intro T hT
  have hdis : Disjoint (e '' T) R := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hxT, rfl⟩ hxR
    exact Set.disjoint_left.1 hT hxT hxR
  exact inducing_hasSmallInductiveDimensionLT (e.image T).isInducing
    (hR (e '' T) hdis)

/-- Scalar coordinates of a Euclidean letter. -/
noncomputable def letterCoordinateEquiv (m : ℕ) :
    LetterSpace m ≃ₗ[ℝ] (Fin m → ℝ) :=
  (EuclideanSpace.equiv (Fin m) ℝ).toLinearEquiv

/-- The coordinate equivalence is automatically a homeomorphism in finite
dimension. -/
noncomputable def letterCoordinateHomeomorph (m : ℕ) :
    LetterSpace m ≃ₜ (Fin m → ℝ) :=
  (letterCoordinateEquiv m).toContinuousLinearEquiv.toHomeomorph

/-- The unary rational-coordinate obstruction. -/
def unaryRationalCoordinateObstruction (m : ℕ) : Set (LetterSpace m) :=
  letterCoordinateEquiv m ⁻¹' rationalCoordinatesAtLeast m

theorem rationalCoordinatesAtLeast_fin_countable (m : ℕ) :
    (rationalCoordinatesAtLeast (ι := Fin m) m).Countable := by
  apply countable_preimage_rationalCoordinatesAtLeast m
    (fun x : Fin m → ℝ ↦ x)
  intro I hI
  have hIuniv : I = Finset.univ :=
    I.card_eq_iff_eq_univ.mp (by simpa using hI)
  intro x y hxy
  funext i
  let ii : I := ⟨i, by simp [hIuniv]⟩
  exact congrFun hxy ii

theorem unaryRationalCoordinateObstruction_countable (m : ℕ) :
    (unaryRationalCoordinateObstruction m).Countable :=
  (rationalCoordinatesAtLeast_fin_countable m).preimage
    (letterCoordinateEquiv m).injective

theorem unaryRationalCoordinateObstruction_forces (m : ℕ) (hm : 0 < m) :
    IsSmallInductiveDimensionObstruction
      (unaryRationalCoordinateObstruction m) m := by
  exact isSmallInductiveDimensionObstruction_preimage_homeomorph
    (letterCoordinateHomeomorph m)
    (rationalCoordinatesAtLeast_isSmallInductiveDimensionObstruction m hm)

/-- The binary square Vandermonde coordinate equivalence as a homeomorphism. -/
noncomputable def binaryWordVandermondeCoordinateHomeomorph (m : ℕ) :
    BinaryWordSpace m ≃ₜ (Fin (m + m) → ℝ) :=
  (binaryWordVandermondeCoordinateEquiv m).toContinuousLinearEquiv.toHomeomorph

theorem binaryRationalCoordinateObstruction_forces (m : ℕ) (hm : 0 < m) :
    IsSmallInductiveDimensionObstruction
      (binaryRationalCoordinateObstruction m) m := by
  exact isSmallInductiveDimensionObstruction_preimage_homeomorph
    (binaryWordVandermondeCoordinateHomeomorph m)
    (rationalCoordinatesAtLeast_isSmallInductiveDimensionObstruction m hm)

/-- The coordinate function of a Euclidean letter. -/
noncomputable def letterCoordinates (m : ℕ) (c : LetterSpace m) : Fin m → ℝ :=
  letterCoordinateEquiv m c

@[simp]
theorem euclideanOfFun_letterCoordinates (m : ℕ) (c : LetterSpace m) :
    euclideanOfFun m (letterCoordinates m c) = c := by
  simp [euclideanOfFun, letterCoordinates, letterCoordinateEquiv]

theorem binaryLeftPlane_eq_patternPlane (m : ℕ) (c : LetterSpace m) :
    binaryLeftPlane m (letterCoordinates m c) = binaryPatternPlane .left c := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    simp [binaryLeftWord, binaryPatternPlane]
  · intro hz
    refine ⟨letterCoordinates m z.1, ?_⟩
    apply Prod.ext
    · exact euclideanOfFun_letterCoordinates m z.1
    · change euclideanOfFun m (letterCoordinates m c) = z.2
      rw [euclideanOfFun_letterCoordinates]
      exact hz.symm

theorem binaryRightPlane_eq_patternPlane (m : ℕ) (c : LetterSpace m) :
    binaryRightPlane m (letterCoordinates m c) = binaryPatternPlane .right c := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    simp [binaryRightWord, binaryPatternPlane]
  · intro hz
    refine ⟨letterCoordinates m z.2, ?_⟩
    apply Prod.ext
    · change euclideanOfFun m (letterCoordinates m c) = z.1
      rw [euclideanOfFun_letterCoordinates]
      exact hz.symm
    · exact euclideanOfFun_letterCoordinates m z.2

theorem binaryDiagonalPlane_eq_patternPlane (m : ℕ) (c : LetterSpace m) :
    binaryDiagonalPlane m (letterCoordinates m c) =
      binaryPatternPlane .diagonal c := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    simp [binaryDiagonalWord, binaryPatternPlane, sub_eq_add_neg]
  · intro hz
    refine ⟨letterCoordinates m z.2, ?_⟩
    apply Prod.ext
    · change euclideanOfFun m
          (letterCoordinates m z.2 + letterCoordinates m c) = z.1
      rw [map_add, euclideanOfFun_letterCoordinates,
        euclideanOfFun_letterCoordinates]
      change z.1 - z.2 = c at hz
      exact (add_comm z.2 c).trans (sub_eq_iff_eq_add.mp hz).symm
    · exact euclideanOfFun_letterCoordinates m z.2

theorem binaryRationalCoordinateObstruction_countable_pattern_inter
    (m : ℕ) (kind : BinaryPatternKind) (c : LetterSpace m) :
    (binaryPatternPlane kind c ∩
      binaryRationalCoordinateObstruction m).Countable := by
  cases kind
  · rw [← binaryLeftPlane_eq_patternPlane]
    exact countable_binaryLeftPlane_inter_obstruction m (letterCoordinates m c)
  · rw [← binaryRightPlane_eq_patternPlane]
    exact countable_binaryRightPlane_inter_obstruction m (letterCoordinates m c)
  · rw [← binaryDiagonalPlane_eq_patternPlane]
    exact countable_binaryDiagonalPlane_inter_obstruction m (letterCoordinates m c)

/-- The explicit unary and binary obstruction packages obtained from
rational coordinate skeletons and a square Vandermonde coordinate change. -/
noncomputable def rationalUnaryBinaryObstructions (m : ℕ) (hm : 0 < m) :
    UnaryBinaryObstructions m where
  unary :=
    { obstruction := unaryRationalCoordinateObstruction m
      forces := unaryRationalCoordinateObstruction_forces m hm
      countable := unaryRationalCoordinateObstruction_countable m }
  binary :=
    { obstruction := binaryRationalCoordinateObstruction m
      forces := binaryRationalCoordinateObstruction_forces m hm
      countable_pattern_inter :=
        binaryRationalCoordinateObstruction_countable_pattern_inter m }

/-- Concrete existence endpoint used by the Anderson--Keisler assembly. -/
theorem exists_unaryBinaryObstructions (m : ℕ) (hm : 0 < m) :
    Nonempty (UnaryBinaryObstructions m) :=
  ⟨rationalUnaryBinaryObstructions m hm⟩

end RationalCoordinateConstruction

end Erdos909.EuclideanObstruction
