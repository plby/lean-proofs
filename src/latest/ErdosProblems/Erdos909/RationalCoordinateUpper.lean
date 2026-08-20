/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.SmallInductiveDimension

/-!
# The countable-trace part of a rational-coordinate Nöbeling construction

This file records the elementary set-theoretic core of an alternative upper
bound considered for Erdős Problem 909.  In a finite real coordinate space,
let the bad set consist of points having at least `m` rational coordinates.
If the restriction of every choice of `m` coordinates to a parametrized
`m`-plane is injective, then the bad set has countable trace on that plane.

The result is formulated without linear algebra: the MDS (all maximal minors
nonzero) property of the chosen coordinate change is exactly the injectivity
hypothesis below.  This makes the theorem directly usable for coordinate,
diagonal, or other pattern planes once their relevant minors have been
verified.
-/

open Set Topology TopologicalSpace

namespace Erdos909.RationalCoordinateUpper

/-- The copy of the rational numbers inside the reals. -/
def rationalReals : Set ℝ := Set.range ((↑) : ℚ → ℝ)

theorem rationalReals_countable : rationalReals.Countable :=
  Set.countable_range ((↑) : ℚ → ℝ)

/-- Points with at least `m` rational coordinates.  The finite set `I`
explicitly witnesses which coordinates are rational. -/
def rationalCoordinatesAtLeast {ι : Type*} (m : ℕ) : Set (ι → ℝ) :=
  {x | ∃ I : Finset ι, I.card = m ∧ ∀ i ∈ I, x i ∈ rationalReals}

/-- The rational-coordinate Nöbeling set of order `k`: points having fewer
than `k + 1` rational coordinates. -/
def rationalCoordinateNobeling {ι : Type*} (k : ℕ) : Set (ι → ℝ) :=
  (rationalCoordinatesAtLeast (k + 1))ᶜ

/-- For a fixed finite set of coordinates, the set of vectors rational on
all of those coordinates is countable after pullback by an injective
coordinate map. -/
theorem countable_rational_on_finset
    {P ι : Type*} {f : P → ι → ℝ} (I : Finset ι)
    (hinj : Function.Injective (fun p ↦ fun i : I ↦ f p i)) :
    {p | ∀ i ∈ I, f p i ∈ rationalReals}.Countable := by
  have hR : {g : I → ℝ | ∀ i, g i ∈ rationalReals}.Countable :=
    Set.countable_pi fun _ ↦ rationalReals_countable
  have hpre :
      ((fun p ↦ fun i : I ↦ f p i) ⁻¹'
        {g : I → ℝ | ∀ i, g i ∈ rationalReals}).Countable :=
    hR.preimage hinj
  apply hpre.mono
  intro p hp i
  exact hp i i.2

/-- The bad rational-coordinate set has countable trace on any parametrized
plane for which every `m`-coordinate projection is injective.

When `P` is an `m`-dimensional pattern plane and `f` is its inclusion after
an MDS coordinate change, the hypothesis is the statement that every
`m × m` minor of the restricted coordinate matrix is nonsingular. -/
theorem countable_preimage_rationalCoordinatesAtLeast
    {P ι : Type*} [Finite ι] (m : ℕ) (f : P → ι → ℝ)
    (hinj : ∀ I : Finset ι, I.card = m →
      Function.Injective (fun p ↦ fun i : I ↦ f p i)) :
    (f ⁻¹' rationalCoordinatesAtLeast m).Countable := by
  apply (Set.countable_iUnion fun I : {I : Finset ι // I.card = m} ↦
    countable_rational_on_finset I.1 (hinj I.1 I.2)).mono
  intro p hp
  rcases hp with ⟨I, hIcard, hIrat⟩
  rw [Set.mem_iUnion]
  exact ⟨⟨I, hIcard⟩, hIrat⟩

/-- Equivalently, the complement of the Nöbeling set has countable trace on
every parametrized plane satisfying the maximal-minor hypothesis. -/
theorem countable_preimage_compl_rationalCoordinateNobeling
    {P ι : Type*} [Finite ι] (k : ℕ) (f : P → ι → ℝ)
    (hinj : ∀ I : Finset ι, I.card = k + 1 →
      Function.Injective (fun p ↦ fun i : I ↦ f p i)) :
    (f ⁻¹' (rationalCoordinateNobeling k)ᶜ).Countable := by
  simpa only [rationalCoordinateNobeling, compl_compl] using
    countable_preimage_rationalCoordinatesAtLeast (k + 1) f hinj

section VandermondeTrace

/-- Parametrization by evaluation of a polynomial of degree less than `m` at
the specified nodes.  Its coordinate matrices are rectangular Vandermonde
matrices. -/
def vandermondeParam {ι : Type*} (m : ℕ) (t : ι → ℝ) :
    (Fin m → ℝ) → ι → ℝ :=
  fun x i ↦ ∑ j : Fin m, t i ^ (j : ℕ) * x j

/-- The Vandermonde evaluation map as a linear endomorphism when the number
of nodes equals the number of coefficients. -/
def vandermondeLinearMap (N : ℕ) (t : Fin N → ℝ) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun := vandermondeParam N t
  map_add' x y := by
    funext i
    simp only [vandermondeParam, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c x := by
    funext i
    simp only [vandermondeParam, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- Every choice of `m` coordinates of a Vandermonde parametrization is
injective when the nodes are distinct. -/
theorem injective_coordinateProjection_vandermondeParam
    {ι : Type*} (m : ℕ) (t : ι → ℝ) (ht : Function.Injective t)
    (I : Finset ι) (hI : I.card = m) :
    Function.Injective
      (fun x ↦ fun i : I ↦ vandermondeParam m t x i) := by
  classical
  let e : I ≃ Fin m := I.equivFinOfCardEq hI
  let u : Fin m → ℝ := fun j ↦ t (e.symm j)
  have hu : Function.Injective u := ht.comp fun _ _ h ↦
    e.symm.injective (Subtype.ext h)
  intro x y hxy
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hu
  intro j
  calc
    (∑ i : Fin m, u j ^ (i : ℕ) * (x - y) i) =
        vandermondeParam m t x (e.symm j) -
          vandermondeParam m t y (e.symm j) := by
      simp only [vandermondeParam, u, Pi.sub_apply, mul_sub,
        Finset.sum_sub_distrib]
    _ = 0 := sub_eq_zero.mpr (congrFun hxy (e.symm j))

/-- Distinct square Vandermonde nodes give a linear automorphism. -/
noncomputable def vandermondeLinearEquiv (N : ℕ) (t : Fin N → ℝ)
    (ht : Function.Injective t) :
    (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ) :=
  LinearEquiv.ofInjectiveEndo (vandermondeLinearMap N t) <| by
    intro x y hxy
    apply injective_coordinateProjection_vandermondeParam N t ht
      Finset.univ (Finset.card_univ.trans (Fintype.card_fin N))
    funext i
    exact congrFun hxy i

@[simp]
theorem vandermondeLinearEquiv_apply (N : ℕ) (t : Fin N → ℝ)
    (ht : Function.Injective t) (x : Fin N → ℝ) :
    vandermondeLinearEquiv N t ht x = vandermondeParam N t x :=
  rfl

/-- Row-scaled Vandermonde parametrization.  Nonzero row scalars preserve
the full-spark property and cover the right and diagonal pattern planes in
the `2m × 2m` Vandermonde coordinate change. -/
def scaledVandermondeParam {ι : Type*} (m : ℕ) (t c : ι → ℝ) :
    (Fin m → ℝ) → ι → ℝ :=
  fun x i ↦ c i * vandermondeParam m t x i

theorem injective_coordinateProjection_scaledVandermondeParam
    {ι : Type*} (m : ℕ) (t c : ι → ℝ)
    (ht : Function.Injective t) (hc : ∀ i, c i ≠ 0)
    (I : Finset ι) (hI : I.card = m) :
    Function.Injective
      (fun x ↦ fun i : I ↦ scaledVandermondeParam m t c x i) := by
  intro x y hxy
  apply injective_coordinateProjection_vandermondeParam m t ht I hI
  funext i
  exact mul_left_cancel₀ (hc i) (congrFun hxy i)

/-- The points on a Vandermonde pattern plane having at least `m` rational
coordinates form a countable set. -/
theorem countable_vandermondeParam_preimage_rationalCoordinatesAtLeast
    {ι : Type*} [Finite ι] (m : ℕ) (t : ι → ℝ)
    (ht : Function.Injective t) :
    (vandermondeParam m t ⁻¹'
      rationalCoordinatesAtLeast m).Countable := by
  apply countable_preimage_rationalCoordinatesAtLeast
  exact fun I hI ↦
    injective_coordinateProjection_vandermondeParam m t ht I hI

/-- Row scaling by nonzero factors does not affect countability of the bad
rational-coordinate trace. -/
theorem countable_scaledVandermondeParam_preimage_rationalCoordinatesAtLeast
    {ι : Type*} [Finite ι] (m : ℕ) (t c : ι → ℝ)
    (ht : Function.Injective t) (hc : ∀ i, c i ≠ 0) :
    (scaledVandermondeParam m t c ⁻¹'
      rationalCoordinatesAtLeast m).Countable := by
  apply countable_preimage_rationalCoordinatesAtLeast
  exact fun I hI ↦
    injective_coordinateProjection_scaledVandermondeParam m t c ht hc I hI

/-- A positive-dimensional Vandermonde pattern plane meets the complement of
the order-`m-1` Nöbeling set in only countably many points. -/
theorem countable_vandermondeParam_preimage_compl_nobeling
    {ι : Type*} [Finite ι] (m : ℕ) (hm : 0 < m) (t : ι → ℝ)
    (ht : Function.Injective t) :
    (vandermondeParam m t ⁻¹'
      (rationalCoordinateNobeling (ι := ι) (m - 1))ᶜ).Countable := by
  rw [rationalCoordinateNobeling, compl_compl,
    Nat.sub_add_cancel hm]
  exact countable_vandermondeParam_preimage_rationalCoordinatesAtLeast m t ht

/-- Distinct positive nodes used in the explicit `2m × 2m` Vandermonde
coordinate system. -/
def positiveNodes (N : ℕ) : Fin N → ℝ :=
  fun i ↦ (i.1 + 1 : ℕ)

theorem positiveNodes_injective (N : ℕ) :
    Function.Injective (positiveNodes N) := by
  intro i j hij
  apply Fin.ext
  change ((i.1 + 1 : ℕ) : ℝ) = (j.1 + 1 : ℕ) at hij
  have hnat : i.1 + 1 = j.1 + 1 := by
    exact_mod_cast hij
  omega

theorem positiveNodes_pos {N : ℕ} (i : Fin N) :
    0 < positiveNodes N i := by
  change (0 : ℝ) < (i.1 + 1 : ℕ)
  positivity

/-- The three restricted pattern maps obtained from the full Vandermonde
coordinate transform: the left plane, the right plane (row factor `t^m`),
and the diagonal plane (row factor `1 + t^m`).  Each has countable bad
rational-coordinate trace. -/
theorem countable_three_vandermonde_pattern_traces (m : ℕ) :
    (vandermondeParam m (positiveNodes (2 * m)) ⁻¹'
        rationalCoordinatesAtLeast m).Countable ∧
    (scaledVandermondeParam m (positiveNodes (2 * m))
        (fun i ↦ positiveNodes (2 * m) i ^ m) ⁻¹'
        rationalCoordinatesAtLeast m).Countable ∧
    (scaledVandermondeParam m (positiveNodes (2 * m))
        (fun i ↦ 1 + positiveNodes (2 * m) i ^ m) ⁻¹'
        rationalCoordinatesAtLeast m).Countable := by
  have ht := positiveNodes_injective (2 * m)
  refine ⟨countable_vandermondeParam_preimage_rationalCoordinatesAtLeast
    m _ ht, ?_, ?_⟩
  · apply countable_scaledVandermondeParam_preimage_rationalCoordinatesAtLeast
      m _ _ ht
    intro i
    exact pow_ne_zero _ (ne_of_gt (positiveNodes_pos i))
  · apply countable_scaledVandermondeParam_preimage_rationalCoordinatesAtLeast
      m _ _ ht
    intro i
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (pow_nonneg (positiveNodes_pos i).le m))

section BinaryWordCoordinateAutomorphism

/-- The Euclidean binary-word space, definitionally the same type as
`EuclideanObstruction.BinaryWordSpace m` but kept here without an import
cycle to the obstruction package. -/
abbrev RationalBinaryWordSpace (m : ℕ) :=
  EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)

/-- Forget the Euclidean norms and concatenate the two letters into their
`m + m` scalar coefficients. -/
noncomputable def binaryWordCoefficientEquiv (m : ℕ) :
    RationalBinaryWordSpace m ≃ₗ[ℝ] (Fin (m + m) → ℝ) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := m)).symm.toLinearEquiv |>.trans
    (EuclideanSpace.equiv (Fin (m + m)) ℝ).toLinearEquiv

/-- The square Vandermonde coordinate equivalence on binary words. -/
noncomputable def binaryWordVandermondeCoordinateEquiv (m : ℕ) :
    RationalBinaryWordSpace m ≃ₗ[ℝ] (Fin (m + m) → ℝ) :=
  (binaryWordCoefficientEquiv m).trans
    (vandermondeLinearEquiv (m + m) (positiveNodes (m + m))
      (positiveNodes_injective (m + m)))

/-- The same coordinate change as an actual automorphism of the Euclidean
binary-word space.  `binaryWordVandermondeCoordinateEquiv` is its scalar
coordinate readout. -/
noncomputable def binaryWordVandermondeAutomorphism (m : ℕ) :
    RationalBinaryWordSpace m ≃ₗ[ℝ] RationalBinaryWordSpace m :=
  (binaryWordVandermondeCoordinateEquiv m).trans
    (binaryWordCoefficientEquiv m).symm

theorem binaryWordVandermondeCoordinateEquiv_bijective (m : ℕ) :
    Function.Bijective (binaryWordVandermondeCoordinateEquiv m) :=
  (binaryWordVandermondeCoordinateEquiv m).bijective

theorem binaryWordVandermondeAutomorphism_bijective (m : ℕ) :
    Function.Bijective (binaryWordVandermondeAutomorphism m) :=
  (binaryWordVandermondeAutomorphism m).bijective

@[simp]
theorem binaryWordCoefficientEquiv_automorphism_apply (m : ℕ)
    (z : RationalBinaryWordSpace m) :
    binaryWordCoefficientEquiv m (binaryWordVandermondeAutomorphism m z) =
      binaryWordVandermondeCoordinateEquiv m z := by
  simp [binaryWordVandermondeAutomorphism]

/-- Repackage ordinary coordinates as a Euclidean vector. -/
noncomputable def euclideanOfFun (m : ℕ) :
    (Fin m → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).toLinearEquiv.symm

@[simp]
theorem binaryWordCoefficientEquiv_apply_castAdd (m : ℕ)
    (x y : Fin m → ℝ) (i : Fin m) :
    binaryWordCoefficientEquiv m (euclideanOfFun m x, euclideanOfFun m y)
      (Fin.castAdd m i) = x i := by
  simp [binaryWordCoefficientEquiv, euclideanOfFun]

@[simp]
theorem binaryWordCoefficientEquiv_apply_natAdd (m : ℕ)
    (x y : Fin m → ℝ) (i : Fin m) :
    binaryWordCoefficientEquiv m (euclideanOfFun m x, euclideanOfFun m y)
      (Fin.natAdd m i) = y i := by
  simp [binaryWordCoefficientEquiv, euclideanOfFun]
  have hindex : i.addNat m = Fin.natAdd m i := by
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hindex, finSumFinEquiv_symm_apply_natAdd]

/-- Affine parametrizations of the left, right, and fixed-difference diagonal
pattern planes in the Euclidean binary-word space. -/
noncomputable def binaryLeftWord (m : ℕ) (c x : Fin m → ℝ) :
    RationalBinaryWordSpace m :=
  (euclideanOfFun m x, euclideanOfFun m c)

noncomputable def binaryRightWord (m : ℕ) (c y : Fin m → ℝ) :
    RationalBinaryWordSpace m :=
  (euclideanOfFun m c, euclideanOfFun m y)

noncomputable def binaryDiagonalWord (m : ℕ) (c x : Fin m → ℝ) :
    RationalBinaryWordSpace m :=
  (euclideanOfFun m (x + c), euclideanOfFun m x)

/-- Applying the full square coordinate equivalence to a pair of letters is
the consecutive-power formula: degrees `0,…,m-1` for the first letter and
degrees `m,…,2m-1` for the second. -/
theorem binaryWordVandermondeCoordinateEquiv_apply_pair (m : ℕ)
    (x y : Fin m → ℝ) (i : Fin (m + m)) :
    binaryWordVandermondeCoordinateEquiv m
        (euclideanOfFun m x, euclideanOfFun m y) i =
      vandermondeParam m (positiveNodes (m + m)) x i +
        positiveNodes (m + m) i ^ m *
          vandermondeParam m (positiveNodes (m + m)) y i := by
  rw [binaryWordVandermondeCoordinateEquiv, LinearEquiv.trans_apply,
    vandermondeLinearEquiv_apply]
  simp only [vandermondeParam, Fin.sum_univ_add,
    binaryWordCoefficientEquiv_apply_castAdd,
    binaryWordCoefficientEquiv_apply_natAdd,
    Fin.val_castAdd, Fin.val_natAdd, pow_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem binaryLeftWord_coordinates_apply (m : ℕ) (c x : Fin m → ℝ)
    (i : Fin (m + m)) :
    binaryWordVandermondeCoordinateEquiv m (binaryLeftWord m c x) i =
      vandermondeParam m (positiveNodes (m + m)) x i +
        positiveNodes (m + m) i ^ m *
          vandermondeParam m (positiveNodes (m + m)) c i := by
  exact binaryWordVandermondeCoordinateEquiv_apply_pair m x c i

theorem binaryRightWord_coordinates_apply (m : ℕ) (c y : Fin m → ℝ)
    (i : Fin (m + m)) :
    binaryWordVandermondeCoordinateEquiv m (binaryRightWord m c y) i =
      vandermondeParam m (positiveNodes (m + m)) c i +
        positiveNodes (m + m) i ^ m *
          vandermondeParam m (positiveNodes (m + m)) y i := by
  exact binaryWordVandermondeCoordinateEquiv_apply_pair m c y i

theorem binaryDiagonalWord_coordinates_apply (m : ℕ) (c x : Fin m → ℝ)
    (i : Fin (m + m)) :
    binaryWordVandermondeCoordinateEquiv m (binaryDiagonalWord m c x) i =
      vandermondeParam m (positiveNodes (m + m)) (x + c) i +
        positiveNodes (m + m) i ^ m *
          vandermondeParam m (positiveNodes (m + m)) x i := by
  exact binaryWordVandermondeCoordinateEquiv_apply_pair m (x + c) x i

theorem vandermondeParam_add {N : ℕ} (m : ℕ) (t : Fin N → ℝ)
    (x y : Fin m → ℝ) :
    vandermondeParam m t (x + y) =
      vandermondeParam m t x + vandermondeParam m t y := by
  funext i
  simp [vandermondeParam, mul_add, Finset.sum_add_distrib]

/-- Every `m` transformed output coordinates determine the free letter on a
left pattern plane. -/
theorem binaryLeftWord_projection_injective (m : ℕ) (c : Fin m → ℝ)
    (I : Finset (Fin (m + m))) (hI : I.card = m) :
    Function.Injective (fun x : Fin m → ℝ ↦ fun i : I ↦
      binaryWordVandermondeCoordinateEquiv m (binaryLeftWord m c x) i) := by
  intro x y hxy
  apply injective_coordinateProjection_vandermondeParam m
    (positiveNodes (m + m)) (positiveNodes_injective (m + m)) I hI
  funext i
  have hi := congrFun hxy i
  change binaryWordVandermondeCoordinateEquiv m (binaryLeftWord m c x)
      (i : Fin (m + m)) =
    binaryWordVandermondeCoordinateEquiv m (binaryLeftWord m c y)
      (i : Fin (m + m)) at hi
  rw [binaryLeftWord_coordinates_apply, binaryLeftWord_coordinates_apply] at hi
  exact add_right_cancel hi

/-- Every `m` transformed output coordinates determine the free letter on a
right pattern plane. -/
theorem binaryRightWord_projection_injective (m : ℕ) (c : Fin m → ℝ)
    (I : Finset (Fin (m + m))) (hI : I.card = m) :
    Function.Injective (fun y : Fin m → ℝ ↦ fun i : I ↦
      binaryWordVandermondeCoordinateEquiv m (binaryRightWord m c y) i) := by
  intro x y hxy
  apply injective_coordinateProjection_vandermondeParam m
    (positiveNodes (m + m)) (positiveNodes_injective (m + m)) I hI
  funext i
  have hi := congrFun hxy i
  change binaryWordVandermondeCoordinateEquiv m (binaryRightWord m c x)
      (i : Fin (m + m)) =
    binaryWordVandermondeCoordinateEquiv m (binaryRightWord m c y)
      (i : Fin (m + m)) at hi
  rw [binaryRightWord_coordinates_apply, binaryRightWord_coordinates_apply] at hi
  have hs : positiveNodes (m + m) (i : Fin (m + m)) ^ m ≠ 0 :=
    pow_ne_zero _ (ne_of_gt
      (positiveNodes_pos (N := m + m) (i : Fin (m + m))))
  exact mul_left_cancel₀ hs (add_left_cancel hi)

/-- Every `m` transformed output coordinates determine the free letter on a
fixed-difference diagonal pattern plane. -/
theorem binaryDiagonalWord_projection_injective (m : ℕ) (c : Fin m → ℝ)
    (I : Finset (Fin (m + m))) (hI : I.card = m) :
    Function.Injective (fun x : Fin m → ℝ ↦ fun i : I ↦
      binaryWordVandermondeCoordinateEquiv m (binaryDiagonalWord m c x) i) := by
  intro x y hxy
  apply injective_coordinateProjection_vandermondeParam m
    (positiveNodes (m + m)) (positiveNodes_injective (m + m)) I hI
  funext i
  have hi := congrFun hxy i
  change binaryWordVandermondeCoordinateEquiv m (binaryDiagonalWord m c x)
      (i : Fin (m + m)) =
    binaryWordVandermondeCoordinateEquiv m (binaryDiagonalWord m c y)
      (i : Fin (m + m)) at hi
  rw [binaryDiagonalWord_coordinates_apply,
    binaryDiagonalWord_coordinates_apply] at hi
  have haddx := congrFun (vandermondeParam_add m
    (positiveNodes (m + m)) x c) (i : Fin (m + m))
  have handy := congrFun (vandermondeParam_add m
    (positiveNodes (m + m)) y c) (i : Fin (m + m))
  rw [haddx, handy] at hi
  have hs : 1 + positiveNodes (m + m) (i : Fin (m + m)) ^ m ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (pow_nonneg
        (positiveNodes_pos (N := m + m) (i : Fin (m + m))).le m))
  apply mul_left_cancel₀ hs
  simp only [Pi.add_apply] at hi
  linear_combination hi

/-- The rational-coordinate bad set pulled back through the full square
Vandermonde coordinate equivalence. -/
def binaryRationalCoordinateObstruction (m : ℕ) :
    Set (RationalBinaryWordSpace m) :=
  binaryWordVandermondeCoordinateEquiv m ⁻¹' rationalCoordinatesAtLeast m

theorem countable_binaryLeftWord_obstruction_preimage
    (m : ℕ) (c : Fin m → ℝ) :
    (binaryLeftWord m c ⁻¹' binaryRationalCoordinateObstruction m).Countable :=
  countable_preimage_rationalCoordinatesAtLeast m
    (fun x ↦ binaryWordVandermondeCoordinateEquiv m (binaryLeftWord m c x))
    (binaryLeftWord_projection_injective m c)

theorem countable_binaryRightWord_obstruction_preimage
    (m : ℕ) (c : Fin m → ℝ) :
    (binaryRightWord m c ⁻¹' binaryRationalCoordinateObstruction m).Countable :=
  countable_preimage_rationalCoordinatesAtLeast m
    (fun x ↦ binaryWordVandermondeCoordinateEquiv m (binaryRightWord m c x))
    (binaryRightWord_projection_injective m c)

theorem countable_binaryDiagonalWord_obstruction_preimage
    (m : ℕ) (c : Fin m → ℝ) :
    (binaryDiagonalWord m c ⁻¹' binaryRationalCoordinateObstruction m).Countable :=
  countable_preimage_rationalCoordinatesAtLeast m
    (fun x ↦ binaryWordVandermondeCoordinateEquiv m (binaryDiagonalWord m c x))
    (binaryDiagonalWord_projection_injective m c)

/-- The actual affine pattern carriers, expressed as ranges of the three
parametrizations. -/
def binaryLeftPlane (m : ℕ) (c : Fin m → ℝ) :
    Set (RationalBinaryWordSpace m) := Set.range (binaryLeftWord m c)

def binaryRightPlane (m : ℕ) (c : Fin m → ℝ) :
    Set (RationalBinaryWordSpace m) := Set.range (binaryRightWord m c)

def binaryDiagonalPlane (m : ℕ) (c : Fin m → ℝ) :
    Set (RationalBinaryWordSpace m) := Set.range (binaryDiagonalWord m c)

theorem countable_binaryLeftPlane_inter_obstruction
    (m : ℕ) (c : Fin m → ℝ) :
    (binaryLeftPlane m c ∩ binaryRationalCoordinateObstruction m).Countable := by
  apply (countable_binaryLeftWord_obstruction_preimage m c).image
    (binaryLeftWord m c) |>.mono
  rintro z ⟨⟨x, rfl⟩, hx⟩
  exact ⟨x, hx, rfl⟩

theorem countable_binaryRightPlane_inter_obstruction
    (m : ℕ) (c : Fin m → ℝ) :
    (binaryRightPlane m c ∩ binaryRationalCoordinateObstruction m).Countable := by
  apply (countable_binaryRightWord_obstruction_preimage m c).image
    (binaryRightWord m c) |>.mono
  rintro z ⟨⟨x, rfl⟩, hx⟩
  exact ⟨x, hx, rfl⟩

theorem countable_binaryDiagonalPlane_inter_obstruction
    (m : ℕ) (c : Fin m → ℝ) :
    (binaryDiagonalPlane m c ∩ binaryRationalCoordinateObstruction m).Countable := by
  apply (countable_binaryDiagonalWord_obstruction_preimage m c).image
    (binaryDiagonalWord m c) |>.mono
  rintro z ⟨⟨x, rfl⟩, hx⟩
  exact ⟨x, hx, rfl⟩

end BinaryWordCoordinateAutomorphism

end VandermondeTrace

section ZeroDimensionalCase

/-- Rational bounded open intervals form the standard countable basis of
the real line. -/
def rationalIntervalBasis : Set (Set ℝ) :=
  ⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Set.Ioo (a : ℝ) (b : ℝ)}

theorem isTopologicalBasis_rationalIntervalBasis :
    TopologicalSpace.IsTopologicalBasis rationalIntervalBasis :=
  Real.isTopologicalBasis_Ioo_rat

theorem mem_rationalIntervalBasis_iff {U : Set ℝ} :
    U ∈ rationalIntervalBasis ↔
      ∃ a b : ℚ, a < b ∧ U = Set.Ioo (a : ℝ) (b : ℝ) := by
  simp only [rationalIntervalBasis, Set.mem_iUnion, Set.mem_singleton_iff]
  aesop

/-- The finite-cylinder basis obtained from rational intervals in each real
coordinate. -/
def rationalBoxBasis {ι : Type*} : Set (Set (ι → ℝ)) :=
  {S | ∃ (U : ι → Set ℝ) (F : Finset ι),
    (∀ i, i ∈ F → U i ∈ rationalIntervalBasis) ∧
      S = (F : Set ι).pi U}

theorem isTopologicalBasis_rationalBoxBasis {ι : Type*} :
    TopologicalSpace.IsTopologicalBasis (rationalBoxBasis (ι := ι)) := by
  exact isTopologicalBasis_pi fun _ ↦ isTopologicalBasis_rationalIntervalBasis

/-- A useful explicit description of the order-zero Nöbeling set. -/
theorem mem_rationalCoordinateNobeling_zero_iff
    {ι : Type*} {x : ι → ℝ} :
    x ∈ rationalCoordinateNobeling 0 ↔ ∀ i, x i ∉ rationalReals := by
  constructor
  · intro hx i hi
    apply hx
    exact ⟨{i}, by simp, fun j hj ↦ by
      have hji : j = i := Finset.mem_singleton.mp hj
      simpa [hji] using hi⟩
  · intro h hx
    rcases hx with ⟨I, hcard, hrat⟩
    have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hI ↦ by
      subst I
      simp at hcard
    obtain ⟨i, hi⟩ := hne
    exact h i (hrat i hi)

/-- On the totally irrational subspace, a coordinate interval with rational
endpoints is clopen: neither endpoint belongs to the subspace. -/
theorem isClopen_subtype_preimage_Ioo_rat
    {ι : Type*} (i : ι) (a b : ℚ) :
    IsClopen
      (Subtype.val ⁻¹' (Function.eval i ⁻¹' Set.Ioo (a : ℝ) (b : ℝ)) :
        Set (rationalCoordinateNobeling (ι := ι) 0)) := by
  let e : rationalCoordinateNobeling (ι := ι) 0 → ℝ := fun x ↦ x.1 i
  have he : Continuous e := (continuous_apply i).comp continuous_subtype_val
  have hopen : IsOpen (e ⁻¹' Set.Ioo (a : ℝ) (b : ℝ)) :=
    isOpen_Ioo.preimage he
  have hclosed : IsClosed (e ⁻¹' Set.Ioo (a : ℝ) (b : ℝ)) := by
    rw [← isOpen_compl_iff]
    have heq : (e ⁻¹' Set.Ioo (a : ℝ) (b : ℝ))ᶜ =
        e ⁻¹' Set.Iio (a : ℝ) ∪ e ⁻¹' Set.Ioi (b : ℝ) := by
      ext x
      have hirr := (mem_rationalCoordinateNobeling_zero_iff.mp x.2) i
      have hnea : e x ≠ (a : ℝ) := by
        intro h
        apply hirr
        exact ⟨a, h.symm⟩
      have hneb : e x ≠ (b : ℝ) := by
        intro h
        apply hirr
        exact ⟨b, h.symm⟩
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Ioo,
        Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · intro hx
        rcases lt_trichotomy (e x) (a : ℝ) with hlt | heqa | hgt
        · exact Or.inl hlt
        · exact (hnea heqa).elim
        · rcases lt_trichotomy (e x) (b : ℝ) with hlt | heqb | hgtb
          · exact (hx ⟨hgt, hlt⟩).elim
          · exact (hneb heqb).elim
          · exact Or.inr hgtb
      · rintro (hlt | hgt) hinside
        · exact (not_lt_of_ge hinside.1.le) hlt
        · exact (not_lt_of_ge hinside.2.le) hgt
    rw [heq]
    exact (isOpen_Iio.preimage he).union (isOpen_Ioi.preimage he)
  exact ⟨hclosed, hopen⟩

/-- The order-zero rational-coordinate Nöbeling set has small inductive
dimension at most zero.  The separate `RationalSkeleton` module proves all
positive orders directly, using endpoint-avoiding grid skeletons. -/
theorem rationalCoordinateNobeling_zero_hasSmallInductiveDimensionLT
    {ι : Type*} :
    HasSmallInductiveDimensionLT
      (rationalCoordinateNobeling (ι := ι) 0) 1 := by
  let b : Set (Set (rationalCoordinateNobeling (ι := ι) 0)) :=
    (fun U ↦ Subtype.val ⁻¹' U) '' rationalBoxBasis
  have hb : TopologicalSpace.IsTopologicalBasis b :=
    isTopologicalBasis_rationalBoxBasis.isInducing IsInducing.subtypeVal
  refine .succ 0 b hb ?_
  intro V hV
  rcases hV with ⟨U, hU, rfl⟩
  rcases hU with ⟨B, F, hBF, rfl⟩
  have hclopen : IsClopen
      (Subtype.val ⁻¹' ((F : Set ι).pi B) :
        Set (rationalCoordinateNobeling (ι := ι) 0)) := by
    rw [Set.pi_def, Set.preimage_iInter]
    simp_rw [Set.preimage_iInter]
    apply isClopen_biInter_finset
    intro i hi
    obtain ⟨a, b, hab, hBi⟩ := mem_rationalIntervalBasis_iff.mp (hBF i hi)
    rw [hBi]
    simpa only [Set.preimage_preimage, Function.comp_def, Set.mem_Ioo,
      Set.preimage_ofPred_eq] using
      isClopen_subtype_preimage_Ioo_rat (ι := ι) i a b
  rw [hclopen.frontier_eq]
  exact .zero

end ZeroDimensionalCase

end Erdos909.RationalCoordinateUpper
