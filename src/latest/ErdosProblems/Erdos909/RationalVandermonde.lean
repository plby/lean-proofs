/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos909.RationalCoordinateUpper
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.EquivFin

/-!
# A Vandermonde MDS coordinate system for binary words

The first `m` columns use powers `0, ..., m - 1`; the second `m` columns use
powers `m, ..., 2m - 1`.  Every `m` output coordinates determine a point on
each left, right, or diagonal pattern plane.  This is the MDS input needed by
the rational-coordinate construction for Erdős Problem 909.
-/

open scoped BigOperators Matrix

namespace Erdos909.RationalVandermonde

noncomputable section

/-- Positive pairwise-distinct evaluation nodes. -/
def node {N : ℕ} (i : Fin N) : ℝ := i.1 + 1

lemma node_injective {N : ℕ} : Function.Injective (node (N := N)) := by
  intro i j h
  apply Fin.ext
  exact_mod_cast add_right_cancel h

lemma node_pos {N : ℕ} (i : Fin N) : 0 < node i := by
  unfold node
  positivity

/-- Evaluation of a polynomial of degree less than `m` at arbitrary nodes. -/
def evalPowers {N : ℕ} (m : ℕ) (x : Fin m → ℝ) : Fin N → ℝ :=
  fun i ↦ ∑ j : Fin m, node i ^ (j : ℕ) * x j

lemma evalPowers_add {N m : ℕ} (x y : Fin m → ℝ) (i : Fin N) :
    evalPowers m (x + y) i = evalPowers m x i + evalPowers m y i := by
  simp [evalPowers, mul_add, Finset.sum_add_distrib]

/-- Any `m` coordinates of `evalPowers m` determine the coefficient vector. -/
lemma evalPowers_projection_injective {N m : ℕ} (I : Finset (Fin N))
    (hI : I.card = m) :
    Function.Injective (fun x : Fin m → ℝ ↦ fun i : I ↦ evalPowers m x (i : Fin N)) := by
  let e : I ≃ Fin m := Finset.equivFinOfCardEq hI
  intro x y hxy
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero
    (f := fun j : Fin m ↦ node ((e.symm j : I) : Fin N))
  · exact node_injective.comp (Subtype.val_injective.comp e.symm.injective)
  · intro j
    have hj := congrFun hxy (e.symm j)
    change (∑ i : Fin m, node ((e.symm j : I) : Fin N) ^ (i : ℕ) *
      (x i - y i)) = 0
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    change evalPowers m x ((e.symm j : I) : Fin N) =
      evalPowers m y ((e.symm j : I) : Fin N) at hj
    exact hj

/-- The square Vandermonde evaluation map. -/
def vandermondeLinearMap (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  (Matrix.vandermonde (node (N := N))).mulVecLin

lemma vandermondeLinearMap_injective (N : ℕ) :
    Function.Injective (vandermondeLinearMap N) := by
  exact Matrix.mulVec_injective_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr node_injective)

/-- The full coordinate automorphism whose matrix is the square Vandermonde
matrix at the positive integer nodes. -/
noncomputable def vandermondeCoordinateEquiv (N : ℕ) :
    (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ) :=
  LinearEquiv.ofInjectiveEndo (vandermondeLinearMap N)
    (vandermondeLinearMap_injective N)

@[simp]
lemma vandermondeCoordinateEquiv_apply (N : ℕ) (x : Fin N → ℝ) (i : Fin N) :
    vandermondeCoordinateEquiv N x i = evalPowers N x i := by
  simp [vandermondeCoordinateEquiv, vandermondeLinearMap, evalPowers,
    Matrix.mulVec, dotProduct, Matrix.vandermonde]

/-- The `2m`-coordinate word map.  Its columns are consecutive powers of the
Vandermonde nodes: the first `m` columns encode the first letter and the next
`m` columns encode the second. -/
def wordMap (m : ℕ) (z : (Fin m → ℝ) × (Fin m → ℝ)) : Fin (m + m) → ℝ :=
  fun i ↦ evalPowers m z.1 i + node i ^ m * evalPowers m z.2 i

def leftPattern (m : ℕ) (c x : Fin m → ℝ) : Fin (m + m) → ℝ :=
  wordMap m (x, c)

def rightPattern (m : ℕ) (c y : Fin m → ℝ) : Fin (m + m) → ℝ :=
  wordMap m (c, y)

def diagonalPattern (m : ℕ) (c x : Fin m → ℝ) : Fin (m + m) → ℝ :=
  wordMap m (x + c, x)

lemma leftPattern_projection_injective (m : ℕ) (c : Fin m → ℝ)
    (I : Finset (Fin (m + m))) (hI : I.card = m) :
    Function.Injective (fun x : Fin m → ℝ ↦ fun i : I ↦ leftPattern m c x i) := by
  intro x y hxy
  apply evalPowers_projection_injective I hI
  funext i
  have hi := congrFun hxy i
  have hi' : evalPowers m x (i : Fin (m + m)) +
      node (i : Fin (m + m)) ^ m * evalPowers m c (i : Fin (m + m)) =
      evalPowers m y (i : Fin (m + m)) +
      node (i : Fin (m + m)) ^ m * evalPowers m c (i : Fin (m + m)) := by
    simpa only [leftPattern, wordMap] using hi
  exact add_right_cancel hi'

lemma rightPattern_projection_injective (m : ℕ) (c : Fin m → ℝ)
    (I : Finset (Fin (m + m))) (hI : I.card = m) :
    Function.Injective (fun y : Fin m → ℝ ↦ fun i : I ↦ rightPattern m c y i) := by
  intro x y hxy
  apply evalPowers_projection_injective I hI
  funext i
  have hi := congrFun hxy i
  have hn : node (i : Fin (m + m)) ^ m ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (node_pos _))
  apply mul_left_cancel₀ hn
  have hi' : evalPowers m c (i : Fin (m + m)) +
      node (i : Fin (m + m)) ^ m * evalPowers m x (i : Fin (m + m)) =
      evalPowers m c (i : Fin (m + m)) +
      node (i : Fin (m + m)) ^ m * evalPowers m y (i : Fin (m + m)) := by
    simpa only [rightPattern, wordMap] using hi
  exact add_left_cancel hi'

lemma diagonalPattern_projection_injective (m : ℕ) (c : Fin m → ℝ)
    (I : Finset (Fin (m + m))) (hI : I.card = m) :
    Function.Injective (fun x : Fin m → ℝ ↦ fun i : I ↦ diagonalPattern m c x i) := by
  intro x y hxy
  apply evalPowers_projection_injective I hI
  funext i
  have hi := congrFun hxy i
  have hn : 1 + node (i : Fin (m + m)) ^ m ≠ 0 := by
    have : 0 < node (i : Fin (m + m)) ^ m := pow_pos (node_pos _) _
    positivity
  apply mul_left_cancel₀ hn
  have hi' : evalPowers m (x + c) (i : Fin (m + m)) +
      node (i : Fin (m + m)) ^ m * evalPowers m x (i : Fin (m + m)) =
      evalPowers m (y + c) (i : Fin (m + m)) +
      node (i : Fin (m + m)) ^ m * evalPowers m y (i : Fin (m + m)) := by
    simpa only [diagonalPattern, wordMap] using hi
  rw [evalPowers_add, evalPowers_add] at hi'
  linarith

open Erdos909.RationalCoordinateUpper in
/-- The rational-coordinate obstruction has countable trace on every left
pattern plane in Vandermonde coordinates. -/
lemma countable_leftPattern_preimage (m : ℕ) (c : Fin m → ℝ) :
    (leftPattern m c ⁻¹' rationalCoordinatesAtLeast m).Countable :=
  countable_preimage_rationalCoordinatesAtLeast m (leftPattern m c)
    (leftPattern_projection_injective m c)

open Erdos909.RationalCoordinateUpper in
/-- The rational-coordinate obstruction has countable trace on every right
pattern plane in Vandermonde coordinates. -/
lemma countable_rightPattern_preimage (m : ℕ) (c : Fin m → ℝ) :
    (rightPattern m c ⁻¹' rationalCoordinatesAtLeast m).Countable :=
  countable_preimage_rationalCoordinatesAtLeast m (rightPattern m c)
    (rightPattern_projection_injective m c)

open Erdos909.RationalCoordinateUpper in
/-- The rational-coordinate obstruction has countable trace on every
diagonal pattern plane in Vandermonde coordinates. -/
lemma countable_diagonalPattern_preimage (m : ℕ) (c : Fin m → ℝ) :
    (diagonalPattern m c ⁻¹' rationalCoordinatesAtLeast m).Countable :=
  countable_preimage_rationalCoordinatesAtLeast m (diagonalPattern m c)
    (diagonalPattern_projection_injective m c)

end

end Erdos909.RationalVandermonde
