import Wikipedia.SzemeredisTheorem.ArithmeticProgression.Count
import Wikipedia.SzemeredisTheorem.Finite.Mean
import Wikipedia.SzemeredisTheorem.LinearForms.Basic

/-!
# Partite weighted simplices

The dense and relative Szemerédi arguments are organized as counting lemmas
for a `(k-1)`-uniform, `k`-partite simplex.  An edge of colour `j` depends on
every vertex coordinate except `j`.  Keeping that dependency in the type
prevents accidental use of the omitted coordinate and matches the dependent
index used by the CFZ blow-up forms.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A vector with coordinate `j` deleted. -/
abbrev DeletedVector {k : ℕ} (V : Fin k → Type*) (j : Fin k) :=
  (i : {i : Fin k // i ≠ j}) → V i.1

/-- Delete coordinate `j` from a dependent vector. -/
def deleteCoordinate {k : ℕ} {V : Fin k → Type*}
    (x : (i : Fin k) → V i) (j : Fin k) :
    DeletedVector V j :=
  fun i => x i.1

/-- A weighted `(k-1)`-uniform, `k`-partite hypergraph. -/
structure WeightedSimplexSystem {k : ℕ} (V : Fin k → Type*) where
  edgeWeight : (j : Fin k) → DeletedVector V j → ℝ

namespace WeightedSimplexSystem

/-- Product of the `k` edge weights on a labelled simplex. -/
def simplexWeight {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) (x : (i : Fin k) → V i) : ℝ :=
  ∏ j : Fin k, H.edgeWeight j (deleteCoordinate x j)

/-- Normalized count of labelled weighted simplices. -/
noncomputable def simplexCount {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : WeightedSimplexSystem V) : ℝ :=
  mean H.simplexWeight

theorem simplexWeight_nonneg {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V)
    (hH : ∀ j x, 0 ≤ H.edgeWeight j x)
    (x : (i : Fin k) → V i) :
    0 ≤ H.simplexWeight x := by
  exact Finset.prod_nonneg fun j _ => hH j (deleteCoordinate x j)

theorem simplexCount_nonneg {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : WeightedSimplexSystem V)
    (hH : ∀ j x, 0 ≤ H.edgeWeight j x) :
    0 ≤ H.simplexCount :=
  mean_nonneg (H.simplexWeight_nonneg hH)

/-- Pointwise domination of nonnegative edge weights dominates the full
simplex weight. -/
theorem simplexWeight_mono {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V)
    (hH : ∀ j x, 0 ≤ H.edgeWeight j x)
    (hHG : ∀ j x, H.edgeWeight j x ≤ G.edgeWeight j x)
    (x : (i : Fin k) → V i) :
    H.simplexWeight x ≤ G.simplexWeight x := by
  exact Finset.prod_le_prod
    (fun j _ => hH j (deleteCoordinate x j))
    (fun j _ => hHG j (deleteCoordinate x j))

theorem simplexCount_mono {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V)
    (hH : ∀ j x, 0 ≤ H.edgeWeight j x)
    (hHG : ∀ j x, H.edgeWeight j x ≤ G.edgeWeight j x) :
    H.simplexCount ≤ G.simplexCount :=
  mean_mono (H.simplexWeight_mono G hH hHG)

end WeightedSimplexSystem

/-- The one-copy arithmetic-progression form attached to edge `j`. -/
def apSimplexForm (k N : ℕ) (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i

/-- Sum of all simplex coordinates.  It becomes the common difference,
up to sign, in the encoded progression. -/
def simplexCoordinateSum (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, x i

/-- First moment of the simplex coordinates.  It becomes the initial term
of the encoded progression. -/
def simplexCoordinateMoment (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, (i : ZMod N) * x i

/-- The edge form is the first moment minus `j` times the coordinate sum.
Consequently, the `k` edge values of one simplex form a cyclic arithmetic
progression. -/
theorem apSimplexForm_deleteCoordinate (k N : ℕ) (j : Fin k)
    (x : Fin k → ZMod N) :
    apSimplexForm k N j (deleteCoordinate x j) =
      simplexCoordinateMoment k N x -
        (j : ZMod N) * simplexCoordinateSum k N x := by
  classical
  let f : Fin k → ZMod N :=
    fun i => (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i ≠ j) f
  have hcomplement :
      (∑ i : {i : Fin k // ¬i ≠ j}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i
    simp only [Finset.mem_univ, forall_const]
    have hij : i.1 = j := not_ne_iff.mp i.2
    rw [hij]
    simp [f]
  have hsum : (∑ i : {i : Fin k // i ≠ j}, f i.1) = ∑ i : Fin k, f i := by
    rw [hcomplement, add_zero] at hsplit
    exact hsplit
  rw [apSimplexForm]
  change (∑ i : {i : Fin k // i ≠ j}, f i.1) =
    simplexCoordinateMoment k N x -
      (j : ZMod N) * simplexCoordinateSum k N x
  rw [hsum]
  simp only [simplexCoordinateMoment, simplexCoordinateSum, f]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The weighted simplex system whose simplices encode arithmetic
progressions. -/
def apSimplexSystem (k N : ℕ) (f : ZMod N → ℝ) :
    WeightedSimplexSystem (fun _ : Fin k => ZMod N) where
  edgeWeight j x := f (apSimplexForm k N j x)

/-- A labelled simplex in the AP system contributes exactly the weight of
the cyclic progression with initial term the coordinate moment and common
difference the negative coordinate sum. -/
theorem apSimplexSystem_simplexWeight
    (k N : ℕ) (f : ZMod N → ℝ)
    (x : Fin k → ZMod N) :
    (apSimplexSystem k N f).simplexWeight x =
      cyclicAPProduct k N f
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) := by
  apply Finset.prod_congr rfl
  intro j _
  change
    f (apSimplexForm k N j (deleteCoordinate x j)) =
      f (cyclicAPTerm
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) j)
  congr 1
  rw [apSimplexForm_deleteCoordinate]
  simp [cyclicAPTerm]
  ring

end Wikipedia.SzemeredisTheorem
