import Wikipedia.SzemeredisTheorem.Hypergraph.PreliminaryOrderedRegularity

/-!
# Bernoulli reduction for bounded boundary products

The preliminary shared-face regularity lemma is stated using Boolean
products on the immediate boundary of an upper face.  This file proves that
this loses no generality for products of arbitrary `[0,1]`-valued boundary
factors.

At successor arity the ordinary `CutTestFamily` coordinates are exactly the
boundary coordinates.  The only formal difference is that
`BooleanCutAssignment` uses an uncurried product index whereas
`BoundaryBooleanCutAssignment` is curried.  After recording the equivalence
between those two presentations, the finite Bernoulli-mixture identities
from `BooleanCutReduction` give:

* every bounded boundary factor is a convex average of Boolean component
  indicators;
* every bounded boundary product is a convex average of
  `boundaryBooleanCutSupport` indicators;
* Boolean preliminary regularity therefore controls every bounded boundary
  product with the same error.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Curry an ordinary Boolean cut assignment at successor arity into the
boundary-assignment presentation. -/
def boundaryBooleanAssignmentOfBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    BoundaryBooleanCutAssignment G j :=
  fun i z => b ⟨i, z⟩

/-- Uncurry a boundary Boolean assignment into the ordinary cut-coordinate
presentation. -/
def booleanAssignmentOfBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutAssignment G (j + 1) :=
  fun q => b q.1 q.2

@[simp]
theorem booleanAssignmentOfBoundary_ofBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        (boundaryBooleanAssignmentOfBoolean b) = b := by
  funext q
  cases q
  rfl

@[simp]
theorem boundaryBooleanAssignmentOfBoolean_ofBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanAssignmentOfBoolean
        (booleanAssignmentOfBoundary b) = b := by
  funext i z
  rfl

/-- The curried and uncurried Boolean boundary assignments are equivalent. -/
def booleanBoundaryAssignmentEquiv
    (G : Type*) (j : ℕ) :
    BooleanCutAssignment G (j + 1) ≃
      BoundaryBooleanCutAssignment G j where
  toFun := boundaryBooleanAssignmentOfBoolean
  invFun := booleanAssignmentOfBoundary
  left_inv := booleanAssignmentOfBoundary_ofBoolean
  right_inv := boundaryBooleanAssignmentOfBoolean_ofBoundary

@[simp]
theorem booleanAssignmentOfBoundary_equiv_apply
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        ((booleanBoundaryAssignmentEquiv G j) b) = b :=
  booleanAssignmentOfBoundary_ofBoolean b

/-- The Bernoulli coefficient of one boundary Boolean assignment. -/
def boundaryBernoulliWeight
    {G : Type*} [Fintype G] {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (b : BoundaryBooleanCutAssignment G j) : ℝ :=
  bernoulliAssignmentWeight
    (cutTestCoordinateValue u)
    (booleanAssignmentOfBoundary b)

/-- Boundary Bernoulli coefficients sum to one. -/
theorem sum_boundaryBernoulliWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1)) :
    ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b = 1 := by
  classical
  calc
    (∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b) =
        ∑ b : BooleanCutAssignment G (j + 1),
          bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b := by
      symm
      exact
        Fintype.sum_equiv
          (booleanBoundaryAssignmentEquiv G j)
          (fun b : BooleanCutAssignment G (j + 1) =>
            bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b)
          (fun b : BoundaryBooleanCutAssignment G j =>
            boundaryBernoulliWeight u b)
          (fun b => by simp [boundaryBernoulliWeight])
    _ = 1 :=
      sum_bernoulliAssignmentWeight
        (cutTestCoordinateValue u)

/-- Bounded boundary factors give nonnegative Bernoulli coefficients. -/
theorem boundaryBernoulliWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u)
    (b : BoundaryBooleanCutAssignment G j) :
    0 ≤ boundaryBernoulliWeight u b := by
  exact
    bernoulliAssignmentWeight_nonneg
      (p := cutTestCoordinateValue u)
      (fun q => hu.nonneg q.1 q.2)
      (fun q => hu.le_one q.1 q.2)
      (booleanAssignmentOfBoundary b)

/-- The boundary component indicator is the corresponding Boolean scalar
coordinate. -/
theorem boundaryBooleanComponentCut_eval
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) (z : Fin j → G) :
    (boundaryBooleanComponentCut b i).eval z =
      booleanValue (booleanAssignmentOfBoundary b) ⟨i, z⟩ := by
  classical
  by_cases h : b i z = true
  · have hz : z ∈ boundaryBooleanComponentCut b i := by
      rw [mem_boundaryBooleanComponentCut]
      exact h
    rw [BooleanCutTest.eval_of_mem _ hz]
    simp [booleanValue, booleanAssignmentOfBoundary, h]
  · have hz : z ∉ boundaryBooleanComponentCut b i := by
      rw [mem_boundaryBooleanComponentCut]
      exact h
    rw [BooleanCutTest.eval_of_not_mem _ hz]
    simp [booleanValue, booleanAssignmentOfBoundary, h]

/-- At successor arity the specialized boundary erasure is the ordinary
cut-test coordinate erasure. -/
theorem eraseBoundaryCoordinate_eq_eraseCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    eraseBoundaryCoordinate i x = eraseCoordinate i x :=
  rfl

/-- The boundary support of a curried assignment is the ordinary Boolean
face-cut support of its uncurried assignment. -/
theorem boundaryBooleanCutSupport_eq_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanCutSupport b =
      booleanFaceCutSupport (booleanAssignmentOfBoundary b) := by
  classical
  ext x
  rw [mem_boundaryBooleanCutSupport,
    mem_booleanFaceCutSupport]
  simp only [booleanAssignmentOfBoundary,
    eraseBoundaryCoordinate_eq_eraseCoordinate]

/-- Evaluating a boundary Boolean support gives exactly the product of its
Boolean component indicators. -/
theorem boundaryBooleanCutSupport_eval
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (x : Fin (j + 1) → G) :
    (boundaryBooleanCutSupport b).eval x =
      cutTestProduct
        (cutTestFamilyOfBooleanAssignment
          (booleanAssignmentOfBoundary b)) x := by
  rw [boundaryBooleanCutSupport_eq_booleanFaceCutSupport,
    booleanFaceCutSupport_eval]

/-- Every scalar boundary factor is the exact Bernoulli expectation of its
Boolean component indicators. -/
theorem boundaryFactor_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (i : Fin (j + 1)) (z : Fin j → G) :
    u i z =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          (boundaryBooleanComponentCut b i).eval z := by
  classical
  have hmoment :
      (∑ b : BooleanCutAssignment G (j + 1),
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            booleanValue b ⟨i, z⟩) =
        u i z := by
    simpa [cutTestCoordinateValue] using
      (sum_bernoulliAssignmentWeight_mul_selected
        (cutTestCoordinateValue u)
        ({⟨i, z⟩} :
          Finset (CutTestCoordinate G (j + 1))))
  rw [← hmoment]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          booleanValue b ⟨i, z⟩)
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          (boundaryBooleanComponentCut b i).eval z)
      (fun b => by
        simp [boundaryBernoulliWeight,
          boundaryBooleanComponentCut_eval])

/-- Every boundary product is the exact convex mixture of the indicators of
boundary Boolean cut supports. -/
theorem boundaryCutProduct_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (x : Fin (j + 1) → G) :
    cutTestProduct u x =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          (boundaryBooleanCutSupport b).eval x := by
  classical
  rw [cutTestProduct_eq_sum_boolean]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutTestProduct
            (cutTestFamilyOfBooleanAssignment b) x)
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          (boundaryBooleanCutSupport b).eval x)
      (fun b => by
        simp [boundaryBernoulliWeight,
          boundaryBooleanCutSupport_eval])

namespace FaceRegularityState

/-- Exact convex-mixture formula for residual correlation against a bounded
boundary product.  The identity itself does not require boundedness. -/
theorem faceCutCorrelation_eq_sum_boundaryBoolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    (u : CutTestFamily G (j + 1)) :
    S.faceCutCorrelation f u =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b) := by
  classical
  rw [S.faceCutCorrelation_eq_sum_boolean]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b))
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b))
      (fun b => by
        rw [S.faceCutCorrelation_boolean]
        simp [boundaryBernoulliWeight,
          boundaryBooleanCutSupport_eq_booleanFaceCutSupport])

/-- Uniform control of all Boolean boundary products controls every bounded
`[0,1]`-valued boundary product, with no loss in the error. -/
theorem abs_faceCutCorrelation_le_of_boundaryBoolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    {ε : ℝ}
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u)
    (hboolean :
      ∀ b : BoundaryBooleanCutAssignment G j,
        |S.booleanCutCorrelation f
          (boundaryBooleanCutSupport b)| ≤ ε) :
    |S.faceCutCorrelation f u| ≤ ε := by
  rw [S.faceCutCorrelation_eq_sum_boundaryBoolean]
  calc
    |∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b)| ≤
        ∑ b : BoundaryBooleanCutAssignment G j,
          |boundaryBernoulliWeight u b *
            S.booleanCutCorrelation f
              (boundaryBooleanCutSupport b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ b : BoundaryBooleanCutAssignment G j,
          boundaryBernoulliWeight u b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw : 0 ≤ boundaryBernoulliWeight u b :=
        boundaryBernoulliWeight_nonneg u hu b
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hboolean b) hw
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_boundaryBernoulliWeight, one_mul]

end FaceRegularityState

/-- Preliminary ordered regularity tested against every bounded boundary
product rather than only Boolean boundary products. -/
def IsPreliminaryOrderedBoundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts),
    (⟨orderedBoundaryPartition lower e⟩ :
      FaceRegularityState (Fin (j + 1) → G)).IsFaceCutRegular
        (partitionAtomIndicator (upper e) a) ε

/-- Boolean preliminary ordered regularity implies bounded-test preliminary
ordered regularity with exactly the same error. -/
theorem IsPreliminaryOrderedRegular.toBounded
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {lower : OrderedFacePartitionSystem G k j}
    {upper : OrderedFacePartitionSystem G k (j + 1)}
    {ε : ℝ}
    (hregular :
      IsPreliminaryOrderedRegular lower upper ε) :
    IsPreliminaryOrderedBoundedRegular
      lower upper ε := by
  intro e a u hu
  exact
    FaceRegularityState.abs_faceCutCorrelation_le_of_boundaryBoolean
      (⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G))
      (partitionAtomIndicator (upper e) a)
      u hu (fun b => hregular e a b)

end Wikipedia.SzemeredisTheorem
