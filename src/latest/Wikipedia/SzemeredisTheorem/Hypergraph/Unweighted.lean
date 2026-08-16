import Wikipedia.SzemeredisTheorem.Hypergraph.Simplex

/-!
# Unweighted partite simplex hypergraphs

The removal argument uses a `(k - 1)`-uniform, `k`-partite hypergraph whose
edge of colour `j` depends on every vertex coordinate except `j`.  This file
gives the finite predicate-valued interface and connects its labelled
simplices exactly to the weighted counting API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- An unweighted `(k - 1)`-uniform, `k`-partite hypergraph. -/
structure SimplexHypergraph {k : ℕ} (V : Fin k → Type*) where
  edge : (j : Fin k) → DeletedVector V j → Prop

namespace SimplexHypergraph

/-- The finite set of edges of one colour. -/
noncomputable def edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k) :
    Finset (DeletedVector V j) := by
  classical
  exact Finset.univ.filter (H.edge j)

@[simp]
theorem mem_edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k)
    (x : DeletedVector V j) :
    x ∈ H.edgeFinset j ↔ H.edge j x := by
  classical
  simp [edgeFinset]

/-- The finite set of labelled simplices. -/
noncomputable def simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    Finset ((i : Fin k) → V i) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, H.edge j (deleteCoordinate x j)

@[simp]
theorem mem_simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    x ∈ H.simplexFinset ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  classical
  simp [simplexFinset]

/-- Regard an unweighted hypergraph as a zero-one weighted system. -/
noncomputable def toWeighted {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) : WeightedSimplexSystem V := by
  classical
  exact
    { edgeWeight := fun j x => if H.edge j x then 1 else 0 }

@[simp]
theorem toWeighted_edgeWeight_of_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : H.edge j x) :
    H.toWeighted.edgeWeight j x = 1 := by
  classical
  simp [toWeighted, hx]

@[simp]
theorem toWeighted_edgeWeight_of_not_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : ¬H.edge j x) :
    H.toWeighted.edgeWeight j x = 0 := by
  classical
  simp [toWeighted, hx]

theorem toWeighted_edgeWeight_nonneg {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    (j : Fin k) (x : DeletedVector V j) :
    0 ≤ H.toWeighted.edgeWeight j x := by
  classical
  simp only [toWeighted]
  split <;> norm_num

theorem toWeighted_edgeWeight_le_one {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    (j : Fin k) (x : DeletedVector V j) :
    H.toWeighted.edgeWeight j x ≤ 1 := by
  classical
  simp only [toWeighted]
  split <;> norm_num

/-- A zero-one simplex weight is exactly the indicator of the labelled
simplex finset. -/
theorem toWeighted_simplexWeight_eq_indicator {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    H.toWeighted.simplexWeight x =
      finsetIndicator H.simplexFinset x := by
  classical
  by_cases hx : x ∈ H.simplexFinset
  · have hedges :
        ∀ j, H.edge j (deleteCoordinate x j) :=
      (H.mem_simplexFinset x).mp hx
    simp [WeightedSimplexSystem.simplexWeight, toWeighted,
      finsetIndicator, hx, hedges]
  · have hnot :
        ¬∀ j, H.edge j (deleteCoordinate x j) := by
      simpa using hx
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero :
        ∏ i : Fin k,
            H.toWeighted.edgeWeight i (deleteCoordinate x i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact toWeighted_edgeWeight_of_not_edge H hj
    rw [WeightedSimplexSystem.simplexWeight, hzero]
    exact (finsetIndicator_of_not_mem hx).symm

/-- The normalized weighted count is the number of labelled simplices divided
by the size of the ambient product. -/
theorem toWeighted_simplexCount_eq_card_div {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : SimplexHypergraph V) :
    H.toWeighted.simplexCount =
      (H.simplexFinset.card : ℝ) /
        Fintype.card ((i : Fin k) → V i) := by
  classical
  rw [WeightedSimplexSystem.simplexCount]
  have hfun :
      H.toWeighted.simplexWeight =
        finsetIndicator H.simplexFinset := by
    funext x
    exact toWeighted_simplexWeight_eq_indicator H x
  rw [hfun, mean_finsetIndicator]

/-- A family of deleted edge sets meets every labelled simplex. -/
def IsSimplexCover {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : (j : Fin k) → Finset (DeletedVector V j)) : Prop :=
  ∀ x ∈ H.simplexFinset,
    ∃ j, deleteCoordinate x j ∈ deleted j

/-- Equivalently, after deleting a simplex cover, no labelled simplex
survives. -/
theorem isSimplexCover_iff {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : (j : Fin k) → Finset (DeletedVector V j)) :
    H.IsSimplexCover deleted ↔
      ∀ x, (∀ j, deleteCoordinate x j ∉ deleted j) →
        ∃ j, ¬H.edge j (deleteCoordinate x j) := by
  classical
  constructor
  · intro hcover x hsurvives
    by_contra h
    push Not at h
    have hx : x ∈ H.simplexFinset := by
      simpa using h
    obtain ⟨j, hj⟩ := hcover x hx
    exact hsurvives j hj
  · intro hnosimplex x hx
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hnosimplex x h
    exact hj ((H.mem_simplexFinset x).mp hx j)

end SimplexHypergraph

end Wikipedia.SzemeredisTheorem
