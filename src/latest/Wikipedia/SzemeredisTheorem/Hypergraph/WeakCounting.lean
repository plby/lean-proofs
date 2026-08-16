import Wikipedia.SzemeredisTheorem.Hypergraph.WeakRegularity
import Wikipedia.SzemeredisTheorem.Transference.APSimplexCut
import Wikipedia.SzemeredisTheorem.Transference.SimplexCounting

/-!
# Weak-regularity counting for simplex systems

Each deleted face of a simplex with `n+1` colours is canonically presented as
an ordinary `Fin n → G` tuple.  A family of regularity states therefore gives
a structured simplex system by conditionally averaging every edge weight.

The main result is an exact weak counting lemma.  If every edge residual is
small against lower-face product cuts, then the original and structured
simplex counts differ by at most `(n+1) ε`.  The proof fixes the missing
vertex in one telescoping term; the remaining edge factors become precisely a
bounded cut-test family on the distinguished edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Canonical `Fin n` presentation of a dependent deleted-coordinate
vector. -/
noncomputable def deletedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

@[simp]
theorem deletedFaceTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedFaceTuple j (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedFaceTuple]

@[simp]
theorem finTupleToDeletedVector_deletedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j (deletedFaceTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
      ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

@[simp]
theorem deletedFaceTuple_deleteCoordinate
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) (t : Fin n) :
    deletedFaceTuple j (deleteCoordinate x j) t =
      x (j.succAbove t) :=
  rfl

/-- Reparameterize one edge weight by the canonical `Fin n` face tuple. -/
noncomputable def canonicalEdgeFunction
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y => H.edgeWeight j (finTupleToDeletedVector j y)

/-- A regularity state for every edge colour. -/
abbrev SimplexRegularitySystem
    (G : Type*) (n : ℕ)
    [Fintype G] [DecidableEq G] :=
  (j : Fin (n + 1)) →
    FaceRegularityState (Fin n → G)

/-- Replace every edge weight by its conditional mean in the corresponding
regularity state. -/
noncomputable def regularizedSimplexSystem
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) :
    WeightedSimplexSystem (fun _ : Fin (n + 1) => G) where
  edgeWeight j x :=
    (S j).structured (canonicalEdgeFunction H j)
      (deletedFaceTuple j x)

@[simp]
theorem regularizedSimplexSystem_edge_finTuple
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    (j : Fin (n + 1)) (y : Fin n → G) :
    (regularizedSimplexSystem H S).edgeWeight j
        (finTupleToDeletedVector j y) =
      (S j).structured (canonicalEdgeFunction H j) y := by
  simp [regularizedSimplexSystem]

theorem canonicalEdgeFunction_nonneg
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) (y : Fin n → G) :
    0 ≤ canonicalEdgeFunction H j y :=
  (hH j (finTupleToDeletedVector j y)).1

theorem canonicalEdgeFunction_le_one
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) (y : Fin n → G) :
    canonicalEdgeFunction H j y ≤ 1 :=
  (hH j (finTupleToDeletedVector j y)).2

/-- Conditional averaging preserves the unit-interval edge bounds. -/
theorem regularizedSimplexSystem_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (S : SimplexRegularitySystem G n) :
    EdgeWeightsInUnitInterval (regularizedSimplexSystem H S) := by
  intro j x
  constructor
  · exact
      (S j).structured_nonneg
        (canonicalEdgeFunction_nonneg hH j)
        (deletedFaceTuple j x)
  · exact
      (S j).structured_le_one
        (canonicalEdgeFunction_le_one hH j)
        (deletedFaceTuple j x)

/-- The non-distinguished factors in an ordered simplex telescoping term. -/
def orderedSimplexEdgeFactor
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j i : Fin k) (x : Fin k → G) : ℝ :=
  (if i < j then H.edgeWeight i (deleteCoordinate x i) else 1) *
  (if j < i then K.edgeWeight i (deleteCoordinate x i) else 1)

@[simp]
theorem orderedSimplexEdgeFactor_self
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j : Fin k) (x : Fin k → G) :
    orderedSimplexEdgeFactor H K j j x = 1 := by
  simp [orderedSimplexEdgeFactor]

/-- Insert the omitted coordinate into a tuple presented with the
subtraction-based arity used by `eraseCoordinate`. -/
def insertErasedCoordinate
    {G : Type*} {n : ℕ} (t : Fin n) (a : G)
    (z : Fin (n - 1) → G) :
    Fin n → G := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m => exact Fin.insertNth t a z

@[simp]
theorem insertErasedCoordinate_eraseCoordinate
    {G : Type*} [DecidableEq G] {n : ℕ}
    (t : Fin n) (a : G) (y : Fin n → G) :
    insertErasedCoordinate t a (eraseCoordinate t y) =
      Function.update y t a := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m =>
      exact insertNth_eraseCoordinate_eq_update t a y

/-- After fixing the distinguished vertex, the other edge of colour
`j.succAbove t` is a function omitting face coordinate `t`. -/
def simplexMixedCutTest
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G) :
    CutTestFamily G n :=
  fun t z =>
    orderedSimplexEdgeFactor H K j (j.succAbove t)
      (Fin.insertNth j a (insertErasedCoordinate t a z))

/-- Evaluation on an erased tuple recovers the corresponding
non-distinguished edge factor. -/
theorem simplexMixedCutTest_eraseCoordinate
    {G : Type*} [DecidableEq G] {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (t : Fin n) (y : Fin n → G) :
    simplexMixedCutTest H K j a t (eraseCoordinate t y) =
      orderedSimplexEdgeFactor H K j (j.succAbove t)
        (Fin.insertNth j a y) := by
  rw [simplexMixedCutTest,
    insertErasedCoordinate_eraseCoordinate,
    Fin.insertNth_update]
  unfold orderedSimplexEdgeFactor
  simp only [deleteCoordinate_update_same]

/-- Unit-interval edge bounds make the reconstructed cut family bounded. -/
theorem simplexMixedCutTest_bounded
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) (a : G) :
    IsBoundedCutTest (simplexMixedCutTest H K j a) := by
  constructor
  · intro t z
    unfold simplexMixedCutTest orderedSimplexEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simp [htj, hjt, (hH _ _).1]
    · by_cases hjt : j < j.succAbove t
      · simp [htj, hjt, (hK _ _).1]
      · exact
          (Fin.succAbove_ne j t
            (le_antisymm (not_lt.mp hjt)
              (not_lt.mp htj))).elim
  · intro t z
    unfold simplexMixedCutTest orderedSimplexEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simpa [htj, hjt] using
        (hH (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j a (insertErasedCoordinate t a z))
            (j.succAbove t))).2
    · by_cases hjt : j < j.succAbove t
      · simpa [htj, hjt] using
          (hK (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j a (insertErasedCoordinate t a z))
              (j.succAbove t))).2
      · exact
          (Fin.succAbove_ne j t
            (le_antisymm (not_lt.mp hjt)
              (not_lt.mp htj))).elim

/-- The full product of ordered factors is the filtered product in the
telescoping definition. -/
theorem prod_orderedSimplexEdgeFactor
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j : Fin k) (x : Fin k → G) :
    (∏ i : Fin k, orderedSimplexEdgeFactor H K j i x) =
      (∏ i ∈ (Finset.univ : Finset (Fin k)) with i < j,
        H.edgeWeight i (deleteCoordinate x i)) *
      ∏ i ∈ (Finset.univ : Finset (Fin k)) with j < i,
        K.edgeWeight i (deleteCoordinate x i) := by
  rw [Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  rfl

/-- The reconstructed cut product is exactly the product of all
non-distinguished telescoping factors. -/
theorem prod_simplexMixedCutTest_eraseCoordinate
    {G : Type*} [DecidableEq G] {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (y : Fin n → G) :
    (∏ t : Fin n,
        simplexMixedCutTest H K j a t
          (eraseCoordinate t y)) =
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with i < j,
        H.edgeWeight i
          (deleteCoordinate (Fin.insertNth j a y) i)) *
      ∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with j < i,
        K.edgeWeight i
          (deleteCoordinate (Fin.insertNth j a y) i) := by
  simp_rw [simplexMixedCutTest_eraseCoordinate]
  calc
    (∏ t : Fin n,
        orderedSimplexEdgeFactor H K j (j.succAbove t)
          (Fin.insertNth j a y)) =
        ∏ i : Fin (n + 1),
          orderedSimplexEdgeFactor H K j i
            (Fin.insertNth j a y) := by
      symm
      calc
        (∏ i : Fin (n + 1),
            orderedSimplexEdgeFactor H K j i
              (Fin.insertNth j a y)) =
            orderedSimplexEdgeFactor H K j j
                (Fin.insertNth j a y) *
              ∏ t : Fin n,
                orderedSimplexEdgeFactor H K j
                  (j.succAbove t) (Fin.insertNth j a y) :=
          Fin.prod_univ_succAbove _ j
        _ =
            ∏ t : Fin n,
              orderedSimplexEdgeFactor H K j
                (j.succAbove t) (Fin.insertNth j a y) := by
          rw [orderedSimplexEdgeFactor_self, one_mul]
    _ = _ :=
      prod_orderedSimplexEdgeFactor H K j
        (Fin.insertNth j a y)

/-- Fixing coordinate `j` turns its mixed telescoping integrand into the
face residual paired with the reconstructed cut product. -/
theorem mixedSimplexTerm_regularized_insertNth
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    (j : Fin (n + 1)) (a : G) (y : Fin n → G) :
    mixedSimplexTerm H (regularizedSimplexSystem H S) j
        (Fin.insertNth j a y) =
      (S j).residual (canonicalEdgeFunction H j) y *
        cutTestProduct
          (simplexMixedCutTest H
            (regularizedSimplexSystem H S) j a) y := by
  have hHj :
      H.edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        canonicalEdgeFunction H j y := by
    simp [canonicalEdgeFunction,
      deleteCoordinate_eq_finTupleToDeletedVector]
  have hKj :
      (regularizedSimplexSystem H S).edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        (S j).structured (canonicalEdgeFunction H j) y := by
    simp [regularizedSimplexSystem,
      deleteCoordinate_eq_finTupleToDeletedVector]
  unfold mixedSimplexTerm FaceRegularityState.residual
  rw [hHj, hKj]
  rw [show
      cutTestProduct
          (simplexMixedCutTest H
            (regularizedSimplexSystem H S) j a) y =
        (∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with i < j,
          H.edgeWeight i
            (deleteCoordinate (Fin.insertNth j a y) i)) *
        ∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with j < i,
          (regularizedSimplexSystem H S).edgeWeight i
            (deleteCoordinate (Fin.insertNth j a y) i) by
      exact prod_simplexMixedCutTest_eraseCoordinate
        H (regularizedSimplexSystem H S) j a y]
  ring

/-- One mixed simplex correlation is the average over the fixed vertex of a
face-cut residual correlation. -/
theorem mixedSimplexCorrelation_regularized_eq_mean
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    (j : Fin (n + 1)) :
    mixedSimplexCorrelation H (regularizedSimplexSystem H S) j =
      mean (fun a : G =>
        (S j).faceCutCorrelation
          (canonicalEdgeFunction H j)
          (simplexMixedCutTest H
            (regularizedSimplexSystem H S) j a)) := by
  unfold mixedSimplexCorrelation
  rw [mean_insertNth n j]
  unfold mean₂
  apply congrArg mean
  funext a
  unfold FaceRegularityState.faceCutCorrelation
  apply congrArg mean
  funext y
  exact mixedSimplexTerm_regularized_insertNth H S j a y

/-- Cut regularity controls one mixed correlation in the weak counting
telescoping expansion. -/
theorem abs_mixedSimplexCorrelation_regularized_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (S : SimplexRegularitySystem G n)
    {ε : ℝ}
    (hregular :
      ∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε)
    (j : Fin (n + 1)) :
    |mixedSimplexCorrelation H
        (regularizedSimplexSystem H S) j| ≤ ε := by
  rw [mixedSimplexCorrelation_regularized_eq_mean]
  let K := regularizedSimplexSystem H S
  have hK : EdgeWeightsInUnitInterval K :=
    regularizedSimplexSystem_unitInterval hH S
  calc
    |mean (fun a : G =>
        (S j).faceCutCorrelation
          (canonicalEdgeFunction H j)
          (simplexMixedCutTest H K j a))| ≤
        mean (fun a : G =>
          |(S j).faceCutCorrelation
            (canonicalEdgeFunction H j)
            (simplexMixedCutTest H K j a)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : G => ε) := by
      apply mean_mono
      intro a
      exact hregular j
        (simplexMixedCutTest H K j a)
        (simplexMixedCutTest_bounded H K hH hK j a)
    _ = ε := mean_const _

/-- Uniform mixed-correlation bound for weakly regularized edge weights. -/
theorem regularizedSimplexSystem_mixedCorrelationLe
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (S : SimplexRegularitySystem G n)
    {ε : ℝ}
    (hregular :
      ∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε) :
    MixedSimplexCorrelationLe H
      (regularizedSimplexSystem H S) ε := by
  intro j
  exact abs_mixedSimplexCorrelation_regularized_le
    H hH S hregular j

/-- **Weak counting lemma.**  Simultaneous cut-regularity of all edge
residuals controls the normalized simplex count by one `ε` per colour. -/
theorem simplexCount_abs_sub_regularized_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (S : SimplexRegularitySystem G n)
    {ε : ℝ}
    (hregular :
      ∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε) :
    |H.simplexCount -
        (regularizedSimplexSystem H S).simplexCount| ≤
      ((n + 1 : ℕ) : ℝ) * ε :=
  simplexCount_abs_sub_le_of_mixedCorrelation
    H (regularizedSimplexSystem H S)
    (regularizedSimplexSystem_mixedCorrelationLe
      H hH S hregular)

/-- Regularize all edge colours independently and apply the weak counting
lemma.  Each output partition has an ambient-size-independent power-of-two
complexity bound relative to its input partition. -/
theorem exists_regularizedSimplexSystem_count_close
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (S₀ : SimplexRegularitySystem G n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : SimplexRegularitySystem G n,
      (∀ j, (S j).partition ≤ (S₀ j).partition) ∧
      (∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε) ∧
      |H.simplexCount -
          (regularizedSimplexSystem H S).simplexCount| ≤
        ((n + 1 : ℕ) : ℝ) * ε ∧
      ∀ j, ∃ m i : ℕ,
        1 < (m : ℝ) * ε ^ 2 ∧
        i < m ∧
        FacePartition.complexity (S j).partition ≤
          2 ^ i *
            FacePartition.complexity (S₀ j).partition := by
  classical
  have hj (j : Fin (n + 1)) :
      ∃ T : FaceRegularityState (Fin n → G),
        T.partition ≤ (S₀ j).partition ∧
        T.IsFaceCutRegular (canonicalEdgeFunction H j) ε ∧
        ∃ m i : ℕ,
          1 < (m : ℝ) * ε ^ 2 ∧
          i < m ∧
          FacePartition.complexity T.partition ≤
            2 ^ i *
              FacePartition.complexity (S₀ j).partition := by
    obtain ⟨m, i, T, hlong, hi, hTS, hregular, hcomplexity⟩ :=
      (S₀ j).exists_faceCutRegular_refinement
        (canonicalEdgeFunction H j)
        (canonicalEdgeFunction_nonneg hH j)
        (canonicalEdgeFunction_le_one hH j) hε
    exact
      ⟨T, hTS, hregular, m, i,
        hlong, hi, hcomplexity⟩
  choose S hS using hj
  refine
    ⟨S, fun j => (hS j).1, fun j => (hS j).2.1,
      ?_, fun j => (hS j).2.2⟩
  exact simplexCount_abs_sub_regularized_le
    H hH S (fun j => (hS j).2.1)

end Wikipedia.SzemeredisTheorem
