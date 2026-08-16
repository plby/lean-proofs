import Wikipedia.GreenTao.Transference.RecursiveRelativeSimplex
import Wikipedia.SzemeredisTheorem.Transference.SimplexCounting

/-!
# Re-embedding a projected relative count

The output of one AP densification step is a pairing on the deleted-face
space `Fin n → ZMod N`.  It is not, in general, another AP pullback family:
the truncated projected factor may depend on the whole deleted face.

It is nevertheless an exact weighted-simplex count.  This file puts an
arbitrary deleted-face function on one selected edge of an `(n + 1)`-partite
simplex and puts `1` on every other edge.  Its simplex count is exactly the
mean of that function, independently of the selected edge.  Applying this
to the product of the projected surrogate and the distinguished factor
gives a selectable full-simplex representation of the projected pairing at
any newly chosen colour.

The final section packages the analytic AP transition followed by this exact
reindexing as a genuine length-two `RelativeDensificationIteration`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A canonical one-edge simplex -/

/-- Canonical `Fin n` coordinates on a deleted face. -/
noncomputable def recursiveDeletedFaceTuple
    {G : Type*} {n : ℕ}
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

@[simp]
theorem recursiveDeletedFaceTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ}
    (j : Fin (n + 1)) (y : Fin n → G) :
    recursiveDeletedFaceTuple j
        (finTupleToDeletedVector j y) = y := by
  funext t
  simp [recursiveDeletedFaceTuple]

@[simp]
theorem recursiveDeletedFaceTuple_deleteCoordinate
    {G : Type*} {n : ℕ}
    (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    recursiveDeletedFaceTuple j (deleteCoordinate x j) =
      fun t => x (j.succAbove t) := by
  rfl

/-- A weighted simplex with one arbitrary edge function, placed at the
selected colour `j`, and constant-one weights on all other colours. -/
noncomputable def oneEdgeSimplexSystem
    {G : Type*} {n : ℕ}
    (F : (Fin n → G) → ℝ)
    (j : Fin (n + 1)) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G) where
  edgeWeight i x :=
    if h : i = j then
      F (recursiveDeletedFaceTuple j (h ▸ x))
    else 1

@[simp]
theorem oneEdgeSimplexSystem_edge_self
    {G : Type*} {n : ℕ}
    (F : (Fin n → G) → ℝ)
    (j : Fin (n + 1))
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) j) :
    (oneEdgeSimplexSystem F j).edgeWeight j x =
      F (recursiveDeletedFaceTuple j x) := by
  simp [oneEdgeSimplexSystem]

theorem oneEdgeSimplexSystem_edge_other
    {G : Type*} {n : ℕ}
    (F : (Fin n → G) → ℝ)
    (j i : Fin (n + 1)) (hij : i ≠ j)
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) i) :
    (oneEdgeSimplexSystem F j).edgeWeight i x = 1 := by
  simp [oneEdgeSimplexSystem, hij]

/-- Pointwise, the one-edge simplex weight is the selected deleted-face
function evaluated on the coordinates outside the selected colour. -/
@[simp]
theorem oneEdgeSimplexSystem_simplexWeight
    {G : Type*} {n : ℕ}
    (F : (Fin n → G) → ℝ)
    (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    (oneEdgeSimplexSystem F j).simplexWeight x =
      F (fun t => x (j.succAbove t)) := by
  rw [WeightedSimplexSystem.simplexWeight,
    Fin.prod_univ_succAbove _ j,
    oneEdgeSimplexSystem_edge_self]
  have htail :
      (∏ t : Fin n,
        (oneEdgeSimplexSystem F j).edgeWeight
          (j.succAbove t)
          (deleteCoordinate x (j.succAbove t))) = 1 := by
    apply Fintype.prod_eq_one
    intro t
    exact oneEdgeSimplexSystem_edge_other
      F j (j.succAbove t) (Fin.succAbove_ne j t) _
  rw [htail, mul_one]
  rfl

/-- The normalized count of the one-edge simplex is exactly the normalized
mean of its edge function.  The omitted coordinate is a uniform fiber. -/
@[simp]
theorem oneEdgeSimplexSystem_simplexCount
    {G : Type*} [Fintype G] [Nonempty G]
    {n : ℕ}
    (F : (Fin n → G) → ℝ)
    (j : Fin (n + 1)) :
    (oneEdgeSimplexSystem F j).simplexCount = mean F := by
  rw [WeightedSimplexSystem.simplexCount, mean_insertNth n j]
  unfold mean₂
  calc
    mean (fun a : G =>
        mean (fun y : Fin n → G =>
          (oneEdgeSimplexSystem F j).simplexWeight
            (Fin.insertNth j a y))) =
        mean (fun _ : G => mean F) := by
      apply congrArg mean
      funext a
      apply congrArg mean
      funext y
      simp
    _ = mean F := mean_const _

/-- Unit-interval bounds on the selected edge are exactly enough to make
the full one-edge simplex unit-interval valued. -/
theorem oneEdgeSimplexSystem_unitInterval
    {G : Type*} {n : ℕ}
    {F : (Fin n → G) → ℝ}
    (hF : ∀ y, 0 ≤ F y ∧ F y ≤ 1)
    (j : Fin (n + 1)) :
    EdgeWeightsInUnitInterval
      (oneEdgeSimplexSystem F j) := by
  intro i x
  by_cases hij : i = j
  · subst i
    simpa using hF (recursiveDeletedFaceTuple j x)
  · simp [oneEdgeSimplexSystem, hij]

/-! ## The projected AP pairing as a selectable simplex -/

/-- The bounded deleted-face function which is counted after one
heterogeneous AP densification step. -/
noncomputable def apProjectedPairingEdge
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  fun y =>
    apHeterogeneousProjectedSurrogate n N g j y *
      apHeterogeneousDistinguishedFaceWeight n N g j y

/-- Re-embed a projected AP pairing as a full simplex whose only
nonconstant edge is placed at the newly selected colour `next`. -/
noncomputable def apProjectedPairingSimplexSystem
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (previous next : Fin (n + 1)) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N) :=
  oneEdgeSimplexSystem
    (apProjectedPairingEdge n N g previous) next

/-- Exact recursive count representation: the projected lower-face pairing
is the full simplex count of the re-embedded one-edge system, at any newly
chosen colour. -/
theorem apProjectedPairingSimplexCount_eq
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (previous next : Fin (n + 1)) :
    (apProjectedPairingSimplexSystem
        n N g previous next).simplexCount =
      apHeterogeneousDensifiedPairing n N g previous := by
  rw [apProjectedPairingSimplexSystem,
    oneEdgeSimplexSystem_simplexCount]
  rfl

/-- The projected-pairing edge is in `[0,1]` whenever the old chosen edge
and all old untouched weights satisfy the hypotheses of one densification
step. -/
theorem apProjectedPairingEdge_mem_unitInterval
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {previous : Fin (n + 1)}
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν previous)
    (y : Fin n → ZMod N) :
    0 ≤ apProjectedPairingEdge n N g previous y ∧
      apProjectedPairingEdge n N g previous y ≤ 1 := by
  have hsurrogate :=
    apHeterogeneousProjectedSurrogate_mem_unitInterval hrest y
  have hdistinguished :=
    apHeterogeneousDistinguishedFaceWeight_mem_unitInterval
      hprevious y
  constructor
  · exact mul_nonneg hsurrogate.1 hdistinguished.1
  · calc
      apProjectedPairingEdge n N g previous y ≤
          1 *
            apHeterogeneousDistinguishedFaceWeight
              n N g previous y := by
        exact mul_le_mul_of_nonneg_right
          hsurrogate.2 hdistinguished.1
      _ ≤ 1 := by simpa using hdistinguished.2

/-- The re-embedded projected count is an admissible fully bounded
weighted simplex, regardless of which colour is selected next. -/
theorem apProjectedPairingSimplexSystem_unitInterval
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {previous : Fin (n + 1)}
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν previous)
    (next : Fin (n + 1)) :
    EdgeWeightsInUnitInterval
      (apProjectedPairingSimplexSystem
        n N g previous next) := by
  exact oneEdgeSimplexSystem_unitInterval
    (apProjectedPairingEdge_mem_unitInterval
      hprevious hrest) next

/-! ## A recursive payload and exact refactor state -/

/-- A projected pairing re-embedded as a selectable full weighted simplex. -/
structure APRecursiveSelectablePayload (n N : ℕ) where
  previous : Fin (n + 1)
  chosen : Fin (n + 1)
  edge : (Fin n → ZMod N) → ℝ

/-- The weighted simplex represented by a selectable payload. -/
noncomputable def APRecursiveSelectablePayload.system
    {n N : ℕ}
    (data : APRecursiveSelectablePayload n N) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N) :=
  oneEdgeSimplexSystem data.edge data.chosen

/-- Its canonical scalar count. -/
noncomputable def APRecursiveSelectablePayload.count
    {n N : ℕ} [NeZero N]
    (data : APRecursiveSelectablePayload n N) : ℝ :=
  data.system.simplexCount

/-- The exact admissibility retained by the recursive representation. -/
def APRecursiveSelectablePayload.IsAdmissible
    {n N : ℕ}
    (data : APRecursiveSelectablePayload n N) : Prop :=
  ∀ y, 0 ≤ data.edge y ∧ data.edge y ≤ 1

/-- The selectable payload canonically associated to an AP projected
pairing. -/
noncomputable def apRecursiveSelectablePayload
    {n N : ℕ} [NeZero N]
    (g : APFaceWeightFamily n N)
    (previous next : Fin (n + 1)) :
    APRecursiveSelectablePayload n N where
  previous := previous
  chosen := next
  edge := apProjectedPairingEdge n N g previous

@[simp]
theorem apRecursiveSelectablePayload_count
    {n N : ℕ} [NeZero N]
    (g : APFaceWeightFamily n N)
    (previous next : Fin (n + 1)) :
    (apRecursiveSelectablePayload g previous next).count =
      apHeterogeneousDensifiedPairing n N g previous := by
  exact apProjectedPairingSimplexCount_eq
    n N g previous next

theorem apRecursiveSelectablePayload_admissible
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {previous : Fin (n + 1)}
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν previous)
    (next : Fin (n + 1)) :
    (apRecursiveSelectablePayload
      g previous next).IsAdmissible :=
  apProjectedPairingEdge_mem_unitInterval hprevious hrest

/-! ## Two certified transitions: densify, then reindex -/

/-- Payload type for the analytic AP state followed by its exact selectable
re-embedding. -/
inductive APRecursiveCountPayload (n N : ℕ)
  | ap : APRelativeSimplexPayload n N →
      APRecursiveCountPayload n N
  | selectable : APRecursiveSelectablePayload n N →
      APRecursiveCountPayload n N

/-- Canonical count of either recursive payload constructor. -/
noncomputable def apRecursiveCountPayloadCount
    (n N : ℕ) [NeZero N] :
    APRecursiveCountPayload n N → ℝ
  | .ap data => apRelativeSimplexPayloadCount n N data
  | .selectable data => data.count

/-- Stage-specific admissibility for the recursive chain. -/
def APRecursiveCountPayload.IsAdmissible
    {n N : ℕ} :
    APRecursiveCountPayload n N → Prop
  | .ap data => data.IsAdmissible
  | .selectable data => data.IsAdmissible

/-- Application invariant for the analytic step and the exact reindexing
step. -/
def APRecursiveCountStateInvariant
    (n N : ℕ) [NeZero N]
    (state :
      RelativeDensificationState
        (APRecursiveCountPayload n N)) : Prop :=
  state.count =
      apRecursiveCountPayloadCount n N state.payload ∧
    state.payload.IsAdmissible

noncomputable def apRecursiveFullState
    {n N : ℕ} [NeZero N]
    (g ν : APFaceWeightFamily n N)
    (previous : Fin (n + 1)) :
    RelativeDensificationState
      (APRecursiveCountPayload n N) where
  payload := .ap (apRelativeSimplexFullPayload g ν previous)
  count := (apHeterogeneousSimplexSystem n N g).simplexCount

noncomputable def apRecursiveProjectedState
    {n N : ℕ} [NeZero N]
    (g ν : APFaceWeightFamily n N)
    (previous : Fin (n + 1)) :
    RelativeDensificationState
      (APRecursiveCountPayload n N) where
  payload := .ap (apRelativeSimplexProjectedPayload g ν previous)
  count := apHeterogeneousDensifiedPairing n N g previous

noncomputable def apRecursiveSelectableState
    {n N : ℕ} [NeZero N]
    (g : APFaceWeightFamily n N)
    (previous next : Fin (n + 1)) :
    RelativeDensificationState
      (APRecursiveCountPayload n N) where
  payload := .selectable
    (apRecursiveSelectablePayload g previous next)
  count := apHeterogeneousDensifiedPairing n N g previous

theorem apRecursiveFullState_valid
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {previous : Fin (n + 1)}
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν previous) :
    APRecursiveCountStateInvariant n N
      (apRecursiveFullState g ν previous) := by
  exact ⟨rfl, hprevious, hrest⟩

theorem apRecursiveProjectedState_valid
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {previous : Fin (n + 1)}
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν previous) :
    APRecursiveCountStateInvariant n N
      (apRecursiveProjectedState g ν previous) := by
  exact
    ⟨rfl,
      apHeterogeneousDistinguishedFaceWeight_mem_unitInterval
        hprevious,
      apHeterogeneousProjectedSurrogate_mem_unitInterval hrest,
      apUntouchedFaceWeights_bounds hrest⟩

theorem apRecursiveSelectableState_valid
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {previous : Fin (n + 1)}
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν previous)
    (next : Fin (n + 1)) :
    APRecursiveCountStateInvariant n N
      (apRecursiveSelectableState g previous next) := by
  exact
    ⟨(apRecursiveSelectablePayload_count
        g previous next).symm,
      apRecursiveSelectablePayload_admissible
        hprevious hrest next⟩

/-- The reindexing transition has exactly zero count loss. -/
theorem apRecursiveProjectedToSelectableCountLoss
    {n N : ℕ} [NeZero N]
    (g ν : APFaceWeightFamily n N)
    (previous next : Fin (n + 1)) :
    RelativeDensificationCountLoss
      (apRecursiveProjectedState g ν previous)
      (apRecursiveSelectableState g previous next)
      0 := by
  simp [RelativeDensificationCountLoss,
    apRecursiveProjectedState, apRecursiveSelectableState]

/-- One masked AP densification step followed by the exact re-embedding at
a newly selected colour is a genuine certified iteration of length two. -/
noncomputable def HasLinearFormsCondition.apMaskedRecursiveTwoStepIteration
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    {g : APFaceWeightFamily n N}
    (previous next : Fin (n + 1))
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν active) previous) :
    RelativeDensificationIteration
      (APRecursiveCountPayload n N)
      (APRecursiveCountStateInvariant n N) where
  length := 2
  state
    | 0 =>
        apRecursiveFullState g
          (apMaskedFaceMajorant ν active) previous
    | 1 =>
        apRecursiveProjectedState g
          (apMaskedFaceMajorant ν active) previous
    | _ =>
        apRecursiveSelectableState g previous next
  error
    | 0 => Real.sqrt (3 * η)
    | _ => 0
  valid := by
    intro i hi
    interval_cases i
    · exact apRecursiveFullState_valid hprevious hrest
    · exact apRecursiveProjectedState_valid hprevious hrest
    · exact apRecursiveSelectableState_valid
        hprevious hrest next
  countLoss := by
    intro i hi
    interval_cases i
    · exact hLF.apMaskedRelativeSimplexStateTransition
        hν active previous hprevious hrest
    · exact apRecursiveProjectedToSelectableCountLoss
        g (apMaskedFaceMajorant ν active) previous next

@[simp]
theorem HasLinearFormsCondition.apMaskedRecursiveTwoStepIteration_length
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    {g : APFaceWeightFamily n N}
    (previous next : Fin (n + 1))
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν active) previous) :
    (hLF.apMaskedRecursiveTwoStepIteration
      hν active previous next hprevious hrest).length = 2 :=
  rfl

@[simp]
theorem HasLinearFormsCondition.apMaskedRecursiveTwoStepIteration_totalError
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    {g : APFaceWeightFamily n N}
    (previous next : Fin (n + 1))
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν active) previous) :
    (hLF.apMaskedRecursiveTwoStepIteration
      hν active previous next hprevious hrest).totalError =
        Real.sqrt (3 * η) := by
  norm_num [RelativeDensificationIteration.totalError,
    HasLinearFormsCondition.apMaskedRecursiveTwoStepIteration,
    Finset.sum_range_succ]

end Wikipedia.SzemeredisTheorem
