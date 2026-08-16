import Wikipedia.GreenTao.Transference.RecursiveRelativeCount

/-!
# A relative densification step for arbitrary simplex edge functions

The AP-specific transition works with edge functions pulled back from one
function on `ZMod N`.  After re-embedding a projected pairing, however, the
only nonconstant edge is an arbitrary function on its whole deleted-face
space.  This file formulates projection and truncation directly for a
`WeightedSimplexSystem`.

For a fully bounded system the constant-one simplex is a pointwise
majorant.  Its projected majorant is identically one, so its first and
second moment errors are exactly zero.  The resulting generic transition
therefore has zero loss.  In particular it consumes the selectable endpoint
constructed in `RecursiveRelativeCount`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projection of an arbitrary weighted simplex -/

/-- Product of all edge weights except colour `j`, after inserting the
missing `j` coordinate. -/
def generalSimplexIncidentProduct
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) : ℝ :=
  ∏ t : Fin n,
    H.edgeWeight (j.succAbove t)
      (deleteCoordinate (Fin.insertNth j a y)
        (j.succAbove t))

/-- Conditional projection of all non-distinguished edge weights. -/
noncomputable def generalSimplexProjectedWeight
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y => mean fun a =>
    generalSimplexIncidentProduct H j a y

/-- Truncation of the arbitrary projected weight at one. -/
noncomputable def generalSimplexProjectedSurrogate
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  truncateAtOne (generalSimplexProjectedWeight H j)

/-- Distinguished edge in canonical `Fin n` deleted-face coordinates. -/
noncomputable def generalSimplexDistinguishedWeight
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y => H.edgeWeight j (finTupleToDeletedVector j y)

/-- The pairing after truncating the arbitrary projection. -/
noncomputable def generalSimplexDensifiedPairing
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) : ℝ :=
  mean fun y =>
    generalSimplexProjectedSurrogate H j y *
      generalSimplexDistinguishedWeight H j y

/-- Inserting the missing coordinate factors the simplex weight into the
incident product and the distinguished edge. -/
theorem generalSimplexWeight_insertNth
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) :
    H.simplexWeight (Fin.insertNth j a y) =
      generalSimplexIncidentProduct H j a y *
        generalSimplexDistinguishedWeight H j y := by
  rw [WeightedSimplexSystem.simplexWeight,
    Fin.prod_univ_succAbove _ j]
  have hdistinguished :
      H.edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        generalSimplexDistinguishedWeight H j y := by
    simp [generalSimplexDistinguishedWeight,
      deleteCoordinate_eq_finTupleToDeletedVector]
  rw [hdistinguished, mul_comm]
  rfl

/-- Exact arbitrary-simplex projection identity. -/
theorem generalSimplexCount_eq_projectedPairing
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    H.simplexCount =
      mean (fun y =>
        generalSimplexProjectedWeight H j y *
          generalSimplexDistinguishedWeight H j y) := by
  rw [WeightedSimplexSystem.simplexCount,
    mean_insertNth n j, mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext y
  calc
    mean (fun a : G =>
        H.simplexWeight (Fin.insertNth j a y)) =
        mean (fun a : G =>
          generalSimplexIncidentProduct H j a y *
            generalSimplexDistinguishedWeight H j y) := by
      apply congrArg mean
      funext a
      exact generalSimplexWeight_insertNth H j a y
    _ = mean (fun a : G =>
          generalSimplexDistinguishedWeight H j y *
            generalSimplexIncidentProduct H j a y) := by
      apply congrArg mean
      funext a
      ring
    _ = generalSimplexDistinguishedWeight H j y *
        mean (fun a : G =>
          generalSimplexIncidentProduct H j a y) :=
      mean_smul _ _
    _ = generalSimplexProjectedWeight H j y *
        generalSimplexDistinguishedWeight H j y := by
      rw [mul_comm]
      rfl

/-! ## Pointwise bounds and projected domination -/

/-- Bounds on precisely the edges untouched when projecting at `j`. -/
def GeneralSimplexUntouchedBounds
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) : Prop :=
  ∀ t x,
    0 ≤ H.edgeWeight (j.succAbove t) x ∧
      H.edgeWeight (j.succAbove t) x ≤
        K.edgeWeight (j.succAbove t) x

theorem generalSimplexIncidentProduct_nonneg
    {G : Type*} {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (a : G) (y : Fin n → G) :
    0 ≤ generalSimplexIncidentProduct H j a y :=
  Finset.prod_nonneg fun t _ => (h t _).1

theorem generalSimplexIncidentProduct_mono
    {G : Type*} {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (a : G) (y : Fin n → G) :
    generalSimplexIncidentProduct H j a y ≤
      generalSimplexIncidentProduct K j a y := by
  unfold generalSimplexIncidentProduct
  exact Finset.prod_le_prod
    (fun t _ => (h t _).1)
    (fun t _ => (h t _).2)

theorem generalSimplexProjectedWeight_nonneg
    {G : Type*} [Fintype G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (y : Fin n → G) :
    0 ≤ generalSimplexProjectedWeight H j y :=
  mean_nonneg fun a =>
    generalSimplexIncidentProduct_nonneg h a y

theorem generalSimplexProjectedWeight_mono
    {G : Type*} [Fintype G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (y : Fin n → G) :
    generalSimplexProjectedWeight H j y ≤
      generalSimplexProjectedWeight K j y :=
  mean_mono fun a =>
    generalSimplexIncidentProduct_mono h a y

theorem generalSimplexProjectedSurrogate_mem_unitInterval
    {G : Type*} [Fintype G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (y : Fin n → G) :
    0 ≤ generalSimplexProjectedSurrogate H j y ∧
      generalSimplexProjectedSurrogate H j y ≤ 1 :=
  truncateAtOne_mem_unitInterval
    (generalSimplexProjectedWeight_nonneg h) y

theorem generalSimplexDistinguishedWeight_mem_unitInterval
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (hj : ∀ x,
      0 ≤ H.edgeWeight j x ∧ H.edgeWeight j x ≤ 1)
    (y : Fin n → G) :
    0 ≤ generalSimplexDistinguishedWeight H j y ∧
      generalSimplexDistinguishedWeight H j y ≤ 1 :=
  hj _

/-! ## The generic analytic transition -/

/-- Projected-majorant moments give the truncation loss for an arbitrary
weighted simplex; no AP-form representation is used. -/
theorem HasProjectedMajorantMoments.abs_generalSimplexCount_sub_densifiedPairing_le
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {η : ℝ} {j : Fin (n + 1)}
    (hMoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight K j) η)
    (hj : ∀ x,
      0 ≤ H.edgeWeight j x ∧ H.edgeWeight j x ≤ 1)
    (hrest : GeneralSimplexUntouchedBounds H K j) :
    |H.simplexCount -
        generalSimplexDensifiedPairing H j| ≤
      Real.sqrt (3 * η) := by
  rw [generalSimplexCount_eq_projectedPairing]
  have hface :
      ∀ y, |generalSimplexDistinguishedWeight H j y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg]
    · exact (generalSimplexDistinguishedWeight_mem_unitInterval
        hj y).2
    · exact (generalSimplexDistinguishedWeight_mem_unitInterval
        hj y).1
  simpa [generalSimplexDensifiedPairing,
    generalSimplexProjectedSurrogate] using
    hMoments.abs_mean_mul_sub_truncateAtOne_mul_le_sqrt
      (generalSimplexProjectedWeight_mono hrest) hface

/-! ## The constant-one majorant -/

/-- The constant-one weighted simplex. -/
def oneWeightedSimplexSystem
    (G : Type*) (n : ℕ) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G) where
  edgeWeight _ _ := 1

@[simp]
theorem oneWeightedSimplexSystem_edge
    {G : Type*} {n : ℕ}
    (j : Fin (n + 1))
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) j) :
    (oneWeightedSimplexSystem G n).edgeWeight j x = 1 :=
  rfl

@[simp]
theorem generalSimplexIncidentProduct_one
    {G : Type*} {n : ℕ}
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) :
    generalSimplexIncidentProduct
      (oneWeightedSimplexSystem G n) j a y = 1 := by
  simp [generalSimplexIncidentProduct,
    oneWeightedSimplexSystem]

@[simp]
theorem generalSimplexProjectedWeight_one
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    (j : Fin (n + 1)) :
    generalSimplexProjectedWeight
      (oneWeightedSimplexSystem G n) j =
        fun _ => 1 := by
  funext y
  simp [generalSimplexProjectedWeight]

/-- The projected constant-one majorant has exact first and second moments,
hence moment error zero. -/
theorem hasProjectedMajorantMoments_generalSimplexOne
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    (j : Fin (n + 1)) :
    HasProjectedMajorantMoments
      (generalSimplexProjectedWeight
        (oneWeightedSimplexSystem G n) j) 0 := by
  rw [generalSimplexProjectedWeight_one]
  refine
    { error_nonneg := le_rfl
      nonneg := fun _ => zero_le_one
      firstMoment_close := ?_
      secondMoment_close := ?_ }
  · simp
  · simp

/-- Every fully bounded simplex is dominated, on its untouched edges, by
the constant-one simplex. -/
theorem EdgeWeightsInUnitInterval.generalSimplexUntouchedBounds_one
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) :
    GeneralSimplexUntouchedBounds H
      (oneWeightedSimplexSystem G n) j := by
  intro t x
  exact hH (j.succAbove t) x

/-- With the constant-one majorant, a fully bounded simplex undergoes the
generic projection/truncation transition with zero count loss. -/
theorem EdgeWeightsInUnitInterval.generalSimplexCount_eq_densifiedPairing
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) :
    H.simplexCount =
      generalSimplexDensifiedPairing H j := by
  have hloss :=
    (hasProjectedMajorantMoments_generalSimplexOne j).abs_generalSimplexCount_sub_densifiedPairing_le
      (fun x => hH j x)
      (hH.generalSimplexUntouchedBounds_one j)
  have hzero :
      |H.simplexCount -
          generalSimplexDensifiedPairing H j| ≤ 0 := by
    simpa using hloss
  exact sub_eq_zero.mp <|
    abs_eq_zero.mp <|
      le_antisymm hzero (abs_nonneg _)

/-! ## Generic full and projected states -/

structure GeneralRelativeSimplexFullPayload
    (G : Type*) (n : ℕ) where
  system : WeightedSimplexSystem
    (fun _ : Fin (n + 1) => G)
  chosen : Fin (n + 1)

structure GeneralRelativeSimplexProjectedPayload
    (G : Type*) (n : ℕ) where
  chosen : Fin (n + 1)
  distinguished : (Fin n → G) → ℝ
  surrogate : (Fin n → G) → ℝ

inductive GeneralRelativeSimplexPayload
    (G : Type*) (n : ℕ)
  | full : GeneralRelativeSimplexFullPayload G n →
      GeneralRelativeSimplexPayload G n
  | projected : GeneralRelativeSimplexProjectedPayload G n →
      GeneralRelativeSimplexPayload G n

noncomputable def generalRelativeSimplexPayloadCount
    (G : Type*) [Fintype G] (n : ℕ) :
    GeneralRelativeSimplexPayload G n → ℝ
  | .full data => data.system.simplexCount
  | .projected data =>
      mean fun y => data.surrogate y * data.distinguished y

def GeneralRelativeSimplexPayload.IsAdmissible
    {G : Type*} {n : ℕ} :
    GeneralRelativeSimplexPayload G n → Prop
  | .full data => EdgeWeightsInUnitInterval data.system
  | .projected data =>
      (∀ y,
        0 ≤ data.distinguished y ∧ data.distinguished y ≤ 1) ∧
      ∀ y, 0 ≤ data.surrogate y ∧ data.surrogate y ≤ 1

def GeneralRelativeSimplexStateInvariant
    (G : Type*) [Fintype G] (n : ℕ)
    (state :
      RelativeDensificationState
        (GeneralRelativeSimplexPayload G n)) : Prop :=
  state.count =
      generalRelativeSimplexPayloadCount G n state.payload ∧
    state.payload.IsAdmissible

noncomputable def generalRelativeSimplexFullState
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    RelativeDensificationState
      (GeneralRelativeSimplexPayload G n) where
  payload := .full { system := H, chosen := j }
  count := H.simplexCount

noncomputable def generalRelativeSimplexProjectedState
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    RelativeDensificationState
      (GeneralRelativeSimplexPayload G n) where
  payload := .projected
    { chosen := j
      distinguished := generalSimplexDistinguishedWeight H j
      surrogate := generalSimplexProjectedSurrogate H j }
  count := generalSimplexDensifiedPairing H j

theorem generalRelativeSimplexFullState_valid
    {G : Type*} [Fintype G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) :
    GeneralRelativeSimplexStateInvariant G n
      (generalRelativeSimplexFullState H j) :=
  ⟨rfl, hH⟩

theorem generalRelativeSimplexProjectedState_valid
    {G : Type*} [Fintype G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) :
    GeneralRelativeSimplexStateInvariant G n
      (generalRelativeSimplexProjectedState H j) := by
  refine
    ⟨rfl,
      generalSimplexDistinguishedWeight_mem_unitInterval
        (fun x => hH j x),
      generalSimplexProjectedSurrogate_mem_unitInterval
        (hH.generalSimplexUntouchedBounds_one j)⟩

/-- The generic constant-one transition as a certified one-step
iteration. -/
noncomputable def EdgeWeightsInUnitInterval.generalRelativeSimplexOneStepIteration
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) :
    RelativeDensificationIteration
      (GeneralRelativeSimplexPayload G n)
      (GeneralRelativeSimplexStateInvariant G n) :=
  RelativeDensificationIteration.single
    (generalRelativeSimplexFullState H j)
    (generalRelativeSimplexProjectedState H j)
    0
    (generalRelativeSimplexFullState_valid hH j)
    (generalRelativeSimplexProjectedState_valid hH j)
    (by
      unfold RelativeDensificationCountLoss
      change
        |H.simplexCount -
          generalSimplexDensifiedPairing H j| ≤ 0
      rw [hH.generalSimplexCount_eq_densifiedPairing j,
        sub_self, abs_zero])

@[simp]
theorem EdgeWeightsInUnitInterval.generalRelativeSimplexOneStepIteration_totalError
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) :
    (hH.generalRelativeSimplexOneStepIteration j).totalError = 0 := by
  simp [RelativeDensificationIteration.totalError,
    EdgeWeightsInUnitInterval.generalRelativeSimplexOneStepIteration,
    RelativeDensificationIteration.single]

/-! ## Consuming the recursive selectable endpoint -/

theorem APRecursiveSelectablePayload.system_unitInterval
    {n N : ℕ}
    {data : APRecursiveSelectablePayload n N}
    (hdata : data.IsAdmissible) :
    EdgeWeightsInUnitInterval data.system :=
  oneEdgeSimplexSystem_unitInterval hdata data.chosen

/-- The arbitrary whole-face endpoint from `RecursiveRelativeCount` is a
valid input to the generic analytic transition at any next colour. -/
noncomputable def APRecursiveSelectablePayload.generalRelativeSimplexOneStepIteration
    {n N : ℕ} [NeZero N]
    {data : APRecursiveSelectablePayload n N}
    (hdata : data.IsAdmissible)
    (next : Fin (n + 1)) :
    RelativeDensificationIteration
      (GeneralRelativeSimplexPayload (ZMod N) n)
      (GeneralRelativeSimplexStateInvariant (ZMod N) n) :=
  (data.system_unitInterval hdata).generalRelativeSimplexOneStepIteration
    next

@[simp]
theorem APRecursiveSelectablePayload.generalRelativeSimplexOneStepIteration_initialCount
    {n N : ℕ} [NeZero N]
    {data : APRecursiveSelectablePayload n N}
    (hdata : data.IsAdmissible)
    (next : Fin (n + 1)) :
    (data.generalRelativeSimplexOneStepIteration
      hdata next).initialCount = data.count :=
  rfl

@[simp]
theorem APRecursiveSelectablePayload.generalRelativeSimplexOneStepIteration_totalError
    {n N : ℕ} [NeZero N]
    {data : APRecursiveSelectablePayload n N}
    (hdata : data.IsAdmissible)
    (next : Fin (n + 1)) :
    (data.generalRelativeSimplexOneStepIteration
      hdata next).totalError = 0 :=
  (data.system_unitInterval hdata).generalRelativeSimplexOneStepIteration_totalError
    next

/-- Specialization to the selectable payload constructed from an AP
projected pairing.  This theorem is the direct handoff from the length-two
chain to a further generic analytic transition. -/
noncomputable def apMaskedRecursiveEndpointNextIteration
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    (active : Fin (n + 1) → Bool)
    {g : APFaceWeightFamily n N}
    (previous embeddedAt next : Fin (n + 1))
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν active) previous) :
    RelativeDensificationIteration
      (GeneralRelativeSimplexPayload (ZMod N) n)
      (GeneralRelativeSimplexStateInvariant (ZMod N) n) := by
  let data :=
    apRecursiveSelectablePayload g previous embeddedAt
  have hdata : data.IsAdmissible :=
    apRecursiveSelectablePayload_admissible
      hprevious hrest embeddedAt
  exact data.generalRelativeSimplexOneStepIteration hdata next

@[simp]
theorem apMaskedRecursiveEndpointNextIteration_initialCount
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    (active : Fin (n + 1) → Bool)
    {g : APFaceWeightFamily n N}
    (previous embeddedAt next : Fin (n + 1))
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν active) previous) :
    (apMaskedRecursiveEndpointNextIteration
      active previous embeddedAt next
      hprevious hrest).initialCount =
        apHeterogeneousDensifiedPairing n N g previous := by
  simp [apMaskedRecursiveEndpointNextIteration]

@[simp]
theorem apMaskedRecursiveEndpointNextIteration_totalError
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    (active : Fin (n + 1) → Bool)
    {g : APFaceWeightFamily n N}
    (previous embeddedAt next : Fin (n + 1))
    (hprevious :
      ∀ z, 0 ≤ g previous z ∧ g previous z ≤ 1)
    (hrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν active) previous) :
    (apMaskedRecursiveEndpointNextIteration
      active previous embeddedAt next
      hprevious hrest).totalError = 0 := by
  simp [apMaskedRecursiveEndpointNextIteration]

end Wikipedia.SzemeredisTheorem
