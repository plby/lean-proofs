import Wikipedia.GreenTao.Transference.RelativeDensificationIteration

/-!
# Heterogeneous AP-simplex densification states

The one-colour calculation in `RelativeDensification` uses one common
function on every non-distinguished AP face.  This file performs the same
calculation for a family of face weights `g i`.  For a chosen colour `j`,
the product of all other colours is averaged over the missing `j`
coordinate, then truncated at one on the actual deleted-face space
`Fin n → ZMod N`.

The final section packages the full simplex count and the resulting
lower-arity pairing as two different constructors of one payload type.  In
particular, the projected state is not falsely identified with another
`(n + 1)`-colour AP simplex.  It records the bounded surrogate on its real
domain and separately transports all untouched pointwise majorant bounds
along `j.succAbove`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Heterogeneous AP face systems -/

/-- One real weight on `ZMod N` for every colour of the canonical
`(n + 1)`-colour AP simplex. -/
abbrev APFaceWeightFamily (n N : ℕ) :=
  (i : Fin (n + 1)) → ZMod N → ℝ

/-- The AP-simplex system associated to a heterogeneous family of face
weights. -/
def apHeterogeneousSimplexSystem
    (n N : ℕ) (g : APFaceWeightFamily n N) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N) where
  edgeWeight i x :=
    g i (apSimplexForm (n + 1) N i x)

@[simp]
theorem apHeterogeneousSimplexSystem_edge
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (i : Fin (n + 1))
    (x : DeletedVector
      (fun _ : Fin (n + 1) => ZMod N) i) :
    (apHeterogeneousSimplexSystem n N g).edgeWeight i x =
      g i (apSimplexForm (n + 1) N i x) :=
  rfl

/-- Product of all heterogeneous AP face weights except colour `j`, after
inserting the missing `j` coordinate. -/
def apHeterogeneousIncidentProduct
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) : ℝ :=
  ∏ t : Fin n,
    g (j.succAbove t)
      (apSimplexForm (n + 1) N (j.succAbove t)
        (deleteCoordinate (Fin.insertNth j a y)
          (j.succAbove t)))

/-- Conditional projection of the heterogeneous non-`j` product onto the
deleted `j` face. -/
noncomputable def apHeterogeneousProjectedWeight
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  fun y =>
    mean (fun a =>
      apHeterogeneousIncidentProduct n N g j a y)

/-- The projected heterogeneous product truncated on its genuine
`Fin n → ZMod N` face space. -/
noncomputable def apHeterogeneousProjectedSurrogate
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  truncateAtOne (apHeterogeneousProjectedWeight n N g j)

@[simp]
theorem apHeterogeneousProjectedSurrogate_apply
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (y : Fin n → ZMod N) :
    apHeterogeneousProjectedSurrogate n N g j y =
      min (apHeterogeneousProjectedWeight n N g j y) 1 :=
  rfl

/-- The chosen AP face written in canonical deleted-face coordinates. -/
noncomputable def apHeterogeneousDistinguishedFaceWeight
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (y : Fin n → ZMod N) : ℝ :=
  g j (apSimplexForm (n + 1) N j
    (finTupleToDeletedVector j y))

/-- A concise predicate for the bounds on precisely the colours untouched
by projection at `j`. -/
def APUntouchedFaceBounds
    {n N : ℕ}
    (g ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) : Prop :=
  ∀ t z,
    0 ≤ g (j.succAbove t) z ∧
      g (j.succAbove t) z ≤ ν (j.succAbove t) z

/-- Reindex the untouched weights by the canonical `Fin n` enumeration of
colours other than `j`. -/
def apUntouchedFaceWeights
    {n N : ℕ}
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (t : Fin n) → ZMod N → ℝ :=
  fun t => g (j.succAbove t)

/-- Reindex the untouched majorants in the same way. -/
def apUntouchedFaceMajorants
    {n N : ℕ}
    (ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (t : Fin n) → ZMod N → ℝ :=
  fun t => ν (j.succAbove t)

/-- Reindexing along `j.succAbove` preserves every untouched pointwise
relative-majorant bound. -/
theorem apUntouchedFaceWeights_bounds
    {n N : ℕ}
    {g ν : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (h : APUntouchedFaceBounds g ν j) :
    ∀ t z,
      0 ≤ apUntouchedFaceWeights g j t z ∧
        apUntouchedFaceWeights g j t z ≤
          apUntouchedFaceMajorants ν j t z :=
  h

/-! ## Projection bounds -/

/-- The incident product is nonnegative when every untouched factor is
nonnegative. -/
theorem apHeterogeneousIncidentProduct_nonneg
    {n N : ℕ}
    {g ν : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (h : APUntouchedFaceBounds g ν j)
    (a : ZMod N) (y : Fin n → ZMod N) :
    0 ≤ apHeterogeneousIncidentProduct n N g j a y := by
  exact Finset.prod_nonneg fun t _ => (h t _).1

/-- Componentwise domination of the untouched factors dominates their
incident product. -/
theorem apHeterogeneousIncidentProduct_mono
    {n N : ℕ}
    {g ν : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (h : APUntouchedFaceBounds g ν j)
    (a : ZMod N) (y : Fin n → ZMod N) :
    apHeterogeneousIncidentProduct n N g j a y ≤
      apHeterogeneousIncidentProduct n N ν j a y := by
  unfold apHeterogeneousIncidentProduct
  exact Finset.prod_le_prod
    (fun t _ => (h t _).1)
    (fun t _ => (h t _).2)

/-- Conditional averaging preserves domination of heterogeneous projected
weights. -/
theorem apHeterogeneousProjectedWeight_mono
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (h : APUntouchedFaceBounds g ν j)
    (y : Fin n → ZMod N) :
    apHeterogeneousProjectedWeight n N g j y ≤
      apHeterogeneousProjectedWeight n N ν j y := by
  unfold apHeterogeneousProjectedWeight
  exact mean_mono fun a =>
    apHeterogeneousIncidentProduct_mono h a y

/-- The projected heterogeneous weight is nonnegative. -/
theorem apHeterogeneousProjectedWeight_nonneg
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (h : APUntouchedFaceBounds g ν j)
    (y : Fin n → ZMod N) :
    0 ≤ apHeterogeneousProjectedWeight n N g j y :=
  mean_nonneg fun a =>
    apHeterogeneousIncidentProduct_nonneg h a y

/-- The new projected surrogate is genuinely `[0,1]`-valued on its
lower-arity face space. -/
theorem apHeterogeneousProjectedSurrogate_mem_unitInterval
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (h : APUntouchedFaceBounds g ν j)
    (y : Fin n → ZMod N) :
    0 ≤ apHeterogeneousProjectedSurrogate n N g j y ∧
      apHeterogeneousProjectedSurrogate n N g j y ≤ 1 :=
  truncateAtOne_mem_unitInterval
    (apHeterogeneousProjectedWeight_nonneg h) y

/-- Unit-interval bounds on the chosen base weight transport to its
canonical deleted-face presentation. -/
theorem apHeterogeneousDistinguishedFaceWeight_mem_unitInterval
    {n N : ℕ}
    {g : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (y : Fin n → ZMod N) :
    0 ≤ apHeterogeneousDistinguishedFaceWeight n N g j y ∧
      apHeterogeneousDistinguishedFaceWeight n N g j y ≤ 1 :=
  hj _

/-! ## Exact heterogeneous count and pairing -/

/-- After inserting coordinate `j`, the heterogeneous simplex weight
factors into the projected incident product and the chosen face weight. -/
theorem apHeterogeneousSimplexWeight_insertNth
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) :
    (apHeterogeneousSimplexSystem n N g).simplexWeight
        (Fin.insertNth j a y) =
      apHeterogeneousIncidentProduct n N g j a y *
        apHeterogeneousDistinguishedFaceWeight n N g j y := by
  rw [WeightedSimplexSystem.simplexWeight,
    Fin.prod_univ_succAbove _ j,
    apHeterogeneousSimplexSystem_edge]
  have hdelete :
      deleteCoordinate (Fin.insertNth j a y) j =
        finTupleToDeletedVector j y := by
    simpa using
      deleteCoordinate_eq_finTupleToDeletedVector
        j (Fin.insertNth j a y)
  rw [hdelete]
  have htail :
      (∏ t : Fin n,
        (apHeterogeneousSimplexSystem n N g).edgeWeight
          (j.succAbove t)
          (deleteCoordinate (Fin.insertNth j a y)
            (j.succAbove t))) =
        apHeterogeneousIncidentProduct n N g j a y := by
    unfold apHeterogeneousIncidentProduct
    apply Fintype.prod_congr
    intro t
    rfl
  rw [htail, apHeterogeneousDistinguishedFaceWeight, mul_comm]

/-- The heterogeneous AP-simplex count is exactly the chosen face paired
with the conditional projection of all other colours. -/
theorem apHeterogeneousSimplexCount_eq_projectedPairing
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (apHeterogeneousSimplexSystem n N g).simplexCount =
      mean (fun y =>
        apHeterogeneousProjectedWeight n N g j y *
          apHeterogeneousDistinguishedFaceWeight n N g j y) := by
  rw [WeightedSimplexSystem.simplexCount,
    mean_insertNth n j, mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext y
  calc
    mean (fun a : ZMod N =>
        (apHeterogeneousSimplexSystem n N g).simplexWeight
          (Fin.insertNth j a y)) =
        mean (fun a : ZMod N =>
          apHeterogeneousIncidentProduct n N g j a y *
            apHeterogeneousDistinguishedFaceWeight n N g j y) := by
      apply congrArg mean
      funext a
      exact apHeterogeneousSimplexWeight_insertNth
        n N g j a y
    _ = mean (fun a : ZMod N =>
          apHeterogeneousDistinguishedFaceWeight n N g j y *
            apHeterogeneousIncidentProduct n N g j a y) := by
      apply congrArg mean
      funext a
      ring
    _ = apHeterogeneousDistinguishedFaceWeight n N g j y *
        mean (fun a : ZMod N =>
          apHeterogeneousIncidentProduct n N g j a y) :=
      mean_smul _ _
    _ = apHeterogeneousProjectedWeight n N g j y *
        apHeterogeneousDistinguishedFaceWeight n N g j y := by
      rw [mul_comm]
      rfl

/-- The lower-arity pairing obtained by truncating the heterogeneous
projection. -/
noncomputable def apHeterogeneousDensifiedPairing
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1)) : ℝ :=
  mean (fun y =>
    apHeterogeneousProjectedSurrogate n N g j y *
      apHeterogeneousDistinguishedFaceWeight n N g j y)

/-- A projected-moment certificate for a heterogeneous majorant family
gives the complete one-step loss estimate. -/
theorem HasProjectedMajorantMoments.abs_apHeterogeneousSimplexCount_sub_densifiedPairing_le
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {η : ℝ} {j : Fin (n + 1)}
    (hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N ν j) η)
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    |(apHeterogeneousSimplexSystem n N g).simplexCount -
        apHeterogeneousDensifiedPairing n N g j| ≤
      Real.sqrt (3 * η) := by
  rw [apHeterogeneousSimplexCount_eq_projectedPairing]
  have hface :
      ∀ y, |apHeterogeneousDistinguishedFaceWeight n N g j y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg]
    · exact (hj _).2
    · exact (hj _).1
  simpa [apHeterogeneousDensifiedPairing,
    apHeterogeneousProjectedSurrogate] using
    hMoments.abs_mean_mul_sub_truncateAtOne_mul_le_sqrt
      (apHeterogeneousProjectedWeight_mono hrest) hface

/-- A constant heterogeneous family recovers the earlier common-weight
projection definition exactly. -/
theorem apHeterogeneousProjectedWeight_const
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    apHeterogeneousProjectedWeight n N (fun _ => ν) j =
      apProjectedMajorant n N ν j :=
  rfl

/-- The existing AP linear-forms condition supplies the heterogeneous
one-step estimate whenever all untouched weights share a common majorant.
No relationship between the distinct `g i` is required. -/
theorem HasLinearFormsCondition.abs_apHeterogeneousSimplexCount_sub_densifiedPairing_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {g : APFaceWeightFamily n N}
    {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν0 : ∀ z, 0 ≤ ν z)
    (j : Fin (n + 1))
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest :
      ∀ t z,
        0 ≤ g (j.succAbove t) z ∧
          g (j.succAbove t) z ≤ ν z) :
    |(apHeterogeneousSimplexSystem n N g).simplexCount -
        apHeterogeneousDensifiedPairing n N g j| ≤
      Real.sqrt (3 * η) := by
  have hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N (fun _ => ν) j) η := by
    rw [apHeterogeneousProjectedWeight_const]
    exact hLF.hasProjectedMajorantMoments_apProjection hν0 j
  exact
    hMoments.abs_apHeterogeneousSimplexCount_sub_densifiedPairing_le
      hj hrest

/-! ## A concrete full-to-projected state transition -/

/-- Data carried by the full AP-simplex stage. -/
structure APRelativeSimplexFullPayload (n N : ℕ) where
  weight : APFaceWeightFamily n N
  majorant : APFaceWeightFamily n N
  chosen : Fin (n + 1)

/-- Data carried after one chosen colour has been projected.

Both live factors are functions on the actual deleted-face space.  The
untouched original factors and majorants are retained, reindexed by
`Fin n`, so their relative bounds remain available without pretending that
the projected pairing is a full AP simplex. -/
structure APRelativeSimplexProjectedPayload (n N : ℕ) where
  chosen : Fin (n + 1)
  distinguished : (Fin n → ZMod N) → ℝ
  surrogate : (Fin n → ZMod N) → ℝ
  untouchedWeight : (t : Fin n) → ZMod N → ℝ
  untouchedMajorant : (t : Fin n) → ZMod N → ℝ

/-- The two honestly different domains which occur in one heterogeneous
densification step. -/
inductive APRelativeSimplexPayload (n N : ℕ)
  | full : APRelativeSimplexFullPayload n N →
      APRelativeSimplexPayload n N
  | projected : APRelativeSimplexProjectedPayload n N →
      APRelativeSimplexPayload n N

/-- Canonical scalar count represented by either payload constructor. -/
noncomputable def apRelativeSimplexPayloadCount
    (n N : ℕ) [NeZero N] :
    APRelativeSimplexPayload n N → ℝ
  | .full data =>
      (apHeterogeneousSimplexSystem n N data.weight).simplexCount
  | .projected data =>
      mean (fun y => data.surrogate y * data.distinguished y)

/-- Structural conditions retained at the two stages. -/
def APRelativeSimplexPayload.IsAdmissible
    {n N : ℕ} :
    APRelativeSimplexPayload n N → Prop
  | .full data =>
      (∀ z,
        0 ≤ data.weight data.chosen z ∧
          data.weight data.chosen z ≤ 1) ∧
        APUntouchedFaceBounds
          data.weight data.majorant data.chosen
  | .projected data =>
      (∀ y,
        0 ≤ data.distinguished y ∧ data.distinguished y ≤ 1) ∧
        (∀ y, 0 ≤ data.surrogate y ∧ data.surrogate y ≤ 1) ∧
        ∀ t z,
          0 ≤ data.untouchedWeight t z ∧
            data.untouchedWeight t z ≤
              data.untouchedMajorant t z

/-- Application invariant for the generic finite iteration API: the scalar
field is the canonical count of the payload, and the stage-specific
boundedness data is valid. -/
def APRelativeSimplexStateInvariant
    (n N : ℕ) [NeZero N]
    (state :
      RelativeDensificationState
        (APRelativeSimplexPayload n N)) : Prop :=
  state.count =
      apRelativeSimplexPayloadCount n N state.payload ∧
    state.payload.IsAdmissible

/-- Full-stage payload built from a heterogeneous family and its
majorants. -/
def apRelativeSimplexFullPayload
    {n N : ℕ}
    (g ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    APRelativeSimplexPayload n N :=
  .full
    { weight := g
      majorant := ν
      chosen := j }

/-- Projected-stage payload on the deleted `j` face. -/
noncomputable def apRelativeSimplexProjectedPayload
    {n N : ℕ} [NeZero N]
    (g ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    APRelativeSimplexPayload n N :=
  .projected
    { chosen := j
      distinguished :=
        apHeterogeneousDistinguishedFaceWeight n N g j
      surrogate :=
        apHeterogeneousProjectedSurrogate n N g j
      untouchedWeight := apUntouchedFaceWeights g j
      untouchedMajorant := apUntouchedFaceMajorants ν j }

/-- The canonical counted state before projection. -/
noncomputable def apRelativeSimplexFullState
    {n N : ℕ} [NeZero N]
    (g ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    RelativeDensificationState
      (APRelativeSimplexPayload n N) where
  payload := apRelativeSimplexFullPayload g ν j
  count :=
    apRelativeSimplexPayloadCount n N
      (apRelativeSimplexFullPayload g ν j)

/-- The canonical counted state after projection and truncation. -/
noncomputable def apRelativeSimplexProjectedState
    {n N : ℕ} [NeZero N]
    (g ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    RelativeDensificationState
      (APRelativeSimplexPayload n N) where
  payload := apRelativeSimplexProjectedPayload g ν j
  count :=
    apRelativeSimplexPayloadCount n N
      (apRelativeSimplexProjectedPayload g ν j)

@[simp]
theorem apRelativeSimplexFullState_count
    {n N : ℕ} [NeZero N]
    (g ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (apRelativeSimplexFullState g ν j).count =
      (apHeterogeneousSimplexSystem n N g).simplexCount :=
  rfl

@[simp]
theorem apRelativeSimplexProjectedState_count
    {n N : ℕ} [NeZero N]
    (g ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (apRelativeSimplexProjectedState g ν j).count =
      apHeterogeneousDensifiedPairing n N g j :=
  rfl

/-- The full canonical state satisfies the concrete invariant. -/
theorem apRelativeSimplexFullState_valid
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    APRelativeSimplexStateInvariant n N
      (apRelativeSimplexFullState g ν j) := by
  exact ⟨rfl, hj, hrest⟩

/-- The projected canonical state satisfies the concrete invariant.  This
is where the new `[0,1]` surrogate and every transported untouched bound are
recorded together. -/
theorem apRelativeSimplexProjectedState_valid
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {j : Fin (n + 1)}
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    APRelativeSimplexStateInvariant n N
      (apRelativeSimplexProjectedState g ν j) := by
  refine
    ⟨rfl,
      apHeterogeneousDistinguishedFaceWeight_mem_unitInterval hj,
      apHeterogeneousProjectedSurrogate_mem_unitInterval hrest,
      apUntouchedFaceWeights_bounds hrest⟩

/-- The quantitative heterogeneous densification theorem is exactly a
count-loss certificate between the two concrete states. -/
theorem HasProjectedMajorantMoments.apRelativeSimplexStateTransition
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {η : ℝ} {j : Fin (n + 1)}
    (hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N ν j) η)
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    RelativeDensificationCountLoss
      (apRelativeSimplexFullState g ν j)
      (apRelativeSimplexProjectedState g ν j)
      (Real.sqrt (3 * η)) := by
  exact
    hMoments.abs_apHeterogeneousSimplexCount_sub_densifiedPairing_le
      hj hrest

namespace RelativeDensificationIteration

/-- A single certified transition as a finite iteration of length one. -/
def single
    {Payload : Type*}
    {Invariant : RelativeDensificationState Payload → Prop}
    (source target : RelativeDensificationState Payload)
    (ε : ℝ)
    (hsource : Invariant source)
    (htarget : Invariant target)
    (hloss : RelativeDensificationCountLoss source target ε) :
    RelativeDensificationIteration Payload Invariant where
  length := 1
  state
    | 0 => source
    | _ + 1 => target
  error := fun _ => ε
  valid := by
    intro i hi
    cases i with
    | zero => exact hsource
    | succ i =>
        have hi0 : i = 0 := by omega
        subst i
        exact htarget
  countLoss := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    exact hloss

end RelativeDensificationIteration

/-- The concrete heterogeneous full-to-projected transition as an actual
`RelativeDensificationIteration`. -/
noncomputable def HasProjectedMajorantMoments.apRelativeSimplexOneStepIteration
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {η : ℝ} {j : Fin (n + 1)}
    (hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N ν j) η)
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    RelativeDensificationIteration
      (APRelativeSimplexPayload n N)
      (APRelativeSimplexStateInvariant n N) :=
  RelativeDensificationIteration.single
    (apRelativeSimplexFullState g ν j)
    (apRelativeSimplexProjectedState g ν j)
    (Real.sqrt (3 * η))
    (apRelativeSimplexFullState_valid hj hrest)
    (apRelativeSimplexProjectedState_valid hj hrest)
    (hMoments.apRelativeSimplexStateTransition hj hrest)

@[simp]
theorem HasProjectedMajorantMoments.apRelativeSimplexOneStepIteration_length
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {η : ℝ} {j : Fin (n + 1)}
    (hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N ν j) η)
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    (hMoments.apRelativeSimplexOneStepIteration hj hrest).length = 1 :=
  rfl

@[simp]
theorem HasProjectedMajorantMoments.apRelativeSimplexOneStepIteration_initialCount
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {η : ℝ} {j : Fin (n + 1)}
    (hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N ν j) η)
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    (hMoments.apRelativeSimplexOneStepIteration hj hrest).initialCount =
      (apHeterogeneousSimplexSystem n N g).simplexCount :=
  rfl

@[simp]
theorem HasProjectedMajorantMoments.apRelativeSimplexOneStepIteration_finalCount
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {η : ℝ} {j : Fin (n + 1)}
    (hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N ν j) η)
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    (hMoments.apRelativeSimplexOneStepIteration hj hrest).finalCount =
      apHeterogeneousDensifiedPairing n N g j :=
  rfl

@[simp]
theorem HasProjectedMajorantMoments.apRelativeSimplexOneStepIteration_totalError
    {n N : ℕ} [NeZero N]
    {g ν : APFaceWeightFamily n N}
    {η : ℝ} {j : Fin (n + 1)}
    (hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N ν j) η)
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest : APUntouchedFaceBounds g ν j) :
    (hMoments.apRelativeSimplexOneStepIteration hj hrest).totalError =
      Real.sqrt (3 * η) := by
  simp [RelativeDensificationIteration.totalError,
    HasProjectedMajorantMoments.apRelativeSimplexOneStepIteration,
    RelativeDensificationIteration.single]

end Wikipedia.SzemeredisTheorem
