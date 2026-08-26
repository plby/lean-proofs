import ErdosProblems.Erdos1002.GaussMovingSignedMarkedContinuous

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Haar-continuity boxes on the finite product torus

The marked factorial argument uses half-open arcs in each torus
coordinate.  This file proves, rather than assumes, that their finite
products have Haar-null frontier.  The proof first identifies the only
possible boundary points of one quotient-circle arc, then uses the
frontier-of-an-intersection inclusion and the atomlessness of circle Haar
measure.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1002

noncomputable section

local instance unitAddCircleMeasureSpaceContinuityBoxes :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitAddCircleProbabilityContinuityBoxes :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance unitAddCircleNoAtomsContinuityBoxes :
    NullSingletonClass (volume : Measure UnitAddCircle) := by
  change NullSingletonClass (AddCircle.haarAddCircle : Measure UnitAddCircle)
  refine ⟨fun x ↦ ?_⟩
  have h := AddCircle.volume_closedBall (1 : ℝ) (x := x) 0
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simpa [Metric.closedBall_zero] using! h

/-! ## One half-open arc -/

/-- The image in `ℝ/ℤ` of a real half-open interval. -/
def unitAddCircleHalfOpenArc (a b : ℝ) : Set UnitAddCircle :=
  ((↑) : ℝ → UnitAddCircle) '' Ico a b

/-- The quotient-circle frontier of a half-open arc can only contain its
two endpoint classes.  This remains true when the endpoints represent the
same class. -/
theorem frontier_unitAddCircleHalfOpenArc_subset
    {a b : ℝ} :
    frontier (unitAddCircleHalfOpenArc a b) ⊆
      {((a : ℝ) : UnitAddCircle), ((b : ℝ) : UnitAddCircle)} := by
  let q : ℝ → UnitAddCircle := fun x ↦ (x : UnitAddCircle)
  have hclosed : IsClosed (q '' Icc a b) := by
    exact (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hclosure : closure (unitAddCircleHalfOpenArc a b) ⊆
      q '' Icc a b := by
    apply closure_minimal
    · exact image_mono Ico_subset_Icc_self
    · exact hclosed
  have hopen : IsOpen (q '' Ioo a b) := by
    exact QuotientAddGroup.isOpenMap_coe (Ioo a b) isOpen_Ioo
  have hinterior : q '' Ioo a b ⊆
      interior (unitAddCircleHalfOpenArc a b) := by
    apply interior_maximal
    · exact image_mono Ioo_subset_Ico_self
    · exact hopen
  intro z hz
  have hzClosure : z ∈ q '' Icc a b :=
    hclosure (frontier_subset_closure hz)
  have hzNotInterior : z ∉
      interior (unitAddCircleHalfOpenArc a b) := by
    exact hz.2
  obtain ⟨x, hx, rfl⟩ := hzClosure
  have hxNot : x ∉ Ioo a b := by
    intro hxOpen
    exact hzNotInterior (hinterior ⟨x, hxOpen, rfl⟩)
  rcases lt_or_eq_of_le hx.1 with hax | hax
  · rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · exact (hxNot ⟨hax, hxb⟩).elim
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (congrArg q hxb)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl (congrArg q hax.symm)

/-! ## Finite products -/

/-- Coordinatewise half-open arc box in the finite product torus. -/
def unitTorusHalfOpenBox
    {r : ℕ} (lower upper : Fin r → ℝ) :
    Set (UnitAddTorus (Fin r)) :=
  ⋂ i, (fun z : UnitAddTorus (Fin r) ↦ z i) ⁻¹'
    unitAddCircleHalfOpenArc (lower i) (upper i)

/-- A finite intersection of sets with null frontier again has null
frontier. -/
private theorem measure_frontier_iInter_fintype_eq_zero
    {Omega iota : Type*} [TopologicalSpace Omega]
    [MeasurableSpace Omega] [Fintype iota]
    (mu : Measure Omega) (s : iota → Set Omega)
    (hnull : ∀ i, mu (frontier (s i)) = 0) :
    mu (frontier (⋂ i, s i)) = 0 := by
  classical
  let interFinset : Finset iota → Set Omega := fun I ↦
    ⋂ i ∈ I, s i
  have hfinset : ∀ I : Finset iota,
      mu (frontier (interFinset I)) = 0 := by
    intro I
    induction I using Finset.induction_on with
    | empty =>
        simp [interFinset]
    | @insert a I ha hI =>
        have hset : interFinset (insert a I) =
            s a ∩ interFinset I := by
          ext x
          simp [interFinset]
        rw [hset]
        exact measure_mono_null (frontier_inter_subset _ _)
          (measure_union_null
            (measure_inter_null_of_null_left _ (hnull a))
            (measure_inter_null_of_null_right _ hI))
  have hall := hfinset Finset.univ
  convert! hall using 2
  ext x
  simp [interFinset]

/-- Every coordinate-cylinder boundary has product-Haar measure zero. -/
private theorem unitTorus_coordinateArc_frontier_null
    {r : ℕ} (i : Fin r) {a b : ℝ} :
    (volume : Measure (UnitAddTorus (Fin r)))
      (frontier ((fun z : UnitAddTorus (Fin r) ↦ z i) ⁻¹'
        unitAddCircleHalfOpenArc a b)) = 0 := by
  let eval : UnitAddTorus (Fin r) → UnitAddCircle := fun z ↦ z i
  have hfrontier : frontier (eval ⁻¹'
      unitAddCircleHalfOpenArc a b) =
      eval ⁻¹' frontier (unitAddCircleHalfOpenArc a b) := by
    exact (isOpenMap_eval i).preimage_frontier_eq_frontier_preimage
      (continuous_apply i) _ |>.symm
  rw [hfrontier]
  apply measure_mono_null
  · intro z hz
    have hzEndpoints :=
      frontier_unitAddCircleHalfOpenArc_subset hz
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hzEndpoints ⊢
    exact hzEndpoints
  · apply measure_union_null
    · exact Measure.pi_hyperplane
        (fun _ : Fin r ↦ (volume : Measure UnitAddCircle)) i
        ((a : ℝ) : UnitAddCircle)
    · exact Measure.pi_hyperplane
        (fun _ : Fin r ↦ (volume : Measure UnitAddCircle)) i
        ((b : ℝ) : UnitAddCircle)

/-- A product of half-open quotient-circle arcs is a Haar-continuity set. -/
theorem unitTorusHaarProbabilityMeasure_frontier_halfOpenBox
    {r : ℕ} (lower upper : Fin r → ℝ) :
    unitTorusHaarProbabilityMeasure (r := r)
      (frontier (unitTorusHalfOpenBox lower upper)) = 0 := by
  rw [← ENNReal.coe_eq_zero]
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  unfold unitTorusHaarProbabilityMeasure unitTorusHalfOpenBox
  change (volume : Measure (UnitAddTorus (Fin r)))
    (frontier (⋂ i,
      (fun z : UnitAddTorus (Fin r) ↦ z i) ⁻¹'
        unitAddCircleHalfOpenArc (lower i) (upper i))) = 0
  exact measure_frontier_iInter_fintype_eq_zero
    (volume : Measure (UnitAddTorus (Fin r)))
    (fun i ↦ (fun z : UnitAddTorus (Fin r) ↦ z i) ⁻¹'
      unitAddCircleHalfOpenArc (lower i) (upper i))
    (fun i ↦ unitTorus_coordinateArc_frontier_null i)

/-- Fully concrete marked-cell consequence: zero-mode convergence and
nonzero Fourier cancellation imply convergence of every half-open torus
box count.  No abstract continuity-set hypothesis remains. -/
theorem
    tendsto_movingSignedMarkedTupleFiniteMeasure_halfOpenBox_of_fourier
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (signedLower signedUpper : Fin r → ℝ)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (massLimit : ℝ) (hmassLimit : 0 < massLimit)
    (hzero : Filter.Tendsto
      (fun n ↦ movingSignedApproximationTupleMassSum
        mu (scale n) signedLower signedUpper (tuples n))
      Filter.atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Filter.Tendsto
        (fun n ↦ movingSignedMarkedFourierTupleSum
          mu (N n) (scale n) signedLower signedUpper mode (tuples n))
        Filter.atTop (nhds 0))
    (torusLower torusUpper : Fin r → ℝ) :
    Filter.Tendsto
      (fun n ↦ movingSignedMarkedTupleFiniteMeasure
        mu (N n) (scale n) signedLower signedUpper (tuples n)
          (unitTorusHalfOpenBox torusLower torusUpper))
      Filter.atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit
          (unitTorusHalfOpenBox torusLower torusUpper))) := by
  exact
    tendsto_movingSignedMarkedTupleFiniteMeasure_apply_of_fourier
      mu N scale signedLower signedUpper tuples massLimit hmassLimit
        hzero hnonzero
        (unitTorusHaarProbabilityMeasure_frontier_halfOpenBox
          torusLower torusUpper)

end

end Erdos1002
