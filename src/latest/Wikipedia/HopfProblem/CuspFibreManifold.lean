import Wikipedia.HopfProblem.CuspFibreImmersion

/-!
# The analytic structure induced on the nonzero cusp fibres

The charts below are the slices of the ambient quotient charts at a fixed
value of the third coordinate.  In particular, the topology is the actual
subspace topology of the cusp fibre, not a topology transported from a torus.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricSpace CuspQuotient

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

def fibreCoordinates : CoordinateSpace 3 →L[ℂ] ComplexPlane₂ :=
  (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂).comp coordinateSplit.toContinuousLinearMap

def fibreInsert (t : ℂ) (z : ComplexPlane₂) : CoordinateSpace 3 :=
  coordinateSplit.symm (t, z)

@[simp] theorem fibreInsert_time (t : ℂ) (z : ComplexPlane₂) : fibreInsert t z 2 = t := rfl

@[simp] theorem fibreCoordinates_insert (t : ℂ) (z : ComplexPlane₂) :
    fibreCoordinates (fibreInsert t z) = z := by
  change (coordinateSplit (coordinateSplit.symm (t, z))).2 = z
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem fibreInsert_coordinates (t : ℂ) (z : CoordinateSpace 3) (hz : z 2 = t) :
    fibreInsert t (fibreCoordinates z) = z := by
  apply coordinateSplit.injective
  change coordinateSplit (coordinateSplit.symm (t, (coordinateSplit z).2)) = coordinateSplit z
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact Prod.ext hz.symm rfl

theorem fibreInsert_holomorphic (t : ℂ) : ContDiff ℂ ω (fibreInsert t) :=
  coordinateSplit.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)

section Slice

variable {Q : Type*} [TopologicalSpace Q] (p : Q → ℂ) (t : ℂ)
    (e : OpenPartialHomeomorph Q (CoordinateSpace 3))
    (he : ∀ w ∈ e.target, p (e.symm w) = w 2) (x₀ : p ⁻¹' {t})

include he in
theorem fibreSlice_time {x : Q} (hx : x ∈ e.source) : e x 2 = p x := by
  have h := he (e x) (e.map_source hx)
  rw [e.left_inv hx] at h
  exact h.symm

def fibreSliceInverse (z : ComplexPlane₂) : p ⁻¹' {t} := by
  classical
  exact if hz : fibreInsert t z ∈ e.target then
    ⟨e.symm (fibreInsert t z), by
      change p (e.symm (fibreInsert t z)) = t
      rw [he _ hz, fibreInsert_time]⟩
    else x₀

theorem fibreSliceInverse_val {z : ComplexPlane₂} (hz : fibreInsert t z ∈ e.target) :
    (fibreSliceInverse p t e he x₀ z : Q) = e.symm (fibreInsert t z) := by
  classical
  simp [fibreSliceInverse, hz]

def fibreSliceChart : OpenPartialHomeomorph (p ⁻¹' {t}) ComplexPlane₂ where
  toFun x := fibreCoordinates (e x)
  invFun := fibreSliceInverse p t e he x₀
  source := Subtype.val ⁻¹' e.source
  target := fibreInsert t ⁻¹' e.target
  map_source' x hx := by
    change fibreInsert t (fibreCoordinates (e x)) ∈ e.target
    have ht : e x 2 = t := (fibreSlice_time p e he hx).trans x.2
    rw [fibreInsert_coordinates t _ ht]
    exact e.map_source hx
  map_target' z hz := by
    change (fibreSliceInverse p t e he x₀ z : Q) ∈ e.source
    rw [fibreSliceInverse_val p t e he x₀ hz]
    exact e.map_target hz
  left_inv' x hx := by
    apply Subtype.ext
    have ht : e x 2 = t := (fibreSlice_time p e he hx).trans x.2
    have hz : fibreInsert t (fibreCoordinates (e x)) ∈ e.target := by
      rw [fibreInsert_coordinates t _ ht]
      exact e.map_source hx
    rw [fibreSliceInverse_val p t e he x₀ hz, fibreInsert_coordinates t _ ht, e.left_inv hx]
  right_inv' z hz := by
    rw [fibreSliceInverse_val p t e he x₀ hz, e.right_inv hz, fibreCoordinates_insert]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (fibreInsert_holomorphic t).continuous
  continuousOn_toFun := fibreCoordinates.continuous.comp_continuousOn
    (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx))
  continuousOn_invFun := by
    apply IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (e.continuousOn_symm.comp (fibreInsert_holomorphic t).continuous.continuousOn
      (fun _ hz => hz)).congr
    intro z hz
    exact fibreSliceInverse_val p t e he x₀ hz

@[simp] theorem fibreSliceChart_source :
    (fibreSliceChart p t e he x₀).source = Subtype.val ⁻¹' e.source := rfl

@[simp] theorem fibreSliceChart_target :
    (fibreSliceChart p t e he x₀).target = fibreInsert t ⁻¹' e.target := rfl

@[simp] theorem fibreSliceChart_apply (x : p ⁻¹' {t}) :
    fibreSliceChart p t e he x₀ x = fibreCoordinates (e x) := rfl

theorem fibreSliceChart_symm_val {z : ComplexPlane₂}
    (hz : z ∈ (fibreSliceChart p t e he x₀).target) :
    ((fibreSliceChart p t e he x₀).symm z : Q) = e.symm (fibreInsert t z) :=
  fibreSliceInverse_val p t e he x₀ hz

variable [ChartedSpace (CoordinateSpace 3) Q]

theorem fibreSlice_transition_holomorphic
    (d : OpenPartialHomeomorph Q (CoordinateSpace 3))
    (hd : ∀ w ∈ d.target, p (d.symm w) = w 2) (y₀ : p ⁻¹' {t})
    (he' : ContMDiffOn I₃ I₃ ω e.symm e.target)
    (hd' : ContMDiffOn I₃ I₃ ω d d.source) :
    ContDiffOn ℂ ω ((fibreSliceChart p t e he x₀).symm.trans
      (fibreSliceChart p t d hd y₀))
      ((fibreSliceChart p t e he x₀).symm.trans (fibreSliceChart p t d hd y₀)).source := by
  let S := ((fibreSliceChart p t e he x₀).symm.trans
    (fibreSliceChart p t d hd y₀)).source
  have hi : ContMDiffOn I₂ I₃ ω (fibreInsert t) S :=
    (fibreInsert_holomorphic t).contMDiff.contMDiffOn
  have hinv : ContMDiffOn I₂ I₃ ω (e.symm ∘ fibreInsert t) S :=
    he'.comp hi (fun _ hz => hz.1)
  have hfwd : ContMDiffOn I₂ I₃ ω (d ∘ (e.symm ∘ fibreInsert t)) S := by
    apply hd'.comp hinv
    intro z hz
    have h := hz.2
    change ((fibreSliceChart p t e he x₀).symm z : Q) ∈ d.source at h
    rw [fibreSliceChart_symm_val p t e he x₀ hz.1] at h
    exact h
  have hfull : ContMDiffOn I₂ I₂ ω (fibreCoordinates ∘ (d ∘ (e.symm ∘ fibreInsert t))) S :=
    fibreCoordinates.contDiff.contMDiff.comp_contMDiffOn hfwd
  apply hfull.contDiffOn.congr
  intro z hz
  change fibreCoordinates (d ((fibreSliceChart p t e he x₀).symm z : Q)) = _
  rw [fibreSliceChart_symm_val p t e he x₀ hz.1]
  rfl

end Slice

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (t : ℂ)

def fibreRepresentative (x : projection C ε ⁻¹' {t}) : Tube (disc ε) :=
  (quotientMap_covering C ε hε hε1 hC hR).surjective x |>.choose

theorem quotientMap_fibreRepresentative (x : projection C ε ⁻¹' {t}) :
    quotientMap C ε (fibreRepresentative C ε hε hε1 hC hR t x) = x :=
  (quotientMap_covering C ε hε hε1 hC hR).surjective x |>.choose_spec

def fibreAmbientChart (x : projection C ε ⁻¹' {t}) :
    OpenPartialHomeomorph (QuotientSpace C ε) (CoordinateSpace 3) :=
  projectionChart C ε hε hε1 hC hR (fibreRepresentative C ε hε hε1 hC hR t x)

theorem fibreAmbientChart_symm_time (x : projection C ε ⁻¹' {t}) {w : CoordinateSpace 3}
    (hw : w ∈ (fibreAmbientChart C ε hε hε1 hC hR t x).target) :
    projection C ε ((fibreAmbientChart C ε hε hε1 hC hR t x).symm w) = w 2 :=
  projectionChart_symm_time C ε hε hε1 hC hR _ hw

theorem fibreAmbientChart_holomorphic (x : projection C ε ⁻¹' {t}) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiffOn I₃ I₃ ω (fibreAmbientChart C ε hε hε1 hC hR t x)
      (fibreAmbientChart C ε hε hε1 hC hR t x).source :=
  projectionChart_holomorphic C ε hε hε1 hC hR
    (fibreRepresentative C ε hε hε1 hC hR t x)

theorem fibreAmbientChart_symm_holomorphic (x : projection C ε ⁻¹' {t}) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiffOn I₃ I₃ ω (fibreAmbientChart C ε hε hε1 hC hR t x).symm
      (fibreAmbientChart C ε hε hε1 hC hR t x).target :=
  projectionChart_symm_holomorphic C ε hε hε1 hC hR
    (fibreRepresentative C ε hε hε1 hC hR t x)

def fibreChart (x : projection C ε ⁻¹' {t}) :
    OpenPartialHomeomorph (projection C ε ⁻¹' {t}) ComplexPlane₂ :=
  fibreSliceChart (projection C ε) t (fibreAmbientChart C ε hε hε1 hC hR t x)
    (fun _ hw => fibreAmbientChart_symm_time C ε hε hε1 hC hR t x hw) x

theorem fibreChart_symm_val (x : projection C ε ⁻¹' {t}) {z : ComplexPlane₂}
    (hz : z ∈ (fibreChart C ε hε hε1 hC hR t x).target) :
    ((fibreChart C ε hε hε1 hC hR t x).symm z : QuotientSpace C ε) =
      (fibreAmbientChart C ε hε hε1 hC hR t x).symm (fibreInsert t z) :=
  fibreSliceChart_symm_val (projection C ε) t
    (fibreAmbientChart C ε hε hε1 hC hR t x)
    (fun _ hw => fibreAmbientChart_symm_time C ε hε hε1 hC hR t x hw) x hz

theorem mem_fibreAmbientChart_source (ht0 : t ≠ 0) (x : projection C ε ⁻¹' {t}) :
    (x : QuotientSpace C ε) ∈ (fibreAmbientChart C ε hε hε1 hC hR t x).source := by
  let a := fibreRepresentative C ε hε hε1 hC hR t x
  have ha : quotientMap C ε a = x := quotientMap_fibreRepresentative C ε hε hε1 hC hR t x
  have ht : time (a : Space) = t := by
    change projection C ε (quotientMap C ε a) = t
    rw [ha]
    exact x.2
  have hmem := mem_projectionChart_source C ε hε hε1 hC hR a (ht ▸ ht0)
  rwa [ha] at hmem

@[instance_reducible] def fibreChartedSpace (ht0 : t ≠ 0) :
    ChartedSpace ComplexPlane₂ (projection C ε ⁻¹' {t}) where
  atlas := range (fibreChart C ε hε hε1 hC hR t)
  chartAt := fibreChart C ε hε hε1 hC hR t
  mem_chart_source x := mem_fibreAmbientChart_source C ε hε hε1 hC hR t ht0 x
  chart_mem_atlas _ := mem_range_self _

theorem fibre_isManifold (ht0 : t ≠ 0) :
    letI := fibreChartedSpace C ε hε hε1 hC hR t ht0
    IsManifold I₂ ω (projection C ε ⁻¹' {t}) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := fibreChartedSpace C ε hε hε1 hC hR t ht0
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  simpa [fibreChart] using fibreSlice_transition_holomorphic (projection C ε) t
    (fibreAmbientChart C ε hε hε1 hC hR t x)
    (fun _ hw => fibreAmbientChart_symm_time C ε hε hε1 hC hR t x hw) x
    (fibreAmbientChart C ε hε hε1 hC hR t y)
    (fun _ hw => fibreAmbientChart_symm_time C ε hε hε1 hC hR t y hw) y
    (projectionChart_symm_holomorphic C ε hε hε1 hC hR _)
    (projectionChart_holomorphic C ε hε hε1 hC hR _)

def fibreShiftedAmbientChart (x : projection C ε ⁻¹' {t}) :
    OpenPartialHomeomorph (QuotientSpace C ε) (CoordinateSpace 3) :=
  (fibreAmbientChart C ε hε hε1 hC hR t x).trans
    (fibreCoordinateShift t).toOpenPartialHomeomorph

theorem fibreShiftedAmbientChart_mem_maximalAtlas (x : projection C ε ⁻¹' {t}) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    fibreShiftedAmbientChart C ε hε hε1 hC hR t x ∈
      IsManifold.maximalAtlas I₃ ω (QuotientSpace C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.isManifold C ε hε hε1 hC hR
  apply (fibreShiftedAmbientChart C ε hε hε1 hC hR t x).mem_maximalAtlas_of_contMDiffOn
  · exact (fibreCoordinateShift_holomorphic t).comp_contMDiffOn
      ((fibreAmbientChart_holomorphic C ε hε hε1 hC hR t x).mono inter_subset_left)
  · exact (fibreAmbientChart_symm_holomorphic C ε hε hε1 hC hR t x).comp
      ((fibreCoordinateShift_symm_holomorphic t).contMDiffOn.mono inter_subset_left)
      (fun _ hw => hw.2)

theorem fibreCoordinateShift_insert (z : ComplexPlane₂) :
    fibreCoordinateShift t (fibreInsert t z) = fibreCoordinateJoin (z, 0) := by
  change ![z 0, z 1, t] + - ![0, 0, t] = ![z 0, z 1, 0]
  ext i
  fin_cases i <;> simp

/-- The actual inclusion of a nonzero fibre has the coordinate normal form
`z ↦ (z, 0)` in its slice charts and the ambient quotient charts. -/
theorem fibre_inclusion_isImmersionOfComplement (ht0 : t ≠ 0) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    letI := fibreChartedSpace C ε hε hε1 hC hR t ht0
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (Subtype.val : (projection C ε ⁻¹' {t}) → QuotientSpace C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.isManifold C ε hε hε1 hC hR
  let := fibreChartedSpace C ε hε hε1 hC hR t ht0
  let := fibre_isManifold C ε hε hε1 hC hR t ht0
  intro x
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt fibreCoordinateJoin
    (fibreChart C ε hε hε1 hC hR t x)
    (fibreShiftedAmbientChart C ε hε hε1 hC hR t x)
    (mem_fibreAmbientChart_source C ε hε hε1 hC hR t ht0 x)
    ⟨mem_fibreAmbientChart_source C ε hε hε1 hC hR t ht0 x, mem_univ _⟩
    (IsManifold.chart_mem_maximalAtlas x)
    (fibreShiftedAmbientChart_mem_maximalAtlas C ε hε hε1 hC hR t x) ?_
  intro z hz
  have hz' : z ∈ (fibreChart C ε hε hε1 hC hR t x).target := by
    simpa [OpenPartialHomeomorph.extend] using hz
  change fibreCoordinateShift t ((fibreAmbientChart C ε hε hε1 hC hR t x)
    (((fibreChart C ε hε hε1 hC hR t x).symm z) : QuotientSpace C ε)) = _
  rw [fibreChart_symm_val C ε hε hε1 hC hR t x hz',
    (fibreAmbientChart C ε hε hε1 hC hR t x).right_inv hz',
    fibreCoordinateShift_insert]
  rfl

theorem fibre_inclusion_holomorphic (ht0 : t ≠ 0) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    letI := fibreChartedSpace C ε hε hε1 hC hR t ht0
    ContMDiff I₂ I₃ ω
      (Subtype.val : (projection C ε ⁻¹' {t}) → QuotientSpace C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := fibreChartedSpace C ε hε hε1 hC hR t ht0
  exact (fibre_inclusion_isImmersionOfComplement C ε hε hε1 hC hR t ht0).contMDiff

end Wikipedia.HopfProblem.CuspUniformization
