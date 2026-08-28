import Wikipedia.HopfProblem.CuspPeriodLattice
import Wikipedia.HopfProblem.CuspCentralFibre

/-!
# Period tori embedded as the nonzero cusp fibres

The exponential parametrization descends through the full period lattice.
Its exact equality criterion proves injectivity, and its range is the
actual nonzero fibre of the constructed cusp projection.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε)

def exponentialLift (z : ComplexPlane₂) : Tube (disc ε) :=
  ⟨exponentialPoint (exponential s) z, by
    change time (exponentialPoint (exponential s) z) ∈ Metric.ball 0 ε
    simpa only [time_exponentialPoint (exponential_ne_zero s),
      Metric.mem_ball, dist_zero_right] using hs⟩

theorem exponentialLift_continuous : Continuous (exponentialLift ε s hs) :=
  (exponentialPoint_holomorphic (exponential_ne_zero s)).continuous.subtype_mk _

theorem exponentialLift_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ (CoordinateSpace 3))
      ω (exponentialLift ε s hs) := by
  intro z
  have he : ContMDiffAt (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (fun w => (exponentialLift ε s hs w : Space)) z ↔
    ContMDiffAt (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (exponentialLift ε s hs) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (exponentialPoint_holomorphic (exponential_ne_zero s) z)

def fibreCover : ComplexPlane₂ → QuotientSpace C ε :=
  quotientMap C ε ∘ exponentialLift ε s hs

theorem fibreCover_continuous : Continuous (fibreCover C ε s hs) :=
  (quotientMap_continuous C ε).comp (exponentialLift_continuous ε s hs)

@[simp] theorem projection_fibreCover (z : ComplexPlane₂) :
    projection C ε (fibreCover C ε s hs z) = exponential s :=
  time_exponentialPoint (exponential_ne_zero s) z

variable (hlog : Real.log ‖exponential s‖ < 0)
    (hRp : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)

theorem fibreCover_eq_iff (z w : ComplexPlane₂) :
    fibreCover C ε s hs z = fibreCover C ε s hs w ↔
      z - w ∈ (periodData C s hlog hRp).lattice := by
  let := tubeAction C (disc ε)
  constructor
  · intro he
    have horb := Quotient.exact he
    change exponentialLift ε s hs z ∈
      MulAction.orbit LatticeGroup (exponentialLift ε s hs w) at horb
    obtain ⟨g, hg⟩ := horb
    have hp : exponentialPoint (exponential s) z =
        exponentialPoint (exponential s)
          (w + logarithmicPeriod C s *ᵥ (fun j => (g.toAdd j : ℂ))) :=
      (congrArg Subtype.val hg).symm.trans (twistedTranslate_exponentialPoint C s g.toAdd w)
    obtain ⟨m, hm⟩ := (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mp hp
    apply (FullPeriodMatrix.mem_lattice_iff _ _).mpr
    refine ⟨m, g.toAdd, ?_⟩
    change z - w = (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (g.toAdd j : ℂ))
    rw [hm]
    abel
  · intro he
    obtain ⟨m, n, hmn⟩ := (FullPeriodMatrix.mem_lattice_iff _ _).mp he
    have hp : exponentialPoint (exponential s) z =
        exponentialPoint (exponential s)
          (w + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) := by
      apply (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mpr
      refine ⟨m, ?_⟩
      have he := sub_eq_iff_eq_add.mp hmn
      change z = (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ)) + w at he
      rw [he]
      abel
    have hl : exponentialLift ε s hs z =
        tubeTranslate C (disc ε) n (exponentialLift ε s hs w) :=
      Subtype.ext (hp.trans (twistedTranslate_exponentialPoint C s n w).symm)
    change quotientMap C ε (exponentialLift ε s hs z) =
      quotientMap C ε (exponentialLift ε s hs w)
    rw [hl, quotientMap_translate]

def fibreMap : (periodData C s hlog hRp).Torus → QuotientSpace C ε :=
  Quotient.lift (fibreCover C ε s hs) (by
    intro z w hzw
    apply (fibreCover_eq_iff C ε s hs hlog hRp z w).mpr
    exact (Submodule.Quotient.eq _).mp (Quotient.sound hzw))

@[simp] theorem fibreMap_mkQ (z : ComplexPlane₂) :
    fibreMap C ε s hs hlog hRp ((periodData C s hlog hRp).lattice.mkQ z) =
      fibreCover C ε s hs z := rfl

theorem fibreMap_injective : Function.Injective (fibreMap C ε s hs hlog hRp) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h z =>
    induction y using Quotient.inductionOn with
    | h w =>
      intro he
      exact (Submodule.Quotient.eq _).mpr ((fibreCover_eq_iff C ε s hs hlog hRp z w).mp he)

theorem fibreMap_continuous : Continuous (fibreMap C ε s hs hlog hRp) :=
  (fibreCover_continuous C ε s hs).quotient_lift _

@[simp] theorem projection_fibreMap (x : (periodData C s hlog hRp).Torus) :
    projection C ε (fibreMap C ε s hs hlog hRp x) = exponential s := by
  induction x using Quotient.inductionOn with
  | h z => exact projection_fibreCover C ε s hs z

theorem fibreMap_range :
    range (fibreMap C ε s hs hlog hRp) = projection C ε ⁻¹' {exponential s} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact projection_fibreMap C ε s hs hlog hRp x
  · induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      have ht : time (x : Space) = exponential s := hx
      obtain ⟨z, hz⟩ := exponentialPoint_surjective_fibre (exponential_ne_zero s) ht
      refine ⟨(periodData C s hlog hRp).lattice.mkQ z, ?_⟩
      apply congrArg (quotientMap C ε)
      exact Subtype.ext hz

theorem fibreMap_holomorphic (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ (CoordinateSpace 3))
      ω (fibreMap C ε s hs hlog hRp) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply DiscreteQuotient.contMDiff_of_comp_mkQ
  exact (quotientMap_holomorphic C ε hε hε1 hC hR).comp (exponentialLift_holomorphic ε s hs)

def fibreMapToFibre (x : (periodData C s hlog hRp).Torus) :
    projection C ε ⁻¹' {exponential s} :=
  ⟨fibreMap C ε s hs hlog hRp x, projection_fibreMap C ε s hs hlog hRp x⟩

theorem fibreMapToFibre_bijective : Function.Bijective (fibreMapToFibre C ε s hs hlog hRp) := by
  constructor
  · intro x y he
    exact fibreMap_injective C ε s hs hlog hRp (congrArg Subtype.val he)
  · intro q
    have hq : (q : QuotientSpace C ε) ∈ range (fibreMap C ε s hs hlog hRp) := by
      rw [fibreMap_range]
      exact q.2
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, Subtype.ext hx⟩

variable (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- This identifies the actual fibre, with its subspace topology, with the
compact complex torus. Holomorphicity of the map into the ambient quotient
is established separately above. -/
def fibreHomeomorph : (periodData C s hlog hRp).Torus ≃ₜ projection C ε ⁻¹' {exponential s} := by
  let := quotient_t2Space C ε hε hε1 hC hR
  let e := Equiv.ofBijective (fibreMapToFibre C ε s hs hlog hRp)
    (fibreMapToFibre_bijective C ε s hs hlog hRp)
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    ((fibreMap_continuous C ε s hs hlog hRp).subtype_mk _)

include hε hε1 hC hR in
theorem fibreMap_isEmbedding : IsEmbedding (fibreMap C ε s hs hlog hRp) := by
  exact IsEmbedding.subtypeVal.comp
    (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR).isEmbedding

/-- Every nonzero fibre is the image of its full period torus by a
holomorphic topological embedding. No period lattice is assumed discrete. -/
theorem nonzero_fibre_torus {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∃ p : FullPeriodMatrix, ∃ f : p.Torus → QuotientSpace C ε,
      ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
        (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω f ∧
      IsEmbedding f ∧ range f = projection C ε ⁻¹' {t} := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let s := logarithm t
  have hst : exponential s = t := exponential_logarithm ht0
  have hs : ‖exponential s‖ < ε := by simpa only [hst] using ht
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr (exponential_ne_zero s)
  have hlog := Real.log_neg hpos (hs.trans hε1)
  have hRp := hR _ hpos hs
  refine ⟨periodData C s hlog hRp, fibreMap C ε s hs hlog hRp,
    fibreMap_holomorphic C ε s hs hlog hRp hε hε1 hC hR,
    fibreMap_isEmbedding C ε s hs hlog hRp hε hε1 hC hR, ?_⟩
  simpa only [hst] using fibreMap_range C ε s hs hlog hRp

include hε hε1 hC hR in
theorem nonzero_fibre_pathConnected {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    IsPathConnected (projection C ε ⁻¹' {t}) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  obtain ⟨p, f, hf, _, he⟩ := nonzero_fibre_torus C ε hε hε1 hC hR ht0 ht
  rw [← he]
  exact isPathConnected_range hf.continuous

include hε hε1 hC hR in
theorem fibre_connected (t : disc ε) : IsConnected (projection C ε ⁻¹' {(t : ℂ)}) := by
  by_cases ht0 : (t : ℂ) = 0
  · rw [ht0]
    exact central_fibre_connected C ε hε
  · have ht : ‖(t : ℂ)‖ < ε := by
      have htball : (t : ℂ) ∈ Metric.ball 0 ε := t.2
      simpa only [Metric.mem_ball, dist_zero_right] using htball
    exact (nonzero_fibre_pathConnected C ε hε hε1 hC hR ht0 ht).isConnected

end Wikipedia.HopfProblem.CuspUniformization
