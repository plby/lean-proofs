import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryTransport
import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryCircleRadius
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMarkedModels

/-!
# Physical circle transport in the actual specialization marking

The torus marking in this file is the marking of the independently
prescribed specialization model.  Its `M₀` self-map is the endpoint of
jointly continuous transport through the original nonzero fibres.  The
representative-preserving change of ambient radius retains both facts.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspQuotient
open PeriodTorusHigherHomology SingularMayerVietoris CuspCentralCohomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRF : SmallDrift (frozen C) ε) (a : ℝ)

/-- The actual endpoint identification is realized by a jointly
continuous circle of literal fibre homeomorphisms. -/
theorem varyingCircleTorusHomeomorph_hasMarkedCircleTransport :
    HasMarkedCircleTransport C ε (rotatedLevel ρ a)
      (varyingCircleTorusHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRF a) := by
  refine ⟨fun s =>
    (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRF a s).trans
      (actualFibreLevelCongr C ε (rotatedLevel_add ρ a s)), ?_, ?_, ?_⟩
  · simpa only [Homeomorph.trans_apply, actualFibreLevelCongr_coe] using
      varyingCircleTransport_joint_continuous C ρ hρ ε hε hε1 hρε hC hRC hRF a
  · intro x
    simpa only [Homeomorph.trans_apply, actualFibreLevelCongr_coe] using
      varyingCircleTransport_zero C ρ hρ ε hε hε1 hρε hC hRC hRF a x
  · intro x
    change (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRF a 1 x :
      QuotientSpace C ε) = _
    rw [← varyingCircleMonodromy_coe,
      varyingCircleMonodromy_eq_markedFibreMonodromy]

/-- The geometric transport uses exactly the product specialization
marking in the original period order, not an unrelated marking. -/
theorem varyingCircleTorusHomeomorph_eq_product :
    varyingCircleTorusHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRF a =
      sourceProductCoordinateHomeomorph.symm.trans
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRF a) := by
  apply Homeomorph.ext
  intro x
  rfl

variable (r : ℝ) (hεr : ε ≤ r)
    (hCr : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- Exact agreement with the already constructed original-radius
specialization marking. -/
theorem radiusMarkedHomeomorph_eq_varyingCircle :
    radiusMarkedHomeomorph C r ε (rotatedLevel ρ a) hεr hCr
      (rotatedLevel_norm_lt ρ a hρ.le ε hρε)
      (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRF a) =
    (varyingCircleTorusHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRF a).trans
      (fibreRadiusHomeomorph C r ε (rotatedLevel ρ a) hεr hCr
        (rotatedLevel_norm_lt ρ a hρ.le ε hρε)) := by
  apply Homeomorph.ext
  intro x
  rfl

/-- The original-radius marking has the same physical full-turn
transport, because ambient radius change keeps the actual representatives. -/
theorem radiusMarkedHomeomorph_hasMarkedCircleTransport :
    HasMarkedCircleTransport C r (rotatedLevel ρ a)
      (radiusMarkedHomeomorph C r ε (rotatedLevel ρ a) hεr hCr
        (rotatedLevel_norm_lt ρ a hρ.le ε hρε)
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRF a)) := by
  rw [radiusMarkedHomeomorph_eq_varyingCircle]
  exact HasMarkedCircleTransport.radius C r ε (rotatedLevel ρ a) hεr hCr
    (rotatedLevel_norm_lt ρ a hρ.le ε hρε)
    (varyingCircleTorusHomeomorph_hasMarkedCircleTransport
      C ρ hρ ε hε hε1 hρε hC hRC hRF a)

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
