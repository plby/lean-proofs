import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryVarying
import Wikipedia.HopfProblem.CuspCentralCohomologyTransport
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyCoordinates

/-!
# Actual circle transport and its original four-period monodromy

The jointly continuous varying family gives homeomorphisms between the
literal time fibres.  The one-turn self-map is defined as the endpoint
of this transport, using the periodicity of the actual base circle.
Only afterwards is it identified with the source shear and with `M₀`
in the original four-period marking.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspQuotient PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε)

/-- Transport from an arbitrary starting angle to the angle advanced
by `s`, between the original quotient fibres. -/
def varyingCircleTransport (r s : ℝ) :
    ActualQuotientFibre C ε (rotatedLevel ρ r) ≃ₜ
      ActualQuotientFibre C ε (rotatedLevel ρ (r + s)) :=
  (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm.trans
    (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD (r + s))

/-- The transport varies jointly continuously in its time and starting
point, with values in the unchanged ambient quotient tube. -/
theorem varyingCircleTransport_joint_continuous (r : ℝ) :
    Continuous (fun p : ℝ × ActualQuotientFibre C ε (rotatedLevel ρ r) =>
      (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRD r p.1 p.2 :
        QuotientSpace C ε)) := by
  have hp : Continuous (fun p : ℝ × ActualQuotientFibre C ε (rotatedLevel ρ r) =>
      (r + p.1,
        (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm p.2)) :=
    (continuous_const.add continuous_fst).prodMk
      ((varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm.continuous.comp
        continuous_snd)
  simpa only [Function.comp_def, varyingCircleFamily, varyingCircleTransport,
    Homeomorph.trans_apply] using
    (varyingCircleFamily_continuous C ρ hρ ε hε hε1 hρε hC hRC hRD).comp hp

/-- The transport covers the literal positive base circle. -/
@[simp] theorem varyingCircleTransport_base (r s : ℝ)
    (x : ActualQuotientFibre C ε (rotatedLevel ρ r)) :
    projection C ε
      (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRD r s x : QuotientSpace C ε) =
      rotatedLevel ρ (r + s) :=
  (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRD r s x).2

@[simp] theorem varyingCircleTransport_zero (r : ℝ)
    (x : ActualQuotientFibre C ε (rotatedLevel ρ r)) :
    (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRD r 0 x : QuotientSpace C ε) =
      (x : QuotientSpace C ε) := by
  change (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD (r + 0)
    ((varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm x) :
      QuotientSpace C ε) = (x : QuotientSpace C ε)
  rw [add_zero, Homeomorph.apply_symm_apply]

/-- A full positive turn has the geometric source-shear endpoint. -/
theorem varyingCircleTransport_one (r : ℝ)
    (x : ActualQuotientFibre C ε (rotatedLevel ρ r)) :
    (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRD r 1 x : QuotientSpace C ε) =
      (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
        (sourceShear (C 0)
          ((varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm x)) :
            QuotientSpace C ε) := by
  simpa only [varyingCircleFamily, varyingCircleTransport, Homeomorph.trans_apply] using
    varyingCircleFamily_add_one C ρ hρ ε hε hε1 hρε hC hRC hRD r
      ((varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm x)

/-- The actual positive-circle endpoint, made into a self-map of its
starting fibre by the proved periodicity of the original base coordinate. -/
def varyingCircleMonodromy (r : ℝ) :
    C(ActualQuotientFibre C ε (rotatedLevel ρ r), ActualQuotientFibre C ε (rotatedLevel ρ r)) where
  toFun x := ⟨(varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRD r 1 x :
      QuotientSpace C ε),
    (varyingCircleTransport_base C ρ hρ ε hε hε1 hρε hC hRC hRD r 1 x).trans
      (rotatedLevel_add_one ρ r)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRD r 1).continuous

/-- The self-map is literally the endpoint of the actual transport. -/
@[simp] theorem varyingCircleMonodromy_coe (r : ℝ)
    (x : ActualQuotientFibre C ε (rotatedLevel ρ r)) :
    (varyingCircleMonodromy C ρ hρ ε hε hε1 hρε hC hRC hRD r x : QuotientSpace C ε) =
      (varyingCircleTransport C ρ hρ ε hε hε1 hρε hC hRC hRD r 1 x : QuotientSpace C ε) := rfl

/-- The actual endpoint agrees with the source-shear conjugate; this
identity is proved from the family, not used to define the endpoint. -/
theorem varyingCircleMonodromy_eq_source_conjugate (r : ℝ) :
    varyingCircleMonodromy C ρ hρ ε hε hε1 hρε hC hRC hRD r =
      (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r :
        C(SourceModel (C 0), ActualQuotientFibre C ε (rotatedLevel ρ r))).comp
          ((sourceShear (C 0)).comp
            ((varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm :
              C(ActualQuotientFibre C ε (rotatedLevel ρ r), SourceModel (C 0)))) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact varyingCircleTransport_one C ρ hρ ε hε hε1 hρε hC hRC hRD r x

/-- The original ordered four-period source marking on the actual
fibre at any chosen initial angle. -/
def varyingCircleTorusHomeomorph (r : ℝ) :
    ProductTorus 4 ≃ₜ ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  (sourceCoordinateTorusHomeomorph (C 0)).symm.trans
    (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r)

@[simp] theorem varyingCircleTorusHomeomorph_apply (r : ℝ) (a : ProductTorus 4) :
    varyingCircleTorusHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r a =
      varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
        ((sourceCoordinateTorusHomeomorph (C 0)).symm a) := rfl

@[simp] theorem varyingCircleTorusHomeomorph_symm_apply (r : ℝ)
    (x : ActualQuotientFibre C ε (rotatedLevel ρ r)) :
    (varyingCircleTorusHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm x =
      sourceCoordinateTorusHomeomorph (C 0)
        ((varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm x) := rfl

/-- Positive-circle transport has exactly the literal `M₀` self-map in
the original four-period marking. No inverse-dual action is substituted. -/
theorem varyingCircleMonodromy_eq_markedFibreMonodromy (r : ℝ) :
    varyingCircleMonodromy C ρ hρ ε hε hε1 hρε hC hRC hRD r =
      CuspCentralCohomology.markedFibreMonodromy
        (varyingCircleTorusHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r) := by
  rw [varyingCircleMonodromy_eq_source_conjugate]
  apply ContinuousMap.ext
  intro x
  change varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
      (sourceShear (C 0)
        ((varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm x)) =
    varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
      ((sourceCoordinateTorusHomeomorph (C 0)).symm
        (torusMatrixMap M₀ (sourceCoordinateTorusHomeomorph (C 0)
          ((varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).symm x))))
  apply congrArg (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r)
  apply (sourceCoordinateTorusHomeomorph (C 0)).injective
  rw [Homeomorph.apply_symm_apply, sourceCoordinateTorusHomeomorph_shear]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
