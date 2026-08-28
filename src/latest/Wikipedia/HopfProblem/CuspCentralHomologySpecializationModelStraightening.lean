import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProjection
import Wikipedia.HopfProblem.CuspRetractionHomeomorph
import Wikipedia.HopfProblem.CuspHoneycombClosedCover

/-!
# Genuine change of twist on the original fixed-time fibres

The already constructed change-of-twist map preserves time and restricts
to a homeomorphism of each literal toric fibre in its small tube. Its exact
equivariance for the original deck translations then descends to the
actual quotient fibres, with their inherited quotient topology.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction

variable (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

/-- Restrict the genuine ambient change of twist without changing the
fixed-time space or its topology. -/
def toricFibreChangeTwist (t : ℂ) (x : ToricFibre t) : ToricFibre t :=
  ⟨changeTwist C D x, (time_changeTwist C D x).trans x.2⟩

@[simp] theorem toricFibreChangeTwist_coe (t : ℂ) (x : ToricFibre t) :
    (toricFibreChangeTwist C D t x : Space) = changeTwist C D x := rfl

variable (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContDiffOn ℂ ω (fun z => D z i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (t : ℂ) (htε : ‖t‖ < ε)

/-- The fixed-time homeomorphism is the literal restriction of
`changeTwist C D`, with inverse `changeTwist D C`. -/
def toricFibreChangeTwistHomeomorph : ToricFibre t ≃ₜ ToricFibre t where
  toFun := toricFibreChangeTwist C D t
  invFun := toricFibreChangeTwist D C t
  left_inv x := Subtype.ext (changeTwist_inverse_on_disc C D hε1 hRC hRD (by
    rw [x.2]
    exact htε))
  right_inv x := Subtype.ext (changeTwist_inverse_on_disc D C hε1 hRD hRC (by
    rw [x.2]
    exact htε))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (changeTwist_continuousOn C D hε hε1
      (fun i j => (hC i j).continuousOn) (fun i j => (hD i j).continuousOn)
      hzero hRC).comp_continuous continuous_subtype_val (fun x => by
        change time (x : Space) ∈ Metric.ball 0 ε
        rw [x.2]
        simpa only [Metric.mem_ball, dist_zero_right] using htε)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (changeTwist_continuousOn D C hε hε1
      (fun i j => (hD i j).continuousOn) (fun i j => (hC i j).continuousOn)
      hzero.symm hRD).comp_continuous continuous_subtype_val (fun x => by
        change time (x : Space) ∈ Metric.ball 0 ε
        rw [x.2]
        simpa only [Metric.mem_ball, dist_zero_right] using htε)

@[simp] theorem toricFibreChangeTwistHomeomorph_coe (x : ToricFibre t) :
    (toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε x : Space) =
      changeTwist C D (x : Space) := rfl

@[simp] theorem toricFibreChangeTwistHomeomorph_symm_coe (x : ToricFibre t) :
    ((toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε).symm x :
      Space) = changeTwist D C (x : Space) := rfl

/-- Exact equivariance uses the original integral labels and twists. -/
theorem toricFibreChangeTwistHomeomorph_equivariant (v : Fin 2 → ℤ) (x : ToricFibre t) :
    toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε
      (toricFibreTranslate C t v x) =
        toricFibreTranslate D t v
          (toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε x) :=
  Subtype.ext (changeTwist_equivariant_on_disc C D hzero hε1 hRC v (by
    rw [x.2]
    exact htε))

theorem toricFibreChangeTwistHomeomorph_symm_equivariant (v : Fin 2 → ℤ) (x : ToricFibre t) :
    (toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε).symm
      (toricFibreTranslate D t v x) =
        toricFibreTranslate C t v
          ((toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε).symm x) :=
  Subtype.ext (changeTwist_equivariant_on_disc D C hzero.symm hε1 hRD v (by
    rw [x.2]
    exact htε))

/-- The actual change of twist preserves and reflects the entire original
fixed-fibre quotient relation, with no additional equivalence closure. -/
theorem fibreProjection_changeTwist_eq_iff (x y : ToricFibre t) :
    fibreProjection C ε t htε x = fibreProjection C ε t htε y ↔
      fibreProjection D ε t htε
        (toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε x) =
      fibreProjection D ε t htε
        (toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε y) := by
  let e := toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε
  have he (v : Fin 2 → ℤ) (z : ToricFibre t) :
      e (toricFibreTranslate C t v z) = toricFibreTranslate D t v (e z) :=
    toricFibreChangeTwistHomeomorph_equivariant C D ε hε hε1 hC hD hzero hRC hRD t htε v z
  change fibreProjection C ε t htε x = fibreProjection C ε t htε y ↔
    fibreProjection D ε t htε (e x) = fibreProjection D ε t htε (e y)
  rw [fibreProjection_eq_iff, fibreProjection_eq_iff]
  apply exists_congr
  intro v
  change ((toricFibreTranslate C t v y : ToricFibre t) : Space) = (x : Space) ↔
    ((toricFibreTranslate D t v (e y) : ToricFibre t) : Space) = (e x : Space)
  rw [← Subtype.ext_iff, ← Subtype.ext_iff, ← he v y, e.injective.eq_iff]

/-- The genuine change of twist descends to a homeomorphism of the actual
quotient fibres, not of replacement spaces endowed with chosen topologies. -/
def actualFibreChangeTwistHomeomorph :
    ActualQuotientFibre C ε t ≃ₜ ActualQuotientFibre D ε t :=
  CuspHoneycombClosedCover.quotientHomeomorph
    (fibreProjection C ε t htε)
    (fibreProjection D ε t htε ∘
      toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε)
    (fibreProjection_isQuotientMap C ε t htε hC)
    ((fibreProjection_isQuotientMap D ε t htε hD).comp
      (toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε).isQuotientMap)
    (fibreProjection_changeTwist_eq_iff C D ε hε hε1 hC hD hzero hRC hRD t htε)

/-- The descended homeomorphism is exactly the original change of twist
on every actual fixed-time representative. -/
@[simp] theorem actualFibreChangeTwistHomeomorph_fibreProjection (x : ToricFibre t) :
    actualFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε
      (fibreProjection C ε t htε x) =
        fibreProjection D ε t htε
          (toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε x) :=
  CuspHoneycombClosedCover.quotientHomeomorph_apply _ _ _ _ _ x

@[simp] theorem actualFibreChangeTwistHomeomorph_symm_fibreProjection (x : ToricFibre t) :
    (actualFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε).symm
      (fibreProjection D ε t htε x) =
        fibreProjection C ε t htε
          ((toricFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε).symm x) := by
  apply (actualFibreChangeTwistHomeomorph C D ε hε hε1 hC hD hzero hRC hRD t htε).injective
  rw [Homeomorph.apply_symm_apply, actualFibreChangeTwistHomeomorph_fibreProjection,
    Homeomorph.apply_symm_apply]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
