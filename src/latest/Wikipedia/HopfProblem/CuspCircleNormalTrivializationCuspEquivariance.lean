import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspBasic
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationEquivariance

/-!
# The normal-product map intertwines the original circle action

Unit scalar multiplication preserves the actual uniform normal-radius
domain. On that original domain, the product map is equivariant for the
unchanged threefold action, not merely for its tangent representation.
The proof passes through the two actual affine cusp coordinate maps.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction

local notation "CD" => CuspGeometry.data

/-- Unit scalar multiplication preserves the exact normal-radius bound. -/
theorem normalRadius_unit_smul (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (v : Fibre)
    (hv : radiusSq v < 4 * (CD).radius) :
    radiusSq ((u : ℂ) • v) < 4 * (CD).radius := by
  rw [radiusSq_unit_smul (u : ℂ) hu]
  exact hv

/-- The actual unit-circle rotation on the unchanged small normal product. -/
def normalProductAction (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : smallNormalProduct) : smallNormalProduct :=
  ⟨((p : RiemannSphere × Fibre).1, (u : ℂ) • (p : RiemannSphere × Fibre).2),
    normalRadius_unit_smul u hu _ p.property⟩

@[simp] theorem normalProductAction_coe (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : smallNormalProduct) :
    (normalProductAction u hu p : RiemannSphere × Fibre) =
      ((p : RiemannSphere × Fibre).1, (u : ℂ) • (p : RiemannSphere × Fibre).2) := rfl

@[simp] theorem normalProductAction_radiusSq (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : smallNormalProduct) :
    radiusSq (normalProductAction u hu p : RiemannSphere × Fibre).2 =
      radiusSq (p : RiemannSphere × Fibre).2 :=
  radiusSq_unit_smul (u : ℂ) hu _

@[simp] theorem normalProductAction_norm (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : smallNormalProduct) :
    ‖(normalProductAction u hu p : RiemannSphere × Fibre).2‖ =
      ‖(p : RiemannSphere × Fibre).2‖ :=
  norm_unit_smul (u : ℂ) hu _

@[simp] theorem normalProductAction_zeroSection (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : RiemannSphere) : normalProductAction u hu (zeroSection p) = zeroSection p := by
  apply Subtype.ext
  exact Prod.ext rfl (smul_zero _)

/-- Each unit rotation is continuous on the original open product domain. -/
theorem normalProductAction_continuous (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    Continuous (normalProductAction u hu) := by
  have h : Continuous (fun p : smallNormalProduct =>
      ((p : RiemannSphere × Fibre).1, (u : ℂ) • (p : RiemannSphere × Fibre).2)) :=
    continuous_subtype_val.fst.prodMk
      ((continuous_const : Continuous (fun _ : smallNormalProduct => (u : ℂ))).smul
        continuous_subtype_val.snd)
  exact h.subtype_mk _

/-- The action on either original base chart is the literal scalar normal action. -/
@[simp] theorem normalProductAction_baseProductChart (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (b : Bool) (q : Model) (hq : radiusSq q.2 < 4 * (CD).radius) :
    normalProductAction u hu ⟨baseProductChart b q, hq⟩ =
      (⟨baseProductChart b (q.1, (u : ℂ) • q.2),
        normalRadius_unit_smul u hu q.2 hq⟩ : smallNormalProduct) :=
  Subtype.ext rfl

/-- Equivariance of the original affine coordinate point, before the cusp quotient. -/
theorem coordinateAction_coordinatePoint (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (q : Model) (hq : radiusSq q.2 < 4 * (CD).radius) :
    FixedCoordinates.coordinateAction u (coordinatePoint b q hq) =
      coordinatePoint b (q.1, (u : ℂ) • q.2) (normalRadius_unit_smul u hu q.2 hq) := by
  apply Subtype.ext
  exact diagonal_chartCoordinates_symm b u hu q.1 q.2

/-- Exact equivariance for the actual multiplicative action on the original threefold. -/
theorem globalProductMap_normalProductAction (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : smallNormalProduct) :
    actionBiholomorph u (globalProductMap p) =
      globalProductMap (normalProductAction u hu p) := by
  obtain ⟨b, q, hq⟩ := baseProductChart_cover (p : RiemannSphere × Fibre)
  have hbound : radiusSq q.2 < 4 * (CD).radius := by
    have hp := p.property
    rw [← hq] at hp
    exact hp
  have hp : p = (⟨baseProductChart b q, hbound⟩ : smallNormalProduct) :=
    Subtype.ext hq.symm
  rw [hp, normalProductAction_baseProductChart, globalProductMap_baseProductChart,
    globalProductMap_baseProductChart, FixedCoordinates.globalMap_coordinateAction,
    coordinateAction_coordinatePoint b u hu]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
