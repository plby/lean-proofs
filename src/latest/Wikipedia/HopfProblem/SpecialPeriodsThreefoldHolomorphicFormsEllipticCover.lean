import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticGeometry
import Wikipedia.HopfProblem.EllipticLogGaugeBasic

/-!
# The actual root-coordinate cover of each small elliptic filling

Restrict the genuine period-vector cover to the inverse image of the
chosen small base disc under the third or fourth power. Its composite
with the actual affine quotient lands in the original small filling
piece and then in the constructed global threefold. Every map is
holomorphic for the already selected native atlases, including at root
zero. The quotient has exactly the original power-coordinate projection.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic EllipticFilling Triangle

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace triangleCompactifiedChartedSpace

/-- The literal root domain of the selected small elliptic base disc. -/
def rootDomain (j : Kind) : TopologicalSpace.Opens Disc :=
  ⟨{z | ‖(z : ℂ) ^ j.order‖ < specialBaseCover.radius (some j)},
    isOpen_lt (continuous_subtype_val.pow j.order).norm continuous_const⟩

abbrev Root (j : Kind) := rootDomain j

@[simp] theorem mem_rootDomain (j : Kind) (z : Disc) :
    z ∈ rootDomain j ↔ ‖(z : ℂ) ^ j.order‖ < specialBaseCover.radius (some j) := Iff.rfl

theorem rootDomain_isOpen (j : Kind) : IsOpen (rootDomain j : Set Disc) :=
  (rootDomain j).isOpen

theorem discZero_mem_rootDomain (j : Kind) : SpecialPeriods.discZero ∈ rootDomain j := by
  change ‖(0 : ℂ) ^ j.order‖ < specialBaseCover.radius (some j)
  rw [zero_pow j.order_pos.ne', norm_zero]
  exact specialBaseCover.radius_pos (some j)

/-- Root zero belongs to the genuine open domain, without shrinking away
the central fibre. -/
def rootZero (j : Kind) : Root j := ⟨SpecialPeriods.discZero, discZero_mem_rootDomain j⟩

@[simp] theorem rootZero_coe (j : Kind) :
    (rootZero j : Disc) = SpecialPeriods.discZero := rfl

theorem rootDomain_mem_nhds (j : Kind) :
    (rootDomain j : Set Disc) ∈ 𝓝 SpecialPeriods.discZero :=
  (rootDomain_isOpen j).mem_nhds (discZero_mem_rootDomain j)

/-- The unchanged complex root coordinate on the nested open subspace. -/
def rootCoordinate (j : Kind) (z : Root j) : ℂ := ((z : Disc) : ℂ)

@[simp] theorem rootCoordinate_rootZero (j : Kind) : rootCoordinate j (rootZero j) = 0 := rfl

theorem rootCoordinate_holomorphic (j : Kind) : ContMDiff I₁ I₁ ω (rootCoordinate j) :=
  contMDiff_subtype_val.comp contMDiff_subtype_val

theorem root_isManifold (j : Kind) : IsManifold I₁ ω (Root j) := inferInstance

/-- The original complex period-vector coordinates over the actual root domain. -/
abbrev Cover (j : Kind) := Root j × ComplexPlane₂

/-- The inherited product atlas, written in the family's product model. -/
@[instance_reducible] def coverChartedSpace (j : Kind) : ChartedSpace FamilyModel (Cover j) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Root j × ComplexPlane₂))

attribute [local instance] coverChartedSpace

local instance discCoverChartedSpace : ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

theorem cover_isManifold (j : Kind) : IsManifold IF ω (Cover j) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) (Root j) ComplexPlane₂

/-- Forget only the small-radius restriction, retaining the original
disc root and both original complex fibre coordinates. -/
def coverToPeriod (j : Kind) (x : Cover j) : Disc × ComplexPlane₂ := (x.1, x.2)

@[simp] theorem coverToPeriod_apply (j : Kind) (x : Cover j) :
    coverToPeriod j x = ((x.1 : Disc), x.2) := rfl

theorem coverToPeriod_holomorphic (j : Kind) : ContMDiff IF IF ω (coverToPeriod j) := by
  rw [modelWithCornersSelf_prod]
  exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd

/-- The actual period cover followed by the actual main affine quotient. -/
def fullCover (j : Kind) (x : Cover j) : SpecialFullFilling j :=
  (specialLocalData j).quotient j.twist (mainTwist_admissible j)
    ((specialLocalData j).periods.quotientMap (coverToPeriod j x))

@[simp] theorem fullCover_projection (j : Kind) (x : Cover j) :
    (specialFullFillingProjection j (fullCover j x) : ℂ) =
      rootCoordinate j x.1 ^ j.order := rfl

theorem fullCover_mem_piece (j : Kind) (x : Cover j) :
    fullCover j x ∈ pieceDomain specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j := by
  change ‖(specialFullFillingProjection j (fullCover j x) : ℂ)‖ <
    specialBaseCover.radius (some j)
  rw [fullCover_projection]
  exact x.1.property

theorem fullCover_holomorphic (j : Kind) : ContMDiff IF IF ω (fullCover j) := by
  let := (specialLocalData j).periods.totalChartedSpace
  let := (specialLocalData j).chartedSpace j.twist (mainTwist_admissible j)
  exact ((specialLocalData j).quotient_holomorphic j.twist (mainTwist_admissible j)).comp
    ((specialLocalData j).periods.quotientMap_holomorphic.comp (coverToPeriod_holomorphic j))

/-- The same actual quotient map, with its proved values in the original
small filling piece and its inherited open-submanifold atlas. -/
def localCover (j : Kind) (x : Cover j) : EllipticGeometry.LocalSpace j :=
  ⟨fullCover j x, fullCover_mem_piece j x⟩

@[simp] theorem localCover_coe (j : Kind) (x : Cover j) :
    (localCover j x : SpecialFullFilling j) = fullCover j x := rfl

theorem localCover_quotient (j : Kind) (x : Cover j) :
    (localCover j x : SpecialFullFilling j) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        ((specialLocalData j).periods.quotientMap ((x.1 : Disc), x.2)) := rfl

@[simp] theorem localCover_parameter (j : Kind) (x : Cover j) :
    EllipticGeometry.parameter j (localCover j x) = rootCoordinate j x.1 ^ j.order := rfl

theorem localCover_holomorphic (j : Kind) : ContMDiff IF IF ω (localCover j) := by
  intro x
  have he : ContMDiffAt IF IF ω
      (fun y : Cover j => (localCover j y : SpecialFullFilling j)) x ↔
      ContMDiffAt IF IF ω (localCover j) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (fullCover_holomorphic j x)

/-- The root-coordinate cover reaches every point of the actual small piece. -/
theorem localCover_surjective (j : Kind) : Surjective (localCover j) := by
  intro y
  obtain ⟨a, ha⟩ :=
    (specialLocalData j).quotient_surjective j.twist (mainTwist_admissible j) y.val
  obtain ⟨x, hx⟩ := (specialLocalData j).periods.quotientMap_surjective a
  have hcover : (specialLocalData j).quotient j.twist (mainTwist_admissible j)
      ((specialLocalData j).periods.quotientMap x) = y.val :=
    (congrArg ((specialLocalData j).quotient j.twist (mainTwist_admissible j)) hx).trans ha
  have hpower := congrArg (fun z => (specialFullFillingProjection j z : ℂ)) hcover
  change (x.1 : ℂ) ^ j.order = (specialFullFillingProjection j y.val : ℂ) at hpower
  have hroot : x.1 ∈ rootDomain j := by
    change ‖(x.1 : ℂ) ^ j.order‖ < specialBaseCover.radius (some j)
    rw [hpower]
    exact y.property
  refine ⟨(⟨x.1, hroot⟩, x.2), Subtype.ext ?_⟩
  exact hcover

theorem localCover_projection_mem_regular_iff (j : Kind) (x : Cover j) :
    specialEllipticPieceProjectionToBase j (localCover j x) ∈ regularPatch ↔
      rootCoordinate j x.1 ≠ 0 := by
  change pieceProjectionToBase specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j (localCover j x) ∈ regularPatch ↔ _
  rw [pieceProjectionToBase_mem_regular_iff]
  change rootCoordinate j x.1 ^ j.order ≠ 0 ↔ rootCoordinate j x.1 ≠ 0
  constructor
  · intro h hz
    exact h (by rw [hz, zero_pow j.order_pos.ne'])
  · intro h
    exact pow_ne_zero j.order h

/-- The genuine global map from the root-coordinate cover into the
constructed threefold, including above root zero. -/
def globalCover (j : Kind) (x : Cover j) : Threefold.Space :=
  EllipticGeometry.inclusion j (localCover j x)

@[simp] theorem globalCover_apply (j : Kind) (x : Cover j) :
    globalCover j x = EllipticGeometry.inclusion j (localCover j x) := rfl

theorem globalCover_holomorphic (j : Kind) : ContMDiff IF IF ω (globalCover j) :=
  (EllipticGeometry.inclusion_holomorphic j).comp (localCover_holomorphic j)

theorem globalCover_projection (j : Kind) (x : Cover j) :
    Threefold.projection (globalCover j x) =
      (punctureChart (some j)).symm (rootCoordinate j x.1 ^ j.order) :=
  EllipticGeometry.projection_inclusion j (localCover j x)

theorem globalCover_projection_mem_regular_iff (j : Kind) (x : Cover j) :
    Threefold.projection (globalCover j x) ∈ regularPatch ↔ rootCoordinate j x.1 ≠ 0 := by
  change Threefold.projection (EllipticGeometry.inclusion j (localCover j x)) ∈
    regularPatch ↔ _
  rw [EllipticGeometry.projection_inclusion]
  exact localCover_projection_mem_regular_iff j x

@[simp] theorem globalCover_rootZero_projection (j : Kind) (u : ComplexPlane₂) :
    Threefold.projection (globalCover j (rootZero j, u)) = puncturePoint (some j) := by
  rw [globalCover_projection, rootCoordinate_rootZero, zero_pow j.order_pos.ne',
    punctureChart_symm_zero]

/-- Adding any vector of the actual period lattice leaves the original
full-filling point unchanged. -/
theorem fullCover_add_period (j : Kind) (z : Root j) (u w : ComplexPlane₂)
    (hw : w ∈ ((specialLocalData j).periods.point (z : Disc)).lattice) :
    fullCover j (z, u + w) = fullCover j (z, u) := by
  apply congrArg ((specialLocalData j).quotient j.twist (mainTwist_admissible j))
  change (specialLocalData j).periods.quotientMap ((z : Disc), u + w) =
    (specialLocalData j).periods.quotientMap ((z : Disc), u)
  rw [← (specialLocalData j).periods.fibreInclusion_mkQ,
    ← (specialLocalData j).periods.fibreInclusion_mkQ]
  apply congrArg ((specialLocalData j).periods.fibreInclusion (z : Disc))
  apply (Submodule.Quotient.eq _).mpr
  simpa only [add_sub_cancel_left] using hw

theorem localCover_add_period (j : Kind) (z : Root j) (u w : ComplexPlane₂)
    (hw : w ∈ ((specialLocalData j).periods.point (z : Disc)).lattice) :
    localCover j (z, u + w) = localCover j (z, u) :=
  Subtype.ext (fullCover_add_period j z u w hw)

theorem globalCover_add_period (j : Kind) (z : Root j) (u w : ComplexPlane₂)
    (hw : w ∈ ((specialLocalData j).periods.point (z : Disc)).lattice) :
    globalCover j (z, u + w) = globalCover j (z, u) :=
  congrArg (EllipticGeometry.inclusion j) (localCover_add_period j z u w hw)

/-- Translation by an actual varying period with the specified integral marking. -/
def periodTranslation (j : Kind) (ℓ : Lattice) (x : Cover j) : Cover j :=
  (x.1, x.2 + LogGauge.periodVector (specialLocalData j).periods ℓ (x.1 : Disc))

@[simp] theorem periodTranslation_apply (j : Kind) (ℓ : Lattice) (x : Cover j) :
    periodTranslation j ℓ x =
      (x.1, x.2 + LogGauge.periodVector (specialLocalData j).periods ℓ (x.1 : Disc)) := rfl

theorem periodTranslation_holomorphic (j : Kind) (ℓ : Lattice) :
    ContMDiff IF IF ω (periodTranslation j ℓ) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst.prodMk (contMDiff_snd.add
    (((LogGauge.periodVector_holomorphic (specialLocalData j).periods ℓ).comp
      contMDiff_subtype_val).comp contMDiff_fst))

theorem localCover_periodTranslation (j : Kind) (ℓ : Lattice) (x : Cover j) :
    localCover j (periodTranslation j ℓ x) = localCover j x :=
  localCover_add_period j x.1 x.2 _
    (LogGauge.periodVector_mem_lattice (specialLocalData j).periods ℓ (x.1 : Disc))

theorem globalCover_periodTranslation (j : Kind) (ℓ : Lattice) (x : Cover j) :
    globalCover j (periodTranslation j ℓ x) = globalCover j x :=
  congrArg (EllipticGeometry.inclusion j) (localCover_periodTranslation j ℓ x)

/-- Insert the zero complex fibre vector, without changing the root. -/
def zeroSection (j : Kind) (z : Root j) : Cover j := (z, 0)

@[simp] theorem zeroSection_apply (j : Kind) (z : Root j) : zeroSection j z = (z, 0) := rfl

theorem zeroSection_holomorphic (j : Kind) : ContMDiff I₁ IF ω (zeroSection j) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_id.prodMk contMDiff_const

theorem globalCover_zeroSection_holomorphic (j : Kind) :
    ContMDiff I₁ IF ω (globalCover j ∘ zeroSection j) :=
  (globalCover_holomorphic j).comp (zeroSection_holomorphic j)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
