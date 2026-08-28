import Wikipedia.HopfProblem.EllipticLogGaugeConjugacy
import Wikipedia.HopfProblem.EllipticLogGaugeHolomorphic
import Wikipedia.HopfProblem.EllipticLogGaugeOpenQuotient
import Wikipedia.HopfProblem.EllipticEquivariantFillings

/-!
# The punctured logarithmic filling and the tautological punctured quotient

Every invariant affine twist acts freely away from the central fibre,
including the zero twist.  We form the actual punctured orbit quotients
with their covering-lift atlases.  The logarithmic gauge descends between
these quotients and identifies the punctured part of an admissible filling
with the untwisted punctured quotient, preserving the powered base map.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

local notation "IF" => modelWithCornersSelf ℂ FamilyModel
local notation "I₁" => modelWithCornersSelf ℂ ℂ

local instance discLocallyCompact : LocallyCompactSpace Disc := unitDisc.isOpen.locallyCompactSpace
local instance familyStarLocallyCompact : LocallyCompactSpace familyOpen :=
  familyOpen.isOpen.locallyCompactSpace

variable {j : Kind} (D : Equivariant.Data j)

/-- A fresh type for the actual orbit quotient on the punctured family.
Unlike the whole filling, this exists also for the invariant zero twist. -/
def StarQuotient (v : Lattice) (hv : j.matrix *ᵥ v = v) : Type :=
  @FiniteQuotient.Space (CyclicGroup j) (FamilyStar D.periods) _ (starAction D v hv)

instance starTopology (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    TopologicalSpace (StarQuotient D v hv) :=
  inferInstanceAs (TopologicalSpace
    (@FiniteQuotient.Space (CyclicGroup j) (FamilyStar D.periods) _ (starAction D v hv)))

def starProject (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    FamilyStar D.periods → StarQuotient D v hv :=
  @FiniteQuotient.project (CyclicGroup j) (FamilyStar D.periods) _ (starAction D v hv)

theorem starProject_surjective (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    Function.Surjective (starProject D v hv) := Quotient.mk_surjective

theorem starProject_continuous (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    Continuous (starProject D v hv) := by
  let := starAction D v hv
  exact FiniteQuotient.project_continuous (CyclicGroup j) (FamilyStar D.periods)

instance starT2Space (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    T2Space (StarQuotient D v hv) := by
  let := starAction D v hv
  let := starAction_continuous D v hv
  exact FiniteQuotient.spaceT2Space (CyclicGroup j) (FamilyStar D.periods)

instance starSecondCountableTopology (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    SecondCountableTopology (StarQuotient D v hv) := by
  let := starAction D v hv
  let := starAction_continuous D v hv
  exact FiniteQuotient.spaceSecondCountableTopology (CyclicGroup j) (FamilyStar D.periods)

instance starLocallyCompactSpace (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    LocallyCompactSpace (StarQuotient D v hv) := by
  let := starAction D v hv
  let := starAction_continuous D v hv
  exact FiniteQuotient.spaceLocallyCompactSpace (CyclicGroup j) (FamilyStar D.periods)

theorem starCoveringMap (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    IsQuotientCoveringMap (starProject D v hv) (CyclicGroup j) := by
  let := starAction D v hv
  let := starAction_continuous D v hv
  let := starAction_free D v hv
  exact FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) (FamilyStar D.periods)

@[instance_reducible] def starChartedSpace (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    ChartedSpace FamilyModel (StarQuotient D v hv) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  exact CoveringQuotient.chartedSpace (E := FamilyModel) (starCoveringMap D v hv)

theorem star_isManifold (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starChartedSpace D v hv
    IsManifold IF ω (StarQuotient D v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := starAction D v hv
  exact CoveringQuotient.isManifold (starCoveringMap D v hv) ω (starAction_holomorphic D v hv)

theorem starProject_holomorphic (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := D.periods.totalChartedSpace
    letI := starChartedSpace D v hv
    ContMDiff IF IF ω (starProject D v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := starAction D v hv
  exact CoveringQuotient.contMDiff_project (starCoveringMap D v hv) ω
    (starAction_holomorphic D v hv)

/-- The untwisted quotient is only taken on the puncture, where its action
really is free. No admissibility of the zero twist is asserted. -/
abbrev TautologicalStar := StarQuotient D 0 (Matrix.mulVec_zero j.matrix)

def gaugeQuotientEquiv (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    StarQuotient D v hv ≃ TautologicalStar D :=
  @quotientEquiv (CyclicGroup j) _ (FamilyStar D.periods) (FamilyStar D.periods)
    (starAction D v hv) (starAction D 0 (Matrix.mulVec_zero j.matrix))
    (gaugeEquiv D.periods v) (gaugeMap_starAction D v hv)

@[simp] theorem gaugeQuotientEquiv_project (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : FamilyStar D.periods) :
    gaugeQuotientEquiv D v hv (starProject D v hv x) =
      starProject D 0 (Matrix.mulVec_zero j.matrix) (gaugeMap D.periods v x) := rfl

@[simp] theorem gaugeQuotientEquiv_symm_project (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : FamilyStar D.periods) :
    (gaugeQuotientEquiv D v hv).symm (starProject D 0 (Matrix.mulVec_zero j.matrix) x) =
      starProject D v hv (gaugeMap D.periods (-v) x) := rfl

def gaugeQuotientBiholomorph (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starChartedSpace D v hv
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph IF IF (StarQuotient D v hv) (TautologicalStar D) ω := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := starChartedSpace D v hv
  let := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
  refine
    { toEquiv := gaugeQuotientEquiv D v hv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · let := starAction D v hv
    apply CoveringQuotient.contMDiff_of_comp (starCoveringMap D v hv) IF ω
    exact (starProject_holomorphic D 0 (Matrix.mulVec_zero j.matrix)).comp
      (gaugeMap_holomorphic D.periods v)
  · let := starAction D 0 (Matrix.mulVec_zero j.matrix)
    apply CoveringQuotient.contMDiff_of_comp
      (starCoveringMap D 0 (Matrix.mulVec_zero j.matrix)) IF ω
    exact (starProject_holomorphic D v hv).comp (gaugeMap_holomorphic D.periods (-v))

@[simp] theorem gaugeQuotientBiholomorph_project (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : FamilyStar D.periods) :
    gaugeQuotientBiholomorph D v hv (starProject D v hv x) =
      starProject D 0 (Matrix.mulVec_zero j.matrix) (gaugeMap D.periods v x) := rfl

def starUpstairsProjection (x : FamilyStar D.periods) : BaseStar :=
  ⟨discPower j.order j.order_pos x.1.1, by
    change (x.1.1 : ℂ) ^ j.order ≠ 0
    exact pow_ne_zero _ x.2⟩

theorem starUpstairsProjection_holomorphic :
    letI := D.periods.totalChartedSpace
    ContMDiff IF I₁ ω (starUpstairsProjection D) := by
  let := D.periods.totalChartedSpace
  have h : ContMDiff IF I₁ ω (fun x : FamilyStar D.periods =>
      (starUpstairsProjection D x : Disc)) :=
    D.upstairsProjection_holomorphic.comp contMDiff_subtype_val
  intro x
  have he : ContMDiffAt IF I₁ ω (fun y => (starUpstairsProjection D y : Disc)) x ↔
      ContMDiffAt IF I₁ ω (starUpstairsProjection D) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (h x)

theorem starUpstairsProjection_invariant (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : FamilyStar D.periods) :
    letI := starAction D v hv
    starUpstairsProjection D (g • x) = starUpstairsProjection D x := by
  let := D.action v hv
  let := starAction D v hv
  apply Subtype.ext
  change discPower j.order j.order_pos ((g • x : FamilyStar D.periods) : D.TotalSpace).1 =
    discPower j.order j.order_pos (x : D.TotalSpace).1
  rw [starAction_coe D v hv]
  exact D.action_discPower v hv g x

def starProjection (v : Lattice) (hv : j.matrix *ᵥ v = v) : StarQuotient D v hv → BaseStar := by
  let := starAction D v hv
  exact FiniteQuotient.descend (starUpstairsProjection D) (starUpstairsProjection_invariant D v hv)

@[simp] theorem starProjection_project (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : FamilyStar D.periods) :
    starProjection D v hv (starProject D v hv x) = starUpstairsProjection D x := rfl

theorem starProjection_holomorphic (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starChartedSpace D v hv
    ContMDiff IF I₁ ω (starProjection D v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := starAction D v hv
  let := starChartedSpace D v hv
  apply CoveringQuotient.contMDiff_of_comp (starCoveringMap D v hv) I₁ ω
  exact starUpstairsProjection_holomorphic D

theorem starProjection_gaugeQuotient (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : StarQuotient D v hv) :
    starProjection D 0 (Matrix.mulVec_zero j.matrix) (gaugeQuotientBiholomorph D v hv x) =
      starProjection D v hv x := by
  obtain ⟨y, rfl⟩ := starProject_surjective D v hv x
  rw [gaugeQuotientBiholomorph_project, starProjection_project, starProjection_project]
  rfl

def fillingOpen (v : Lattice) (hv : AdmissibleTwist j v) :
    TopologicalSpace.Opens (D.Space v hv) :=
  ⟨{x | (D.projection v hv x : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp (D.projection_continuous v hv))
      continuous_const⟩

abbrev FillingStar (v : Lattice) (hv : AdmissibleTwist j v) := fillingOpen D v hv

@[simp] theorem quotient_preimage_fillingOpen (v : Lattice) (hv : AdmissibleTwist j v) :
    (D.quotient v hv) ⁻¹' (fillingOpen D v hv : Set (D.Space v hv)) =
      (familyOpen : Set D.TotalSpace) := by
  ext x
  change (D.projection v hv (D.quotient v hv x) : ℂ) ≠ 0 ↔ (x.1 : ℂ) ≠ 0
  simp only [D.projection_quotient, discPower_coe, ne_eq, pow_eq_zero_iff j.order_pos.ne']

def fillingStarProject (v : Lattice) (hv : AdmissibleTwist j v)
    (x : FamilyStar D.periods) : FillingStar D v hv :=
  ⟨D.quotient v hv x, by
    change (D.projection v hv (D.quotient v hv x) : ℂ) ≠ 0
    rw [D.projection_quotient, discPower_coe]
    exact pow_ne_zero _ x.2⟩

theorem fillingStarProject_surjective (v : Lattice) (hv : AdmissibleTwist j v) :
    Function.Surjective (fillingStarProject D v hv) := by
  let := D.action v hv.1
  exact restrictedProject_surjective (CyclicGroup j) familyOpen (fillingOpen D v hv)
    (quotient_preimage_fillingOpen D v hv)

def fillingStarProjection (v : Lattice) (hv : AdmissibleTwist j v)
    (x : FillingStar D v hv) : BaseStar := ⟨D.projection v hv x, x.2⟩

theorem fillingStarProjection_holomorphic (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    ContMDiff IF I₁ ω (fillingStarProjection D v hv) := by
  let := D.chartedSpace v hv
  have h : ContMDiff IF I₁ ω (fun x : FillingStar D v hv =>
      (fillingStarProjection D v hv x : Disc)) :=
    (D.projection_holomorphic v hv).comp contMDiff_subtype_val
  intro x
  have he : ContMDiffAt IF I₁ ω (fun y => (fillingStarProjection D v hv y : Disc)) x ↔
      ContMDiffAt IF I₁ ω (fillingStarProjection D v hv) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (h x)

def fillingOpenComparison (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := starChartedSpace D v hv.1
    letI := D.chartedSpace v hv
    Diffeomorph IF IF (StarQuotient D v hv.1) (FillingStar D v hv) ω := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  let := starAction D v hv.1
  exact openQuotientBiholomorph (CyclicGroup j) familyOpen (fillingOpen D v hv)
    (starAction_coe D v hv.1) (quotient_preimage_fillingOpen D v hv)
    (D.action_holomorphic v hv.1)

@[simp] theorem fillingOpenComparison_project (v : Lattice) (hv : AdmissibleTwist j v)
    (x : FamilyStar D.periods) :
    fillingOpenComparison D v hv (starProject D v hv.1 x) = fillingStarProject D v hv x := rfl

def fillingToTautologicalBiholomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph IF IF (FillingStar D v hv) (TautologicalStar D) ω := by
  let := D.chartedSpace v hv
  let := starChartedSpace D v hv.1
  let := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
  exact (fillingOpenComparison D v hv).symm.trans (gaugeQuotientBiholomorph D v hv.1)

@[simp] theorem fillingToTautologicalBiholomorph_project (v : Lattice)
    (hv : AdmissibleTwist j v) (x : FamilyStar D.periods) :
    fillingToTautologicalBiholomorph D v hv (fillingStarProject D v hv x) =
      starProject D 0 (Matrix.mulVec_zero j.matrix) (gaugeMap D.periods v x) := rfl

theorem fillingToTautologicalBiholomorph_base (v : Lattice) (hv : AdmissibleTwist j v)
    (x : FillingStar D v hv) :
    starProjection D 0 (Matrix.mulVec_zero j.matrix) (fillingToTautologicalBiholomorph D v hv x) =
      fillingStarProjection D v hv x := by
  obtain ⟨y, rfl⟩ := fillingStarProject_surjective D v hv x
  rfl

theorem fillingToTautologicalBiholomorph_base_coe (v : Lattice) (hv : AdmissibleTwist j v)
    (x : FillingStar D v hv) :
    (starProjection D 0 (Matrix.mulVec_zero j.matrix)
      (fillingToTautologicalBiholomorph D v hv x) : Disc) =
      D.projection v hv x := by
  rw [fillingToTautologicalBiholomorph_base]
  rfl

end Wikipedia.HopfProblem.Elliptic.LogGauge
