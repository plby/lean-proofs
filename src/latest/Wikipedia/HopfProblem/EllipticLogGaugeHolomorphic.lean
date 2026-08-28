import Wikipedia.HopfProblem.EllipticLogGaugeBasic
import Wikipedia.HopfProblem.CuspPuncturedManifold
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# The logarithmic period gauge is biholomorphic

Local normalized logarithms give holomorphic lifts of the global quotient
translation. Holomorphicity descends through the actual period-family
covering, so no complex atlas is transported along the gauge map.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

local notation "IF" => modelWithCornersSelf ℂ FamilyModel
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

local instance gaugeCoveringChartedSpace : ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

local instance gaugeCoveringManifold : IsManifold IF ω (Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) Disc ComplexPlane₂

variable (P : HolomorphicPeriodMap ℂ Disc)

theorem project_isLocalDiffeomorph :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph IF IF ω (project P) := by
  let := P.totalChartedSpace
  let := P.coveringAction
  have hq : IsLocalDiffeomorph IF IF ω P.quotientMap :=
    CoveringQuotient.project_isLocalDiffeomorph
      P.quotientCoveringMap P.coveringAction_holomorphic
  exact isLocalDiffeomorph_restrictOpens IF IF hq coverOpen familyOpen (fun _ hx => hx)

theorem project_holomorphic :
    letI := P.totalChartedSpace
    ContMDiff IF IF ω (project P) := by
  let := P.totalChartedSpace
  exact (project_isLocalDiffeomorph P).contMDiff

theorem gaugeLift_holomorphicAt (v : Lattice) {a : ℂ → ℂ} {x : CoverStar}
    (ha : ContDiffAt ℂ ω a (x.1.1 : ℂ)) :
    ContMDiffAt IF IF ω (gaugeLift P v a) x := by
  have hb : ContMDiff IF I₁ ω (fun y : CoverStar => y.1.1) := by
    have hfst : ContMDiff IF I₁ ω (Prod.fst : Disc × ComplexPlane₂ → Disc) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    exact hfst.comp contMDiff_subtype_val
  have hw : ContMDiff IF I₂ ω (fun y : CoverStar => y.1.2) := by
    have hsnd : ContMDiff IF I₂ ω
        (Prod.snd : Disc × ComplexPlane₂ → ComplexPlane₂) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_snd
    exact hsnd.comp contMDiff_subtype_val
  have hbc : ContMDiff IF I₁ ω (fun y : CoverStar => (y.1.1 : ℂ)) :=
    contMDiff_subtype_val.comp hb
  have hscalar : ContMDiffAt IF I₁ ω (fun y : CoverStar => a y.1.1) x :=
    ha.contMDiffAt.comp x hbc.contMDiffAt
  have hp : ContMDiff IF I₂ ω (fun y : CoverStar => periodVector P v y.1.1) :=
    (periodVector_holomorphic P v).comp hb
  have hsum : ContMDiffAt IF I₂ ω
      (fun y : CoverStar => y.1.2 + a y.1.1 • periodVector P v y.1.1) x :=
    hw.contMDiffAt.add (hscalar.smul hp.contMDiffAt)
  have hpair : ContMDiffAt IF IF ω
      (fun y : CoverStar => (y.1.1, y.1.2 + a y.1.1 • periodVector P v y.1.1)) x := by
    simpa only [← modelWithCornersSelf_prod] using hb.contMDiffAt.prodMk hsum
  have he : ContMDiffAt IF IF ω (Subtype.val ∘ gaugeLift P v a) x ↔
      ContMDiffAt IF IF ω (gaugeLift P v a) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp hpair

theorem gaugeMap_comp_project_holomorphic (v : Lattice) :
    letI := P.totalChartedSpace
    ContMDiff IF IF ω (gaugeMap P v ∘ project P) := by
  let := P.totalChartedSpace
  intro x
  have hl := gaugeLift_holomorphicAt P v (x := x) (localLog_contDiffAt x.2)
  have h := (project_holomorphic P).contMDiffAt.comp x hl
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (gaugeMap_project_localLog P v x.2)

theorem gaugeMap_holomorphic (v : Lattice) :
    letI := P.totalChartedSpace
    ContMDiff IF IF ω (gaugeMap P v) := by
  let := P.totalChartedSpace
  exact contMDiff_of_comp_localDiffeomorph IF IF IF
    (project_isLocalDiffeomorph P) (project_surjective P)
    (gaugeMap_comp_project_holomorphic P v)

theorem gaugeMap_continuous (v : Lattice) : Continuous (gaugeMap P v) := by
  let := P.totalChartedSpace
  exact (gaugeMap_holomorphic P v).continuous

def gaugeBiholomorph (v : Lattice) :
    letI := P.totalChartedSpace
    Diffeomorph IF IF (FamilyStar P) (FamilyStar P) ω := by
  let := P.totalChartedSpace
  exact {
    toEquiv := gaugeEquiv P v
    contMDiff_toFun := gaugeMap_holomorphic P v
    contMDiff_invFun := gaugeMap_holomorphic P (-v) }

@[simp] theorem gaugeBiholomorph_apply (v : Lattice) (x : FamilyStar P) :
    gaugeBiholomorph P v x = gaugeMap P v x := rfl

@[simp] theorem gaugeBiholomorph_symm_apply (v : Lattice) (x : FamilyStar P) :
    letI := P.totalChartedSpace
    (gaugeBiholomorph P v).symm x = gaugeMap P (-v) x := rfl

theorem zeroSection_holomorphic :
    letI := P.totalChartedSpace
    ContMDiff I₁ IF ω (zeroSection P) := by
  let := P.totalChartedSpace
  have h : ContMDiff I₁ IF ω (fun z : BaseStar => (zeroSection P z : P.TotalSpace)) :=
    (HolomorphicPeriodMap.zeroSection_holomorphic P).comp contMDiff_subtype_val
  intro z
  have he : ContMDiffAt I₁ IF ω (Subtype.val ∘ zeroSection P) z ↔
      ContMDiffAt I₁ IF ω (zeroSection P) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (h z)

theorem sectionMap_holomorphic (v : Lattice) :
    letI := P.totalChartedSpace
    ContMDiff I₁ IF ω (sectionMap P v) := by
  let := P.totalChartedSpace
  exact (gaugeMap_holomorphic P v).comp (zeroSection_holomorphic P)

end Wikipedia.HopfProblem.Elliptic.LogGauge
