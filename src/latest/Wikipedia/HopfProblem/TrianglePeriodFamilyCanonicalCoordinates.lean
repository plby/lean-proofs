import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalDerivatives
import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.CoveringVolumeCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyGeometry

/-!
# Actual period-family coordinate changes are lattice shears

The natural covering charts on a period family have coordinate changes
locally equal to `(z, ζ) ↦ (z, ζ + Π(z)λ)`. This is an equality near every
overlap point, not an assumption about its Jacobian. The upper half-plane
and its actual regular triangle domain both satisfy the common-coordinate
condition used in the proof.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ Model

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold I₁ ω B]

local instance productChartedSpace : ChartedSpace Model (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

local instance productManifold : IsManifold I₃ ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) B ComplexPlane₂

omit [IsManifold I₁ ω B] in
theorem product_chart_apply (a x : B × ComplexPlane₂) :
    chartAt Model a x = (chartAt ℂ a.1 x.1, x.2) := rfl

omit [IsManifold I₁ ω B] in
theorem product_chart_symm_apply (a : B × ComplexPlane₂) (u : Model) :
    (chartAt Model a).symm u = ((chartAt ℂ a.1).symm u.1, u.2) := rfl

/-- The actual varying lattice translation written in one base chart. -/
def periodDisplacement (P : HolomorphicPeriodMap ℂ B) (a : B) (v : RealPlane₄)
    (z : ℂ) : ComplexPlane₂ := P.periodEquiv ((chartAt ℂ a).symm z) v

theorem periodDisplacement_contDiffAt (P : HolomorphicPeriodMap ℂ B)
    (a : B) (v : RealPlane₄) {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    ContDiffAt ℂ ω (periodDisplacement P a v) z := by
  have hi : ContMDiffAt I₁ I₁ ω (chartAt ℂ a).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) hz
  have hp : ContMDiffAt I₁ I₂ ω (fun b : B => P.periodEquiv b v)
      ((chartAt ℂ a).symm z) := (P.holomorphic_periodEquiv_const v).contMDiffAt
  exact (hp.comp z hi).contDiffAt

variable (coordinate : B → ℂ) (hcoordinate : ∀ a x : B, chartAt ℂ a x = coordinate x)

omit [IsManifold I₁ ω B] in
include hcoordinate in
theorem base_chart_inverse_coordinate (a : B) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) : coordinate ((chartAt ℂ a).symm z) = z := by
  rw [← hcoordinate a]
  exact (chartAt ℂ a).right_inv hz

omit [IsManifold I₁ ω B] in
include hcoordinate in
/-- An actual lattice deck map has the triangular shear formula in the
original product charts, locally at every allowed source coordinate. -/
theorem coveringAction_coordinate_eventually (P : HolomorphicPeriodMap ℂ B)
    (a b : B × ComplexPlane₂) (g : Multiplicative standardLattice)
    {u : Model} (hu : u ∈ (chartAt Model a).target) :
    letI := P.coveringAction
    (chartAt Model b ∘ (fun x : B × ComplexPlane₂ => g • x) ∘ (chartAt Model a).symm) =ᶠ[𝓝 u]
      (fun w : Model => (w.1, w.2 + periodDisplacement P a.1 g.toAdd w.1)) := by
  let := P.coveringAction
  filter_upwards [(chartAt Model a).open_target.mem_nhds hu] with w hw
  change (chartAt ℂ b.1 ((chartAt ℂ a.1).symm w.1),
    w.2 + P.periodEquiv ((chartAt ℂ a.1).symm w.1) g.toAdd) = _
  rw [hcoordinate, base_chart_inverse_coordinate coordinate hcoordinate a.1 hw.1]
  rfl

omit [IsManifold I₁ ω B] in
include hcoordinate in
/-- The actual quotient-chart transition is locally one of these lattice
shears. The lattice element is obtained from the covering's exact orbit fibres. -/
theorem family_chart_transition_eventually_shear (P : HolomorphicPeriodMap ℂ B)
    (i j : P.TotalSpace) {u : Model} :
    letI := P.coveringAction
    u ∈ ((CoveringQuotient.chart (E := Model) P.quotientCoveringMap i).symm.trans
      (CoveringQuotient.chart (E := Model) P.quotientCoveringMap j)).source →
    ∃ g : Multiplicative standardLattice,
      (((CoveringQuotient.chart (E := Model) P.quotientCoveringMap i).symm.trans
        (CoveringQuotient.chart (E := Model) P.quotientCoveringMap j)) : Model → Model) =ᶠ[𝓝 u]
          (fun w : Model => (w.1, w.2 + periodDisplacement P
            (CoveringQuotient.representative P.quotientCoveringMap i).1 g.toAdd w.1)) := by
  let := P.coveringAction
  intro hu
  obtain ⟨g, _, hg⟩ := CoveringQuotient.transition_eventually_deck P.quotientCoveringMap
    (fun g => (P.coveringAction_holomorphic g).continuous) i j hu
  refine ⟨g, hg.trans ?_⟩
  exact coveringAction_coordinate_eventually coordinate hcoordinate P
    (CoveringQuotient.representative P.quotientCoveringMap i)
    (CoveringQuotient.representative P.quotientCoveringMap j) g hu.1.1

/-- The genuine preferred family chart, with its covering action made explicit. -/
def familyChart (P : HolomorphicPeriodMap ℂ B) (i : P.TotalSpace) :
    OpenPartialHomeomorph P.TotalSpace Model :=
  letI := P.coveringAction
  CoveringQuotient.chart (E := Model) P.quotientCoveringMap i

omit [IsManifold I₁ ω B] in
theorem familyChart_eq_chartAt (P : HolomorphicPeriodMap ℂ B) (i : P.TotalSpace) :
    letI := P.totalChartedSpace
    familyChart P i = chartAt Model i := rfl

def familyRepresentative (P : HolomorphicPeriodMap ℂ B) (i : P.TotalSpace) :
    B × ComplexPlane₂ :=
  letI := P.coveringAction
  CoveringQuotient.representative P.quotientCoveringMap i

omit [IsManifold I₁ ω B] in
theorem familyChart_symm_apply (P : HolomorphicPeriodMap ℂ B) (i : P.TotalSpace) (u : Model) :
    (familyChart P i).symm u =
      P.quotientMap ((chartAt Model (familyRepresentative P i)).symm u) := by
  let := P.coveringAction
  exact congrFun (CoveringQuotient.chart_symm (E := Model) P.quotientCoveringMap i) u

omit [IsManifold I₁ ω B] in
theorem familyChart_target_subset (P : HolomorphicPeriodMap ℂ B) (i : P.TotalSpace) :
    (familyChart P i).target ⊆ (chartAt Model (familyRepresentative P i)).target :=
  fun _ hu => hu.1

include hcoordinate in
/-- Unit Jacobian on the whole actual family-chart overlap. -/
theorem family_chart_transition_det (P : HolomorphicPeriodMap ℂ B)
    (i j : P.TotalSpace) {u : Model}
    (hu : u ∈ ((familyChart P i).symm.trans (familyChart P j)).source) :
    LinearMap.det
      (fderiv ℂ ((familyChart P i).symm.trans (familyChart P j)) u).toLinearMap = 1 := by
  let := P.coveringAction
  obtain ⟨g, hg⟩ := family_chart_transition_eventually_shear coordinate hcoordinate P i j hu
  have he : fderiv ℂ ((familyChart P i).symm.trans (familyChart P j)) u =
      fderiv ℂ (shearMap (periodDisplacement P
        (CoveringQuotient.representative P.quotientCoveringMap i).1 g.toAdd)) u :=
    hg.fderiv_eq
  rw [he]
  have hz : u.1 ∈ (chartAt ℂ
      (CoveringQuotient.representative P.quotientCoveringMap i).1).target := hu.1.1.1
  have hd := (periodDisplacement_contDiffAt P
    (CoveringQuotient.representative P.quotientCoveringMap i).1 g.toAdd hz).differentiableAt
      (by simp)
  exact det_fderiv_shearMap u.2 hd.hasDerivAt

include hcoordinate in
theorem family_chart_transition_det_at (P : HolomorphicPeriodMap ℂ B)
    (i j x : P.TotalSpace) (hi : x ∈ (familyChart P i).source)
    (hj : x ∈ (familyChart P j).source) :
    LinearMap.det (fderiv ℂ ((familyChart P i).symm.trans (familyChart P j))
      (familyChart P i x)).toLinearMap = 1 := by
  apply family_chart_transition_det coordinate hcoordinate
  refine ⟨(familyChart P i).map_source hi, ?_⟩
  change (familyChart P i).symm (familyChart P i x) ∈ (familyChart P j).source
  rwa [(familyChart P i).left_inv hi]

include hcoordinate in
/-- The standard genuine product-model top covector is unchanged by
every transition in the actual varying-period family atlas. -/
theorem family_chart_transition_volume (P : HolomorphicPeriodMap ℂ B)
    (i j x : P.TotalSpace) (hi : x ∈ (familyChart P i).source)
    (hj : x ∈ (familyChart P j).source) :
    volume.compContinuousLinearMap
      (fderiv ℂ ((familyChart P i).symm.trans (familyChart P j)) (familyChart P i x)) =
        volume := by
  rw [volume_pullback, family_chart_transition_det_at coordinate hcoordinate P i j x hi hj,
    one_smul]

/-- The installed upper-half-plane chart is its actual inclusion into `ℂ`. -/
theorem upperHalfPlane_chart_apply (a z : UpperHalfPlane) :
    chartAt ℂ a z = (z : ℂ) := rfl

/-- The regular domain's inherited chart has the same actual coordinate. -/
theorem regularPoint_chart_apply (a z : SpecialPeriods.TriangleRegularPoint) :
    chartAt ℂ a z = (z.val : ℂ) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
