import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalFactors

/-!
# Actual triangle-action Jacobians in the period-family charts

For the full three-form `dz ∧ dζ₀ ∧ dζ₁`, the automorphy multiplier is
the derivative of the base action times the determinant of the actual
right block. Base-direction derivatives of the fibre matrix and lattice
translations are included in the differentiated maps and cancel only by
the proved block-triangular determinant identity.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

open SpecialPeriods

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ Model

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold I₁ ω B] [MulAction TriangleGroup B]

local instance automorphyProductChartedSpace : ChartedSpace Model (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

local instance automorphyProductManifold : IsManifold I₃ ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) B ComplexPlane₂

variable (coordinate : B → ℂ) (hcoordinate : ∀ a x : B, chartAt ℂ a x = coordinate x)

omit [MulAction TriangleGroup B] in
include hcoordinate in
theorem coordinate_holomorphic : ContMDiff I₁ I₁ ω coordinate := by
  intro x
  have hc : ContMDiffAt I₁ I₁ ω (chartAt ℂ x) x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source ℂ x)
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => (hcoordinate x y).symm

/-- The actual base action expressed in the source base chart. -/
def baseActionCoordinate (_D : Data ℂ B) (g : TriangleGroup) (a : B) (z : ℂ) : ℂ :=
  coordinate (g • (chartAt ℂ a).symm z)

/-- The actual fibre matrix in that same base coordinate. -/
def rightBlockCoordinate (D : Data ℂ B) (g : TriangleGroup) (a : B) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := D.rightBlock g ((chartAt ℂ a).symm z)

/-- A genuine target lattice translation evaluated after the base action. -/
def transportedDisplacement (D : Data ℂ B) (g : TriangleGroup) (a : B)
    (v : RealPlane₄) (z : ℂ) : ComplexPlane₂ :=
  D.periods.periodEquiv (g • (chartAt ℂ a).symm z) v

include hcoordinate in
theorem baseActionCoordinate_contDiffAt (D : Data ℂ B) (g : TriangleGroup) (a : B)
    {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    ContDiffAt ℂ ω (baseActionCoordinate coordinate D g a) z := by
  have hi : ContMDiffAt I₁ I₁ ω (chartAt ℂ a).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) hz
  have ha : ContMDiff I₁ I₁ ω (fun b : B => coordinate (g • b)) :=
    (coordinate_holomorphic coordinate hcoordinate).comp (D.base_holomorphic g)
  exact (ha.contMDiffAt.comp z hi).contDiffAt

theorem rightBlockCoordinate_contDiffAt (D : Data ℂ B) (g : TriangleGroup) (a : B)
    {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) (i j : Fin 2) :
    ContDiffAt ℂ ω (fun w => rightBlockCoordinate D g a w i j) z := by
  have hi : ContMDiffAt I₁ I₁ ω (chartAt ℂ a).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) hz
  exact ((D.rightBlock_entry_holomorphic g i j).contMDiffAt.comp z hi).contDiffAt

theorem transportedDisplacement_contDiffAt (D : Data ℂ B) (g : TriangleGroup) (a : B)
    (v : RealPlane₄) {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    ContDiffAt ℂ ω (transportedDisplacement D g a v) z := by
  have hi : ContMDiffAt I₁ I₁ ω (chartAt ℂ a).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) hz
  have hp := (D.periods.holomorphic_periodEquiv_const v).comp (D.base_holomorphic g)
  exact (hp.contMDiffAt.comp z hi).contDiffAt

omit [IsManifold I₁ ω B] in
include hcoordinate in
theorem complexLift_chart_expression (D : Data ℂ B) (g : TriangleGroup)
    (a b : B × ComplexPlane₂) :
    chartAt Model b ∘ D.complexLift g ∘ (chartAt Model a).symm =
      skewMap (baseActionCoordinate coordinate D g a.1)
        (rightBlockCoordinate D g a.1) (fun _ => 0) := by
  funext w
  change (chartAt ℂ b.1 (g • (chartAt ℂ a.1).symm w.1),
    D.rightBlock g ((chartAt ℂ a.1).symm w.1) *ᵥ w.2) = _
  rw [hcoordinate]
  simp only [skewMap, baseActionCoordinate, rightBlockCoordinate, add_zero]

include hcoordinate in
/-- The Jacobian of the actual lifted triangle action. -/
theorem complexLift_chart_det_fderiv (D : Data ℂ B) (g : TriangleGroup)
    (a b : B × ComplexPlane₂) {u : Model} (hu : u ∈ (chartAt Model a).target) :
    LinearMap.det (fderiv ℂ
      (chartAt Model b ∘ D.complexLift g ∘ (chartAt Model a).symm) u).toLinearMap =
        deriv (baseActionCoordinate coordinate D g a.1) u.1 *
          (D.rightBlock g ((chartAt ℂ a.1).symm u.1)).det := by
  rw [complexLift_chart_expression coordinate hcoordinate]
  exact det_fderiv_skewMap_of_differentiable u.2
    ((baseActionCoordinate_contDiffAt coordinate hcoordinate D g a.1 hu.1).differentiableAt
      (by simp))
    (fun i j => (rightBlockCoordinate_contDiffAt D g a.1 hu.1 i j).differentiableAt (by simp))
    (differentiableAt_const 0)

include hcoordinate in
/-- Pullback of the genuine top alternating covector through the actual
lifted action, with every base-direction derivative accounted for. -/
theorem complexLift_chart_volume (D : Data ℂ B) (g : TriangleGroup)
    (a b : B × ComplexPlane₂) {u : Model} (hu : u ∈ (chartAt Model a).target) :
    volume.compContinuousLinearMap
      (fderiv ℂ (chartAt Model b ∘ D.complexLift g ∘ (chartAt Model a).symm) u) =
        (deriv (baseActionCoordinate coordinate D g a.1) u.1 *
          (D.rightBlock g ((chartAt ℂ a.1).symm u.1)).det) • volume := by
  rw [volume_pullback, complexLift_chart_det_fderiv coordinate hcoordinate D g a b hu]

/-- The actual triangle map on the lattice-quotient period family. -/
def familyMap (D : Data ℂ B) (g : TriangleGroup) : D.TotalSpace → D.TotalSpace :=
  letI := D.totalAction
  fun x => g • x

omit [IsManifold I₁ ω B] in
theorem familyMap_quotientMap (D : Data ℂ B) (g : TriangleGroup) (x : B × ComplexPlane₂) :
    familyMap D g (D.periods.quotientMap x) = D.periods.quotientMap (D.complexLift g x) := by
  let := D.totalAction
  exact (D.complexLift_quotientMap g x).symm

def familyActionCoordinate (D : Data ℂ B) (g : TriangleGroup) (i j : D.TotalSpace) :
    Model → Model :=
  familyChart D.periods j ∘ familyMap D g ∘ (familyChart D.periods i).symm

omit [IsManifold I₁ ω B] in
include hcoordinate in
/-- In actual family charts the triangle map is locally its true linear
lift followed by one target lattice translation. -/
theorem familyActionCoordinate_eventually_skew (D : Data ℂ B) (g : TriangleGroup)
    (i j : D.TotalSpace) {u : Model} (hu : u ∈ (familyChart D.periods i).target)
    (hj : familyMap D g ((familyChart D.periods i).symm u) ∈ (familyChart D.periods j).source) :
    ∃ v : Multiplicative standardLattice,
      familyActionCoordinate D g i j =ᶠ[𝓝 u]
        skewMap (baseActionCoordinate coordinate D g (familyRepresentative D.periods i).1)
          (rightBlockCoordinate D g (familyRepresentative D.periods i).1)
          (transportedDisplacement D g (familyRepresentative D.periods i).1 v.toAdd) := by
  let := D.periods.coveringAction
  let a := familyRepresentative D.periods i
  let b := familyRepresentative D.periods j
  let x := (chartAt Model a).symm u
  let y := D.complexLift g x
  have hy : D.periods.quotientMap y ∈ (familyChart D.periods j).source := by
    rw [familyChart_symm_apply, familyMap_quotientMap] at hj
    exact hj
  obtain ⟨v, _, hv⟩ := CoveringQuotient.localInverse_eventually_deck D.periods.quotientCoveringMap
    (fun v => (D.periods.coveringAction_holomorphic v).continuous) b y hy.1
  have ht : Tendsto (D.complexLift g ∘ (chartAt Model a).symm) (𝓝 u) (𝓝 y) :=
    (D.complexLift_holomorphic g).continuous.continuousAt.comp
      ((chartAt Model a).symm.continuousAt (familyChart_target_subset D.periods i hu))
  refine ⟨v, ?_⟩
  filter_upwards [hv.comp_tendsto ht] with w hw
  change familyChart D.periods j (familyMap D g ((familyChart D.periods i).symm w)) = _
  rw [familyChart_symm_apply, familyMap_quotientMap]
  change (chartAt Model b)
    ((CoveringQuotient.localInverse D.periods.quotientCoveringMap b)
      (D.periods.quotientMap (D.complexLift g ((chartAt Model a).symm w)))) = _
  rw [show (CoveringQuotient.localInverse D.periods.quotientCoveringMap b)
      (D.periods.quotientMap (D.complexLift g ((chartAt Model a).symm w))) =
        v • D.complexLift g ((chartAt Model a).symm w) from hw]
  change (chartAt ℂ b.1 (g • (chartAt ℂ a.1).symm w.1),
    D.rightBlock g ((chartAt ℂ a.1).symm w.1) *ᵥ w.2 +
      D.periods.periodEquiv (g • (chartAt ℂ a.1).symm w.1) v.toAdd) = _
  rw [hcoordinate]
  rfl

include hcoordinate in
/-- The same automorphy factor holds for the actual triangle action on
the varying lattice quotient, not only for a formal vector-space lift. -/
theorem familyActionCoordinate_det_fderiv (D : Data ℂ B) (g : TriangleGroup)
    (i j : D.TotalSpace) {u : Model} (hu : u ∈ (familyChart D.periods i).target)
    (hj : familyMap D g ((familyChart D.periods i).symm u) ∈ (familyChart D.periods j).source) :
    LinearMap.det (fderiv ℂ (familyActionCoordinate D g i j) u).toLinearMap =
      deriv (baseActionCoordinate coordinate D g (familyRepresentative D.periods i).1) u.1 *
        (D.rightBlock g ((chartAt ℂ (familyRepresentative D.periods i).1).symm u.1)).det := by
  obtain ⟨v, hv⟩ := familyActionCoordinate_eventually_skew coordinate hcoordinate D g i j hu hj
  rw [hv.fderiv_eq]
  have hz : u.1 ∈ (chartAt ℂ (familyRepresentative D.periods i).1).target :=
    (familyChart_target_subset D.periods i hu).1
  exact det_fderiv_skewMap_of_differentiable u.2
    ((baseActionCoordinate_contDiffAt coordinate hcoordinate D g _ hz).differentiableAt (by simp))
    (fun k l => (rightBlockCoordinate_contDiffAt D g _ hz k l).differentiableAt (by simp))
    ((transportedDisplacement_contDiffAt D g _ v.toAdd hz).differentiableAt (by simp))

include hcoordinate in
theorem familyActionCoordinate_volume (D : Data ℂ B) (g : TriangleGroup)
    (i j : D.TotalSpace) {u : Model} (hu : u ∈ (familyChart D.periods i).target)
    (hj : familyMap D g ((familyChart D.periods i).symm u) ∈ (familyChart D.periods j).source) :
    volume.compContinuousLinearMap (fderiv ℂ (familyActionCoordinate D g i j) u) =
      (deriv (baseActionCoordinate coordinate D g (familyRepresentative D.periods i).1) u.1 *
        (D.rightBlock g ((chartAt ℂ (familyRepresentative D.periods i).1).symm u.1)).det) •
          volume := by
  rw [volume_pullback, familyActionCoordinate_det_fderiv coordinate hcoordinate D g i j hu hj]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
