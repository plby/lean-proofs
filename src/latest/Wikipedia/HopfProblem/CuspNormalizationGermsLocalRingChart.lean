import Wikipedia.HopfProblem.CuspNormalizationGermsLocalRingRestriction
import Wikipedia.HopfProblem.CuspNormalizationGermsChart
import Wikipedia.HopfProblem.CuspNormalizationGermsIntegral

/-!
# Local rings on the actual charted central fibre

The actual central-set germ in a quotient chart has the already proved
ring identification with the active plane-union germ. At a central point
the active set is nonempty, so this is a local ring. Evaluation and the
individual normalization pullbacks preserve the literal representatives.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open CuspQuotient ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : E₃)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s
local notation "R" => ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b

/-- The proved actual chart comparison, now with the literal restricted
plane-union germ ring rather than its branch-image presentation. -/
def chartRestrictedEquivRestricted (hb : b ∈ (e).target) :
    R ≃+* RestrictedAnalyticGerm (activeBranches b) :=
  (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb).trans
    (restrictedEquivBranchImage (activeBranches b)).symm

@[simp] theorem chartRestrictedEquivRestricted_rangeRestrict
    (hb : b ∈ (e).target) (φ : AmbientGerm) :
    chartRestrictedEquivRestricted C ε hε hε1 hC hR a s b hb
      ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ) =
        (toPlaneUnion (activeBranches b)).rangeRestrict φ := by
  apply (restrictedEquivBranchImage (activeBranches b)).injective
  change restrictedEquivBranchImage (activeBranches b)
    ((restrictedEquivBranchImage (activeBranches b)).symm
      (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb
        ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ))) = _
  rw [RingEquiv.apply_symm_apply, chartRestrictedEquivBranchImage_rangeRestrict,
    restrictedEquivBranchImage_rangeRestrict]

/-- The actual central-point chart germ is a local ring. -/
theorem chartRestrictedAnalyticGerm_isLocalRing (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) : IsLocalRing R := by
  let := restrictedAnalyticGerm_isLocalRing (activeBranches b)
    ((activeBranches_nonempty_iff b).mpr hcentral)
  exact (chartRestrictedEquivRestricted C ε hε hε1 hC hR a s b hb).symm.isLocalRing

/-- Evaluation on the actual central chart germ, computed through the
proved equality of the actual central-set and active-plane set germs. -/
def chartRestrictedEval (hb : b ∈ (e).target) (hcentral : Triangle.time b = 0) :
    R →+* ℂ :=
  (restrictedEval (activeBranches b) ((activeBranches_nonempty_iff b).mpr hcentral)).comp
    (chartRestrictedEquivRestricted C ε hε hε1 hC hR a s b hb).toRingHom

@[simp] theorem chartRestrictedEval_rangeRestrict (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) (φ : AmbientGerm) :
    chartRestrictedEval C ε hε hε1 hC hR a s b hb hcentral
      ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ) = eval (0 : E₃) φ := by
  change restrictedEval (activeBranches b) ((activeBranches_nonempty_iff b).mpr hcentral)
    (chartRestrictedEquivRestricted C ε hε hε1 hC hR a s b hb
      ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ)) = _
  rw [chartRestrictedEquivRestricted_rangeRestrict, restrictedEval_rangeRestrict]

/-- In centered coordinates the evaluation is exactly the value at zero. -/
@[simp] theorem chartRestrictedEval_ofAnalytic (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) (f : E₃ → ℂ) (hf : AnalyticAt ℂ f 0) :
    chartRestrictedEval C ε hε hε1 hC hR a s b hb hcentral
      ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict (ofAnalytic f hf)) = f 0 :=
  chartRestrictedEval_rangeRestrict C ε hε hε1 hC hR a s b hb hcentral _

theorem chartRestrictedEval_surjective (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) :
    Function.Surjective (chartRestrictedEval C ε hε hε1 hC hR a s b hb hcentral) :=
  (restrictedEval_surjective (activeBranches b)
    ((activeBranches_nonempty_iff b).mpr hcentral)).comp
      (chartRestrictedEquivRestricted C ε hε hε1 hC hR a s b hb).surjective

@[simp] theorem chartRestricted_isUnit_iff_eval_ne_zero (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) (φ : R) :
    IsUnit φ ↔ chartRestrictedEval C ε hε hε1 hC hR a s b hb hcentral φ ≠ 0 := by
  exact (MulEquiv.isUnit_map
    (chartRestrictedEquivRestricted C ε hε hε1 hC hR a s b hb)).symm.trans
      (restricted_isUnit_iff_eval_ne_zero (activeBranches b)
        ((activeBranches_nonempty_iff b).mpr hcentral) _)

/-- The unique maximal ideal in the actual chart germ is the evaluation kernel. -/
theorem chartRestricted_maximalIdeal_eq_ker_eval (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) :
    letI := chartRestrictedAnalyticGerm_isLocalRing C ε hε hε1 hC hR a s b hb hcentral
    IsLocalRing.maximalIdeal R =
      RingHom.ker (chartRestrictedEval C ε hε hε1 hC hR a s b hb hcentral) := by
  let := chartRestrictedAnalyticGerm_isLocalRing C ε hε hε1 hC hR a s b hb hcentral
  exact (IsLocalRing.ker_eq_maximalIdeal
    (chartRestrictedEval C ε hε hε1 hC hR a s b hb hcentral)
    (chartRestrictedEval_surjective C ε hε hε1 hC hR a s b hb hcentral)).symm

/-- Every actual normalization branch pullback has the same value at the
point as the original singular function germ. -/
@[simp] theorem eval_chartRestrictionToBranches (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) (φ : R) (j : activeBranches b) :
    eval (0 : E₂) (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb φ j) =
      chartRestrictedEval C ε hε hε1 hC hR a s b hb hcentral φ := by
  obtain ⟨ψ, rfl⟩ := (toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict_surjective φ
  rw [chartRestrictedEval_rangeRestrict, chartRestrictionToBranches_rangeRestrict]
  change eval (0 : E₂)
    (normalizationBranchPullback C ε hε hε1 hC hR a s b hb j j.property ψ) = _
  unfold normalizationBranchPullback
  exact eval_pullbackAt _ _ _ ψ

/-- Actual pullback to each point above the singular point is a local
ring homomorphism. -/
theorem chartRestrictionToBranch_isLocalHom (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) (j : activeBranches b) :
    IsLocalHom (GermsFinite.coordinateMap
      (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb) j) where
  map_nonunit φ hφ := by
    apply (chartRestricted_isUnit_iff_eval_ne_zero C ε hε hε1 hC hR a s b hb hcentral φ).mpr
    rw [← eval_chartRestrictionToBranches C ε hε hε1 hC hR a s b hb hcentral φ j]
    exact (isUnit_iff_eval_ne_zero _).mp hφ

/-- Simultaneous actual pullback reflects units as well. This does not
assert that the product of all branch rings is local. -/
theorem chartRestrictionToBranches_isLocalHom (hb : b ∈ (e).target)
    (hcentral : Triangle.time b = 0) :
    IsLocalHom (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb) := by
  obtain ⟨j, hj⟩ := (activeBranches_nonempty_iff b).mpr hcentral
  let j₀ : activeBranches b := ⟨j, hj⟩
  let : IsLocalHom ((Pi.evalRingHom (fun _ : activeBranches b => BranchGerm) j₀).comp
      (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb)) :=
    chartRestrictionToBranch_isLocalHom C ε hε hε1 hC hR a s b hb hcentral j₀
  exact isLocalHom_of_comp (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb)
    (Pi.evalRingHom (fun _ : activeBranches b => BranchGerm) j₀)

end Wikipedia.HopfProblem.CuspNormalization.Germs
