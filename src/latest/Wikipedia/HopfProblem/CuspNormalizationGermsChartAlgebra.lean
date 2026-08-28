import Wikipedia.HopfProblem.CuspNormalizationGermsChart
import Wikipedia.HopfProblem.CuspNormalizationGermsBirational

/-!
# Finite integral and total-fraction comparison for the actual cusp chart

The singular ring here is the ring of actual ambient-analytic function
germs on the actual central set in an adapted quotient chart. Its map to
the analytic branch germs is the proved pullback along the actual
normalization map. This map is injective, finite and integral; its actual
total fraction ring is the product of the branch fraction fields.

These results use the proved analytic coordinate cofactors and actual
branch-germ domains. No separator or birationality assumption remains.
Integral closedness of the branch rings is a separate analytic assertion.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open CuspQuotient ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : E₃)

local notation "R" => ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b

variable (hb : b ∈ (normalizationChart C ε hε hε1 hC hR a s).target)

include hb

/-- Actual normalization pullback on the chart-restricted analytic germ
ring is a finite ring homomorphism. -/
theorem chartRestrictionToBranches_finite :
    (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb).Finite :=
  (GermsFinite.range_inclusion_finite (toBranches (activeBranches b))
    (toBranches_coordinate_surjective (activeBranches b))).comp
      (RingHom.Finite.of_surjective
        (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb).toRingHom
        (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb).surjective)

theorem chartRestrictionToBranches_isIntegral :
    (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb).IsIntegral :=
  (chartRestrictionToBranches_finite C ε hε hε1 hC hR a s b hb).to_isIntegral

/-- The scalar action is induced by the actual normalization pullback. -/
theorem chartRestrictionToBranches_moduleFinite :
    letI := (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb).toAlgebra
    Module.Finite R (activeBranches b → BranchGerm) :=
  chartRestrictionToBranches_finite C ε hε hε1 hC hR a s b hb

omit hb in
private theorem chart_mem_nonZeroDivisors_equiv_iff {S T : Type*}
    [CommRing S] [CommRing T] (f : S ≃+* T) (x : S) :
    x ∈ nonZeroDivisors S ↔ f x ∈ nonZeroDivisors T := by
  constructor
  · intro hx
    rw [← MulEquivClass.map_nonZeroDivisors f]
    exact Submonoid.mem_map.mpr ⟨x, hx, rfl⟩
  · exact mem_nonZeroDivisors_of_injective f.injective

/-- A genuine central-set germ is a non-zero-divisor exactly when its
actual normalization pullback is nonzero on every branch. -/
theorem chartRestricted_mem_nonZeroDivisors_iff (φ : R) :
    φ ∈ nonZeroDivisors R ↔
      ∀ j : activeBranches b, chartRestrictionToBranches C ε hε hε1 hC hR a s b hb φ j ≠ 0 := by
  rw [chart_mem_nonZeroDivisors_equiv_iff
    (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb) φ]
  exact (separatingFamily (activeBranches b)).mem_nonZeroDivisors_iff _

/-- The actual chart-restricted central function-germ ring is reduced. -/
theorem chartRestrictedAnalyticGerm_isReduced : IsReduced R :=
  isReduced_of_injective (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb)
    (chartRestrictionToBranches_injective C ε hε hε1 hC hR a s b hb)

/-- The genuine total fraction ring of the chart-restricted central
function-germ ring is the product of the actual branch fraction fields. -/
def chartRestrictedTotalFractionEquiv :
    FractionRing R ≃+* (activeBranches b → FractionRing BranchGerm) :=
  (IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing R) (L := FractionRing (BranchImage (activeBranches b)))
    (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb)).trans
      (branchImageTotalFractionEquiv (activeBranches b))

/-- The total-fraction comparison commutes with the actual germ pullback. -/
@[simp] theorem chartRestrictedTotalFractionEquiv_algebraMap_apply
    (φ : R) (j : activeBranches b) :
    chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb
      (algebraMap R (FractionRing R) φ) j =
        algebraMap BranchGerm (FractionRing BranchGerm)
          (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb φ j) := by
  change branchImageTotalFractionEquiv (activeBranches b)
    (IsFractionRing.ringEquivOfRingEquiv
      (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb)
      (algebraMap R (FractionRing R) φ)) j = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    branchImageTotalFractionEquiv_algebraMap_apply]
  rfl

/-- On each ambient analytic representative, the fraction comparison is
the actual pullback by `ν` in the centered affine branch chart. -/
@[simp] theorem chartRestrictedTotalFractionEquiv_ambient_apply
    (φ : AmbientGerm) (j : activeBranches b) :
    chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb
      (algebraMap R (FractionRing R)
        ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ)) j =
      algebraMap BranchGerm (FractionRing BranchGerm)
        (normalizationBranchPullback C ε hε hε1 hC hR a s b hb j j.property φ) := by
  rw [chartRestrictedTotalFractionEquiv_algebraMap_apply, chartRestrictionToBranches_rangeRestrict]
  rfl

/-- The same formula in the proved coordinate-plane description. -/
theorem chartRestrictedTotalFractionEquiv_ambient_coordinate_apply
    (φ : AmbientGerm) (j : activeBranches b) :
    chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb
      (algebraMap R (FractionRing R)
        ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ)) j =
      algebraMap BranchGerm (FractionRing BranchGerm) (toBranch j φ) := by
  rw [chartRestrictedTotalFractionEquiv_ambient_apply, normalizationBranchPullback_eq_toBranch]

/-- Actual fractions map to the fractions of the actual branch
restrictions of their numerator and non-zero-divisor denominator. -/
theorem chartRestrictedTotalFractionEquiv_mk'_apply
    (φ : R) (d : nonZeroDivisors R) (j : activeBranches b) :
    chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb
      (IsLocalization.mk' (FractionRing R) φ d) j =
        algebraMap BranchGerm (FractionRing BranchGerm)
          (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb φ j) /
        algebraMap BranchGerm (FractionRing BranchGerm)
          (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb d.val j) := by
  have hd : algebraMap BranchGerm (FractionRing BranchGerm)
      (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb d.val j) ≠ 0 :=
    (map_ne_zero_iff (algebraMap BranchGerm (FractionRing BranchGerm))
      (IsFractionRing.injective BranchGerm (FractionRing BranchGerm))).mpr
        ((chartRestricted_mem_nonZeroDivisors_iff C ε hε hε1 hC hR a s b hb d.val).mp d.prop j)
  apply (eq_div_iff hd).mpr
  have h := congrArg (fun x : FractionRing R =>
    chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb x j)
      (IsLocalization.mk'_spec (FractionRing R) φ d)
  simpa only [map_mul, Pi.mul_apply, chartRestrictedTotalFractionEquiv_algebraMap_apply] using h

end Wikipedia.HopfProblem.CuspNormalization.Germs
