import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularBase
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalGeneratorBase
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersLocal
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The genuine regular-base differential

The derivative is taken in the native preferred chart of the actual regular
upper-half-plane domain.  All inherited charts have the same complex forward
coordinate; their inverses therefore agree wherever both are defined.  This
proves chart independence, holomorphicity and nonvanishing of the derivative,
and the exact chain rule for every actual triangle-group element.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open TrianglePeriodFamily
open TrianglePeriodFamily.Canonical

/-- The exact source-chart expression of the invariant finite coordinate. -/
def chartCoordinate (a : TriangleRegularPoint) : ℂ → ℂ :=
  upstairsCoordinate ∘ (chartAt ℂ a).symm

theorem regularPoint_chart_self_mem_target (z : TriangleRegularPoint) :
    (z.val : ℂ) ∈ (chartAt ℂ z).target := by
  simpa only [regularPoint_chart_apply] using
    (chartAt ℂ z).map_source (mem_chart_source ℂ z)

theorem regularPoint_chart_symm_eq (a z : TriangleRegularPoint)
    (hz : (z.val : ℂ) ∈ (chartAt ℂ a).target) :
    (chartAt ℂ a).symm (z.val : ℂ) = z := by
  apply Subtype.ext
  apply UpperHalfPlane.ext
  exact base_chart_inverse_coordinate (fun w : TriangleRegularPoint => (w.val : ℂ))
    regularPoint_chart_apply a hz

theorem regularPoint_chart_symm_eventuallyEq (a b : TriangleRegularPoint) {w : ℂ}
    (ha : w ∈ (chartAt ℂ a).target) (hb : w ∈ (chartAt ℂ b).target) :
    (chartAt ℂ a).symm =ᶠ[𝓝 w] (chartAt ℂ b).symm := by
  filter_upwards [(chartAt ℂ a).open_target.mem_nhds ha,
    (chartAt ℂ b).open_target.mem_nhds hb] with u hua hub
  apply Subtype.ext
  apply UpperHalfPlane.ext
  exact (base_chart_inverse_coordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
    regularPoint_chart_apply a hua).trans
      (base_chart_inverse_coordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
        regularPoint_chart_apply b hub).symm

theorem chartCoordinate_contDiffOn (a : TriangleRegularPoint) :
    ContDiffOn ℂ ω (chartCoordinate a) (chartAt ℂ a).target :=
  (upstairsCoordinate_holomorphic.comp_contMDiffOn
    (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω))).contDiffOn

/-- The native chart, with its genuine holomorphic inverse. -/
def regularPointChartPartial (a : TriangleRegularPoint) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularPoint ℂ ω where
  toPartialEquiv := (chartAt ℂ a).toPartialEquiv
  open_source := (chartAt ℂ a).open_source
  open_target := (chartAt ℂ a).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

theorem chartCoordinate_isLocalDiffeomorphAt (a : TriangleRegularPoint) {w : ℂ}
    (hw : w ∈ (chartAt ℂ a).target) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartCoordinate a) w :=
  ((regularPointChartPartial a).symm.isLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω hw).comp
    (K := 𝓘(ℂ)) (P := ℂ)
    (upstairsCoordinate_isLocalDiffeomorph ((chartAt ℂ a).symm w))

/-- The actual scalar differential in the native preferred source chart. -/
def coordinateDerivative (z : TriangleRegularPoint) : ℂ :=
  deriv (chartCoordinate z) (z.val : ℂ)

/-- Every valid inherited source chart computes that same differential. -/
theorem coordinateDerivative_eq_deriv_chart (a z : TriangleRegularPoint)
    (hz : (z.val : ℂ) ∈ (chartAt ℂ a).target) :
    coordinateDerivative z = deriv (chartCoordinate a) (z.val : ℂ) :=
  ((regularPoint_chart_symm_eventuallyEq z a
    (regularPoint_chart_self_mem_target z) hz).fun_comp upstairsCoordinate).deriv_eq

theorem chartCoordinate_hasDerivAt (a z : TriangleRegularPoint)
    (hz : (z.val : ℂ) ∈ (chartAt ℂ a).target) :
    HasDerivAt (chartCoordinate a) (coordinateDerivative z) (z.val : ℂ) := by
  rw [coordinateDerivative_eq_deriv_chart a z hz]
  exact ((chartCoordinate_contDiffOn a).contDiffAt
    ((chartAt ℂ a).open_target.mem_nhds hz)).differentiableAt (by simp) |>.hasDerivAt

theorem coordinateDerivative_ne_zero (z : TriangleRegularPoint) :
    coordinateDerivative z ≠ 0 :=
  MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
    (chartCoordinate_isLocalDiffeomorphAt z (regularPoint_chart_self_mem_target z))

/-- Holomorphicity follows by differentiating a fixed actual chart expression
on its open target, and using the proved chart independence nearby. -/
theorem coordinateDerivative_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω coordinateDerivative := by
  have hcoordinate : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun w : TriangleRegularPoint => (w.val : ℂ)) :=
    coordinate_holomorphic _ regularPoint_chart_apply
  intro z
  have hz := regularPoint_chart_self_mem_target z
  have hd : ContDiffOn ℂ ω (deriv (chartCoordinate z)) (chartAt ℂ z).target :=
    (chartCoordinate_contDiffOn z).deriv_of_isOpen (chartAt ℂ z).open_target (by simp)
  have hh : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun w : TriangleRegularPoint => deriv (chartCoordinate z) (w.val : ℂ)) z :=
    ((hd.contDiffAt ((chartAt ℂ z).open_target.mem_nhds hz)).contMDiffAt).comp z
      (hcoordinate z)
  apply hh.congr_of_eventuallyEq
  filter_upwards [hcoordinate.continuous.continuousAt
    ((chartAt ℂ z).open_target.mem_nhds hz)] with w hw
  exact coordinateDerivative_eq_deriv_chart z w hw

/-- The derivative is the scalar of the actual manifold differential. -/
theorem coordinateDerivative_eq_mfderiv (z : TriangleRegularPoint) :
    coordinateDerivative z =
      (show ℂ →L[ℂ] ℂ from mfderiv 𝓘(ℂ) 𝓘(ℂ) upstairsCoordinate z) 1 := by
  rw [((upstairsCoordinate_holomorphic z).mdifferentiableAt (by simp)).mfderiv]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ, chartAt_self_eq]
  rfl

/-- Differentiating the actual invariant finite coordinate gives its exact
covariance under every triangle element, in any valid source-family chart. -/
theorem coordinateDerivative_action (D : Data ℂ TriangleRegularPoint) (g : TriangleGroup)
    (a z : TriangleRegularPoint) (hz : (z.val : ℂ) ∈ (chartAt ℂ a).target) :
    coordinateDerivative (g • z) *
        deriv (baseActionCoordinate (fun x : TriangleRegularPoint => (x.val : ℂ)) D g a)
          (z.val : ℂ) = coordinateDerivative z := by
  let A := baseActionCoordinate (fun x : TriangleRegularPoint => (x.val : ℂ)) D g a
  have hA : HasDerivAt A (deriv A (z.val : ℂ)) (z.val : ℂ) :=
    (baseActionCoordinate_contDiffAt (fun x : TriangleRegularPoint => (x.val : ℂ))
      regularPoint_chart_apply D g a hz).differentiableAt (by simp) |>.hasDerivAt
  have hAz : A (z.val : ℂ) = ((g • z).val : ℂ) := by
    change ((g • (chartAt ℂ a).symm (z.val : ℂ)).val : ℂ) = _
    rw [regularPoint_chart_symm_eq a z hz]
  have houter := chartCoordinate_hasDerivAt (g • z) (g • z)
    (regularPoint_chart_self_mem_target (g • z))
  have hcomp := houter.comp_of_eq (z.val : ℂ) hA hAz.symm
  have htarget : ∀ᶠ w in 𝓝 (z.val : ℂ), A w ∈ (chartAt ℂ (g • z)).target := by
    apply hA.continuousAt
    rw [hAz]
    exact (chartAt ℂ (g • z)).open_target.mem_nhds
      (regularPoint_chart_self_mem_target (g • z))
  have he : chartCoordinate (g • z) ∘ A =ᶠ[𝓝 (z.val : ℂ)] chartCoordinate a := by
    filter_upwards [htarget] with w hw
    change upstairsCoordinate
      ((chartAt ℂ (g • z)).symm ((g • (chartAt ℂ a).symm w).val : ℂ)) =
        upstairsCoordinate ((chartAt ℂ a).symm w)
    rw [regularPoint_chart_symm_eq (g • z) (g • (chartAt ℂ a).symm w) hw,
      upstairsCoordinate_invariant]
  exact (hcomp.congr_of_eventuallyEq he.symm).unique (chartCoordinate_hasDerivAt a z hz)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
