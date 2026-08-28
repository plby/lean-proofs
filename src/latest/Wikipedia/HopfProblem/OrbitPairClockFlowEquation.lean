import Wikipedia.HopfProblem.OrbitPairCompactClockVelocity
import Wikipedia.HopfProblem.OrbitPairSupportedFlowDerivative

/-!
# Exact original-clock motion of the supported ambient flow

The clock projection of every ambient trajectory solves the same scalar
ODE. Uniqueness compares it with the affine clock curve as long as that
curve lies in the cutoff plateau. This controls all ambient points, not
only points on the sphere track.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

def scalarClockField (t : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t := clockCutoff t

theorem scalarClockField_smooth_one :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) 1
      (fun t => (⟨t, scalarClockField t⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
  contMDiff_vectorSpace_iff_contDiff.mpr clockCutoff.contDiff

theorem scalar_integralCurve_of_hasDerivAt {γ : ℝ → ℝ}
    (hγ : ∀ t, HasDerivAt γ (clockCutoff (γ t)) t) :
    IsMIntegralCurve γ scalarClockField := by
  intro t
  have hd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ t
      (ContinuousLinearMap.toSpanSingleton ℝ (clockCutoff (γ t))) :=
    (hγ t).hasFDerivAt.hasMFDerivAt
  exact hd.congr_mfderiv
    (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ (clockCutoff (γ t))).symm

theorem scalarClockField_affine_curve (a : ℝ) :
    IsMIntegralCurveOn (fun s : ℝ => a + s) scalarClockField (Ioo (-2 - a) (2 - a)) := by
  intro s hs
  have hcut : clockCutoff (a + s) = 1 := clockCutoff_one ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hd : HasDerivAt (fun u : ℝ => a + u) (clockCutoff (a + s)) s := by
    rw [hcut]
    exact (hasDerivAt_id s).const_add a
  have hm : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u : ℝ => a + u) s
      (ContinuousLinearMap.toSpanSingleton ℝ (clockCutoff (a + s))) := hd.hasFDerivAt.hasMFDerivAt
  exact (hm.congr_mfderiv
    (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ (clockCutoff (a + s))).symm).hasMFDerivWithinAt

theorem scalar_mfderiv_congr_source_model {E H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I J : ModelWithCorners ℝ E H}
    (h : I = J) (f : X → ℝ) (x : X) :
    (mfderiv I 𝓘(ℝ, ℝ) f x : E →L[ℝ] ℝ) = mfderiv J 𝓘(ℝ, ℝ) f x := by
  subst J
  rfl

variable {G N : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  [T2Space N] [CompactSpace N]

attribute [local instance] cylinderChartedSpace cylinder_isManifold

variable (v : SupportedFlow.Field (E := ℝ × G) (M := ℝ × N))
  (hclock : ∀ p : ℝ × N, (v.vector p).1 = clockCutoff p.1)

include hclock

theorem hasDerivAt_flow_clock (p : ℝ × N) (s : ℝ) :
    HasDerivAt (fun t => (v.flow t p).1) (clockCutoff (v.flow s p).1) s := by
  have hf : ContMDiff 𝓘(ℝ, ℝ × G) 𝓘(ℝ, ℝ) ∞ (Prod.fst : ℝ × N → ℝ) := by
    simpa +instances only [modelWithCornersSelf_prod, cylinderChartedSpace] using
      (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) 𝓘(ℝ, ℝ) ∞
        (Prod.fst : ℝ × N → ℝ))
  have hd := v.hasDerivAt_comp Prod.fst hf p s
  have hdf : (mfderiv 𝓘(ℝ, ℝ × G) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × N → ℝ) (v.flow s p) :
      (ℝ × G) →L[ℝ] ℝ) = ContinuousLinearMap.fst ℝ ℝ G := by
    have hmodel := scalar_mfderiv_congr_source_model
      (modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := G))
      (Prod.fst : ℝ × N → ℝ) (v.flow s p)
    exact hmodel.trans (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, G)) (x := v.flow s p))
  have hval := congrArg (fun L : (ℝ × G) →L[ℝ] ℝ => L (v.vector (v.flow s p))) hdf
  exact hd.congr_deriv (hval.trans (hclock (v.flow s p)))

theorem flow_clock_integralCurve (p : ℝ × N) :
    IsMIntegralCurve (fun s => (v.flow s p).1) scalarClockField :=
  scalar_integralCurve_of_hasDerivAt (hasDerivAt_flow_clock v hclock p)

theorem flow_clock_eq_add {a s : ℝ} (ha : a ∈ Ioo (-2 : ℝ) 2)
    (hs : a + s ∈ Ioo (-2 : ℝ) 2) (x : N) : (v.flow s (a, x)).1 = a + s := by
  have hzero : (0 : ℝ) ∈ Ioo (-2 - a) (2 - a) := ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have htime : s ∈ Ioo (-2 - a) (2 - a) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hinit : (v.flow 0 (a, x)).1 = a + 0 := by rw [v.flow_zero, add_zero]
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero scalarClockField_smooth_one
    ((flow_clock_integralCurve v hclock (a, x)).isMIntegralCurveOn _)
    (scalarClockField_affine_curve a) hinit htime

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
