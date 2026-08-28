import Wikipedia.HopfProblem.OrbitPairCoherentBundleOrientation
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Orientation signs in arbitrary native parametrizations

An orientation section is expressed in the preferred tangent chart at each
point. Its raw bit need not vary continuously. Multiplying by the sign of
the native derivative of a partial diffeomorphism cancels precisely those
chart changes. The resulting orientation of the parametrization is
continuous, hence constant on every connected part of its source.
-/

noncomputable section

open Set Function Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeChartOrientation

open DeterminantSignCover Wikipedia.SmoothSixDPoincare

variable {D E H M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (o : Orientation (tangentBundleCore I M))
  (c : PartialDiffeomorph 𝓘(ℝ, D) I D M ∞) (J : E ≃L[ℝ] D)

def derivative (z : D) : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) I c z

def nativeFrame (z : D) : E →L[ℝ] E :=
  (derivative c z).comp J.toContinuousLinearMap

theorem nativeFrame_det_ne_zero {z : D} (hz : z ∈ c.source) :
    (nativeFrame c J z).det ≠ 0 := by
  intro hzero
  have hker := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero
  exact hker (LinearMap.ker_eq_bot.mpr
    ((PartialChart.bijective_mfderiv c hz).1.comp J.injective))

/-- Derivative coordinates with the target chart fixed at `c z₀`. -/
def fixedFrame (z₀ z : D) : E →L[ℝ] E :=
  (inTangentCoordinates 𝓘(ℝ, D) I id c (derivative c) z₀ z).comp
    J.toContinuousLinearMap

theorem fixedFrame_eq {z₀ z : D} (hz : c z ∈ (chartAt H (c z₀)).source) :
    fixedFrame c J z₀ z =
      ((tangentBundleCore I M).coordChange (achart H (c z)) (achart H (c z₀)) (c z)).comp
        (nativeFrame c J z) := by
  unfold fixedFrame
  rw [inTangentCoordinates_eq (I := 𝓘(ℝ, D)) (I' := I) id c (derivative c)
    (show z ∈ (chartAt D z₀).source from mem_univ z) hz]
  simp only [tangentBundleCore_coordChange_model_space, ContinuousLinearMap.comp_id]
  rfl

theorem continuousAt_fixedFrame {z₀ : D} (hz₀ : z₀ ∈ c.source) :
    ContinuousAt (fixedFrame c J z₀) z₀ := by
  have hc : ContMDiffAt 𝓘(ℝ, D) I ∞ c z₀ :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hz₀)
  have hd := hc.mfderiv_const (m := 0) (by simp)
  exact hd.continuousAt.clm_comp continuousAt_const

/-- The orientation of the actual parametrization, measured against a
fixed linear identification of its domain model. -/
def sign (z : D) : Bool := action (nativeFrame c J z).det (o.rawSign (c z))

theorem sign_eq_fixedFrame {z₀ z : D} (hz : z ∈ c.source)
    (hchart : c z ∈ (chartAt H (c z₀)).source) :
    sign o c J z = action (fixedFrame c J z₀ z).det
      (o.localSign (achart H (c z₀)) (c z)) := by
  rw [fixedFrame_eq c J hchart, o.localSign_eq_action_rawSign]
  let T : E →L[ℝ] E := (tangentBundleCore I M).coordChange
    (achart H (c z)) (achart H (c z₀)) (c z)
  change action (nativeFrame c J z).det (o.rawSign (c z)) =
    action (T.comp (nativeFrame c J z)).det (action T.det (o.rawSign (c z)))
  have hdet : (T.comp (nativeFrame c J z)).det = T.det * (nativeFrame c J z).det :=
    LinearMap.det_comp _ _
  rw [hdet]
  exact (action_mul_cancel _ _
    (coordChange_det_ne_zero (tangentBundleCore I M) _ _
      ⟨mem_chart_source H (c z), hchart⟩)
    (nativeFrame_det_ne_zero c J hz) _).symm

theorem continuousAt_sign {z₀ : D} (hz₀ : z₀ ∈ c.source) :
    ContinuousAt (sign o c J) z₀ := by
  have hc := c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hz₀)
  have hchart₀ : c z₀ ∈ (chartAt H (c z₀)).source := mem_chart_source H (c z₀)
  have hlocal : ContinuousAt (fun z => o.localSign (achart H (c z₀)) (c z)) z₀ :=
    ((o.continuousOn_localSign (achart H (c z₀))).continuousAt
      ((chartAt H (c z₀)).open_source.mem_nhds hchart₀)).comp hc
  have hdet : (fixedFrame c J z₀ z₀).det ≠ 0 := by
    rw [fixedFrame_eq c J hchart₀,
      coordChange_self_eq (tangentBundleCore I M) (achart H (c z₀)) hchart₀,
      ContinuousLinearMap.id_comp]
    exact nativeFrame_det_ne_zero c J hz₀
  have hsign : ContinuousAt (fun z => action (fixedFrame c J z₀ z).det
      (o.localSign (achart H (c z₀)) (c z))) z₀ := by
    have hpair : ContinuousAt (fun z : D => ((fixedFrame c J z₀ z).det,
        o.localSign (achart H (c z₀)) (c z))) z₀ :=
      (ContinuousLinearMap.continuous_det.continuousAt.comp
        (continuousAt_fixedFrame c J hz₀)).prodMk hlocal
    exact (continuousAt_action hdet (o.localSign (achart H (c z₀)) (c z₀))).comp_of_eq
      hpair rfl
  apply hsign.congr_of_eventuallyEq
  have hchart : ∀ᶠ z in 𝓝 z₀, c z ∈ (chartAt H (c z₀)).source :=
    hc.eventually ((chartAt H (c z₀)).open_source.mem_nhds hchart₀)
  filter_upwards [c.open_source.mem_nhds hz₀, hchart] with z hz hcz
  exact sign_eq_fixedFrame o c J hz hcz

theorem continuousOn_sign : ContinuousOn (sign o c J) c.source :=
  fun _ hz => (continuousAt_sign o c J hz).continuousWithinAt

theorem sign_eq_on_preconnected {A : Type*} [TopologicalSpace A]
    {a : A → D} {s : Set A} (hs : IsPreconnected s) (ha : ContinuousOn a s)
    (himage : MapsTo a s c.source) {x y : A} (hx : x ∈ s) (hy : y ∈ s) :
    sign o c J (a x) = sign o c J (a y) :=
  hs.constant ((continuousOn_sign o c J).comp ha himage) hx hy

end Wikipedia.HopfProblem.OrbitPair.NativeChartOrientation
