import Wikipedia.HopfProblem.DegreeCollapseUniquePhaseCorrectedCylinder
import Wikipedia.HopfProblem.DegreeCollapseCubicChartFromCorrectedCylinder
import Wikipedia.HopfProblem.DegreeCollapseCylinderBasinLabels
import Wikipedia.HopfProblem.DegreeCollapseCubicSliceBasins
import Wikipedia.HopfProblem.DegreeCollapseNativeConnectionCancellation
import Wikipedia.HopfProblem.DegreeCollapseScalarHeightChange

/-!
# Native cancellation from original transverse endpoint data

The original endpoint basins and slice formulas determine the cylinder
labels. A unique transverse connection constructs the supported holonomy
correction, the phase correction, and a full cubic field chart. Analytic
cancellation then removes precisely the original two critical points.
Neither a modified field nor a connecting normal-form chart is supplied.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {Z E M : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ}

open Classical in
theorem cancel_unique_native_transverse_connection
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hAsource : A.source = U ×ˢ univ)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ z ∈ A.source, z.2 ∈ Ioo (0 : ℝ) 1 → f (A z) = b - s * z.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield : ∀ y ∈ A.target, V y =
      FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (criticalPoints E f))
    (Q P : PartialDiffeomorph
      𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) 𝓘(ℝ, Z)
      (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) Z ∞)
    (H : PartialDiffeomorph
      𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) ∞)
    (h0 : 0 ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hQsource : Q.source = H.source) (hPsource : P.source = H.target)
    (hQtarget : Q.target = U) (hPtarget : P.target = U)
    (hdiagram : ∀ u ∈ H.source, P (H u) = Q u)
    (htrans : NativeTransversality.At
      𝓘(ℝ, MorseHandle.NegativeSpace σ) 𝓘(ℝ, MorseHandle.PositiveSpace σ)
      𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      (fun x => H (x, 0)) (fun y => (0, y)) 0 0)
    (v₀ v₁ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ)
    (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁)
    (hv₀zero : v₀ 0 = 0) (hv₁zero : v₁ 0 = 0)
    {Rq Rp Tq Tp : ℝ} (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq : ∀ u ∈ Q.source,
      cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq) ∈
        closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep : ∀ u ∈ P.source,
      cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp) ∈
        closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq : ∀ u ∈ Q.source,
      Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)) =
        A (Q u, Tq + v₀ u))
    (hphasep : ∀ u ∈ P.source,
      Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)) =
        A (P u, Tp + v₁ u))
    (hqbasin : ∀ z ∈ Φq.source,
      Tendsto (fun t => F t (Φq z)) atBot (𝓝 (Φq (-a, 0))) ↔
        ∀ i, σ i = 1 → z.2 i = 0)
    (hpbasin : ∀ z ∈ Φp.source,
      Tendsto (fun t => F t (Φp z)) atTop (𝓝 (Φp (a, 0))) ↔
        ∀ i, σ i = -1 → z.2 i = 0)
    (hold : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 (Φq (-a, 0))) →
      Tendsto (fun t => F t x) atTop (𝓝 (Φp (a, 0))) → ∃ t, F t (A (0, 0)) = x)
    (hp : Φp (a, 0) ∈ criticalPoints E f) (hq : Φq (-a, 0) ∈ criticalPoints E f)
    (hpq : f (Φp (a, 0)) < f (Φq (-a, 0)))
    {c d : ℝ} (hc : c < f (Φp (a, 0))) (hd : f (Φq (-a, 0)) < d)
    (hpair : ∀ x ∈ criticalPoints E f,
      f x ∈ Icc c d → x = Φp (a, 0) ∨ x = Φq (-a, 0)) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ x, x ∈ criticalPoints E g ↔
        x ∈ criticalPoints E f ∧ x ≠ Φp (a, 0) ∧ x ≠ Φq (-a, 0)) ∧
      ∀ x, f x ∉ Ioo c d → g =ᶠ[𝓝 x] f := by
  have hV1 := hV.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hQU : Q.target ⊆ U := fun _ hz => hQtarget ▸ hz
  have hPU : P.target ⊆ U := fun _ hz => hPtarget ▸ hz
  have hflow (z : Z) (hz : z ∈ U) (t : ℝ) : A (z, t) = F t (A (z, 0)) := by
    simpa only [zero_add] using
      (FlowSuspension.native_vertical_cylinder_flow A hAsource hV1 hAfield F hF z hz 0 t).symm
  have hleft := FlowSuspension.cylinder_outgoing_basin_labels F A Q
    (fun z hz => hflow z (hQU hz))
    (fun u => Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)))
    (fun u => Tq + v₀ u) hphaseq
    (fun u hu => outgoing_cubic_slice_basin σ hσ a Tq Φq F hqbasin u (hboxq (hsliceq u hu)))
  have hright := FlowSuspension.cylinder_incoming_basin_labels F A P
    (fun z hz => hflow z (hPU hz))
    (fun u => Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)))
    (fun u => Tp + v₁ u) hphasep
    (fun u hu => incoming_cubic_slice_basin σ a Tp Φp F hpbasin u (hboxp (hslicep u hu)))
  rw [hQtarget, hQsource] at hleft
  rw [hPtarget, hPsource] at hright
  have hheightAux : ∀ z ∈ A.source, z.2 ∈ Ioo (0 : ℝ) 1 →
      f (A z) / s = b / s - z.2 := by
    intro z hz ht
    rw [hheight z hz ht]
    field_simp
  obtain ⟨L₁, L₂, N, W, G, Ξ, _, hNsub, hW, hG, hzeroW, hdescW, hgerm,
      hΞsource, hΞtarget, hΞfield, hΞaxis, hunique, hmatch⟩ :=
    FlowSuspension.exists_unique_phase_corrected_cylinder A hAsource
      (hf.div_const s) hheightAux V hV hAfield
      F hF Q P H h0 hH0 hQ0 hP0 (fun _ hz => hQsource ▸ hz)
      (fun _ hz => hPsource ▸ hz) hQtarget hPtarget hdiagram htrans
      (fun z hz => hleft z hz 0) (fun z hz => hright z hz 1) hold hv₀ hv₁ hv₀zero hv₁zero
  have hdescWf (x : M) (hx : x ∉ criticalPoints E f) : mvfderiv 𝓘(ℝ, E) f x (W x) < 0 :=
    (FlowTimeChange.descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hs (W x)).mp
      (hdescW x ((FlowTimeChange.descending_height_div_const_iff
        (hf.mdifferentiableAt (by simp)) hs (V x)).mpr (hdesc x hx)))
  have hAregular (x : M) (hx : x ∈ A.target) : V x ≠ 0 := by
    intro hz
    rw [hAfield x hx] at hz
    have hh := (partialChartField_zero_iff A (fun _ : Z × ℝ => (0, 1)) hx).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hqN : Φq (-a, 0) ∉ N := fun hx => hAregular _ (hNsub hx) (hzero _ hq)
  have hpN : Φp (a, 0) ∉ N := fun hx => hAregular _ (hNsub hx) (hzero _ hp)
  have hQ0source : 0 ∈ Q.source := hQsource ▸ h0
  have hP0source : 0 ∈ P.source := by
    rw [hPsource, ← hH0]
    exact H.map_source' h0
  have hne : Φq (-a, 0) ≠ Φp (a, 0) := by
    intro h
    exact hpq.ne (congrArg f h.symm)
  obtain ⟨Γ, hΓaxis, hΓfield, hΓq, hΓp, hΓcenter⟩ :=
    exists_full_cubic_chart_from_corrected_cylinder σ hσ ha Φq Φp A hAsource hV1
      hqfield hpfield hAfield F hF L₁ L₂ Q P v₀ v₁ Q.open_source P.open_source
      hQ0source hP0source (fun u hu => hQU (Q.map_source' hu))
      (fun u hu => hPU (P.map_source' hu)) hRq hRp hboxq hboxp hsliceq hslicep
      hphaseq hphasep Ξ Q.open_source hQ0source hΞsource hΞtarget
      (hW.of_le (by simp)) hΞfield G hG (hgerm _ hqN) (hgerm _ hpN) hne
      (hmatch.mono fun _ h => h.1) (hmatch.mono fun _ h => h.2)
  have hΓ0 : Γ (0, 0) = A (0, 0) := hΓcenter.trans (hΞaxis 0)
  have hσne : ∀ i, σ i ≠ 0 := by
    intro i
    rcases hσ i with hi | hi <;> rw [hi] <;> norm_num
  have hcancel := cancel_unique_native_cubic_connection σ hσne ha Γ hΓaxis hf hm W hW
    hΓfield G hG (fun x hx => (hzeroW x).mpr (hzero x hx))
    hdescWf hinj
    (by rw [hΓp]; exact hp) (by rw [hΓq]; exact hq)
    (by rw [hΓp, hΓq]; exact hpq) (by rw [hΓp]; exact hc) (by rw [hΓq]; exact hd)
    (by simpa only [hΓp, hΓq] using hpair)
    (by
      intro x _ hbot htop
      rw [hΓq] at hbot
      rw [hΓp] at htop
      rw [hΓ0]
      exact hunique x hbot htop)
  simpa only [hΓp, hΓq] using hcancel

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
