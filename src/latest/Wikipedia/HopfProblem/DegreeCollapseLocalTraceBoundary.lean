import Wikipedia.HopfProblem.DegreeCollapseNativeTraceNormalDerivative
import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryHomology

/-!
# Construct the actual small normal boundary of a transverse native trace

Use any genuine native parameter chart centered at the crossing. The
normal derivative is constructed from native transversality and the
chart derivative. Its continuous linear equivalence supplies actual
small-boundary data inside any prescribed neighborhood, hence an actual
homology isomorphism for the normalized normal boundary map.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M A G H X : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [ChartedSpace H X] {f : M → ℝ} {p : M}

theorem exists_native_trace_boundary_data
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ G = Module.finrank ℝ d.chart.NegativeCoordinates)
    (g : X → d.UpperLevel) (x : X)
    (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, A) I A X ∞)
    (hsource : (0 : A) ∈ Ψ.source) (hcenter : Ψ 0 = x)
    {s : Set A} (hs : s ∈ 𝓝 (0 : A)) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffAt I 𝓘(ℝ, RegularLevel.Model E) ∞ g x →
    d.surgery.beltSphere v = g x →
    NativeTransversality.At I (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g d.surgery.beltSphere x v →
    ∃ L : A ≃L[ℝ] d.chart.NegativeCoordinates,
      Nonempty (LocalDegree.BoundaryData (fun z : A => d.beltNormal (g (Ψ z))) L s) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hg hcross htrans
  let N : X → d.chart.NegativeCoordinates := d.beltNormal ∘ g
  have hx : g x ∈ d.beltNormalDomain := hcross ▸ d.belt_mem_normalDomain v
  have hnormal := (d.contMDiffOn_beltNormal hf).contMDiffAt
    (d.isOpen_beltNormalDomain.mem_nhds hx)
  have hN : ContMDiffAt I 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ N x := hnormal.comp x hg
  have hNΨ : ContMDiffAt I 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ N (Ψ 0) := by
    rw [hcenter]
    exact hN
  have hΨ : ContMDiffAt 𝓘(ℝ, A) I ∞ Ψ 0 :=
    Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds hsource)
  let F : A → d.chart.NegativeCoordinates := N ∘ Ψ
  have hF : ContDiffAt ℝ ∞ F 0 := (hNΨ.comp 0 hΨ).contDiffAt
  have hBN : Bijective (mfderiv I 𝓘(ℝ, d.chart.NegativeCoordinates) N x) :=
    bijective_native_trace_beltNormal d hf n hdim g x v
      (hg.mdifferentiableAt (by simp)) hcross htrans
  have hBΨ := PartialChart.bijective_mfderiv Ψ hsource
  have hder : fderiv ℝ F 0 =
      (mfderiv I 𝓘(ℝ, d.chart.NegativeCoordinates) N x : G →L[ℝ] d.chart.NegativeCoordinates).comp
        (mfderiv 𝓘(ℝ, A) I Ψ 0) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp 0 (hNΨ.mdifferentiableAt (by simp))
      (hΨ.mdifferentiableAt (by simp)), hcenter]
  have hBF : Bijective (fderiv ℝ F 0) := by
    rw [hder]
    exact hBN.comp hBΨ
  let L := (LinearEquiv.ofBijective (fderiv ℝ F 0).toLinearMap hBF).toContinuousLinearEquiv
  have hFL : HasFDerivAt F L.toContinuousLinearMap 0 :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have hF0 : F 0 = 0 := by
    change d.beltNormal (g (Ψ 0)) = 0
    rw [hcenter, ← hcross, d.beltNormal_belt]
  exact ⟨L, LocalDegree.nonempty_boundaryData_of_contDiffAt L hFL hF0 hs hF⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
