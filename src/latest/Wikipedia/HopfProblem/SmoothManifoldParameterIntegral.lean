import Wikipedia.HopfProblem.SmoothMorseLemmaTaylorIntegral
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth compact-interval integrals on the original manifold

Local smoothness near a compact parameter interval suffices for the actual
integral to be smooth. A constructed cutoff extends the integrand near the
interval, and a tube neighborhood gives equality of the original integrals.
The manifold statement uses its original charts and does not transport an atlas.
-/

noncomputable section

open Set Topology MeasureTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothManifoldParameterIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint smoothness on an open neighborhood of the entire interval gives
smooth dependence of the literal integral at the original parameter. -/
theorem contDiffAt_intervalIntegral {G : E × ℝ → F} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (a b : ℝ) (x : E)
    (hline : ∀ t ∈ uIcc a b, (x, t) ∈ U) :
    ContDiffAt ℝ ∞ (fun y => ∫ t in a..b, G (y, t)) x := by
  let K : Set (E × ℝ) := {x} ×ˢ uIcc a b
  have hK : IsCompact K := isCompact_singleton.prod isCompact_uIcc
  have hKU : K ⊆ U := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    obtain rfl := mem_singleton_iff.mp hy
    exact hline t ht
  obtain ⟨G', hG', W, hWo, hKW, _, heq⟩ :=
    PeriodTorusLineBundleClassificationTransport.exists_smooth_extension_near_closed
      hK.isClosed hU hKU hG
  have hglobal := SmoothMorseLemma.contDiff_parametric_intervalIntegral G' hG' a b
  obtain ⟨N, V, hNo, _, hxN, hIV, hNV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hWo hKW
  apply hglobal.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hNo.mem_nhds (hxN (mem_singleton x))] with y hy
  apply intervalIntegral.integral_congr
  intro t ht
  exact (heq (hNV (show (y, t) ∈ N ×ˢ V from ⟨hy, hIV ht⟩))).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Integrating a jointly smooth function over a fixed compact real interval
is smooth for the original boundaryless real manifold atlas. -/
theorem contMDiff_intervalIntegral {G : M × ℝ → F}
    (hG : ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ G) (a b : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun x => ∫ t in a..b, G (x, t)) := by
  intro x
  let e := chartAt E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hx' : e x ∈ e.target := e.map_source hx
  have hlocal : ContDiffOn ℝ ∞ (fun p : E × ℝ => G (e.symm p.1, p.2))
      (e.target ×ˢ univ) := by
    have hinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target :=
      contMDiffOn_chart_symm
    have hfirst : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞
        (fun p : E × ℝ => e.symm p.1) (e.target ×ˢ univ) :=
      hinv.comp (contDiff_fst.contMDiff.contMDiffOn) (fun _ hp => hp.1)
    have hpair : ContMDiffOn 𝓘(ℝ, E × ℝ) ((𝓘(ℝ, E)).prod 𝓘(ℝ)) ∞
        (fun p : E × ℝ => (e.symm p.1, p.2)) (e.target ×ˢ univ) :=
      hfirst.prodMk (contDiff_snd.contMDiff.contMDiffOn)
    exact (hG.comp_contMDiffOn hpair).contDiffOn
  have hint := contDiffAt_intervalIntegral (e.open_target.prod isOpen_univ)
    hlocal a b (e x) (fun _ _ => ⟨hx', mem_univ _⟩)
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e x :=
    contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hx)
  have hcomp := hint.contMDiffAt.comp x hchart
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.left_inv hy]

end Wikipedia.HopfProblem.SmoothManifoldParameterIntegral
