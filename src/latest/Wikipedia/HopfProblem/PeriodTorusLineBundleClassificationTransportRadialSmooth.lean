import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportIntegral

/-!
# Local smoothness of radial one-form integrals

A constructed cutoff extends the one-form near the compact segment, and the
tube lemma proves that its parameter integral agrees locally with the actual
one. The interval and the open chart are fixed; no global frame is assumed.
-/

noncomputable section

open Set Topology MeasureTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem contDiffAt_radial_integral (C : E → E →L[ℝ] ℂ) {U : Set E}
    (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) (a b : ℝ) (x₀ : E)
    (hchart : MapsTo (fun t : ℝ => t • x₀) (uIcc a b) U) :
    ContDiffAt ℝ ∞ (fun x => ∫ t in a..b, C (t • x) x) x₀ := by
  let K : Set E := (fun t : ℝ => t • x₀) '' uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image (continuous_id.smul continuous_const)
  have hKU : K ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hchart ht
  obtain ⟨G, hG, W, hWo, hKW, -, hGeq⟩ := exists_smooth_extension_near_closed
    (E := E) (F := E →L[ℝ] ℂ) (f := C) (K := K) (U := U)
    hK.isClosed hU hKU hC
  let F : E × ℝ → ℂ := fun q => G (q.2 • q.1) q.1
  have hF : ContDiff ℝ ∞ F :=
    (hG.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_fst
  have hglobal : ContDiff ℝ ∞ (fun x => ∫ t in a..b, F (x, t)) :=
    contDiff_parametric_intervalIntegral F hF a b
  let O : Set (E × ℝ) := {q | q.2 • q.1 ∈ W}
  have hOo : IsOpen O := hWo.preimage (continuous_snd.smul continuous_fst)
  have hKO : ({x₀} ×ˢ uIcc a b) ⊆ O := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    obtain rfl := mem_singleton_iff.mp hx
    exact hKW ⟨t, ht, rfl⟩
  obtain ⟨N, V, hNo, -, hxN, hIV, hNV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hOo hKO
  apply hglobal.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hNo.mem_nhds (hxN (mem_singleton x₀))] with x hx
  apply intervalIntegral.integral_congr
  intro t ht
  have htx : t • x ∈ W := hNV (show (x, t) ∈ N ×ˢ V from ⟨hx, hIV ht⟩)
  exact congrArg (fun L : E →L[ℝ] ℂ => L x) (hGeq htx).symm

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
