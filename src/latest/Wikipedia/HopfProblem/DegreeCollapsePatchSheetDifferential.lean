import Wikipedia.HopfProblem.DegreeCollapsePatchSourceCoordinates
import Wikipedia.SmoothSixDPoincare.TubularSheetTransition

/-!
# The original branch derivative in the actual tubular sheet coordinates

The sheet transition derivative composed with the induced original source
coordinate derivative is the original immersion derivative in inverse
tubular coordinates. Composing with the forward tubular derivative gives
an exact comparison square, retaining the original source tangent map.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare

variable {A B Z E M G N : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace N] [ChartedSpace G N]
  {F : N → M} {K : Set N} {k : (ℝ × ℝ) → M}
  (d : StripNormalData A B (E := E) (F '' K) k)
  (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)

theorem sheetDifferential_comp_patchSource
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : N} (hK : K ∈ 𝓝 x)
    (hx : F x = k (t, 0)) (hT : F x ∈ Ψ.target) :
    (d.sheetDifferential Ψ t).comp
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, ℝ × A) (patchSourceCoordinates d.chart F) x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ × ℝ) × Z) Ψ.symm (F x)).comp
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) := by
  have hcenter : F x = d.chart (StripCoordinates.center t) := hx.trans (d.center t)
  have hxD : F x ∈ d.chart.target := hcenter.symm ▸ d.chart.map_source' (d.line ht)
  have hinv : d.chart.symm (F x) = StripCoordinates.center t := by
    rw [hcenter]
    exact d.chart.left_inv' (d.line ht)
  have hfactor := original_patch_derivative_factor d.chart F hF d.sheet hK hxD
  rw [hinv] at hfactor
  have hT' : d.chart (StripCoordinates.center t) ∈ Ψ.target := hcenter ▸ hT
  rw [d.sheetDifferential_eq_native Ψ ht hT', ← hcenter]
  exact (congrArg (fun L : G →L[ℝ] E =>
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ × ℝ) × Z) Ψ.symm (F x)).comp L) hfactor).symm

theorem original_derivative_eq_forward_sheetDifferential
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : N} (hK : K ∈ 𝓝 x)
    (hx : F x = k (t, 0)) (hT : F x ∈ Ψ.target) :
    mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x =
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) Ψ (Ψ.symm (F x))).comp
        ((d.sheetDifferential Ψ t).comp
          (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, ℝ × A) (patchSourceCoordinates d.chart F) x)) := by
  have hdiff : Ψ.toOpenPartialHomeomorph.MDifferentiable
      𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) :=
    ⟨Ψ.mdifferentiableOn (by simp), Ψ.symm.mdifferentiableOn (by simp)⟩
  have hTR := hdiff.comp_symm_deriv hT
  rw [sheetDifferential_comp_patchSource d Ψ hF ht hK hx hT]
  change (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x : G →L[ℝ] E) =
    (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) Ψ (Ψ.symm (F x)) :
      ((ℝ × ℝ) × Z) →L[ℝ] E).comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ × ℝ) × Z) Ψ.symm (F x) :
          E →L[ℝ] ((ℝ × ℝ) × Z)).comp
          (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x : G →L[ℝ] E))
  exact (congrArg (fun L : E →L[ℝ] E =>
    L.comp (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x)) hTR).symm

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
