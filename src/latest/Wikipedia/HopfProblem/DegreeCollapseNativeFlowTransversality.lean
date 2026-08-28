import Wikipedia.HopfProblem.DegreeCollapseProjectedFlowTransversality

/-!
# Native transverse flow sheets imply transverse cylinder labels

The genuine native cylinder transports the full tangent-space condition
to its vector-space coordinates. Exact transverse-label germs there
then project it to the label-sheet condition used by cancellation.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem transverse_labels_of_native_flow_sheets
    (C : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    (hC0 : (0 : Z × ℝ) ∈ C.source)
    (F : ℝ × A → M) (G : ℝ × B → M)
    (hF : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F 0)
    (hG : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) G 0)
    (hF0 : F 0 = C 0) (hG0 : G 0 = C 0)
    {f : A → Z} {g : B → Z}
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (C.symm (F u)).1) =ᶠ[𝓝 0]
      (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (C.symm (G u)).1) =ᶠ[𝓝 0]
      (fun u : ℝ × B => g u.2))
    (htrans : NativeTransversality.At 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) F G 0 0) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) f g 0 0 := by
  have hFt : F 0 ∈ C.target := hF0.symm ▸ C.map_source' hC0
  have hGt : G 0 ∈ C.target := hG0.symm ▸ C.map_source' hC0
  have hFb : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, Z × ℝ) (C.symm ∘ F) 0 :=
    (C.symm.mdifferentiableAt (by simp) hFt).comp (f := F) 0 hF
  have hGb : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z × ℝ) (C.symm ∘ G) 0 :=
    (C.symm.mdifferentiableAt (by simp) hGt).comp (f := G) 0 hG
  have hcross : G 0 = F 0 := hG0.trans hF0.symm
  have ht := ChartMapPerturbation.transverse_in_chart C.symm hF hG hcross hFt (htrans hcross)
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at ht
  have hl := transverse_labels_of_time_independent_flow_sheets
    hFb.differentiableAt hGb.differentiableAt hf hg hlabelF hlabelG ht
  intro _
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv]
  exact hl

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
