import Wikipedia.HopfProblem.DegreeCollapseNativeLevelTransverseSheets

/-!
# Transversality transferred through actual sheet factorizations

If two transverse native sheets factor locally through two other smooth
sheets, the latter tangent images also span. Exact germ factorizations
are sufficient; no rank or dimension comparison is assumed.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B U V E HU HV HE X Y M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace HE]
  {I : ModelWithCorners ℝ U HU} {I' : ModelWithCorners ℝ V HV}
  {J : ModelWithCorners ℝ E HE}
  [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y] [ChartedSpace HV Y]
  [TopologicalSpace M] [ChartedSpace HE M]

theorem native_transversality_of_sheet_factorizations
    {F : X → M} {G : Y → M} {f : A → M} {g : B → M}
    {u : X → A} {v : Y → B} {x : X} {y : Y}
    (hf : MDifferentiableAt 𝓘(ℝ, A) J f 0)
    (hg : MDifferentiableAt 𝓘(ℝ, B) J g 0)
    (hu : MDifferentiableAt I 𝓘(ℝ, A) u x)
    (hv : MDifferentiableAt I' 𝓘(ℝ, B) v y)
    (hu0 : u x = 0) (hv0 : v y = 0)
    (hF : F =ᶠ[𝓝 x] (f ∘ u)) (hG : G =ᶠ[𝓝 y] (g ∘ v))
    (hcross : G y = F x) (htrans : NativeTransversality.At I I' J F G x y) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) J f g 0 0 := by
  have hfx : MDifferentiableAt 𝓘(ℝ, A) J f (u x) := hu0 ▸ hf
  have hgy : MDifferentiableAt 𝓘(ℝ, B) J g (v y) := hv0 ▸ hg
  have hFd : (mfderiv I J F x : U →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, A) J f 0 : A →L[ℝ] E).comp (mfderiv I 𝓘(ℝ, A) u x) := by
    have heq : (mfderiv I J F x : U →L[ℝ] E) = mfderiv I J (f ∘ u) x := hF.mfderiv_eq
    rw [heq, mfderiv_comp x hfx hu, hu0]
  have hGd : (mfderiv I' J G y : V →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, B) J g 0 : B →L[ℝ] E).comp (mfderiv I' 𝓘(ℝ, B) v y) := by
    have heq : (mfderiv I' J G y : V →L[ℝ] E) = mfderiv I' J (g ∘ v) y := hG.mfderiv_eq
    rw [heq, mfderiv_comp y hgy hv, hv0]
  intro _ z
  obtain ⟨⟨a, b⟩, hab⟩ := htrans hcross z
  refine ⟨(mfderiv I 𝓘(ℝ, A) u x a, mfderiv I' 𝓘(ℝ, B) v y b), ?_⟩
  rw [hFd, hGd] at hab
  exact hab

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
