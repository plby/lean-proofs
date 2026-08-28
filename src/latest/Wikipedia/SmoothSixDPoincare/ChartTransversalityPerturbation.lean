import Wikipedia.SmoothSixDPoincare.ManifoldSheetTranslations
import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Transverse perturbation on a genuine chart plateau

A compactly supported chart translation is smooth on the original manifold.
One small parameter makes it transverse to the second sheet at every point
where the cutoff is locally one. No transversality is assumed there.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {D Z G F H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]
  [TopologicalSpace N] [ChartedSpace K N]

/-- A locally constant translation does not change the native derivative into a vector space. -/
theorem mfderiv_eq_of_translation_germ {u v : X → F} {a : F} {x : X}
    (hu : MDifferentiableAt I 𝓘(ℝ, F) u x)
    (hevent : v =ᶠ[𝓝 x] fun z => u z + a) :
    (mfderiv I 𝓘(ℝ, F) v x : D →L[ℝ] F) = mfderiv I 𝓘(ℝ, F) u x := by
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) u x
  let C : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (fun _ : X => a) x
  have hC : C = 0 := mfderiv_const
  have hh := mfderiv_add hu
    (show MDifferentiableAt I 𝓘(ℝ, F) (fun _ : X => a) x from mdifferentiableAt_const)
  change (mfderiv I 𝓘(ℝ, F) (fun z => u z + a) x : D →L[ℝ] F) = A + C at hh
  rw [hC] at hh
  exact hevent.mfderiv_eq.trans (hh.trans (add_zero A))

/-- Transversality in a genuine smooth target chart implies native transversality. -/
theorem transverse_of_chart
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hxy : g y = f x) (hx : f x ∈ c.source)
    (ht : Surjective ((mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F).coprod
      (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F))) :
    Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod
      (mfderiv I' J g y : Z →L[ℝ] G)) := by
  let A : D →L[ℝ] G := mfderiv I J f x
  let B : Z →L[ℝ] G := mfderiv I' J g y
  let C : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) c (f x)
  have hy : g y ∈ c.source := hxy ▸ hx
  have hA : (mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F) = C.comp A :=
    mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf
  have hB : (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F) = C.comp B := by
    rw [mfderiv_comp y (c.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  have heq : (C.comp A).coprod (C.comp B) = C.comp (A.coprod B) := by
    apply ContinuousLinearMap.ext
    intro v
    change C (A v.1) + C (B v.2) = C (A v.1 + B v.2)
    exact (C.map_add _ _).symm
  rw [hA, hB] at ht
  change Surjective ((C.comp A).coprod (C.comp B)) at ht
  rw [heq] at ht
  have hC : Injective C := (PartialChart.bijective_mfderiv c hx).injective
  change Surjective (A.coprod B)
  intro w
  obtain ⟨v, hv⟩ := ht (C w)
  exact ⟨v, hC hv⟩

/-- Native transversality is preserved by the actual target chart. -/
theorem transverse_in_chart
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hxy : g y = f x) (hx : f x ∈ c.source)
    (ht : Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod
      (mfderiv I' J g y : Z →L[ℝ] G))) :
    Surjective ((mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F).coprod
      (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F)) := by
  let A : D →L[ℝ] G := mfderiv I J f x
  let B : Z →L[ℝ] G := mfderiv I' J g y
  let C : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) c (f x)
  have hy : g y ∈ c.source := hxy ▸ hx
  have hA : (mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F) = C.comp A :=
    mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf
  have hB : (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F) = C.comp B := by
    rw [mfderiv_comp y (c.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  rw [hA, hB]
  change Surjective ((C.comp A).coprod (C.comp B))
  have hC : Surjective C := (PartialChart.bijective_mfderiv c hx).surjective
  change Surjective (A.coprod B) at ht
  intro w
  obtain ⟨z, hz⟩ := hC w
  obtain ⟨v, hv⟩ := ht z
  refine ⟨v, ?_⟩
  change C (A v.1) + C (B v.2) = w
  rw [← C.map_add]
  exact (congrArg C hv).trans hz

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ F]
  [I.Boundaryless] [I'.Boundaryless]
  [IsManifold I ∞ X] [IsManifold I' ∞ Y] [LindelofSpace (X × Y)]

/-- Every plateau of the original cutoff becomes transverse for one arbitrarily small
valid parameter. The statement does not assert transversality in the transition region. -/
theorem exists_small_transverse_plateau_parameter
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : X → N} {g : Y → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ Valid c f β a ∧ ContMDiff I J ∞ (perturb c f β a) ∧
      ∀ x, (β =ᶠ[𝓝 x] fun _ => 1) → ∀ y, g y = perturb c f β a x →
        Surjective ((mfderiv I J (perturb c f β a) x : D →L[ℝ] G).coprod
          (mfderiv I' J g y : Z →L[ℝ] G)) := by
  let U : Set X := f ⁻¹' c.source
  let V : Set Y := g ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have hV : IsOpen V := c.open_source.preimage hg.continuous
  have hcf : ContMDiffOn I 𝓘(ℝ, F) ∞ (c ∘ f) U :=
    c.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ hx => hx)
  have hcg : ContMDiffOn I' 𝓘(ℝ, F) ∞ (c ∘ g) V :=
    c.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
  have hdense := TransverseCoordinates.dense_native_translations hU hV hcf hcg hdim
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, ha, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have hn : ‖a‖ < min ε δ := by simpa only [dist_zero_left] using hnorm
  have hva : Valid c f β a := hvalid a (lt_min_iff.mp hn).2
  have hsmooth := contMDiff_perturb c hf hβ hsupport hva
  refine ⟨a, (lt_min_iff.mp hn).1, hva, hsmooth, ?_⟩
  intro x hx y hxy
  have hone : β x = 1 := hx.eq_of_nhds
  have hfx : f x ∈ c.source := hsupport (subset_tsupport β (by
    change β x ≠ 0
    rw [hone]
    norm_num))
  have hnew : perturb c f β a x ∈ c.source := perturb_mem_source c f β hva hfx
  have hgy : g y ∈ c.source := hxy ▸ hnew
  have hcross : (c ∘ g) y = (c ∘ f) x + a := by
    change c (g y) = c (f x) + a
    rw [hxy, chart_perturb c f β hva hfx]
    simp only [coordinateFamily, hone, one_smul]
  have ht := ha x hfx y hgy hcross
  have hevent : c ∘ perturb c f β a =ᶠ[𝓝 x] fun z => c (f z) + a := by
    filter_upwards [hx, hU.mem_nhds hfx] with z hz hzc
    change c (perturb c f β a z) = c (f z) + a
    rw [chart_perturb c f β hva hzc]
    simp only [coordinateFamily, hz, one_smul]
  have hcfAt := (hcf.contMDiffAt (hU.mem_nhds hfx)).mdifferentiableAt (by simp)
  have hderiv : (mfderiv I 𝓘(ℝ, F) (c ∘ perturb c f β a) x : D →L[ℝ] F) =
      mfderiv I 𝓘(ℝ, F) (c ∘ f) x := mfderiv_eq_of_translation_germ hcfAt hevent
  apply transverse_of_chart c (hsmooth.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp)) hxy hnew
  rw [hderiv]
  exact ht

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
