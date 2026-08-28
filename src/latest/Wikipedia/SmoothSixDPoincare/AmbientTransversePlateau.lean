import Wikipedia.SmoothSixDPoincare.AmbientIsotopy
import Wikipedia.SmoothSixDPoincare.ChartTransversalityPerturbation

/-!
# Transverse plateaus realized by actual ambient diffeomorphisms

The good translation parameter supplied by native Sard is realized by the
constructed ambient bump family. Thus the first sheet remains the image of
the original sheet under a genuine smooth diffeomorphism. The second sheet
is held fixed when testing the new intersections.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {D Z G F H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]
  [LindelofSpace (X × Y)]

/-- An arbitrarily small good coordinate translation is an actual ambient diffeomorphism.
All original points over the cutoff plateau become transverse to the unchanged second sheet. -/
theorem exists_ambient_transverse_plateau
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : X → N} {g : Y → N} {β : F → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ c.target)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ ∃ e : Diffeomorph J J N N ∞,
      (∀ y, e y = SupportedDiffeomorph.bumpFamily c.symm β (a, y)) ∧
      (∀ y ∉ c.symm '' tsupport β, e y = y) ∧
      SupportedDiffeomorph.IsotopicToIdentity e ∧
      ∀ x, f x ∈ c.source → (β =ᶠ[𝓝 (c (f x))] fun _ => 1) →
        ∀ y, g y = e (f x) →
          Surjective ((mfderiv I J (e ∘ f) x : D →L[ℝ] G).coprod
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
  obtain ⟨δ, hδ, hdiff, -, hsource⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily c.symm hβ hcompact hsupport
  obtain ⟨η, hη, hisotopy⟩ :=
    SupportedDiffeomorph.exists_radius_bumpFamily_isotopy c.symm hβ hcompact hsupport
  obtain ⟨a, ha, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε (lt_min hδ hη))
  have hn : ‖a‖ < min ε (min δ η) := by simpa only [dist_zero_left] using hnorm
  have haδ := (lt_min_iff.mp (lt_min_iff.mp hn).2).1
  have haη := (lt_min_iff.mp (lt_min_iff.mp hn).2).2
  obtain ⟨e, he⟩ := hdiff a haδ
  have hsrc := hsource a haδ
  refine ⟨a, (lt_min_iff.mp hn).1, e, he, ?_, hisotopy a haη e he, ?_⟩
  · intro y hy
    rw [he]
    exact SupportedDiffeomorph.bumpFamily_fixed_outside c.symm β a hy
  · intro x hfx hx y hxy
    have hnew : e (f x) ∈ c.source := by
      rw [he]
      exact SupportedDiffeomorph.bumpFamily_mem_target c.symm β a hsrc hfx
    have hgy : g y ∈ c.source := hxy ▸ hnew
    have hcfAt := hcf.contMDiffAt (hU.mem_nhds hfx)
    have hevent : c ∘ (e ∘ f) =ᶠ[𝓝 x] fun z => c (f z) + a := by
      filter_upwards [hU.mem_nhds hfx, hx.comp_tendsto hcfAt.continuousAt] with z hz hβz
      change β (c (f z)) = 1 at hβz
      change c (e (f z)) = c (f z) + a
      rw [he]
      have hh := SupportedDiffeomorph.bumpFamily_coordinates c.symm β a hsrc hz
      change c (SupportedDiffeomorph.bumpFamily c.symm β (a, f z)) =
        c (f z) + β (c (f z)) • a at hh
      exact hh.trans (by rw [hβz, one_smul])
    have hcross : (c ∘ g) y = (c ∘ f) x + a := by
      change c (g y) = c (f x) + a
      rw [hxy]
      exact hevent.eq_of_nhds
    have ht := ha x hfx y hgy hcross
    have hderiv := mfderiv_eq_of_translation_germ
      (hcfAt.mdifferentiableAt (by simp)) hevent
    apply transverse_of_chart c ((e.contMDiff.comp hf).mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp)) hxy hnew
    rw [hderiv]
    exact ht

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
