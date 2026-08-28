import Wikipedia.NoExoticSixSphere.RelativeSphereIntersectionTimes
import Wikipedia.NoExoticSixSphere.RelativeImmersedSphereRepresentative
import Wikipedia.NoExoticSixSphere.SphereNativeDerivativeCoordinates

/-!
# A relative immersed representative transverse to a fixed sphere

One parameter satisfies all jet, self-intersection, center-avoidance, and
fixed-sphere incidence conditions. One time then avoids all singularities
and is regular for both kinds of intersection. The actual relative homotopy
and protected native derivatives are retained.
-/

noncomputable section

open Set Function Topology
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereFamily SphereSumNeck
open SpatiallyRelativeSphereFamily
open ManifoldAffineSphereFamily (exists_finite_chart_cover)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_relative_immersed_representative_transverse_to
    (f g : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (χ : Sphere 3 → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hn : ∀ s, 0 ≤ χ s) (hbound : ∀ s, ‖χ s‖ ≤ 1)
    (hi : ∀ s, χ s = 0 → Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (ht : ∀ s z, χ s = 0 → χ z = 0 → s ≠ z → f s = f z →
      NativeSphereTransverseAt f f s z)
    (hm : ∀ s z, χ s = 0 → f s = g z → NativeSphereTransverseAt f g s z)
    (b : M) :
    ∃ F : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ F ∧
      f.HomotopicRel F {s | χ s = 0} ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) F s)) ∧
      NativeSphereSelfTransverse F ∧ NativeSpherePairTransverse F g ∧
      (∀ s, χ s = 0 → mfderiv (𝓡 3) (𝓡 6) F s = mfderiv (𝓡 3) (𝓡 6) f s) ∧
      ∀ s, χ s ≠ 0 → F s ≠ b := by
  let f₀ : ℝ → Sphere 3 → M := fun _ s ↦ f s
  let g₀ : ℝ → Sphere 3 → M := fun _ s ↦ g s
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  have hg₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g₀) :=
    hg.comp contMDiff_snd
  obtain ⟨S, hSfin, hS⟩ := exists_finite_chart_cover 3 (Sphere 3)
  obtain ⟨C, hCfin, hC⟩ := exists_finite_chart_cover 6 M
  obtain ⟨δ, hδ, hmem₀, hsmooth⟩ := exists_smooth_parameter_ball e r f₀ χ hf₀ hχ hbound
  obtain ⟨p, hp, hgen, ha, hmut⟩ :=
    RelativeSphereIntersectionFamily.exists_small_simultaneous_in_charts e r f₀ g₀ χ
      hf₀ hg₀ hχ rfl S hSfin.countable C hCfin.countable b hδ
  have hmem : ∀ t s, ambient e f₀ χ p t s ∈ r.domain := hmem₀ p hp
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f₀ χ p)) :=
    hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hp)
  let P := SpatiallyRelativeSphereFamily.map e r f₀ χ p
  let A := {q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1} ∩ singularParameters (n := 6) P
  have hdis : IsDiscrete A :=
    isDiscrete_interior_singularParameters e r f₀ χ hf₀ hχ p hn hP S C hS hC hmem hgen
      (fun _ _ s hs ↦ hi s hs)
  have hcount : A.Countable :=
    (HereditarilyLindelofSpace.isLindelof A).countable_of_isDiscrete hdis
  have hsreg := SpatiallyRelativeSphereFamily.ae_regular_time_in_charts e r f₀ χ hf₀ hχ p
    volume S hSfin.countable C hCfin.countable hgen
  have hmreg := RelativeSphereIntersectionFamily.ae_regular_time_in_charts e r f₀ g₀ χ
    hf₀ hg₀ hχ p volume S hSfin.countable C hCfin.countable hmut
  have hdense := Measure.dense_of_ae
    (hsreg.and (hmreg.and ((hcount.image Prod.fst).ae_notMem volume)))
  obtain ⟨t, ⟨htself, htmut, hta⟩, htime⟩ :=
    hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr (by norm_num : (0 : ℝ) < 1))
  have hF : ContMDiff (𝓡 3) (𝓡 6) ∞ (P t) :=
    hP.comp (contMDiff_const.prodMk contMDiff_id)
  let F : C(Sphere 3, M) := ⟨P t, hF.continuous⟩
  have H : f.HomotopicRel F {s | χ s = 0} := by
    refine ⟨{
      toFun := fun q ↦ P ((q.1 : ℝ) * t) q.2
      continuous_toFun := hP.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_
    }⟩
    · intro s
      change P ((0 : ℝ) * t) s = f s
      rw [zero_mul]
      exact map_eq_outside e r f₀ χ p (Or.inl le_rfl) s
    · intro s
      change P ((1 : ℝ) * t) s = P t s
      rw [one_mul]
    · exact fun u s hs ↦ map_eq_zero_cutoff e r f₀ χ p ((u : ℝ) * t) s hs
  refine ⟨F, hF, H, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    by_contra hs
    exact hta ⟨(t, s), ⟨htime, hs⟩, rfl⟩
  · exact self_transverse_of_regular_time e r f₀ χ hf₀ hχ hn p hP S C hS hC
      t htime (hmem t) htself ht
  · exact RelativeSphereIntersectionFamily.pair_transverse_of_regular_time e r f₀ g₀ χ
      hf₀ hg₀ hχ hn p hP S C hS hC t htime (hmem t) htmut hm
  · exact fun s hs ↦ mfderiv_map_of_zero_cutoff e r f₀ χ hf₀ hχ hn p t s hs
  · exact fun s hs ↦ map_ne_center_of_avoids_in_charts e r f₀ χ hf₀ hχ
      S C hS hC b p ha t s htime hs (hmem t s)

end NoExoticSixSphere.EuclideanEmbedding
