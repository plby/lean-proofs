import Wikipedia.NoExoticSixSphere.FlatSphereChartInsertion
import Wikipedia.NoExoticSixSphere.RelativeImmersedSphereRepresentative
import Wikipedia.NoExoticSixSphere.BasedSphereMapSmoothing

/-!
# A based immersed representative with a prescribed embedded model derivative

For an arbitrary continuous sphere map, flattening, chart insertion, and the
constructed relative generic slice give a smooth self-transverse immersion.
The actual based homotopy is retained, the chosen center fiber is globally
unique, and the native derivative at the center agrees with the specified
embedded chart model. No smoothness of the initial sphere map is assumed.
-/

noncomputable section

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_based_immersed_representative_with_model
    (f : C(Sphere 3, M)) (x : Sphere 3)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 6) E M ∞)
    (hball : ball (0 : E) 3 ⊆ Φ.source) (hcenter : Φ 0 = f x)
    (v : Sphere 3 → E) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ v)
    (hbound : ∀ s, ‖v s‖ ≤ 2) (hxv : v x = 0)
    (hvimm : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (fun z ↦ Φ (v z)) s))
    (hvinj : Injective (fun z ↦ Φ (v z))) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.HomotopicRel g {x} ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) ∧
      (∀ s z, s ≠ z → g s = g z → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g s).coprod (mfderiv (𝓡 3) (𝓡 6) g z))) ∧
      mfderiv (𝓡 3) (𝓡 6) g x = mfderiv (𝓡 3) (𝓡 6) (fun z ↦ Φ (v z)) x ∧
      ∀ s, g s = f x ↔ s = x := by
  obtain ⟨f₀, hf₀, H₀, U, hU, hxU, hflat⟩ := exists_smooth_flat_based_sphereMap x f
  have hflat' : EqOn f₀ (fun _ ↦ Φ 0) U := fun s hs ↦ (hflat hs).trans hcenter.symm
  obtain ⟨F, hF, HF, χ, hχ, hn, hboundχ, hχx, W, hW, hχW, hFW⟩ :=
    exists_flat_sphere_chart_insertion Φ hball f₀ hf₀ x U hU hxU hflat' v hv hbound hxv
  have hD : ∀ s, χ s = 0 → mfderiv (𝓡 3) (𝓡 6) F s =
      mfderiv (𝓡 3) (𝓡 6) (fun z ↦ Φ (v z)) s := by
    intro s hs
    have he : (F : Sphere 3 → M) =ᶠ[𝓝 s] (fun z ↦ Φ (v z)) := by
      filter_upwards [hW.mem_nhds (hχW hs)] with z hz
      exact hFW hz
    exact he.mfderiv_eq
  have hFi : ∀ s, χ s = 0 → Injective (mfderiv (𝓡 3) (𝓡 6) F s) := by
    intro s hs
    rw [hD s hs]
    exact hvimm s
  have hinj : InjOn F {s | χ s = 0} := by
    intro s hs z hz he
    apply hvinj
    exact (hFW (hχW hs)).symm.trans (he.trans (hFW (hχW hz)))
  have hFt : ∀ s z, χ s = 0 → χ z = 0 → s ≠ z → F s = F z → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) F s).coprod (mfderiv (𝓡 3) (𝓡 6) F z)) :=
    fun s z hs hz hne he ↦ (hne (hinj hs hz he)).elim
  obtain ⟨g, hg, H, hgi, hgt, hDg, hu⟩ :=
    e.exists_selfTransverse_immersed_relative_unique_center r F hF χ hχ hn hboundχ hFi hFt
      x hχx (fun s hs he ↦ hinj hs hχx he)
  have Hx : F.HomotopicRel g {x} := by
    obtain ⟨K⟩ := H
    refine ⟨{ toHomotopy := K.toHomotopy, prop' := ?_ }⟩
    intro u s hs
    rcases hs with rfl
    exact K.eq_fst u hχx
  have hFx : F x = f x :=
    (hFW (hχW hχx)).trans ((congrArg Φ hxv).trans hcenter)
  refine ⟨g, hg, H₀.trans (HF.trans Hx), hgi, hgt, (hDg x hχx).trans (hD x hχx), ?_⟩
  intro s
  rw [← hFx]
  exact hu s

end NoExoticSixSphere.EuclideanEmbedding
