import Wikipedia.HopfProblem.DegreeCollapseLowSphereEmbeddedRepresentative
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!

# Continuous sphere maps in an original open subset have embedded representatives there

Smooth the original map in the original open-subset atlas. The proved
small-parameter construction gives an embedded immersive endpoint and an
actual homotopy staying in that open subset. Lift this homotopy through
the literal subtype to retain the original homotopy class inside the open
subset, not merely its image class in the ambient manifold.
-/

noncomputable section

open Function Set TopologicalSpace Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereParameters

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding SingularMayerVietoris

variable {d n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)

include e r in
theorem exists_embedded_representative_in_open (hn : 2 * d < n) (U : Opens M)
    (f : C(Sphere d, U)) :
    ∃ g : C(Sphere d, U),
      ContMDiff (𝓡 d) (𝓡 n) ∞ ((subtypeInclusion (U : Set M)).comp g) ∧ f.Homotopic g ∧
      IsClosedEmbedding ((subtypeInclusion (U : Set M)).comp g) ∧
      ∀ s, Injective (mfderiv (𝓡 d) (𝓡 n) ((subtypeInclusion (U : Set M)).comp g) s) := by
  obtain ⟨F, hF, HF⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 d) (J := 𝓡 n) f
  let F₀ := (subtypeInclusion (U : Set M)).comp F
  have hF₀ : ContMDiff (𝓡 d) (𝓡 n) ∞ F₀ := contMDiff_subtype_val.comp hF
  obtain ⟨g, hg, hi, hd, H, hH⟩ := exists_embedded_homotopy_in_open_of_smooth e r hn
    F₀ hF₀ (U : Set M) U.isOpen (fun s ↦ (F s).property)
  have hgU (s : Sphere d) : g s ∈ U := by
    have he : H (1, s) = g s := H.map_one_left s
    exact he ▸ hH (1, s)
  let gU : C(Sphere d, U) :=
    ⟨fun s ↦ ⟨g s, hgU s⟩, g.continuous.subtype_mk _⟩
  let HU : F.Homotopy gU :=
    { toFun := fun q ↦ ⟨H q, hH q⟩
      continuous_toFun := H.continuous.subtype_mk _
      map_zero_left := fun s ↦ Subtype.ext (H.map_zero_left s)
      map_one_left := fun s ↦ Subtype.ext (H.map_one_left s) }
  exact ⟨gU, hg, HF.trans ⟨HU⟩, hi, hd⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSphereParameters

