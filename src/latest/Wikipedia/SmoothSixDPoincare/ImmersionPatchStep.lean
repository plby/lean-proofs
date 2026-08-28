import Wikipedia.SmoothSixDPoincare.AffinePatchFamily
import Wikipedia.SmoothSixDPoincare.MapSmoothingPatch

/-!
# Adding an immersive patch while retaining earlier patches and future charts

One small affine parameter satisfies the compact stability conditions and
avoids all singular and collision parameters on the new plateau. The actual
relative homotopy can fix any set on which the chosen cutoff vanishes.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open PlaneImmersion (Plane)
open ManifoldSmoothing (MapSmoothingPatch)

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- Improve one compact plateau while keeping an old compact immersive region and the entire
finite family of target-chart constraints. -/
theorem exists_immersion_patch_step {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, Plane) J (X := Plane) (N := N)) (i : ι)
    (f : C(Plane, N)) (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set Plane} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J f x))
    (hLsub : L ⊆ (p i).plateau) (hfixed : ∀ x ∈ C, (p i).cutoff x = 0) :
    ∃ g : C(Plane, N), ContMDiff 𝓘(ℝ, Plane) J ∞ g ∧
      (∀ j, (p j).Compatible g) ∧ f.HomotopicRel g C ∧
      Topology.IsClosedEmbedding (fun x : L => g x) ∧
      ∀ x ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g x) := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep : ∀ᶠ A : G × G in 𝓝 0,
      ∀ j, (p j).Compatible (affinePatch (p i).chart f (p i).cutoff A) := by
    apply eventually_all.mpr
    intro j
    exact eventually_affinePatch_maps_compact_into_open (p i).chart hf (p i).smooth.contDiff
      hinner (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold := eventually_affinePatch_injective_derivative (p i).chart hf (p i).smooth.contDiff
    (p i).compact hinner hK hinj
  let Q : (Plane → N) → Prop := fun g => (∀ j, (p j).Compatible g) ∧
    ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g x)
  have hQ : ∀ᶠ A : G × G in 𝓝 0, Q (affinePatch (p i).chart f (p i).cutoff A) :=
    hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, ⟨Hrel⟩, hemb, hplateau⟩ :=
    exists_affine_embedding_patch_with_property (p i).chart f hf
      (p i).smooth.contDiff (p i).outer_smooth.contDiff (p i).compact
      (hcompatible i) (p i).nested hdim Q hQ hL hLsub
  refine ⟨g, hg, hc, ?_, hemb, ?_⟩
  · exact ⟨{ Hrel.toHomotopy with prop' := fun t x hx => Hrel.eq_fst t (hfixed x hx) }⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hKnew x hx
    · exact hplateau x (hLsub hx)

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
