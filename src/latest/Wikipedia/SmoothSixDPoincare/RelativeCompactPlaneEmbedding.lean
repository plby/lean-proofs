import Wikipedia.SmoothSixDPoincare.CompactPlaneImmersion
import Wikipedia.SmoothSixDPoincare.CompactImmersionEmbedding

/-!
# Relative smooth embeddings of compact planar regions

At the fixed points the original map must already be injective and have
injective native derivatives. Openness and compactness give an immersive
neighborhood there. The remaining compact region is first made immersive,
then all distinct collisions are removed. Every construction fixes the
prescribed closed set through an actual relative homotopy.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open PlaneImmersion (Plane)

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- A smooth planar map can be made into an embedded immersion on a compact region, relative
to a closed set where it is already injective with injective native derivatives. -/
theorem exists_relative_compact_embedding (f : C(Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set Plane} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, Plane) J f x)) :
    ∃ g : C(Plane, N), ContMDiff 𝓘(ℝ, Plane) J ∞ g ∧ f.HomotopicRel g C ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g x) := by
  let U : Set Plane := {x | Function.Injective (mfderiv 𝓘(ℝ, Plane) J f x)}
  have hU : IsOpen U := isOpen_injective_derivative hf
  have hCU : K ∩ C ⊆ U := fun x hx => hderiv x hx
  obtain ⟨D, hD, hCD, hDU⟩ := exists_compact_between (hK.inter_right hC) hU hCU
  let L := K \ interior D
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hdis : Disjoint L C := disjoint_left.mpr (fun _ hx hxC => hx.2 (hCD ⟨hx.1, hxC⟩))
  obtain ⟨g₁, hg₁, hhom₁, hinj₁⟩ := exists_immersion_on_compact_rel f hf hdim hD hL
    (fun x hx => hDU hx) hC hdis
  have hKinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g₁ x) := by
    intro x hx
    apply hinj₁ x
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr ⟨hx, fun hi => hxD (interior_subset hi)⟩
  have hfixed₁ : InjOn g₁ (K ∩ C) := by
    intro x hx y hy hxy
    apply hfixed hx hy
    rw [hhom₁.fst_eq_snd hx.2, hhom₁.fst_eq_snd hy.2]
    exact hxy
  have hd : 2 * Module.finrank ℝ Plane < Module.finrank ℝ G := by
    simp only [Plane, Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨g₂, hg₂, hhom₂, hemb, hinj₂⟩ :=
    exists_compact_embedding_of_immersion g₁ hg₁ hd hK hKinj hC hfixed₁
  exact ⟨g₂, hg₂, hhom₁.trans hhom₂, hemb, hinj₂⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
