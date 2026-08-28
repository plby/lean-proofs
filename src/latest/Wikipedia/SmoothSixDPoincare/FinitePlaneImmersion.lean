import Wikipedia.SmoothSixDPoincare.ImmersionPatchStep

/-!
# Finite relative immersion improvement on compact planar sets

Each affine patch retains the previously treated compact union and every
future target-chart constraint. The relative homotopies concatenate. Only
injectivity of the derivative, not global injectivity of the map, is retained
across the induction.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open PlaneImmersion (Plane)
open ManifoldSmoothing (MapSmoothingPatch)

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- Improve finitely many compact plateaus, preserving an original compact immersive set. -/
theorem exists_finite_patch_immersion {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, Plane) J (X := Plane) (N := N))
    (L : ι → Set Plane) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau)
    (f : C(Plane, N)) (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f)
    (hcompatible : ∀ i, (p i).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set Plane} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J f x))
    (hfixed : ∀ i x, x ∈ C → (p i).cutoff x = 0) (s : Finset ι) :
    ∃ g : C(Plane, N), ContMDiff 𝓘(ℝ, Plane) J ∞ g ∧
      (∀ i, (p i).Compatible g) ∧ f.HomotopicRel g C ∧
      ∀ x ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, HomotopicRel.refl f, ?_⟩
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty] using hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) :=
      hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, -, hinj₂⟩ := exists_immersion_patch_step p i g₁ hg₁ hc₁
      hdim hKold (hL i) hinj₁ (hLsub i) (hfixed i)
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply hinj₂ x
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hxj
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, hjs, hxj⟩))

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
