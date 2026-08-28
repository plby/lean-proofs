import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyPatches
import Wikipedia.HopfProblem.DegreeCollapseImmersedArcAmbientChart
import Wikipedia.HopfProblem.DegreeCollapsePatchCrossingChart

/-!
# Actual ambient arc charts and shared corners for immersed-sphere branches

Specialize the patch constructions to the original immersed three-sphere.
All charts use the original target atlas and recognize the full compact
branch images. Both corner maps retain the native endpoint parametrizations
already present in the constructed source arcs.
-/

noncomputable section

open Set Function Module Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]
  {f : Sphere 3 → M}

theorem CleanJoiningArc.exists_ambient_patch_chart
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    {x y : Sphere 3} {u v : Vector 3} (a : CleanJoiningArc f x y u v)
    {U : Set (Sphere 3)} (hU : IsOpen U)
    (hAU : a.map '' Icc (0 : ℝ) 1 ⊆ U)
    (hemb : IsClosedEmbedding (fun x : closure U => f x))
    {O : Set M} (hO : IsOpen O) (hAO : MapsTo (f ∘ a.map) (Icc (0 : ℝ) 1) O) :
    ∃ Φ : PartialDiffeomorph
        𝓘(ℝ, StripCoordinates.Space (Vector 2) (Vector 3)) (𝓡 6)
        (StripCoordinates.Space (Vector 2) (Vector 3)) M ∞,
      MapsTo StripCoordinates.center (Icc (0 : ℝ) 1) Φ.source ∧ Φ.target ⊆ O ∧
      (∀ t, StripCoordinates.center t ∈ Φ.source → Φ (StripCoordinates.center t) = f (a.map t)) ∧
      (∀ q ∈ Φ.source, Φ q ∈ f '' closure U ↔ q.2 = 0) := by
  have hia : InjOn a.map (Icc (0 : ℝ) 1) := by
    intro t ht s hs he
    exact congrArg Subtype.val (a.embedded.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) he)
  exact exists_clean_ambient_chart_along_patch_arc hf hemb.isEmbedding hi
    a.smooth hia a.immersed hU subset_closure (fun t ht => hAU ⟨t, ht, rfl⟩)
    2 3 (by simp) (by simp) hO hAO

theorem exists_native_branch_corner_pair
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} {u₀ u₁ v₀ v₁ : Vector 3}
    (a : CleanJoiningArc f x₀ x₁ u₀ u₁) (b : CleanJoiningArc f y₀ y₁ v₀ v₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    {U V : Set (Sphere 3)} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : a.map '' Icc (0 : ℝ) 1 ⊆ U) (hBV : b.map '' Icc (0 : ℝ) 1 ⊆ V)
    (hUV : Disjoint (closure U) (closure V))
    (heU : IsClosedEmbedding (fun x : closure U => f x))
    (heV : IsClosedEmbedding (fun x : closure V => f x))
    {O : Set M} (hO : IsOpen O) (hAO : MapsTo (f ∘ a.map) (Icc (0 : ℝ) 1) O) :
    ∃ c₀ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
        (fun t => f (NativeParametrization.centered (D := Vector 3) x₀ (t • u₀)))
        (fun t => f (NativeParametrization.centered (D := Vector 3) y₀ (t • v₀))),
      ∃ c₁ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
          (fun t => f (NativeParametrization.centered (D := Vector 3) x₁ (t • u₁)))
          (fun t => f (NativeParametrization.centered (D := Vector 3) y₁ (t • v₁))),
        MapsTo c₀.map c₀.domain O ∧ MapsTo c₁.map c₁.domain O := by
  have hx₀ : x₀ ∈ U := hAU ⟨0, by simp, a.start⟩
  have hx₁ : x₁ ∈ U := hAU ⟨1, by simp, a.finish⟩
  have hy₀ : y₀ ∈ V := hBV ⟨0, by simp, b.start⟩
  have hy₁ : y₁ ∈ V := hBV ⟨1, by simp, b.finish⟩
  have hne₀ : x₀ ≠ y₀ := fun he => (Set.disjoint_left.mp hUV)
    (subset_closure hx₀) (by rw [he]; exact subset_closure hy₀)
  have hne₁ : x₁ ≠ y₁ := fun he => (Set.disjoint_left.mp hUV)
    (subset_closure hx₁) (by rw [he]; exact subset_closure hy₁)
  have hx₀O : f x₀ ∈ O := by
    have h := hAO (by simp : (0 : ℝ) ∈ Icc 0 1)
    simpa only [Function.comp_apply, a.start] using h
  have hx₁O : f x₁ ∈ O := by
    have h := hAO (by simp : (1 : ℝ) ∈ Icc 0 1)
    simpa only [Function.comp_apply, a.finish] using h
  obtain ⟨c₀, hc₀O⟩ := exists_clean_corner_of_source_patches hf hf heU.isEmbedding heV.isEmbedding
    hU hV subset_closure subset_closure hx₀ hy₀ hc₀.symm
      (by simp) (ht x₀ y₀ hne₀ hc₀) hu₀ hv₀ hO hx₀O
  obtain ⟨c₁, hc₁O⟩ := exists_clean_corner_of_source_patches hf hf heU.isEmbedding heV.isEmbedding
    hU hV subset_closure subset_closure hx₁ hy₁ hc₁.symm
      (by simp) (ht x₁ y₁ hne₁ hc₁) hu₁ hv₁ hO hx₁O
  exact ⟨c₀, c₁, hc₀O, hc₁O⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
