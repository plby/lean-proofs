import Wikipedia.HopfProblem.DegreeCollapseImmersedBigonBoundary
import Wikipedia.HopfProblem.DegreeCollapseImmersedTubularBigon

/-!
# Actual branch bigons with embedded fillings avoiding the whole immersion

Combine the original immersion's native branch charts, shared corner maps,
and full strip germs with simple connectivity and relative general position.
The given ambient open set sees only the two selected source patches.
Consequently the constructed bigon interior avoids the entire original
immersed sphere, not just the two selected patch images. Both strip normal
data are retained for the still separate Whitney framing problem.
-/

noncomputable section

open Set Function Module Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare WhitneyPairModel

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M] [SimplyConnectedSpace M]
  {f : Sphere 3 → M}

theorem exists_native_branch_tubular_bigon
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} {u₀ u₁ v₀ v₁ : Vector 3}
    (a : CleanJoiningArc f x₀ x₁ u₀ u₁) (b : CleanJoiningArc f y₀ y₁ v₀ v₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    {U V : Set (Sphere 3)} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : a.map '' Icc (0 : ℝ) 1 ⊆ U) (hBV : b.map '' Icc (0 : ℝ) 1 ⊆ V)
    (hUV : Disjoint (closure U) (closure V))
    (hUc : IsCompact (closure U)) (hVc : IsCompact (closure V))
    (heU : IsClosedEmbedding (fun x : closure U => f x))
    (heV : IsClosedEmbedding (fun x : closure V => f x))
    {O : Set M} (hO : IsOpen O)
    (hAO : MapsTo (f ∘ a.map) (Icc (0 : ℝ) 1) O)
    (hBO : MapsTo (f ∘ b.map) (Icc (0 : ℝ) 1) O)
    (hpre : f ⁻¹' O ⊆ U ∪ V) :
    ∃ c₀ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
        (fun t => f (NativeParametrization.centered (D := Vector 3) x₀ (t • u₀)))
        (fun t => f (NativeParametrization.centered (D := Vector 3) y₀ (t • v₀))),
      ∃ c₁ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
          (fun t => f (NativeParametrization.centered (D := Vector 3) x₁ (t • u₁)))
          (fun t => f (NativeParametrization.centered (D := Vector 3) y₁ (t • v₁))),
        ∃ k : CleanStripPatch (E := Vector 6) (f '' closure U) (f '' closure V)
            (f ∘ a.map) c₀.map c₁.map,
          ∃ l : CleanStripPatch (E := Vector 6) (f '' closure V) (f '' closure U)
              (f ∘ b.map) c₀.swap.map c₁.swap.map,
            Nonempty (StripNormalData (Vector 2) (Vector 3) (E := Vector 6)
              (f '' closure U) k.map) ∧
            Nonempty (StripNormalData (Vector 2) (Vector 3) (E := Vector 6)
              (f '' closure V) l.map) ∧ MapsTo k.map k.domain O ∧ MapsTo l.map l.domain O ∧
            ∀ h : ℝ, 0 < h →
              ∃ d : TubularBigon (E := Vector 6) (f '' closure U) (f '' closure V)
                  (f ∘ a.map) (f ∘ b.map) k.map l.map h,
                ∀ p ∈ interior (bigon h), d.map p ∉ range f := by
  obtain ⟨c₀, c₁, k, l, hnK, hnL, hkO, hlO, _, hboundary⟩ :=
    exists_native_branch_bigon_boundary hf hi ht a b hc₀ hc₁ hu₀ hu₁ hv₀ hv₁
      hU hV hAU hBV hUV hUc hVc heU heV hO hAO hBO
  have hcover : range f ∩ O ⊆ (f '' closure U) ∪ (f '' closure V) := by
    rintro z ⟨⟨x, rfl⟩, hxO⟩
    rcases hpre hxO with hxU | hxV
    · exact Or.inl ⟨x, subset_closure hxU, rfl⟩
    · exact Or.inr ⟨x, subset_closure hxV, rfl⟩
  refine ⟨c₀, c₁, k, l, hnK, hnL, hkO, hlO, ?_⟩
  intro h hh
  obtain ⟨d⟩ := (hboundary h hh).1
  exact exists_tubularBigon_of_simplyConnected ⟨f, hf.continuous⟩ hf (by simp) (by simp)
    d hO hAO hBO hcover (image_subset_range _ _) (image_subset_range _ _)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
