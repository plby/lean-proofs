import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyPatches
import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyFilling
import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyChart
import Wikipedia.HopfProblem.DegreeCollapseCompatibleChartRestriction
import Wikipedia.HopfProblem.DegreeCollapseSelectiveTransversality
import Wikipedia.HopfProblem.DegreeCollapseSelectedFiberPairRemoval

/-!
# Actual self-transverse cancellation from the original clean source arcs

Construct the patch closures, shared corners, strips, embedded filling,
compatible chart, whole-bigon isolation, and selective endpoint. The only
geometric inputs here are the original clean disjoint source arcs and the
two selected two-preimage fibers with opposite native signs. The endpoint
removes exactly the original pairs over those values and stays a smooth
self-transverse immersion homotopic to the original map.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare WhitneyPairModel
open OrbitPair.DeterminantSignCover

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M] [SimplyConnectedSpace M]
  (oN : Orientation (tangentBundleCore (𝓡 3) (Sphere 3)))
  (oM : Orientation (tangentBundleCore (𝓡 6) M))
  (J : Sheet ≃L[ℝ] Vector 3) (K : (Vector 3 × Vector 3) ≃L[ℝ] Vector 6)

include J

theorem exists_cancellation_from_clean_arc_pair (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} {u₀ u₁ v₀ v₁ : Vector 3}
    (a : CleanJoiningArc f x₀ x₁ u₀ u₁) (b : CleanJoiningArc f y₀ y₁ v₀ v₁)
    (hab : Disjoint (a.map '' Icc (0 : ℝ) 1) (b.map '' Icc (0 : ℝ) 1))
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁)
    (hsign : ImmersedCorner.intersectionSign oN oM K f x₀ y₀ ≠
      ImmersedCorner.intersectionSign oN oM K f x₁ y₁) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      SphereSelfIntersections.pairs g = SphereSelfIntersections.pairs f \
        {p : Sphere 3 × Sphere 3 | f p.1 ∈ ({f x₀, f x₁} : Set M)} := by
  obtain ⟨U, V, O, hU, hV, hO, hAU, hBV, hUc, hVc, hUV, hiU, _, heU, heV,
      hAOBO, hpreO, _⟩ := exists_clean_source_patches hf hi
    (SphereSelfIntersections.finite_pairs hf ht hi) a b hab hc₀ hc₁ hfib₀ hfib₁
  have hAO : MapsTo (f ∘ a.map) (Icc (0 : ℝ) 1) O :=
    fun t htI => hAOBO ⟨a.map t, Or.inl ⟨t, htI, rfl⟩, rfl⟩
  have hBO : MapsTo (f ∘ b.map) (Icc (0 : ℝ) 1) O :=
    fun t htI => hAOBO ⟨b.map t, Or.inr ⟨t, htI, rfl⟩, rfl⟩
  obtain ⟨c₀, c₁, k, l, ⟨d⟩, ⟨e⟩, _, _, hfill⟩ :=
    exists_native_branch_tubular_bigon hf hi ht a b hc₀ hc₁ hu₀ hu₁ hv₀ hv₁
      hU hV hAU hBV hUV hUc hVc heU heV hO hAO hBO hpreO
  obtain ⟨tube, havoid⟩ := hfill 1 (by norm_num)
  have hα : MapsTo a.map (Icc (0 : ℝ) 1) (interior (closure U)) := by
    intro t htI
    exact hU.subset_interior_closure (hAU ⟨t, htI, rfl⟩)
  have hβ : MapsTo b.map (Icc (0 : ℝ) 1) (interior (closure V)) := by
    intro t htI
    exact hV.subset_interior_closure (hBV ⟨t, htI, rfl⟩)
  have hcornerTrans : ∀ t : ℝ, t = 0 ∨ t = 1 → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f (b.map t)).coprod (mfderiv (𝓡 3) (𝓡 6) f (a.map t))) := by
    intro t htend
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases htend with rfl | rfl <;> simp
    have hne : b.map t ≠ a.map t := by
      intro heq
      exact (Set.disjoint_left.mp hab)
        ⟨t, htI, rfl⟩ ⟨t, htI, heq⟩
    apply ht _ _ hne
    rcases htend with rfl | rfl
    · simpa only [a.start, b.start] using hc₀.symm
    · simpa only [a.finish, b.finish] using hc₁.symm
  have hsign' : ImmersedCorner.intersectionSign oN oM K f (a.map 0) (b.map 0) ≠
      ImmersedCorner.intersectionSign oN oM K f (a.map 1) (b.map 1) := by
    simpa only [a.start, b.start, a.finish, b.finish] using hsign
  obtain ⟨c⟩ := ImmersedCorner.nonempty_compatibleChart_of_opposite_native_signs
    oN oM J K tube d e hf hi hUc hVc hα hβ hcornerTrans hsign'
  obtain ⟨c', hpre⟩ := exists_branch_isolated_compatibleChart c f.continuous
    hU hV hAO hBO hpreO havoid
  obtain ⟨g, hg, hrel, hgi, hgt, hpairs⟩ :=
    SelectiveSheet.exists_selfTransverse_selective_cancellation c' hf hi ht
      (hiU.mono subset_closure) hU hV hUc hUV hpre
  have hx₀ : x₀ ∈ U := hAU ⟨0, by simp, a.start⟩
  have hx₁ : x₁ ∈ U := hAU ⟨1, by simp, a.finish⟩
  have hy₀ : y₀ ∉ U := fun hy => (Set.disjoint_left.mp hUV) (subset_closure hy)
    (subset_closure (hBV ⟨0, by simp, b.start⟩))
  have hy₁ : y₁ ∉ U := fun hy => (Set.disjoint_left.mp hUV) (subset_closure hy)
    (subset_closure (hBV ⟨1, by simp, b.finish⟩))
  refine ⟨g, hg, hrel, hgi, hgt, ?_⟩
  change {p : Sphere 3 × Sphere 3 | p.1 ≠ p.2 ∧ g p.1 = g p.2} = _
  rw [hpairs]
  simp only [Function.comp_apply, a.start, a.finish]
  exact SelectiveSheet.selective_pair_removal_eq_value_removal hx₀ hx₁ hy₀ hy₁ hfib₀ hfib₁

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
