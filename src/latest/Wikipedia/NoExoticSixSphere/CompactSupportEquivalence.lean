import Wikipedia.NoExoticSixSphere.CompactFundamentalSupport

/-!
# Transport of proved compact-support properties

An actual bijection of support points, actual relative homology
equivalences, and commuting local-evaluation equivalences transport the
support properties. Every local mod-two equivalence preserves the
constructed canonical class, by the proved uniqueness of its nonzero value.
No global class or detection property on the source is assumed.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace E M] [ChartedSpace E N]

/-- Commuting actual global and local equivalences transport all compact-support properties. -/
theorem CompactFundamentalSupport.of_evaluation_equivalences {K : Set M} {L : Set N}
    (hK : IsCompact K) (points : K ≃ L)
    (F : ∀ k : ℕ, Homology (ModuleCat.of ℤ (ZMod 2)) K k ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ (ZMod 2)) L k)
    (G : ∀ x : K, RelativeCoefficients.ModHomology 2 ({(x : M)}ᶜ : Set M) (n + 3) ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology 2 ({(points x : N)}ᶜ : Set N) (n + 3))
    (hsquare : ∀ (x : K) (a : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3)),
      evaluate (ModuleCat.of ℤ (ZMod 2)) L (points x) (points x).property (n + 3) (F (n + 3) a) =
        G x (evaluate (ModuleCat.of ℤ (ZMod 2)) K x x.property (n + 3) a))
    (hL : CompactFundamentalSupport (E := E) n L) :
    CompactFundamentalSupport (E := E) n K where
  compact := hK
  above k hk := by
    let := hL.above k hk
    exact (F k).injective.subsingleton
  detected a b hab := by
    apply (F (n + 3)).injective
    have hall : ∀ y : L,
        evaluate (ModuleCat.of ℤ (ZMod 2)) L y y.property (n + 3) (F (n + 3) a) =
          evaluate (ModuleCat.of ℤ (ZMod 2)) L y y.property (n + 3) (F (n + 3) b) := by
      intro y
      obtain ⟨x, rfl⟩ := points.surjective y
      exact (hsquare x a).trans
        ((congrArg (G x) (hab x x.property)).trans (hsquare x b).symm)
    apply hL.detected
    intro y hy
    exact hall ⟨y, hy⟩
  fundamental := by
    obtain ⟨c, hc⟩ := hL.fundamental
    refine ⟨(F (n + 3)).symm c, ?_⟩
    intro x hx
    let y : K := ⟨x, hx⟩
    apply (G y).injective
    have he := hsquare y ((F (n + 3)).symm c)
    rw [LinearEquiv.apply_symm_apply] at he
    have hclass := ModTwoLocalClass.injective_map_manifoldClass (E := E) n
      x (points y : N) (G y).toLinearMap (G y).injective
    exact (he.symm.trans (hc (points y) (points y).property)).trans hclass.symm

end NoExoticSixSphere.SupportedRelativeHomology
