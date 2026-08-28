import Wikipedia.NoExoticSixSphere.ConvexLocalEvaluation
import Wikipedia.NoExoticSixSphere.LocalCoefficientVanishing
import Wikipedia.NoExoticSixSphere.EmptySupportedHomology
import Wikipedia.NoExoticSixSphere.SupportedFundamentalClass

/-!
# Compact supports with proved local detection and a fundamental class

This predicate records three actual relative-homology conclusions needed
for the local-to-global argument. It is proved here for the empty support
and every compact convex Euclidean support, including those with empty
interior. No conclusion for arbitrary compact supports is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- These are properties of the original supported relative homology groups and evaluation maps. -/
structure CompactFundamentalSupport (K : Set M) : Prop where
  compact : IsCompact K
  above : ∀ k : ℕ, n + 3 < k → Subsingleton (Homology (ModuleCat.of ℤ (ZMod 2)) K k)
  detected : ∀ a b : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3),
    (∀ (x : M) (hx : x ∈ K), evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3) a =
      evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3) b) → a = b
  fundamental : ∃ c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3),
    IsFundamentalOn (E := E) n K c

theorem CompactFundamentalSupport.empty : CompactFundamentalSupport (E := E) n (∅ : Set M) where
  compact := isCompact_empty
  above k _ := homology_empty_subsingleton (ModuleCat.of ℤ (ZMod 2)) k
  detected a b _ := (homology_empty_subsingleton (ModuleCat.of ℤ (ZMod 2)) (n + 3)).elim a b
  fundamental := ⟨0, fun _ hx => False.elim hx⟩

/-- Detection supplies uniqueness of a class with the prescribed local values. -/
theorem CompactFundamentalSupport.existsUnique {K : Set M}
    (hK : CompactFundamentalSupport (E := E) n K) :
    ∃! c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3), IsFundamentalOn (E := E) n K c := by
  obtain ⟨c, hc⟩ := hK.fundamental
  exact ⟨c, hc, fun d hd => hK.detected d c (fun x hx => (hd x hx).trans (hc x hx).symm)⟩

/-- A compact convex Euclidean support has all three properties by actual local evaluation. -/
theorem compactConvex_fundamentalSupport (K : Set E) (hK : IsCompact K) (hC : Convex ℝ K) :
    CompactFundamentalSupport (E := E) n K := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx⟩ := hne
    refine { compact := hK, above := ?_, detected := ?_, fundamental := ?_ }
    · intro k hk
      let := LocalCoefficientVanishing.above_subsingleton (E := E) n 2 (by decide) x k hk
      exact (ConvexLocalHomology.evaluateEquiv 2 (by decide) K hK hC x hx k).injective.subsingleton
    · intro a b he
      exact (ConvexLocalHomology.evaluate_bijective 2 (by decide) K hK hC x hx (n + 3)).injective
        (he x hx)
    · apply ExistsUnique.exists
      exact existsUnique_fundamentalClass_of_evaluate_bijective (E := E) n K ⟨x, hx⟩
        (fun y hy => ConvexLocalHomology.evaluate_bijective 2 (by decide) K hK hC y hy (n + 3))
  · have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst K
    exact CompactFundamentalSupport.empty n

end NoExoticSixSphere.SupportedRelativeHomology
