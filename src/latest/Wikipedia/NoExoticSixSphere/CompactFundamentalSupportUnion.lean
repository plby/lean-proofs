import Wikipedia.NoExoticSixSphere.CompactFundamentalSupport
import Wikipedia.NoExoticSixSphere.SupportedUnionInjectivity

/-!
# Closed-union closure of proved compact fundamental supports

Above-dimensional vanishing on the intersection supplies injectivity of
the original union restriction pair. Local detection on the intersection
proves actual agreement of the two fundamental classes there. The genuine
Mayer–Vietoris gluing theorem then constructs the class on the union.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- The three actual homological properties are preserved by this compact union. -/
theorem CompactFundamentalSupport.union {K L : Set M}
    (hK : CompactFundamentalSupport (E := E) n K)
    (hL : CompactFundamentalSupport (E := E) n L)
    (hI : CompactFundamentalSupport (E := E) n (K ∩ L)) :
    CompactFundamentalSupport (E := E) n (K ∪ L) where
  compact := hK.compact.union hL.compact
  above k hk := by
    let := hK.above k hk
    let := hL.above k hk
    let := hI.above (k + 1) (by omega)
    exact homology_union_subsingleton 2 (by decide) K L hK.compact.isClosed hL.compact.isClosed k
  detected a b hab := by
    let := hI.above ((n + 3) + 1) (by omega)
    apply eq_of_restrict_union_eq 2 (by decide) K L
      hK.compact.isClosed hL.compact.isClosed (n + 3) a b
    · apply hK.detected
      intro x hx
      have ha := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ (ZMod 2))
        (Set.subset_union_left : K ⊆ K ∪ L) x hx (n + 3)) a
      have hb := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ (ZMod 2))
        (Set.subset_union_left : K ⊆ K ∪ L) x hx (n + 3)) b
      exact ha.trans ((hab x (Or.inl hx)).trans hb.symm)
    · apply hL.detected
      intro x hx
      have ha := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ (ZMod 2))
        (Set.subset_union_right : L ⊆ K ∪ L) x hx (n + 3)) a
      have hb := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ (ZMod 2))
        (Set.subset_union_right : L ⊆ K ∪ L) x hx (n + 3)) b
      exact ha.trans ((hab x (Or.inr hx)).trans hb.symm)
  fundamental := by
    obtain ⟨a, ha⟩ := hK.fundamental
    obtain ⟨b, hb⟩ := hL.fundamental
    have haI := IsFundamentalOn.restrict (E := E) n (Set.inter_subset_left : K ∩ L ⊆ K) ha
    have hbI := IsFundamentalOn.restrict (E := E) n (Set.inter_subset_right : K ∩ L ⊆ L) hb
    have hab := hI.detected _ _ (fun x hx => (haI x hx).trans (hbI x hx).symm)
    obtain ⟨c, hc, _, _⟩ := exists_fundamental_union n K L hK.compact.isClosed hL.compact.isClosed
      a b ha hb hab
    exact ⟨c, hc⟩

end NoExoticSixSphere.SupportedRelativeHomology
