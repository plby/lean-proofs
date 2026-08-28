import Wikipedia.NoExoticSixSphere.RelativeMayerVietoris
import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology

/-!
# Gluing actual relative classes supported on two closed subsets

The relative Mayer–Vietoris sequence of the open complements proves that
two supported classes with equal restrictions to the intersection lift to
a class supported on the union. The lift has the original restriction
maps. When both classes are fundamental, the lift is fundamental on the
whole union. Agreement on the intersection is an explicit hypothesis;
it is not inferred merely from equality of all pointwise local values.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M]

/-- Matching supported relative classes glue along the actual two closed supports. -/
theorem exists_lift_union (p : ℕ) (hp : p ≠ 0) (K L : Set M)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    (a : Homology (ModuleCat.of ℤ (ZMod p)) K n)
    (b : Homology (ModuleCat.of ℤ (ZMod p)) L n)
    (hab : restrict (ModuleCat.of ℤ (ZMod p)) (Set.inter_subset_left : K ∩ L ⊆ K) n a =
      restrict (ModuleCat.of ℤ (ZMod p)) (Set.inter_subset_right : K ∩ L ⊆ L) n b) :
    ∃ c : Homology (ModuleCat.of ℤ (ZMod p)) (K ∪ L) n,
      restrict (ModuleCat.of ℤ (ZMod p)) (Set.subset_union_left : K ⊆ K ∪ L) n c = a ∧
        restrict (ModuleCat.of ℤ (ZMod p)) (Set.subset_union_right : L ⊆ K ∪ L) n c = b := by
  have hgen (I W : Set M) (hI : I = Kᶜ ∩ Lᶜ) (hW : W = Kᶜ ∪ Lᶜ)
      (hIL : I ⊆ Kᶜ) (hIR : I ⊆ Lᶜ) (hLW : Kᶜ ⊆ W) (hRW : Lᶜ ⊆ W)
      (he : homologyLinearMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ (ZMod p)) hLW) n a =
        homologyLinearMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ (ZMod p)) hRW) n b) :
      ∃ c : RelativeCoefficients.ModHomology p I n,
        homologyLinearMap
            (RelativeCoefficients.subsetMap (ModuleCat.of ℤ (ZMod p)) hIL) n c = a ∧
          homologyLinearMap
            (RelativeCoefficients.subsetMap (ModuleCat.of ℤ (ZMod p)) hIR) n c = b := by
    subst I
    subst W
    exact RelativeMayerVietoris.exists_lift_of_agree Kᶜ Lᶜ p hp
      hK.isOpen_compl hL.isOpen_compl n a b he
  exact hgen (K ∪ L)ᶜ (K ∩ L)ᶜ (Set.compl_union K L) (Set.compl_inter K L)
    (fun _ hx hy => hx (Or.inl hy)) (fun _ hx hy => hx (Or.inr hy))
    (fun _ hx hy => hx hy.1) (fun _ hx hy => hx hy.2) hab

end NoExoticSixSphere.SupportedRelativeHomology

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace E M]

/-- Matching actual fundamental classes glue to a fundamental class on the closed union. -/
theorem exists_fundamental_union (K L : Set M) (hK : IsClosed K) (hL : IsClosed L)
    (a : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3))
    (b : Homology (ModuleCat.of ℤ (ZMod 2)) L (n + 3))
    (ha : IsFundamentalOn (E := E) n K a) (hb : IsFundamentalOn (E := E) n L b)
    (hab : restrict (ModuleCat.of ℤ (ZMod 2)) (Set.inter_subset_left : K ∩ L ⊆ K) (n + 3) a =
      restrict (ModuleCat.of ℤ (ZMod 2)) (Set.inter_subset_right : K ∩ L ⊆ L) (n + 3) b) :
    ∃ c : Homology (ModuleCat.of ℤ (ZMod 2)) (K ∪ L) (n + 3),
      IsFundamentalOn (E := E) n (K ∪ L) c ∧
        restrict (ModuleCat.of ℤ (ZMod 2)) (Set.subset_union_left : K ⊆ K ∪ L) (n + 3) c = a ∧
        restrict (ModuleCat.of ℤ (ZMod 2)) (Set.subset_union_right : L ⊆ K ∪ L) (n + 3) c = b := by
  obtain ⟨c, hcK, hcL⟩ := exists_lift_union 2 (by decide) K L hK hL (n + 3) a b hab
  refine ⟨c, ?_, hcK, hcL⟩
  intro x hx
  rcases hx with hx | hx
  · have he := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ (ZMod 2))
      (Set.subset_union_left : K ⊆ K ∪ L) x hx (n + 3)) c
    change evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3)
      (restrict (ModuleCat.of ℤ (ZMod 2)) Set.subset_union_left (n + 3) c) = _ at he
    rw [hcK] at he
    exact he.symm.trans (ha x hx)
  · have he := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ (ZMod 2))
      (Set.subset_union_right : L ⊆ K ∪ L) x hx (n + 3)) c
    change evaluate (ModuleCat.of ℤ (ZMod 2)) L x hx (n + 3)
      (restrict (ModuleCat.of ℤ (ZMod 2)) Set.subset_union_right (n + 3) c) = _ at he
    rw [hcL] at he
    exact he.symm.trans (hb x hx)

end NoExoticSixSphere.SupportedRelativeHomology
