import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeMayerVietoris
import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology

/-!
# Integral gluing and detection on closed support unions

Apply the genuine integral relative Mayer--Vietoris sequence to the open
complements. Matching original classes lift to the actual union. Vanishing
one degree higher on the intersection makes the original restriction pair
injective. Pointwise agreement is not substituted for intersection agreement.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportedUnion

open SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M]

theorem exists_lift_union (K L : Set M) (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    (a : Homology (ModuleCat.of ℤ ℤ) K n) (b : Homology (ModuleCat.of ℤ ℤ) L n)
    (hab : restrict (ModuleCat.of ℤ ℤ) (Set.inter_subset_left : K ∩ L ⊆ K) n a =
      restrict (ModuleCat.of ℤ ℤ) (Set.inter_subset_right : K ∩ L ⊆ L) n b) :
    ∃ c : Homology (ModuleCat.of ℤ ℤ) (K ∪ L) n,
      restrict (ModuleCat.of ℤ ℤ) (Set.subset_union_left : K ⊆ K ∪ L) n c = a ∧
        restrict (ModuleCat.of ℤ ℤ) (Set.subset_union_right : L ⊆ K ∪ L) n c = b := by
  have hgen (I W : Set M) (hI : I = Kᶜ ∩ Lᶜ) (hW : W = Kᶜ ∪ Lᶜ)
      (hIL : I ⊆ Kᶜ) (hIR : I ⊆ Lᶜ) (hLW : Kᶜ ⊆ W) (hRW : Lᶜ ⊆ W)
      (he : homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hLW) n a =
        homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hRW) n b) :
      ∃ c : (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) I).homology n,
        homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hIL) n c = a ∧
          homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hIR) n c = b := by
    subst I
    subst W
    exact IntegralRelativeMayerVietoris.exists_lift_of_agree Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl n a b he
  exact hgen (K ∪ L)ᶜ (K ∩ L)ᶜ (Set.compl_union K L) (Set.compl_inter K L)
    (fun _ hx hy => hx (Or.inl hy)) (fun _ hx hy => hx (Or.inr hy))
    (fun _ hx hy => hx hy.1) (fun _ hx hy => hx hy.2) hab

theorem eq_of_restrict_union_eq (K L : Set M) (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    [Subsingleton (Homology (ModuleCat.of ℤ ℤ) (K ∩ L) (n + 1))]
    (a b : Homology (ModuleCat.of ℤ ℤ) (K ∪ L) n)
    (hleft : restrict (ModuleCat.of ℤ ℤ) (Set.subset_union_left : K ⊆ K ∪ L) n a =
      restrict (ModuleCat.of ℤ ℤ) (Set.subset_union_left : K ⊆ K ∪ L) n b)
    (hright : restrict (ModuleCat.of ℤ ℤ) (Set.subset_union_right : L ⊆ K ∪ L) n a =
      restrict (ModuleCat.of ℤ ℤ) (Set.subset_union_right : L ⊆ K ∪ L) n b) : a = b := by
  have hgen (I W : Set M) (hI : I = Kᶜ ∩ Lᶜ) (hW : W = Kᶜ ∪ Lᶜ)
      (hIL : I ⊆ Kᶜ) (hIR : I ⊆ Lᶜ)
      [Subsingleton ((RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) W).homology (n + 1))]
      (c d : (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) I).homology n)
      (hl : homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hIL) n c =
        homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hIL) n d)
      (hr : homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hIR) n c =
        homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hIR) n d) :
      c = d := by
    subst I
    subst W
    apply IntegralRelativeMayerVietoris.firstMap_injective_of_subsingleton_union Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl n
    rw [RelativeMayerVietoris.firstMap_apply, RelativeMayerVietoris.firstMap_apply, hl, hr]
  exact hgen (K ∪ L)ᶜ (K ∩ L)ᶜ (Set.compl_union K L) (Set.compl_inter K L)
    (fun _ hx hy => hx (Or.inl hy)) (fun _ hx hy => hx (Or.inr hy)) a b hleft hright

theorem homology_union_subsingleton (K L : Set M) (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    [Subsingleton (Homology (ModuleCat.of ℤ ℤ) K n)]
    [Subsingleton (Homology (ModuleCat.of ℤ ℤ) L n)]
    [Subsingleton (Homology (ModuleCat.of ℤ ℤ) (K ∩ L) (n + 1))] :
    Subsingleton (Homology (ModuleCat.of ℤ ℤ) (K ∪ L) n) :=
  ⟨fun a b => eq_of_restrict_union_eq K L hK hL n a b
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportedUnion
