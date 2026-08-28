import Wikipedia.NoExoticSixSphere.SupportedMayerVietoris

/-!
# Detection on a closed union from the actual Mayer–Vietoris sequence

Vanishing one degree higher on the intersection makes the pair of original
restriction maps injective. In particular, vanishing on both pieces and
one degree higher on their intersection implies vanishing on the union.
These are consequences of the proved connecting-map exactness.
-/

noncomputable section

namespace NoExoticSixSphere.RelativeMayerVietoris

open RelativeCoefficients

variable {M : Type} [TopologicalSpace M]

theorem firstMap_injective_of_subsingleton_union (p : ℕ) (hp : p ≠ 0) (U V : Set M)
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) [Subsingleton (ModHomology p (U ∪ V) (n + 1))] :
    Function.Injective (firstMap (ModuleCat.of ℤ (ZMod p)) U V n) := by
  have hd : connecting U V p hp hU hV n = 0 := Subsingleton.elim _ _
  apply LinearMap.ker_eq_bot.mp
  rw [← exact_left U V p hp hU hV n, hd, LinearMap.range_zero]

end NoExoticSixSphere.RelativeMayerVietoris

namespace NoExoticSixSphere.SupportedRelativeHomology

open Wikipedia.HopfProblem SingularMayerVietoris

variable {M : Type} [TopologicalSpace M]

/-- The original restriction pair is injective when the intersection's next group vanishes. -/
theorem eq_of_restrict_union_eq (p : ℕ) (hp : p ≠ 0) (K L : Set M)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    [Subsingleton (Homology (ModuleCat.of ℤ (ZMod p)) (K ∩ L) (n + 1))]
    (a b : Homology (ModuleCat.of ℤ (ZMod p)) (K ∪ L) n)
    (hleft : restrict (ModuleCat.of ℤ (ZMod p)) (Set.subset_union_left : K ⊆ K ∪ L) n a =
      restrict (ModuleCat.of ℤ (ZMod p)) (Set.subset_union_left : K ⊆ K ∪ L) n b)
    (hright : restrict (ModuleCat.of ℤ (ZMod p)) (Set.subset_union_right : L ⊆ K ∪ L) n a =
      restrict (ModuleCat.of ℤ (ZMod p)) (Set.subset_union_right : L ⊆ K ∪ L) n b) : a = b := by
  have hgen (I W : Set M) (hI : I = Kᶜ ∩ Lᶜ) (hW : W = Kᶜ ∪ Lᶜ)
      (hIL : I ⊆ Kᶜ) (hIR : I ⊆ Lᶜ)
      [Subsingleton (RelativeCoefficients.ModHomology p W (n + 1))]
      (c d : RelativeCoefficients.ModHomology p I n)
      (hl : homologyLinearMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ (ZMod p)) hIL) n c =
        homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ (ZMod p)) hIL) n d)
      (hr : homologyLinearMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ (ZMod p)) hIR) n c =
        homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ (ZMod p)) hIR) n d) :
      c = d := by
    subst I
    subst W
    apply RelativeMayerVietoris.firstMap_injective_of_subsingleton_union p hp Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl n
    rw [RelativeMayerVietoris.firstMap_apply, RelativeMayerVietoris.firstMap_apply, hl, hr]
  exact hgen (K ∪ L)ᶜ (K ∩ L)ᶜ (Set.compl_union K L) (Set.compl_inter K L)
    (fun _ hx hy => hx (Or.inl hy)) (fun _ hx hy => hx (Or.inr hy)) a b hleft hright

/-- Actual relative vanishing propagates across a closed union by the proved exact sequence. -/
theorem homology_union_subsingleton (p : ℕ) (hp : p ≠ 0) (K L : Set M)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    [Subsingleton (Homology (ModuleCat.of ℤ (ZMod p)) K n)]
    [Subsingleton (Homology (ModuleCat.of ℤ (ZMod p)) L n)]
    [Subsingleton (Homology (ModuleCat.of ℤ (ZMod p)) (K ∩ L) (n + 1))] :
    Subsingleton (Homology (ModuleCat.of ℤ (ZMod p)) (K ∪ L) n) :=
  ⟨fun a b => eq_of_restrict_union_eq p hp K L hK hL n a b
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

end NoExoticSixSphere.SupportedRelativeHomology
