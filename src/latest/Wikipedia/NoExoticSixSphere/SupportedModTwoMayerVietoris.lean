import Wikipedia.NoExoticSixSphere.RelativeModTwoMayerVietorisMaps
import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology

/-!
# Lifting supported cohomology classes from the intersection

If two actual classes on closed supports have the same extension to the
union, cohomological Mayer--Vietoris constructs a class on the intersection
whose original support extensions are the two specified classes. This is
the middle exactness statement with the original support maps.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X]

/-- Equal extensions to the union lift together from the actual intersection support. -/
theorem exists_intersection_lift (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)
    (n : ℕ) (a : Cohomology K n) (b : Cohomology L n)
    (hab : extend (Set.subset_union_left : K ⊆ K ∪ L) n a =
      extend (Set.subset_union_right : L ⊆ K ∪ L) n b) :
    ∃ c : Cohomology (K ∩ L) n,
      extend (Set.inter_subset_left : K ∩ L ⊆ K) n c = a ∧
        extend (Set.inter_subset_right : K ∩ L ⊆ L) n c = b := by
  have hgen (I W : Set X) (hI : I = Kᶜ ∩ Lᶜ) (hW : W = Kᶜ ∪ Lᶜ)
      (hIL : I ⊆ Kᶜ) (hIR : I ⊆ Lᶜ) (hLW : Kᶜ ⊆ W) (hRW : Lᶜ ⊆ W)
      (he : (HomologicalComplex.homologyMap (ModTwoDualComplex.map
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hIL)) n).hom a =
        (HomologicalComplex.homologyMap (ModTwoDualComplex.map
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hIR)) n).hom b) :
      ∃ c : RelativeModTwoCochains.Cohomology W n,
        (HomologicalComplex.homologyMap (ModTwoDualComplex.map
            (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hLW)) n).hom c = a ∧
          (HomologicalComplex.homologyMap (ModTwoDualComplex.map
            (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) hRW)) n).hom c = b := by
    subst I
    subst W
    exact RelativeModTwoMayerVietoris.exists_lift_of_agree Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl n a b he
  exact hgen (K ∪ L)ᶜ (K ∩ L)ᶜ (Set.compl_union K L) (Set.compl_inter K L)
    (fun _ hx hy => hx (Or.inl hy)) (fun _ hx hy => hx (Or.inr hy))
    (fun _ hx hy => hx hy.1) (fun _ hx hy => hx hy.2) hab

end NoExoticSixSphere.SupportedModTwoCohomology
