import Wikipedia.NoExoticSixSphere.CommonSmallCapCohomology
import Wikipedia.NoExoticSixSphere.RelativeModTwoConnectingUnionCocycles

/-!
# Common-small cap agrees with cap localized from the actual union quotient

Every common-small simplex lies either in the overlap or in the union
of the annihilated pieces. Its original inclusion into that small
complex identifies the overlap cap with the original localized cap of
the actual union-relative cochain.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- Simultaneous smallness implies smallness for the overlap and the union of the other pieces. -/
theorem commonSmall_le_overlap_union :
    commonSmall U A V B ≤ support (U ∩ V) ⊔ support (A ∪ B) := by
  intro n s hs
  change (s ∈ (support U).obj n ∨ s ∈ (support A).obj n) ∧
    (s ∈ (support V).obj n ∨ s ∈ (support B).obj n) at hs
  change s ∈ (support (U ∩ V)).obj n ∨ s ∈ (support (A ∪ B)).obj n
  rcases hs with ⟨hU | hA, hV | hB⟩
  · left
    rw [support_inter]
    exact ⟨hU, hV⟩
  · exact Or.inr ((support_mono (Set.subset_union_right : B ⊆ A ∪ B)) n hB)
  · exact Or.inr ((support_mono (Set.subset_union_left : A ⊆ A ∪ B)) n hA)
  · exact Or.inr ((support_mono (Set.subset_union_left : A ⊆ A ∪ B)) n hA)

/-- The original simplex inclusion into the overlap/union small complex. -/
abbrev commonToOverlapSmall : (commonSmall U A V B : SSet) ⟶ Small (U ∩ V) (A ∪ B) :=
  SSet.Subcomplex.homOfLE (commonSmall_le_overlap_union U A V B)

theorem commonToOverlapSmall_inclusion :
    commonToOverlapSmall U A V B ≫ smallInclusion (U ∩ V) (A ∪ B) =
      commonSmallInclusion U A V B := SSet.Subcomplex.homOfLE_ι _

theorem commonToOverlapSmall_chain_inclusion (R : ModuleCat.{0} ℤ) :
    (SimplicialCoefficients.chains R).map (commonToOverlapSmall U A V B) ≫
        (SimplicialCoefficients.chains R).map (smallInclusion (U ∩ V) (A ∪ B)) =
      commonSmallChainInclusion U A V B R :=
  (SimplicialCoefficients.homOfLE_inclusion R (commonSmall_le_overlap_union U A V B))

end NoExoticSixSphere.SingularSubcomplex

namespace NoExoticSixSphere.CommonSmallModTwoCap

open ModTwoCapProduct (Coefficient)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- The overlap cap of the actual union pullback equals the original overlap-localized cap. -/
theorem capInDegree_union {p q n : ℕ} (h : p + q = n)
    (θ : RelativeModTwoCochains.Cochain (A ∪ B) p) (c : (complex U A V B).X n) :
    capInDegree U A V B h
        (((ModTwoDualComplex.map
          (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)).f p).hom θ) c =
      SmallModTwoCap.capInDegree (U ∩ V) (A ∪ B) h θ
        ((((SimplicialCoefficients.chains Coefficient).map
          (SingularSubcomplex.commonToOverlapSmall U A V B)).f n).hom c) := by
  apply SmallModTwoCap.inclusion_injective (U ∩ V) q
  have he := congrArg (fun m => (m.f n).hom c)
    (SingularSubcomplex.commonToOverlapSmall_chain_inclusion U A V B Coefficient)
  apply (inclusion_capInDegree U A V B h _ c).trans
  apply Eq.trans _ (SmallModTwoCap.inclusion_capInDegree (U ∩ V) (A ∪ B) h θ _).symm
  exact congrArg₂ (fun α t => ModTwoCapProduct.capInDegree h α t)
    (SmallRelativeModTwoCochains.toAbsolute_union A B p θ) he.symm

end NoExoticSixSphere.CommonSmallModTwoCap
