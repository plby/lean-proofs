import Wikipedia.NoExoticSixSphere.RelativeSmallChainComparison
import Wikipedia.NoExoticSixSphere.RelativeHomologyHomeomorph

/-!
# Excision for an actual open cover

For an open cover `U ∪ V = X`, inclusion of pairs `(U, U ∩ V) → (X, V)`
induces an isomorphism on relative singular homology in every degree.
The map is the actual map of pairs: the small-chain comparison and the
intersection-subtype identification are proved to factor that map.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The second subset restricted to the first, as a genuine subset of the subspace. -/
def overlapIn : Set U := Subtype.val ⁻¹' V

/-- The two actual presentations of the intersection have their usual subspace topologies. -/
def overlapHomeomorph : overlapIn U V ≃ₜ (U ∩ V : Set X) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem overlap_inclusion :
    (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)).comp
        (overlapHomeomorph U V : C(overlapIn U V, (U ∩ V : Set X))) =
      subtypeInclusion (overlapIn U V) := by
  ext x
  rfl

theorem overlap_chain_square :
    inclusion (overlapIn U V) ≫ 𝟙 (singularComplex U) =
      (chainHomeomorphIso (overlapHomeomorph U V)).hom ≫ intersectionToLeft U V := by
  rw [Category.comp_id]
  change singularChainMap (subtypeInclusion (overlapIn U V)) =
    singularChainMap (overlapHomeomorph U V : C(overlapIn U V, (U ∩ V : Set X))) ≫
      singularChainMap (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))
  rw [← chainMap_comp, overlap_inclusion]

/-- Identifying the two intersection subtypes gives an isomorphism of relative complexes. -/
def overlapQuotientMap : complex (overlapIn U V) ⟶ intersectionQuotient U V :=
  cokernel.map (inclusion (overlapIn U V)) (intersectionToLeft U V)
    (chainHomeomorphIso (overlapHomeomorph U V)).hom (𝟙 _) (overlap_chain_square U V)

instance overlapQuotientMap_isIso : IsIso (overlapQuotientMap U V) := by
  unfold overlapQuotientMap
  infer_instance

@[reassoc]
theorem projection_overlapQuotientMap :
    projection (overlapIn U V) ≫ overlapQuotientMap U V =
      cokernel.π (intersectionToLeft U V) := by
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

/-- The actual inclusion of pairs whose map is the excision isomorphism. -/
def excisionChainMap : complex (overlapIn U V) ⟶ complex V :=
  mapChain (subtypeInclusion U) (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V
    from fun _ hx => hx)

/-- The small-chain construction factors the original inclusion map of pairs. -/
theorem excisionChainMap_eq :
    excisionChainMap U V = overlapQuotientMap U V ≫ intersectionComparison U V := by
  apply (cancel_epi (cokernel.π (inclusion (overlapIn U V)))).mp
  change projection (overlapIn U V) ≫ _ = projection (overlapIn U V) ≫ _
  change projection (overlapIn U V) ≫ mapChain (subtypeInclusion U) _ = _
  rw [projection_mapChain, ← Category.assoc, projection_overlapQuotientMap,
    intersectionProjection_comparison]

/-- Open-cover excision, proved at the level of the actual relative chain map. -/
theorem excisionChainMap_quasiIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) : QuasiIso (excisionChainMap U V) := by
  rw [excisionChainMap_eq]
  let := intersectionComparison_quasiIso U V hU hV hcover
  infer_instance

/-- The actual inclusion-induced relative homology map. -/
abbrev excisionMap (n : ℕ) : Homology (overlapIn U V) n →ₗ[ℤ] Homology V n :=
  homologyLinearMap (excisionChainMap U V) n

/-- Excision for relative integral singular homology, including degree zero. -/
def excisionEquiv (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    Homology (overlapIn U V) n ≃ₗ[ℤ] Homology V n := by
  let := excisionChainMap_quasiIso U V hU hV hcover
  exact (isoOfQuasiIsoAt (excisionChainMap U V) n).toLinearEquiv

theorem excisionEquiv_toLinearMap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (excisionEquiv U V hU hV hcover n).toLinearMap = excisionMap U V n := rfl

theorem excisionMap_bijective (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) : Function.Bijective (excisionMap U V n) :=
  (excisionEquiv U V hU hV hcover n).bijective

end NoExoticSixSphere.RelativeSingularHomology
