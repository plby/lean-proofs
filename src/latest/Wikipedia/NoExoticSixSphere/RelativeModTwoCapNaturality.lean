import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainPullback
import Wikipedia.NoExoticSixSphere.RelativeModTwoCapCohomology
import Wikipedia.NoExoticSixSphere.ModTwoCapNaturality

/-!
# Naturality of the actual relative cap product

The formula concerns the original maps of pairs, cochain precomposition,
and absolute homology pushforward. Quotient surjectivity reduces it to
the already proved identity of the original front/back cap chains.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)
open RelativeModTwoCochains (Cochain Cocycle Cohomology complex cocycle_coboundary_zero
  pullback pullbackMap cohomologyPullback)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {U : Set X} {V : Set Y}

/-- Naturality on the original relative chain quotient, in every total degree. -/
theorem spaceMap_capInDegree (f : C(X, Y)) (hf : Set.MapsTo f U V)
    {p q n : ℕ} (h : p + q = n) (α : Cochain V p)
    (c : (RelativeCoefficients.complex Coefficient U).X n) :
    ((RelativeCoefficients.spaceMap Coefficient f).f q).hom
        (capInDegree U h (pullback f hf p α) c) =
      capInDegree V h α (((RelativeCoefficients.mapChain Coefficient f hf).f n).hom c) := by
  subst n
  obtain ⟨b, rfl⟩ := RelativeCoefficients.quotientMap_surjective Coefficient U (p + q) c
  have he := congrArg (fun g => (g.f (p + q)).hom b)
    (RelativeCoefficients.projection_mapChain Coefficient f hf)
  change ((RelativeCoefficients.mapChain Coefficient f hf).f (p + q)).hom
      (RelativeCoefficients.quotientMap Coefficient U (p + q) b) =
    RelativeCoefficients.quotientMap Coefficient V (p + q)
      (((RelativeCoefficients.spaceMap Coefficient f).f (p + q)).hom b) at he
  rw [he, capInDegree_quotientMap, capInDegree_quotientMap,
    RelativeModTwoCochains.toAbsolute_pullback]
  exact ModTwoCapProduct.spaceMap_cap f p q (RelativeModTwoCochains.toAbsolute V p α) b

/-- Mapping original capped cycles agrees with capping their original pair-map images. -/
theorem mapCycles_cap (f : C(X, Y)) (hf : Set.MapsTo f U V) (p q : ℕ) (α : Cocycle V p)
    (c : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) (p + q)) :
    ModuleHomology.mapCycles (RelativeCoefficients.spaceMap Coefficient f) q
        (capCycles U p q (SingularCohomologyFree.mapCocycles (pullbackMap f hf) p α).val
          (cocycle_coboundary_zero U p
            (SingularCohomologyFree.mapCocycles (pullbackMap f hf) p α)) c) =
      capCycles V p q α.val (cocycle_coboundary_zero V p α)
        (ModuleHomology.mapCycles (RelativeCoefficients.mapChain Coefficient f hf) (p + q) c) := by
  apply Subtype.ext
  let β := SingularCohomologyFree.mapCocycles (pullbackMap f hf) p α
  have hβ : β.val = pullback f hf p α.val :=
    SingularCohomologyFree.mapCocycles_val (pullbackMap f hf) p α
  have hleft := ModuleHomology.mapCycles_val (RelativeCoefficients.spaceMap Coefficient f) q
    (capCycles U p q β.val (cocycle_coboundary_zero U p β) c)
  have hright := capCycles_val V p q α.val (cocycle_coboundary_zero V p α)
    (ModuleHomology.mapCycles (RelativeCoefficients.mapChain Coefficient f hf) (p + q) c)
  apply hleft.trans
  apply (congrArg ((RelativeCoefficients.spaceMap Coefficient f).f q).hom
    (capCycles_val U p q β.val (cocycle_coboundary_zero U p β) c)).trans
  apply (congrArg (fun γ : Cochain U p =>
    ((RelativeCoefficients.spaceMap Coefficient f).f q).hom
      (capInDegree U (q := q) rfl γ c.val)) hβ).trans
  apply (spaceMap_capInDegree f hf rfl α.val c.val).trans
  exact (hright.trans (congrArg (capInDegree V (q := q) rfl α.val)
    (ModuleHomology.mapCycles_val
      (RelativeCoefficients.mapChain Coefficient f hf) (p + q) c))).symm

/-- Naturality on both genuine relative class groups, with absolute output. -/
theorem capProduct_naturality (f : C(X, Y)) (hf : Set.MapsTo f U V) (p q : ℕ)
    (a : Cohomology V p) (c : (RelativeCoefficients.complex Coefficient U).homology (p + q)) :
    modHomologyMap 2 f q (capProduct U p q (cohomologyPullback f hf p a) c) =
      capProduct V p q a
        ((HomologicalComplex.homologyMap (RelativeCoefficients.mapChain Coefficient f hf)
          (p + q)).hom c) := by
  obtain ⟨α, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective (complex V) p a
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective
    (RelativeCoefficients.complex Coefficient U) (p + q) c
  rw [RelativeModTwoCochains.cohomologyPullback_cocycleClass, capProduct_cocycle_cycle,
    ModTwoCapProduct.modHomologyMap_cycleClass, ModuleHomology.homologyMap_cycleClass,
    capProduct_cocycle_cycle]
  exact congrArg (ModuleHomology.cycleClass (modComplex 2 Y) q) (mapCycles_cap f hf p q α z)

end NoExoticSixSphere.RelativeModTwoCap
