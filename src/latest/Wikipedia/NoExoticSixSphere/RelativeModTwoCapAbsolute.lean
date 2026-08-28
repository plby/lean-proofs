import Wikipedia.NoExoticSixSphere.RelativeModTwoCapDegree
import Wikipedia.NoExoticSixSphere.ModTwoCapDegree

/-!
# Comparison with the original absolute cap product

The actual absolute-to-relative projection and relative-to-absolute
cochain precomposition intertwine the constructed cap products. This is
proved on the original representatives, not by identifying abstract ranks.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- The original quotient precomposition on genuine cohomology. -/
abbrev toAbsoluteCohomology (p : ℕ) : Cohomology U p →ₗ[ℤ] ModTwoCapProduct.Cohomology X p :=
  (HomologicalComplex.homologyMap (toAbsoluteMap U) p).hom

theorem toAbsoluteCohomology_cocycleClass (p : ℕ) (α : Cocycle U p) :
    toAbsoluteCohomology U p (SingularCohomologyFree.cocycleClass (complex U) p α) =
      SingularCohomologyFree.cocycleClass (ModTwoCapProduct.cochainComplex X) p
        (SingularCohomologyFree.mapCocycles (toAbsoluteMap U) p α) :=
  SingularCohomologyFree.homologyMap_cocycleClass (toAbsoluteMap U) p α

end NoExoticSixSphere.RelativeModTwoCochains

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)
open RelativeModTwoCochains (Cocycle Cohomology complex cocycle_coboundary_zero
  toAbsoluteMap toAbsolute toAbsoluteCohomology)

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- The original projection of an absolute cycle gives its original cap representative. -/
theorem capCycles_projection (p q : ℕ) (α : Cocycle U p)
    (c : ModuleHomology.Cycle (modComplex 2 X) (p + q)) :
    capCycles U p q α.val (cocycle_coboundary_zero U p α)
        (ModuleHomology.mapCycles (RelativeCoefficients.projection Coefficient U) (p + q) c) =
      ModTwoCapProduct.capCycles p q
        (SingularCohomologyFree.mapCocycles (toAbsoluteMap U) p α).val
        (ModTwoCapProduct.cocycle_coboundary_zero X p
          (SingularCohomologyFree.mapCocycles (toAbsoluteMap U) p α)) c := by
  apply Subtype.ext
  let β := SingularCohomologyFree.mapCocycles (toAbsoluteMap U) p α
  have hβ : β.val = toAbsolute U p α.val :=
    SingularCohomologyFree.mapCocycles_val (toAbsoluteMap U) p α
  apply (capCycles_val U p q α.val (cocycle_coboundary_zero U p α) _).trans
  apply (congrArg (capInDegree U (q := q) rfl α.val)
    (ModuleHomology.mapCycles_val
      (RelativeCoefficients.projection Coefficient U) (p + q) c)).trans
  apply (capInDegree_quotientMap U rfl α.val c.val).trans
  exact ((ModTwoCapProduct.capCycles_val p q β.val
    (ModTwoCapProduct.cocycle_coboundary_zero X p β) c).trans
      (congrArg (fun γ : ModTwoCapProduct.Cochain X p =>
        ModTwoCapProduct.cap (q := q) γ c.val) hβ)).symm

/-- The two actual cap products commute with the original absolute-relative maps. -/
theorem capProduct_projection (p q : ℕ) (a : Cohomology U p)
    (c : ModHomology 2 X (p + q)) :
    capProduct U p q a
        ((HomologicalComplex.homologyMap (RelativeCoefficients.projection Coefficient U)
          (p + q)).hom c) =
      ModTwoCapProduct.capProduct X p q (toAbsoluteCohomology U p a) c := by
  obtain ⟨α, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective (complex U) p a
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective (modComplex 2 X) (p + q) c
  rw [ModuleHomology.homologyMap_cycleClass, capProduct_cocycle_cycle,
    RelativeModTwoCochains.toAbsoluteCohomology_cocycleClass,
    ModTwoCapProduct.capProduct_cocycle_cycle]
  exact congrArg (ModuleHomology.cycleClass (modComplex 2 X) q) (capCycles_projection U p q α z)

theorem capProductInDegree_projection {p q n : ℕ} (h : p + q = n) (a : Cohomology U p)
    (c : ModHomology 2 X n) :
    capProductInDegree U h a
        ((HomologicalComplex.homologyMap (RelativeCoefficients.projection Coefficient U) n).hom c) =
      ModTwoCapProduct.capProductInDegree X h (toAbsoluteCohomology U p a) c := by
  subst n
  exact capProduct_projection U p q a c

end NoExoticSixSphere.RelativeModTwoCap
