import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapCohomology
import Wikipedia.NoExoticSixSphere.RelativeSingularHomologyMaps

/-!
# Naturality of the original relative integral cap product

Pair maps act on the actual integral relative cochains by precomposition.
The original quotient projection square reduces cap naturality to the
proved front/back simplex identity. Both original cycle quotients are
retained when passing to cohomology and homology.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open FirstHurewicz SingularMayerVietoris
open NoExoticSixSphere.RelativeSingularHomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {U : Set X} {V : Set Y}

/-- Pullback along the original integral chain map of pairs. -/
def pullbackMap (f : C(X, Y)) (hf : Set.MapsTo f U V) :
    cochainComplex V ⟶ cochainComplex U :=
  SingularCohomologyFree.dualMap (mapChain f hf)

abbrev pullback (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ) :
    Cochain V p →ₗ[ℤ] Cochain U p := ((pullbackMap f hf).f p).hom

theorem pullback_apply (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ)
    (α : Cochain V p) (c : (complex U).X p) :
    pullback f hf p α c = α (((mapChain f hf).f p).hom c) := rfl

theorem toAbsolute_pullback (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ)
    (α : Cochain V p) :
    toAbsolute U p (pullback f hf p α) =
      SingularCohomologyCup.pullback f p (toAbsolute V p α) := by
  apply LinearMap.ext
  intro c
  exact congrArg α (congrArg (fun g => (g.f p).hom c) (projection_mapChain f hf))

/-- The actual relative integral cohomology pullback. -/
abbrev cohomologyPullback (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ) :
    Cohomology V p →ₗ[ℤ] Cohomology U p :=
  (HomologicalComplex.homologyMap (pullbackMap f hf) p).hom

theorem cohomologyPullback_cocycleClass (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ)
    (α : Cocycle V p) :
    cohomologyPullback f hf p (SingularCohomologyFree.cocycleClass (cochainComplex V) p α) =
      SingularCohomologyFree.cocycleClass (cochainComplex U) p
        (SingularCohomologyFree.mapCocycles (pullbackMap f hf) p α) :=
  SingularCohomologyFree.homologyMap_cocycleClass (pullbackMap f hf) p α

/-- Cap naturality on the actual integral relative chain quotient. -/
theorem chainMap_capInDegree (f : C(X, Y)) (hf : Set.MapsTo f U V)
    {p q n : ℕ} (h : p + q = n) (α : Cochain V p) (c : (complex U).X n) :
    inducedChain f q (capInDegree U h (pullback f hf p α) c) =
      capInDegree V h α (((mapChain f hf).f n).hom c) := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective U n c
  have he := congrArg (fun g => (g.f n).hom b) (projection_mapChain f hf)
  change ((mapChain f hf).f n).hom (quotientMap U n b) =
    quotientMap V n (inducedChain f n b) at he
  rw [he, capInDegree_quotientMap, capInDegree_quotientMap, toAbsolute_pullback]
  exact IntegralCap.naturality h f (toAbsolute V p α) b

/-- The cap cycle identity retains the original maps on cycles. -/
theorem mapCycles_cap (f : C(X, Y)) (hf : Set.MapsTo f U V) (p q : ℕ) (α : Cocycle V p)
    (c : ModuleHomology.Cycle (complex U) (p + q)) :
    ModuleHomology.mapCycles (singularChainMap f) q
        (capCycles U p q (SingularCohomologyFree.mapCocycles (pullbackMap f hf) p α).val
          (cocycle_coboundary_zero U p
            (SingularCohomologyFree.mapCocycles (pullbackMap f hf) p α)) c) =
      capCycles V p q α.val (cocycle_coboundary_zero V p α)
        (ModuleHomology.mapCycles (mapChain f hf) (p + q) c) := by
  apply Subtype.ext
  let β := SingularCohomologyFree.mapCocycles (pullbackMap f hf) p α
  have hβ : β.val = pullback f hf p α.val :=
    SingularCohomologyFree.mapCocycles_val (pullbackMap f hf) p α
  have hleft := ModuleHomology.mapCycles_val (singularChainMap f) q
    (capCycles U p q β.val (cocycle_coboundary_zero U p β) c)
  have hright := capCycles_val V p q α.val (cocycle_coboundary_zero V p α)
    (ModuleHomology.mapCycles (mapChain f hf) (p + q) c)
  apply hleft.trans
  apply (congrArg ((singularChainMap f).f q).hom
    (capCycles_val U p q β.val (cocycle_coboundary_zero U p β) c)).trans
  apply (congrArg (fun γ : Cochain U p =>
    inducedChain f q (capInDegree U (q := q) rfl γ c.val)) hβ).trans
  apply (chainMap_capInDegree f hf rfl α.val c.val).trans
  exact (hright.trans (congrArg (capInDegree V (q := q) rfl α.val)
    (ModuleHomology.mapCycles_val (mapChain f hf) (p + q) c))).symm

/-- Naturality after descending through both genuine integral class groups. -/
theorem capProduct_naturality (f : C(X, Y)) (hf : Set.MapsTo f U V) (p q : ℕ)
    (a : Cohomology V p) (c : (complex U).homology (p + q)) :
    (HomologicalComplex.homologyMap (singularChainMap f) q).hom
        (capProduct U p q (cohomologyPullback f hf p a) c) =
      capProduct V p q a
        ((HomologicalComplex.homologyMap (mapChain f hf) (p + q)).hom c) := by
  obtain ⟨α, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective (cochainComplex V) p a
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective (complex U) (p + q) c
  rw [cohomologyPullback_cocycleClass, capProduct_cocycle_cycle,
    ModuleHomology.homologyMap_cycleClass, ModuleHomology.homologyMap_cycleClass,
    capProduct_cocycle_cycle]
  exact congrArg (ModuleHomology.cycleClass (singularComplex Y) q) (mapCycles_cap f hf p q α z)

/-- The same original cap product with an explicitly named total degree. -/
def capProductInDegree (U : Set X) {p q n : ℕ} (h : p + q = n) :
    Cohomology U p →ₗ[ℤ] ((complex U).homology n →ₗ[ℤ] (singularComplex X).homology q) := by
  subst n
  exact capProduct U p q

theorem capProductInDegree_naturality (f : C(X, Y)) (hf : Set.MapsTo f U V)
    {p q n : ℕ} (h : p + q = n) (a : Cohomology V p) (c : (complex U).homology n) :
    (HomologicalComplex.homologyMap (singularChainMap f) q).hom
        (capProductInDegree U h (cohomologyPullback f hf p a) c) =
      capProductInDegree V h a ((HomologicalComplex.homologyMap (mapChain f hf) n).hom c) := by
  subst n
  exact capProduct_naturality f hf p q a c

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
