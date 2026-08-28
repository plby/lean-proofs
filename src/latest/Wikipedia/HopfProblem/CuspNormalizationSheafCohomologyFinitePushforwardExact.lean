import Wikipedia.HopfProblem.CuspNormalizationSheafFiniteStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exactness of actual finite closed pushforward

For a closed continuous map with finite fibres and Hausdorff source,
the actual pushforward stalk is the product of the source stalks on its
fibre. The naturality of that proved equivalence transfers exactness of
genuine sheaf complexes. The actual pullback adjunction also shows that
pushforward preserves injective objects.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward

/-- Genuine small sheaves of abelian groups on the open-set site. -/
abbrev AbelianSheaf (X : TopCat.{0}) :=
  TopCat.Sheaf AddCommGrpCat.{0} X

/-- The actual topological pushforward functor, not a replacement model. -/
abbrev pushforward {X Y : TopCat.{0}} (f : X ⟶ Y) : AbelianSheaf X ⥤ AbelianSheaf Y :=
  TopCat.Sheaf.pushforward AddCommGrpCat f

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- Actual additive sheaf pushforward is an additive functor. -/
instance pushforward_additive : (pushforward f).Additive where
  map_add := by intros; rfl

/-- The actual pushforward sends the zero sheaf morphism to zero. -/
instance pushforward_preservesZeroMorphisms : (pushforward f).PreservesZeroMorphisms where
  map_zero := by intros; rfl

/-- Actual inverse image preserves finite limits on abelian sheaves. -/
theorem pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat f) := by
  change PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) AddCommGrpCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- Actual pushforward preserves injectives because its actual left
adjoint preserves monomorphisms. No finiteness hypothesis is needed. -/
theorem pushforward_preservesInjectiveObjects : (pushforward f).PreservesInjectiveObjects := by
  let _ := pullback_preservesFiniteLimits f
  let _ := preservesMonomorphisms_of_preservesLimitsOfShape
    (TopCat.Sheaf.pullback AddCommGrpCat f)
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f)

variable [T2Space X] (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

include hf hfinite

/-- The actual finite closed pushforward preserves every exact short
complex of genuine sheaves of abelian groups. -/
theorem pushforward_exact (S : ShortComplex (AbelianSheaf X)) (hS : S.Exact) :
    (S.map (pushforward f)).Exact := by
  classical
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map (pushforward f))).mpr
  intro y
  let K := SheafBiproduct.stalkFunctor Y y
  let e₁ := SheafFiniteStalk.pushforwardStalkEquiv f hf S.X₁ y (hfinite y)
  let e₂ := SheafFiniteStalk.pushforwardStalkEquiv f hf S.X₂ y (hfinite y)
  let e₃ := SheafFiniteStalk.pushforwardStalkEquiv f hf S.X₃ y (hfinite y)
  apply (((S.map (pushforward f)).map K).ab_exact_iff).mpr
  intro s hs
  have hzero : e₃ (K.map ((pushforward f).map S.g) s) = 0 :=
    (congrArg e₃ hs).trans e₃.map_zero
  have hker (x : f ⁻¹' {y}) :
      (SheafBiproduct.stalkFunctor X x.val).map S.g (e₂ s x) = 0 :=
    (SheafFiniteStalk.pushforwardStalkEquiv_naturality f hf S.g y (hfinite y) s x).symm.trans
      (congrFun hzero x)
  have hlocal (x : f ⁻¹' {y}) :
      ∃ u, (SheafBiproduct.stalkFunctor X x.val).map S.f u = e₂ s x := by
    have hexact := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS x.val
    exact ((S.map (SheafBiproduct.stalkFunctor X x.val)).ab_exact_iff.mp hexact)
      (e₂ s x) (hker x)
  choose u hu using hlocal
  refine ⟨e₁.symm u, ?_⟩
  apply e₂.injective
  funext x
  exact (SheafFiniteStalk.pushforwardStalkEquiv_naturality f hf S.f y (hfinite y)
    (e₁.symm u) x).trans
      ((congrArg ((SheafBiproduct.stalkFunctor X x.val).map S.f)
        (congrFun (e₁.apply_symm_apply u) x)).trans (hu x))

/-- The exactness assertion gives genuine preservation of finite
limits and colimits by the actual pushforward functor. -/
theorem pushforward_preservesFiniteLimitsAndColimits :
    PreservesFiniteLimits (pushforward f) ∧ PreservesFiniteColimits (pushforward f) :=
  ((pushforward f).exact_tfae.out 1 3).mp (pushforward_exact f hf hfinite)

/-- In particular the actual finite closed pushforward preserves finite colimits. -/
theorem pushforward_preservesFiniteColimits : PreservesFiniteColimits (pushforward f) :=
  (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).2

/-- The actual finite closed pushforward preserves genuine short exact sequences. -/
theorem pushforward_shortExact (S : ShortComplex (AbelianSheaf X)) (hS : S.ShortExact) :
    (S.map (pushforward f)).ShortExact := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact hS.map_of_exact (pushforward f)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward
