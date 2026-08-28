import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupPairStalk
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Exactness of the genuine pair-sheaf columns

The original stalk comparison converts the kernel equation to the two
original coefficient equations. Their actual preimages give an actual
pair-stalk preimage. No acyclicity or exactness property of a new
comparison complex is assumed.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Pairs

open CuspNormalization.SheafBiproduct

variable {X : TopCat.{0}}

/-- Pairing an injective original stalk map remains injective on actual pair stalks. -/
theorem stalk_map_injective {F G : AbSheaf X} (f : F ⟶ G) (x : X)
    (h : Function.Injective ((stalkFunctor X x).map f).hom) :
    Function.Injective ((stalkFunctor X x).map (map f)).hom := by
  intro a b hab
  apply (stalkEquiv F x).injective
  have he := (stalkEquiv_map f x a).symm.trans
    ((congrArg (stalkEquiv G x) hab).trans (stalkEquiv_map f x b))
  exact Prod.ext (h (congrArg Prod.fst he)) (h (congrArg Prod.snd he))

/-- Actual exact sheaf columns remain exact after taking literal coefficient pairs. -/
theorem map_exact (S : ShortComplex (AbSheaf X)) (h : S.Exact) :
    (S.map (functor X)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map (functor X))).mpr
  intro x
  apply (ShortComplex.ab_exact_iff _).mpr
  intro s hs
  change (stalkFunctor X x).map (map S.g) s = 0 at hs
  have hstalk := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp h x
  have he := (S.map (stalkFunctor X x)).ab_exact_iff_function_exact.mp hstalk
  have hclosed := (stalkEquiv_map S.g x s).symm.trans
    ((congrArg (stalkEquiv S.X₃ x) hs).trans (_root_.map_zero (stalkEquiv S.X₃ x)))
  obtain ⟨a, ha⟩ := (he (stalkEquiv S.X₂ x s).1).mp (congrArg Prod.fst hclosed)
  obtain ⟨b, hb⟩ := (he (stalkEquiv S.X₂ x s).2).mp (congrArg Prod.snd hclosed)
  refine ⟨(stalkEquiv S.X₁ x).symm (a, b), (stalkEquiv S.X₂ x).injective ?_⟩
  change stalkEquiv S.X₂ x
      ((stalkFunctor X x).map (map S.f) ((stalkEquiv S.X₁ x).symm (a, b))) =
    stalkEquiv S.X₂ x s
  rw [stalkEquiv_map, AddEquiv.apply_symm_apply]
  exact Prod.ext ha hb

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Pairs
