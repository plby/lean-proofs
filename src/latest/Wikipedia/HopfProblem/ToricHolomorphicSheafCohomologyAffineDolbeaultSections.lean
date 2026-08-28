import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultDerivatives
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultPairs

/-!
# The two actual affine Dolbeault differentials

The first differential is the pair of actual antiholomorphic derivatives.
The second is literally `dbarFirst b - dbarSecond a`. Both maps are complex
linear on genuine sections and commute with actual restriction. Their
composite vanishes by the proved real mixed-derivative theorem.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

open PeriodTorusLineBundleClassification

/-- The actual `(0,1)` differential of an affine smooth function. -/
def differentialSection (U : Opens (ℂ × ℂ)) : SmoothSection U →ₗ[ℂ] PairSection U :=
  (derivativeSection false U).prod (derivativeSection true U)

/-- The actual `(0,2)` differential, in the coordinate order `z,w`. -/
def topSection (U : Opens (ℂ × ℂ)) : PairSection U →ₗ[ℂ] SmoothSection U :=
  (derivativeSection false U).comp (LinearMap.snd ℂ (SmoothSection U) (SmoothSection U)) -
    (derivativeSection true U).comp (LinearMap.fst ℂ (SmoothSection U) (SmoothSection U))

@[simp] theorem differentialSection_fst (U : Opens (ℂ × ℂ)) (s : SmoothSection U) :
    (differentialSection U s).1 = derivativeSection false U s := rfl

@[simp] theorem differentialSection_snd (U : Opens (ℂ × ℂ)) (s : SmoothSection U) :
    (differentialSection U s).2 = derivativeSection true U s := rfl

/-- The top coefficient retains the literal actual partial derivatives. -/
@[simp] theorem topSection_apply (U : Opens (ℂ × ℂ)) (s : PairSection U) (q : U) :
    topSection U s q =
      dbarFirst (smoothExtend U s.2) q - dbarSecond (smoothExtend U s.1) q := rfl

theorem differentialSection_restrict {U V : Opens (ℂ × ℂ)} (h : U ≤ V)
    (s : SmoothSection V) :
    differentialSection U (restriction h s) = pairRestriction h (differentialSection V s) :=
  Prod.ext (derivativeSection_restrict false h s) (derivativeSection_restrict true h s)

theorem topSection_restrict {U V : Opens (ℂ × ℂ)} (h : U ≤ V) (s : PairSection V) :
    topSection U (pairRestriction h s) = restriction h (topSection V s) := by
  change derivativeSection false U (restriction h s.2) -
      derivativeSection true U (restriction h s.1) =
    restriction h (derivativeSection false V s.2 - derivativeSection true V s.1)
  rw [derivativeSection_restrict, derivativeSection_restrict, map_sub]

/-- Real mixed-derivative symmetry makes this a genuine complex. -/
theorem topSection_differentialSection (U : Opens (ℂ × ℂ)) (s : SmoothSection U) :
    topSection U (differentialSection U s) = 0 := by
  change derivativeSection false U (derivativeSection true U s) -
    derivativeSection true U (derivativeSection false U s) = 0
  rw [derivativeSection_commute, sub_self]

/-- The actual sheaf map given by the first differential. -/
def differential : smoothSheaf ⟶ pairSheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom (differentialSection U.unop).toAddMonoidHom
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        exact AddMonoidHom.ext (differentialSection_restrict (leOfHom h.unop)) }

/-- The actual sheaf map given by the top differential. -/
def topDifferential : pairSheaf ⟶ smoothSheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom (topSection U.unop).toAddMonoidHom
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        exact AddMonoidHom.ext (topSection_restrict (leOfHom h.unop)) }

theorem differential_topDifferential : differential ≫ topDifferential = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (topSection_differentialSection U.unop)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
