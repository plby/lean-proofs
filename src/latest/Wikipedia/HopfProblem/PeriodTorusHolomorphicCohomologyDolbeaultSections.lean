import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultDerivatives
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultPairs

/-!
# The actual native period-torus Dolbeault differentials

The two differentials are the pair of actual antiholomorphic coordinate
derivatives and the literal expression `∂bar₀ b - ∂bar₁ a`. They act on
genuine native sections, commute with every restriction, and compose
to zero by the proved mixed-derivative identity.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open PeriodTorusLineBundleClassification

/-- The actual first native Dolbeault differential. -/
def differentialSection (p : PeriodDomain) (U : Opens p.Torus) :
    SmoothSection p U →ₗ[ℂ] PairSection p U :=
  (derivativeSection p 0 U).prod (derivativeSection p 1 U)

/-- The actual top differential in the original coordinate order `0,1`. -/
def topSection (p : PeriodDomain) (U : Opens p.Torus) :
    PairSection p U →ₗ[ℂ] SmoothSection p U :=
  (derivativeSection p 0 U).comp (LinearMap.snd ℂ (SmoothSection p U) (SmoothSection p U)) -
    (derivativeSection p 1 U).comp (LinearMap.fst ℂ (SmoothSection p U) (SmoothSection p U))

@[simp] theorem differentialSection_fst (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) : (differentialSection p U s).1 = derivativeSection p 0 U s := rfl

@[simp] theorem differentialSection_snd (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) : (differentialSection p U s).2 = derivativeSection p 1 U s := rfl

@[simp] theorem topSection_apply (p : PeriodDomain) (U : Opens p.Torus)
    (s : PairSection p U) (x : U) :
    topSection p U s x = derivativeValue p 0 U s.2 x - derivativeValue p 1 U s.1 x := rfl

/-- On the actual covering space, this is the literal top-form coefficient. -/
theorem topSection_pullback (p : PeriodDomain) (U : Opens p.Torus) (s : PairSection p U)
    (z : ComplexPlane₂) (hz : p.lattice.mkQ z ∈ U) :
    topSection p U s ⟨p.lattice.mkQ z, hz⟩ =
      dbarCoordinate (liftSection p U s.2) 0 z -
        dbarCoordinate (liftSection p U s.1) 1 z := by
  rw [topSection_apply, derivativeValue_pullback p 0 U s.2 z hz,
    derivativeValue_pullback p 1 U s.1 z hz]

theorem differentialSection_restrict (p : PeriodDomain) {U V : Opens p.Torus}
    (h : U ≤ V) (s : SmoothSection p V) :
    differentialSection p U (restriction p h s) =
      pairRestriction p h (differentialSection p V s) :=
  Prod.ext (derivativeSection_restrict p 0 h s) (derivativeSection_restrict p 1 h s)

theorem topSection_restrict (p : PeriodDomain) {U V : Opens p.Torus}
    (h : U ≤ V) (s : PairSection p V) :
    topSection p U (pairRestriction p h s) = restriction p h (topSection p V s) := by
  change derivativeSection p 0 U (restriction p h s.2) -
      derivativeSection p 1 U (restriction p h s.1) =
    restriction p h (derivativeSection p 0 V s.2 - derivativeSection p 1 V s.1)
  rw [derivativeSection_restrict, derivativeSection_restrict, map_sub]

/-- The two actual differentials compose to zero. -/
theorem topSection_differentialSection (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) : topSection p U (differentialSection p U s) = 0 := by
  change derivativeSection p 0 U (derivativeSection p 1 U s) -
    derivativeSection p 1 U (derivativeSection p 0 U s) = 0
  rw [derivativeSection_commute, sub_self]

def differential (p : PeriodDomain) : smoothSheaf p ⟶ pairSheaf p where
  hom :=
    { app U := AddCommGrpCat.ofHom (differentialSection p U.unop).toAddMonoidHom
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        exact AddMonoidHom.ext (differentialSection_restrict p (leOfHom h.unop)) }

def topDifferential (p : PeriodDomain) : pairSheaf p ⟶ smoothSheaf p where
  hom :=
    { app U := AddCommGrpCat.ofHom (topSection p U.unop).toAddMonoidHom
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        exact AddMonoidHom.ext (topSection_restrict p (leOfHom h.unop)) }

theorem differential_topDifferential (p : PeriodDomain) :
    differential p ≫ topDifferential p = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (topSection_differentialSection p U.unop)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
