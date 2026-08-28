import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultGlobalBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultSections

/-!
# Literal global native Dolbeault formulas on the period cover

The genuine native global smooth-section comparison with smooth periodic
covering functions intertwines both actual Dolbeault differentials with
the literal coordinate derivatives used by the Fourier solvers.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open PeriodTorusLineBundleClassification

/-- On the top open the local lift is the literal global quotient pullback. -/
theorem liftSection_top_eq_globalLift (p : PeriodDomain) (s : SmoothSection p ⊤) :
    liftSection p ⊤ s = globalLift p s := by
  funext z
  exact liftSection_apply p ⊤ s z (by trivial)

/-- The actual global section derivative pulls back to the literal
antiholomorphic coordinate derivative on the covering vector space. -/
theorem globalLift_derivativeSection (p : PeriodDomain) (i : Fin 2)
    (s : SmoothSection p ⊤) (z : ComplexPlane₂) :
    globalLift p (derivativeSection p i ⊤ s) z = dbarCoordinate (globalLift p s) i z := by
  have h := derivativeSection_pullback p i ⊤ s z (by trivial)
  rw [liftSection_top_eq_globalLift] at h
  exact h

theorem globalLift_derivativeSection_fun (p : PeriodDomain) (i : Fin 2)
    (s : SmoothSection p ⊤) :
    globalLift p (derivativeSection p i ⊤ s) = dbarCoordinate (globalLift p s) i :=
  funext (globalLift_derivativeSection p i s)

theorem globalLift_differentialSection_fst (p : PeriodDomain)
    (s : SmoothSection p ⊤) (z : ComplexPlane₂) :
    globalLift p (differentialSection p ⊤ s).1 z =
      dbarCoordinate (globalLift p s) 0 z :=
  globalLift_derivativeSection p 0 s z

theorem globalLift_differentialSection_snd (p : PeriodDomain)
    (s : SmoothSection p ⊤) (z : ComplexPlane₂) :
    globalLift p (differentialSection p ⊤ s).2 z =
      dbarCoordinate (globalLift p s) 1 z :=
  globalLift_derivativeSection p 1 s z

/-- The top differential retains its actual coordinate order and sign. -/
theorem globalLift_topSection (p : PeriodDomain) (s : PairSection p ⊤)
    (z : ComplexPlane₂) :
    globalLift p (topSection p ⊤ s) z =
      dbarCoordinate (globalLift p s.2) 0 z - dbarCoordinate (globalLift p s.1) 1 z := by
  have h := topSection_pullback p ⊤ s z (by trivial)
  rw [liftSection_top_eq_globalLift, liftSection_top_eq_globalLift] at h
  exact h

theorem globalLift_topSection_fun (p : PeriodDomain) (s : PairSection p ⊤) :
    globalLift p (topSection p ⊤ s) = fun z =>
      dbarCoordinate (globalLift p s.2) 0 z - dbarCoordinate (globalLift p s.1) 1 z :=
  funext (globalLift_topSection p s)

/-- Genuine closed native forms have the literal closedness equation
required by the independent covering-space Fourier construction. -/
theorem globalLift_closed_of_topSection_zero (p : PeriodDomain) (s : PairSection p ⊤)
    (hs : topSection p ⊤ s = 0) (z : ComplexPlane₂) :
    dbarCoordinate (globalLift p s.2) 0 z = dbarCoordinate (globalLift p s.1) 1 z := by
  have h := congrArg (fun t : SmoothSection p ⊤ => globalLift p t z) hs
  rw [globalLift_topSection] at h
  exact sub_eq_zero.mp h

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
