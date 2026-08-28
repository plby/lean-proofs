import Wikipedia.HopfProblem.CuspCoinvariantExtensionPuncturedBasic
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingPeriods

/-!
# Exact marked-circle agreement on an entire original cusp shell

The logarithmic cover and the genuine varying real period equivalences
parametrize every punctured cusp point.  Consequently an endpoint formula
on all original period representatives is equality with the actual
punctured gamma map on the whole shell, not merely on a model fibre or
on homology classes.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open CuspUniformization CuspRetraction CuspBoundaryTopVanishing
open SpecialPeriods.CuspFamily

/-- Every actual punctured cusp point has original real-period coordinates. -/
theorem exists_original_period_point (D : Data)
    (q : PuncturedQuotient D.correction D.radius) :
    ∃ (s : LogBase D.radius) (x : RealPlane₄),
      puncturedCuspCover D.correction D.radius (periodLogCover D s x) = q := by
  obtain ⟨p, hp⟩ := puncturedCuspCover_surjective D.correction D.radius q
  let s : LogBase D.radius := ⟨p.val.1, p.property⟩
  let x : RealPlane₄ := (D.periods.periodEquiv s).symm p.val.2
  refine ⟨s, x, ?_⟩
  have he : periodLogCover D s x = p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (D.periods.periodEquiv s).apply_symm_apply p.val.2
  rw [he]
  exact hp

/-- Original representative formulas give agreement with the literal
punctured gamma map at every point of the prescribed whole shell. -/
theorem coreGamma_eq_puncturedGamma_on_shell (D : Data) {η : ℝ}
    (hηr : η < D.radius)
    (core : C(ClosedQuotient D.correction D.radius η, AddCircle (1 : ℝ)))
    (hcore : ∀ (s : LogBase D.radius) (hsη : ‖exponential (s : ℂ)‖ ≤ η)
      (x : RealPlane₄), ‖exponential (s : ℂ)‖ = η →
        core (closedQuotientMap D.correction hηr
          (periodPointPunctured D η s hsη x).1) = (x 0 : AddCircle (1 : ℝ)))
    (q : PuncturedQuotient D.correction D.radius)
    (hq : ‖CuspQuotient.projection D.correction D.radius q.val‖ = η) :
    core ⟨q.val, hq.le⟩ = puncturedGamma D q := by
  obtain ⟨s, x, rfl⟩ := exists_original_period_point D q
  have hs : ‖exponential (s : ℂ)‖ = η := by
    change ‖ToricSpace.time (totalExponentialPoint (periodLogCover D s x))‖ = η at hq
    rw [time_totalExponentialPoint] at hq
    exact hq
  have he : (⟨(puncturedCuspCover D.correction D.radius (periodLogCover D s x)).val,
      hq.le⟩ : ClosedQuotient D.correction D.radius η) =
      closedQuotientMap D.correction hηr (periodPointPunctured D η s hs.le x).1 := by
    apply Subtype.ext
    exact (periodPointPunctured_quotient D η hηr s hs.le x).symm
  rw [he, hcore s hs.le x hs]
  exact (puncturedGamma_realCoordinates D s x).symm

end Wikipedia.HopfProblem.CuspCoinvariantExtension
