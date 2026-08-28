import Wikipedia.HopfProblem.CuspCoinvariantExtensionPuncturedBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspCoordinates

/-!
# The punctured gamma coordinate is invariant under the native real vertical flow

The flow below is the restriction of the original toric cusp flow.
Its logarithmic-cover formula adds a multiple of the actual fourth
period column. For real time this changes only the fourth real period
coordinate, and hence fixes the original gamma coordinate everywhere
on the punctured cusp.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open CuspUniformization SpecialPeriods.CuspFamily

/-- Restriction of the original complex vertical cusp flow to its actual punctured locus. -/
def puncturedFlow (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (s : ℂ) :
    C(PuncturedQuotient C r, PuncturedQuotient C r) where
  toFun q := ⟨SpecialPeriods.Threefold.VerticalAction.Cusp.flow C r s q.1, by
    change CuspQuotient.projection C r
      (SpecialPeriods.Threefold.VerticalAction.Cusp.flow C r s q.1) ≠ 0
    rw [SpecialPeriods.Threefold.VerticalAction.Cusp.projection_flow]
    exact q.2⟩
  continuous_toFun :=
    ((SpecialPeriods.Threefold.VerticalAction.Cusp.flow_continuous C r s).comp
      continuous_subtype_val).subtype_mk _

@[simp] theorem puncturedFlow_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (s : ℂ) (q : PuncturedQuotient C r) :
    (puncturedFlow C r s q : CuspQuotient.QuotientSpace C r) =
      SpecialPeriods.Threefold.VerticalAction.Cusp.flow C r s q := rfl

/-- The restriction retains the exact original logarithmic-cover flow formula. -/
theorem puncturedFlow_cover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (s : ℂ) (p : LogCover r) :
    puncturedFlow C r s (puncturedCuspCover C r p) =
      puncturedCuspCover C r
        (SpecialPeriods.Threefold.VerticalAction.Cusp.logFlow r s p) := by
  apply Subtype.ext
  exact SpecialPeriods.Threefold.VerticalAction.Cusp.flow_totalCuspCover C r s p

/-- The original fourth column of every varying cusp period map is the real delta direction. -/
theorem cuspPeriodEquiv_real_delta (D : Data) (s : LogBase D.radius) (t : ℝ) :
    D.periods.periodEquiv s (Pi.single (3 : Fin 4) t) =
      (t : ℂ) • (![0, 1] : ComplexPlane₂) := by
  rw [D.periodEquiv_matrix]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Real native flow changes precisely the original fourth real period coordinate. -/
theorem puncturedFlow_realCoordinates (D : Data) (s : LogBase D.radius)
    (x : RealPlane₄) (t : ℝ) :
    puncturedFlow D.correction D.radius (t : ℂ)
      (puncturedCuspCover D.correction D.radius
        ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩) =
      puncturedCuspCover D.correction D.radius
        ⟨((s : ℂ), D.periods.periodEquiv s (x + Pi.single (3 : Fin 4) t)), s.property⟩ := by
  rw [puncturedFlow_cover]
  have hv : D.periods.periodEquiv s (x + Pi.single (3 : Fin 4) t) =
      D.periods.periodEquiv s x + (t : ℂ) • (![0, 1] : ComplexPlane₂) := by
    rw [map_add, cuspPeriodEquiv_real_delta]
  exact congrArg (fun z : ComplexPlane₂ => puncturedCuspCover D.correction D.radius
    ⟨((s : ℂ), z), s.property⟩) hv.symm

/-- The original gamma coordinate is invariant on the entire native punctured cusp. -/
theorem puncturedGamma_realFlow (D : Data) (t : ℝ)
    (q : PuncturedQuotient D.correction D.radius) :
    puncturedGamma D (puncturedFlow D.correction D.radius (t : ℂ) q) =
      puncturedGamma D q := by
  obtain ⟨p, rfl⟩ := puncturedCuspCover_surjective D.correction D.radius q
  rw [puncturedFlow_cover, puncturedGamma_cover, puncturedGamma_cover]
  change (((D.periods.periodEquiv ⟨p.1.1, p.2⟩).symm
    (p.1.2 + (t : ℂ) • (![0, 1] : ComplexPlane₂))) 0 : AddCircle (1 : ℝ)) =
      (((D.periods.periodEquiv ⟨p.1.1, p.2⟩).symm p.1.2) 0 : AddCircle (1 : ℝ))
  rw [← cuspPeriodEquiv_real_delta D ⟨p.1.1, p.2⟩ t, map_add,
    LinearEquiv.symm_apply_apply]
  simp

end Wikipedia.HopfProblem.CuspCoinvariantExtension
