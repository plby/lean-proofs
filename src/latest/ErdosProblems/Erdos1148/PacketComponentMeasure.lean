import ErdosProblems.Erdos1148.DiscriminantPacket

/-! # Identifying packet components with arbitrary integral-form lifts -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma ClosedFlowOrbit.measure_eq_of_integral_formAction (o p : ClosedFlowOrbit) (γ : SL(2, ℤ))
    (h : formAction o.lift (splitForm ℝ) =
      formAction ((γ : SL(2, ℝ)) * p.lift) (splitForm ℝ)) : o.measure = p.measure := by
  let q : ClosedFlowOrbit :=
    { lift := (γ : SL(2, ℝ)) * p.lift
      period := p.period
      period_pos := p.period_pos
      period_group := (flowPeriodGroup_integral_mul γ p.lift).trans p.period_group }
  exact (o.measure_eq_of_formAction_eq q h).trans (q.measure_eq_of_integral_mul p γ rfl)

lemma ClosedFlowOrbit.measure_eq_of_scaled_integral_forms (o p : ClosedFlowOrbit)
    {ρ : ℝ} (hρ : ρ ≠ 0) {t u : ℤ × ℤ × ℤ}
    (ht : ρ • formAction o.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (hu : ρ • formAction p.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) u)
    (γ : SL(2, ℤ)) (hγ : formAction γ u = t) : o.measure = p.measure := by
  have hscale : ρ • formAction o.lift (splitForm ℝ) =
      ρ • formAction ((γ : SL(2, ℝ)) * p.lift) (splitForm ℝ) := by
    rw [ht, formAction_mul, ← formAction_smul, hu, ← mapCoeffs_formAction, hγ]
  have heq := congrArg (fun v : ℝ × ℝ × ℝ => ρ⁻¹ • v) hscale
  apply o.measure_eq_of_integral_formAction p γ
  simpa only [smul_smul, inv_mul_cancel₀ hρ, one_smul] using heq

theorem ClosedFlowOrbit.measure_eq_packetOrbit {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (o : ClosedFlowOrbit) (t : IntegralDiscrForm d) (q : IntegralFormOrbits d)
    (hq : integralFormOrbitMk t = q)
    (ho : Real.sqrt (d : ℝ) • formAction o.lift (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t.1) : o.measure = (packetOrbit hd hns q).measure := by
  have hrep : integralFormOrbitMk q.out = integralFormOrbitMk t :=
    (Quotient.out_eq q).trans hq.symm
  obtain ⟨γ, hγ⟩ := (integralFormOrbitMk_eq_iff q.out t).mp hrep
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact o.measure_eq_of_scaled_integral_forms (packetOrbit hd hns q)
    (Real.sqrt_pos.mpr hdR).ne' ho (packetOrbit_form hd hns q) γ hγ

end Erdos1148.DukeArithmetic
