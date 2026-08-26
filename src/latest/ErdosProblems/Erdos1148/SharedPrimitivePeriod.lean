import ErdosProblems.Erdos1148.PrimitivePellPeriods
import ErdosProblems.Erdos1148.ClosedFlowOrbit

/-! # All primitive forms of a fixed discriminant have the same period -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma even_middle_sub_discr (t : ℤ × ℤ × ℤ) : Even (t.2.1 - discr t) := by
  have hb : t.2.1 % 2 = 0 ∨ t.2.1 % 2 = 1 := by omega
  rcases hb with hb | hb <;>
    simp [Int.even_iff, discr, pow_two, Int.sub_emod, Int.mul_emod, hb]

lemma even_trace_sub_middle_iff {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) (T U : ℤ) :
    Even (T - t.2.1 * U) ↔ Even (T - d * U) := by
  have hbd : Even (t.2.1 - d) := ht ▸ even_middle_sub_discr t
  constructor
  · intro h
    rw [show T - d * U = (T - t.2.1 * U) + (t.2.1 - d) * U by ring]
    exact h.add (hbd.mul_right U)
  · intro h
    rw [show T - t.2.1 * U = (T - d * U) - (t.2.1 - d) * U by ring]
    exact h.sub (hbd.mul_right U)

theorem primitive_flowPeriod_iff_discr_coordinates {d : ℤ} (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (s : ℝ) : s ∈ flowPeriodGroup g ↔
      ∃ T U : ℤ, (T : ℝ) = 2 * Real.cosh (s / 2) ∧
        (U : ℝ) = -2 * Real.sinh (s / 2) / Real.sqrt (d : ℝ) ∧
        T ^ 2 - d * U ^ 2 = 4 ∧ Even (T - d * U) := by
  rw [primitive_flowPeriod_iff_pell_coordinates hd ht g hg s]
  simp only [even_trace_sub_middle_iff htd]

theorem primitive_flowPeriodGroups_eq {d : ℤ} (hd : 0 < d)
    {t u : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (hu : PrimitiveIntegralForm u)
    (htd : discr t = d) (hud : discr u = d) (g h : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (hh : Real.sqrt (d : ℝ) • formAction h (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) u) :
    flowPeriodGroup g = flowPeriodGroup h := by
  ext s
  rw [primitive_flowPeriod_iff_discr_coordinates hd ht htd g hg,
    primitive_flowPeriod_iff_discr_coordinates hd hu hud h hh]

theorem ClosedFlowOrbit.primitive_period_eq {d : ℤ} (hd : 0 < d)
    {t u : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (hu : PrimitiveIntegralForm u)
    (htd : discr t = d) (hud : discr u = d) (o p : ClosedFlowOrbit)
    (ho : Real.sqrt (d : ℝ) • formAction o.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (hp : Real.sqrt (d : ℝ) • formAction p.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) u) :
    o.period = p.period :=
  o.period_eq_of_group_eq p (primitive_flowPeriodGroups_eq hd ht hu htd hud o.lift p.lift ho hp)

end Erdos1148.DukeArithmetic
