import ErdosProblems.Erdos633.ActualGroupOneRationality

/-!
# Necessary group-one angle conditions and the exact V square test

The V integer obstruction follows from the derived rational scale and area
equation, including the factor two in `2 sin(A/4)`.
-/

namespace Erdos633

theorem CongruentTiling.groupOne_U_necessary_angle_condition
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleA)
    (hC : P.angleC = 2 * R.angleB) :
    P.angleB = 2 * P.angleA ∧ Real.sin (P.angleA / 2) ∈ rationalReals := by
  obtain ⟨s, _, _, _, _, hs, _, _, hsrat, _, _⟩ :=
    T.groupOne_U_rational_parameters_ordered hR hrel hA hB hC
  refine ⟨by linarith, ?_⟩
  have heq : Real.sin (P.angleA / 2) = s / 2 := by rw [hA, hs]; ring
  rw [heq]
  exact rationalReals.div_mem hsrat (rationalReals_nat 2)

theorem CongruentTiling.groupOne_V_necessary_integer_condition
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hA : P.angleA = 2 * R.angleA) (hB : P.angleB = R.angleB)
    (hC : P.angleC = R.angleA + R.angleB) :
    P.angleC = P.angleA / 2 + P.angleB ∧ ∃ m n : ℕ, 0 < n ∧
      2 * Real.sin (P.angleA / 4) = (m : ℝ) / n ∧ ¬ IsSquare (2 * n ^ 2 - m ^ 2) := by
  obtain ⟨s, L, hs0, hs1, hL, hs, _, _, hsrat, hLrat, harea⟩ :=
    T.groupOne_V_rational_parameters_ordered hR hrel hA hB hC
  obtain ⟨q, hq⟩ := (mem_rationalReals_iff s).mp hsrat
  obtain ⟨l, hl⟩ := (mem_rationalReals_iff L).mp hLrat
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (show (0 : ℝ) < q by rwa [hq])
  have hq1 : q < 1 := by exact_mod_cast (show (q : ℝ) < 1 by rwa [hq])
  have hl0 : l ≠ 0 := by
    intro hz
    rw [hz, Rat.cast_zero] at hl
    linarith
  have hareaR : (N : ℝ) = (l : ℝ) ^ 2 * (2 - (q : ℝ) ^ 2) := by
    rw [hl, hq]
    exact harea
  have hareaQ : (N : ℚ) = l ^ 2 * (2 - q ^ 2) := by exact_mod_cast hareaR
  obtain ⟨m, n, _, hmn, hcoord⟩ := rational_parameter_coordinates hq0.le hq1
  have htest := groupOne_V_count_isSquare_iff N l hl0 hmn
    (by simpa only [hcoord] using hareaQ)
  have hsP : 2 * Real.sin (P.angleA / 4) = s := by
    rw [hA, show 2 * R.angleA / 4 = R.angleA / 2 by ring, ← hs]
  have hcoordR : (q : ℝ) = (m : ℝ) / n := by
    simpa using congrArg (fun x : ℚ => (x : ℝ)) hcoord
  refine ⟨by linarith, m, n, by omega, ?_, fun h => hN (htest.mpr h)⟩
  rw [hsP, ← hq, hcoordR]

end Erdos633
