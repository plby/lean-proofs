import ErdosProblems.Erdos633b.TriquadraticAngles
import ErdosProblems.Erdos633b.TriquadraticTiling
import ErdosProblems.Erdos633b.Specification
import ErdosProblems.Erdos633b.Arithmetic
import Mathlib.Algebra.Ring.Int.Parity

/-!
The complete constructed family has the exact case-(7) angles and nonsquare count.
Transport to an arbitrary triangle satisfying that case is still a separate obligation.
-/

namespace Erdos633b.TriquadraticCoordinates

theorem rationalOuter_angle_relations (a c : ℕ) (ha : 0 < a) (hac : a < c) :
    (rationalOuter a c ha hac).angle 2 =
        (rationalOuter a c ha hac).angle 0 / 2 + (rationalOuter a c ha hac).angle 1 ∧
      2 * Real.sin ((rationalOuter a c ha hac).angle 0 / 4) = (a : ℝ) / c := by
  have h := rational_parameter_bounds a c ha hac
  exact outer_angle_relations c ((a : ℝ) / c) (Real.sqrt (4 - ((a : ℝ) / c) ^ 2))
    h.1 h.2.1 h.2.2.1 (Real.sqrt_pos.mpr h.2.2.2) (Real.sq_sqrt h.2.2.2.le)

theorem rationalOuter_eightCases (a c : ℕ) (ha : 0 < a) (hac : a < c)
    (hn : ¬ IsSquare (2 * (c : ℤ) ^ 2 - (a : ℤ) ^ 2)) :
    EightCases (rationalOuter a c ha hac) := by
  obtain ⟨hrel, hparam⟩ := rationalOuter_angle_relations a c ha hac
  refine ⟨Equiv.refl _, ?_⟩
  dsimp only [Equiv.refl_apply]
  right; right; right; right; right; right; left
  exact ⟨hrel, a, c, ha, ha.trans hac, hparam, hn⟩

theorem rational_count_nonsquare (a c : ℕ) (hac : a < c)
    (hn : ¬ IsSquare (2 * (c : ℤ) ^ 2 - (a : ℤ) ^ 2)) :
    ¬ IsSquare (2 * c ^ 2 - a ^ 2) := by
  have hle : a ^ 2 ≤ 2 * c ^ 2 := by nlinarith
  have hcast : ((2 * c ^ 2 - a ^ 2 : ℕ) : ℤ) = 2 * (c : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
    rw [Nat.cast_sub hle]
    push_cast
    rfl
  intro h
  apply hn
  rw [← hcast]
  exact Int.isSquare_natCast_iff.mpr h

/-- An actual nonsquare tiling for every admissible rational case-(7) representative. -/
theorem rational_case_seven (a c : ℕ) (ha : 0 < a) (hac : a < c) (hdiv : c ∣ a ^ 2)
    (hn : ¬ IsSquare (2 * (c : ℤ) ^ 2 - (a : ℤ) ^ 2)) :
    EightCases (rationalOuter a c ha hac) ∧ HasNonsquareTiling (rationalOuter a c ha hac) :=
  ⟨rationalOuter_eightCases a c ha hac hn,
    rationalOuter_hasNonsquareTiling a c ha hac hdiv (rational_count_nonsquare a c hac hn)⟩

/-- Clear denominators without changing the prescribed parameter or its nonsquare class. -/
theorem case_seven_representative (m k : ℕ) (hm : 0 < m) (hmk : m < k)
    (hn : ¬ IsSquare (2 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2)) :
    ∃ T : Triangle, T.angle 2 = T.angle 0 / 2 + T.angle 1 ∧
      2 * Real.sin (T.angle 0 / 4) = (m : ℝ) / k ∧ HasNonsquareTiling T := by
  have hk : 0 < k := hm.trans hmk
  have ha : 0 < m * k := Nat.mul_pos hm hk
  have hac : m * k < k ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hmk hk
  have hdiv : k ^ 2 ∣ (m * k) ^ 2 := ⟨m ^ 2, by ring⟩
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkkZ : ((k ^ 2 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hk.ne'
  have hrq : (((m * k : ℕ) : ℤ) : ℚ) / ((k ^ 2 : ℕ) : ℤ) = (m : ℚ) / k := by
    push_cast
    field_simp
  have hiff := triquadratic_integer_representation_isSquare
    ((m * k : ℕ) : ℤ) ((k ^ 2 : ℕ) : ℤ) m k hkkZ hkZ hrq
  have hn' : ¬ IsSquare (2 * ((k ^ 2 : ℕ) : ℤ) ^ 2 - ((m * k : ℕ) : ℤ) ^ 2) :=
    fun hh => hn (hiff.mp hh)
  have hresult := rational_case_seven (m * k) (k ^ 2) ha hac hdiv hn'
  obtain ⟨hrel, hparam⟩ := rationalOuter_angle_relations (m * k) (k ^ 2) ha hac
  have hrr : ((m * k : ℕ) : ℝ) / (k ^ 2 : ℕ) = (m : ℝ) / k := by
    push_cast
    field_simp
  exact ⟨rationalOuter (m * k) (k ^ 2) ha hac, hrel, hparam.trans hrr, hresult.2⟩

end Erdos633b.TriquadraticCoordinates
