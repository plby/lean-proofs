import ErdosProblems.Erdos633b.Trigonometry
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! Explicit positive integral 120-degree side triples from rational half-angle data. -/

namespace Erdos633b.GroupTwoParameters

def a (u v : ℕ) : ℕ := 4 * u * (u + v)
def b (u v : ℕ) : ℕ := v * (4 * u + 3 * v)
def c (u v : ℕ) : ℕ := 3 * (u + v) ^ 2 + u ^ 2

theorem a_pos (u v : ℕ) (hu : 0 < u) (hv : 0 < v) : 0 < a u v := by
  dsimp only [a]
  positivity

theorem b_pos (u v : ℕ) (hu : 0 < u) (hv : 0 < v) : 0 < b u v := by
  dsimp only [b]
  positivity

theorem c_pos (u v : ℕ) (hu : 0 < u) (hv : 0 < v) : 0 < c u v := by
  dsimp only [c]
  positivity

theorem relation (u v : ℕ) : c u v ^ 2 = a u v ^ 2 + a u v * b u v + b u v ^ 2 := by
  dsimp only [a, b, c]
  ring

theorem cosine_ratio (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ((a u v : ℝ) + 2 * b u v) / (2 * c u v) =
      (3 - ((u : ℝ) / (u + v)) ^ 2) / (3 + ((u : ℝ) / (u + v)) ^ 2) := by
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hvr : (0 : ℝ) < v := by exact_mod_cast hv
  have huv : (u : ℝ) + v ≠ 0 := (add_pos hur hvr).ne'
  dsimp only [a, b, c]
  push_cast
  field_simp
  ring

theorem half_parameter_bounds (α : ℝ) (hα : 0 < α) (hα3 : α < Real.pi / 3) :
    0 < Real.sqrt 3 * Real.tan (α / 2) ∧ Real.sqrt 3 * Real.tan (α / 2) < 1 := by
  have hd : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ht : 0 < Real.tan (α / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [Real.pi_pos])
  have hlt := Real.strictMonoOn_tan
    (show α / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
    (show Real.pi / 6 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos]) (by linarith : α / 2 < Real.pi / 6)
  rw [Real.tan_pi_div_six] at hlt
  exact ⟨mul_pos hd ht, by
    have hh := mul_lt_mul_of_pos_left hlt hd
    simpa only [mul_one_div_cancel hd.ne'] using hh⟩

theorem positive_parts (q : ℚ) (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ (q : ℝ) = (u : ℝ) / (u + v) := by
  have hqr : 0 < q := by exact_mod_cast hq
  have hnum : 0 < q.num := Rat.num_pos.mpr hqr
  let u := q.num.toNat
  let k := q.den
  have hu : 0 < u := by dsimp only [u]; omega
  have hk : 0 < k := q.pos
  have huc : (u : ℝ) = q.num := by
    have h := Int.toNat_of_nonneg hnum.le
    exact_mod_cast h
  have hqv : (q : ℝ) = (u : ℝ) / k := by rw [Rat.cast_def, huc]
  have huk : u < k := by
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    rw [hqv] at hq1
    exact_mod_cast (div_lt_one hkr).mp hq1
  refine ⟨u, k - u, hu, Nat.sub_pos_of_lt huk, ?_⟩
  rw [show (u : ℝ) + (k - u : ℕ) = k by
    rw [Nat.cast_sub huk.le]
    ring]
  exact hqv

end Erdos633b.GroupTwoParameters
