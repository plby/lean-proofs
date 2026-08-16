import Mathlib

namespace Erdos1148

def R_star_disc (d : ℤ) : Set (ℤ × ℤ × ℤ) :=
  { t | t.2.1 ^ 2 - 4 * t.1 * t.2.2 = d ∧ Int.gcd t.1 (Int.gcd t.2.1 t.2.2) = 1 }
def V_disc_plus_1 : Set (ℝ × ℝ × ℝ) :=
  { t | t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 1 }
def Omega_strict : Set (ℝ × ℝ × ℝ) :=
  { t | t ∈ V_disc_plus_1 ∧ |t.1 - t.2.2| < 1 ∧ |t.2.1| < 1 ∧ |t.1 + t.2.2| < 1 }
noncomputable def project_to_hyperboloid (n : ℤ) (t : ℤ × ℤ × ℤ) : ℝ × ℝ × ℝ :=
  let s := Real.sqrt (4 * (n : ℝ))
  ((t.1 : ℝ) / s, (t.2.1 : ℝ) / s, (t.2.2 : ℝ) / s)
def DukeTheoremStatement : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n ≥ N →
  ∃ t ∈ R_star_disc (4 * n),
    project_to_hyperboloid n t ∈ Omega_strict ∧
    t.1 % 2 = t.2.2 % 2
end Erdos1148

attribute [local instance] Classical.propDecidable

namespace Erdos1148

theorem erdos_problem_1148 (h_duke : DukeTheoremStatement) :
  ∃ N : ℤ, ∀ n : ℤ, n ≥ N → ∃ x y z : ℤ, n = x^2 + y^2 - z^2 ∧ max (x^2) (max (y^2) (z^2)) ≤ n := by
  sorry

end Erdos1148
