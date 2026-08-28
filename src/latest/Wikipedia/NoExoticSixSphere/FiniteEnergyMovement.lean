import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Movement bounds for a finite sequence of energy-controlled steps

If each step increases energy by at most a small allowance, a high-energy
endpoint forces every earlier step to have lost little energy. The associated
small-movement bounds therefore accumulate to a bound from the original point.
-/

namespace NoExoticSixSphere.FiniteEnergyMovement

variable {Y : Type*}

theorem energy_le_after (energy : Y → ℝ) (z : ℕ → Y) (n : ℕ) (ξ : ℝ)
    (hstep : ∀ j < n, energy (z (j + 1)) ≤ energy (z j) + ξ)
    {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    energy (z j) ≤ energy (z i) + ((j - i : ℕ) : ℝ) * ξ := by
  revert hjn
  induction j, hij using Nat.le_induction with
  | base => intro _; simp
  | succ j hij ih =>
    intro hjn
    have hprev := ih (by omega)
    have hnext := hstep j (by omega)
    have heq : j + 1 - i = (j - i) + 1 := by omega
    rw [heq, Nat.cast_add, Nat.cast_one]
    nlinarith

variable [PseudoMetricSpace Y]

theorem displacement_le_of_high_endpoint (energy : Y → ℝ) (z : ℕ → Y) (n : ℕ)
    (ξ ζ ρ A B : ℝ) (hξ : 0 ≤ ξ)
    (hstep : ∀ j < n, energy (z (j + 1)) ≤ energy (z j) + ξ)
    (hmove : ∀ j < n, energy (z j) - energy (z (j + 1)) ≤ 2 * ζ →
      dist (z (j + 1)) (z j) ≤ ρ)
    (hstart : energy (z 0) ≤ B) (hfinish : A ≤ energy (z n))
    (hbudget : B - A + 2 * (n : ℝ) * ξ ≤ 2 * ζ) :
    dist (z n) (z 0) ≤ (n : ℝ) * ρ := by
  have hsmall (j : ℕ) (hj : j < n) : dist (z (j + 1)) (z j) ≤ ρ := by
    apply hmove j hj
    have hup := energy_le_after energy z n ξ hstep (Nat.zero_le j) hj.le
    simp only [Nat.sub_zero] at hup
    have hback := energy_le_after energy z n ξ hstep (Nat.succ_le_of_lt hj) le_rfl
    have hjξ : (j : ℝ) * ξ ≤ (n : ℝ) * ξ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) hξ
    have hdiff : ((n - (j + 1) : ℕ) : ℝ) * ξ ≤ (n : ℝ) * ξ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n (j + 1)) hξ
    linarith
  have hdist : ∀ j ≤ n, dist (z j) (z 0) ≤ (j : ℝ) * ρ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      calc
        dist (z (j + 1)) (z 0) ≤ dist (z (j + 1)) (z j) + dist (z j) (z 0) :=
          dist_triangle _ _ _
        _ ≤ ρ + (j : ℝ) * ρ := add_le_add (hsmall j (by omega)) (ih (by omega))
        _ = ((j + 1 : ℕ) : ℝ) * ρ := by rw [Nat.cast_add, Nat.cast_one]; ring
  exact hdist n le_rfl

end NoExoticSixSphere.FiniteEnergyMovement
