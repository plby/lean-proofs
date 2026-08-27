import ErdosProblems.Erdos587.HooleyCommonFactorTerminal
import ErdosProblems.Erdos587.HomogeneousTerminal

/-! Square witnesses in homogeneous rank-two progressions with fixed log-log thresholds. -/

namespace Erdos587

theorem exists_delta_homogeneous_rank_two_terminal (C : ℝ) (hC : 0 < C) :
    ∃ Tmin : ℝ, ∀ (r q₁ q₂ H J T : ℕ), Tmin ≤ (T : ℝ) →
      0 < q₁ → 0 < q₂ → 0 < H → 0 < J → q₁.gcd q₂ ∣ r →
      T = r + q₁ * H + q₂ * J →
      (T : ℝ) ≤ C * ((q₁ * H + q₂ * J : ℕ) : ℝ) →
      (∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
        r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ → x₁ = x₂ ∧ y₁ = y₂) →
      (T : ℝ) ^ (1 / 4 : ℝ) * (max 1 (Real.log (Real.log (T : ℝ)))) ^ 11 ≤ H →
      (T : ℝ) ^ (1 / 4 : ℝ) * (max 1 (Real.log (Real.log (T : ℝ)))) ^ 11 ≤ J →
      (T : ℝ) ^ (3 / 4 : ℝ) * (max 1 (Real.log (Real.log (T : ℝ)))) ^ 11 ≤ (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = r + q₁ * x + q₂ * y := by
  obtain ⟨Tmin, hterminal⟩ := exists_delta_common_factor_terminal C hC
  refine ⟨Tmin, ?_⟩
  intro r q₁ q₂ H J T hbig hq₁ hq₂ hH hJ hhom hTdef hspan hproper hsideH hsideJ hprod
  obtain ⟨g, t, u, v, hg, hu, hv, huv, hr, hq₁eq, hq₂eq⟩ :=
    homogeneous_rank_two_factorization hq₁ hq₂ hhom
  have heval (x y : ℕ) : r + q₁ * x + q₂ * y = g * (t + u * x + v * y) := by
    rw [hr, hq₁eq, hq₂eq]
    ring
  have hTdef' : T = g * (t + u * H + v * J) := hTdef.trans (heval H J)
  have hspan' : (T : ℝ) ≤ C * g * ((u : ℝ) * H + v * J) := by
    calc
      (T : ℝ) ≤ C * ((q₁ * H + q₂ * J : ℕ) : ℝ) := hspan
      _ = C * g * ((u : ℝ) * H + v * J) := by
        rw [hq₁eq, hq₂eq]
        push_cast
        ring
  have hproper' : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂ := by
    intro x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ heq
    apply hproper x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂
    rw [heval, heval, heq]
  obtain ⟨x, hx, y, hy, z, hz, heq⟩ := hterminal g t u v H J T hbig hg hu hv hH hJ huv
    hTdef' hspan' hproper' hsideH hsideJ hprod
  exact ⟨x, hx, y, hy, z, hz, heq.trans (heval x y).symm⟩

end Erdos587
