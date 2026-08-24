import ErdosProblems.Erdos587.ReducedLatticeBoxWidth

/-! The one-step primitive subrectangle, with all geometric losses explicit. -/

namespace Erdos587

theorem exists_primitive_subrectangle {g u v t H J T : ℕ} {C : ℝ}
    (hg : 0 < g) (hH : 0 < H) (hJ : 0 < J) (huv : u.Coprime v) (hJH : J ≤ H)
    (hsmall : 256 * g ≤ J) (hT : 0 < T) (hTdef : T = g * (t + u * H + v * J))
    (hC : 0 ≤ C) (hspan : (T : ℝ) ≤ C * g * ((u : ℝ) * H + v * J))
    (hshort : (H : ℝ) * (g.gcd u : ℝ) ≤ 4 * Real.sqrt T)
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) :
    ∃ r a b H₀ J₀ T₀ : ℕ, 0 < a ∧ 0 < b ∧ 0 < H₀ ∧ 0 < J₀ ∧ a.Coprime b ∧
      T₀ = r + a * H₀ + b * J₀ ∧
      (∀ x₁ ≤ H₀, ∀ y₁ ≤ J₀, ∀ x₂ ≤ H₀, ∀ y₂ ≤ J₀,
        r + a * x₁ + b * y₁ = r + a * x₂ + b * y₂ → x₁ = x₂ ∧ y₁ = y₂) ∧
      (∀ x ≤ H₀, ∀ y ≤ J₀, ∃ X ≤ H, ∃ Y ≤ J,
        g ^ 2 * (r + a * x + b * y) = g * (t + u * X + v * Y)) ∧
      (T : ℝ) / (4 * (g : ℝ) ^ 2) ≤ T₀ ∧ (T₀ : ℝ) ≤ (T : ℝ) / (g : ℝ) ^ 2 ∧
      (T₀ : ℝ) ≤ (256 * C) * ((a : ℝ) * H₀ + b * J₀) ∧
      (H : ℝ) * J / (8192 * g) ≤ (H₀ : ℝ) * J₀ ∧
      min ((H : ℝ) / (128 * g)) ((H : ℝ) * J / (512 * Real.sqrt T)) ≤ H₀ ∧
      min ((H : ℝ) / (128 * g)) ((H : ℝ) * J / (512 * Real.sqrt T)) ≤ J₀ := by
  obtain ⟨P⟩ := exists_reduced_lattice_box t hg hH hJ huv hJH hsmall
  have hsteps := P.positive_steps hproper
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hTcast : (T : ℝ) = (g : ℝ) * ((t : ℝ) + u * H + v * J) := by exact_mod_cast hTdef
  have hmaximum := P.maximum_bounds
  rw [← hTcast] at hmaximum
  have hwidths := P.widths_lower_of_short_side hTR hshort
  refine ⟨P.base, P.firstStep, P.secondStep, P.firstWidth, P.secondWidth, P.maximum,
    hsteps.1, hsteps.2, P.firstWidth_pos, P.secondWidth_pos, P.coprime_steps,
    rfl, P.proper hproper, P.image, hmaximum.1, hmaximum.2, ?_, P.volume_lower, hwidths.1, hwidths.2⟩
  apply P.span_control hC
  rwa [← hTcast]

end Erdos587
