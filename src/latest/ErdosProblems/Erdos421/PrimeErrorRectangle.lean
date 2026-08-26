import ErdosProblems.Erdos421.PrimeErrorPerronIntegrand
import ErdosProblems.Erdos421.ZetaPrimeErrorStrip

/-! # The unconditional finite contour bound across the cancelled zeta pole -/

namespace Erdos421

open Complex MeasureTheory Set

theorem exists_primeErrorPerron_rectangle_bound :
    ∃ H₀ > 1, ∃ C > 0, ∀ x a b H : ℝ,
      1 ≤ x → 1 / 2 ≤ a → a ≤ b → H₀ ≤ H →
      1 - logPowerZeroWidth H / 64 ≤ a → b ≤ 1 + logPowerZeroWidth H / 64 →
      ‖∫ y : ℝ in -H..H, primeErrorPerronIntegrand x ((b : ℂ) + y * I)‖ ≤
        4 * Real.pi * x ^ a * (C * H) + 2 * (b - a) * (x ^ b * (C * H) / H ^ 2) := by
  obtain ⟨H₀, hH₀, C, hC, hstrip⟩ := exists_zetaPrimeError_full_strip_bound
  refine ⟨H₀, hH₀, C, hC, ?_⟩
  intro x a b H hx ha hab hH hlo hhi
  have hHp : 0 < H := by linarith
  have hpoint : ∀ s ∈ Icc a b ×ℂ Icc (-H) H,
      riemannZeta₁ s ≠ 0 ∧ ‖zetaPrimeError s‖ ≤ C * H := by
    intro s hs
    have hβ : |s.re - 1| ≤ logPowerZeroWidth H / 64 := by
      apply abs_le.mpr
      constructor <;> linarith [hs.1.1, hs.1.2]
    have ht : |s.im| ≤ H := abs_le.mpr hs.2
    have hb := hstrip H s.re s.im hH hβ ht
    simpa only [re_add_im] using hb
  exact primeErrorPerronIntegrand_rectangle_bound hx ha hab hHp (by positivity)
    (fun s hs ↦ (hpoint s hs).1) (fun s hs ↦ (hpoint s hs).2)

end Erdos421
