/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedNormalization

/-!
# Pinned tensor-square asymptotics with the literal finite singular series

The generic tail tends to one, and the exact normalization identity
transfers the proved graph asymptotic to the finite pinned series.
The prime-progression and coefficient-support bridges remain separate.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem tendsto_compactPinnedTotientTensorSquareSum_finite_normalized
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated] {K : ℕ}
    (h : Fin K) (w m p₀ Y : α → ℕ) (V : α → ℝ)
    (L : α → (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hY : Tendsto Y l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hp₀ : ∀ᶠ a in l, (p₀ a).Prime)
    (hwY : ∀ᶠ a in l, w a ≤ Y a) (hYp₀ : ∀ᶠ a in l, Y a < p₀ a)
    (hcop : ∀ᶠ a in l, (m a * p₀ a - 1).Coprime (primorial (Y a)))
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hmV : ∀ᶠ a in l, Real.log (m a) ≤ V a)
    (hp₀V : ∀ᶠ a in l, Real.log (p₀ a) ≤ 2 * V a)
    (hLlower : ∀ᶠ a in l, ∀ i, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ L a i)
    (hLupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (S : Finset J) (F : J → (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    Tendsto (fun a ↦ pinnedFiniteFourierNormalization h (w a) (m a) (p₀ a) (Y a) (L a) *
      compactTotientSelbergTensorSquareSum (fun p ↦ decide (w a < p))
        (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
        (truncatedPinnedFourierCompanion (m a) (Y a)) S F (L a)) l
      (𝓝 (selbergTensorSquareMainConstant S F)) := by
  have hKp₀ : ∀ᶠ a in l, K ≤ p₀ a := by
    filter_upwards [hw.eventually_ge_atTop K, hwY, hYp₀] with a hwa hYa hpa
    omega
  have hmain := tendsto_compactPinnedTotientTensorSquareSum_normalized h w m p₀ Y V L
    hw hV hm hp₀ hKp₀ hYp₀ hcutoff hmV hp₀V hLlower hLupper S F hcompact hsmooth
  have hlim := hmain.mul (tendsto_genericPinnedFourierSingularTail_one h Y hY)
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [hm, hp₀, hwY, hYp₀, hcop, hw.eventually_ge_atTop (14 * K + 1)]
    with a hma hpa hYa hpYa hca hwa
  rw [mul_right_comm, pinnedFourierNormalization_mul_genericTail h hma hpa hwa hYa hpYa hca]

end

end Erdos4b
