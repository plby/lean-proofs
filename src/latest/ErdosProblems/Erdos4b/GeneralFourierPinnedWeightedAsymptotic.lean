/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierWeightedTotientSquare
import ErdosProblems.Erdos4b.GeneralFourierPinnedFiniteAsymptotic

/-!
# Finite pinned asymptotics with explicit profile amplitudes

Each scalar amplitude is fixed with the source profile. The graph
conditions and the finite singular normalization are all discharged;
every amplitude product remains in the limiting constant.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem tendsto_compactPinnedWeightedTotientTensorSquareSum_finite_normalized
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
    (S : Finset J) (c : J → ℂ)
    (F : J → (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    Tendsto (fun a ↦ pinnedFiniteFourierNormalization h (w a) (m a) (p₀ a) (Y a) (L a) *
      compactWeightedTotientSelbergTensorSquareSum (fun p ↦ decide (w a < p))
        (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
        (truncatedPinnedFourierCompanion (m a) (Y a)) S c F (L a)) l
      (𝓝 (weightedSelbergTensorSquareMainConstant S c F)) := by
  have hKp₀ : ∀ᶠ a in l, K ≤ p₀ a := by
    filter_upwards [hw.eventually_ge_atTop K, hwY, hYp₀] with a hwa hYa hpa
    omega
  have hmain : Tendsto (fun a ↦ doubledFourierNormalization (w a)
      (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
      (truncatedPinnedFourierCompanion (m a) (Y a)) (L a) *
      compactWeightedTotientSelbergTensorSquareSum (fun p ↦ decide (w a < p))
        (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
        (truncatedPinnedFourierCompanion (m a) (Y a)) S c F (L a)) l
      (𝓝 (weightedSelbergTensorSquareMainConstant S c F)) := by
    apply tendsto_compactWeightedTotientSelbergTensorSquareSum_normalized
      (fun a ↦ pinnedIndexExceptionalModulus h (m a) (p₀ a)) w
      (fun a ↦ roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
      (fun a ↦ truncatedPinnedFourierCompanion (m a) (Y a)) L
      (fun a ↦ fourierQuarterExponent (V a)) V
    · filter_upwards [hm, hp₀, hKp₀, hYp₀, hw.eventually_ge_atTop (14 * K + 1),
        hV.eventually_ge_atTop 1, hLlower] with a hma hpa hKa hYa hwa hVa hLa
      exact pinnedDoubledFourierBoxConditions h (L a) hma hpa hKa hYa hwa hVa hLa
    · filter_upwards [hw.eventually_ge_atTop K] with a hwa
      intro p ij hij
      exact roughPinnedFourierEdges_companion h hwa ij hij
    · exact hw
    · exact hV
    · exact tendsto_fourierQuarterExponent_zero hV
    · exact tendsto_fourierQuarterExponent_mul_log_zero hV
    · exact hcutoff
    · exact (by positivity : 0 ≤ 1 + 4 * (Fintype.card (PinnedShiftIndex h) : ℝ) ^ 2)
    · filter_upwards [hm, hKp₀, hmV, hp₀V, hV.eventually_ge_atTop (Real.log (2 * (K : ℝ)))]
        with a hma hKa hmVa hpVa hKVa
      exact log_pinnedIndexExceptionalModulus_le h hma hKa hmVa hpVa hKVa
    · exact hLupper
    · exact hcompact
    · exact hsmooth
  have hlim := hmain.mul (tendsto_genericPinnedFourierSingularTail_one h Y hY)
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [hm, hp₀, hwY, hYp₀, hcop, hw.eventually_ge_atTop (14 * K + 1)]
    with a hma hpa hYa hpYa hca hwa
  rw [mul_right_comm, pinnedFourierNormalization_mul_genericTail h hma hpa hwa hYa hpYa hca]

end

end Erdos4b
