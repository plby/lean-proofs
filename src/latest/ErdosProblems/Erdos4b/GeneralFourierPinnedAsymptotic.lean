/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedEnvelope
import ErdosProblems.Erdos4b.GeneralFourierTotientCoefficientSquare

/-!
# Totient Fourier asymptotics for the pinned index graph

The matching estimate and the nonzero exceptional integer discharge
the graph hypotheses. This is the analytic asymptotic for that graph;
its identification with the pinned prime-progression sum is separate.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

def roughPinnedFourierEdges {K : ℕ} (h : Fin K) (w m p₀ Y p : ℕ) :
    Finset (PinnedShiftIndex h × PinnedShiftIndex h) :=
  if w < p then truncatedPinnedFourierEdges h m p₀ Y p else ∅

theorem roughPinnedFourierEdges_companion
    {K w m p₀ Y p : ℕ} (h : Fin K) (hKw : K ≤ w)
    (ij : PinnedShiftIndex h × PinnedShiftIndex h)
    (hij : ij ∈ roughPinnedFourierEdges h w m p₀ Y p) :
    truncatedPinnedFourierCompanion m Y p = true := by
  unfold roughPinnedFourierEdges at hij
  split_ifs at hij with hwp
  · exact truncatedPinnedFourierEdges_companion h hKw hwp ij hij
  · exact (Finset.notMem_empty _ hij).elim

theorem card_pinnedShiftIndex_le {K : ℕ} (h : Fin K) :
    Fintype.card (PinnedShiftIndex h) ≤ K := by
  calc
    _ ≤ Fintype.card (Fin K) := Fintype.card_le_of_injective
      (Subtype.val : PinnedShiftIndex h → Fin K) Subtype.val_injective
    _ = _ := Fintype.card_fin K

theorem pinnedDoubledFourierBoxConditions
    {K w m p₀ Y : ℕ} (h : Fin K) {V : ℝ}
    (L : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ)
    (hm : 0 < m) (hp₀ : p₀.Prime) (hKp₀ : K ≤ p₀) (hYp₀ : Y < p₀)
    (hw : 14 * K + 1 ≤ w) (hV : 1 ≤ V)
    (hL : ∀ i, 2 * (V + 1) ^ (3 / 4 : ℝ) ≤ L i) :
    DoubledFourierBoxConditions (pinnedIndexExceptionalModulus h m p₀) w
      (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y)
      L (Real.sqrt V) (fourierQuarterExponent V) := by
  refine ⟨fun i ↦ fourierScale_pos_of_threeQuarter_bound hV (hL i),
    pinnedIndexExceptionalModulus_pos h hm hKp₀,
    by omega, fourierQuarterExponent_nonneg (by linarith), ?_, ?_, ?_,
    fun i ↦ sqrt_box_scale_le_fourierQuarterExponent hV (hL i)⟩
  · simp only [Fintype.card_sum, Nat.cast_add]
    have hcard : (Fintype.card (PinnedShiftIndex h) : ℝ) ≤ K := by
      exact_mod_cast card_pinnedShiftIndex_le h
    have hwR : 14 * (K : ℝ) + 1 ≤ w := by exact_mod_cast hw
    linarith
  · intro p hwp
    rw [roughPinnedFourierEdges, if_pos hwp]
    exact card_truncatedPinnedFourierEdges_le h p.property hp₀ (by omega : K ≤ w) hwp hYp₀
  · intro p hwp hnot
    rw [roughPinnedFourierEdges, if_pos hwp]
    exact truncatedPinnedFourierEdges_generic h hnot

theorem tendsto_compactPinnedTotientTensorSquareSum_normalized
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated] {K : ℕ}
    (h : Fin K) (w m p₀ Y : α → ℕ) (V : α → ℝ)
    (L : α → (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hp₀ : ∀ᶠ a in l, (p₀ a).Prime)
    (hKp₀ : ∀ᶠ a in l, K ≤ p₀ a) (hYp₀ : ∀ᶠ a in l, Y a < p₀ a)
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hmV : ∀ᶠ a in l, Real.log (m a) ≤ V a)
    (hp₀V : ∀ᶠ a in l, Real.log (p₀ a) ≤ 2 * V a)
    (hLlower : ∀ᶠ a in l, ∀ i, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ L a i)
    (hLupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (S : Finset J) (F : J → (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    Tendsto (fun a ↦ doubledFourierNormalization (w a)
      (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
      (truncatedPinnedFourierCompanion (m a) (Y a)) (L a) *
      compactTotientSelbergTensorSquareSum (fun p ↦ decide (w a < p))
        (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
        (truncatedPinnedFourierCompanion (m a) (Y a)) S F (L a)) l
      (𝓝 (selbergTensorSquareMainConstant S F)) := by
  apply tendsto_compactTotientSelbergTensorSquareSum_normalized
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

end

end Erdos4b
