/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSingularTruncation

/-!
# The full-to-finite affine singular-product ratio tends to one

Both the pre-sieve tuple and all arithmetic parameters can vary. The
actual auxiliary-prime correction is included, and positivity is proved
for the finite singular product before dividing by it.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

theorem tendsto_log_fullAffineExceptionalInteger_div_zero
    {α : Type*} {l : Filter α} (K : ℕ) (w m q Y : α → ℕ) (V : α → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hq : ∀ᶠ a in l, (q a).Prime)
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hmV : ∀ᶠ a in l, Real.log (m a) ≤ V a)
    (hqV : ∀ᶠ a in l, Real.log (q a) ≤ V a)
    (hVY : Tendsto (fun a ↦ V a / Y a) l (𝓝 0)) :
    Tendsto (fun a ↦
      Real.log (m a * crossExceptionalModulus (preSievedShifts K (w a)) (m a) (q a) : ℕ) /
        Y a) l (𝓝 0) := by
  have hb : Tendsto (fun a ↦ (1 + 4 * (K : ℝ) ^ 2) * (V a / Y a)) l (𝓝 0) := by
    simpa only [mul_zero] using hVY.const_mul (1 + 4 * (K : ℝ) ^ 2)
  apply squeeze_zero' (Eventually.of_forall fun a ↦
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) _ hb
  filter_upwards [hm, hq, hmV, hqV,
    eventually_log_primorial_le_ambient w V hw hV hcutoff,
    hV.eventually_ge_atTop (Real.log ((K : ℝ) ^ 2 + 1))] with a hma hqa hmVa hqVa hPa hKa
  exact (div_le_div_of_nonneg_right
    (log_fullAffineExceptionalInteger_le K (w a) hma hqa hmVa hqVa hPa hKa)
    (Nat.cast_nonneg (Y a))).trans_eq (mul_div_assoc _ _ _)

theorem tendsto_tprod_roughActualAffineSingularFactor_one
    {α : Type*} {l : Filter α} (K : ℕ) (w m q Y : α → ℕ)
    (hw : Tendsto w l atTop) (hY : Tendsto Y l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hq : ∀ᶠ a in l, (q a).Prime)
    (hwY : ∀ᶠ a in l, w a ≤ Y a) (hYq : ∀ᶠ a in l, Y a < q a)
    (hmass : Tendsto (fun a ↦
      Real.log (m a * crossExceptionalModulus (preSievedShifts K (w a)) (m a) (q a) : ℕ) /
        Y a) l (𝓝 0)) :
    Tendsto (fun a ↦ ∏' p : Nat.Primes,
      roughActualAffineSingularFactor (preSievedShifts K (w a)) (Y a) (m a) (q a) p)
      l (𝓝 1) := by
  let M (a : α) := m a * crossExceptionalModulus (preSievedShifts K (w a)) (m a) (q a)
  have hM : ∀ᶠ a in l, 0 < M a := by
    filter_upwards [hm, hq] with a hma hqa
    exact Nat.mul_pos hma (crossExceptionalModulus_pos (H := preSievedShifts K (w a)) hma hqa)
  have he : ∀ᶠ a in l, ∀ p : Nat.Primes, Y a < p →
      (indexedPreSievedFourierEdges K (w a) (m a) (q a) p).card ≤ Fintype.card (Fin K) := by
    filter_upwards [hwY, hw.eventually_ge_atTop K] with a hwa hKa
    intro p hYp
    simpa only [Fintype.card_fin] using
      card_indexedPreSievedFourierEdges_le p.property hKa (hwa.trans_lt hYp)
  have hg : ∀ᶠ a in l, ∀ p : Nat.Primes, Y a < p → ¬p.val ∣ M a →
      indexedPreSievedFourierEdges K (w a) (m a) (q a) p = ∅ ∧
        affineFourierCompanionSwitch (m a) p = true :=
    Eventually.of_forall fun a p hp hnot ↦ indexedPreSievedFourierEdges_generic hnot
  have hF := tendsto_tprod_roughDoubledFourierSingularFactor_one M Y
    (fun a ↦ indexedPreSievedFourierEdges K (w a) (m a) (q a))
    (fun a ↦ affineFourierCompanionSwitch (m a)) hY hM hmass he hg
  have hqTop : Tendsto q l atTop := tendsto_atTop_mono' l (hYq.mono fun a ha ↦ ha.le) hY
  have hC := tendsto_affineAuxiliaryPrimeCorrection_one K
    (fun a ↦ preSievedShifts K (w a)) m q (fun a ↦ card_preSievedShifts K (w a)) hq hqTop
  have hlim := hC.mul hF
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [hm, hq, hwY, hYq, hw.eventually_ge_atTop (14 * K + 1)]
    with a hma hqa hwa hqaY hKa
  have hlarge : 7 * (Fintype.card (preSievedShifts K (w a) ⊕ preSievedShifts K (w a)) : ℝ) ≤
      w a := by
    simp only [Fintype.card_sum, Fintype.card_coe, card_preSievedShifts, Nat.cast_add]
    have hKr : 14 * (K : ℝ) + 1 ≤ w a := by exact_mod_cast hKa
    linarith
  exact (hasProd_roughActualAffineSingularFactor_larger_cutoff
    hma hqa (by omega : K ≤ w a) hwa hqaY hlarge).tprod_eq.symm

theorem tendsto_fullActualAffineSingularProduct_div_truncated_one
    {α : Type*} {l : Filter α} (K : ℕ) (w m q Y : α → ℕ)
    (hw : Tendsto w l atTop) (hY : Tendsto Y l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (heven : ∀ᶠ a in l, Even (m a))
    (hq : ∀ᶠ a in l, (q a).Prime)
    (hwY : ∀ᶠ a in l, w a ≤ Y a) (hYq : ∀ᶠ a in l, Y a < q a)
    (hmass : Tendsto (fun a ↦
      Real.log (m a * crossExceptionalModulus (preSievedShifts K (w a)) (m a) (q a) : ℕ) /
        Y a) l (𝓝 0)) :
    Tendsto (fun a ↦ fullActualAffineSingularProduct K (w a) (m a) (q a) /
      (largeGapSingularSeries (preSievedShifts K (w a)) (m a) (q a) (Y a) : ℂ)) l (𝓝 1) := by
  have ht := tendsto_tprod_roughActualAffineSingularFactor_one K w m q Y hw hY hm hq hwY hYq hmass
  apply ht.congr'
  filter_upwards [hm, heven, hq, hwY, hYq, hw.eventually_ge_atTop (14 * K + 1)]
    with a hma hme hqa hwa hYqa hKa
  have hlarge : 7 * (Fintype.card (preSievedShifts K (w a) ⊕ preSievedShifts K (w a)) : ℝ) ≤
      w a := by
    simp only [Fintype.card_sum, Fintype.card_coe, card_preSievedShifts, Nat.cast_add]
    have hKr : 14 * (K : ℝ) + 1 ≤ w a := by exact_mod_cast hKa
    linarith
  have hS : (largeGapSingularSeries (preSievedShifts K (w a)) (m a) (q a) (Y a) : ℂ) ≠ 0 := by
    exact_mod_cast (largeGapSingularSeries_preSievedShifts_pos (by omega : 2 * K ≤ w a) hme).ne'
  rw [fullActualAffineSingularProduct_eq_truncated_mul_tail
    hma hqa (by omega : K ≤ w a) hwa hYqa hlarge, mul_div_cancel_left₀ _ hS]

end

end Erdos4b
