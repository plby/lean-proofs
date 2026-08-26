/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierEndpointDecay

/-!
# The actual normalized CRT endpoint error tends to zero

The uniform affine normalization bound and the coefficient-mass bound
are composed with the exponential endpoint envelope. The tuple may
vary with the pre-sieve cutoff; no limiting index type is assumed here.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

theorem tendsto_sourceAnalyticSelbergNormalizedEndpoint_zero
    {α J : Type*} {l : Filter α} (K : ℕ) (hK : 0 < K) (S : Finset J)
    (w m q T : α → ℕ) (P : α → Finset ℕ) (V LE : α → ℝ)
    (F : (a : α) → J → preSievedShifts K (w a) → ℝ → ℝ) (G : ℝ → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hP : ∀ a, ∀ p ∈ P a, p.Prime)
    (hm : ∀ᶠ a in l, 0 < m a) (hmeven : ∀ᶠ a in l, Even (m a))
    (hq : ∀ᶠ a in l, (q a).Prime) (hwq : ∀ᶠ a in l, w a < q a)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ a in l, ∀ (d e : preSievedShifts K (w a) → ℕ),
      |sourceAnalyticSelbergCoefficient S (F a) G (V a) (LE a) d e| ≤ C)
    (hFsupport : ∀ᶠ a in l, ∀ j ∈ S, ∀ u : preSievedShifts K (w a) → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F a j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (hdata : ∀ᶠ a in l, 0 < LE a ∧ LE a ≤ V a ∧ (K : ℝ) * LE a ≤ V a / 40 ∧
      (primorial (w a) : ℝ) ≤ Real.exp (V a / 8) ∧ Real.exp (V a / 2) ≤ T a) :
    Tendsto (fun a ↦
      fullAffineFourierNormalization K (w a) (m a) (q a) (twoFamilySelbergScales (V a) (LE a)) *
        (doubledSelbergGeneralNormalizationError (preSievedShifts K (w a))
          (cutoffDivisorTupleSupport (preSievedShifts K (w a)) (P a))
          (cutoffCompanionDivisorTupleSupport (preSievedShifts K (w a)) (P a) (m a))
          (sourceAnalyticSelbergCoefficient S (F a) G (V a) (LE a))
          (primorial (w a)) (m a) (q a) (T a) : ℂ) / (T a : ℂ)) l (𝓝 0) := by
  obtain ⟨W, hW⟩ := exists_uniform_actualAffineFourierNormalization_bound K
  have henvelope := tendsto_normalized_sourceEndpointEnvelope_zero K hC V LE
    (fun a ↦ (primorial (w a) : ℝ)) (fun a ↦ (T a : ℝ)) hV
    (hdata.mono fun a ha ↦ ⟨ha.1.le, ha.2.1, ha.2.2.1, Nat.cast_nonneg _, ha.2.2.2⟩)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _) _ henvelope
  filter_upwards [hm, hmeven, hq, hwq, hbound, hFsupport, hdata,
    hw.eventually_ge_atTop (max W 2), hV.eventually_ge_atTop 1]
    with a hma hmea hqa hwqa hba hFa ha hwa hVa
  have hVa0 : 0 < V a := by linarith
  have hTa : 0 < T a := by
    exact_mod_cast (Real.exp_pos (V a / 2)).trans_le ha.2.2.2.2
  have hscales : ∀ i : Fin K ⊕ Fin K, 0 ≤ twoFamilySelbergScales (V a) (LE a) i := by
    intro i
    cases i
    · exact hVa0.le
    · exact ha.1.le
  have hupper : ∀ i : Fin K ⊕ Fin K, twoFamilySelbergScales (V a) (LE a) i ≤ V a := by
    intro i
    cases i
    · exact le_rfl
    · exact ha.2.1
  have hprod : (∏ i : Fin K ⊕ Fin K, twoFamilySelbergScales (V a) (LE a) i) ≤
      V a ^ (2 * K) := by
    calc
      _ ≤ ∏ _i : Fin K ⊕ Fin K, V a :=
        Finset.prod_le_prod (fun i hi ↦ hscales i) (fun i hi ↦ hupper i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_sum,
        Fintype.card_fin, ← two_mul]
  have hnorm := (hW ((le_max_left _ _).trans hwa) hma hqa hwqa
    (twoFamilySelbergScales (V a) (LE a)) hscales).trans
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4))
  have herror := sourceAnalyticSelbergEndpointError_abs_le (preSievedShifts K (w a)) (P a)
    (hP a) (primorial (w a)) (m a) (q a) (T a) (primorial_pos _) S (F a) G
    hC hVa0 ha.1 hba hFa hGsupport
  simp only [Fintype.card_coe, card_preSievedShifts] at herror
  have h := norm_fullAffineFourierNormalization_mul_error_div_le
    (twoFamilySelbergScales (V a) (LE a)) hK ((le_max_right _ _).trans hwa)
    hma hmea hTa hnorm (sq_nonneg _) herror
  convert h using 1
  ring

end

end Erdos4b
