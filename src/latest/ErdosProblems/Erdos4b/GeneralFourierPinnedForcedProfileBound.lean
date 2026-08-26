/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedProfileBound
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedIncidence
import ErdosProblems.Erdos4b.GeneralFourierPinnedFiniteAsymptotic

/-!
# The forced pinned profile bound with the literal finite singular series

All graph conditions follow from the arithmetic pinned graph. The generic
tail transfers the full Fourier normalization to the finite singular
series, uniformly in the extra prime and its prescribed residue.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem exists_eventually_pinned_forcedProfile_finite_bound
    {α : Type*} {l : Filter α} {K : ℕ}
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
    (F : ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) × Bool) → ℝ → ℂ)
    (hcompact : ∀ ib, HasCompactSupport (F ib)) (hsmooth : ∀ ib, ContDiff ℝ ∞ (F ib)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in l, ∀ (p : Nat.Primes), w a < p.val →
      ∀ (r N : ℕ), compactProfileTensorCommonBound F (fun i _ ↦ L a i) ≤ N →
        ‖pinnedFiniteFourierNormalization h (w a) (m a) (p₀ a) (Y a) (L a) *
          cutoffForcedSelbergProfileTensorSum
            (selectedFourierPrimeCutoff (fun q ↦ decide (w a < q)) (boundedFourierPrimes N))
            (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
            (truncatedPinnedFourierCompanion (m a) (Y a)) p
            (PinnedForcedLocalEquations h (w a) (m a) (p₀ a) p r) F (fun i _ ↦ L a i)‖ ≤
          C / (p : ℝ) := by
  have hKp₀ : ∀ᶠ a in l, K ≤ p₀ a := by
    filter_upwards [hw.eventually_ge_atTop K, hwY, hYp₀] with a hwa hYa hpa
    omega
  have hdata : ∀ᶠ a in l, DoubledFourierBoxConditions
      (pinnedIndexExceptionalModulus h (m a) (p₀ a)) (w a)
      (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
      (truncatedPinnedFourierCompanion (m a) (Y a)) (L a)
      (Real.sqrt (V a)) (fourierQuarterExponent (V a)) := by
    filter_upwards [hm, hp₀, hKp₀, hYp₀, hw.eventually_ge_atTop (14 * K + 1),
      hV.eventually_ge_atTop 1, hLlower] with a hma hpa hKa hYa hwa hVa hLa
    exact pinnedDoubledFourierBoxConditions h (L a) hma hpa hKa hYa hwa hVa hLa
  have hcoherent : ∀ᶠ a in l, ∀ p : Nat.Primes,
      ∀ ij ∈ roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a) p,
        truncatedPinnedFourierCompanion (m a) (Y a) p = true := by
    filter_upwards [hw.eventually_ge_atTop K] with a hwa
    intro p ij hij
    exact roughPinnedFourierEdges_companion h hwa ij hij
  have hsize : ∀ᶠ a in l, Real.log (pinnedIndexExceptionalModulus h (m a) (p₀ a)) ≤
      (1 + 4 * (Fintype.card (PinnedShiftIndex h) : ℝ) ^ 2) * V a := by
    filter_upwards [hm, hKp₀, hmV, hp₀V, hV.eventually_ge_atTop (Real.log (2 * (K : ℝ)))]
      with a hma hKa hmVa hpVa hKVa
    exact log_pinnedIndexExceptionalModulus_le h hma hKa hmVa hpVa hKVa
  obtain ⟨C, hC, hbound⟩ := exists_eventually_normalized_forcedProfile_bound
    (fun a ↦ pinnedIndexExceptionalModulus h (m a) (p₀ a)) w
    (fun a ↦ roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
    (fun a ↦ truncatedPinnedFourierCompanion (m a) (Y a)) L
    (fun a ↦ fourierQuarterExponent (V a)) V hdata hcoherent hw hV
    (tendsto_fourierQuarterExponent_zero hV) (tendsto_fourierQuarterExponent_mul_log_zero hV)
    hcutoff (by positivity : 0 ≤ 1 + 4 * (Fintype.card (PinnedShiftIndex h) : ℝ) ^ 2)
    hsize hLupper F hcompact hsmooth
  have htail : ∀ᶠ a in l, ‖genericPinnedFourierSingularTail h (Y a)‖ ≤ 2 := by
    have ht := (tendsto_genericPinnedFourierSingularTail_one h Y hY).norm
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : ‖(1 : ℂ)‖ < 2))] with a ha
    exact ha.le
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hbound, htail, hm, hp₀, hwY, hYp₀, hcop,
    hw.eventually_ge_atTop (14 * K + 1)] with a hba hta hma hpa hYa hpYa hca hwa
  intro p hp r N hN
  have hb := hba p hp (PinnedForcedLocalEquations h (w a) (m a) (p₀ a) p r)
    (PinnedForcedPrimeChoiceEquations h (w a) (m a) (p₀ a) p r)
    (fun P hP hpP c ↦ pinnedForcedLocalEquations_reconstructed h P hP
      (w a) (m a) (p₀ a) r ⟨p.val, hpP⟩ c) N hN
  rw [← pinnedFourierNormalization_mul_genericTail h hma hpa hwa hYa hpYa hca,
    mul_right_comm _ (genericPinnedFourierSingularTail h (Y a)), norm_mul]
  exact (mul_le_mul hb hta (norm_nonneg _) (div_nonneg hC (Nat.cast_nonneg _))).trans_eq
    (by ring)

end

end Erdos4b
