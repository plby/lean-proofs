/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedIntegralBound
import ErdosProblems.Erdos4b.GeneralFourierTotientL1Bounds

/-!
# Uniform reciprocal-prime bound for compact smooth forced profiles

The Schwartz representation is chosen once for each fixed profile.
The eventual constant is independent of the forced prime, its local
restriction, and every enlarged coordinate cutoff.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

theorem exists_eventually_normalized_forcedProfile_bound
    {α ι : Type*} [Fintype ι] {l : Filter α}
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (σ V : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (Real.sqrt (V a)) (σ a))
    (hcoherent : ∀ᶠ a in l, ∀ p : Nat.Primes, ∀ ij ∈ edges a p, companion a p = true)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hσ : Tendsto σ l (𝓝 0))
    (hlog : Tendsto (fun a ↦ σ a * Real.log (V a + 1)) l (𝓝 0))
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ᶠ a in l, Real.log (M a) ≤ B * V a)
    (hupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ)
    (hcompact : ∀ ib, HasCompactSupport (F ib)) (hsmooth : ∀ ib, ContDiff ℝ ∞ (F ib)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in l, ∀ (p : Nat.Primes), w a < p.val →
      ∀ (R : ((ι ⊕ ι) → Bool → ℕ) → Prop) (force : DoubledPrimeChoice ι → Prop),
      (∀ (P : Finset ℕ), (∀ r ∈ P, r.Prime) → ∀ hpP : p.val ∈ P,
        ∀ c : P → DoubledPrimeChoice ι,
          R (doubledPrimeChoiceDivisor P c) ↔ force (c ⟨p.val, hpP⟩)) →
      ∀ N : ℕ, compactProfileTensorCommonBound F (fun i _ ↦ L a i) ≤ N →
        ‖doubledFourierNormalization (w a) (edges a) (companion a) (L a) *
          cutoffForcedSelbergProfileTensorSum
            (selectedFourierPrimeCutoff (fun r ↦ decide (w a < r)) (boundedFourierPrimes N))
            (edges a) (companion a) p R F (fun i _ ↦ L a i)‖ ≤ C / (p : ℝ) := by
  classical
  choose f hf using fun ib ↦ exists_schwartz_laplaceFourierProfile (F ib) (hcompact ib) (hsmooth ib)
  have heqF : (fun ib ↦ laplaceFourierProfile (f ib)) = F := by
    funext ib t
    exact hf ib t
  have hcompact' : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)) := by
    intro ib
    simpa only [show laplaceFourierProfile (f ib) = F ib from funext (hf ib)] using hcompact ib
  obtain ⟨C, hC, hbound⟩ := exists_eventually_integral_norm_totientKernel_log_envelope_bound
    M w edges companion L σ V hdata hw hV hσ hlog hcutoff hB hsize hupper f
  refine ⟨4 * Fintype.card (DoubledPrimeChoice ι) * C, by positivity, ?_⟩
  filter_upwards [hdata, hcoherent, hbound, hw.eventually_gt_atTop 0,
    hw.eventually_ge_atTop (2 * Fintype.card (NonemptyDoubledPrimeChoice ι) + 2)]
    with a ha hca hba hw0 hwa
  intro p hp R force hR N hN
  have hN' : compactProfileTensorCommonBound
      (fun ib ↦ laplaceFourierProfile (f ib)) (fun i _ ↦ L a i) ≤ N := by
    simpa only [heqF] using hN
  have hb := norm_normalized_cutoffForcedSelbergProfileTensorSum_le
    (w a) (edges a) (companion a) hca p hp R force hR f hcompact' (L a) ha.scale_pos
    hw0 (by exact_mod_cast hwa) hN' hba.1
  rw [heqF] at hb
  apply hb.trans
  exact (mul_le_mul_of_nonneg_left hba.2 (by positivity)).trans_eq (by ring)

end

end Erdos4b
