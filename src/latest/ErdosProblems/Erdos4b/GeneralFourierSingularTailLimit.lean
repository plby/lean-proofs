/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSingularTail

/-!
# Uniform convergence of the singular tail

The graph and exceptional integer can vary. A logarithmic exceptional
mass that is small relative to the truncation cutoff suffices.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

theorem tendsto_doubledFourierSingularTailBound_zero
    (ι : Type*) [Fintype ι] {α : Type*} {l : Filter α} (M Y : α → ℕ)
    (hY : Tendsto Y l atTop)
    (hmass : Tendsto (fun a ↦ Real.log (M a) / Y a) l (𝓝 0)) :
    Tendsto (fun a ↦ doubledFourierSingularTailBound ι (M a) (Y a)) l (𝓝 0) := by
  have hrec : Tendsto (fun a ↦ (2 : ℝ) / Y a) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hY)
  have h := ((hrec.const_mul (pairProductErrorConstant (Fintype.card (ι ⊕ ι)))).add
    (hmass.const_mul ((Fintype.card (ι ⊕ ι) : ℝ) / Real.log 2))).const_mul
      ((2 : ℝ) ^ Fintype.card (ι ⊕ ι))
  simpa only [doubledFourierSingularTailBound, mul_zero, add_zero] using h

theorem tendsto_tprod_roughDoubledFourierSingularFactor_one
    {ι : Type*} [Fintype ι] {α : Type*} {l : Filter α}
    (M Y : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (hY : Tendsto Y l atTop) (hM : ∀ᶠ a in l, 0 < M a)
    (hmass : Tendsto (fun a ↦ Real.log (M a) / Y a) l (𝓝 0))
    (hedgeCard : ∀ᶠ a in l, ∀ p : Nat.Primes, Y a < p → (edges a p).card ≤ Fintype.card ι)
    (hgeneric : ∀ᶠ a in l, ∀ p : Nat.Primes, Y a < p → ¬p.val ∣ M a →
      edges a p = ∅ ∧ companion a p = true) :
    Tendsto (fun a ↦ ∏' p : Nat.Primes,
      roughDoubledFourierSingularFactor (Y a) (edges a) (companion a) p) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound := tendsto_doubledFourierSingularTailBound_zero ι M Y hY hmass
  have hexp : Tendsto (fun a ↦ Real.exp (doubledFourierSingularTailBound ι (M a) (Y a)) - 1)
      l (𝓝 0) := by
    simpa only [Function.comp_def, Real.exp_zero, sub_self] using
      ((Real.continuous_exp.tendsto 0).comp hbound).sub_const 1
  apply squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _) _ hexp
  filter_upwards [hM, hedgeCard, hgeneric,
    hY.eventually_ge_atTop (7 * Fintype.card (ι ⊕ ι) + 1)] with a hMa he hg hYa
  exact norm_tprod_roughDoubledFourierSingularFactor_sub_one_le (edges a) (companion a)
    hMa (by omega) (by exact_mod_cast (show 7 * Fintype.card (ι ⊕ ι) ≤ Y a by omega)) he hg

end

end Erdos4b
