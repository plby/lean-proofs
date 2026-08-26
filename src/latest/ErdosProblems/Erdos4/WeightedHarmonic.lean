import ErdosProblems.Erdos4.HarmonicUniform
import ErdosProblems.Erdos4.ProfileAbel

/-!
# The actual weighted fixed-modulus harmonic asymptotic

The error is uniform over every completion endpoint up to the outer
cutoff. The modulus and profile parameters are fixed before that cutoff
tends to infinity.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.WeightedHarmonic

noncomputable def weight (W n : ℕ) : ℝ := by
  classical
  exact if Squarefree n ∧ n.Coprime W then 1 / (Nat.totient n : ℝ) else 0

theorem weight_zero (W : ℕ) : weight W 0 = 0 := by simp [weight]

theorem weight_nonneg (W n : ℕ) : 0 ≤ weight W n := by
  unfold weight
  split_ifs <;> positivity

theorem sum_zero_endpoint_eq (f : ℕ → ℝ) (hf : f 0 = 0) (T : ℕ) :
    (∑ n ∈ Finset.Icc 0 T, f n) = ∑ n ∈ Finset.Icc 1 T, f n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hn).2⟩
  · intro n hn hnnot
    have hnzero : n = 0 := by
      have hnle := (Finset.mem_Icc.mp hn).2
      have hnot : ¬(1 ≤ n ∧ n ≤ T) := by simpa only [Finset.mem_Icc] using hnnot
      omega
    simpa only [hnzero] using hf

theorem cumulative_eq (W : ℕ) (x : ℝ) :
    BoundedGaps.Maynard.abelCumulative (weight W) x =
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W ⌊x⌋₊ := by
  unfold BoundedGaps.Maynard.abelCumulative
  rw [sum_zero_endpoint_eq (weight W) (weight_zero W)]
  rfl

noncomputable def weightedSum (W : ℕ) (m k : ℝ) (R T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 T, ProfileSmooth.scaled m k R n * weight W n

/-- A fixed squarefree modulus and the actual explicit profile satisfy
the harmonic transfer uniformly for all smaller positive endpoints. -/
theorem uniform_asymptotic {W : ℕ} (hW : 0 < W) (hSq : Squarefree W)
    {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧ ∀ T : ℕ, 1 ≤ T → T ≤ R →
      |weightedSum W m k R T -
        BoundedGaps.Maynard.coprimeHarmonicDensity W * Real.log R *
          PrimitiveProfile.primitive m k (Real.log T / Real.log R)| ≤ ε * Real.log R := by
  have hhalf : 0 < ε / 2 := by linarith
  filter_upwards [HarmonicUniform.fixed_modulus_uniform_real hW hSq hhalf] with R hR
  refine ⟨hR.1, ?_⟩
  intro T hT hTR
  have hE : 0 ≤ (ε / 2) * Real.log R := mul_nonneg hhalf.le (Real.log_natCast_nonneg R)
  have happrox : ∀ x ∈ Set.Icc (1 : ℝ) T,
      |BoundedGaps.Maynard.abelCumulative (weight W) x -
        BoundedGaps.Maynard.coprimeHarmonicDensity W * Real.log x| ≤ (ε / 2) * Real.log R := by
    intro x hx
    rw [cumulative_eq]
    exact hR.2 x hx.1 (hx.2.trans (by exact_mod_cast hTR))
  have hh := ProfileAbel.weighted_error_le hm hk hR.1 hT (weight_zero W) hE happrox
  rw [sum_zero_endpoint_eq
    (fun n => ProfileSmooth.scaled m k R n * weight W n) (by rw [weight_zero, mul_zero])] at hh
  exact hh.trans_eq (by ring)

end Erdos4.WeightedHarmonic
