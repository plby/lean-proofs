import ErdosProblems.Erdos67b.MRCofactorBlock
import ErdosProblems.Erdos67b.MRTDensity

/-!
# A single power-sized block with explicit exceptional density

For the first Ramaré block `[L,(L-1)^K]`, the Mertens main term in the
beta-sieve estimate is exactly a constant divided by `K`.  This packages
that parameter choice while retaining the finite, eventually vanishing
sieve remainder.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem exists_uniform_powerBlock_atypical_density :
    ∃ C : ℝ, 0 < C ∧
      ∀ {L K : ℕ}, 3 ≤ L → 2 ≤ K →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
          ((atypicalFactorizationSet
            ({(L, (L - 1) ^ K)} : Finset (ℕ × ℕ)) X).card : ℝ) ≤
            (C / (K : ℝ) + epsilon) * X := by
  obtain ⟨A, S, hA, hS, hlog, hdensity⟩ :=
    exists_eventually_card_atypicalFactorizationSet_mertens_bound
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let C : ℝ := (1 + eta) * Real.exp (2 * PrimeEstimates.mertensBound)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro L K hL hK epsilon hepsilon
  let I : ℕ × ℕ := (L, (L - 1) ^ K)
  let blocks : Finset (ℕ × ℕ) := {I}
  have hLpow : L ≤ (L - 1) ^ K := by
    have hbase : L ≤ (L - 1) ^ 2 := by
      have hn : 2 ≤ L - 1 := by omega
      calc
        L ≤ 2 * (L - 1) := by omega
        _ ≤ (L - 1) * (L - 1) := Nat.mul_le_mul_right (L - 1) hn
        _ = (L - 1) ^ 2 := by ring
    have hpowmono : (L - 1) ^ 2 ≤ (L - 1) ^ K := by
      exact Nat.pow_le_pow_right (by omega) hK
    exact hbase.trans hpowmono
  have hblocks : ∀ J ∈ blocks, 3 ≤ J.1 ∧ J.1 ≤ J.2 := by
    intro J hJ
    simp only [blocks, Finset.mem_singleton] at hJ
    subst J
    exact ⟨hL, hLpow⟩
  obtain ⟨X₀, hX₀⟩ := hdensity blocks hblocks epsilon hepsilon
  refine ⟨X₀, ?_⟩
  intro X hX
  have hraw := hX₀ X hX
  have hlogbase : 0 < Real.log ((L - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L - 1 by omega))
  have hKreal : (0 : ℝ) < (K : ℝ) := by positivity
  have hratio :
      Real.log ((L - 1 : ℕ) : ℝ) /
          Real.log (((L - 1) ^ K : ℕ) : ℝ) = 1 / (K : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    field_simp
  have hCdiv : C / (K : ℝ) =
      (1 + eta) * (Real.exp (2 * PrimeEstimates.mertensBound) *
        (1 / (K : ℝ))) := by
    dsimp [C]
    ring
  rw [hCdiv]
  simpa only [blocks, I, Finset.sum_singleton, eta, hratio] using hraw

end

end Erdos67b
