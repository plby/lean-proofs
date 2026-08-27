/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMainConstantEuler
import ErdosProblems.Erdos4b.FGKMTActualDenominators

/-!
# Telescoping the local factors of successive coordinate sums

The product of the one-dimensional main constants has precisely the
multivariate Euler factor `1 + j / g(p)`, together with `j` copies of
the ordinary harmonic density. The summability hypotheses are discharged
for the actual denominators `p - k + s`, `s < j ≤ k`.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators Topology

def multivariateSieveConstant (M : ℕ) (g : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∏ s ∈ Finset.range j, sieveMainConstant M (fun p => g p + s)

theorem prod_one_add_reciprocal_shift {g : ℝ} (hg : 0 < g) (j : ℕ) :
    (∏ s ∈ Finset.range j, (1 + 1 / (g + s))) = (g + j) / g := by
  induction j with
  | zero => simp [hg.ne']
  | succ j ih =>
      have hgj : g + j ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hg (Nat.cast_nonneg j))
      rw [Finset.prod_range_succ, ih, Nat.cast_succ]
      field_simp [hg.ne', hgj]
      ring

theorem prod_shifted_sieveEulerFactor (M p j : ℕ) (g : ℕ → ℝ)
    (hg : ¬p ∣ M → 0 < g p) :
    (∏ s ∈ Finset.range j, sieveEulerFactor M (fun q => g q + s) p) =
      (if p ∣ M then 1 else 1 + (j : ℝ) / g p) * (1 - 1 / (p : ℝ)) ^ j := by
  by_cases hpM : p ∣ M
  · simp [sieveEulerFactor, hpM]
  · simp only [sieveEulerFactor, if_neg hpM, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range]
    rw [prod_one_add_reciprocal_shift (hg hpM)]
    congr 1
    field_simp [(hg hpM).ne']

theorem multivariateSieveConstant_eulerProduct {M j : ℕ} (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → 0 < g p)
    (hsum : ∀ s : ℕ, s < j → Summable
      (fun n => |harmonicCorrection (roughSieveWeight M (fun p => g p + s)) n|)) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow,
      (if p ∣ M then 1 else 1 + (j : ℝ) / g p) * (1 - 1 / (p : ℝ)) ^ j)
      atTop (𝓝 (multivariateSieveConstant M g j)) := by
  have hlim := tendsto_finsetProd (Finset.range j) (fun s hs =>
    sieveMainConstant_eulerProduct (hsum s (Finset.mem_range.mp hs)))
  apply hlim.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  exact prod_shifted_sieveEulerFactor M p j g (hg p (Nat.prime_of_mem_primesBelow hp))

theorem actual_multivariateSieveConstant_eulerProduct {k M j : ℕ}
    (hk : 2 ≤ k) (hM : 0 < M) (hj : j ≤ k)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow,
      (if p ∣ M then 1 else 1 + (j : ℝ) / ((p : ℝ) - k)) *
        (1 - 1 / (p : ℝ)) ^ j)
      atTop (𝓝 (multivariateSieveConstant M (fun p => (p : ℝ) - k) j)) := by
  have hrough : ∀ p : ℕ, p.Prime → ¬p ∣ M → 2 * (k : ℝ) ^ 2 < p := by
    intro p hp hpM
    have hlt : 2 * k ^ 2 < p := by
      by_contra hnot
      exact hpM (hsmall p hp (by omega))
    exact_mod_cast hlt
  apply multivariateSieveConstant_eulerProduct
  · intro p hp hpM
    have hhalf := (rough_real_bounds (by exact_mod_cast hk) (hrough p hp hpM)).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    linarith
  · intro s hs
    have hsk : s < k := hs.trans_le hj
    have hb p hp hpM := shiftedDenominator_bounds hk hsk (hrough p hp hpM)
    exact (harmonicCorrection_roughSieveWeight_moments (by omega : 0 < k) hM
      (fun p hp hpk => hsmall p hp (by omega)) _
      (fun p hp hpM => (hb p hp hpM).1)
      (fun p hp hpM => (hb p hp hpM).2.1)).1

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.actual_multivariateSieveConstant_eulerProduct
