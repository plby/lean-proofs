import ErdosProblems.Erdos587.GreedySubsetSums

/-! Quantitative time bounds for the greedy growth process. -/

open scoped Pointwise

namespace Erdos587.CFP

/-- Summing relative growth over an interval gives an additive time bound. -/
theorem growth_interval_linear {f : ℕ → ℝ} (hmono : Monotone f) (q a n : ℕ)
    (hstep : ∀ i < n, ((q : ℝ) + 1) * f (a + i) ≤ q * f (a + i + 1)) :
    ((n : ℝ) + q) * f a ≤ q * f (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev := ih (fun i hi => hstep i (by omega))
      have hbase : f a ≤ f (a + n) := hmono (by omega)
      calc
        ((↑(n + 1) : ℝ) + q) * f a = f a + ((n : ℝ) + q) * f a := by
          push_cast
          ring
        _ ≤ f a + q * f (a + n) := add_le_add (le_refl _) hprev
        _ ≤ f (a + n) + q * f (a + n) := add_le_add hbase (le_refl _)
        _ = ((q : ℝ) + 1) * f (a + n) := by ring
        _ ≤ q * f (a + (n + 1)) := by
          simpa only [Nat.add_assoc] using hstep n (by omega)

theorem growth_interval_doubling {f : ℕ → ℝ} (hmono : Monotone f) {q : ℕ}
    (hq : 0 < q) (a : ℕ)
    (hstep : ∀ i < q, ((q : ℝ) + 1) * f (a + i) ≤ q * f (a + i + 1)) :
    2 * f a ≤ f (a + q) := by
  have hh := growth_interval_linear hmono q a q hstep
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (mul_le_mul_iff_right₀ hqR).mp
  nlinarith

theorem growth_interval_pow_two {f : ℕ → ℝ} (hmono : Monotone f) {q : ℕ}
    (hq : 0 < q) (a n : ℕ)
    (hstep : ∀ i < q * n, ((q : ℝ) + 1) * f (a + i) ≤ q * f (a + i + 1)) :
    (2 : ℝ) ^ n * f a ≤ f (a + q * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev := ih (fun i hi => hstep i (by rw [Nat.mul_succ]; omega))
      have hblock := growth_interval_doubling hmono hq (a + q * n) (fun i hi => by
        simpa only [Nat.add_assoc] using hstep (q * n + i) (by rw [Nat.mul_succ]; omega))
      calc
        (2 : ℝ) ^ (n + 1) * f a = 2 * ((2 : ℝ) ^ n * f a) := by rw [pow_succ']; ring
        _ ≤ 2 * f (a + q * n) := mul_le_mul_of_nonneg_left hprev (by norm_num)
        _ ≤ f (a + q * (n + 1)) := by
          simpa only [Nat.mul_succ, Nat.add_assoc] using hblock

/-- A size band with bounded ratio requires only linearly many growth steps. -/
theorem reaches_threshold_of_growth_below {f : ℕ → ℝ} (hmono : Monotone f)
    {q : ℕ} (hq : 0 < q) (a D : ℕ) {L U : ℝ} (hL : 0 < L)
    (hstart : L ≤ f a) (hbudget : U ≤ D * L)
    (hstep : ∀ i < q * D, f (a + i) < U →
      ((q : ℝ) + 1) * f (a + i) ≤ q * f (a + i + 1)) :
    U ≤ f (a + q * D) := by
  by_contra hn
  have hend : f (a + q * D) < U := lt_of_not_ge hn
  have hsteps : ∀ i < q * D,
      ((q : ℝ) + 1) * f (a + i) ≤ q * f (a + i + 1) := by
    intro i hi
    exact hstep i hi ((hmono (by omega)).trans_lt hend)
  have hh := growth_interval_linear hmono q a (q * D) hsteps
  have hbase := mul_le_mul_of_nonneg_left hstart
    (show (0 : ℝ) ≤ (q * D : ℕ) + q by positivity)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlast := mul_lt_mul_of_pos_left (hend.trans_le hbudget) hqR
  push_cast at hh hbase
  nlinarith

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem greedySubset_card_mono (A : Finset G) :
    Monotone (fun n => (greedySubset A n).subsetSum.card) := by
  intro i j hij
  exact Finset.card_le_card (Finset.subsetSum_mono (greedySubset_mono A hij))

theorem greedySubset_real_card_mono (A : Finset G) :
    Monotone (fun n => ((greedySubset A n).subsetSum.card : ℝ)) := by
  intro i j hij
  exact Nat.cast_le.mpr (greedySubset_card_mono A hij)

theorem greedySubset_doubling (A : Finset G) {k : ℕ} (hk : 0 < k) (a : ℕ)
    (hlarge : ∀ i < 2 * k, 2 * (greedySubset A (a + i)).subsetSum.card ≤
      (k • insert 0 (A \ greedySubset A (a + i))).card) :
    2 * (greedySubset A a).subsetSum.card ≤ (greedySubset A (a + 2 * k)).subsetSum.card := by
  have hh := growth_interval_doubling (greedySubset_real_card_mono A)
    (Nat.mul_pos (by decide : 0 < 2) hk) a (fun i hi => by
      exact_mod_cast greedySubset_growth A (a + i) k (hlarge i hi))
  exact_mod_cast hh

end Erdos587.CFP
