/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ControlledGeneralEventually

/-!
# A fixed-power divisor-count bound for the controlled prime test set

Only the standard fact `τ(n) = n^{o(1)}` is needed downstream.  This file
proves the concrete eventual estimate `τ(n) ≤ n^(3/32)` from the prime
factorization formula.  Primes below `2^16` contribute a fixed power of
`log n`; every larger prime pays the sixteenth power of its local divisor
factor directly from its prime-power contribution to `n`.
-/

namespace Erdos360

open Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

private lemma succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pow_succ]
      omega

private lemma card_divisors_pow_sixteen_le
    {n : ℕ} (hn : 0 < n) :
    n.divisors.card ^ 16 ≤ (Nat.log 2 n + 1) ^ (65536 * 16) * n := by
  let small := n.primeFactors.filter fun p ↦ p < 65536
  let large := n.primeFactors.filter fun p ↦ ¬p < 65536
  let f : ℕ → ℕ := fun p ↦ n.factorization p + 1
  have hsplit : (∏ p ∈ small, f p) * (∏ p ∈ large, f p) =
      ∏ p ∈ n.primeFactors, f p := by
    simpa [small, large] using
      (Finset.prod_filter_mul_prod_filter_not n.primeFactors
        (fun p ↦ p < 65536) f)
  have hsmallCard : small.card ≤ 65536 := by
    have hsub : small ⊆ Finset.range 65536 := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hsmallFactor : ∀ p ∈ small, f p ≤ Nat.log 2 n + 1 := by
    intro p hp
    have hpF := (Finset.mem_filter.mp hp).1
    have hpPrime := Nat.prime_of_mem_primeFactors hpF
    have hpPow : p ^ n.factorization p ≤ n := by
      simpa only using Nat.ordProj_le p hn.ne'
    have htwoPow : 2 ^ n.factorization p ≤ p ^ n.factorization p := by
      exact Nat.pow_le_pow_left hpPrime.two_le _
    have hfac : n.factorization p ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le Nat.one_lt_two (htwoPow.trans hpPow)
    dsimp [f]
    omega
  have hsmall : (∏ p ∈ small, f p) ≤
      (Nat.log 2 n + 1) ^ 65536 := by
    calc
      (∏ p ∈ small, f p) ≤
          ∏ _p ∈ small, (Nat.log 2 n + 1) := by
        apply Finset.prod_le_prod
        · intro p hp
          positivity
        intro p hp
        exact hsmallFactor p hp
      _ = (Nat.log 2 n + 1) ^ small.card := by simp
      _ ≤ (Nat.log 2 n + 1) ^ 65536 := by
        exact pow_le_pow_right₀ (by omega) hsmallCard
  have hlargeLocal : ∀ p ∈ large, (f p) ^ 16 ≤
      p ^ n.factorization p := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := Nat.prime_of_mem_primeFactors hpData.1
    have haPos : 0 < n.factorization p :=
      hpPrime.factorization_pos_of_dvd hn.ne'
        (Nat.dvd_of_mem_primeFactors hpData.1)
    have hsucc := succ_le_two_pow (n.factorization p)
    have hpLarge : 2 ^ 16 ≤ p := by
      norm_num
      exact Nat.le_of_not_gt hpData.2
    calc
      (f p) ^ 16 ≤ (2 ^ n.factorization p) ^ 16 := by
        exact Nat.pow_le_pow_left (by simpa [f] using hsucc) _
      _ = 2 ^ (n.factorization p * 16) := (pow_mul _ _ _).symm
      _ = 2 ^ (16 * n.factorization p) := by rw [Nat.mul_comm]
      _ = (2 ^ 16) ^ n.factorization p := pow_mul _ _ _
      _ ≤ p ^ n.factorization p := Nat.pow_le_pow_left hpLarge _
  have hlargePow : (∏ p ∈ large, f p) ^ 16 ≤ n := by
    have hlocal : (∏ p ∈ large, f p) ^ 16 ≤
        ∏ p ∈ large, p ^ n.factorization p := by
      rw [← Finset.prod_pow]
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le _
      intro p hp
      exact hlargeLocal p hp
    have hdvd : (∏ p ∈ large, p ^ n.factorization p) ∣ n := by
      have hsub : large ⊆ n.primeFactors := Finset.filter_subset _ _
      have hprodDvd := Finset.prod_dvd_prod_of_subset large n.primeFactors
        (fun p ↦ p ^ n.factorization p) hsub
      rw [← Nat.prod_primeFactors_pow_factorization hn.ne'] at hprodDvd
      exact hprodDvd
    exact hlocal.trans (Nat.le_of_dvd hn hdvd)
  rw [Nat.card_divisors hn.ne']
  rw [← hsplit]
  calc
    ((∏ p ∈ small, f p) * (∏ p ∈ large, f p)) ^ 16 =
        (∏ p ∈ small, f p) ^ 16 *
          (∏ p ∈ large, f p) ^ 16 := mul_pow _ _ _
    _ ≤ ((Nat.log 2 n + 1) ^ 65536) ^ 16 * n := by gcongr
    _ = (Nat.log 2 n + 1) ^ (65536 * 16) * n := by
      rw [pow_mul]

private lemma eventually_natLog_pow_le_rpow_half :
    ∀ᶠ n : ℕ in atTop,
      ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (65536 * 16) ≤
        Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
  let K : ℕ := 65536 * 16
  let e : ℝ := 1 / (4 * K : ℝ)
  let C : ℝ := (12 * K : ℕ) ^ K
  have he : 0 < e := by dsimp [e, K]; positivity
  have hquarterTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 1,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    hquarterTop.eventually (eventually_ge_atTop C)] with n hn hlog hlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnatLog := natLogTwo_cast_le_two_mul_log (m := n) (by omega)
  have hlogBound : Real.log (n : ℝ) ≤
      (4 * K : ℕ) * Real.rpow (n : ℝ) e := by
    have h := Real.log_le_rpow_div hnR.le he
    dsimp [e]
    calc
      Real.log (n : ℝ) ≤
          Real.rpow (n : ℝ) (1 / (4 * K : ℝ)) /
            (1 / (4 * K : ℝ)) := h
      _ = (4 * K : ℕ) *
          Real.rpow (n : ℝ) (1 / (4 * K : ℝ)) := by
        norm_num [K]
        ring
  have hbase : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤
      (12 * K : ℕ) * Real.rpow (n : ℝ) e := by
    have hlogThree : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤
        3 * Real.log (n : ℝ) := by
      push_cast
      nlinarith
    calc
      ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log (n : ℝ) := hlogThree
      _ ≤ 3 * ((4 * K : ℕ) * Real.rpow (n : ℝ) e) :=
        mul_le_mul_of_nonneg_left hlogBound (by norm_num)
      _ = (12 * K : ℕ) * Real.rpow (n : ℝ) e := by
        push_cast
        ring
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      ((Nat.log 2 n + 1 : ℕ) : ℝ)) hbase K
  have hrpowK : (Real.rpow (n : ℝ) e) ^ K =
      Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
    calc
      (Real.rpow (n : ℝ) e) ^ K =
          Real.rpow (Real.rpow (n : ℝ) e) (K : ℝ) :=
        (Real.rpow_natCast _ K).symm
      _ = Real.rpow (n : ℝ) (e * K) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = _ := by
        congr 1
        dsimp [e, K]
        norm_num
  have hupper : (((Nat.log 2 n + 1 : ℕ) : ℝ) ^ K) ≤
      C * Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
    calc
      (((Nat.log 2 n + 1 : ℕ) : ℝ) ^ K) ≤
          (((12 * K : ℕ) : ℝ) * Real.rpow (n : ℝ) e) ^ K := hpow
      _ = C * Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
        rw [mul_pow, hrpowK]
  have hhalf : Real.rpow (n : ℝ) (1 / 2 : ℝ) =
      Real.rpow (n : ℝ) (1 / 4 : ℝ) *
        Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
    convert Real.rpow_add hnR (1 / 4 : ℝ) (1 / 4 : ℝ) using 1 <;>
      norm_num
  dsimp [K] at hupper ⊢
  change (((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (65536 * 16)) ≤
    Real.rpow (n : ℝ) (1 / 2 : ℝ)
  rw [hhalf]
  exact hupper.trans (by
    exact mul_le_mul_of_nonneg_right hlarge
      (Real.rpow_nonneg hnR.le _))

/-- A concrete form of `τ(n) = n^{o(1)}` sufficient for the controlled
cutoff `U ≈ n^(1/8)`. -/
theorem eventually_card_divisors_le_rpow_three_thirtytwo :
    ∀ᶠ n : ℕ in atTop,
      (n.divisors.card : ℝ) ≤ Real.rpow (n : ℝ) (3 / 32 : ℝ) := by
  filter_upwards [eventually_gt_atTop 1,
    eventually_natLog_pow_le_rpow_half] with n hn hlogPow
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hfinite := card_divisors_pow_sixteen_le hnPos
  have hfiniteR : ((n.divisors.card : ℝ) ^ 16) ≤
      (((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (65536 * 16)) * (n : ℝ) := by
    exact_mod_cast hfinite
  have hthreeHalves : Real.rpow (n : ℝ) (1 / 2 : ℝ) * (n : ℝ) =
      Real.rpow (n : ℝ) (3 / 2 : ℝ) := by
    calc
      _ = Real.rpow (n : ℝ) (1 / 2 : ℝ) *
          Real.rpow (n : ℝ) 1 := by
        rw [show Real.rpow (n : ℝ) 1 = (n : ℝ) by
          simpa only [Real.rpow_eq_pow] using Real.rpow_one (n : ℝ)]
      _ = Real.rpow (n : ℝ) ((1 / 2 : ℝ) + 1) :=
        (Real.rpow_add hnR _ _).symm
      _ = _ := by norm_num
  have hpowers : ((n.divisors.card : ℝ) ^ 16) ≤
      Real.rpow (n : ℝ) (3 / 2 : ℝ) := by
    calc
      _ ≤ (((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (65536 * 16)) *
          (n : ℝ) := hfiniteR
      _ ≤ Real.rpow (n : ℝ) (1 / 2 : ℝ) * (n : ℝ) := by gcongr
      _ = _ := hthreeHalves
  have htargetPow : (Real.rpow (n : ℝ) (3 / 32 : ℝ)) ^ 16 =
      Real.rpow (n : ℝ) (3 / 2 : ℝ) := by
    calc
      _ = Real.rpow (Real.rpow (n : ℝ) (3 / 32 : ℝ)) (16 : ℝ) :=
        (Real.rpow_natCast _ 16).symm
      _ = Real.rpow (n : ℝ) ((3 / 32 : ℝ) * 16) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = _ := by norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : 16 ≠ 0)
    (Real.rpow_nonneg hnR.le _)
  change ((n.divisors.card : ℝ) ^ 16) ≤
    (Real.rpow (n : ℝ) (3 / 32 : ℝ)) ^ 16
  rw [htargetPow]
  exact hpowers

end Erdos360

#print axioms Erdos360.eventually_card_divisors_le_rpow_three_thirtytwo
