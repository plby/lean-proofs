import ErdosProblems.Erdos448.Lemma4FirstMoment448
import ErdosProblems.Erdos448.NormalizedDivisorMoment448

open Filter Finset
open scoped BigOperators Topology

namespace NaturalGridConcentration448

attribute [local instance] Classical.propDecidable

open Lemma4FirstMoment448

/-!
This file develops the one-sided geometric-grid selector.  Unlike the
two-sided normal-order selector in the paper, it tests only the upper tail
needed to make the close-pair weight at least one.
-/

/-- The natural logarithmic cutoffs `K, 3K, 9K, ...`. -/
def naturalGridScale (K j : ℕ) : ℕ := K * 3 ^ j

/-- Number of prime factors of `d` below the natural cutoff `2^q`. -/
noncomputable def omegaAtLogScale (d q : ℕ) : ℕ :=
  omegaBelow d ((2 ^ q : ℕ) : ℝ)

/-- A divisor passes every grid test whose index is smaller than the divisor.
This finite relevance condition is enough because a divisor of `n` is at
most `n`, so rejected divisors are covered by the first `n` grid tests. -/
def naturalGridGood (K d : ℕ) : Prop :=
  ∀ j < d, 2 ^ (5 * omegaAtLogScale d (naturalGridScale K j)) ≤
    (naturalGridScale K j) ^ 2

noncomputable def naturalGridSelectedDivisors (K n : ℕ) : Finset ℕ :=
  n.divisors.filter (naturalGridGood K)

theorem naturalGridSelectedDivisors_subset (K n : ℕ) :
    naturalGridSelectedDivisors K n ⊆ n.divisors :=
  Finset.filter_subset _ _

lemma self_le_three_pow (k : ℕ) : k ≤ 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        k + 1 ≤ 3 ^ k + 1 := Nat.add_le_add_right ih 1
        _ ≤ 3 ^ k * 3 := by
          have hpow : 1 ≤ 3 ^ k :=
            Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
          calc
            3 ^ k + 1 ≤ 3 ^ k + 3 ^ k := Nat.add_le_add_left hpow _
            _ ≤ 3 ^ k + 3 ^ k + 3 ^ k := Nat.le_add_right _ _
            _ = 3 ^ k * 3 := by ring
        _ = 3 ^ (k + 1) := by rw [pow_succ]

lemma self_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left
          (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))) _
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

lemma exists_le_naturalGridScale {K k : ℕ} (hK : 0 < K) :
    ∃ j, k ≤ naturalGridScale K j := by
  refine ⟨k, ?_⟩
  unfold naturalGridScale
  have hK1 : 1 ≤ K := hK
  exact (self_le_three_pow k).trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right (3 ^ k) hK1)

lemma le_naturalGridScale_self {K k : ℕ} (hK : 0 < K) :
    k ≤ naturalGridScale K k := by
  unfold naturalGridScale
  exact (self_le_three_pow k).trans (by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (3 ^ k) (show 1 ≤ K from hK))

/-- The first grid index whose scale is at least `k`; its value at `K=0`
is immaterial because every application assumes `K>0`. -/
noncomputable def gridCeilIndex (K k : ℕ) : ℕ :=
  if hK : K = 0 then 0 else
    Nat.find (exists_le_naturalGridScale (K := K) (k := k)
      (Nat.pos_of_ne_zero hK))

theorem le_gridScale_gridCeilIndex {K k : ℕ} (hK : 0 < K) :
    k ≤ naturalGridScale K (gridCeilIndex K k) := by
  rw [gridCeilIndex, dif_neg hK.ne']
  exact Nat.find_spec (exists_le_naturalGridScale (K := K) (k := k) hK)

theorem gridCeilIndex_le_self {K k : ℕ} (hK : 0 < K) :
    gridCeilIndex K k ≤ k := by
  rw [gridCeilIndex, dif_neg hK.ne']
  apply Nat.find_min'
  exact le_naturalGridScale_self hK

theorem gridScale_gridCeilIndex_le_three_mul
    {K k : ℕ} (hK : 0 < K) (hk : K ≤ k) :
    naturalGridScale K (gridCeilIndex K k) ≤ 3 * k := by
  by_cases hj : gridCeilIndex K k = 0
  · rw [hj]
    simp only [naturalGridScale, pow_zero, mul_one]
    omega
  · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [hi]
    have hminimal : ¬ k ≤ naturalGridScale K i := by
      rw [gridCeilIndex, dif_neg hK.ne'] at hi
      exact Nat.find_min (exists_le_naturalGridScale (K := K) (k := k) hK)
        (by omega : i < Nat.find
          (exists_le_naturalGridScale (K := K) (k := k) hK))
    have hlt : naturalGridScale K i < k := Nat.lt_of_not_ge hminimal
    calc
      naturalGridScale K (i + 1) = 3 * naturalGridScale K i := by
        simp [naturalGridScale, pow_succ]
        ring
      _ ≤ 3 * k := Nat.mul_le_mul_left 3 hlt.le

lemma omegaBelow_mono_right {d : ℕ} {u v : ℝ} (huv : u ≤ v) :
    omegaBelow d u ≤ omegaBelow d v := by
  unfold omegaBelow
  generalize d.primeFactorsList = l
  induction l with
  | nil => simp
  | cons p l ih =>
      by_cases hpu : (p : ℝ) < u
      · have hpv : (p : ℝ) < v := hpu.trans_le huv
        simp [hpu, hpv, ih]
      · by_cases hpv : (p : ℝ) < v
        · simp [hpu, hpv]
          omega
        · simp [hpu, hpv, ih]

lemma omegaAtLogScale_mono {d q r : ℕ} (hqr : q ≤ r) :
    omegaAtLogScale d q ≤ omegaAtLogScale d r := by
  apply omegaBelow_mono_right
  exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hqr

lemma omegaAtLogScale_le_totalOmega (d q : ℕ) :
    omegaAtLogScale d q ≤ d.primeFactorsList.length := by
  unfold omegaAtLogScale omegaBelow
  exact List.length_filter_le _ _

lemma pow_two_totalOmega_le {d : ℕ} (hd : d ≠ 0) :
    2 ^ d.primeFactorsList.length ≤ d := by
  have hall : ∀ p ∈ d.primeFactorsList, 2 ≤ p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactorsList hp).two_le
  have aux : ∀ l : List ℕ, (∀ p ∈ l, 2 ≤ p) →
      2 ^ l.length ≤ l.prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
        intro hl
        simp only [List.length_cons, pow_succ, List.prod_cons]
        have hp : 2 ≤ p := hl p (by simp)
        have htail : 2 ^ l.length ≤ l.prod :=
          ih (fun q hq => hl q (by simp [hq]))
        simpa [Nat.mul_comm] using Nat.mul_le_mul htail hp
  have hlist : 2 ^ d.primeFactorsList.length ≤ d.primeFactorsList.prod :=
    aux d.primeFactorsList hall
  rwa [Nat.prod_primeFactorsList hd] at hlist

lemma omegaAtLogScale_le_ownScale {d k : ℕ} (hd : d ≠ 0)
    (hk : Nat.log 2 d = k) : omegaAtLogScale d k ≤ k := by
  have hpowOmega : 2 ^ omegaAtLogScale d k ≤ d :=
    (Nat.pow_le_pow_right (by omega) (omegaAtLogScale_le_totalOmega d k)).trans
      (pow_two_totalOmega_le hd)
  have := Nat.le_log_of_pow_le (by omega : 1 < (2 : ℕ)) hpowOmega
  simpa [hk] using this

/-! The numerical weight supplied by the selector. -/

noncomputable def naturalGridWeightConstant (K : ℕ) : ℝ :=
  max ((2 : ℝ) ^ K) 3

lemma naturalGridWeightConstant_pos (K : ℕ) :
    0 < naturalGridWeightConstant K := by
  unfold naturalGridWeightConstant
  exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)

noncomputable def naturalGridWeight (K d k : ℕ) : ℝ :=
  naturalGridWeightConstant K * (k : ℝ) ^ (2 / 5 : ℝ) *
    (1 / 2 : ℝ) ^ omegaAtLogScale d k

lemma fifth_power_bound_implies_weight
    {C k m : ℕ} (hk : 0 < k) (hC : C ≤ 3 * k)
    (hpow : 2 ^ (5 * m) ≤ C ^ 2) :
    (1 : ℝ) ≤ 3 * (k : ℝ) ^ (2 / 5 : ℝ) * (1 / 2 : ℝ) ^ m := by
  have hpowR : (2 : ℝ) ^ (5 * m) ≤ (C : ℝ) ^ 2 := by exact_mod_cast hpow
  have hCR : (C : ℝ) ≤ 3 * k := by exact_mod_cast hC
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by
    by_contra h
    have hC0 : C = 0 := Nat.eq_zero_of_not_pos h
    subst C
    norm_num at hpow
  have hlogC : Real.log (C : ℝ) ≤ Real.log (3 * (k : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hCpos) hCR
  have hlogs : 5 * (m : ℝ) * Real.log 2 ≤ 2 * Real.log (C : ℝ) := by
    have h := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpowR
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    convert h using 1 <;> ring
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have htarget :
      0 ≤ Real.log 3 + (2 / 5 : ℝ) * Real.log (k : ℝ) -
        (m : ℝ) * Real.log 2 := by
    have hlogmul : Real.log (3 * (k : ℝ)) = Real.log 3 + Real.log (k : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hkR)]
    rw [hlogmul] at hlogC
    nlinarith
  rw [Real.rpow_def_of_pos hkR]
  rw [show ((1 / 2 : ℝ) ^ m) =
      Real.exp (-(m : ℝ) * Real.log 2) by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        congr 1
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
        ring]
  rw [show (3 : ℝ) = Real.exp (Real.log 3) by
    rw [Real.exp_log (by norm_num)]]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by convert htarget using 1 <;> ring)

lemma fifth_power_bound_implies_exact_weight
    {C m : ℕ} (hC : 0 < C) (hpow : 2 ^ (5 * m) ≤ C ^ 2) :
    (1 : ℝ) ≤ (C : ℝ) ^ (2 / 5 : ℝ) * (1 / 2 : ℝ) ^ m := by
  have hpowR : (2 : ℝ) ^ (5 * m) ≤ (C : ℝ) ^ 2 := by exact_mod_cast hpow
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hlogs : 5 * (m : ℝ) * Real.log 2 ≤ 2 * Real.log (C : ℝ) := by
    have h := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpowR
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    convert h using 1 <;> ring
  have htarget :
      0 ≤ (2 / 5 : ℝ) * Real.log (C : ℝ) - (m : ℝ) * Real.log 2 := by
    linarith
  rw [Real.rpow_def_of_pos hCR]
  rw [show ((1 / 2 : ℝ) ^ m) =
      Real.exp (-(m : ℝ) * Real.log 2) by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        congr 1
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
        ring]
  rw [← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by convert htarget using 1 <;> ring)

theorem one_le_naturalGridWeight_of_good
    {K d k : ℕ} (hK : 0 < K) (hk : 0 < k) (hkd : k < d)
    (hgood : naturalGridGood K d) :
    (1 : ℝ) ≤ naturalGridWeight K d k := by
  by_cases hlow : k < K
  · have htest := hgood 0 (by omega)
    have hkK : k ≤ K := hlow.le
    have hOmega : omegaAtLogScale d k ≤ omegaAtLogScale d K := by
      simpa [naturalGridScale] using omegaAtLogScale_mono hkK
    have hpowMono : 2 ^ (5 * omegaAtLogScale d k) ≤
        2 ^ (5 * omegaAtLogScale d K) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 5 hOmega)
    have htestK : 2 ^ (5 * omegaAtLogScale d K) ≤ K ^ 2 := by
      simpa [naturalGridScale] using htest
    have hbase : (1 : ℝ) ≤
        (K : ℝ) ^ (2 / 5 : ℝ) * (1 / 2 : ℝ) ^ omegaAtLogScale d k :=
      fifth_power_bound_implies_exact_weight hK (hpowMono.trans htestK)
    have hkpow : 1 ≤ (k : ℝ) ^ (2 / 5 : ℝ) := by
      apply Real.one_le_rpow
      · exact_mod_cast hk
      · norm_num
    have hKrpow : (K : ℝ) ^ (2 / 5 : ℝ) ≤ (K : ℝ) :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast hK) (by norm_num)
    have hKpow : (K : ℝ) ≤ (2 : ℝ) ^ K := by
      exact_mod_cast self_le_two_pow K
    have hC : (K : ℝ) ^ (2 / 5 : ℝ) ≤
        naturalGridWeightConstant K :=
      hKrpow.trans (hKpow.trans (le_max_left _ _))
    have hhalfpos : 0 < (1 / 2 : ℝ) ^ omegaAtLogScale d k := by positivity
    have hcoef : (K : ℝ) ^ (2 / 5 : ℝ) ≤
        naturalGridWeightConstant K * (k : ℝ) ^ (2 / 5 : ℝ) := by
      calc
        (K : ℝ) ^ (2 / 5 : ℝ) ≤ naturalGridWeightConstant K := hC
        _ = naturalGridWeightConstant K * 1 := by ring
        _ ≤ naturalGridWeightConstant K * (k : ℝ) ^ (2 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left hkpow (naturalGridWeightConstant_pos K).le
    unfold naturalGridWeight
    calc
      (1 : ℝ) ≤ (K : ℝ) ^ (2 / 5 : ℝ) *
          (1 / 2 : ℝ) ^ omegaAtLogScale d k := hbase
      _ ≤ (naturalGridWeightConstant K * (k : ℝ) ^ (2 / 5 : ℝ)) *
          (1 / 2 : ℝ) ^ omegaAtLogScale d k := by
        exact mul_le_mul_of_nonneg_right
          hcoef hhalfpos.le
  · have hkK : K ≤ k := Nat.le_of_not_gt hlow
    let j := gridCeilIndex K k
    have hjd : j < d := (gridCeilIndex_le_self hK).trans_lt hkd
    have htest := hgood j hjd
    have hkq : k ≤ naturalGridScale K j := le_gridScale_gridCeilIndex hK
    have hOmega : omegaAtLogScale d k ≤
        omegaAtLogScale d (naturalGridScale K j) := omegaAtLogScale_mono hkq
    have hpowMono : 2 ^ (5 * omegaAtLogScale d k) ≤
        2 ^ (5 * omegaAtLogScale d (naturalGridScale K j)) := by
      exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 5 hOmega)
    have hq : naturalGridScale K j ≤ 3 * k :=
      gridScale_gridCeilIndex_le_three_mul hK hkK
    have hbase := fifth_power_bound_implies_weight hk hq (hpowMono.trans htest)
    have hC : (3 : ℝ) ≤ naturalGridWeightConstant K := le_max_right _ _
    have hfactor : 0 ≤ (k : ℝ) ^ (2 / 5 : ℝ) *
        (1 / 2 : ℝ) ^ omegaAtLogScale d k := by positivity
    unfold naturalGridWeight
    calc
      (1 : ℝ) ≤ 3 * (k : ℝ) ^ (2 / 5 : ℝ) *
          (1 / 2 : ℝ) ^ omegaAtLogScale d k := hbase
      _ = 3 * ((k : ℝ) ^ (2 / 5 : ℝ) *
          (1 / 2 : ℝ) ^ omegaAtLogScale d k) := by ring
      _ ≤ naturalGridWeightConstant K * ((k : ℝ) ^ (2 / 5 : ℝ) *
          (1 / 2 : ℝ) ^ omegaAtLogScale d k) :=
        mul_le_mul_of_nonneg_right hC hfactor
      _ = naturalGridWeightConstant K * (k : ℝ) ^ (2 / 5 : ℝ) *
          (1 / 2 : ℝ) ^ omegaAtLogScale d k := by ring

/-! Rejection is bounded by the geometric union of one-grid upper tails. -/

def naturalGridBadAt (K j d : ℕ) : Prop :=
  (naturalGridScale K j) ^ 2 <
    2 ^ (5 * omegaAtLogScale d (naturalGridScale K j))

noncomputable def naturalGridBadFraction (K j n : ℕ) : ℝ :=
  divisorPredicateFraction (naturalGridBadAt K j) n

noncomputable def naturalGridRejectedFraction (K n : ℕ) : ℝ :=
  by
    classical
    exact if n = 0 then 0 else
      (((n.divisors.filter fun d ↦ ¬ naturalGridGood K d).card : ℕ) : ℝ) /
        n.divisors.card

lemma not_naturalGridGood_iff (K d : ℕ) :
    ¬ naturalGridGood K d ↔ ∃ j < d, naturalGridBadAt K j d := by
  constructor
  · intro h
    simp only [naturalGridGood, not_forall, not_le] at h
    rcases h with ⟨j, hj⟩
    rcases hj with ⟨hjd, hbad⟩
    exact ⟨j, hjd, hbad⟩
  · rintro ⟨j, hjd, hbad⟩ hgood
    exact (Nat.not_lt_of_ge (hgood j hjd)) hbad

theorem naturalGridRejectedFraction_le_sum (K n : ℕ) :
    naturalGridRejectedFraction K n ≤
      ∑ j ∈ Finset.range n, naturalGridBadFraction K j n := by
  by_cases hn : n = 0
  · subst n
    simp [naturalGridRejectedFraction, naturalGridBadFraction,
      divisorPredicateFraction]
  let badAt : ℕ → Finset ℕ := fun j =>
    n.divisors.filter (naturalGridBadAt K j)
  have hsubset :
      n.divisors.filter (fun d => ¬ naturalGridGood K d) ⊆
        (Finset.range n).biUnion badAt := by
    intro d hd
    have hdm := Finset.mem_filter.mp hd
    rcases (not_naturalGridGood_iff K d).mp hdm.2 with ⟨j, hjd, hj⟩
    have hdn : d ≤ n := Nat.divisor_le hdm.1
    exact Finset.mem_biUnion.mpr ⟨j,
      Finset.mem_range.mpr (hjd.trans_le hdn),
      Finset.mem_filter.mpr ⟨hdm.1, hj⟩⟩
  have hcard :
      (n.divisors.filter (fun d => ¬ naturalGridGood K d)).card ≤
        ∑ j ∈ Finset.range n, (badAt j).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  simp only [naturalGridRejectedFraction, naturalGridBadFraction,
    divisorPredicateFraction, if_neg hn]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  dsimp only [badAt] at hcard
  have hcard' :
      (n.divisors.filter (fun d => ¬ naturalGridGood K d)).card ≤
        ∑ j ∈ Finset.range n,
          (n.divisors.filter (naturalGridBadAt K j)).card := hcard
  have hcardReal :
      ((n.divisors.filter (fun d => ¬ naturalGridGood K d)).card : ℝ) ≤
        ((∑ j ∈ Finset.range n,
          (n.divisors.filter (naturalGridBadAt K j)).card : ℕ) : ℝ) := by
    exact_mod_cast hcard'
  push_cast at hcardReal
  convert hcardReal using 1

/-! ## Chernoff bound for one grid point -/

noncomputable def naturalTailThreshold (q : ℕ) : ℝ :=
  (2 / 5 : ℝ) * Real.log (q : ℝ) / Real.log 2

noncomputable def naturalDecayExponent : ℝ :=
  (1 / 10 : ℝ) - (2 / 5 : ℝ) * Real.log (6 / 5) / Real.log 2

lemma naturalDecayExponent_neg : naturalDecayExponent < 0 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h65 : 0 < (6 / 5 : ℝ) := by norm_num
  have hlogpow : Real.log (2 : ℝ) < 4 * Real.log (6 / 5 : ℝ) := by
    calc
      Real.log (2 : ℝ) < Real.log ((6 / 5 : ℝ) ^ 4) := by
        apply Real.log_lt_log (by norm_num)
        norm_num
      _ = 4 * Real.log (6 / 5 : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hratio : (1 / 4 : ℝ) < Real.log (6 / 5) / Real.log 2 := by
    rw [lt_div_iff₀ hlog2]
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hratio (by norm_num : (0 : ℝ) < 2 / 5)
  unfold naturalDecayExponent
  calc
    (1 / 10 : ℝ) - (2 / 5 : ℝ) * Real.log (6 / 5) / Real.log 2 =
        (1 / 10 : ℝ) - (2 / 5 : ℝ) *
          (Real.log (6 / 5) / Real.log 2) := by ring
    _ < (1 / 10 : ℝ) - (2 / 5 : ℝ) * (1 / 4 : ℝ) :=
      sub_lt_sub_left hmul _
    _ = 0 := by norm_num

lemma naturalGridBadAt_implies_threshold
    {K j d : ℕ} (hK : 0 < K) (hbad : naturalGridBadAt K j d) :
    naturalTailThreshold (naturalGridScale K j) ≤
      (omegaAtLogScale d (naturalGridScale K j) : ℝ) := by
  let q := naturalGridScale K j
  let m := omegaAtLogScale d q
  have hq : 0 < q := by
    dsimp [q, naturalGridScale]
    positivity
  have hpow : (q : ℝ) ^ 2 < (2 : ℝ) ^ (5 * m) := by
    exact_mod_cast hbad
  have hlog := Real.log_lt_log (pow_pos (by exact_mod_cast hq) 2) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold naturalTailThreshold
  dsimp [q, m] at *
  apply (div_le_iff₀ hlog2).2
  nlinarith

lemma naturalGridBadFraction_le_moment
    {K : ℕ} (hK : 0 < K) (j n : ℕ) :
    naturalGridBadFraction K j n ≤
      rankinScale (naturalTailThreshold (naturalGridScale K j)) (6 / 5) *
        NormalizedDivisorMoment448.fixedMoment
          (2 ^ naturalGridScale K j) n := by
  unfold naturalGridBadFraction
  have h := divisorPredicateFraction_le_rankin
    (naturalGridBadAt K j) (y := (6 / 5 : ℝ))
      (c := naturalTailThreshold (naturalGridScale K j))
      (u := (((2 ^ naturalGridScale K j : ℕ) : ℝ)))
      (by norm_num) (fun d hd =>
        one_le_rankinScale_mul_pow_of_one_lt (by norm_num)
          (naturalGridBadAt_implies_threshold hK hd)) n
  simpa [NormalizedDivisorMoment448.fixedMoment, omegaAtLogScale] using h

lemma naturalGridBadFraction_nonneg (K j n : ℕ) :
    0 ≤ naturalGridBadFraction K j n :=
  divisorPredicateFraction_nonneg _ _

lemma sum_naturalGridBadFraction_le_moment
    {K : ℕ} (hK : 0 < K) (j x : ℕ) :
    (∑ n ∈ Finset.range x, naturalGridBadFraction K j n) ≤
      rankinScale (naturalTailThreshold (naturalGridScale K j)) (6 / 5) *
        ∑ n ∈ Finset.range x,
          NormalizedDivisorMoment448.fixedMoment
            (2 ^ naturalGridScale K j) n := by
  calc
    (∑ n ∈ Finset.range x, naturalGridBadFraction K j n) ≤
        ∑ n ∈ Finset.range x,
          rankinScale (naturalTailThreshold (naturalGridScale K j)) (6 / 5) *
            NormalizedDivisorMoment448.fixedMoment
              (2 ^ naturalGridScale K j) n :=
      Finset.sum_le_sum fun n hn => naturalGridBadFraction_le_moment hK j n
    _ = rankinScale (naturalTailThreshold (naturalGridScale K j)) (6 / 5) *
        ∑ n ∈ Finset.range x,
          NormalizedDivisorMoment448.fixedMoment
            (2 ^ naturalGridScale K j) n := by
      rw [Finset.mul_sum]

lemma rankin_mul_log_pow_eq_decay (q : ℕ) (hq : 0 < q) :
    rankinScale (naturalTailThreshold q) (6 / 5) *
        (Real.log ((2 ^ q : ℕ) : ℝ)).rpow (1 / 10 : ℝ) =
      (Real.log 2).rpow (1 / 10 : ℝ) *
        Real.exp (naturalDecayExponent * Real.log (q : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogPow : Real.log (((2 ^ q : ℕ) : ℝ)) =
      (q : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogPowPos : 0 < Real.log (((2 ^ q : ℕ) : ℝ)) := by
    rw [hlogPow]
    positivity
  rw [rankinScale]
  change Real.exp (-naturalTailThreshold q * Real.log (6 / 5)) *
      Real.log (((2 ^ q : ℕ) : ℝ)) ^ (1 / 10 : ℝ) =
    Real.log 2 ^ (1 / 10 : ℝ) *
      Real.exp (naturalDecayExponent * Real.log (q : ℝ))
  rw [Real.rpow_def_of_pos hlogPowPos,
    Real.rpow_def_of_pos hlog2]
  rw [hlogPow, Real.log_mul (ne_of_gt hqR) (ne_of_gt hlog2)]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold naturalTailThreshold naturalDecayExponent
  field_simp [ne_of_gt hlog2]
  ring

lemma exp_decay_log_gridScale {K j : ℕ} (hK : 0 < K) :
    Real.exp (naturalDecayExponent *
        Real.log (naturalGridScale K j : ℝ)) =
      Real.exp (naturalDecayExponent * Real.log (K : ℝ)) *
        (Real.exp (naturalDecayExponent * Real.log 3)) ^ j := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  rw [naturalGridScale, Nat.cast_mul, Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  rw [Real.log_mul (ne_of_gt hKR) (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)),
    Real.log_pow]
  rw [mul_add, Real.exp_add, ← Real.exp_nat_mul]
  congr 1
  ring

lemma decayRatio_nonneg : 0 ≤ Real.exp (naturalDecayExponent * Real.log 3) :=
  (Real.exp_pos _).le

lemma decayRatio_lt_one : Real.exp (naturalDecayExponent * Real.log 3) < 1 := by
  rw [Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos naturalDecayExponent_neg
    (Real.log_pos (by norm_num))

lemma finite_decay_grid_sum_le (K x : ℕ) (hK : 0 < K) :
    (∑ j ∈ Finset.range x,
      Real.exp (naturalDecayExponent *
        Real.log (naturalGridScale K j : ℝ))) ≤
      Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
        (1 - Real.exp (naturalDecayExponent * Real.log 3)) := by
  let r := Real.exp (naturalDecayExponent * Real.log 3)
  have hgeom := hasSum_geometric_of_lt_one decayRatio_nonneg decayRatio_lt_one
  have hfinite : (∑ j ∈ Finset.range x, r ^ j) ≤ (1 - r)⁻¹ := by
    rw [← hgeom.tsum_eq]
    exact hgeom.summable.sum_le_tsum (Finset.range x) (fun j hj => by positivity)
  calc
    (∑ j ∈ Finset.range x,
      Real.exp (naturalDecayExponent *
        Real.log (naturalGridScale K j : ℝ))) =
        Real.exp (naturalDecayExponent * Real.log (K : ℝ)) *
          ∑ j ∈ Finset.range x, r ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact exp_decay_log_gridScale hK
    _ ≤ Real.exp (naturalDecayExponent * Real.log (K : ℝ)) *
        (1 - r)⁻¹ :=
      mul_le_mul_of_nonneg_left hfinite (Real.exp_pos _).le
    _ = Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
        (1 - Real.exp (naturalDecayExponent * Real.log 3)) := by
      simp only [r, div_eq_mul_inv]

lemma gridDecayCoefficient_tendsto_zero :
    Tendsto (fun K : ℕ =>
      Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
        (1 - Real.exp (naturalDecayExponent * Real.log 3)))
      atTop (𝓝 0) := by
  have hpow : Tendsto
      (fun K : ℕ => Real.exp (naturalDecayExponent * Real.log (K : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop
      (neg_pos.mpr naturalDecayExponent_neg)).comp tendsto_natCast_atTop_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with K hK
    change (K : ℝ) ^ (- -naturalDecayExponent) =
      Real.exp (naturalDecayExponent * Real.log (K : ℝ))
    rw [Real.rpow_def_of_pos (by exact_mod_cast hK : (0 : ℝ) < K)]
    congr 1
    ring
  have := hpow.mul_const
    ((1 - Real.exp (naturalDecayExponent * Real.log 3))⁻¹)
  simpa only [div_eq_mul_inv, zero_mul] using this

lemma fixedMoment_range_le_partialSum (Y x : ℕ) (hx : 0 < x) :
    (∑ n ∈ Finset.range x, NormalizedDivisorMoment448.fixedMoment Y n) ≤
      HalberstamScratch.partialSum
        (NormalizedDivisorMoment448.fixedMoment Y) x := by
  let S := (Finset.range x).erase 0
  have hzero : 0 ∈ Finset.range x := Finset.mem_range.mpr hx
  have hrange :
      (∑ n ∈ Finset.range x, NormalizedDivisorMoment448.fixedMoment Y n) =
        ∑ n ∈ S, NormalizedDivisorMoment448.fixedMoment Y n := by
    have hsplit := Finset.sum_erase_add (Finset.range x)
      (NormalizedDivisorMoment448.fixedMoment Y) hzero
    simp only [NormalizedDivisorMoment448.fixedMoment_zero, add_zero] at hsplit
    exact hsplit.symm
  rw [hrange, HalberstamScratch.partialSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hn' := Finset.mem_erase.mp hn
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr hn'.1,
        (Nat.le_of_lt (Finset.mem_range.mp hn'.2))⟩
  · intro n hn hnot
    exact NormalizedDivisorMoment448.fixedMoment_nonneg Y n

theorem exists_fixedMoment_range_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x Y : ℕ, 2 ≤ x → 2 ≤ Y →
        (∑ n ∈ Finset.range x,
          NormalizedDivisorMoment448.fixedMoment Y n) ≤
          C * (x : ℝ) *
            (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
  rcases NormalizedDivisorMoment448.exists_fixedMoment_partialSum_uniform with
    ⟨C, hC, hmean⟩
  refine ⟨C, hC, fun x Y hx hY => ?_⟩
  exact (fixedMoment_range_le_partialSum Y x (by omega)).trans
    (hmean x Y hx hY)

lemma one_grid_sum_bound
    {C : ℝ} (hC : 0 ≤ C)
    (hmoment : ∀ x Y : ℕ, 2 ≤ x → 2 ≤ Y →
      (∑ n ∈ Finset.range x,
        NormalizedDivisorMoment448.fixedMoment Y n) ≤
        C * (x : ℝ) * (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ))
    {K : ℕ} (hK : 0 < K) (j x : ℕ) (hx : 2 ≤ x) :
    (∑ n ∈ Finset.range x, naturalGridBadFraction K j n) ≤
      (C * (Real.log 2).rpow (1 / 10 : ℝ)) * (x : ℝ) *
        Real.exp (naturalDecayExponent *
          Real.log (naturalGridScale K j : ℝ)) := by
  let q := naturalGridScale K j
  have hq : 0 < q := by
    dsimp [q, naturalGridScale]
    positivity
  have hY : 2 ≤ 2 ^ q := by
    exact (show 2 ^ 1 ≤ 2 ^ q from Nat.pow_le_pow_right (by omega) hq)
  have hpoint := sum_naturalGridBadFraction_le_moment hK j x
  have hmean := hmoment x (2 ^ q) hx hY
  have hscale : 0 ≤ rankinScale (naturalTailThreshold q) (6 / 5) :=
    (rankinScale_pos _ _).le
  calc
    (∑ n ∈ Finset.range x, naturalGridBadFraction K j n) ≤
        rankinScale (naturalTailThreshold q) (6 / 5) *
          ∑ n ∈ Finset.range x,
            NormalizedDivisorMoment448.fixedMoment (2 ^ q) n := by
      simpa [q] using hpoint
    _ ≤ rankinScale (naturalTailThreshold q) (6 / 5) *
        (C * (x : ℝ) *
          (Real.log ((2 ^ q : ℕ) : ℝ)).rpow (1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmean hscale
    _ = (C * (Real.log 2).rpow (1 / 10 : ℝ)) * (x : ℝ) *
        Real.exp (naturalDecayExponent * Real.log (q : ℝ)) := by
      have hid := rankin_mul_log_pow_eq_decay q hq
      calc
        rankinScale (naturalTailThreshold q) (6 / 5) *
            (C * (x : ℝ) *
              (Real.log ((2 ^ q : ℕ) : ℝ)).rpow (1 / 10 : ℝ)) =
            (C * (x : ℝ)) *
              (rankinScale (naturalTailThreshold q) (6 / 5) *
                (Real.log ((2 ^ q : ℕ) : ℝ)).rpow (1 / 10 : ℝ)) := by ring
        _ = (C * (x : ℝ)) *
            ((Real.log 2).rpow (1 / 10 : ℝ) *
              Real.exp (naturalDecayExponent * Real.log (q : ℝ))) := by
          rw [hid]
        _ = (C * (Real.log 2).rpow (1 / 10 : ℝ)) * (x : ℝ) *
            Real.exp (naturalDecayExponent * Real.log (q : ℝ)) := by ring

lemma sum_rejectedFraction_le_grid_sum (K x : ℕ) :
    (∑ n ∈ Finset.range x, naturalGridRejectedFraction K n) ≤
      ∑ j ∈ Finset.range x,
        ∑ n ∈ Finset.range x, naturalGridBadFraction K j n := by
  calc
    (∑ n ∈ Finset.range x, naturalGridRejectedFraction K n) ≤
        ∑ n ∈ Finset.range x,
          ∑ j ∈ Finset.range n, naturalGridBadFraction K j n :=
      Finset.sum_le_sum fun n hn => naturalGridRejectedFraction_le_sum K n
    _ ≤ ∑ n ∈ Finset.range x,
          ∑ j ∈ Finset.range x, naturalGridBadFraction K j n := by
      apply Finset.sum_le_sum
      intro n hn
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hn)))
        (fun j hj hnot => naturalGridBadFraction_nonneg K j n)
    _ = ∑ j ∈ Finset.range x,
        ∑ n ∈ Finset.range x, naturalGridBadFraction K j n := by
      rw [Finset.sum_comm]

lemma rejected_sum_bound
    {C : ℝ} (hC : 0 ≤ C)
    (hmoment : ∀ x Y : ℕ, 2 ≤ x → 2 ≤ Y →
      (∑ n ∈ Finset.range x,
        NormalizedDivisorMoment448.fixedMoment Y n) ≤
        C * (x : ℝ) * (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ))
    {K : ℕ} (hK : 0 < K) {x : ℕ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.range x, naturalGridRejectedFraction K n) ≤
      (C * (Real.log 2).rpow (1 / 10 : ℝ)) * (x : ℝ) *
        (Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
          (1 - Real.exp (naturalDecayExponent * Real.log 3))) := by
  have hstart := sum_rejectedFraction_le_grid_sum K x
  have hper :
      (∑ j ∈ Finset.range x,
        ∑ n ∈ Finset.range x, naturalGridBadFraction K j n) ≤
      ∑ j ∈ Finset.range x,
        (C * (Real.log 2).rpow (1 / 10 : ℝ)) * (x : ℝ) *
          Real.exp (naturalDecayExponent *
            Real.log (naturalGridScale K j : ℝ)) := by
    exact Finset.sum_le_sum fun j hj => one_grid_sum_bound hC hmoment hK j x hx
  calc
    (∑ n ∈ Finset.range x, naturalGridRejectedFraction K n) ≤
        ∑ j ∈ Finset.range x,
          ∑ n ∈ Finset.range x, naturalGridBadFraction K j n := hstart
    _ ≤ ∑ j ∈ Finset.range x,
        (C * (Real.log 2).rpow (1 / 10 : ℝ)) * (x : ℝ) *
          Real.exp (naturalDecayExponent *
            Real.log (naturalGridScale K j : ℝ)) := hper
    _ = (C * (Real.log 2).rpow (1 / 10 : ℝ)) * (x : ℝ) *
        ∑ j ∈ Finset.range x,
          Real.exp (naturalDecayExponent *
            Real.log (naturalGridScale K j : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (C * (Real.log 2).rpow (1 / 10 : ℝ)) * (x : ℝ) *
        (Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
          (1 - Real.exp (naturalDecayExponent * Real.log 3))) := by
      apply mul_le_mul_of_nonneg_left (finite_decay_grid_sum_le K x hK)
      exact mul_nonneg (mul_nonneg hC
        (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _).le)
        (Nat.cast_nonneg x)

theorem exists_naturalGrid_firstMoment :
    ∃ K : ℕ, 0 < K ∧
      ∀ᶠ x : ℕ in atTop,
        (∑ n ∈ Finset.range x, naturalGridRejectedFraction K n) ≤
          (1 / 20 : ℝ) * x := by
  rcases exists_fixedMoment_range_uniform with ⟨C, hC, hmoment⟩
  let A := C * (Real.log 2).rpow (1 / 10 : ℝ)
  have hcoef : Tendsto (fun K : ℕ => A *
      (Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
        (1 - Real.exp (naturalDecayExponent * Real.log 3))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul gridDecayCoefficient_tendsto_zero)
  have hev : ∀ᶠ K : ℕ in atTop,
      A * (Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
        (1 - Real.exp (naturalDecayExponent * Real.log 3))) < (1 / 20 : ℝ) :=
    (tendsto_order.1 hcoef).2 _ (by norm_num)
  rcases (hev.and (eventually_gt_atTop 0)).exists with ⟨K, hsmall, hK⟩
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hbound := rejected_sum_bound hC hmoment hK hx
  calc
    (∑ n ∈ Finset.range x, naturalGridRejectedFraction K n) ≤
        A * (x : ℝ) *
          (Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
            (1 - Real.exp (naturalDecayExponent * Real.log 3))) := by
      simpa [A] using hbound
    _ = (A *
          (Real.exp (naturalDecayExponent * Real.log (K : ℝ)) /
            (1 - Real.exp (naturalDecayExponent * Real.log 3)))) * x := by ring
    _ ≤ (1 / 20 : ℝ) * x :=
      mul_le_mul_of_nonneg_right hsmall.le (Nat.cast_nonneg x)

theorem naturalGridRejectedFraction_nonneg (K n : ℕ) :
    0 ≤ naturalGridRejectedFraction K n := by
  simp only [naturalGridRejectedFraction]
  split_ifs <;> positivity

/-- The positive-mass set on which at least four fifths of the divisors
survive all natural-grid upper-tail tests. -/
def naturalGridFourFifthsSet (K : ℕ) : Set ℕ :=
  {n : ℕ | 4 * n.divisors.card ≤
    5 * (naturalGridSelectedDivisors K n).card}

theorem compl_naturalGridFourFifthsSet_subset_superlevel (K : ℕ) :
    (naturalGridFourFifthsSet K)ᶜ ⊆
      {n : ℕ | (1 / 5 : ℝ) < naturalGridRejectedFraction K n} := by
  intro n hn
  have hnot : ¬4 * n.divisors.card ≤
      5 * (naturalGridSelectedDivisors K n).card := hn
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    simp [naturalGridSelectedDivisors] at hnot
  have htau : 0 < n.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
  have hpartition :
      (naturalGridSelectedDivisors K n).card +
          (n.divisors.filter fun d ↦ ¬ naturalGridGood K d).card =
        n.divisors.card := by
    simpa [naturalGridSelectedDivisors] using
      (Finset.card_filter_add_card_filter_not
        (s := n.divisors) (naturalGridGood K))
  have hrejectedNat : n.divisors.card <
      5 * (n.divisors.filter fun d ↦ ¬ naturalGridGood K d).card := by
    omega
  change (1 / 5 : ℝ) < naturalGridRejectedFraction K n
  simp only [naturalGridRejectedFraction, if_neg hn0]
  apply (lt_div_iff₀ (by exact_mod_cast htau :
    (0 : ℝ) < n.divisors.card)).2
  have hrejectedReal : (n.divisors.card : ℝ) <
      5 * ((n.divisors.filter fun d ↦ ¬ naturalGridGood K d).card : ℝ) := by
    exact_mod_cast hrejectedNat
  linarith

theorem naturalGridFourFifthsSet_compl_upperDensity_le_one_fourth
    (K : ℕ)
    (hmean : ∀ᶠ x : ℕ in atTop,
      (∑ n ∈ Finset.range x, naturalGridRejectedFraction K n) ≤
        (1 / 20 : ℝ) * x) :
    ((naturalGridFourFifthsSet K)ᶜ : Set ℕ).upperDensity ≤ 1 / 4 := by
  calc
    ((naturalGridFourFifthsSet K)ᶜ : Set ℕ).upperDensity ≤
        ({n : ℕ | (1 / 5 : ℝ) < naturalGridRejectedFraction K n} :
          Set ℕ).upperDensity :=
      Erdos448.upperDensity_mono
        (compl_naturalGridFourFifthsSet_subset_superlevel K)
    _ ≤ (1 / 20 : ℝ) / (1 / 5 : ℝ) :=
      Erdos448.upperDensity_superlevel_le
        (naturalGridRejectedFraction K)
        (naturalGridRejectedFraction_nonneg K) (by norm_num) hmean
    _ = 1 / 4 := by norm_num

/-- Unconditional natural-grid selector package: a fixed positive grid origin,
an eventual rejected-mass bound, and hence a four-fifths set whose complement
has upper density at most one fourth. -/
theorem exists_naturalGrid_goodSet :
    ∃ K : ℕ, 0 < K ∧
      ((naturalGridFourFifthsSet K)ᶜ : Set ℕ).upperDensity ≤ 1 / 4 := by
  rcases exists_naturalGrid_firstMoment with ⟨K, hK, hmean⟩
  exact ⟨K, hK,
    naturalGridFourFifthsSet_compl_upperDensity_le_one_fourth K hmean⟩

/-! ## The normalized exponential moment and its local Euler factors -/

noncomputable def naturalMoment (q n : ℕ) : ℝ :=
  divisorMoment (6 / 5 : ℝ) (((2 ^ q : ℕ) : ℝ)) n

noncomputable def naturalMomentAF (q : ℕ) : ArithmeticFunction ℝ :=
  divisorMomentAF (6 / 5 : ℝ) (((2 ^ q : ℕ) : ℝ))

lemma naturalMoment_nonneg (q n : ℕ) : 0 ≤ naturalMoment q n :=
  divisorMoment_nonneg (by norm_num) _ _

@[simp] lemma naturalMoment_zero (q : ℕ) : naturalMoment q 0 = 0 := by
  simp [naturalMoment]

@[simp] lemma naturalMoment_one (q : ℕ) : naturalMoment q 1 = 1 := by
  simp [naturalMoment]

lemma naturalMoment_mul {q a b : ℕ} (hab : a.Coprime b) :
    naturalMoment q (a * b) = naturalMoment q a * naturalMoment q b :=
  divisorMoment_mul hab _ _

lemma geom_average_six_fifths_le_pow (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), (6 / 5 : ℝ) ^ i) / (j + 1 : ℝ) ≤
      (6 / 5 : ℝ) ^ j := by
  have hsum : (∑ i ∈ Finset.range (j + 1), (6 / 5 : ℝ) ^ i) ≤
      ∑ _i ∈ Finset.range (j + 1), (6 / 5 : ℝ) ^ j := by
    apply Finset.sum_le_sum
    intro i hi
    exact pow_le_pow_right₀ (by norm_num)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hj : (0 : ℝ) < j + 1 := by positivity
  calc
    (∑ i ∈ Finset.range (j + 1), (6 / 5 : ℝ) ^ i) / (j + 1 : ℝ) ≤
        (∑ _i ∈ Finset.range (j + 1), (6 / 5 : ℝ) ^ j) /
          (j + 1 : ℝ) := div_le_div_of_nonneg_right hsum hj.le
    _ = (6 / 5 : ℝ) ^ j := by simp [ne_of_gt hj]

lemma naturalMoment_prime_pow_le {q p j : ℕ} (hp : p.Prime) :
    naturalMoment q (p ^ j) ≤ (6 / 5 : ℝ) ^ j := by
  rw [naturalMoment, divisorMoment_prime_pow (6 / 5)
    (((2 ^ q : ℕ) : ℝ)) hp]
  by_cases hcut : (p : ℝ) < ((2 ^ q : ℕ) : ℝ)
  · simp only [if_pos hcut]
    simpa only [Nat.cast_add, Nat.cast_one] using
      geom_average_six_fifths_le_pow j
  · simp only [if_neg hcut]
    simp only [pow_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [div_self (by positivity : (j + 1 : ℝ) ≠ 0)]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 6 / 5)

lemma naturalMoment_prime {q p : ℕ} (hp : p.Prime)
    (hcut : (p : ℝ) < ((2 ^ q : ℕ) : ℝ)) :
    naturalMoment q p = 11 / 10 := by
  rw [show p = p ^ 1 by simp, naturalMoment,
    divisorMoment_prime_pow (6 / 5) (((2 ^ q : ℕ) : ℝ)) hp]
  simp only [if_pos hcut]
  norm_num [Finset.sum_range_succ]

lemma naturalMoment_prime_pow_eq_one_of_not_lt {q p j : ℕ}
    (hp : p.Prime) (hcut : ¬(p : ℝ) < ((2 ^ q : ℕ) : ℝ)) :
    naturalMoment q (p ^ j) = 1 := by
  exact divisorMoment_prime_pow_eq_one_of_not_lt _ _ hp hcut

noncomputable def naturalLocalEuler (q p : ℕ) : ℝ :=
  ∑' j : ℕ, naturalMoment q (p ^ j) / ((p ^ j : ℕ) : ℝ)

lemma naturalLocalEuler_summable (q : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ =>
      ‖naturalMoment q (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) := by
  have hpow : ∀ j : ℕ, naturalMoment q (p ^ (j + 1)) ≤
      (6 / 5 : ℝ) * (6 / 5 : ℝ) ^ j := by
    intro j
    simpa [pow_succ, mul_comm] using
      naturalMoment_prime_pow_le (q := q) hp (j := j + 1)
  exact (HalberstamScratch.prime_power_local_mass
    (naturalMoment q) p (6 / 5) (6 / 5) hp
    (naturalMoment_nonneg q) (naturalMoment_one q)
    (by norm_num) (by norm_num) (by norm_num) hpow).1

lemma naturalLocalEuler_nonneg (q : ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ naturalLocalEuler q p := by
  apply tsum_nonneg
  intro j
  exact div_nonneg (naturalMoment_nonneg q _) (Nat.cast_nonneg _)

lemma naturalLocalEuler_eq_geometric_of_not_lt (q : ℕ) {p : ℕ}
    (hp : p.Prime) (hcut : ¬(p : ℝ) < ((2 ^ q : ℕ) : ℝ)) :
    naturalLocalEuler q p = (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hpR : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hpInv : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by exact_mod_cast hp.pos)]
    exact_mod_cast hp.one_lt
  rw [naturalLocalEuler]
  calc
    (∑' j : ℕ, naturalMoment q (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
        ∑' j : ℕ, ((p : ℝ)⁻¹) ^ j := by
      apply tsum_congr
      intro j
      rw [naturalMoment_prime_pow_eq_one_of_not_lt hp hcut]
      simp only [one_div, Nat.cast_pow, inv_pow]
    _ = (1 - (p : ℝ)⁻¹)⁻¹ :=
      (hasSum_geometric_of_lt_one hpR hpInv).tsum_eq

lemma naturalLocalEuler_le_raw (q : ℕ) {p : ℕ} (hp : p.Prime)
    (hcut : (p : ℝ) < ((2 ^ q : ℕ) : ℝ)) :
    naturalLocalEuler q p ≤
      1 + (11 / 10 : ℝ) / p +
        ((6 / 5 : ℝ) / p) ^ 2 * (1 - (6 / 5 : ℝ) / p)⁻¹ := by
  let a : ℕ → ℝ := fun j =>
    naturalMoment q (p ^ j) / ((p ^ j : ℕ) : ℝ)
  let b : ℕ → ℝ := fun j => ((6 / 5 : ℝ) / p) ^ j
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : 0 ≤ (6 / 5 : ℝ) / p := by positivity
  have hr1 : (6 / 5 : ℝ) / p < 1 := by
    apply (div_lt_one hpR).2
    exact (by norm_num : (6 / 5 : ℝ) < 2).trans_le (by exact_mod_cast hp.two_le)
  have hb : Summable b := summable_geometric_of_lt_one hr0 hr1
  have haNorm := naturalLocalEuler_summable q hp
  have ha : Summable a := haNorm.of_norm
  have htail : ∀ j : ℕ, a (j + 2) ≤ b (j + 2) := by
    intro j
    dsimp [a, b]
    have hden : 0 ≤ (((p ^ (j + 2) : ℕ) : ℝ)) := Nat.cast_nonneg _
    calc
      naturalMoment q (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) ≤
          (6 / 5 : ℝ) ^ (j + 2) / ((p ^ (j + 2) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (naturalMoment_prime_pow_le hp) hden
      _ = ((6 / 5 : ℝ) / p) ^ (j + 2) := by
        rw [Nat.cast_pow]
        ring
  have haTail : Summable (fun j : ℕ => a (j + 2)) :=
    (summable_nat_add_iff 2).mpr ha
  have hbTailSummable : Summable (fun j : ℕ => b (j + 2)) :=
    (summable_nat_add_iff 2).mpr hb
  have htailSum : (∑' j : ℕ, a (j + 2)) ≤ ∑' j : ℕ, b (j + 2) :=
    haTail.tsum_le_tsum htail hbTailSummable
  have haSplit : (∑' j : ℕ, a j) = a 0 + a 1 + ∑' j : ℕ, a (j + 2) := by
    rw [ha.tsum_eq_zero_add]
    have hat := (summable_nat_add_iff 1).mpr ha
    rw [hat.tsum_eq_zero_add]
    ring
  have hbTail : (∑' j : ℕ, b (j + 2)) =
      ((6 / 5 : ℝ) / p) ^ 2 * (1 - (6 / 5 : ℝ) / p)⁻¹ := by
    rw [show (fun j : ℕ => b (j + 2)) = fun j =>
        ((6 / 5 : ℝ) / p) ^ 2 * ((6 / 5 : ℝ) / p) ^ j by
      funext j
      simp [b, pow_add, mul_comm]]
    rw [tsum_mul_left, (hasSum_geometric_of_lt_one hr0 hr1).tsum_eq]
  rw [naturalLocalEuler, haSplit]
  have ha0 : a 0 = 1 := by simp [a, naturalMoment_one]
  have ha1 : a 1 = (11 / 10 : ℝ) / p := by
    simp [a, naturalMoment_prime hp hcut]
  rw [ha0, ha1]
  linarith

lemma naturalLocalEuler_le_baseline_mul_correction
    (q : ℕ) {p : ℕ} (hp : p.Prime) :
    naturalLocalEuler q p ≤
      (1 - (p : ℝ)⁻¹)⁻¹ *
        (if (p : ℝ) < ((2 ^ q : ℕ) : ℝ) then
          1 + (1 / 10 : ℝ) / p + 5 / (p : ℝ) ^ 2 else 1) := by
  by_cases hcut : (p : ℝ) < ((2 ^ q : ℕ) : ℝ)
  · rw [if_pos hcut]
    have hraw := naturalLocalEuler_le_raw q hp hcut
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by positivity
    have hp1 : (0 : ℝ) < p - 1 := by linarith
    have hr0 : 0 ≤ (6 / 5 : ℝ) / p := by positivity
    have hrle : (6 / 5 : ℝ) / p ≤ 3 / 5 := by
      rw [div_le_iff₀ hp0]
      nlinarith
    have hden : (2 / 5 : ℝ) ≤ 1 - (6 / 5 : ℝ) / p := by linarith
    have hdenpos : 0 < 1 - (6 / 5 : ℝ) / p := lt_of_lt_of_le (by norm_num) hden
    have hinv : (1 - (6 / 5 : ℝ) / p)⁻¹ ≤ 5 / 2 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hdenpos).2
      nlinarith
    have hsq : ((6 / 5 : ℝ) / p) ^ 2 ≤
        (36 / 25 : ℝ) / p ^ 2 := by
      ring_nf
      exact le_rfl
    have htail : ((6 / 5 : ℝ) / p) ^ 2 *
        (1 - (6 / 5 : ℝ) / p)⁻¹ ≤ (18 / 5 : ℝ) / p ^ 2 := by
      calc
        ((6 / 5 : ℝ) / p) ^ 2 *
            (1 - (6 / 5 : ℝ) / p)⁻¹ ≤
            ((6 / 5 : ℝ) / p) ^ 2 * (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
        _ = (18 / 5 : ℝ) / p ^ 2 := by ring
    have hbase : (1 + (p : ℝ)⁻¹) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [inv_eq_one_div]
      field_simp [ne_of_gt hp0, ne_of_gt hp1]
      nlinarith
    have hcorr : 0 ≤ 1 + (1 / 10 : ℝ) / p + 5 / (p : ℝ) ^ 2 := by
      positivity
    calc
      naturalLocalEuler q p ≤
          1 + (11 / 10 : ℝ) / p +
            ((6 / 5 : ℝ) / p) ^ 2 *
              (1 - (6 / 5 : ℝ) / p)⁻¹ := hraw
      _ ≤ 1 + (11 / 10 : ℝ) / p + (18 / 5 : ℝ) / p ^ 2 := by
        linarith
      _ ≤ (1 + (p : ℝ)⁻¹) *
          (1 + (1 / 10 : ℝ) / p + 5 / (p : ℝ) ^ 2) := by
        have hpSq : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos hp0
        rw [one_div]
        field_simp [ne_of_gt hp0, ne_of_gt hpSq]
        nlinarith
      _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ *
          (1 + (1 / 10 : ℝ) / p + 5 / (p : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hbase hcorr
  · rw [if_neg hcut, mul_one]
    exact (naturalLocalEuler_eq_geometric_of_not_lt q hp hcut).le

end NaturalGridConcentration448

#print axioms NaturalGridConcentration448.one_le_naturalGridWeight_of_good
#print axioms NaturalGridConcentration448.exists_naturalGrid_firstMoment
#print axioms NaturalGridConcentration448.exists_naturalGrid_goodSet
