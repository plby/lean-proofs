import Mathlib

open scoped BigOperators
open Finset

namespace PrimePowerMassLinear448

/-- A deliberately generous but completely explicit dyadic estimate. -/
lemma dyadic_weight_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k)) =
      4 - (((2 * n + 4 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hpow]
      ring

lemma dyadic_weight_sum_le_four (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k)) ≤ 4 := by
  rw [dyadic_weight_sum_eq]
  exact sub_le_self _ (div_nonneg (by positivity) (by positivity))

lemma prime_log_div_sq_dyadic_block_le (k : ℕ) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
      (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
  classical
  let B : Finset ℕ := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcard : B.card ≤ 2 ^ k := by
    calc
      B.card ≤ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card :=
        Finset.card_filter_le _ _
      _ = 2 ^ k := by
        rw [Nat.card_Ico, pow_succ]
        omega
  have hpoint : ∀ p ∈ B,
      Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
        (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) := by
    intro p hp
    have hpB := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hpB.1
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpB.2.pos
    have hlow : ((2 ^ k : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpIco.1
    have hupp : (p : ℝ) ≤ (((2 ^ (k + 1) : ℕ) : ℝ)) := by
      exact_mod_cast hpIco.2.le
    have hlog : Real.log (p : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      calc
        Real.log (p : ℝ) ≤ Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) :=
          Real.log_le_log hpPos hupp
        _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
          rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num,
            Real.log_pow]
    have hlowSq : (((2 ^ k : ℕ) : ℝ)) ^ 2 ≤ (p : ℝ) ^ 2 := by gcongr
    have hnumNonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 :=
      mul_nonneg (by positivity) hlog2
    calc
      Real.log (p : ℝ) / (p : ℝ) ^ 2
          ≤ (((k + 1 : ℕ) : ℝ) * Real.log 2) / (p : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hlog (sq_nonneg _)
      _ ≤ (((k + 1 : ℕ) : ℝ) * Real.log 2) /
            (((2 ^ k : ℕ) : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_left hnumNonneg (by positivity) hlowSq
      _ = (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) := by
          rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num, ← pow_mul]
          simp [Nat.mul_comm]
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) ^ 2)
        = ∑ p ∈ B, Real.log (p : ℝ) / (p : ℝ) ^ 2 := rfl
    _ ≤ ∑ p ∈ B,
          (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) :=
      Finset.sum_le_sum hpoint
    _ = (B.card : ℝ) *
          ((((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ k : ℕ) : ℝ) *
          ((((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k)) := by
      gcongr
    _ = (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
      rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num]
      have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [show (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k by
        rw [two_mul, pow_add]]
      field_simp [hpow]

theorem sum_primesLE_log_div_sq_le (Y : ℕ) :
    (∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
      4 * Real.log 2 := by
  classical
  let S : Finset ℕ := Nat.primesLE Y
  let T : Finset ℕ := Finset.range (Nat.log 2 Y + 1)
  have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ T := by
    intro p hp
    have hpS := Nat.mem_primesLE.mp hp
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.log_mono_right hpS.1))
  have hdecomp :
      (∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2) =
        ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun p : ℕ => Real.log (p : ℝ) / (p : ℝ) ^ 2)
  have hfiber : ∀ k ∈ T,
      (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
    intro k hk
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpFilter := Finset.mem_filter.mp hp
      have hpS := Nat.mem_primesLE.mp hpFilter.1
      have hpPrime : Nat.Prime p := hpS.2
      have hpNe : p ≠ 0 := hpPrime.ne_zero
      have hlog : Nat.log 2 p = k := hpFilter.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr
          ⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpNe,
            by simpa [hlog, Nat.succ_eq_add_one] using
              Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩,
          hpPrime⟩
    · intro p hp _hnot
      have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
        (sq_nonneg _)
  calc
    (∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) / (p : ℝ) ^ 2)
        = ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ 2 := rfl
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2 := hdecomp.symm
    _ ≤ ∑ k ∈ T,
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum hfiber
    _ ≤ ∑ k ∈ T,
          (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
      exact Finset.sum_le_sum (fun k hk => prime_log_div_sq_dyadic_block_le k)
    _ = Real.log 2 *
          ∑ k ∈ T, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ Real.log 2 * 4 := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [T] using dyadic_weight_sum_le_four (Nat.log 2 Y + 1))
        (Real.log_nonneg (by norm_num))
    _ = 4 * Real.log 2 := by ring

/-- The finite encoding of pairs `(p,j)` for the prime power `p^(j+1) ≤ Q`. -/
def primePowerPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.primesLE Q ×ˢ Finset.range Q).filter fun pj => pj.1 ^ (pj.2 + 1) ≤ Q

/-- The prime-power logarithmic mass used in the Halberstam--Richert proof. -/
noncomputable def pairPrimePowerMass (h : ℕ → ℝ) (Q : ℕ) : ℝ :=
  ∑ pj ∈ primePowerPairs Q,
    h (pj.1 ^ (pj.2 + 1)) * Real.log ((pj.1 ^ (pj.2 + 1) : ℕ) : ℝ)

/-- The exact mass used by `PrimePowerConvolution448`: the prime `p` runs
below `Q+1` and the positive exponent runs through `1,...,log_p Q`. -/
noncomputable def primePowerMass (h : ℕ → ℝ) (Q : ℕ) : ℝ :=
  ∑ p ∈ (Q + 1).primesBelow,
    ∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
      h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)

/-- Explicit constant for the linear prime-power mass bound. -/
noncomputable def massConstant (lambda1 lambda2 : ℝ) : ℝ :=
  lambda1 *
    (Real.log 4 +
      8 * lambda2 * Real.log 2 / (1 - lambda2 / 2) ^ 2)

lemma primePowerPairs_zero : primePowerPairs 0 = ∅ := by
  simp [primePowerPairs]

lemma pairPrimePowerMass_zero (h : ℕ → ℝ) : pairPrimePowerMass h 0 = 0 := by
  simp [pairPrimePowerMass, primePowerPairs]

lemma sum_Icc_one_eq_sum_range_succ (f : ℕ → ℝ) (L : ℕ) :
    (∑ nu ∈ Finset.Icc 1 L, f nu) =
      ∑ j ∈ Finset.range L, f (j + 1) := by
  have hIcc : Finset.Icc 1 L = Finset.Ico 1 (L + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hlen : L + 1 - 1 = L := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm]

lemma primesBelow_succ_eq_primesLE (Q : ℕ) :
    (Q + 1).primesBelow = Nat.primesLE Q := by
  ext p
  simp [Nat.mem_primesBelow, Nat.mem_primesLE]

lemma weighted_geometric_tail_le
    (lambda2 : ℝ) (hlambda2 : 0 ≤ lambda2) (hlambda2_lt : lambda2 < 2)
    (N : ℕ) :
    (∑ k ∈ Finset.range N,
        lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) ≤
      2 * lambda2 / (1 - lambda2 / 2) ^ 2 := by
  let r : ℝ := lambda2 / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnat := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hrnorm
  have hgeom := hasSum_geometric_of_lt_one hr0 hr1
  have hsum : HasSum (fun k : ℕ => ((k + 2 : ℕ) : ℝ) * r ^ k)
      (r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹) := by
    convert hnat.add (hgeom.mul_left 2) using 1 <;> ext k <;> push_cast <;> ring
  have hnonneg : ∀ k : ℕ, 0 ≤ ((k + 2 : ℕ) : ℝ) * r ^ k := by
    intro k
    positivity
  have hfinite :
      (∑ k ∈ Finset.range N, ((k + 2 : ℕ) : ℝ) * r ^ k) ≤
        r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹ := by
    rw [← hsum.tsum_eq]
    exact hsum.summable.sum_le_tsum (Finset.range N) (fun k _hk => hnonneg k)
  have hone : 0 < 1 - r := sub_pos.mpr hr1
  have hcoarse : r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹ ≤
      2 / (1 - r) ^ 2 := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hone)).2
    field_simp [ne_of_gt hone]
    nlinarith
  calc
    (∑ k ∈ Finset.range N,
        lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) =
        lambda2 * ∑ k ∈ Finset.range N,
          (((k + 2 : ℕ) : ℝ) * r ^ k) := by
      simp only [r, Finset.mul_sum]
    _ ≤ lambda2 * (2 / (1 - r) ^ 2) :=
      mul_le_mul_of_nonneg_left (hfinite.trans hcoarse) hlambda2
    _ = 2 * lambda2 / (1 - lambda2 / 2) ^ 2 := by
      dsimp [r]
      ring

lemma tail_prime_power_term_le
    (h : ℕ → ℝ) (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1) (hlambda2 : 0 ≤ lambda2)
    (hpow : ∀ (p j : ℕ), p.Prime →
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    {Q p k : ℕ} (hp : p.Prime) :
    (if p ^ (k + 2) ≤ Q then
        h (p ^ (k + 2)) * Real.log ((p ^ (k + 2) : ℕ) : ℝ)
      else 0) ≤
      lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) *
        (lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : 2 ≤ p := hp.two_le
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hright : 0 ≤
      lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) *
        (lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) := by
    positivity
  split_ifs with hpQ
  · have hpowLowerNat : p ^ 2 * 2 ^ k ≤ p ^ (k + 2) := by
      rw [show k + 2 = 2 + k by omega, pow_add]
      exact Nat.mul_le_mul_left (p ^ 2) (Nat.pow_le_pow_left hpTwo k)
    have hbaseQNat : p ^ 2 * 2 ^ k ≤ Q := hpowLowerNat.trans hpQ
    have hbasePos : 0 < (p : ℝ) ^ 2 * (2 : ℝ) ^ k := by positivity
    have hbaseQ : (p : ℝ) ^ 2 * (2 : ℝ) ^ k ≤ (Q : ℝ) := by
      exact_mod_cast hbaseQNat
    have hratio : 1 ≤ (Q : ℝ) / ((p : ℝ) ^ 2 * (2 : ℝ) ^ k) :=
      (le_div_iff₀ hbasePos).2 (by simpa using hbaseQ)
    have hA : 0 ≤ lambda1 * lambda2 ^ (k + 1) *
        (((k + 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by positivity
    calc
      h (p ^ (k + 2)) * Real.log ((p ^ (k + 2) : ℕ) : ℝ)
          ≤ (lambda1 * lambda2 ^ (k + 1)) *
              Real.log ((p ^ (k + 2) : ℕ) : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [Nat.add_assoc] using hpow p (k + 1) hp)
              (Real.log_nonneg (by
                exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
                  (pow_ne_zero _ hp.ne_zero))))
      _ = lambda1 * lambda2 ^ (k + 1) *
            (((k + 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by
          rw [Nat.cast_pow, Real.log_pow]
      _ ≤ (lambda1 * lambda2 ^ (k + 1) *
            (((k + 2 : ℕ) : ℝ) * Real.log (p : ℝ))) *
            ((Q : ℝ) / ((p : ℝ) ^ 2 * (2 : ℝ) ^ k)) := by
          nlinarith
      _ = lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) *
            (lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) := by
          rw [div_pow, pow_succ]
          have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
          have htwone : (2 : ℝ) ≠ 0 := by norm_num
          field_simp [hpne, htwone]
  · exact hright

lemma prime_inner_mass_le
    (h : ℕ → ℝ) (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1) (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p j : ℕ), p.Prime →
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    {Q p : ℕ} (hp : p.Prime) (hpQ : p ≤ Q) :
    (∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
        h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)) ≤
      lambda1 * Real.log (p : ℝ) +
        (lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) *
          (2 * lambda2 / (1 - lambda2 / 2) ^ 2) := by
  let L := Nat.log p Q
  let A : ℝ := lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2)
  have hLpos : 0 < L := Nat.log_pos hp.one_lt hpQ
  have hpowlog : p ^ L ≤ Q := by
    exact Nat.pow_log_le_self p (Nat.ne_of_gt (hp.pos.trans_le hpQ))
  have hlogp : 0 ≤ Real.log (p : ℝ) := hp.log_pos.le
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  rw [sum_Icc_one_eq_sum_range_succ]
  have hL : L = (L - 1) + 1 := by omega
  rw [show Nat.log p Q = L by rfl, hL, Finset.sum_range_succ']
  have htail :
      (∑ k ∈ Finset.range (L - 1),
          h (p ^ (k + 1 + 1)) *
            Real.log ((p ^ (k + 1 + 1) : ℕ) : ℝ)) ≤
        A * (2 * lambda2 / (1 - lambda2 / 2) ^ 2) := by
    calc
      (∑ k ∈ Finset.range (L - 1),
          h (p ^ (k + 1 + 1)) *
            Real.log ((p ^ (k + 1 + 1) : ℕ) : ℝ))
          ≤ ∑ k ∈ Finset.range (L - 1),
              A * (lambda2 *
                (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hkL : k + 2 ≤ L := by
              have := Finset.mem_range.mp hk
              omega
            have hpkQ : p ^ (k + 2) ≤ Q :=
              (Nat.pow_le_pow_right hp.pos hkL).trans hpowlog
            simpa [A, Nat.add_assoc, hpkQ] using
              tail_prime_power_term_le h lambda1 lambda2
                hlambda1 hlambda2 hpow (Q := Q) (p := p) (k := k) hp
      _ = A * ∑ k ∈ Finset.range (L - 1),
            lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k) := by
          rw [Finset.mul_sum]
      _ ≤ A * (2 * lambda2 / (1 - lambda2 / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (weighted_geometric_tail_le lambda2 hlambda2 hlambda2_lt (L - 1)) hA
  have hfirst :
      h (p ^ (0 + 1)) * Real.log ((p ^ (0 + 1) : ℕ) : ℝ) ≤
        lambda1 * Real.log (p : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right (hpow p 0 hp) hlogp
  simpa [add_comm] using add_le_add htail hfirst

/-- The explicit linear prime-power mass estimate in exactly the indexing and
finite encoding used by `PrimePowerConvolution448.primePowerMass`. -/
theorem primePowerMass_le_linear
    (h : ℕ → ℝ) (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1) (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p j : ℕ), p.Prime →
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j) :
    ∀ Q : ℕ,
      primePowerMass h Q ≤ massConstant lambda1 lambda2 * (Q : ℝ) := by
  intro Q
  let C : ℝ := 2 * lambda2 / (1 - lambda2 / 2) ^ 2
  have hden : 0 < 1 - lambda2 / 2 := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hinner : ∀ p ∈ Nat.primesLE Q,
      (∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
          h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)) ≤
        lambda1 * Real.log (p : ℝ) +
          (lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) * C := by
    intro p hpMem
    have hpData := Nat.mem_primesLE.mp hpMem
    exact prime_inner_mass_le h lambda1 lambda2 hlambda1 hlambda2
      hlambda2_lt hpow hpData.2 hpData.1
  have htheta :
      lambda1 * (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤
        lambda1 * (Real.log 4 * (Q : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hlambda1
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have htailCoeff : 0 ≤ lambda1 * (Q : ℝ) * C := by positivity
  have hprimeSq :
      (lambda1 * (Q : ℝ) * C) *
          (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
        (lambda1 * (Q : ℝ) * C) * (4 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (sum_primesLE_log_div_sq_le Q) htailCoeff
  calc
    primePowerMass h Q =
        ∑ p ∈ Nat.primesLE Q,
          ∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
            h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ) := by
      rw [primePowerMass, primesBelow_succ_eq_primesLE]
    _ ≤ ∑ p ∈ Nat.primesLE Q,
          (lambda1 * Real.log (p : ℝ) +
            (lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) * C) :=
      Finset.sum_le_sum hinner
    _ = lambda1 * (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) +
          (lambda1 * (Q : ℝ) * C) *
            (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ lambda1 * (Real.log 4 * (Q : ℝ)) +
          (lambda1 * (Q : ℝ) * C) * (4 * Real.log 2) :=
      add_le_add htheta hprimeSq
    _ = massConstant lambda1 lambda2 * (Q : ℝ) := by
      dsimp [C, massConstant]
      ring

#print axioms primePowerMass_le_linear

end PrimePowerMassLinear448
