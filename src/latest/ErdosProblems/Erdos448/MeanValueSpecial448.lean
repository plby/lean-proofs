import ErdosProblems.Erdos202
import Util.MertensThird

open scoped BigOperators
open Filter Finset

namespace Erdos448Scratch

lemma shifted_geometric_summable_and_tsum_le
    {r delta : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdelta : 0 < delta) (hdelta_le : delta ≤ 1 - r) :
    Summable (fun k : ℕ => ((k + 2 : ℕ) : ℝ) * r ^ k) ∧
      (∑' k : ℕ, ((k + 2 : ℕ) : ℝ) * r ^ k) ≤ 2 / delta ^ 2 := by
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hk : Summable (fun k : ℕ => (k : ℝ) * r ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hgeom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr0 hr1
  have htwo : Summable (fun k : ℕ => 2 * r ^ k) := hgeom.mul_left 2
  have hsplit : (fun k : ℕ => ((k + 2 : ℕ) : ℝ) * r ^ k) =
      fun k : ℕ => (k : ℝ) * r ^ k + 2 * r ^ k := by
    funext k
    push_cast
    ring
  have hsum : Summable (fun k : ℕ => ((k + 2 : ℕ) : ℝ) * r ^ k) := by
    rw [hsplit]
    exact hk.add htwo
  refine ⟨hsum, ?_⟩
  have hsumEq :
      (∑' k : ℕ, ((k + 2 : ℕ) : ℝ) * r ^ k) =
        r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹ := by
    rw [hsplit, hk.tsum_add htwo,
      tsum_coe_mul_geometric_of_norm_lt_one hrnorm]
    congr 1
    exact ((hasSum_geometric_of_lt_one hr0 hr1).mul_left 2).tsum_eq
  rw [hsumEq]
  have honeMinus : 0 < 1 - r := sub_pos.mpr hr1
  have hdeltaSq : delta ^ 2 ≤ (1 - r) ^ 2 := by nlinarith
  rw [le_div_iff₀ (sq_pos_of_pos hdelta)]
  have hform :
      (r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹) * delta ^ 2 =
        (2 - r) * delta ^ 2 / (1 - r) ^ 2 := by
    field_simp [ne_of_gt honeMinus]
    ring
  rw [hform]
  rw [div_le_iff₀ (sq_pos_of_pos honeMinus)]
  have htwoMinus : 0 ≤ 2 - r := by linarith
  nlinarith

/-- Finite mass of prime powers `p^(j+1) ≤ Q`. -/
noncomputable def primePowerMass (h : ℕ → ℝ) (Q : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE Q, ∑ j ∈ Finset.range (Nat.log p Q),
    h (p ^ (j + 1)) * Real.log ((p ^ (j + 1) : ℕ) : ℝ)

/-- The exact nested-index mass used by the integrated convolution theorem. -/
noncomputable def primePowerMassIcc (h : ℕ → ℝ) (Q : ℕ) : ℝ :=
  ∑ p ∈ (Q + 1).primesBelow, ∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
    h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)

lemma sum_range_shift_eq_sum_Icc (f : ℕ → ℝ) (L : ℕ) :
    (∑ j ∈ Finset.range L, f (j + 1)) = ∑ nu ∈ Finset.Icc 1 L, f nu := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

theorem primePowerMass_eq_primePowerMassIcc (h : ℕ → ℝ) (Q : ℕ) :
    primePowerMass h Q = primePowerMassIcc h Q := by
  classical
  have hprimes : Nat.primesLE Q = (Q + 1).primesBelow := by
    ext p
    rw [Nat.mem_primesLE, Nat.mem_primesBelow]
    constructor
    · rintro ⟨hpQ, hp⟩
      exact ⟨Nat.lt_succ_of_le hpQ, hp⟩
    · rintro ⟨hpQ, hp⟩
      exact ⟨Nat.le_of_lt_succ hpQ, hp⟩
  unfold primePowerMass primePowerMassIcc
  rw [hprimes]
  apply Finset.sum_congr rfl
  intro p hp
  exact sum_range_shift_eq_sum_Icc
    (fun nu => h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)) (Nat.log p Q)

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
    have hlowSq : (((2 ^ k : ℕ) : ℝ)) ^ 2 ≤ (p : ℝ) ^ 2 := by
      gcongr
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

/-- A uniform explicit reciprocal-square prime sum.  The constant `4` is a
slightly relaxed version of the sharp `3` obtained by starting the dyadic
decomposition at `k = 1`; keeping the empty `k = 0` block makes the Lean
fiber decomposition substantially cleaner. -/
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

/-- Explicit local prime-power mass bound used in the
Levin--Fainleib/Halberstam--Richert summation argument.  With
`delta = 1 - lambda2 / 2`, the coefficient `8` comes from the relaxed
`4 * log 2` reciprocal-square prime bound above. -/
theorem primePowerMass_le
    (h : ℕ → ℝ) (lambda1 lambda2 : ℝ)
    (_hh_nonneg : ∀ n, 0 ≤ h n)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p : ℕ), Nat.Prime p → ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    (Q : ℕ) :
    primePowerMass h Q ≤
      lambda1 * (Real.log 4 +
        8 * lambda2 * Real.log 2 / (1 - lambda2 / 2) ^ 2) * (Q : ℝ) := by
  classical
  let delta : ℝ := 1 - lambda2 / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hinner : ∀ p ∈ Nat.primesLE Q,
      (∑ j ∈ Finset.range (Nat.log p Q),
          h (p ^ (j + 1)) * Real.log ((p ^ (j + 1) : ℕ) : ℝ)) ≤
        lambda1 * Real.log (p : ℝ) +
          (Q : ℝ) * (2 * lambda1 * lambda2 / delta ^ 2) *
            (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
    intro p hpMem
    have hpData := Nat.mem_primesLE.mp hpMem
    have hpLe : p ≤ Q := hpData.1
    have hp : Nat.Prime p := hpData.2
    have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hQNe : Q ≠ 0 := by
      exact Nat.ne_of_gt (hp.pos.trans_le hpLe)
    have hlogPos : 0 < Nat.log p Q := Nat.log_pos hp.one_lt hpLe
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlogPos)
    have hlogp : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_le)
    let r : ℝ := lambda2 / (p : ℝ)
    have hr0 : 0 ≤ r := div_nonneg hlambda2 hpReal.le
    have hr1 : r < 1 := by
      dsimp [r]
      exact (div_lt_one hpReal).2 (hlambda2_lt.trans_le hpTwo)
    have hr_le : r ≤ lambda2 / 2 := by
      dsimp [r]
      exact div_le_div_of_nonneg_left hlambda2 (by norm_num) hpTwo
    have hdelta_le : delta ≤ 1 - r := by
      dsimp [delta]
      linarith
    have hshift := shifted_geometric_summable_and_tsum_le
      hr0 hr1 hdelta hdelta_le
    have htailTerm : ∀ k ∈ Finset.range m,
        h (p ^ ((k + 1) + 1)) *
            Real.log ((p ^ ((k + 1) + 1) : ℕ) : ℝ) ≤
          (Q : ℝ) *
            (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
              (((k + 2 : ℕ) : ℝ) * r ^ k) := by
      intro k hk
      have hkLt : k < m := Finset.mem_range.mp hk
      have hkLog : k + 2 ≤ Nat.log p Q := by omega
      have hpPow : p ^ (k + 2) ≤ Q := Nat.pow_le_of_le_log hQNe hkLog
      have hpPowReal : ((p ^ (k + 2) : ℕ) : ℝ) ≤ (Q : ℝ) := by
        exact_mod_cast hpPow
      have hfactorNonneg :
          0 ≤ (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
            (((k + 2 : ℕ) : ℝ) * r ^ k) := by
        positivity
      calc
        h (p ^ ((k + 1) + 1)) *
            Real.log ((p ^ ((k + 1) + 1) : ℕ) : ℝ)
            = h (p ^ (k + 2)) *
                (((k + 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by
              congr 2
              rw [show (((p ^ (k + 2) : ℕ) : ℝ)) = (p : ℝ) ^ (k + 2) by
                norm_num, Real.log_pow]
        _ ≤ (lambda1 * lambda2 ^ (k + 1)) *
              (((k + 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [Nat.add_assoc] using hpow p hp (k + 1))
              (mul_nonneg (by positivity) hlogp)
        _ = ((p ^ (k + 2) : ℕ) : ℝ) *
              ((lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
                (((k + 2 : ℕ) : ℝ) * r ^ k)) := by
            rw [show (((p ^ (k + 2) : ℕ) : ℝ)) = (p : ℝ) ^ (k + 2) by
              norm_num]
            dsimp [r]
            have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpReal
            rw [div_pow]
            field_simp [hpNe]
            ring
        _ ≤ (Q : ℝ) *
              ((lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
                (((k + 2 : ℕ) : ℝ) * r ^ k)) :=
            mul_le_mul_of_nonneg_right hpPowReal hfactorNonneg
        _ = (Q : ℝ) *
              (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
                (((k + 2 : ℕ) : ℝ) * r ^ k) := by ring
    rw [hm, Finset.sum_range_succ']
    have hfirst :
        h (p ^ (0 + 1)) * Real.log ((p ^ (0 + 1) : ℕ) : ℝ) ≤
          lambda1 * Real.log (p : ℝ) := by
      simpa using mul_le_mul_of_nonneg_right (hpow p hp 0) hlogp
    have htailSum :
        (∑ k ∈ Finset.range m,
            h (p ^ ((k + 1) + 1)) *
              Real.log ((p ^ ((k + 1) + 1) : ℕ) : ℝ)) ≤
          (Q : ℝ) *
            (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
              (2 / delta ^ 2) := by
      calc
        (∑ k ∈ Finset.range m,
            h (p ^ ((k + 1) + 1)) *
              Real.log ((p ^ ((k + 1) + 1) : ℕ) : ℝ))
            ≤ ∑ k ∈ Finset.range m,
                (Q : ℝ) *
                  (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
                    (((k + 2 : ℕ) : ℝ) * r ^ k) :=
              Finset.sum_le_sum htailTerm
        _ = ((Q : ℝ) *
              (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2)) *
                ∑ k ∈ Finset.range m, (((k + 2 : ℕ) : ℝ) * r ^ k) := by
              rw [Finset.mul_sum]
        _ ≤ ((Q : ℝ) *
              (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2)) *
                (∑' k : ℕ, (((k + 2 : ℕ) : ℝ) * r ^ k)) := by
              gcongr
              exact Summable.sum_le_tsum (Finset.range m)
                (fun k hk => by positivity) hshift.1
        _ ≤ ((Q : ℝ) *
              (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2)) *
                (2 / delta ^ 2) := by
              exact mul_le_mul_of_nonneg_left hshift.2 (by positivity)
        _ = (Q : ℝ) *
              (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
                (2 / delta ^ 2) := by ring
    calc
      (∑ k ∈ Finset.range m,
          h (p ^ ((k + 1) + 1)) *
            Real.log ((p ^ ((k + 1) + 1) : ℕ) : ℝ)) +
          h (p ^ (0 + 1)) * Real.log ((p ^ (0 + 1) : ℕ) : ℝ)
          ≤ (Q : ℝ) *
              (lambda1 * lambda2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) *
                (2 / delta ^ 2) + lambda1 * Real.log (p : ℝ) :=
            add_le_add htailSum hfirst
      _ = lambda1 * Real.log (p : ℝ) +
            (Q : ℝ) * (2 * lambda1 * lambda2 / delta ^ 2) *
              (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
          have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpReal
          have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
          field_simp [hpNe, hdeltaNe]
          ring
  have htheta :
      (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤
        Real.log 4 * (Q : ℝ) := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hsquare := sum_primesLE_log_div_sq_le Q
  calc
    primePowerMass h Q
        ≤ ∑ p ∈ Nat.primesLE Q,
            (lambda1 * Real.log (p : ℝ) +
              (Q : ℝ) * (2 * lambda1 * lambda2 / delta ^ 2) *
                (Real.log (p : ℝ) / (p : ℝ) ^ 2)) := by
          unfold primePowerMass
          exact Finset.sum_le_sum hinner
    _ = lambda1 * (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) +
          ((Q : ℝ) * (2 * lambda1 * lambda2 / delta ^ 2)) *
            (∑ p ∈ Nat.primesLE Q,
              Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ lambda1 * (Real.log 4 * (Q : ℝ)) +
          ((Q : ℝ) * (2 * lambda1 * lambda2 / delta ^ 2)) *
            (4 * Real.log 2) := by
          gcongr
    _ = lambda1 * (Real.log 4 +
          8 * lambda2 * Real.log 2 / (1 - lambda2 / 2) ^ 2) * (Q : ℝ) := by
          dsimp [delta]
          ring

theorem primePowerMassIcc_le
    (h : ℕ → ℝ) (lambda1 lambda2 : ℝ)
    (hh_nonneg : ∀ n, 0 ≤ h n)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p : ℕ), Nat.Prime p → ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    (Q : ℕ) :
    primePowerMassIcc h Q ≤
      lambda1 * (Real.log 4 +
        8 * lambda2 * Real.log 2 / (1 - lambda2 / 2) ^ 2) * (Q : ℝ) := by
  rw [← primePowerMass_eq_primePowerMassIcc]
  exact primePowerMass_le h lambda1 lambda2 hh_nonneg hlambda1 hlambda2
    hlambda2_lt hpow Q

/-- The coefficient-one reciprocal-prime upper bound needed by the
Halberstam--Richert estimate.  This is extracted from the already formalized
weak form of Mertens' third theorem. -/
theorem reciprocal_prime_sum_le_log_three_log (N : ℕ) (hN : 3 ≤ N) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
      Real.log (3 * Real.log (N : ℝ)) := by
  classical
  let P : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hterm : ∀ p ∈ P,
      (1 : ℝ) / (p : ℝ) ≤ -Real.log (1 - 1 / (p : ℝ)) := by
    intro p hp
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hpCast : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
    have hpos : 0 < (1 : ℝ) - 1 / (p : ℝ) := by
      exact sub_pos.mpr (by simpa [one_div] using inv_lt_one_of_one_lt₀ hpCast)
    have hlog := Real.log_le_sub_one_of_pos hpos
    linarith
  have hsum_log :
      (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ≤
        -Real.log (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
    calc
      (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
          ≤ ∑ p ∈ P, -Real.log (1 - 1 / (p : ℝ)) :=
            Finset.sum_le_sum hterm
      _ = -(∑ p ∈ P, Real.log (1 - 1 / (p : ℝ))) := by
            exact Finset.sum_neg_distrib _
      _ = -Real.log (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
            rw [Real.log_prod]
            intro p hp
            have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hpCast : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
            exact ne_of_gt (sub_pos.mpr
              (by simpa [one_div] using inv_lt_one_of_one_lt₀ hpCast))
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hN))
  have hM :
      1 / (3 * Real.log (N : ℝ)) ≤
        ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    have hP : P = (Finset.range (N + 1)).filter Nat.Prime := by
      ext p
      simp only [P, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      constructor
      · rintro ⟨⟨_hp1, hpN⟩, hpPrime⟩
        exact ⟨Nat.lt_succ_of_le hpN, hpPrime⟩
      · rintro ⟨hpN, hpPrime⟩
        exact ⟨⟨hpPrime.one_le, Nat.le_of_lt_succ hpN⟩, hpPrime⟩
    rw [hP]
    exact mertens_third_theorem N hN
  have hqpos : 0 < (1 : ℝ) / (3 * Real.log (N : ℝ)) := by positivity
  have hlogM := Real.log_le_log hqpos hM
  have hupper :
      -Real.log (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤
        Real.log (3 * Real.log (N : ℝ)) := by
    calc
      -Real.log (∏ p ∈ P, (1 - 1 / (p : ℝ)))
          ≤ -Real.log (1 / (3 * Real.log (N : ℝ))) := by linarith
      _ = Real.log (3 * Real.log (N : ℝ)) := by
        rw [one_div, Real.log_inv]
        ring
  exact hsum_log.trans hupper

/-- What the nonnegative Euler-product argument in `Erdos202` gives at the
fixed Rankin parameter `1/2`.  Notice the absence of the extra `1 / log N`
factor in the right-hand side: this is precisely why this lemma alone cannot
replace the Halberstam--Richert mean-value theorem. -/
theorem half_omega_euler_bound (N : ℕ) (hN : 3 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ((1 : ℝ) / 2) ^ Erdos202.omega n) ≤
      (N : ℝ) * Real.exp (((1 : ℝ) / 2) *
        Real.log (3 * Real.log (N : ℝ))) := by
  classical
  let P : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hpos : ∀ p ∈ P, 0 < (p : ℝ) := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hEuler := Erdos202.omega_weighted_sum_le_euler_product
    N ((1 : ℝ) / 2) (by norm_num)
  have hProd := Erdos202.finite_euler_product_one_add_le_exp_sum
    P (z := (1 : ℝ) / 2) (by norm_num) hpos
  have hPrime := reciprocal_prime_sum_le_log_three_log N hN
  calc
    (∑ n ∈ Finset.Icc 1 N, ((1 : ℝ) / 2) ^ Erdos202.omega n)
        ≤ (N : ℝ) * P.prod
            (fun p : ℕ => (1 : ℝ) + ((1 : ℝ) / 2) / (p : ℝ)) := by
          simpa [P] using hEuler
    _ ≤ (N : ℝ) * Real.exp (((1 : ℝ) / 2) *
          P.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hProd (by positivity)
    _ ≤ (N : ℝ) * Real.exp (((1 : ℝ) / 2) *
          Real.log (3 * Real.log (N : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Real.exp_le_exp]
        exact mul_le_mul_of_nonneg_left (by simpa [P] using hPrime) (by norm_num)

/-- A finite convolution/mean-value lemma.  To prove a linear first moment it
is enough to dominate the summand by a nonnegative divisor convolution whose
reciprocal sum is uniformly bounded.  This is the weakest reusable interface
reached in this experiment for the selected close-pair function. -/
theorem divisor_majorant_first_moment
    (f g : ℕ → ℝ) (N : ℕ)
    (hf : ∀ n ∈ Finset.Icc 1 N,
      f n ≤ ∑ d ∈ n.divisors, g d)
    (hg : ∀ d, 0 ≤ g d) :
    (∑ n ∈ Finset.Icc 1 N, f n) ≤
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, g d / (d : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, f n)
        ≤ ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, g d :=
          Finset.sum_le_sum hf
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n), g d := by
      refine Finset.sum_le_sum ?_
      intro n hn
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro d hd
        have hdDvd : d ∣ n := Nat.dvd_of_mem_divisors hd
        have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
        have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr
            ⟨Nat.succ_le_of_lt hdPos,
              (Nat.le_of_dvd hnPos hdDvd).trans (Finset.mem_Icc.mp hn).2⟩,
            hdDvd⟩
      · intro d hd _hnot
        exact hg d
    _ = ∑ d ∈ Finset.Icc 1 N,
          (((Finset.Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) * g d := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ((N : ℝ) / (d : ℝ)) * g d := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have hdIcc := Finset.mem_Icc.mp hd
      have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
      have hcardNat := Erdos202.card_Icc_filter_dvd_le_div N d hdPos
      have hcardReal :
          (((Finset.Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) ≤
            (N : ℝ) / (d : ℝ) := by
        exact (Nat.cast_le.mpr hcardNat).trans Nat.cast_div_le
      exact mul_le_mul_of_nonneg_right hcardReal (hg d)
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, g d / (d : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdNe : (d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt
          (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1))
      field_simp [hdNe]

/-- Two-divisor version of the preceding finite mean-value argument.  It is
the exact elementary reindexing behind close-pair first moments: a fixed pair
`(d,e)` occurs precisely in the multiples of `lcm d e`. -/
theorem pair_divisor_first_moment
    (W : ℕ → ℕ → ℝ) (N : ℕ)
    (hW : ∀ d e, 0 ≤ W d e) :
    (∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, W d e) ≤
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
        ∑ e ∈ Finset.Icc 1 N, W d e / ((Nat.lcm d e : ℕ) : ℝ) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 N
  have hDivSubset : ∀ n ∈ S,
      n.divisors ⊆ S.filter (fun d => d ∣ n) := by
    intro n hn d hd
    have hdDvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.succ_le_of_lt hdPos,
          (Nat.le_of_dvd hnPos hdDvd).trans (Finset.mem_Icc.mp hn).2⟩,
        hdDvd⟩
  calc
    (∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, W d e)
        ≤ ∑ n ∈ S, ∑ d ∈ S.filter (fun d => d ∣ n),
            ∑ e ∈ S.filter (fun e => e ∣ n), W d e := by
      refine Finset.sum_le_sum ?_
      intro n hn
      calc
        (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, W d e)
            ≤ ∑ d ∈ n.divisors,
                ∑ e ∈ S.filter (fun e => e ∣ n), W d e := by
              refine Finset.sum_le_sum ?_
              intro d hd
              exact Finset.sum_le_sum_of_subset_of_nonneg (hDivSubset n hn)
                (fun e he _ => hW d e)
        _ ≤ ∑ d ∈ S.filter (fun d => d ∣ n),
              ∑ e ∈ S.filter (fun e => e ∣ n), W d e := by
              exact Finset.sum_le_sum_of_subset_of_nonneg (hDivSubset n hn)
                (fun d hd _ => Finset.sum_nonneg (fun e he => hW d e))
    _ = ∑ d ∈ S, ∑ e ∈ S,
          ((((S.filter (fun n => Nat.lcm d e ∣ n)).card : ℕ) : ℝ) * W d e) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      have hdistrib : ∀ n : ℕ,
          (if d ∣ n then ∑ e ∈ S, (if e ∣ n then W d e else 0) else 0) =
            ∑ e ∈ S, (if d ∣ n then (if e ∣ n then W d e else 0) else 0) := by
        intro n
        by_cases hdN : d ∣ n <;> simp [hdN]
      simp_rw [hdistrib]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      have hite : ∀ n : ℕ,
          (if d ∣ n then (if e ∣ n then W d e else 0) else 0) =
            if Nat.lcm d e ∣ n then W d e else 0 := by
        intro n
        simp only [Nat.lcm_dvd_iff]
        by_cases hdN : d ∣ n <;> by_cases heN : e ∣ n <;> simp [hdN, heN]
      simp_rw [hite]
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ S, ∑ e ∈ S,
          ((N : ℝ) / ((Nat.lcm d e : ℕ) : ℝ)) * W d e := by
      refine Finset.sum_le_sum ?_
      intro d hd
      refine Finset.sum_le_sum ?_
      intro e he
      have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
      have hePos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp he).1
      have hlcmPos : 0 < Nat.lcm d e := Nat.lcm_pos hdPos hePos
      have hcardNat := Erdos202.card_Icc_filter_dvd_le_div N (Nat.lcm d e) hlcmPos
      have hcardReal :
          (((S.filter (fun n => Nat.lcm d e ∣ n)).card : ℕ) : ℝ) ≤
            (N : ℝ) / ((Nat.lcm d e : ℕ) : ℝ) := by
        simpa [S] using
          ((Nat.cast_le.mpr hcardNat).trans Nat.cast_div_le)
      exact mul_le_mul_of_nonneg_right hcardReal (hW d e)
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
          ∑ e ∈ Finset.Icc 1 N, W d e / ((Nat.lcm d e : ℕ) : ℝ) := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
      have hePos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp he).1
      have hlcmNe : ((Nat.lcm d e : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.lcm_pos hdPos hePos))
      field_simp [hlcmNe]

/-- The normalized divisor-pair moment used by the ET Cauchy--Schwarz
reduction. -/
noncomputable def normalizedPairMoment (W : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, W d e) /
    (n.divisors.card : ℝ)

/-- Exact elementary first-moment reduction for normalized close-pair sums.
After grouping a pair by `q = lcm d e`, divisor-count monotonicity supplies
`tau(q) ≤ tau(n)`.  Thus the only genuinely analytic obligation is a uniform
bound for the displayed double reciprocal-lcm sum. -/
theorem normalized_pair_first_moment
    (W : ℕ → ℕ → ℝ) (N : ℕ)
    (hW : ∀ d e, 0 ≤ W d e) :
    (∑ n ∈ Finset.Icc 1 N, normalizedPairMoment W n) ≤
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (W d e / ((Nat.lcm d e).divisors.card : ℝ)) /
          ((Nat.lcm d e : ℕ) : ℝ) := by
  classical
  let V : ℕ → ℕ → ℝ := fun d e =>
    W d e / ((Nat.lcm d e).divisors.card : ℝ)
  have hV : ∀ d e, 0 ≤ V d e := by
    intro d e
    exact div_nonneg (hW d e) (by positivity)
  have hpoint : ∀ n ∈ Finset.Icc 1 N,
      normalizedPairMoment W n ≤
        ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, V d e := by
    intro n hn
    have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    unfold normalizedPairMoment
    rw [Finset.sum_div]
    refine Finset.sum_le_sum ?_
    intro d hd
    rw [Finset.sum_div]
    refine Finset.sum_le_sum ?_
    intro e he
    have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
    have hePos : 0 < e := Nat.pos_of_mem_divisors he
    have hdDvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have heDvd : e ∣ n := Nat.dvd_of_mem_divisors he
    have hqDvd : Nat.lcm d e ∣ n := Nat.lcm_dvd hdDvd heDvd
    have hqPos : 0 < Nat.lcm d e := Nat.lcm_pos hdPos hePos
    have hsubset : (Nat.lcm d e).divisors ⊆ n.divisors := by
      intro a ha
      have haDvd : a ∣ Nat.lcm d e := Nat.dvd_of_mem_divisors ha
      exact Nat.mem_divisors.mpr ⟨haDvd.trans hqDvd, Nat.ne_of_gt hnPos⟩
    have hcardNat : (Nat.lcm d e).divisors.card ≤ n.divisors.card :=
      Finset.card_le_card hsubset
    have hcardReal :
        (((Nat.lcm d e).divisors.card : ℕ) : ℝ) ≤
          ((n.divisors.card : ℕ) : ℝ) := by exact_mod_cast hcardNat
    have hqCardPos : 0 < (((Nat.lcm d e).divisors.card : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr
        ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, Nat.ne_of_gt hqPos⟩⟩)
    exact div_le_div_of_nonneg_left (hW d e) hqCardPos hcardReal
  calc
    (∑ n ∈ Finset.Icc 1 N, normalizedPairMoment W n)
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, V d e :=
          Finset.sum_le_sum hpoint
    _ ≤ (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
          ∑ e ∈ Finset.Icc 1 N, V d e / ((Nat.lcm d e : ℕ) : ℝ) :=
      pair_divisor_first_moment V N hV
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          (W d e / ((Nat.lcm d e).divisors.card : ℝ)) /
            ((Nat.lcm d e : ℕ) : ℝ) := by rfl

/-- Consumer-shaped `O(N)` form of `normalized_pair_first_moment`. -/
theorem normalized_pair_linear_of_reciprocal_lcm
    (W : ℕ → ℕ → ℝ) (C : ℝ)
    (hW : ∀ d e, 0 ≤ W d e)
    (hrecip : ∀ N : ℕ,
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (W d e / ((Nat.lcm d e).divisors.card : ℝ)) /
          ((Nat.lcm d e : ℕ) : ℝ)) ≤ C) :
    ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N, normalizedPairMoment W n) ≤ C * (N : ℝ) := by
  intro N
  calc
    (∑ n ∈ Finset.Icc 1 N, normalizedPairMoment W n)
        ≤ (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
            (W d e / ((Nat.lcm d e).divisors.card : ℝ)) /
              ((Nat.lcm d e : ℕ) : ℝ) :=
          normalized_pair_first_moment W N hW
    _ ≤ (N : ℝ) * C :=
      mul_le_mul_of_nonneg_left (hrecip N) (by positivity)
    _ = C * (N : ℝ) := by ring

/-- Exact local Euler-factor estimate for the prime-power hypothesis in the
Halberstam--Richert lemma.  The indexing is chosen so that the first nontrivial
term has bound `lambda1`, and each further prime power costs one factor of
`lambda2`. -/
theorem prime_power_local_mass
    (h : ℕ → ℝ) (p : ℕ) (lambda1 lambda2 : ℝ)
    (hp : Nat.Prime p)
    (hh_nonneg : ∀ n, 0 ≤ h n)
    (hh_one : h 1 = 1)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j) :
    Summable (fun j : ℕ => ‖h (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) ∧
      (∑' j : ℕ, ‖h (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) ≤
        1 + lambda1 / ((p : ℝ) - lambda2) := by
  let r : ℝ := lambda2 / (p : ℝ)
  let c : ℝ := lambda1 / (p : ℝ)
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr_nonneg : 0 ≤ r := by
    exact div_nonneg hlambda2 hpReal.le
  have hr_lt : r < 1 := by
    dsimp [r]
    exact (div_lt_one hpReal).2 (hlambda2_lt.trans_le hpTwo)
  have hc_nonneg : 0 ≤ c := div_nonneg hlambda1 hpReal.le
  have hbound : ∀ j : ℕ,
      ‖h (p ^ (j + 1)) / ((p ^ (j + 1) : ℕ) : ℝ)‖ ≤ c * r ^ j := by
    intro j
    have hdenom_nonneg : 0 ≤ (((p ^ (j + 1) : ℕ) : ℝ)) := by positivity
    calc
      ‖h (p ^ (j + 1)) / ((p ^ (j + 1) : ℕ) : ℝ)‖
          = h (p ^ (j + 1)) / ((p ^ (j + 1) : ℕ) : ℝ) := by
              rw [Real.norm_eq_abs, abs_of_nonneg]
              exact div_nonneg (hh_nonneg _) hdenom_nonneg
      _ ≤ (lambda1 * lambda2 ^ j) /
            ((p ^ (j + 1) : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (hpow j) hdenom_nonneg
      _ = c * r ^ j := by
          rw [Nat.cast_pow, pow_succ]
          dsimp [c, r]
          have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpReal
          rw [div_pow]
          field_simp [hpNe]
  have hgeom : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  have hmajor : Summable (fun j : ℕ => c * r ^ j) :=
    hgeom.mul_left c
  have htail : Summable
      (fun j : ℕ => ‖h (p ^ (j + 1)) / ((p ^ (j + 1) : ℕ) : ℝ)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound hmajor
  have hseries : Summable
      (fun j : ℕ => ‖h (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.add_comm] using htail
  refine ⟨hseries, ?_⟩
  rw [hseries.tsum_eq_zero_add]
  have hzero : ‖h (p ^ 0) / ((p ^ 0 : ℕ) : ℝ)‖ = 1 := by
    simp [hh_one]
  rw [hzero]
  have htail_le :
      (∑' j : ℕ, ‖h (p ^ (j + 1)) / ((p ^ (j + 1) : ℕ) : ℝ)‖) ≤
        ∑' j : ℕ, c * r ^ j :=
    htail.tsum_le_tsum hbound hmajor
  have hmajor_sum : (∑' j : ℕ, c * r ^ j) = c * (1 - r)⁻¹ :=
    ((hasSum_geometric_of_lt_one hr_nonneg hr_lt).mul_left c).tsum_eq
  calc
    1 + ∑' j : ℕ, ‖h (p ^ (j + 1)) / ((p ^ (j + 1) : ℕ) : ℝ)‖
        ≤ 1 + ∑' j : ℕ, c * r ^ j := by linarith
    _ = 1 + c * (1 - r)⁻¹ := by rw [hmajor_sum]
    _ = 1 + lambda1 / ((p : ℝ) - lambda2) := by
      dsimp [c, r]
      have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpReal
      have hdiffPos : 0 < (p : ℝ) - lambda2 := sub_pos.mpr
        (hlambda2_lt.trans_le hpTwo)
      field_simp [hpNe, ne_of_gt hdiffPos]

/-- Consumer-shaped linear estimate.  The remaining ET-specific task is to
construct `g` from the selected close-pair scale decomposition and prove the
uniform reciprocal-sum hypothesis. -/
theorem selected_pair_linear_of_divisor_majorant
    (f g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ d, 0 ≤ g d)
    (hrecip : ∀ N : ℕ,
      (∑ d ∈ Finset.Icc 1 N, g d / (d : ℝ)) ≤ C)
    (hmajor : ∀ N : ℕ, ∀ n ∈ Finset.Icc 1 N,
      f n ≤ ∑ d ∈ n.divisors, g d) :
    ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, f n) ≤ C * (N : ℝ) := by
  intro N
  calc
    (∑ n ∈ Finset.Icc 1 N, f n)
        ≤ (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, g d / (d : ℝ) :=
          divisor_majorant_first_moment f g N (hmajor N) hg
    _ ≤ (N : ℝ) * C :=
      mul_le_mul_of_nonneg_left (hrecip N) (by positivity)
    _ = C * (N : ℝ) := by ring

end Erdos448Scratch
