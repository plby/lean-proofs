/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.PrimeBins
import ErdosProblems.Erdos896.Ford.TkTail
import ErdosProblems.Erdos896.Ford.UkBound
import ErdosProblems.Erdos896.Ford.StirlingScale
import ErdosProblems.Erdos896.Ford.Denominator
import ErdosProblems.Erdos896.Ford.Reduction

/-!
# Summing Ford's `T_k` estimates

This file contains the summation step in the upper bound for integers with a
divisor in `(y, 2y]`.  It is kept separate from the prime-bin estimate for an
individual `T_k` and from the order-statistics estimate for `U_k`: the point
of the present file is the transition from those estimates to Ford's
logarithmic scale.
-/

namespace Erdos896.Ford

open Filter Asymptotics
open scoped BigOperators

/-! ## The factorial envelope -/

/-- The factorial term which occurs at the critical index. -/
private noncomputable def factorialTerm (a : ℝ) (k : ℕ) : ℝ :=
  a ^ k / ((k + 1).factorial : ℝ)

private lemma factorialTerm_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    0 ≤ factorialTerm a k := by
  exact div_nonneg (pow_nonneg ha k) (by positivity)

private lemma factorialTerm_step {a : ℝ} (ha : 0 < a) (k : ℕ) :
    factorialTerm a k = ((k + 2 : ℕ) : ℝ) / a * factorialTerm a (k + 1) := by
  simp only [factorialTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp
  ring

private lemma factorialTerm_step_forward (a : ℝ) (k : ℕ) :
    factorialTerm a (k + 1) = a / ((k + 2 : ℕ) : ℝ) * factorialTerm a k := by
  simp only [factorialTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp
  ring

/-- A convenient piecewise majorant for the expression obtained after
inserting Ford's bound for `U_k` into the prime-bin bound for `T_k`.

Below the critical index the factorial terms grow geometrically; above it,
the factor `2^(k-v)` makes them decrease geometrically. -/
private noncomputable def tkEnvelope (a : ℝ) (v k : ℕ) : ℝ :=
  if k ≤ v then
    (1 + ((v - k : ℕ) : ℝ) ^ 2) * factorialTerm a k
  else
    (1 + ((k - v : ℕ) : ℝ) ^ 2) * factorialTerm a k /
      (2 : ℝ) ^ (k - v)

private lemma tkEnvelope_nonneg {a : ℝ} (ha : 0 ≤ a) (v k : ℕ) :
    0 ≤ tkEnvelope a v k := by
  rw [tkEnvelope]
  split_ifs
  · exact mul_nonneg (by positivity) (factorialTerm_nonneg ha k)
  · exact div_nonneg (mul_nonneg (by positivity) (factorialTerm_nonneg ha k))
      (by positivity)

/-! The two geometric comparisons are stated separately.  This is the only
place where the harmless numerical window around `2 log 2` is used. -/

private lemma factorialTerm_le_critical_of_le
    {a : ℝ} {v k : ℕ} (ha : 0 < a) (hv : 8 ≤ v)
    (halower : (5 : ℝ) / 4 * v ≤ a) (hkv : k ≤ v) :
    factorialTerm a k ≤ ((9 : ℝ) / 10) ^ (v - k) * factorialTerm a v := by
  induction hkv using Nat.decreasingInduction with
  | self => simp
  | of_succ k hkv ih =>
      rw [factorialTerm_step ha k]
      have hk2 : ((k + 2 : ℕ) : ℝ) / a ≤ (9 : ℝ) / 10 := by
        apply (div_le_iff₀ ha).2
        have hk2v : (k + 2 : ℕ) ≤ v + 1 := by omega
        have hvnum : ((v + 1 : ℕ) : ℝ) ≤ (9 : ℝ) / 8 * v := by
          have hv' : (8 : ℝ) ≤ v := by exact_mod_cast hv
          push_cast
          linarith
        calc
          ((k + 2 : ℕ) : ℝ) ≤ (v + 1 : ℕ) := by exact_mod_cast hk2v
          _ ≤ (9 : ℝ) / 8 * v := hvnum
          _ = (9 : ℝ) / 10 * ((5 : ℝ) / 4 * v) := by ring
          _ ≤ (9 : ℝ) / 10 * a := by gcongr
      calc
        ((k + 2 : ℕ) : ℝ) / a * factorialTerm a (k + 1) ≤
            ((9 : ℝ) / 10) *
              (((9 : ℝ) / 10) ^ (v - (k + 1)) * factorialTerm a v) := by
                gcongr
                exact factorialTerm_nonneg ha.le (k + 1)
        _ = ((9 : ℝ) / 10) ^ (v - k) * factorialTerm a v := by
          have hsub : v - k = (v - (k + 1)) + 1 := by omega
          rw [hsub, pow_succ]
          ring

private lemma factorialTerm_div_pow_le_critical_of_ge
    {a : ℝ} {v k : ℕ} (ha : 0 ≤ a)
    (haupper : a ≤ (3 : ℝ) / 2 * v) (hvk : v ≤ k) :
    factorialTerm a k / (2 : ℝ) ^ (k - v) ≤
      ((3 : ℝ) / 4) ^ (k - v) * factorialTerm a v := by
  induction hvk with
  | refl => simp
  | @step k hvk ih =>
      have hratio : a / ((2 : ℝ) * (k + 2)) ≤ (3 : ℝ) / 4 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (k + 2))).2
        calc
          a ≤ (3 : ℝ) / 2 * v := haupper
          _ ≤ (3 : ℝ) / 2 * (k + 2) := by
            gcongr
            exact_mod_cast (Nat.le_trans hvk (by omega : k ≤ k + 2))
          _ = (3 : ℝ) / 4 * (2 * (k + 2)) := by
            ring
      have hpow : k + 1 - v = (k - v) + 1 := by
        simpa [Nat.succ_eq_add_one] using Nat.succ_sub hvk
      rw [hpow, pow_succ, pow_succ, factorialTerm_step_forward]
      calc
        (a / ↑(k + 2) * factorialTerm a k) /
            ((2 : ℝ) ^ (k - v) * 2) =
            (a / (2 * (k + 2))) *
              (factorialTerm a k / (2 : ℝ) ^ (k - v)) := by
                push_cast
                field_simp
        _ ≤ (3 / 4 : ℝ) *
              (((3 / 4 : ℝ) ^ (k - v)) * factorialTerm a v) := by
                apply mul_le_mul hratio ih
                · exact div_nonneg (factorialTerm_nonneg ha k) (by positivity)
                · norm_num
        _ = (3 / 4 : ℝ) ^ ((k - v) + 1) * factorialTerm a v := by
          rw [pow_succ]
          ring

/-! ## Summing the envelope -/

private noncomputable def geomMajorant (r : ℝ) (d : ℕ) : ℝ :=
  (1 + (d : ℝ) ^ 2) * r ^ d

private lemma geomMajorant_nonneg {r : ℝ} (hr : 0 ≤ r) (d : ℕ) :
    0 ≤ geomMajorant r d := by
  unfold geomMajorant
  positivity

private lemma summable_geomMajorant {r : ℝ} (hr : |r| < 1) :
    Summable (geomMajorant r) := by
  have hnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs] using hr
  have hgeo : Summable (fun d : ℕ ↦ r ^ d) :=
    summable_geometric_of_norm_lt_one hnorm
  have hpoly : Summable (fun d : ℕ ↦ (d : ℝ) ^ 2 * r ^ d) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  convert hgeo.add hpoly using 1
  funext d
  simp only [geomMajorant]
  ring

/-- An absolute constant dominating the two convergent geometric series in
the lower- and upper-index ranges. -/
private noncomputable def envelopeConstant : ℝ :=
  ∑' d : ℕ, geomMajorant (9 / 10 : ℝ) d +
    ∑' d : ℕ, geomMajorant (3 / 4 : ℝ) d

private lemma envelopeConstant_nonneg : 0 ≤ envelopeConstant := by
  apply add_nonneg
  · exact tsum_nonneg fun d ↦ geomMajorant_nonneg (by norm_num) d
  · exact tsum_nonneg fun d ↦ geomMajorant_nonneg (by norm_num) d

private lemma tkEnvelope_pointwise_le
    {a : ℝ} {v k : ℕ} (ha : 0 < a) (hv : 8 ≤ v)
    (halower : (5 : ℝ) / 4 * v ≤ a)
    (haupper : a ≤ (3 : ℝ) / 2 * v) :
    tkEnvelope a v k ≤
      (if k ≤ v then geomMajorant (9 / 10 : ℝ) (v - k)
       else geomMajorant (3 / 4 : ℝ) (k - v)) * factorialTerm a v := by
  by_cases hkv : k ≤ v
  · rw [tkEnvelope, if_pos hkv, if_pos hkv, geomMajorant]
    calc
      (1 + (↑(v - k)) ^ 2) * factorialTerm a k ≤
          (1 + (↑(v - k)) ^ 2) *
            ((9 / 10 : ℝ) ^ (v - k) * factorialTerm a v) := by
              gcongr
              exact factorialTerm_le_critical_of_le ha hv halower hkv
      _ = ((1 + (↑(v - k)) ^ 2) * (9 / 10 : ℝ) ^ (v - k)) *
          factorialTerm a v := by ring
  · have hvk : v ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkv)
    rw [tkEnvelope, if_neg hkv, if_neg hkv, geomMajorant]
    calc
      (1 + (↑(k - v)) ^ 2) * factorialTerm a k / (2 : ℝ) ^ (k - v) =
          (1 + (↑(k - v)) ^ 2) *
            (factorialTerm a k / (2 : ℝ) ^ (k - v)) := by ring
      _ ≤ (1 + (↑(k - v)) ^ 2) *
            ((3 / 4 : ℝ) ^ (k - v) * factorialTerm a v) := by
              gcongr
              exact factorialTerm_div_pow_le_critical_of_ge ha.le haupper hvk
      _ = ((1 + (↑(k - v)) ^ 2) * (3 / 4 : ℝ) ^ (k - v)) *
          factorialTerm a v := by ring

private lemma sum_reindexed_le_tsum
    (s : Finset ℕ) (f : ℕ → ℕ) (g : ℕ → ℝ)
    (hf : Set.InjOn f s) (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n) :
    ∑ k ∈ s, g (f k) ≤ ∑' d, g d := by
  let t := s.image f
  have hsum : ∑ k ∈ s, g (f k) = ∑ d ∈ t, g d := by
    apply Finset.sum_bij (fun k _ ↦ f k)
    · intro k hk
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · intro k₁ hk₁ k₂ hk₂ h
      exact hf hk₁ hk₂ h
    · intro d hd
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
      exact ⟨k, hk, rfl⟩
    · intros
      rfl
  rw [hsum]
  exact hg.sum_le_tsum t (fun _ _ ↦ hg0 _)

private lemma sum_tkEnvelope_le
    {a : ℝ} {v n : ℕ} (ha : 0 < a) (hv : 8 ≤ v)
    (halower : (5 : ℝ) / 4 * v ≤ a)
    (haupper : a ≤ (3 : ℝ) / 2 * v) :
    ∑ k ∈ Finset.range n, tkEnvelope a v k ≤
      envelopeConstant * factorialTerm a v := by
  classical
  let low := (Finset.range n).filter fun k ↦ k ≤ v
  let high := (Finset.range n).filter fun k ↦ ¬k ≤ v
  have hcrit : 0 ≤ factorialTerm a v := factorialTerm_nonneg ha.le v
  have hpoint :
      ∑ k ∈ Finset.range n, tkEnvelope a v k ≤
        ∑ k ∈ Finset.range n,
          (if k ≤ v then geomMajorant (9 / 10 : ℝ) (v - k)
           else geomMajorant (3 / 4 : ℝ) (k - v)) * factorialTerm a v := by
    exact Finset.sum_le_sum fun k _ ↦
      tkEnvelope_pointwise_le ha hv halower haupper
  rw [← Finset.sum_mul] at hpoint
  refine hpoint.trans ?_
  apply mul_le_mul_of_nonneg_right _ hcrit
  have hsplit :
      ∑ k ∈ Finset.range n,
          (if k ≤ v then geomMajorant (9 / 10 : ℝ) (v - k)
           else geomMajorant (3 / 4 : ℝ) (k - v)) =
        (∑ k ∈ low, geomMajorant (9 / 10 : ℝ) (v - k)) +
        (∑ k ∈ high, geomMajorant (3 / 4 : ℝ) (k - v)) := by
    simp only [low, high, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkv : k ≤ v <;> simp [hkv]
  rw [hsplit, envelopeConstant]
  apply add_le_add
  · apply sum_reindexed_le_tsum low (fun k ↦ v - k)
      (geomMajorant (9 / 10 : ℝ))
    · intro k₁ hk₁ k₂ hk₂ h
      change k₁ ∈ (Finset.range n).filter (fun k ↦ k ≤ v) at hk₁
      change k₂ ∈ (Finset.range n).filter (fun k ↦ k ≤ v) at hk₂
      have hk₁v := (Finset.mem_filter.mp hk₁).2
      have hk₂v := (Finset.mem_filter.mp hk₂).2
      change v - k₁ = v - k₂ at h
      omega
    · exact summable_geomMajorant (by norm_num)
    · exact fun d ↦ geomMajorant_nonneg (by norm_num) d
  · apply sum_reindexed_le_tsum high (fun k ↦ k - v)
      (geomMajorant (3 / 4 : ℝ))
    · intro k₁ hk₁ k₂ hk₂ h
      change k₁ ∈ (Finset.range n).filter (fun k ↦ ¬k ≤ v) at hk₁
      change k₂ ∈ (Finset.range n).filter (fun k ↦ ¬k ≤ v) at hk₂
      have hk₁v := (Finset.mem_filter.mp hk₁).2
      have hk₂v := (Finset.mem_filter.mp hk₂).2
      change k₁ - v = k₂ - v at h
      omega
    · exact summable_geomMajorant (by norm_num)
    · exact fun d ↦ geomMajorant_nonneg (by norm_num) d

/-! ## Public finite assembly interface -/

/-- Public name for the critical factorial term used in Ford's summation. -/
noncomputable def fordCriticalTerm (a : ℝ) (v : ℕ) : ℝ :=
  factorialTerm a v

/-- Public name for the piecewise envelope obtained from the `U_k` bound. -/
noncomputable def fordTkEnvelope (a : ℝ) (v k : ℕ) : ℝ :=
  tkEnvelope a v k

theorem fordCriticalTerm_nonneg {a : ℝ} (ha : 0 ≤ a) (v : ℕ) :
    0 ≤ fordCriticalTerm a v := by
  exact factorialTerm_nonneg ha v

/-- Finite assembly of pointwise `T_k` estimates.  The statement is generic
so the prime-bin module can be improved independently: once each term is
bounded by a common constant times `fordTkEnvelope`, the entire finite sum
is bounded by an absolute constant times the critical factorial term.

This is a helper theorem, not an assumed Ford estimate. -/
theorem ford_sum_le_critical_of_le_envelope
    (T : ℕ → ℝ) {a C : ℝ} {v n : ℕ}
    (ha : 0 < a) (hC : 0 ≤ C) (hv : 8 ≤ v)
    (halower : (5 : ℝ) / 4 * v ≤ a)
    (haupper : a ≤ (3 : ℝ) / 2 * v)
    (hT : ∀ k ∈ Finset.range n, T k ≤ C * fordTkEnvelope a v k) :
    ∑ k ∈ Finset.range n, T k ≤
      (C * envelopeConstant) * fordCriticalTerm a v := by
  have hsum :
      ∑ k ∈ Finset.range n, T k ≤
        C * ∑ k ∈ Finset.range n, tkEnvelope a v k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hT
  calc
    ∑ k ∈ Finset.range n, T k ≤
        C * ∑ k ∈ Finset.range n, tkEnvelope a v k := hsum
    _ ≤ C * (envelopeConstant * factorialTerm a v) := by
      gcongr
      exact sum_tkEnvelope_le ha hv halower haupper
    _ = (C * envelopeConstant) * fordCriticalTerm a v := by
      simp [fordCriticalTerm]
      ring

/-! ## The range `k ≤ 10v` -/

private lemma ford_loglog_scale_window {y : ℕ}
    (hv : 14 ≤ fordBinIndex y) :
    let v := fordBinIndex y
    let a := 2 * Real.log (Real.log (2 * y))
    0 < a ∧ (5 : ℝ) / 4 * v ≤ a ∧ a ≤ (3 : ℝ) / 2 * v := by
  let v := fordBinIndex y
  let t := Real.log (Real.log (2 * y))
  let a := 2 * t
  have hv1 : 1 ≤ v := by dsimp [v]; omega
  have hvR : (14 : ℝ) ≤ v := by exact_mod_cast hv
  have htBounds := fordBinIndex_log_log_bounds (y := y) hv1
  have htLower : (v : ℝ) * Real.log 2 ≤ t := by
    simpa [v, t] using htBounds.1
  have htUpper : t < ((v : ℝ) + 1) * Real.log 2 := by
    simpa [v, t] using htBounds.2
  have htPos : 0 < t := by
    have hvPos : (0 : ℝ) < v := by positivity
    exact (mul_pos hvPos (Real.log_pos (by norm_num))).trans_le htLower
  dsimp [a]
  refine ⟨by positivity, ?_, ?_⟩
  · have hlogLower := Real.log_two_gt_d9
    dsimp [t] at htLower ⊢
    nlinarith
  · have hlogUpper := Real.log_two_lt_d9
    dsimp [t] at htUpper ⊢
    nlinarith

/-- Assembly of Ford's Lemma 3.5 with any already proved `U_k` envelope.
This is kept as a conditional helper solely to separate the prime-bin and
order-statistics modules; the assumption-free corollary below instantiates
it with Ford's clustered-volume theorem. -/
theorem ford_sum_Tk_small_of_uk_envelope
    (hUk : ∃ C : ℝ, 0 < C ∧ ∀ y k : ℕ,
      14 ≤ fordBinIndex y → k ≤ 10 * fordBinIndex y →
        (2 * Real.log (Real.log (2 * y))) ^ k * uk k (fordBinIndex y) ≤
          C * fordTkEnvelope (2 * Real.log (Real.log (2 * y)))
            (fordBinIndex y) k) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      ∑ k ∈ Finset.range (10 * fordBinIndex y + 1), Tk y k ≤
        C * fordCriticalTerm (2 * Real.log (Real.log (2 * y)))
          (fordBinIndex y) := by
  obtain ⟨C₅, hC₅, h₅⟩ := ford_lemma_three_five
  obtain ⟨Cᵤ, hCᵤ, hᵤ⟩ := hUk
  let C := C₅ * Cᵤ
  let D := C * envelopeConstant + 1
  have hC : 0 ≤ C := mul_nonneg hC₅.le hCᵤ.le
  have hD : 0 < D := by
    dsimp [D]
    linarith [mul_nonneg hC envelopeConstant_nonneg]
  refine ⟨D, hD, ?_⟩
  intro y hv
  let v := fordBinIndex y
  let a := 2 * Real.log (Real.log (2 * y))
  have hv1 : 1 ≤ v := by dsimp [v]; omega
  obtain ⟨ha, halower, haupper⟩ := ford_loglog_scale_window hv
  have hpoint : ∀ k ∈ Finset.range (10 * v + 1),
      Tk y k ≤ C * fordTkEnvelope a v k := by
    intro k hk
    have hkv : k ≤ 10 * v := by simpa using (Finset.mem_range.mp hk)
    have hbin := h₅ y k hv1 hkv
    have huk := hᵤ y k hv hkv
    calc
      Tk y k ≤ C₅ * (a ^ k * uk k v) := by
        simpa [a, v, mul_assoc] using hbin
      _ ≤ C₅ * (Cᵤ * fordTkEnvelope a v k) := by
        exact mul_le_mul_of_nonneg_left huk hC₅.le
      _ = C * fordTkEnvelope a v k := by simp [C, mul_assoc]
  have hsmall := ford_sum_le_critical_of_le_envelope
    (T := Tk y) (a := a) (C := C) ha hC (by omega : 8 ≤ v)
    halower haupper hpoint
  calc
    ∑ k ∈ Finset.range (10 * fordBinIndex y + 1), Tk y k =
        ∑ k ∈ Finset.range (10 * v + 1), Tk y k := rfl
    _ ≤ (C * envelopeConstant) * fordCriticalTerm a v := hsmall
    _ ≤ D * fordCriticalTerm a v := by
      apply mul_le_mul_of_nonneg_right _ (fordCriticalTerm_nonneg ha.le v)
      dsimp [D]
      linarith
    _ = D * fordCriticalTerm (2 * Real.log (Real.log (2 * y)))
          (fordBinIndex y) := rfl

/-- Multiplication by the prime-bin scale turns `ukEnvelope` into the
factorial envelope summed in this file. -/
lemma pow_mul_ukEnvelope_eq_fordTkEnvelope (a : ℝ) (k v : ℕ) :
    a ^ k * ukEnvelope k v = fordTkEnvelope a v k := by
  by_cases hkv : k ≤ v
  · simp only [ukEnvelope, hkv, if_pos, fordTkEnvelope, tkEnvelope,
      factorialTerm]
    ring
  · simp only [ukEnvelope, hkv, if_false, fordTkEnvelope, tkEnvelope,
      factorialTerm]
    ring

/-- The scaled `U_k` envelope needed by the finite summation, now obtained
without hypotheses from Ford's Lemma 3.6. -/
theorem ford_uk_scaled_envelope_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y k : ℕ,
      14 ≤ fordBinIndex y → k ≤ 10 * fordBinIndex y →
        (2 * Real.log (Real.log (2 * y))) ^ k * uk k (fordBinIndex y) ≤
          C * fordTkEnvelope (2 * Real.log (Real.log (2 * y)))
            (fordBinIndex y) k := by
  obtain ⟨C, hC, hbound⟩ := ford_uk_piecewise_bound
  refine ⟨C, hC, ?_⟩
  intro y k hv hk
  let a := 2 * Real.log (Real.log (2 * y))
  let v := fordBinIndex y
  have ha : 0 ≤ a := (ford_loglog_scale_window hv).1.le
  have hmain := hbound k v hk
  calc
    a ^ k * uk k v ≤ a ^ k * (C * ukEnvelope k v) :=
      mul_le_mul_of_nonneg_left hmain (pow_nonneg ha k)
    _ = C * fordTkEnvelope a v k := by
      rw [← pow_mul_ukEnvelope_eq_fordTkEnvelope a k v]
      ring

/-- Ford's small-index sum with all geometric inputs instantiated. -/
theorem ford_sum_Tk_small :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      ∑ k ∈ Finset.range (10 * fordBinIndex y + 1), Tk y k ≤
        C * fordCriticalTerm (2 * Real.log (Real.log (2 * y)))
          (fordBinIndex y) :=
  ford_sum_Tk_small_of_uk_envelope ford_uk_scaled_envelope_bound

theorem fordCriticalTerm_eq_stirlingTerm (y : ℕ) :
    fordCriticalTerm (2 * Real.log (Real.log (2 * y))) (fordBinIndex y) =
      stirlingTerm ((2 * y : ℕ) : ℝ) := by
  simp [fordCriticalTerm, factorialTerm, stirlingTerm, stirlingIndex,
    fordBinIndex]

theorem fordWeightSum_two_mul_eq_sum_Tk (y : ℕ) :
    fordWeightSum (2 * y) =
      ∑ k ∈ Finset.range ((Nat.primesLE (2 * y)).card + 1), Tk y k := by
  rw [sum_Tk_eq]
  simp [fordWeightSum, fordPrimeSubsets, primeSubsetProd]

private lemma sum_Tk_total_le_small_add_tail (y K : ℕ) :
    ∑ k ∈ Finset.range ((Nat.primesLE (2 * y)).card + 1), Tk y k ≤
      (∑ k ∈ Finset.range K, Tk y k) +
        ∑ k ∈ Finset.Icc K (Nat.primesLE (2 * y)).card, Tk y k := by
  classical
  let n := (Nat.primesLE (2 * y)).card
  have hdisj : Disjoint (Finset.range K) (Finset.Icc K n) := by
    rw [Finset.disjoint_left]
    intro k hkRange hkIcc
    have hklt := Finset.mem_range.mp hkRange
    have hKk := (Finset.mem_Icc.mp hkIcc).1
    omega
  have hsubset : Finset.range (n + 1) ⊆
      Finset.range K ∪ Finset.Icc K n := by
    intro k hk
    have hkn : k ≤ n := by simpa using (Finset.mem_range.mp hk)
    by_cases hkK : k < K
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hkK)
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr
        ⟨Nat.le_of_not_gt hkK, hkn⟩)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun k _ _ ↦ Tk_nonneg y k)
  rw [Finset.sum_union hdisj] at hsum
  exact hsum

/-- Finite assembly boundary for the two genuinely different estimates:
the clustered estimate for `k ≤ 10v` and the elementary factorial tail.
Both hypotheses are proved independently in their respective modules. -/
theorem fordWeightSum_two_mul_le_stirling_of_small_tail
    (hSmall : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      ∑ k ∈ Finset.range (10 * fordBinIndex y + 1), Tk y k ≤
        C * fordCriticalTerm (2 * Real.log (Real.log (2 * y)))
          (fordBinIndex y))
    (hTail : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      ∑ k ∈ Finset.Icc (10 * fordBinIndex y + 1)
          (Nat.primesLE (2 * y)).card, Tk y k ≤
        C * stirlingTerm ((2 * y : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      fordWeightSum (2 * y) ≤ C * stirlingTerm ((2 * y : ℕ) : ℝ) := by
  obtain ⟨Csmall, hCsmall, hsmall⟩ := hSmall
  obtain ⟨Ctail, hCtail, htail⟩ := hTail
  refine ⟨Csmall + Ctail, add_pos hCsmall hCtail, ?_⟩
  intro y hv
  have hterm : 0 ≤ stirlingTerm ((2 * y : ℕ) : ℝ) := by
    rw [← fordCriticalTerm_eq_stirlingTerm]
    exact fordCriticalTerm_nonneg (ford_loglog_scale_window hv).1.le _
  rw [fordWeightSum_two_mul_eq_sum_Tk]
  calc
    ∑ k ∈ Finset.range ((Nat.primesLE (2 * y)).card + 1), Tk y k ≤
        (∑ k ∈ Finset.range (10 * fordBinIndex y + 1), Tk y k) +
          ∑ k ∈ Finset.Icc (10 * fordBinIndex y + 1)
            (Nat.primesLE (2 * y)).card, Tk y k :=
      sum_Tk_total_le_small_add_tail y _
    _ ≤ Csmall * fordCriticalTerm (2 * Real.log (Real.log (2 * y)))
          (fordBinIndex y) + Ctail * stirlingTerm ((2 * y : ℕ) : ℝ) :=
      add_le_add (hsmall y hv) (htail y hv)
    _ = (Csmall + Ctail) * stirlingTerm ((2 * y : ℕ) : ℝ) := by
      rw [fordCriticalTerm_eq_stirlingTerm]
      ring

/-- All analytic inputs except the final clustered-volume instantiation have
now been discharged: the tail theorem is unconditional. -/
theorem fordWeightSum_two_mul_le_stirling_of_uk_envelope
    (hUk : ∃ C : ℝ, 0 < C ∧ ∀ y k : ℕ,
      14 ≤ fordBinIndex y → k ≤ 10 * fordBinIndex y →
        (2 * Real.log (Real.log (2 * y))) ^ k * uk k (fordBinIndex y) ≤
          C * fordTkEnvelope (2 * Real.log (Real.log (2 * y)))
            (fordBinIndex y) k) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      fordWeightSum (2 * y) ≤ C * stirlingTerm ((2 * y : ℕ) : ℝ) :=
  fordWeightSum_two_mul_le_stirling_of_small_tail
    (ford_sum_Tk_small_of_uk_envelope hUk) ford_sum_Tk_tail

/-! ## From the even endpoint to the logarithmic scale -/

theorem fordWeightSum_nonneg (x : ℕ) : 0 ≤ fordWeightSum x := by
  unfold fordWeightSum
  exact Finset.sum_nonneg fun s _ ↦
    div_nonneg (L_nonneg _ _) (Nat.cast_nonneg _)

/-- Enlarging the prime endpoint only adds nonnegative squarefree weights. -/
theorem fordWeightSum_mono : Monotone fordWeightSum := by
  intro x y hxy
  rw [fordWeightSum_eq, fordWeightSum_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    rw [fordPrimeSubsets, Finset.mem_powerset] at hs ⊢
    intro p hp
    have hp' := hs hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_mem_primesLE hp').trans hxy,
        Nat.prime_of_mem_primesLE hp'⟩
  · intro s _ _
    unfold fordWeight
    exact div_nonneg (L_nonneg _ _) (Nat.cast_nonneg _)

theorem fordBinIndex_tendsto_atTop :
    Tendsto fordBinIndex atTop atTop := by
  have hmul : Tendsto (fun y : ℕ ↦ (2 : ℝ) * (y : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hloglog : Tendsto
      (fun y : ℕ ↦ Real.log (Real.log ((2 : ℝ) * (y : ℝ))))
      atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hmul)
  have hdiv : Tendsto
      (fun y : ℕ ↦ Real.log (Real.log ((2 : ℝ) * (y : ℝ))) / Real.log 2)
      atTop atTop := by
    simpa only [div_eq_mul_inv] using hloglog.atTop_mul_const
      (inv_pos.mpr (Real.log_pos one_lt_two))
  have hfloor := tendsto_nat_floor_atTop.comp hdiv
  change Tendsto
    (fun y : ℕ ↦
      ⌊Real.log (Real.log ((2 : ℝ) * (y : ℝ))) / Real.log 2⌋₊)
    atTop atTop at hfloor
  have heq : fordBinIndex =
      (fun y : ℕ ↦
        ⌊Real.log (Real.log ((2 : ℝ) * (y : ℝ))) / Real.log 2⌋₊) := by
    funext y
    simp only [fordBinIndex]
  rw [heq]
  exact hfloor

/-- Replacing `t` by `2t` changes Ford's logarithmic target by at most an
absolute factor on the positive iterated-log domain. -/
theorem stirlingTarget_two_mul_le (t : ℕ) (ht : 3 ≤ t) :
    stirlingTarget ((2 * t : ℕ) : ℝ) ≤
      4 * stirlingTarget (t : ℝ) := by
  let α : ℝ := 2 - Erdos896.delta896
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by positivity
  have hlogt : 1 < Real.log (t : ℝ) := by
    apply (Real.lt_log_iff_exp_lt ht0).2
    exact Real.exp_one_lt_three.trans_le htR
  have hlogt0 : 0 < Real.log (t : ℝ) := zero_lt_one.trans hlogt
  have hlog2t : Real.log (((2 * t : ℕ) : ℝ)) =
      Real.log 2 + Real.log (t : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne']
  have hlogtwo_le : Real.log 2 ≤ Real.log (t : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (Set.mem_Ioi.mpr ht0) (by exact_mod_cast (show 2 ≤ t by omega))
  have hlogBound : Real.log (((2 * t : ℕ) : ℝ)) ≤
      2 * Real.log (t : ℝ) := by
    rw [hlog2t]
    linarith
  have hlog2tPos : 0 < Real.log (((2 * t : ℕ) : ℝ)) := by
    rw [hlog2t]
    positivity
  have hlogMono : Real.log (t : ℝ) ≤
      Real.log (((2 * t : ℕ) : ℝ)) := by
    rw [hlog2t]
    exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))
  have hloglogMono : Real.log (Real.log (t : ℝ)) ≤
      Real.log (Real.log (((2 * t : ℕ) : ℝ))) := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hlogt0)
      (Set.mem_Ioi.mpr hlog2tPos) hlogMono
  have hα0 : 0 ≤ α := by
    dsimp [α]
    linarith [Erdos896.delta896_le_one]
  have hα2 : α ≤ 2 := by
    dsimp [α]
    linarith [Erdos896.delta896_nonneg]
  have htwoα : (2 : ℝ) ^ α ≤ 4 := by
    calc
      (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hα2
      _ = 4 := by norm_num
  have hnum : Real.log (((2 * t : ℕ) : ℝ)) ^ α ≤
      4 * Real.log (t : ℝ) ^ α := by
    calc
      Real.log (((2 * t : ℕ) : ℝ)) ^ α ≤
          (2 * Real.log (t : ℝ)) ^ α :=
        Real.rpow_le_rpow hlog2tPos.le hlogBound hα0
      _ = (2 : ℝ) ^ α * Real.log (t : ℝ) ^ α := by
        rw [Real.mul_rpow (by norm_num) hlogt0.le]
      _ ≤ 4 * Real.log (t : ℝ) ^ α := by
        exact mul_le_mul_of_nonneg_right htwoα (Real.rpow_nonneg hlogt0.le _)
  have hloglogt : 0 < Real.log (Real.log (t : ℝ)) := Real.log_pos hlogt
  have hden : Real.log (Real.log (t : ℝ)) ^ (3 / 2 : ℝ) ≤
      Real.log (Real.log (((2 * t : ℕ) : ℝ))) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hloglogt.le hloglogMono (by norm_num)
  have hdenPos : 0 < Real.log (Real.log (t : ℝ)) ^ (3 / 2 : ℝ) := by
    positivity
  rw [stirlingTarget, stirlingTarget]
  change Real.log (((2 * t : ℕ) : ℝ)) ^ α /
      Real.log (Real.log (((2 * t : ℕ) : ℝ))) ^ (3 / 2 : ℝ) ≤
    4 * (Real.log (t : ℝ) ^ α /
      Real.log (Real.log (t : ℝ)) ^ (3 / 2 : ℝ))
  calc
    Real.log (((2 * t : ℕ) : ℝ)) ^ α /
          Real.log (Real.log (((2 * t : ℕ) : ℝ))) ^ (3 / 2 : ℝ) ≤
        Real.log (((2 * t : ℕ) : ℝ)) ^ α /
          Real.log (Real.log (t : ℝ)) ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hlog2tPos.le _) hdenPos hden
    _ ≤ (4 * Real.log (t : ℝ) ^ α) /
          Real.log (Real.log (t : ℝ)) ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_right hnum hdenPos.le
    _ = 4 * (Real.log (t : ℝ) ^ α /
          Real.log (Real.log (t : ℝ)) ^ (3 / 2 : ℝ)) := by ring

/-- Uniform logarithmic-scale consequence of an even-endpoint Stirling
bound.  This helper makes the monotonicity and doubling passage explicit. -/
theorem exists_fordWeightSum_le_scale_of_even_stirling
    (hEven : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      fordWeightSum (2 * y) ≤ C * stirlingTerm ((2 * y : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordWeightSum t ≤ C * stirlingTarget (t : ℝ) := by
  obtain ⟨C, hC, heven⟩ := hEven
  have hIndex := fordBinIndex_tendsto_atTop
  rw [tendsto_atTop_atTop] at hIndex
  obtain ⟨T, hT⟩ := hIndex 14
  let K : ℝ := Real.exp 1 * (Real.log 2) ^ (3 / 2 : ℝ)
  refine ⟨4 * (C * K), by dsimp [K]; positivity, max T 3, ?_⟩
  intro t ht
  have htT : T ≤ t := (le_max_left T 3).trans ht
  have ht3 : 3 ≤ t := (le_max_right T 3).trans ht
  have hidx : 14 ≤ fordBinIndex t := hT t htT
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht3
  have ht0 : (0 : ℝ) < t := by positivity
  have h2t0 : (0 : ℝ) < ((2 * t : ℕ) : ℝ) := by positivity
  have hlog2t : 1 < Real.log (((2 * t : ℕ) : ℝ)) := by
    apply (Real.lt_log_iff_exp_lt h2t0).2
    have : (Real.exp 1 : ℝ) < 2 * t := by
      nlinarith [Real.exp_one_lt_three]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact this
  have hstir := stirlingTerm_le_target hlog2t
  have htarget := stirlingTarget_two_mul_le t ht3
  calc
    fordWeightSum t ≤ fordWeightSum (2 * t) :=
      fordWeightSum_mono (by omega)
    _ ≤ C * stirlingTerm ((2 * t : ℕ) : ℝ) := heven t hidx
    _ ≤ C * (K * stirlingTarget ((2 * t : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [K] using hstir) hC.le
    _ ≤ C * (K * (4 * stirlingTarget (t : ℝ))) := by
      gcongr
    _ = 4 * (C * K) * stirlingTarget (t : ℝ) := by ring

/-- The same conclusion with the target unfolded, for downstream modules
that should not need to depend on the Stirling helper's definition name. -/
theorem exists_fordWeightSum_le_explicit_scale_of_even_stirling
    (hEven : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      fordWeightSum (2 * y) ≤ C * stirlingTerm ((2 * y : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordWeightSum t ≤
        C * ((Real.log t) ^ (2 - Erdos896.delta896) /
          (Real.log (Real.log t)) ^ (3 / 2 : ℝ)) := by
  simpa only [stirlingTarget] using
    exists_fordWeightSum_le_scale_of_even_stirling hEven

private lemma inv_log_sq_mul_stirlingTarget {t : ℕ} (ht : 3 ≤ t) :
    (1 / Real.log t ^ 2) * stirlingTarget (t : ℝ) =
      1 / Erdos896.logDenom896 t := by
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by positivity
  have hlogt : 1 < Real.log (t : ℝ) := by
    apply (Real.lt_log_iff_exp_lt ht0).2
    exact Real.exp_one_lt_three.trans_le htR
  have hlogt0 : 0 < Real.log (t : ℝ) := zero_lt_one.trans hlogt
  have hloglogt0 : 0 < Real.log (Real.log (t : ℝ)) := Real.log_pos hlogt
  rw [stirlingTarget, Erdos896.logDenom896, Erdos896.logDenom896R,
    Real.rpow_sub hlogt0]
  field_simp
  rw [Real.rpow_two]

/-- Ford's denominator-removal estimate turns the weight-sum scale into the
upper bound for the analytic `S`-sum. -/
theorem exists_fordDenominatorSum_le_scale_of_weight
    (hWeight : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordWeightSum t ≤ C * stirlingTarget (t : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordDenominatorSum t ≤ C / Erdos896.logDenom896 t := by
  obtain ⟨Cden, hCden, hden⟩ :=
    exists_fordDenominatorSum_le_const_div_log_sq
  obtain ⟨Cweight, hCweight, T, hweight⟩ := hWeight
  let C := (Cden + 1) * Cweight
  refine ⟨C, by dsimp [C]; positivity, max T 3, ?_⟩
  intro t ht
  have htT : T ≤ t := (le_max_left T 3).trans ht
  have ht3 : 3 ≤ t := (le_max_right T 3).trans ht
  have hlogt : 0 < Real.log (t : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hinv : 0 ≤ Cden / Real.log t ^ 2 := by positivity
  calc
    fordDenominatorSum t ≤
        Cden / Real.log t ^ 2 * fordWeightSum t := hden t (by omega)
    _ ≤ Cden / Real.log t ^ 2 *
          (Cweight * stirlingTarget (t : ℝ)) :=
      mul_le_mul_of_nonneg_left (hweight t htT) hinv
    _ = (Cden * Cweight) *
          ((1 / Real.log t ^ 2) * stirlingTarget (t : ℝ)) := by ring
    _ = (Cden * Cweight) * (1 / Erdos896.logDenom896 t) := by
      rw [inv_log_sq_mul_stirlingTarget ht3]
    _ ≤ ((Cden + 1) * Cweight) * (1 / Erdos896.logDenom896 t) := by
      have hdenom := Erdos896.logDenom896_pos ht3
      gcongr
      linarith
    _ = C / Erdos896.logDenom896 t := by
      dsimp [C]
      ring

theorem exists_fordDenominatorSum_le_scale_of_even_stirling
    (hEven : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      fordWeightSum (2 * y) ≤ C * stirlingTerm ((2 * y : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordDenominatorSum t ≤ C / Erdos896.logDenom896 t :=
  exists_fordDenominatorSum_le_scale_of_weight
    (exists_fordWeightSum_le_scale_of_even_stirling hEven)

/-- Fully assembled weight and `S` bounds from a proved `U_k` envelope.
These helper statements keep the analytic summation independent of the
geometric module that establishes the envelope. -/
theorem exists_fordWeightSum_le_scale_of_uk_envelope
    (hUk : ∃ C : ℝ, 0 < C ∧ ∀ y k : ℕ,
      14 ≤ fordBinIndex y → k ≤ 10 * fordBinIndex y →
        (2 * Real.log (Real.log (2 * y))) ^ k * uk k (fordBinIndex y) ≤
          C * fordTkEnvelope (2 * Real.log (Real.log (2 * y)))
            (fordBinIndex y) k) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordWeightSum t ≤
        C * ((Real.log t) ^ (2 - Erdos896.delta896) /
          (Real.log (Real.log t)) ^ (3 / 2 : ℝ)) :=
  exists_fordWeightSum_le_explicit_scale_of_even_stirling
    (fordWeightSum_two_mul_le_stirling_of_uk_envelope hUk)

theorem exists_fordDenominatorSum_le_scale_of_uk_envelope
    (hUk : ∃ C : ℝ, 0 < C ∧ ∀ y k : ℕ,
      14 ≤ fordBinIndex y → k ≤ 10 * fordBinIndex y →
        (2 * Real.log (Real.log (2 * y))) ^ k * uk k (fordBinIndex y) ≤
          C * fordTkEnvelope (2 * Real.log (Real.log (2 * y)))
            (fordBinIndex y) k) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordDenominatorSum t ≤ C / Erdos896.logDenom896 t :=
  exists_fordDenominatorSum_le_scale_of_even_stirling
    (fordWeightSum_two_mul_le_stirling_of_uk_envelope hUk)

/-! ## Assumption-free upper bounds -/

/-- The squarefree Ford weight has the Erdős--Tenenbaum--Ford logarithmic
scale.  This is the public input consumed by `ReductionCollapse`. -/
theorem exists_fordWeightSum_le_scale :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordWeightSum t ≤
        C * ((Real.log t) ^ (2 - Erdos896.delta896) /
          (Real.log (Real.log t)) ^ (3 / 2 : ℝ)) :=
  exists_fordWeightSum_le_scale_of_uk_envelope ford_uk_scaled_envelope_bound

/-- Ford's denominator-weighted `S`-sum is bounded by the reciprocal
logarithmic denominator. -/
theorem exists_fordDenominatorSum_le_scale :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t →
      fordDenominatorSum t ≤ C / Erdos896.logDenom896 t :=
  exists_fordDenominatorSum_le_scale_of_uk_envelope
    ford_uk_scaled_envelope_bound

end Erdos896.Ford
