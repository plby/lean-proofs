import ErdosProblems.Erdos587.HooleySieveMean
import ErdosProblems.Erdos587.HooleySmoothTail

/-!
# A single smooth-prefix tail range in a short progression

The rough-cofactor divisor cost and the smooth-prefix Rankin saving are
kept in one exponential. The next step is to choose logarithmic prime
ranges for which the saving dominates the cofactor cost.
-/

open scoped BigOperators

namespace Erdos587

theorem delta_sieve_tail_range_weighted_le {A B : ℤ} (hB : B ≠ 0) (hAB : IsCoprime A B)
    {Q z N Y D : ℕ} (hQ : 0 < Q) (hz : 2 ≤ z) (hcut : D * Q ^ 2 ≤ Y)
    {T β M : ℝ} (hT : 0 < T) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hM : β * Real.log (z : ℝ) ≤ M) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Y)
    (hvalues : ∀ n ∈ S, (A + B * n).natAbs ≤ N)
    {K : ℝ} (hK : 0 ≤ K)
    (hcover : ∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
      0 < a ∧ 0 < b ∧ a ≤ D ∧ T ≤ a ∧
      a.primeFactors ⊆ Nat.primesLE z ∧ (∀ p ∈ b.primeFactors, Q < p) ∧
      (b.divisors.card : ℝ) ≤ K) :
    (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
      3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) *
        K * Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M - β * Real.log T) *
            ∑ d ∈ Finset.Icc 1 N, (hooleyDelta d : ℝ) / d := by
  classical
  let E := (Finset.Icc 1 (min D N)).filter (fun a : ℕ =>
    T ≤ (a : ℝ) ∧ a.primeFactors ⊆ Nat.primesLE z)
  have hEpos (a : ℕ) (ha : a ∈ E) : 0 < a :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  have hEsub : E ⊆ Finset.Icc 1 N := by
    intro a ha
    obtain ⟨ha1, haD⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    exact Finset.mem_Icc.mpr ⟨ha1, (le_min_iff.mp haD).2⟩
  have hEcut (a : ℕ) (ha : a ∈ E) : a * Q ^ 2 ≤ Y :=
    (Nat.mul_le_mul_right _
      (le_min_iff.mp (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2).1).trans hcut
  have hEcover : ∀ n ∈ S, ∃ a ∈ E, ∃ b : ℕ, 0 < b ∧ (A + B * n).natAbs = a * b ∧
      (∀ p ∈ b.primeFactors, Q < p) ∧ (b.divisors.card : ℝ) ≤ K := by
    intro n hn
    obtain ⟨a, b, hfactor, ha, hb, haD, hTa, hsmooth, hrough, hweight⟩ := hcover n hn
    have haN : a ≤ N := by nlinarith [hvalues n hn]
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, le_min haD haN⟩,
      hTa, hsmooth⟩, b, hb, hfactor, hrough, hweight⟩
  have hsieve := delta_weighted_factor_sieve_le hB hAB hQ S E hS hEpos hEcut
    hK hEcover
  have htail := delta_smooth_harmonic_tail_le E hz hEsub
    (fun a ha => (Finset.mem_filter.mp ha).2.2) hT
    (fun a ha => (Finset.mem_filter.mp ha).2.1) hβ0 hβ hM
  have hlogQ : 0 < Real.log (Q + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q + 1 by omega))
  calc
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) * K *
        ∑ d ∈ E, (hooleyDelta d : ℝ) / d := hsieve
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) * K *
        (Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M - β * Real.log T) *
          ∑ d ∈ Finset.Icc 1 N, (hooleyDelta d : ℝ) / d) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

theorem delta_sieve_tail_range_le {A B : ℤ} (hB : B ≠ 0) (hAB : IsCoprime A B)
    {Q z N Y D : ℕ} (hQ : 0 < Q) (hz : 2 ≤ z) (hcut : D * Q ^ 2 ≤ Y)
    {T β M : ℝ} (hT : 0 < T) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hM : β * Real.log (z : ℝ) ≤ M) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Y)
    (hvalues : ∀ n ∈ S, (A + B * n).natAbs ≤ N)
    (hcover : ∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
      0 < a ∧ 0 < b ∧ a ≤ D ∧ T ≤ a ∧
      a.primeFactors ⊆ Nat.primesLE z ∧ ∀ p ∈ b.primeFactors, Q < p) :
    (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
      3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) *
        Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log (Q + 1 : ℕ) +
          20 * deltaRankinMertensConstant * M * Real.exp M - β * Real.log T) *
            ∑ d ∈ Finset.Icc 1 N, (hooleyDelta d : ℝ) / d := by
  let K := Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log (Q + 1 : ℕ))
  have hbound := delta_sieve_tail_range_weighted_le hB hAB hQ hz hcut hT hβ0 hβ hM
    S hS hvalues (Real.exp_nonneg (Real.log 2 * Real.log (N : ℝ) / Real.log (Q + 1 : ℕ)))
  have hcover' : ∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
      0 < a ∧ 0 < b ∧ a ≤ D ∧ T ≤ a ∧ a.primeFactors ⊆ Nat.primesLE z ∧
      (∀ p ∈ b.primeFactors, Q < p) ∧ (b.divisors.card : ℝ) ≤ K := by
    intro n hn
    obtain ⟨a, b, hfactor, ha, hb, haD, hTa, hsmooth, hrough⟩ := hcover n hn
    have hbN : b ≤ N := by nlinarith [hvalues n hn]
    exact ⟨a, b, hfactor, ha, hb, haD, hTa, hsmooth, hrough,
      card_divisors_rough_exp_le (by omega : 2 ≤ Q + 1) hb.ne'
        (fun p hp => hrough p hp) hbN⟩
  calc
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) *
        K * Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M - β * Real.log T) *
          ∑ d ∈ Finset.Icc 1 N, (hooleyDelta d : ℝ) / d := hbound hcover'
    _ = _ := by
      dsimp only [K]
      rw [show Real.log 2 * Real.log (N : ℝ) / Real.log (Q + 1 : ℕ) +
          20 * deltaRankinMertensConstant * M * Real.exp M - β * Real.log T =
            Real.log 2 * Real.log (N : ℝ) / Real.log (Q + 1 : ℕ) +
              (20 * deltaRankinMertensConstant * M * Real.exp M - β * Real.log T) by ring,
        Real.exp_add]
      ring

end Erdos587
