import ErdosProblems.Erdos964.LinearCharacterSieve
import BoundedGaps.BombieriVinogradov.Analytic.ReciprocalTotientPrefix

/-!
# Conductor multipliers and excluded prime factors

An excluded prime factor must divide the multiplier of the inducing
conductor. Summing the reciprocal totient over these multiples gives the
additional reciprocal-prime factor needed for a small correction term.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

/-- Reindex the reciprocal-totient character mass by the inducing conductor
and its positive multiplier. -/
theorem sum_conductor_weights_eq (T : ℕ)
    (F : ∀ _q d : ℕ, primitiveCharacters d → ℝ) :
    (∑ q ∈ Finset.Ioc 0 T,
      (∑ d : q.divisors, ∑ ψ : primitiveCharacters d.1, F q d.1 ψ) / q.totient) =
      ∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
        ((d * k).totient : ℝ)⁻¹ * ∑ ψ : primitiveCharacters d, F (d * k) d ψ := by
  classical
  calc
    _ = ∑ q ∈ Finset.Ioc 0 T, ∑ d : q.divisors, ∑ ψ : primitiveCharacters d.1,
        (q.totient : ℝ)⁻¹ * F q d.1 ψ := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      simp only [mul_comm]
    _ = ∑ z ∈ positiveFactorPairs T, ∑ ψ : primitiveCharacters z.1,
        ((z.1 * z.2).totient : ℝ)⁻¹ * F (z.1 * z.2) z.1 ψ :=
      sum_primitive_conductors_up_to_eq_sum_positiveFactorPairs
        (fun {q d} _ ψ => (q.totient : ℝ)⁻¹ * F q d ψ)
    _ = _ := by
      simp only [← Finset.mul_sum]
      simpa using sum_positiveFactorPairs_filter_fst_eq_sum_multipliers
        (Q := T) (fun _ => True)
        (fun d k => ((d * k).totient : ℝ)⁻¹ * ∑ ψ : primitiveCharacters d, F (d * k) d ψ)

theorem sum_multiples_Ioc {A : Type*} [AddCommMonoid A]
    (p K : ℕ) (hp : 0 < p) (f : ℕ → A) :
    (∑ k ∈ Finset.Ioc 0 K with p ∣ k, f k) =
      ∑ l ∈ Finset.Ioc 0 (K / p), f (p * l) := by
  apply Finset.sum_bij (fun k _ => k / p)
  · intro k hk
    obtain ⟨hkIoc, hpk⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkpos, hkK⟩ := Finset.mem_Ioc.mp hkIoc
    exact Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hkpos hpk) hp,
      Nat.div_le_div_right hkK⟩
  · intro k hk l hl hkl
    have hpk := (Finset.mem_filter.mp hk).2
    have hpl := (Finset.mem_filter.mp hl).2
    calc
      k = p * (k / p) := (Nat.mul_div_cancel' hpk).symm
      _ = p * (l / p) := congrArg (p * ·) hkl
      _ = l := Nat.mul_div_cancel' hpl
  · intro l hl
    obtain ⟨hlpos, hlK⟩ := Finset.mem_Ioc.mp hl
    refine ⟨p * l, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp hlpos,
      ?_⟩, Nat.dvd_mul_right p l⟩, ?_⟩
    · simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp).mp hlK
    · exact Nat.mul_div_right l hp
  · intro k hk
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hk).2]

/-- Uniform logarithmic bound for the multiplier totients with an imposed
divisor. The extra factor `1 / φ(p)` is retained. -/
theorem sum_multiples_inv_totient_le (T d p : ℕ) (hd : 0 < d) (hp : 0 < p) :
    (∑ k ∈ Finset.Ioc 0 (T / d) with p ∣ k,
      ((d * k).totient : ℝ)⁻¹) ≤
      (d.totient : ℝ)⁻¹ * (p.totient : ℝ)⁻¹ * (4 * (1 + Real.log (T : ℝ))) := by
  rw [sum_multiples_Ioc p (T / d) hp]
  have htotal : 0 ≤ 4 * (1 + Real.log (T : ℝ)) := by
    have := Real.log_natCast_nonneg T
    positivity
  have hprefix :
      (∑ l ∈ Finset.Ioc 0 (T / d / p), (l.totient : ℝ)⁻¹) ≤
        4 * (1 + Real.log (T : ℝ)) := by
    by_cases hpos : 0 < T / d / p
    · have h := reciprocalTotientPrefix_le_four_mul_one_add_log hpos
      have hlog : Real.log ((T / d / p : ℕ) : ℝ) ≤ Real.log (T : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hpos
        · exact_mod_cast (Nat.div_le_self (T / d) p).trans (Nat.div_le_self T d)
      calc
        _ = reciprocalTotientPrefix (T / d / p) := rfl
        _ ≤ 4 * (1 + Real.log ((T / d / p : ℕ) : ℝ)) := h
        _ ≤ _ := by linarith
    · have hz : T / d / p = 0 := Nat.eq_zero_of_not_pos hpos
      simpa only [hz, Finset.Ioc_self, Finset.sum_empty] using htotal
  calc
    _ ≤ ∑ l ∈ Finset.Ioc 0 (T / d / p),
        ((d * p).totient : ℝ)⁻¹ * (l.totient : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro l hl
      simpa only [mul_assoc] using inv_totient_mul_le_mul_inv_totient
        (Nat.mul_pos hd hp) (Finset.mem_Ioc.mp hl).1
    _ = ((d * p).totient : ℝ)⁻¹ *
        ∑ l ∈ Finset.Ioc 0 (T / d / p), (l.totient : ℝ)⁻¹ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((d * p).totient : ℝ)⁻¹ * (4 * (1 + Real.log (T : ℝ))) :=
      mul_le_mul_of_nonneg_left hprefix (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (inv_totient_mul_le_mul_inv_totient hd hp) htotal

/-- The same multiplier estimate with the exact conductor support. -/
theorem sum_multiples_inv_totient_le_indicator (T d p : ℕ)
    (hd : 0 < d) (hp : 0 < p) :
    (∑ k ∈ Finset.Ioc 0 (T / d) with p ∣ k,
      ((d * k).totient : ℝ)⁻¹) ≤
      if d ≤ T / p then
        (d.totient : ℝ)⁻¹ * (p.totient : ℝ)⁻¹ * (4 * (1 + Real.log (T : ℝ)))
      else 0 := by
  by_cases hcut : d ≤ T / p
  · rw [if_pos hcut]
    exact sum_multiples_inv_totient_le T d p hd hp
  · have hempty : (Finset.Ioc 0 (T / d)).filter (fun k => p ∣ k) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨hkIoc, hpk⟩ := Finset.mem_filter.mp hk
      obtain ⟨hkpos, hkT⟩ := Finset.mem_Ioc.mp hkIoc
      have hpkle := Nat.le_of_dvd hkpos hpk
      apply hcut
      apply (Nat.le_div_iff_mul_le hp).mpr
      calc
        d * p ≤ d * k := Nat.mul_le_mul_left d hpkle
        _ ≤ T := by simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkT
    rw [hempty, Finset.sum_empty, if_neg hcut]

/-- Average a nonnegative conductor quantity over moduli with an excluded
prime. Both the reciprocal-prime weight and the smaller conductor range
`T / p` are preserved. -/
theorem excludedPrime_conductor_mass_le (P : Finset ℕ) (T : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (U : ℕ → ℝ) (hU : ∀ d, 0 ≤ U d) :
    (∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
      ((d * k).totient : ℝ)⁻¹ *
        ∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, U d) ≤
      ∑ p ∈ P, ((p.totient : ℝ)⁻¹ * (4 * (1 + Real.log (T : ℝ)))) *
        ∑ d ∈ Finset.Ioc 0 (T / p), U d / d.totient := by
  classical
  have hpoint (d k : ℕ) :
      ((d * k).totient : ℝ)⁻¹ *
          (∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, U d) ≤
        ∑ p ∈ P, if p ∣ k then ((d * k).totient : ℝ)⁻¹ * U d else 0 := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ p ∈ P with p ∣ k, ((d * k).totient : ℝ)⁻¹ * U d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpP, hpdk, hpd⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨hpP, ((hP p hpP).dvd_mul.mp hpdk).resolve_left hpd⟩
        · intro p _ _
          exact mul_nonneg (by positivity) (hU d)
      _ = _ := Finset.sum_filter _ _
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
        ∑ p ∈ P, if p ∣ k then ((d * k).totient : ℝ)⁻¹ * U d else 0 := by
      exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun k _ => hpoint d k))
    _ = ∑ p ∈ P, ∑ d ∈ Finset.Ioc 0 T,
        U d * ∑ k ∈ Finset.Ioc 0 (T / d) with p ∣ k,
          ((d * k).totient : ℝ)⁻¹ := by
      calc
        _ = ∑ d ∈ Finset.Ioc 0 T, ∑ p ∈ P, ∑ k ∈ Finset.Ioc 0 (T / d),
            if p ∣ k then ((d * k).totient : ℝ)⁻¹ * U d else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
        _ = _ := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero, mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hfilter : (Finset.Ioc 0 T).filter (fun d => d ≤ T / p) =
          Finset.Ioc 0 (T / p) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        have := Nat.div_le_self T p
        omega
      calc
        _ ≤ ∑ d ∈ Finset.Ioc 0 T,
            if d ≤ T / p then U d *
              ((d.totient : ℝ)⁻¹ * (p.totient : ℝ)⁻¹ *
                (4 * (1 + Real.log (T : ℝ)))) else 0 := by
          apply Finset.sum_le_sum
          intro d hd
          have h := mul_le_mul_of_nonneg_left
            (sum_multiples_inv_totient_le_indicator T d p
              (Finset.mem_Ioc.mp hd).1 (hP p hp).pos) (hU d)
          simpa only [mul_ite, mul_zero] using h
        _ = _ := by
          rw [← Finset.sum_filter, hfilter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring

/-- The ordinary multiplier sum costs only a logarithmic factor. -/
theorem conductor_mass_le_log_prefix (T : ℕ) (U : ℕ → ℝ) (hU : ∀ d, 0 ≤ U d) :
    (∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
      ((d * k).totient : ℝ)⁻¹ * U d) ≤
      (4 * (1 + Real.log (T : ℝ))) *
        ∑ d ∈ Finset.Ioc 0 T, U d / d.totient := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left
    (sum_multiples_inv_totient_le T d 1 (Finset.mem_Ioc.mp hd).1 (by norm_num)) (hU d)
  simpa only [one_dvd, Finset.filter_true, Nat.totient_one, Nat.cast_one,
    inv_one, mul_one, Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

end Erdos964
