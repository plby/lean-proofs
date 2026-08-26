import ErdosProblems.Erdos4.SelbergCoefficients

/-!
# Möbius inversion over bounded multiples

The square-majorant coefficients use the upper divisibility transform rather
than the usual sum over divisors. This file proves that finite transform
directly, with the cutoff retained in every sum.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos4.UpperMobiusInversion

open SelbergCoefficients

theorem sum_mu_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, mu d) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, mu] using h

theorem sum_interval_divisibility_mu {D r t : ℕ}
    (hr : r ∈ Finset.Icc 1 D) (ht : t ∈ Finset.Icc 1 D) :
    (∑ d ∈ Finset.Icc 1 D, if r ∣ d ∧ d ∣ t then mu (t / d) else 0) =
      if r = t then 1 else 0 := by
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  have htpos : 0 < t := (Finset.mem_Icc.mp ht).1
  by_cases hrt : r ∣ t
  · have hqpos : 0 < t / r := Nat.div_pos (Nat.le_of_dvd htpos hrt) hrpos
    have hsum : (∑ d ∈ Finset.Icc 1 D, if r ∣ d ∧ d ∣ t then mu (t / d) else 0) =
        ∑ u ∈ (t / r).divisors, mu ((t / r) / u) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_bij
        (fun (d : ℕ) (_hd : d ∈ (Finset.Icc 1 D).filter (fun d => r ∣ d ∧ d ∣ t)) => d / r)
      · intro d hd
        have hdd := (Finset.mem_filter.mp hd).2
        exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_div hdd.1 hdd.2, hqpos.ne'⟩
      · intro d hd e he heq
        have hrd := (Finset.mem_filter.mp hd).2.1
        have hre := (Finset.mem_filter.mp he).2.1
        calc
          d = r * (d / r) := (Nat.mul_div_cancel' hrd).symm
          _ = r * (e / r) := congrArg (fun a => r * a) heq
          _ = e := Nat.mul_div_cancel' hre
      · intro u hu
        have hudvd := Nat.dvd_of_mem_divisors hu
        have hupos := Nat.pos_of_mem_divisors hu
        have hrdvd : r * u ∣ t := by
          have hh := Nat.mul_dvd_mul_left r hudvd
          rwa [Nat.mul_div_cancel' hrt] at hh
        have hru : r * u ∈ Finset.Icc 1 D := Finset.mem_Icc.mpr
          ⟨Nat.mul_pos hrpos hupos, (Nat.le_of_dvd htpos hrdvd).trans (Finset.mem_Icc.mp ht).2⟩
        refine ⟨r * u, Finset.mem_filter.mpr ⟨hru, dvd_mul_right r u, hrdvd⟩, ?_⟩
        exact Nat.mul_div_cancel_left u hrpos
      · intro d hd
        have hrd := (Finset.mem_filter.mp hd).2.1
        rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hrd]
    rw [hsum, Nat.sum_div_divisors, sum_mu_divisors]
    have hiff : t / r = 1 ↔ r = t := by
      constructor
      · intro heq
        have hh := Nat.mul_div_cancel' hrt
        rw [heq, mul_one] at hh
        exact hh
      · intro heq
        subst t
        exact Nat.div_self hrpos
    simp only [hiff]
  · have hne : r ≠ t := fun heq => hrt (heq ▸ dvd_refl t)
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro d _hd
    have hh : ¬ (r ∣ d ∧ d ∣ t) := fun h => hrt (dvd_trans h.1 h.2)
    rw [if_neg hh]

/-- The upper Möbius transform is the inverse of summing over bounded
multiples. -/
theorem upper_inversion (D : ℕ) (y : ℕ → ℝ) {r : ℕ} (hr : r ∈ Finset.Icc 1 D) :
    (∑ d ∈ Finset.Icc 1 D, if r ∣ d then
      (∑ t ∈ Finset.Icc 1 D, if d ∣ t then mu (t / d) * y t else 0) else 0) = y r := by
  have hexpand : ∀ d,
      (if r ∣ d then (∑ t ∈ Finset.Icc 1 D, if d ∣ t then mu (t / d) * y t else 0) else 0) =
      ∑ t ∈ Finset.Icc 1 D, (if r ∣ d ∧ d ∣ t then mu (t / d) else 0) * y t := by
    intro d
    by_cases hrd : r ∣ d
    · simp only [hrd, true_and, ↓reduceIte, ite_mul, zero_mul]
    · simp only [hrd, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  have hterm : ∀ t ∈ Finset.Icc 1 D,
      (∑ d ∈ Finset.Icc 1 D, (if r ∣ d ∧ d ∣ t then mu (t / d) else 0) * y t) =
      (if r = t then 1 else 0) * y t := by
    intro t ht
    rw [← Finset.sum_mul, sum_interval_divisibility_mu hr ht]
  rw [Finset.sum_congr rfl hterm]
  simp [ite_mul, hr]

/-- The selected Selberg coefficients have the prescribed upper-divisor
transform exactly, not merely asymptotically. -/
theorem coefficient_transform {D r : ℕ} (hD : 1 ≤ D) (hr : r ∈ Finset.Icc 1 D) :
    (∑ d ∈ Finset.Icc 1 D, if r ∣ d then coefficient D d / (d : ℝ) else 0) =
      mu r / ((Nat.totient r : ℝ) * harmonicMass D) := by
  have hH := harmonicMass_pos hD
  have hquot : ∀ d ∈ Finset.Icc 1 D,
      coefficient D d / (d : ℝ) = (1 / harmonicMass D) *
        ∑ t ∈ Finset.Icc 1 D, if d ∣ t then mu (t / d) * (mu t / (Nat.totient t : ℝ)) else 0 := by
    intro d hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    unfold coefficient
    simp_rw [mul_div_assoc]
    field_simp
  calc
    (∑ d ∈ Finset.Icc 1 D, if r ∣ d then coefficient D d / (d : ℝ) else 0) =
        (1 / harmonicMass D) * ∑ d ∈ Finset.Icc 1 D, if r ∣ d then
          (∑ t ∈ Finset.Icc 1 D, if d ∣ t then mu (t / d) * (mu t / (Nat.totient t : ℝ)) else 0)
          else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hrd : r ∣ d
      · simp only [if_pos hrd, hquot d hd]
      · simp only [if_neg hrd, mul_zero]
    _ = mu r / ((Nat.totient r : ℝ) * harmonicMass D) := by
      rw [upper_inversion D (fun t => mu t / (Nat.totient t : ℝ)) hr]
      ring

end Erdos4.UpperMobiusInversion
