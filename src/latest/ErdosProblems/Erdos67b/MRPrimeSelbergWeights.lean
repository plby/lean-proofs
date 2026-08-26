import ErdosProblems.Erdos896.PNT.Mathlib.NumberTheory.Sieve.SelbergBounds

/-!
# Optimized reciprocal-density Selberg coefficients for prime kernels

This specializes the existing proved Selberg optimization. The sieve is
the actual unit-weight counting problem through `D^2`; its coefficients
have cutoff `D` and a main quadratic cost at most `1 / log D`.
-/

open scoped BigOperators ArithmeticFunction.zeta

namespace Erdos67b

noncomputable section

theorem mrReciprocalSieveDensity_apply (n : ℕ) :
    ((ζ : ArithmeticFunction ℝ).pdiv .id) n = 1 / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hn, Nat.cast_one, ArithmeticFunction.id_apply]

def mrPrimeSelbergSieve (D : ℕ) (hD : 1 ≤ D) : SelbergSieve where
  support := Finset.Icc 1 (D ^ 2)
  prodPrimes := primorial (D ^ 2)
  prodPrimes_squarefree := squarefree_primorial _
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := (D : ℝ) ^ 2
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := ArithmeticFunction.isMultiplicative_zeta.natCast.pdiv
    ArithmeticFunction.isMultiplicative_id.natCast
  nu_pos_of_prime := by
    intro p hp _
    rw [mrReciprocalSieveDensity_apply]
    exact div_pos zero_lt_one (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    rw [mrReciprocalSieveDensity_apply]
    exact (div_lt_one (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt)
  level := (D : ℝ) ^ 2
  one_le_level := one_le_pow₀ (by exact_mod_cast hD)

def mrPrimeSelbergCoefficient (D : ℕ) (hD : 1 ≤ D) (d : ℕ) : ℝ :=
  (mrPrimeSelbergSieve D hD).selbergWeights d

def mrPrimeSelbergMass (D : ℕ) (hD : 1 ≤ D) : ℝ :=
  (mrPrimeSelbergSieve D hD).selbergBoundingSum

theorem mrPrimeSelbergCoefficient_one (D : ℕ) (hD : 1 ≤ D) :
    mrPrimeSelbergCoefficient D hD 1 = 1 :=
  (mrPrimeSelbergSieve D hD).weight_one_of_selberg

theorem mrAbs_primeSelbergCoefficient_le_one (D : ℕ) (hD : 1 ≤ D) (d : ℕ) :
    |mrPrimeSelbergCoefficient D hD d| ≤ 1 :=
  (mrPrimeSelbergSieve D hD).selberg_bound_weights d

theorem mrPrimeSelbergCoefficient_eq_zero_of_not_dvd
    (D : ℕ) (hD : 1 ≤ D) {d : ℕ} (hd : ¬ d ∣ primorial (D ^ 2)) :
    mrPrimeSelbergCoefficient D hD d = 0 :=
  (mrPrimeSelbergSieve D hD).selbergWeights_eq_zero_of_not_dvd hd

theorem mrPrimeSelbergCoefficient_eq_zero_of_gt
    (D : ℕ) (hD : 1 ≤ D) {d : ℕ} (hd : D < d) :
    mrPrimeSelbergCoefficient D hD d = 0 := by
  apply (mrPrimeSelbergSieve D hD).selbergWeights_eq_zero
  change ¬ (d : ℝ) ^ 2 ≤ (D : ℝ) ^ 2
  have hlt : (D : ℝ) < d := by exact_mod_cast hd
  have hnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  nlinarith

theorem mrPrimeSelbergMass_pos (D : ℕ) (hD : 1 ≤ D) :
    0 < mrPrimeSelbergMass D hD := (mrPrimeSelbergSieve D hD).selbergBoundingSum_pos

theorem mrPrimeSelbergMass_ge_log (D : ℕ) (hD : 1 ≤ D) :
    Real.log (D : ℝ) ≤ mrPrimeSelbergMass D hD := by
  have hh := Sieve.boundingSum_ge_log (mrPrimeSelbergSieve D hD) rfl (by
    intro p hp hpD
    apply hp.dvd_primorial_iff.2
    change (p : ℝ) ≤ (D : ℝ) ^ 2 at hpD
    exact_mod_cast hpD)
  change Real.log ((D : ℝ) ^ 2) / 2 ≤ mrPrimeSelbergMass D hD at hh
  simpa only [Real.log_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    using hh

theorem mrPrimeSelbergMass_inv_le (D : ℕ) (hD : 2 ≤ D) :
    (mrPrimeSelbergMass D (by omega))⁻¹ ≤ 1 / Real.log (D : ℝ) := by
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  simpa only [one_div] using inv_anti₀ hlog (mrPrimeSelbergMass_ge_log D (by omega))

theorem mrPrimeSelberg_sum_eq_Icc (D : ℕ) (hD : 1 ≤ D)
    (F : ℕ → ℝ) (hF : ∀ d, mrPrimeSelbergCoefficient D hD d = 0 → F d = 0) :
    (∑ d ∈ (primorial (D ^ 2)).divisors, F d) = ∑ d ∈ Finset.Icc 1 D, F d := by
  classical
  let S := (primorial (D ^ 2)).divisors ∩ Finset.Icc 1 D
  calc
    _ = ∑ d ∈ S, F d := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro d hd hnot
      have hdpos := Nat.pos_of_mem_divisors hd
      have hdD : D < d := by
        have hnotIcc : d ∉ Finset.Icc 1 D := by
          intro hin
          exact hnot (Finset.mem_inter.mpr ⟨hd, hin⟩)
        simp only [Finset.mem_Icc] at hnotIcc
        omega
      exact hF d (mrPrimeSelbergCoefficient_eq_zero_of_gt D hD hdD)
    _ = ∑ d ∈ Finset.Icc 1 D, F d := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro d hd hnot
      apply hF d
      apply mrPrimeSelbergCoefficient_eq_zero_of_not_dvd
      intro hdvd
      exact hnot (Finset.mem_inter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdvd, primorial_ne_zero _⟩, hd⟩)

theorem mrPrimeSelberg_quadratic_eq_mass_inv (D : ℕ) (hD : 1 ≤ D) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e /
        (Nat.lcm d e : ℝ)) = (mrPrimeSelbergMass D hD)⁻¹ := by
  let s := mrPrimeSelbergSieve D hD
  let w := mrPrimeSelbergCoefficient D hD
  have hnu (n : ℕ) : s.nu n = 1 / (n : ℝ) := mrReciprocalSieveDensity_apply n
  have hfull : (∑ d ∈ (primorial (D ^ 2)).divisors,
      ∑ e ∈ (primorial (D ^ 2)).divisors, w d * w e / (Nat.lcm d e : ℝ)) =
        (mrPrimeSelbergMass D hD)⁻¹ := by
    have hm := s.selberg_bound_simple_mainSum
    change BoundingSieve.mainSum (s := s.toBoundingSieve) (SelbergSieve.lambdaSquared w) =
      (mrPrimeSelbergMass D hD)⁻¹ at hm
    rw [SelbergSieve.lambdaSquared_mainSum_eq_quad_form] at hm
    apply Eq.trans ?_ hm
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e _he
    have hgnz : s.nu (Nat.gcd d e) ≠ 0 :=
      BoundingSieve.nu_ne_zero (s := s.toBoundingSieve)
        ((Nat.gcd_dvd_left d e).trans (Nat.dvd_of_mem_divisors hd))
    have hlcm := s.nu_mult.map_lcm hgnz
    calc
      _ = w d * w e * s.nu (Nat.lcm d e) := by rw [hnu]; ring
      _ = w d * w e * (s.nu d * s.nu e / s.nu (Nat.gcd d e)) := by rw [hlcm]
      _ = _ := by rw [div_eq_mul_inv]; ring
  have houter := mrPrimeSelberg_sum_eq_Icc D hD
    (fun d ↦ ∑ e ∈ (primorial (D ^ 2)).divisors, w d * w e / (Nat.lcm d e : ℝ))
    (by intro d hd; simp only [w, hd, zero_mul, zero_div, Finset.sum_const_zero])
  rw [houter] at hfull
  apply Eq.trans ?_ hfull
  apply Finset.sum_congr rfl
  intro d _hd
  exact (mrPrimeSelberg_sum_eq_Icc D hD
    (fun e ↦ w d * w e / (Nat.lcm d e : ℝ))
    (by intro e he; simp only [w, he, mul_zero, zero_div])).symm

theorem mrPrimeSelberg_quadratic_le_log_inv (D : ℕ) (hD : 2 ≤ D) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      mrPrimeSelbergCoefficient D (by omega) d * mrPrimeSelbergCoefficient D (by omega) e /
        (Nat.lcm d e : ℝ)) ≤ 1 / Real.log (D : ℝ) := by
  rw [mrPrimeSelberg_quadratic_eq_mass_inv]
  exact mrPrimeSelbergMass_inv_le D hD

end

end Erdos67b
