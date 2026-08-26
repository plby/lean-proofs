import ErdosProblems.Erdos4.UpperMobiusInversion

/-!
# Exact optimization of the elementary square majorant

The lcm quadratic form diagonalizes using the totient divisor identity.
Upper Möbius inversion then evaluates the concrete coefficients exactly.
-/

open scoped BigOperators

namespace Erdos4.SelbergOptimization

open SelbergCoefficients SieveMajorant UpperMobiusInversion

theorem inv_lcm_eq_gcd_div (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (Nat.lcm d e : ℝ)⁻¹ = (Nat.gcd d e : ℝ) / ((d : ℝ) * e) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hlcm : (0 : ℝ) < Nat.lcm d e := by exact_mod_cast Nat.lcm_pos hd he
  have hmul : (Nat.gcd d e : ℝ) * Nat.lcm d e = (d : ℝ) * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  field_simp
  nlinarith

theorem gcd_eq_sum_common_totient {D d e : ℕ}
    (hd : d ∈ Finset.Icc 1 D) (_he : e ∈ Finset.Icc 1 D) :
    (Nat.gcd d e : ℝ) = ∑ r ∈ Finset.Icc 1 D,
      if r ∣ d ∧ r ∣ e then (Nat.totient r : ℝ) else 0 := by
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hgpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hdpos
  have hfilter : (Finset.Icc 1 D).filter (fun r => r ∣ d ∧ r ∣ e) = (Nat.gcd d e).divisors := by
    ext r
    constructor
    · intro hr
      have hrd := (Finset.mem_filter.mp hr).2
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hrd.1 hrd.2, hgpos.ne'⟩
    · intro hr
      have hrd := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hr)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hr, ?_⟩, hrd⟩
      exact (Nat.le_of_dvd hdpos hrd.1).trans (Finset.mem_Icc.mp hd).2
  rw [← Finset.sum_filter, hfilter]
  exact_mod_cast (Nat.sum_totient (Nat.gcd d e)).symm

theorem pair_eq_totient_sum {D d e : ℕ}
    (hd : d ∈ Finset.Icc 1 D) (he : e ∈ Finset.Icc 1 D) (lambda : ℕ → ℝ) :
    lambda d * lambda e / (Nat.lcm d e : ℝ) =
      ∑ r ∈ Finset.Icc 1 D, (Nat.totient r : ℝ) *
        (if r ∣ d then lambda d / (d : ℝ) else 0) *
        (if r ∣ e then lambda e / (e : ℝ) else 0) := by
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hepos : 0 < e := (Finset.mem_Icc.mp he).1
  calc
    lambda d * lambda e / (Nat.lcm d e : ℝ) =
        (lambda d / (d : ℝ)) * (lambda e / (e : ℝ)) * (Nat.gcd d e : ℝ) := by
      rw [div_eq_mul_inv, inv_lcm_eq_gcd_div d e hdpos hepos]
      ring
    _ = (lambda d / (d : ℝ)) * (lambda e / (e : ℝ)) *
        ∑ r ∈ Finset.Icc 1 D, if r ∣ d ∧ r ∣ e then (Nat.totient r : ℝ) else 0 := by
      rw [gcd_eq_sum_common_totient hd he]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hrd : r ∣ d
      · by_cases hre : r ∣ e
        · simp only [hrd, hre, and_self, ↓reduceIte]
          ring
        · simp [hrd, hre]
      · simp [hrd]

theorem sum_rank_one_forms {α : Type*} (S : Finset α) (w : α → ℝ) (b : α → α → ℝ) :
    (∑ d ∈ S, ∑ e ∈ S, ∑ r ∈ S, w r * b r d * b r e) =
      ∑ r ∈ S, w r * (∑ d ∈ S, b r d) ^ 2 := by
  have hswap : (∑ d ∈ S, ∑ e ∈ S, ∑ r ∈ S, w r * b r d * b r e) =
      ∑ d ∈ S, ∑ r ∈ S, ∑ e ∈ S, w r * b r d * b r e := by
    exact Finset.sum_congr rfl (fun d _hd => Finset.sum_comm)
  rw [hswap, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  apply Finset.sum_congr rfl
  intro e _he
  ring

theorem mainTerm_eq_diagonal (D : ℕ) (lambda : ℕ → ℝ) :
    mainTerm D lambda = ∑ r ∈ Finset.Icc 1 D, (Nat.totient r : ℝ) *
      (∑ d ∈ Finset.Icc 1 D, if r ∣ d then lambda d / (d : ℝ) else 0) ^ 2 := by
  unfold mainTerm
  calc
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, lambda d * lambda e / (Nat.lcm d e : ℝ)) =
        ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, ∑ r ∈ Finset.Icc 1 D,
          (Nat.totient r : ℝ) * (if r ∣ d then lambda d / (d : ℝ) else 0) *
          (if r ∣ e then lambda e / (e : ℝ) else 0) :=
      Finset.sum_congr rfl (fun d hd =>
        Finset.sum_congr rfl (fun e he => pair_eq_totient_sum hd he lambda))
    _ = _ := sum_rank_one_forms _ _ _

/-- The concrete main term is the reciprocal of its harmonic normalizer. -/
theorem mainTerm_coefficient {D : ℕ} (hD : 1 ≤ D) :
    mainTerm D (coefficient D) = 1 / harmonicMass D := by
  have hH := harmonicMass_pos hD
  rw [mainTerm_eq_diagonal]
  have hterm : ∀ r ∈ Finset.Icc 1 D,
      (Nat.totient r : ℝ) *
        (∑ d ∈ Finset.Icc 1 D, if r ∣ d then coefficient D d / (d : ℝ) else 0) ^ 2 =
          (mu r ^ 2 / (Nat.totient r : ℝ)) / harmonicMass D ^ 2 := by
    intro r hr
    have hphi : (0 : ℝ) < Nat.totient r := by
      exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hr).1
    rw [coefficient_transform hD hr]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  change harmonicMass D / harmonicMass D ^ 2 = 1 / harmonicMass D
  field_simp

/-- An unconditional finite Selberg majorant with explicit endpoint loss. -/
theorem sum_weight_coefficient_le {D : ℕ} (hD : 1 ≤ D) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, weight D (coefficient D) n) ≤
      (N : ℝ) / harmonicMass D + (D : ℝ) ^ 4 := by
  have hweight := sum_weight_le D N (coefficient D)
  rw [mainTerm_coefficient hD] at hweight
  have habs := sum_abs_coefficient_le hD
  have hnonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 D, |coefficient D d| :=
    Finset.sum_nonneg (fun d _hd => abs_nonneg _)
  have hpow : (∑ d ∈ Finset.Icc 1 D, |coefficient D d|) ^ 2 ≤ (D : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((D : ℝ) ^ 2 - ∑ d ∈ Finset.Icc 1 D, |coefficient D d|)]
  simp only [mul_one_div] at hweight
  exact hweight.trans (add_le_add (le_refl _) hpow)

end Erdos4.SelbergOptimization
