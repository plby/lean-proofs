/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.FullShiftedPrimeMass

/-! # A harmonic first moment for large prime divisors of the totient -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem prime_sq_dvd_or_primeFactor_pred_of_dvd_totient
    {p n : ℕ} (hp : p.Prime) (hpφ : p ∣ Nat.totient n) :
    p ^ 2 ∣ n ∨ ∃ q ∈ n.primeFactors, p ∣ q - 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [Nat.totient_eq_div_primeFactors_mul] at hpφ
  rcases hp.dvd_mul.mp hpφ with hquot | hprod
  · have hquotdiv : n / ∏ q ∈ n.primeFactors, q ∣ n :=
      Nat.div_dvd_of_dvd n.prod_primeFactors_dvd
    have hpn := hquot.trans hquotdiv
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩
    have hprad : p ∣ ∏ q ∈ n.primeFactors, q := Finset.dvd_prod_of_mem id hpmem
    have hmul := mul_dvd_mul hquot hprad
    rw [Nat.div_mul_cancel n.prod_primeFactors_dvd] at hmul
    exact Or.inl (by simpa only [pow_two] using hmul)
  · exact Or.inr (hp.prime.dvd_finsetProd_iff (fun q : ℕ ↦ q - 1) |>.mp hprod)

theorem sum_inv_totient_divisible_Icc_le {N p : ℕ} (hp : p.Prime) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n ↦ p ∣ Nat.totient n), (1 : ℝ) / n) ≤
      (harmonic N : ℝ) * ((1 : ℝ) / (p : ℝ) ^ 2 + packetPrimeMean (b1PrimePacket N p)) := by
  have hsub : (Finset.Icc 1 N).filter (fun n ↦ p ∣ Nat.totient n) ⊆
      (Finset.Icc 1 N).filter (p ^ 2 ∣ ·) ∪
        (b1PrimePacket N p).biUnion (fun q ↦ (Finset.Icc 1 N).filter (q ∣ ·)) := by
    intro n hn
    obtain ⟨hn, hpφ⟩ := Finset.mem_filter.mp hn
    rcases prime_sq_dvd_or_primeFactor_pred_of_dvd_totient hp hpφ with hsq | ⟨q, hq, hpq⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, hsq⟩)
    · have hqN := (Nat.le_of_mem_primeFactors hq).trans (Finset.mem_Icc.mp hn).2
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q,
        mem_b1PrimePacket_iff.mpr ⟨hqN, Nat.prime_of_mem_primeFactors hq, hpq⟩,
        Finset.mem_filter.mpr ⟨hn, Nat.dvd_of_mem_primeFactors hq⟩⟩)
  have hdiv (d : ℕ) (hd : 0 < d) :
      (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), (1 : ℝ) / n) ≤ (harmonic N : ℝ) / d := by
    rw [sum_inv_filter_Icc_dvd_eq_harmonic_div hd]
    exact div_le_div_of_nonneg_right (harmonic_cast_mono (Nat.div_le_self N d)) (by positivity)
  calc
    _ ≤ (∑ n ∈ (Finset.Icc 1 N).filter (p ^ 2 ∣ ·), (1 : ℝ) / n) +
        (∑ n ∈ (b1PrimePacket N p).biUnion (fun q ↦ (Finset.Icc 1 N).filter (q ∣ ·)), (1 : ℝ) / n) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot ↦ by positivity)).trans
        (sum_union_le_add_sum (fun n hn ↦ by positivity))
    _ ≤ (harmonic N : ℝ) / (p ^ 2 : ℕ) +
        ∑ q ∈ b1PrimePacket N p, ∑ n ∈ (Finset.Icc 1 N).filter (q ∣ ·), (1 : ℝ) / n :=
      add_le_add (hdiv _ (pow_pos hp.pos 2))
        (sum_biUnion_le_sum _ _ _ (fun q hq n hn ↦ by positivity))
    _ ≤ (harmonic N : ℝ) / (p ^ 2 : ℕ) +
        ∑ q ∈ b1PrimePacket N p, (harmonic N : ℝ) / q :=
      add_le_add le_rfl (Finset.sum_le_sum fun q hq ↦ hdiv q (mem_b1PrimePacket_iff.mp hq).2.1.pos)
    _ = _ := by
      simp only [packetPrimeMean, mul_add, Finset.mul_sum, Nat.cast_pow]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro q hq
        ring

noncomputable def totientPrimeTailMoment (N z : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (∑ p ∈ primeFactorsAbove (Nat.totient n) z, (1 : ℝ) / p) / n

theorem totientPrimeTailMoment_eq_incidence (N z : ℕ) :
    totientPrimeTailMoment N z =
      ∑ p ∈ (Nat.primesLE N).filter (z < ·), (1 : ℝ) / p *
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n ↦ p ∣ Nat.totient n), (1 : ℝ) / n := by
  have hset {n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
      primeFactorsAbove (Nat.totient n) z =
        ((Nat.primesLE N).filter (z < ·)).filter (· ∣ Nat.totient n) := by
    ext p
    simp only [mem_primeFactorsAbove_iff, Nat.mem_primeFactors, Finset.mem_filter, Nat.mem_primesLE]
    have hφpos := Nat.totient_pos.mpr (Finset.mem_Icc.mp hn).1
    constructor
    · rintro ⟨⟨hp, hdiv, hne⟩, hzp⟩
      exact ⟨⟨⟨(Nat.le_of_dvd hφpos hdiv).trans ((Nat.totient_le n).trans (Finset.mem_Icc.mp hn).2), hp⟩,
        hzp⟩, hdiv⟩
    · rintro ⟨⟨⟨hpN, hp⟩, hzp⟩, hdiv⟩
      exact ⟨⟨hp, hdiv, hφpos.ne'⟩, hzp⟩
  unfold totientPrimeTailMoment
  calc
    _ = ∑ n ∈ Finset.Icc 1 N,
        ∑ p ∈ (Nat.primesLE N).filter (z < ·),
          if p ∣ Nat.totient n then ((1 : ℝ) / p) * (1 / n) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hset hn, Finset.sum_div, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum, Finset.sum_filter]

theorem exists_totientPrimeTailMoment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N z : ℕ, 2 ≤ z →
      totientPrimeTailMoment N z ≤
        C * (harmonic N : ℝ) * (b1DoubleLog N + 2 : ℝ) /
          ((z : ℝ) * Real.log (z : ℝ)) := by
  obtain ⟨C, hC, hpackets⟩ := exists_primePacket_tail_bound
  obtain ⟨D, hD, htail⟩ := exists_sum_inv_sq_primesAbove_le
  refine ⟨C + D, by positivity, ?_⟩
  intro N z hz
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun n hn ↦ by positivity
  have hden : 0 < (z : ℝ) * Real.log (z : ℝ) :=
    mul_pos (by exact_mod_cast (show 0 < z by omega)) (Real.log_pos (by exact_mod_cast (show 1 < z by omega)))
  have hcube : (∑ p ∈ (Nat.primesLE N).filter (z < ·), ((1 : ℝ) / p) * (1 / (p : ℝ) ^ 2)) ≤
      D / ((z : ℝ) * Real.log (z : ℝ)) := by
    refine (Finset.sum_le_sum ?_).trans (htail N z hz)
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.one_le
    have hfrac : (1 : ℝ) / p ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < p)).mpr hp1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2)
  rw [totientPrimeTailMoment_eq_incidence]
  calc
    _ ≤ ∑ p ∈ (Nat.primesLE N).filter (z < ·), (1 : ℝ) / p *
        ((harmonic N : ℝ) * ((1 : ℝ) / (p : ℝ) ^ 2 + packetPrimeMean (b1PrimePacket N p))) := by
      exact Finset.sum_le_sum fun p hp ↦ mul_le_mul_of_nonneg_left
        (sum_inv_totient_divisible_Icc_le (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2) (by positivity)
    _ = (harmonic N : ℝ) *
        ((∑ p ∈ (Nat.primesLE N).filter (z < ·), ((1 : ℝ) / p) * (1 / (p : ℝ) ^ 2)) +
        ∑ p ∈ (Nat.primesLE N).filter (z < ·), packetPrimeMean (b1PrimePacket N p) / p) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (harmonic N : ℝ) * (D / ((z : ℝ) * Real.log (z : ℝ)) +
        C * (b1DoubleLog N + 2 : ℝ) / ((z : ℝ) * Real.log (z : ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hcube (hpackets N N z hz)) hH
    _ ≤ (C + D) * (harmonic N : ℝ) * (b1DoubleLog N + 2 : ℝ) /
        ((z : ℝ) * Real.log (z : ℝ)) := by
      rw [← add_div]
      simp only [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hden.le
      have hZ := Nat.cast_nonneg (α := ℝ) (b1DoubleLog N)
      have hZ1 : (1 : ℝ) ≤ b1DoubleLog N + 2 := by linarith only [hZ]
      have hprod := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hZ1 hD.le) hH
      nlinarith only [hprod]

theorem harmonic_pow_le_mul_harmonic {N : ℕ} (hN : 1 ≤ N) (a : ℕ) :
    (harmonic (N ^ a) : ℝ) ≤ (a + 1 : ℝ) * (harmonic N : ℝ) := by
  have hH1 : (1 : ℝ) ≤ harmonic N := by
    simpa using harmonic_cast_mono hN
  have hlog : Real.log (N : ℝ) ≤ harmonic N :=
    (Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast Nat.le_succ N)).trans
      (log_add_one_le_harmonic N)
  have htop := harmonic_le_one_add_log (N ^ a)
  rw [Nat.cast_pow, Real.log_pow] at htop
  have ha := Nat.cast_nonneg (α := ℝ) a
  nlinarith only [hH1, hlog, htop, ha]

theorem eventually_totientPrimeTailMoment_power_small
    {ε : ℝ} (hε : 0 < ε) (a : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      totientPrimeTailMoment (N ^ a) (b1DoubleLog N) ≤ ε * Real.log (N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_totientPrimeTailMoment_bound
  filter_upwards [eventually_harmonic_doubleLog_pow_div_small
      (show 0 ≤ C * (a + 1 : ℝ) by positivity) hε a,
    tendsto_b1DoubleLog_atTop.eventually_ge_atTop 2, eventually_ge_atTop 1]
    with N hsmall hZ hN
  have hden : 0 ≤ (b1DoubleLog N : ℝ) * Real.log (b1DoubleLog N : ℝ) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ b1DoubleLog N by omega)))
  calc
    _ ≤ C * (harmonic (N ^ a) : ℝ) * (b1DoubleLog (N ^ a) + 2 : ℝ) /
        ((b1DoubleLog N : ℝ) * Real.log (b1DoubleLog N : ℝ)) := hbound _ _ hZ
    _ ≤ C * ((a + 1 : ℝ) * (harmonic N : ℝ)) * (b1DoubleLog (N ^ a) + 2 : ℝ) /
        ((b1DoubleLog N : ℝ) * Real.log (b1DoubleLog N : ℝ)) := by
      gcongr
      exact harmonic_pow_le_mul_harmonic hN a
    _ = (C * (a + 1 : ℝ)) * (harmonic N : ℝ) * (b1DoubleLog (N ^ a) + 2 : ℝ) /
        ((b1DoubleLog N : ℝ) * Real.log (b1DoubleLog N : ℝ)) := by ring
    _ ≤ _ := hsmall

noncomputable def totientTailBadOddCofactors (N : ℕ) : Finset ℕ :=
  (oddRawCofactors N).filter fun m ↦
    1 < ∑ p ∈ primeFactorsAbove (Nat.totient m) (b1DoubleLog N), (1 : ℝ) / p

theorem sum_inv_totientTailBadOddCofactors_le_moment (N : ℕ) :
    (∑ m ∈ totientTailBadOddCofactors N, (1 : ℝ) / m) ≤
      totientPrimeTailMoment (N ^ 28) (b1DoubleLog N) := by
  calc
    _ ≤ ∑ m ∈ totientTailBadOddCofactors N,
        (∑ p ∈ primeFactorsAbove (Nat.totient m) (b1DoubleLog N), (1 : ℝ) / p) / m := by
      apply Finset.sum_le_sum
      intro m hm
      exact div_le_div_of_nonneg_right (Finset.mem_filter.mp hm).2.le (by positivity)
    _ ≤ ∑ m ∈ Finset.Icc 1 (N ^ 28),
        (∑ p ∈ primeFactorsAbove (Nat.totient m) (b1DoubleLog N), (1 : ℝ) / p) / m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        have hmraw := (Finset.mem_filter.mp hm).1
        exact Finset.mem_Icc.mpr ⟨oddRawCofactors_pos hmraw, oddRawCofactors_le_pow_twenty_eight hmraw⟩
      · intro m hm hnot
        positivity
    _ = _ := rfl

theorem eventually_totientTailBadOddCofactors_mass_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ totientTailBadOddCofactors N, (1 : ℝ) / m) ≤ ε * Real.log (N : ℝ) := by
  filter_upwards [eventually_totientPrimeTailMoment_power_small hε 28] with N hN
  exact (sum_inv_totientTailBadOddCofactors_le_moment N).trans hN

noncomputable def totientB1B5Cofactors (N S : ℕ) (C : ℝ) : Finset ℕ :=
  (b1B5Cofactors N S C).filter fun m ↦
    (∑ p ∈ primeFactorsAbove (Nat.totient m) (b1DoubleLog N), (1 : ℝ) / p) ≤ 1

theorem totientB1B5Cofactors_subset (N S : ℕ) (C : ℝ) :
    totientB1B5Cofactors N S C ⊆ b1B5Cofactors N S C := Finset.filter_subset _ _

theorem exists_eventually_sum_inv_totientB1B5Cofactors_lower :
    ∃ S : ℕ, ∃ C c : ℝ, 101 ≤ S ∧ 0 < C ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        c * Real.log (N : ℝ) ≤ ∑ m ∈ totientB1B5Cofactors N S C, (1 : ℝ) / m := by
  obtain ⟨S, C, c, hS, hC, hc, hmass⟩ := exists_eventually_sum_inv_b1B5Cofactors_lower
  refine ⟨S, C, c / 2, hS, hC, by positivity, ?_⟩
  filter_upwards [hmass, eventually_totientTailBadOddCofactors_mass_small
    (ε := c / 2) (by positivity)] with N hmassN hbad
  let P : ℕ → Prop := fun m ↦
    (∑ p ∈ primeFactorsAbove (Nat.totient m) (b1DoubleLog N), (1 : ℝ) / p) ≤ 1
  have hsplit := Finset.sum_filter_add_sum_filter_not (b1B5Cofactors N S C) P (fun m ↦ (1 : ℝ) / m)
  have hsub : (b1B5Cofactors N S C).filter (fun m ↦ ¬ P m) ⊆ totientTailBadOddCofactors N := by
    intro m hm
    exact Finset.mem_filter.mpr ⟨gcdSmoothB1Cofactors_subset_oddRaw N
      (b1B5Cofactors_subset_gcd N S C (Finset.mem_filter.mp hm).1),
        lt_of_not_ge (Finset.mem_filter.mp hm).2⟩
  have hbad' := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun m : ℕ ↦ (1 : ℝ) / m) (fun m hm hnot ↦ by positivity)
  change (∑ m ∈ totientB1B5Cofactors N S C, (1 : ℝ) / m) + _ = _ at hsplit
  linarith only [hmassN, hbad, hbad', hsplit]

#print axioms exists_eventually_sum_inv_totientB1B5Cofactors_lower

end Erdos822
