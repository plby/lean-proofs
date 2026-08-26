/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SquarefreeSieveMass
import ErdosProblems.Erdos822.LargeCutoffSquarefreeMass

/-! # The squarefree deletion at the B1 arithmetic cutoff -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

def smallSquareBadCofactors (N y : ℕ) : Finset ℕ :=
  ((Nat.primesLE (N ^ 4)).filter (y < ·)).biUnion (squareDivisibleCoprimeOddCofactors N)

theorem sum_inv_smallSquareBadCofactors_le {N y : ℕ} {B : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ y) (hB : 0 ≤ B)
    (hbound : ∀ p : ℕ, p.Prime → p ^ 2 ≤ N ^ 21 →
      (∑ m ∈ squareDivisibleCoprimeOddCofactors N p, (1 : ℝ) / m) ≤
        (harmonic N : ℝ) * (B / (p : ℝ) ^ 2 + 1 / (N : ℝ) ^ 19)) :
    (∑ m ∈ smallSquareBadCofactors N y, (1 : ℝ) / m) ≤
      B * (harmonic N : ℝ) / y + 1 := by
  let P := (Nat.primesLE (N ^ 4)).filter (y < ·)
  have hP : P ⊆ Finset.Ioc y (N ^ 4) := by
    intro p hp
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_filter.mp hp).2,
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1⟩
  have hcard : P.card ≤ N ^ 4 := by
    have h := Finset.card_le_card hP
    rw [Nat.card_Ioc] at h
    exact h.trans (Nat.sub_le _ _)
  have htail : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (y : ℝ) := by
    simpa only [Nat.cast_pow] using sum_inv_sq_le_inv_of_subset_Ioc hy hP
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun n hn ↦ by positivity
  have herror : (harmonic N : ℝ) * ((P.card : ℝ) / (N : ℝ) ^ 19) ≤ 1 := by
    have hcardR : (P.card : ℝ) ≤ (N : ℝ) ^ 4 := by exact_mod_cast hcard
    calc
      _ ≤ (N : ℝ) * ((N : ℝ) ^ 4 / (N : ℝ) ^ 19) := by
        gcongr
        exact harmonic_le_natCast N
      _ = (N : ℝ) ^ 5 / (N : ℝ) ^ 19 := by ring
      _ ≤ 1 := by
        apply (div_le_one (by positivity : (0 : ℝ) < (N : ℝ) ^ 19)).mpr
        exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ N) (show 5 ≤ 19 by norm_num)
  calc
    _ ≤ ∑ p ∈ P, ∑ m ∈ squareDivisibleCoprimeOddCofactors N p, (1 : ℝ) / m :=
      sum_biUnion_le_sum _ _ _ (fun p hp m hm ↦ by positivity)
    _ ≤ ∑ p ∈ P, (harmonic N : ℝ) * (B / (p : ℝ) ^ 2 + 1 / (N : ℝ) ^ 19) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpN := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      apply hbound p hpprime
      calc
        p ^ 2 ≤ (N ^ 4) ^ 2 := Nat.pow_le_pow_left hpN 2
        _ = N ^ 8 := by ring
        _ ≤ N ^ 21 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ = (harmonic N : ℝ) *
        (B * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) + (P.card : ℝ) / (N : ℝ) ^ 19) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
      congr 2
      · apply Finset.sum_congr rfl
        intro p hp
        ring
      · ring
    _ ≤ (harmonic N : ℝ) * (B * (1 / (y : ℝ))) + 1 := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hB) hH) herror
    _ = _ := by ring

theorem largeSquareBadCoprimeOddCofactors_subset_split (N y : ℕ) :
    largeSquareBadCoprimeOddCofactors N y ⊆
      smallSquareBadCofactors N y ∪ largeSquareBadCoprimeOddCofactors N (N ^ 4) := by
  intro m hm
  obtain ⟨p, hp, hm⟩ := mem_largeSquareBadCoprimeOddCofactors_iff.mp hm
  have hpdata := mem_largeSquarePrimes_iff.mp hp
  by_cases hsmall : p ≤ N ^ 4
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p,
      Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hsmall, hpdata.2.2⟩, hpdata.1⟩, hm⟩)
  · exact Finset.mem_union_right _ (mem_largeSquareBadCoprimeOddCofactors_iff.mpr ⟨p,
      mem_largeSquarePrimes_iff.mpr ⟨by omega, hpdata.2.1, hpdata.2.2⟩, hm⟩)

theorem eventually_largeSquareBadCoprimeOddCofactors_b1_mass_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ largeSquareBadCoprimeOddCofactors N (b1Cutoff N), (1 : ℝ) / m) ≤
        ε * Real.log (N : ℝ) := by
  obtain ⟨B, hB, hbound⟩ := exists_eventually_squareDivisibleCofactors_sharp_bound
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hbound, eventually_reciprocalPrimeIntervalSum_four_five_upper_one,
    (tendsto_natCast_atTop_atTop.comp tendsto_b1Cutoff_atTop).eventually_ge_atTop (4 * B / ε),
    tendsto_b1Cutoff_atTop.eventually_ge_atTop 1, hlog.eventually_ge_atTop (8 / ε),
    eventually_ge_atTop 4] with N hboundN hR hylarge hy hloglarge hN
  have hR' : (∑ r ∈ middlePrimes N, (1 : ℝ) / r) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff] using hR
  have hbig : (∑ m ∈ largeSquareBadCoprimeOddCofactors N (N ^ 4), (1 : ℝ) / m) ≤ 3 :=
    (sum_inv_largeSquareBadCoprimeOddCofactors_le (by omega) (one_le_pow₀ (by omega))
      (Nat.pow_lt_pow_right (by omega : 1 < N) (show 4 < 21 by norm_num))).trans
        (largeCutoff_squarefree_error_le_three (by omega) hR')
  have hsmall := sum_inv_smallSquareBadCofactors_le (by omega : 2 ≤ N) hy hB.le hboundN
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (largeSquareBadCoprimeOddCofactors_subset_split N (b1Cutoff N))
    (f := fun m : ℕ ↦ (1 : ℝ) / m) (fun m hm hnot ↦ by positivity)
  have hunion := sum_union_le_add_sum
    (s := smallSquareBadCofactors N (b1Cutoff N))
    (t := largeSquareBadCoprimeOddCofactors N (N ^ 4))
    (f := fun m : ℕ ↦ (1 : ℝ) / m) (fun m hm ↦ by positivity)
  have hlogN : 1 ≤ Real.log (N : ℝ) := BoundedGaps.Maynard.one_le_log_natCast hN
  have hH : (harmonic N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have := harmonic_le_one_add_log N
    linarith only [this, hlogN]
  have hypos : (0 : ℝ) < b1Cutoff N := by exact_mod_cast hy
  have hcoeff : B * (harmonic N : ℝ) / b1Cutoff N ≤ ε / 2 * Real.log (N : ℝ) := by
    have h := (div_le_iff₀ hε).mp hylarge
    dsimp only [Function.comp_apply] at h
    have hBy : 2 * B / (b1Cutoff N : ℝ) ≤ ε / 2 := by
      apply (div_le_iff₀ hypos).mpr
      nlinarith only [h]
    calc
      _ ≤ B * (2 * Real.log (N : ℝ)) / b1Cutoff N := by gcongr
      _ = (2 * B / (b1Cutoff N : ℝ)) * Real.log (N : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBy (by linarith)
  have hfour := (div_le_iff₀ hε).mp hloglarge
  linarith only [hbig, hsmall, hsub, hunion, hcoeff, hfour]

noncomputable def gilCofactors (N S : ℕ) (C : ℝ) : Finset ℕ :=
  largeSquarefreeFilter (totientB1B5Cofactors N S C) (b1Cutoff N)

theorem gilCofactors_subset_totientB1B5 (N S : ℕ) (C : ℝ) :
    gilCofactors N S C ⊆ totientB1B5Cofactors N S C := largeSquarefreeFilter_subset _ _

theorem gilCofactors_subset_b1B5 (N S : ℕ) (C : ℝ) :
    gilCofactors N S C ⊆ b1B5Cofactors N S C :=
  (gilCofactors_subset_totientB1B5 N S C).trans (totientB1B5Cofactors_subset N S C)

theorem gilCofactors_subset_oddRaw (N S : ℕ) (C : ℝ) :
    gilCofactors N S C ⊆ oddRawCofactors N :=
  (gilCofactors_subset_b1B5 N S C).trans
    ((b1B5Cofactors_subset_gcd N S C).trans (gcdSmoothB1Cofactors_subset_oddRaw N))

theorem exists_eventually_sum_inv_gilCofactors_lower :
    ∃ S : ℕ, ∃ C c : ℝ, 101 ≤ S ∧ 0 < C ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        c * Real.log (N : ℝ) ≤ ∑ m ∈ gilCofactors N S C, (1 : ℝ) / m := by
  obtain ⟨S, C, c, hS, hC, hc, hmass⟩ := exists_eventually_sum_inv_totientB1B5Cofactors_lower
  refine ⟨S, C, c / 2, hS, hC, by positivity, ?_⟩
  filter_upwards [hmass, eventually_largeSquareBadCoprimeOddCofactors_b1_mass_small
    (ε := c / 2) (by positivity), eventually_ge_atTop 2] with N hmassN hbad hN
  have hrawsub : totientB1B5Cofactors N S C ⊆ oddRawCofactors N :=
    (totientB1B5Cofactors_subset N S C).trans
      ((b1B5Cofactors_subset_gcd N S C).trans (gcdSmoothB1Cofactors_subset_oddRaw N))
  have hfree : ∀ m ∈ totientB1B5Cofactors N S C, ∀ p : ℕ, p.Prime → b1Cutoff N < p →
      p ^ 2 ∣ shiftedTotient m → ¬ p ∣ m := by
    intro m hm p hp hyp hsq
    exact not_dvd_of_dvd_shiftedTotient_of_largeGcdFree
      (b1B5Cofactors_largeGcdFree (totientB1B5Cofactors_subset N S C hm)) hp hyp
      ((dvd_pow_self p (by norm_num)).trans hsq)
  have hsub := bad_largeSquarefreeFilter_subset_largeSquareBad (by omega : 1 ≤ N) hrawsub hfree
  have hbad' := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun m : ℕ ↦ (1 : ℝ) / m) (fun m hm hnot ↦ by positivity)
  have hsplit := Finset.sum_filter_add_sum_filter_not (totientB1B5Cofactors N S C)
    (fun m ↦ ∀ p : ℕ, p.Prime → b1Cutoff N < p → ¬ p ^ 2 ∣ shiftedTotient m)
    (fun m ↦ (1 : ℝ) / m)
  change (∑ m ∈ gilCofactors N S C, (1 : ℝ) / m) +
    (∑ m ∈ badLargeSquarefreeFilter (totientB1B5Cofactors N S C) (b1Cutoff N), (1 : ℝ) / m) = _ at hsplit
  linarith only [hmassN, hbad, hbad', hsplit]

theorem gilCofactors_preserving {N S m : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hm : m ∈ gilCofactors N S C) : SmoothTotientPreserving m (b1Cutoff N) :=
  b1B5Cofactors_preserving hN (gilCofactors_subset_b1B5 N S C hm)

theorem gilCofactors_largeGcdFree {N S m : ℕ} {C : ℝ}
    (hm : m ∈ gilCofactors N S C) : m ∈ largeGcdFreeOddCofactors N (b1Cutoff N) :=
  b1B5Cofactors_largeGcdFree (gilCofactors_subset_b1B5 N S C hm)

theorem gilCofactors_largeSquarefree {N S m : ℕ} {C : ℝ}
    (hm : m ∈ gilCofactors N S C) :
    ∀ p : ℕ, p.Prime → b1Cutoff N < p → ¬ p ^ 2 ∣ shiftedTotient m :=
  (mem_largeSquarefreeFilter_iff.mp hm).2

theorem gilCofactors_totientTail {N S m : ℕ} {C : ℝ}
    (hm : m ∈ gilCofactors N S C) :
    (∑ p ∈ primeFactorsAbove (Nat.totient m) (b1DoubleLog N), (1 : ℝ) / p) ≤ 1 :=
  (Finset.mem_filter.mp (gilCofactors_subset_totientB1B5 N S C hm)).2

theorem gilCofactors_smoothPart_le_natLog {N S m : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) (hm : m ∈ gilCofactors N S C) :
    smoothPart m (b1Cutoff N) ≤ Nat.log 2 N :=
  b1B5Cofactors_smoothPart_le_natLog hN hy (gilCofactors_subset_b1B5 N S C hm)

theorem eventually_gilCofactors_full_primeMass_le {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ gilCofactors N S C,
      primeDivisorReciprocalMass (shiftedTotient m) ≤ C + 2 := by
  filter_upwards [eventually_b1B5Cofactors_full_primeMass_le hS C] with N hN
  exact fun m hm ↦ hN m (gilCofactors_subset_b1B5 N S C hm)

#print axioms exists_eventually_sum_inv_gilCofactors_lower

end Erdos822
