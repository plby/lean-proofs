import ErdosProblems.Erdos380.SieveDenominator
import ErdosProblems.Erdos380.PrimeCounts
import ErdosProblems.Erdos380.MixingScale

/-!
# An elementary uniform upper bound for primes in a progression

The Fourier sieve is applied to the progression parameter.  Its denominator
is bounded by the elementary harmonic argument, so no prime-distribution
theorem in arithmetic progressions is assumed.
-/

open scoped BigOperators Function

namespace Erdos380

noncomputable def progressionSievePrimes (q Q : ℕ) : Finset ℕ :=
  (Nat.primesLE Q).filter fun p => ¬ p ∣ q

lemma mem_progressionSievePrimes {q Q p : ℕ} :
    p ∈ progressionSievePrimes q Q ↔ p.Prime ∧ p ≤ Q ∧ ¬ p ∣ q := by
  simp [progressionSievePrimes, Nat.mem_primesLE, and_assoc, and_left_comm]

noncomputable def affinePrimesAbove (q a m0 M Q : ℕ) : Finset ℕ :=
  (Finset.Ioc m0 (m0 + M)).filter fun n => (q * n + a).Prime ∧ Q < q * n + a

/-- The progression-parameter form of the sieve, retaining its exact
squarefree denominator. -/
theorem affinePrimesAbove_card_le_sieveDenominator
    (q a m0 M Q : ℕ) (hq : 0 < q) (hQ : 1 ≤ Q) (hQM : Q ^ 2 ≤ M) :
    ((affinePrimesAbove q a m0 M Q).card : ℝ) ≤
      ((M : ℝ) + M) / sieveDenominator q Q := by
  classical
  let t := progressionSievePrimes q Q
  have ht (p : t) : p.1.Prime ∧ p.1 ≤ Q ∧ ¬ p.1 ∣ q :=
    mem_progressionSievePrimes.mp p.2
  letI : ∀ p : t, NeZero p.1 := fun p => ⟨(ht p).1.ne_zero⟩
  have hcop (p : t) : q.Coprime p.1 :=
    ((ht p).1.coprime_iff_not_dvd.mpr (ht p).2.2).symm
  let c (p : t) : (ZMod p.1)ˣ := ZMod.unitOfCoprime q (hcop p)
  let root (p : t) : ZMod p.1 := -((c p)⁻¹ : (ZMod p.1)ˣ) * (a : ZMod p.1)
  let vanish (p : t) : Finset (ZMod p.1) := {root p}
  have hroot (p : t) (n : ℕ) (hn : (n : ZMod p.1) = root p) :
      p.1 ∣ q * n + a := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hc : (c p : ZMod p.1) = q := ZMod.coe_unitOfCoprime q (hcop p)
    simp only [Nat.cast_add, Nat.cast_mul, hn, root, ← hc]
    simp [← mul_assoc]
  have hsub : affinePrimesAbove q a m0 M Q ⊆ residueClassSurvivors vanish m0 M := by
    intro n hn
    obtain ⟨hnI, hnprime, hnlarge⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr ⟨hnI, ?_⟩
    intro p hnp
    have heq : (n : ZMod p.1) = root p := Finset.mem_singleton.mp hnp
    have hpdvd := hroot p n heq
    have hpEq : q * n + a = p.1 := (hnprime.dvd_iff_eq (ht p).1.ne_one).mp hpdvd
    have hpQ := (ht p).2.1
    omega
  have hpair : Pairwise (Nat.Coprime on fun p : t => p.1) := by
    intro p r hpr
    exact (Nat.coprime_primes (ht p).1 (ht r).1).mpr (Subtype.coe_injective.ne hpr)
  have hsieve := residueClassSurvivors_card_le_productCutoff
    (fun p : t => p.1) hpair vanish m0 M Q hQ hQM
    (fun p => Finset.singleton_nonempty _)
    (fun p => by simpa [vanish] using (ht p).1.one_lt)
  let D : ℝ := ∑ T ∈ productCutoffFamily (fun p : t => p.1) Q,
    ∏ p ∈ T, (1 : ℝ) / (p.1 - 1 : ℕ)
  have hsum : (∑ T ∈ productCutoffFamily (fun p : t => p.1) Q,
      ∏ p ∈ T, residueRemovalRatio (fun p : t => p.1) vanish p) = D := by
    simp [D, residueRemovalRatio, vanish]
  rw [hsum] at hsieve
  have hden : sieveDenominator q Q ≤ D :=
    sieveDenominator_le_productCutoff (fun p hp hpQ hpq =>
      mem_progressionSievePrimes.mpr ⟨hp, hpQ, hpq⟩)
  have hdenpos : 0 < sieveDenominator q Q := by
    have hlog : 0 < Real.log (Q + 1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q + 1))
    have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have h := sieveDenominator_ge_log q Q hq
    have hpos : 0 < (Nat.totient q : ℝ) / q * Real.log (Q + 1 : ℕ) := by positivity
    linarith
  exact (show ((affinePrimesAbove q a m0 M Q).card : ℝ) ≤
      ((residueClassSurvivors vanish m0 M).card : ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans
    (hsieve.trans (div_le_div_of_nonneg_left (by positivity) hdenpos hden))

/-- An explicit elementary progression sieve bound. -/
theorem affinePrimesAbove_card_le_log
    (q a m0 M Q : ℕ) (hq : 0 < q) (hQ : 1 ≤ Q) (hQM : Q ^ 2 ≤ M) :
    ((affinePrimesAbove q a m0 M Q).card : ℝ) ≤
      4 * M * q / (Nat.totient q * Real.log (Q + 1 : ℕ)) := by
  have hsieve := affinePrimesAbove_card_le_sieveDenominator q a m0 M Q hq hQ hQM
  have hden := sieveDenominator_ge_log q Q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0 < Real.log (Q + 1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q + 1))
  have hdenpos : 0 < sieveDenominator q Q := by
    have : 0 < (Nat.totient q : ℝ) / q * Real.log (Q + 1 : ℕ) := by positivity
    linarith
  apply hsieve.trans
  rw [div_le_div_iff₀ hdenpos (mul_pos hphi hlog)]
  have hd : (Nat.totient q : ℝ) * Real.log (Q + 1 : ℕ) ≤
      2 * sieveDenominator q Q * q := by
    rw [← div_le_iff₀ hqR]
    simpa only [div_mul_eq_mul_div] using hden
  nlinarith [mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 * M by positivity)]

noncomputable def dyadicPrimeResidueCount (N q : ℕ) (a : ZMod q) : ℕ :=
  ((dyadicPrimes N).filter fun p : ℕ => (p : ZMod q) = a).card

lemma dyadicPrimeResidueCount_le_affine
    (N q Q : ℕ) (a : ZMod q) (hq : 0 < q) (hqN : q ≤ N) (hQN : Q ≤ N) :
    dyadicPrimeResidueCount N q a ≤ (affinePrimesAbove q a.val 0 (2 * N / q) Q).card := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let S := (dyadicPrimes N).filter fun p : ℕ => (p : ZMod q) = a
  have hdecomp {p : ℕ} (hp : p ∈ S) : q * (p / q) + a.val = p := by
    have ha := congrArg ZMod.val (Finset.mem_filter.mp hp).2
    rw [ZMod.val_natCast] at ha
    simpa only [ha, add_comm] using (Nat.mod_add_div p q)
  have hinj : Set.InjOn (fun p : ℕ => p / q) S := by
    intro p hp r hr heq
    have h := congrArg (fun m : ℕ => q * m + a.val) heq
    exact (hdecomp hp).symm.trans (h.trans (hdecomp hr))
  have hsub : S.image (fun p => p / q) ⊆ affinePrimesAbove q a.val 0 (2 * N / q) Q := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have hpPool := (Finset.mem_filter.mp hp).1
    have hpI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpPool).1
    apply Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply Finset.mem_Ioc.mpr
      constructor
      · exact Nat.div_pos (hqN.trans hpI.1.le) hq
      · simpa only [zero_add] using Nat.div_le_div_right hpI.2
    · rw [hdecomp hp]
      exact ⟨dyadicPrimes_prime hpPool, hQN.trans_lt hpI.1⟩
  calc
    dyadicPrimeResidueCount N q a = S.card := rfl
    _ = (S.image (fun p => p / q)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem dyadicPrimeResidueCount_le_log
    (N q Q : ℕ) (a : ZMod q) (hq : 0 < q) (hqN : q ≤ N)
    (hQ : 1 ≤ Q) (hQN : Q ≤ N) (hsize : Q ^ 2 * q ≤ 2 * N) :
    (dyadicPrimeResidueCount N q a : ℝ) ≤
      8 * N / (Nat.totient q * Real.log (Q + 1 : ℕ)) := by
  have hQM : Q ^ 2 ≤ 2 * N / q := (Nat.le_div_iff_mul_le hq).mpr hsize
  have hcard : (dyadicPrimeResidueCount N q a : ℝ) ≤
      ((affinePrimesAbove q a.val 0 (2 * N / q) Q).card : ℝ) := by
    exact_mod_cast dyadicPrimeResidueCount_le_affine N q Q a hq hqN hQN
  apply hcard.trans ((affinePrimesAbove_card_le_log q a.val 0 (2 * N / q) Q hq hQ hQM).trans ?_)
  have hprod : ((2 * N / q : ℕ) : ℝ) * q ≤ 2 * N := by
    exact_mod_cast Nat.div_mul_le_self (2 * N) q
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

lemma dyadicPrimeResidueProbability_le_log_ratio
    (N q Q : ℕ) (a : ZMod q) (hq : 0 < q) (hqN : q ≤ N)
    (hQ : 1 ≤ Q) (hQN : Q ≤ N) (hsize : Q ^ 2 * q ≤ 2 * N)
    (hN : 4 ≤ N)
    (hc : ((N : ℝ) / Real.log N) / 10 ≤ ((dyadicPrimes N).card : ℝ)) :
    (dyadicPrimeResidueCount N q a : ℝ) / ((dyadicPrimes N).card : ℝ) ≤
      80 * Real.log N / (Nat.totient q * Real.log (Q + 1 : ℕ)) := by
  have hM := dyadic_pool_card_positive hN hc
  have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0 < Real.log (Q + 1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q + 1))
  have hcount := dyadicPrimeResidueCount_le_log N q Q a hq hqN hQ hQN hsize
  have hcount' := (le_div_iff₀ (mul_pos hphi hlog)).mp hcount
  have hNcount := dyadic_pool_card_lower_mul hN hc
  apply (div_le_div_iff₀ hM (mul_pos hphi hlog)).mpr
  nlinarith

/-- Uniform arithmetic-progression upper bound for the prime pools used
in the product-mixing argument, including moduli up to `T^50`. -/
theorem exists_uniform_dyadicPrimeResidueProbability_bound :
    ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ N : ℕ, T ^ 90 ≤ N → N ≤ T ^ 110 →
      ∀ q : ℕ, 0 < q → q ≤ T ^ 50 → ∀ a : ZMod q,
        (dyadicPrimeResidueCount N q a : ℝ) / ((dyadicPrimes N).card : ℝ) ≤
          8800 / (Nat.totient q : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp eventually_dyadicPrimes_card_bounds
  refine ⟨max 4 N₀, fun T hT N hlow hhigh q hq hqT a => ?_⟩
  have hT4 : 4 ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := by omega
  have hTN : T ≤ N := by
    calc
      T = T ^ 1 := by simp
      _ ≤ T ^ 90 := Nat.pow_le_pow_right hT1 (by decide)
      _ ≤ N := hlow
  have hqN : q ≤ N := hqT.trans
    ((Nat.pow_le_pow_right hT1 (by decide : 50 ≤ 90)).trans hlow)
  have hsize : T ^ 2 * q ≤ 2 * N := by
    calc
      T ^ 2 * q ≤ T ^ 2 * T ^ 50 := Nat.mul_le_mul_left _ hqT
      _ = T ^ 52 := by rw [← pow_add]
      _ ≤ T ^ 90 := Nat.pow_le_pow_right hT1 (by decide)
      _ ≤ N := hlow
      _ ≤ 2 * N := by omega
  have hN4 : 4 ≤ N := hT4.trans hTN
  have hc := (hN₀ N ((le_max_right _ _).trans (hT.trans hTN))).1
  have hbase := dyadicPrimeResidueProbability_le_log_ratio N q T a hq hqN hT1 hTN hsize hN4 hc
  have hlog := mixing_scale_log_le hT1 (by omega : 0 < N) hhigh
  have hlogT : Real.log (T : ℝ) ≤ Real.log (T + 1 : ℕ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show T ≤ T + 1 by omega)
  have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hL : 0 < Real.log (T + 1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T + 1))
  apply hbase.trans
  rw [div_le_div_iff₀ (mul_pos hphi hL) hphi]
  have hLbound : 80 * Real.log (N : ℝ) ≤ 8800 * Real.log (T + 1 : ℕ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hLbound hphi.le]

end Erdos380
