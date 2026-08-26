import ErdosProblems.Erdos380.PrimeProgressionSieve
import ErdosProblems.Erdos380.FiniteHighMoments
import ErdosProblems.Erdos380.ShiftedPrimeHits
import BoundedGaps.Maynard.PrimeMertens

/-! # Bounded-order divisibility moments for small primes -/

open scoped BigOperators Classical

namespace Erdos380

lemma totient_prod_distinct_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    Nat.totient (∏ p ∈ t, p) = ∏ p ∈ t, Nat.totient p := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert p t hpt ih =>
    have hp := ht p (Finset.mem_insert_self _ _)
    have ht' : ∀ r ∈ t, r.Prime := fun r hr => ht r (Finset.mem_insert_of_mem hr)
    have hc : p.Coprime (∏ r ∈ t, r) := Nat.Coprime.prod_right fun r hr =>
      (Nat.coprime_primes hp (ht' r hr)).mpr (by intro h; exact hpt (h ▸ hr))
    rw [Finset.prod_insert hpt, Nat.totient_mul hc, Finset.prod_insert hpt, ih ht']

def smallPrimeDivisibilityEvent (c : ℕ) (h : ℤ) (p r : ℕ) : Prop :=
  (p : ℤ) ∣ (c * r : ℕ) + h

lemma smallPrimeDivisibilityEvent_impossible {c p : ℕ} {h : ℤ}
    (hp : p.Prime) (hph : ¬ (p : ℤ) ∣ h) (hc : ¬ c.Coprime p) (r : ℕ) :
    ¬ smallPrimeDivisibilityEvent c h p r := by
  have hpc : p ∣ c := by
    by_contra hnot
    exact hc (hp.coprime_iff_not_dvd.mpr hnot).symm
  have hpcr : (p : ℤ) ∣ (c * r : ℕ) := by
    exact_mod_cast hpc.trans (dvd_mul_right c r)
  intro hhit
  have hdiff := dvd_sub hhit hpcr
  exact hph (by simpa only [add_sub_cancel_left] using hdiff)

lemma prime_product_int_dvd (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime)
    (n : ℤ) (hd : ∀ p ∈ t, (p : ℤ) ∣ n) :
    ((∏ p ∈ t, p : ℕ) : ℤ) ∣ n := by
  rw [Int.natCast_dvd]
  exact Finset.prod_primes_dvd n.natAbs (fun p hp => (ht p hp).prime)
    (fun p hp => Int.natCast_dvd.mp (hd p hp))

/-- A joint-event upper bound on the actual uniform dyadic prime pool.
The coefficient and the signed shift are arbitrary; primes dividing the
shift are excluded explicitly. -/
theorem smallPrime_joint_bound
    {T N : ℕ} (hT : 1 ≤ T)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ T ^ 50 → ∀ a : ZMod q,
      (dyadicPrimeResidueCount N q a : ℝ) / ((dyadicPrimes N).card : ℝ) ≤
        8800 / (Nat.totient q : ℝ))
    (c : ℕ) (h : ℤ) (t : Finset ℕ)
    (ht : ∀ p ∈ t, p.Prime) (htT : ∀ p ∈ t, p ≤ T)
    (hth : ∀ p ∈ t, ¬ (p : ℤ) ∣ h) (hcard : t.card ≤ 50) :
    (𝔼 r ∈ dyadicPrimes N,
      ∏ p ∈ t, if smallPrimeDivisibilityEvent c h p r then (1 : ℝ) else 0) ≤
      8800 * ∏ p ∈ t, (1 : ℝ) / Nat.totient p := by
  classical
  by_cases hc : ∀ p ∈ t, c.Coprime p
  · let q := ∏ p ∈ t, p
    have hq : 0 < q := Finset.prod_pos fun p hp => (ht p hp).pos
    have hqT : q ≤ T ^ 50 := by
      calc
        q ≤ ∏ _p ∈ t, T := Finset.prod_le_prod' htT
        _ = T ^ t.card := by simp
        _ ≤ T ^ 50 := Nat.pow_le_pow_right hT hcard
    have hcop : c.Coprime q := Nat.Coprime.prod_right hc
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime c hcop
    let a : ZMod q := ((-u⁻¹ : (ZMod q)ˣ) : ZMod q) * (h : ZMod q)
    have hpoint (r : ℕ) :
        (∏ p ∈ t, if smallPrimeDivisibilityEvent c h p r then (1 : ℝ) else 0) ≤
          if (r : ZMod q) = a then (1 : ℝ) else 0 := by
      rw [Finset.prod_boole]
      by_cases hevent : ∀ p ∈ t, smallPrimeDivisibilityEvent c h p r
      · have hdiv : (q : ℤ) ∣ (c * r : ℕ) + h :=
          prime_product_int_dvd t ht _ hevent
        have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdiv
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at hz
        have huc : (u : ZMod q) = c := ZMod.coe_unitOfCoprime c hcop
        rw [← huc] at hz
        have ha : (r : ZMod q) = a := by
          have hz' : (u : ZMod q) * (r : ZMod q) + ((1 : (ZMod q)ˣ) : ZMod q) * h = 0 := by
            simpa using hz
          simpa [a] using (unit_affine_zero_iff u 1 r h).mp hz'
        rw [if_pos ha]
        split_ifs <;> norm_num
      · simp only [if_neg hevent]
        split_ifs <;> norm_num
    calc
      _ ≤ 𝔼 r ∈ dyadicPrimes N, if (r : ZMod q) = a then (1 : ℝ) else 0 :=
        Finset.expect_le_expect fun r _ => hpoint r
      _ = (dyadicPrimeResidueCount N q a : ℝ) / ((dyadicPrimes N).card : ℝ) := by
        rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
        rfl
      _ ≤ 8800 / (Nat.totient q : ℝ) := hAP q hq hqT a
      _ = _ := by
        dsimp [q]
        rw [totient_prod_distinct_primes t ht]
        simp only [Nat.cast_prod, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  · push Not at hc
    obtain ⟨p, hp, hpc⟩ := hc
    have hz (r : ℕ) :
        (∏ l ∈ t, if smallPrimeDivisibilityEvent c h l r then (1 : ℝ) else 0) = 0 := by
      apply Finset.prod_eq_zero hp
      simp [smallPrimeDivisibilityEvent_impossible (ht p hp) (hth p hp) hpc r]
    simp only [hz, Finset.expect_const_zero]
    positivity

noncomputable def normalizedSmallPrimeMass (t : Finset ℕ) (T c : ℕ) (h : ℤ) (r : ℕ) : ℝ :=
  ∑ p ∈ t, (Real.log p / Real.log T) *
    if smallPrimeDivisibilityEvent c h p r then (1 : ℝ) else 0

theorem normalizedSmallPrimeMass_moment_le
    {T N : ℕ} (hT : 2 ≤ T)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ T ^ 50 → ∀ a : ZMod q,
      (dyadicPrimeResidueCount N q a : ℝ) / ((dyadicPrimes N).card : ℝ) ≤
        8800 / (Nat.totient q : ℝ))
    (c : ℕ) (h : ℤ) (t : Finset ℕ)
    (ht : ∀ p ∈ t, p.Prime) (htT : ∀ p ∈ t, p ≤ T)
    (hth : ∀ p ∈ t, ¬ (p : ℤ) ∣ h) :
    (𝔼 r ∈ dyadicPrimes N, normalizedSmallPrimeMass t T c h r ^ 50) ≤
      8800 * (50 : ℝ) ^ 50 *
        Real.exp (∑ p ∈ t, (Real.log p / Real.log T) * (1 / (Nat.totient p : ℝ))) := by
  classical
  let w (p : t) : ℝ := Real.log p.1 / Real.log T
  let b (p : t) : ℝ := 1 / Nat.totient p.1
  let E (p : t) (r : ℕ) := smallPrimeDivisibilityEvent c h p.1 r
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hw0 (p : t) : 0 ≤ w p := div_nonneg (Real.log_natCast_nonneg _) hlogT.le
  have hw1 (p : t) : w p ≤ 1 := by
    apply (div_le_one hlogT).mpr
    exact Real.log_le_log (by exact_mod_cast (ht p.1 p.2).pos) (by exact_mod_cast htT p.1 p.2)
  have hjoint (U : Finset t) (hU : U.card ≤ 50) :
      (𝔼 r ∈ dyadicPrimes N, ∏ p ∈ U, if E p r then (1 : ℝ) else 0) ≤
        8800 * ∏ p ∈ U, b p := by
    let u : Finset ℕ := U.image Subtype.val
    have hsub : u ⊆ t := by
      intro p hp
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
      exact r.2
    have hj := smallPrime_joint_bound (T := T) (N := N) (by omega) hAP c h u
      (fun p hp => ht p (hsub hp)) (fun p hp => htT p (hsub hp))
      (fun p hp => hth p (hsub hp)) (Finset.card_image_le.trans hU)
    have hprod (r : ℕ) :
        (∏ p ∈ u, if smallPrimeDivisibilityEvent c h p r then (1 : ℝ) else 0) =
          ∏ p ∈ U, if E p r then (1 : ℝ) else 0 := by
      rw [show u = U.image Subtype.val from rfl, Finset.prod_image]
      exact fun _ _ _ _ h => Subtype.ext h
    have hbprod : (∏ p ∈ u, (1 : ℝ) / Nat.totient p) = ∏ p ∈ U, b p := by
      rw [show u = U.image Subtype.val from rfl, Finset.prod_image]
      exact fun _ _ _ _ h => Subtype.ext h
    simpa only [hprod, hbprod] using hj
  have hmoment := finite_high_moment_from_joint_bounds (dyadicPrimes N) w b E 50 8800
    hw0 hw1 (fun p => by dsimp [b]; positivity) (by norm_num) hjoint
  have hmass (r : ℕ) : (∑ p : t, w p * if E p r then (1 : ℝ) else 0) =
      normalizedSmallPrimeMass t T c h r :=
    Finset.sum_coe_sort t (fun p => (Real.log p / Real.log T) *
      if smallPrimeDivisibilityEvent c h p r then (1 : ℝ) else 0)
  have hsum : (∑ p : t, w p * b p) =
      ∑ p ∈ t, (Real.log p / Real.log T) * (1 / (Nat.totient p : ℝ)) :=
    Finset.sum_coe_sort t (fun p => (Real.log p / Real.log T) * (1 / (Nat.totient p : ℝ)))
  simpa only [hmass, hsum, Nat.cast_ofNat] using hmoment

theorem exists_uniform_normalized_prime_log_totient_bound :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ T : ℕ, 2 ≤ T → ∀ t : Finset ℕ, t ⊆ Nat.primesLE T →
      (∑ p ∈ t, (Real.log p / Real.log T) * (1 / (Nat.totient p : ℝ))) ≤ S := by
  obtain ⟨C, hC⟩ := BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨2 + 2 * C / Real.log 2, by positivity, fun T hT t ht => ?_⟩
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hlogs : Real.log (2 : ℝ) ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hM : BoundedGaps.Maynard.primeLogHarmonicSum T ≤ Real.log T + C := by
    have h := (abs_le.mp (hC T)).2
    linarith
  calc
    _ ≤ ∑ p ∈ Nat.primesLE T, (Real.log p / Real.log T) * (1 / (Nat.totient p : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg ht (fun p _ _ => by
        exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) hlogT.le) (by positivity))
    _ ≤ ∑ p ∈ Nat.primesLE T, (Real.log p / Real.log T) * (2 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (prime_reciprocal_totient_le (Nat.prime_of_mem_primesLE hp))
        (div_nonneg (Real.log_natCast_nonneg p) hlogT.le)
    _ = (2 / Real.log T) * BoundedGaps.Maynard.primeLogHarmonicSum T := by
      rw [BoundedGaps.Maynard.primeLogHarmonicSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (2 / Real.log T) * (Real.log T + C) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = 2 + 2 * C / Real.log T := by field_simp
    _ ≤ _ := by
      have hd := div_le_div_of_nonneg_left (show 0 ≤ 2 * C by positivity) hlog2 hlogs
      linarith

/-- The required fiftieth moment, with an absolute constant independent of
the coefficient, signed shift, and growing modulus scale. -/
theorem exists_uniform_smallPrime_fiftieth_moment :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ N : ℕ,
      T ^ 90 ≤ N → N ≤ T ^ 110 → ∀ c : ℕ, ∀ h : ℤ, ∀ t : Finset ℕ,
      t ⊆ Nat.primesLE T → (∀ p ∈ t, ¬ (p : ℤ) ∣ h) →
      (𝔼 r ∈ dyadicPrimes N, normalizedSmallPrimeMass t T c h r ^ 50) ≤ K := by
  obtain ⟨T₁, hAP⟩ := exists_uniform_dyadicPrimeResidueProbability_bound
  obtain ⟨S, hS0, hS⟩ := exists_uniform_normalized_prime_log_totient_bound
  refine ⟨8800 * (50 : ℝ) ^ 50 * Real.exp S, by positivity, max 2 T₁, ?_⟩
  intro T hT N hlow hhigh c h t ht hth
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hAP' := hAP T ((le_max_right _ _).trans hT) N hlow hhigh
  have hmoment := normalizedSmallPrimeMass_moment_le hT2 hAP' c h t
    (fun p hp => Nat.prime_of_mem_primesLE (ht hp))
    (fun p hp => Nat.le_of_mem_primesLE (ht hp)) hth
  exact hmoment.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hS T hT2 t ht)) (by positivity))

end Erdos380
