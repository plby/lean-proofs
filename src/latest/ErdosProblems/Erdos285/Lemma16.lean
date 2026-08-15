import ErdosProblems.Erdos285.PrimePowers

/-!
# Martin's small-prime-power elimination lemma

This file formalizes the elementary LCM step used for the small prime powers
in Martin's exact correction.  If `q = p ^ e` is the largest exact
prime-power part of the reduced denominator of a rational `r`, we subtract a
single unit fraction whose denominator is `lcm(1,...,q) / a`, where
`1 ≤ a ≤ p - 1`.  The residue `a` is chosen so that reduction cancels one
additional factor of `p`; all other prime-power parts were already strictly
smaller than `q`.
-/

namespace Erdos285.Lemma16

open Finset
open scoped BigOperators

noncomputable section

open PrimePowers

/-- A prime power dividing `lcm(1,...,y)` is at most `y`. -/
lemma isPrimePow_le_of_dvd_initialLcm {y t : ℕ} (ht : IsPrimePow t)
    (htL : t ∣ initialLcm y) : t ≤ y := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 ht
  have hL0 : initialLcm y ≠ 0 := by
    simp [initialLcm]
  have hkL : k ≤ (initialLcm y).factorization p :=
    (hp.pow_dvd_iff_le_factorization hL0).1 htL
  have hfac : (initialLcm y).factorization p =
      (Icc 1 y).sup (fun a ↦ a.factorization p) := by
    rw [initialLcm]
    simpa only [id_eq] using
      (Finset.factorization_lcm
        (s := Icc 1 y) (f := id) (by
          intro a ha
          exact Nat.ne_of_gt (Finset.mem_Icc.mp ha).1) p)
  rw [hfac] at hkL
  have hIcc : (Icc 1 y).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hkL
    omega
  obtain ⟨a, ha, hsup⟩ :=
    UnitFractions.Finset.sup_eq_mem (s := Icc 1 y)
      (f := fun a ↦ a.factorization p) hIcc
  rw [hsup] at hkL
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp ha).1
  have hpa : p ^ k ∣ a := (hp.pow_dvd_iff_le_factorization ha0).2 hkL
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hpa).trans (Finset.mem_Icc.mp ha).2

/-- Every exact prime-power part of the initial LCM is at most its endpoint. -/
lemma initialLcm_primePowerSmooth (y : ℕ) :
    PrimePowerSmooth y (initialLcm y) := by
  have hL0 : initialLcm y ≠ 0 := by simp [initialLcm]
  intro t ht
  exact isPrimePow_le_of_dvd_initialLcm
    ((mem_primePowerParts hL0).mp ht).1
    ((mem_primePowerParts hL0).mp ht).2.1

/-- If all exact prime-power parts of `d` are at most `y`, then `d` divides
`lcm(1,...,y)`. -/
lemma dvd_initialLcm_of_primePowerSmooth {d y : ℕ} (hd : d ≠ 0)
    (hdy : PrimePowerSmooth y d) : d ∣ initialLcm y := by
  have hparts : (primePowerParts d).lcm id ∣ initialLcm y := by
    apply Finset.lcm_dvd
    intro t ht
    exact (Finset.dvd_lcm (s := Icc 1 y) (f := id)
      (Finset.mem_Icc.mpr
        ⟨((mem_primePowerParts hd).mp ht).1.one_lt.le, hdy t ht⟩))
  have hpartsEq : (primePowerParts d).lcm id = d := by
    calc
      (primePowerParts d).lcm id =
          UnitFractions.lcmA (UnitFractions.ppowers_in_set {d}) := by
            rw [primePowerParts_eq_ppowers_in_singleton]
      _ = UnitFractions.lcmA ({d} : Finset ℕ) :=
        UnitFractions.lcm_Q (by simpa using hd.symm)
      _ = d := by simp [UnitFractions.lcmA]
  rwa [hpartsEq] at hparts

/-- At the endpoint `q = p^e`, the `p`-part of `lcm(1,...,q)` is exactly
`q`. -/
lemma primePower_mem_initialLcm_parts {p e q : ℕ} (hp : p.Prime)
    (he : 0 < e) (hq : q = p ^ e) :
    q ∈ primePowerParts (initialLcm q) := by
  subst q
  have hqpp : IsPrimePow (p ^ e) := ⟨p, e, hp.prime, he, rfl⟩
  have hqmem : p ^ e ∈ Icc 1 (p ^ e) := by
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, le_rfl⟩
  have hqL : p ^ e ∣ initialLcm (p ^ e) :=
    Finset.dvd_lcm (s := Icc 1 (p ^ e)) (f := id) hqmem
  rw [mem_primePowerParts (by simp [initialLcm])]
  refine ⟨hqpp, hqL, ?_⟩
  rw [Nat.coprime_pow_left_iff he, hp.coprime_iff_not_dvd]
  intro hpdiv
  have hsuccDiv : p ^ (e + 1) ∣ initialLcm (p ^ e) := by
    rw [pow_succ]
    exact Nat.mul_dvd_of_dvd_div hqL hpdiv
  have hle := isPrimePow_le_of_dvd_initialLcm
    (show IsPrimePow (p ^ (e + 1)) from
      ⟨p, e + 1, hp.prime, Nat.succ_pos e, rfl⟩) hsuccDiv
  exact (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self e))) hle

/-- Dividing the endpoint LCM by its base prime removes the only possible
exact prime-power part of size `q = p^e`. -/
lemma largestPrimePowerPart_lt_of_dvd_initialLcm_div_prime
    {p e q d : ℕ} (hp : p.Prime) (he : 0 < e) (hq : q = p ^ e)
    (hd : d ∣ initialLcm q / p) :
    largestPrimePowerPart d < q := by
  subst q
  have hpq : p ∣ p ^ e := dvd_pow_self p he.ne'
  have hqL : p ^ e ∣ initialLcm (p ^ e) :=
    Finset.dvd_lcm (s := Icc 1 (p ^ e)) (f := id)
      (Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, le_rfl⟩)
  have hpL : p ∣ initialLcm (p ^ e) := hpq.trans hqL
  have hbound : PrimePowerSmooth (p ^ e - 1) d := by
    intro t ht
    have hd0 : d ≠ 0 := by
      intro hzero
      subst d
      simp [primePowerParts] at ht
    have htSpec := (mem_primePowerParts hd0).mp ht
    have htLdiv : t ∣ initialLcm (p ^ e) / p := htSpec.2.1.trans hd
    have htL : t ∣ initialLcm (p ^ e) :=
      htLdiv.trans (Nat.div_dvd_of_dvd hpL)
    have htle : t ≤ p ^ e :=
      isPrimePow_le_of_dvd_initialLcm htSpec.1 htL
    have htne : t ≠ p ^ e := by
      intro hteq
      subst t
      have hsuccDiv : p ^ (e + 1) ∣ initialLcm (p ^ e) := by
        simpa [pow_succ, mul_comm] using
          (Nat.mul_dvd_of_dvd_div hpL htLdiv)
      have hle := isPrimePow_le_of_dvd_initialLcm
        (show IsPrimePow (p ^ (e + 1)) from
          ⟨p, e + 1, hp.prime, Nat.succ_pos e, rfl⟩) hsuccDiv
      exact (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self e))) hle
    omega
  have hle : largestPrimePowerPart d ≤ p ^ e - 1 :=
    largestPrimePowerPart_le_iff.mpr hbound
  have hqpos : 0 < p ^ e := pow_pos hp.pos e
  omega

/-- Cancel a displayed common natural factor before bounding a rational's
reduced denominator. -/
lemma rat_den_dvd_div_of_eq_divInt {r : ℚ} {a : ℤ} {b p : ℕ}
    (hb : b ≠ 0) (hp0 : p ≠ 0) (hpb : p ∣ b)
    (hpa : (p : ℤ) ∣ a) (hr : r = Rat.divInt a b) :
    r.den ∣ b / p := by
  obtain ⟨b', rfl⟩ := hpb
  obtain ⟨a', ha'⟩ := hpa
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  have hrepr : r = Rat.divInt a' b' := by
    rw [hr, ha']
    push_cast
    exact Rat.divInt_mul_left hpZ
  rw [hrepr]
  have hdenZ : (((Rat.divInt a' b').den : ℕ) : ℤ) ∣ (b' : ℤ) :=
    Rat.den_dvd a' b'
  have hden : (Rat.divInt a' b').den ∣ b' := by
    exact_mod_cast hdenZ
  simpa [hp0] using hden

/-- Martin's Lemma 16 (the small-prime-power step).

The returned numerator `a` is the least positive residue of
`r.num * (L / r.den)` modulo `p`, and the unit-fraction denominator is
`n = L / a`, where `L = lcm(1,...,q)`. -/
theorem smallPrimePower_elimination (r : ℚ) {p e q : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q = p ^ e)
    (hqmax : q = largestPrimePowerPart r.den) :
    ∃ a n : ℕ,
      1 ≤ a ∧ a ≤ p - 1 ∧ Nat.Coprime p a ∧
      a ∣ initialLcm q ∧ n = initialLcm q / a ∧
      initialLcm q / (p - 1) ≤ n ∧
      q ∣ n ∧ q ∈ primePowerParts n ∧
      PrimePowerSmooth q n ∧ largestPrimePowerPart n = q ∧
      largestPrimePowerPart (r - (1 : ℚ) / n).den < q := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hqpp : IsPrimePow q := by
    subst q
    exact ⟨p, e, hp.prime, he, rfl⟩
  have hqpos : 0 < q := hqpp.pos
  have hqleDen : q ≤ r.den := by
    rw [hqmax]
    exact largestPrimePowerPart_le
  have hden2 : 2 ≤ r.den := hqpp.two_le.trans hqleDen
  have hqDen : q ∈ primePowerParts r.den := by
    rw [hqmax]
    exact largestPrimePowerPart_mem hden2
  have hdenSmooth : PrimePowerSmooth q r.den := by
    rw [← largestPrimePowerPart_le_iff, ← hqmax]
  have hdenL : r.den ∣ initialLcm q :=
    dvd_initialLcm_of_primePowerSmooth r.den_ne_zero hdenSmooth
  have hqLpart : q ∈ primePowerParts (initialLcm q) :=
    primePower_mem_initialLcm_parts hp he hq
  have hLpos : 0 < initialLcm q :=
    Nat.pos_of_ne_zero (by simp [initialLcm])
  have hqDenSpec := (mem_primePowerParts r.den_ne_zero).mp hqDen
  have hqLSpec := (mem_primePowerParts (by simp [initialLcm])).mp hqLpart
  have hpq : p ∣ q := by
    subst q
    exact dvd_pow_self p he.ne'
  have hpDen : p ∣ r.den := hpq.trans hqDenSpec.2.1
  have hpNumCoprime : Nat.Coprime p r.num.natAbs :=
    Nat.Coprime.of_dvd_left hpDen r.reduced.symm
  have hratioDvd : initialLcm q / r.den ∣ initialLcm q / q :=
    Nat.div_dvd_div_left hdenL hqDenSpec.2.1
  have hpRatioCoprime : Nat.Coprime p (initialLcm q / r.den) := by
    have hpLquot : Nat.Coprime p (initialLcm q / q) :=
      Nat.Coprime.of_dvd_left hpq hqLSpec.2.2
    exact Nat.Coprime.of_dvd_right hratioDvd hpLquot
  have hnumCast : (r.num : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hdiv ↦ (hp.coprime_iff_not_dvd.mp hpNumCoprime)
      (Int.natCast_dvd.mp hdiv)
  have hratioCast : ((initialLcm q / r.den : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hpRatioCoprime
  let u : ZMod p :=
    (r.num : ZMod p) * ((initialLcm q / r.den : ℕ) : ZMod p)
  have hu : u ≠ 0 := mul_ne_zero hnumCast hratioCast
  let a : ℕ := u.val
  have haPos : 0 < a := ZMod.val_pos.mpr hu
  have haLt : a < p := ZMod.val_lt u
  have haLe : a ≤ p - 1 := by omega
  have hpa : Nat.Coprime p a := by
    rw [hp.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt haPos haLt
  have hpLeq : p ≤ q := by
    rw [hq]
    exact Nat.le_self_pow he.ne' p
  have haq : a ≤ q := haLt.le.trans hpLeq
  have haL : a ∣ initialLcm q := by
    exact Finset.dvd_lcm (s := Icc 1 q) (f := id)
      (Finset.mem_Icc.mpr ⟨haPos, haq⟩)
  let n : ℕ := initialLcm q / a
  have hnEq : n = initialLcm q / a := rfl
  have hlower : initialLcm q / (p - 1) ≤ n := by
    rw [hnEq]
    exact Nat.div_le_div le_rfl haLe haPos.ne'
  have haqCoprime : Nat.Coprime a q := by
    rw [hq]
    exact hpa.symm.pow_right e
  have haLquot : a ∣ initialLcm q / q := by
    rw [← haqCoprime.dvd_mul_right]
    simpa [Nat.mul_div_cancel' hqLSpec.2.1, mul_comm] using haL
  have hnFactor : n = q * ((initialLcm q / q) / a) := by
    rw [hnEq, ← Nat.mul_div_assoc q haLquot, Nat.mul_div_cancel' hqLSpec.2.1]
  have hqN : q ∣ n := hnFactor.symm ▸ dvd_mul_right q _
  have hqNquot : n / q = (initialLcm q / q) / a := by
    rw [hnFactor, Nat.mul_div_cancel_left _ hqpos]
  have hqNcoprime : Nat.Coprime q (n / q) := by
    rw [hqNquot]
    exact Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd haLquot) hqLSpec.2.2
  have hqNpart : q ∈ primePowerParts n := by
    have hn0 : n ≠ 0 := by
      exact Nat.ne_of_gt
        (Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos)
    exact (mem_primePowerParts hn0).mpr ⟨hqpp, hqN, hqNcoprime⟩
  have hnSmooth : PrimePowerSmooth q n := by
    intro t ht
    have hn0 : n ≠ 0 := by
      exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos)
    have htSpec := (mem_primePowerParts hn0).mp ht
    exact isPrimePow_le_of_dvd_initialLcm htSpec.1
      (htSpec.2.1.trans (Nat.div_dvd_of_dvd haL))
  have hnLargest : largestPrimePowerPart n = q := by
    apply Nat.le_antisymm
    · exact largestPrimePowerPart_le_iff.mpr hnSmooth
    · exact le_largestPrimePowerPart hqNpart
  let m : ℕ := initialLcm q / r.den
  let z : ℤ := r.num * (m : ℤ) - a
  have hzCast : (z : ZMod p) = 0 := by
    simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [show (a : ZMod p) = u by exact ZMod.natCast_zmod_val u]
    simp [u, m]
  have hpz : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzCast
  have hresidual : r - (1 : ℚ) / n = Rat.divInt z (initialLcm q) := by
    rw [Rat.divInt_eq_div]
    change r - (1 : ℚ) / n = (z : ℚ) / (initialLcm q : ℚ)
    have hzRat : (z : ℚ) = (r.num : ℚ) * (m : ℚ) - (a : ℚ) := by
      simp [z]
    rw [hzRat]
    nth_rewrite 1 [← Rat.num_div_den r]
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast haPos.ne'
    rw [hnEq, Nat.cast_div haL haQ]
    have hLdecomp : (initialLcm q : ℚ) =
        (r.den : ℚ) * (m : ℕ) := by
      dsimp [m]
      exact_mod_cast (Nat.mul_div_cancel' hdenL).symm
    have hmPos : 0 < m := by
      dsimp [m]
      exact Nat.div_pos (Nat.le_of_dvd hLpos hdenL) r.den_pos
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hmPos.ne'
    have hdQ : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [hLdecomp]
    field_simp [haQ, hmQ, hdQ]
  have hpL : p ∣ initialLcm q := hpq.trans hqLSpec.2.1
  have hresDen : (r - (1 : ℚ) / n).den ∣ initialLcm q / p :=
    rat_den_dvd_div_of_eq_divInt hLpos.ne' hp.ne_zero hpL hpz hresidual
  have hdescent :
      largestPrimePowerPart (r - (1 : ℚ) / n).den < q :=
    largestPrimePowerPart_lt_of_dvd_initialLcm_div_prime hp he hq hresDen
  exact ⟨a, n, haPos, haLe, hpa, haL, hnEq, hlower, hqN, hqNpart,
    hnSmooth, hnLargest, hdescent⟩

/-- Uniform exponential form of Martin's Lemma 16.  The constant comes from
the formalized estimate `lcm(1,...,y) ≤ exp(C y)`; it is independent of the
rational, the prime, and the exponent. -/
theorem exists_uniform_smallPrimePower_elimination_exp_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℚ) (p e q : ℕ), p.Prime → 0 < e → q = p ^ e →
        q = largestPrimePowerPart r.den →
        ∃ a n : ℕ,
          0 < n ∧ 1 ≤ a ∧ a ≤ p - 1 ∧ Nat.Coprime p a ∧
          a ∣ initialLcm q ∧ n = initialLcm q / a ∧
          initialLcm q / (p - 1) ≤ n ∧
          q ∈ primePowerParts n ∧ largestPrimePowerPart n = q ∧
          largestPrimePowerPart (r - (1 : ℚ) / n).den < q ∧
          (n : ℝ) ≤ Real.exp (C * q) := by
  obtain ⟨C, hCpos, hC⟩ := exists_initialLcm_le_exp
  refine ⟨C, hCpos, ?_⟩
  intro r p e q hp he hq hqmax
  obtain ⟨a, n, haPos, haLe, hpa, haL, hnEq, hlower, hqN, hqNpart,
      hnSmooth, hnLargest, hdescent⟩ :=
    smallPrimePower_elimination r hp he hq hqmax
  have hnPos : 0 < n := by
    rw [hnEq]
    exact Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (by simp [initialLcm])) haL) haPos
  have hnLNat : n ≤ initialLcm q := by
    rw [hnEq]
    exact Nat.div_le_self _ _
  have hnL : (n : ℝ) ≤ initialLcm q := by exact_mod_cast hnLNat
  exact ⟨a, n, hnPos, haPos, haLe, hpa, haL, hnEq, hlower, hqNpart,
    hnLargest, hdescent, hnL.trans (hC q)⟩

end

end Erdos285.Lemma16
