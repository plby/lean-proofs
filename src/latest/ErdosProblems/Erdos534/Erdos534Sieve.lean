import ErdosProblems.Erdos534.Erdos534PrimeExpansion

namespace Erdos534

open scoped BigOperators

lemma sieveDensity_eq_prod_ratio (T : Finset ℕ) :
    sieveDensity T =
      ((∏ q ∈ T, (q - 1 : ℕ)) : ℚ) / ((∏ q ∈ T, q : ℕ) : ℚ) := by
  rw [sieveDensity, Finset.prod_div_distrib]
  simp only [Nat.cast_prod]

lemma card_sifted_quotient_doubling_of_nat_product {T : Finset ℕ}
    {x d p : ℕ} (hT : ∀ q ∈ T, q.Prime) (hd : 0 < d) (hp : 2 ≤ p)
    (hprod :
      3 * 2 ^ (T.card - 1) * d * (∏ q ∈ T, q) ≤
        (p - 2) * x * (∏ q ∈ T, (q - 1))) :
    2 * (sifted T (x / d)).card ≤
      (sifted T (p * x / d)).card := by
  apply card_sifted_quotient_doubling_of_density hT hd hp
  rw [sieveDensity_eq_prod_ratio]
  have hden : (0 : ℚ) < ((∏ q ∈ T, q : ℕ) : ℚ) := by
    exact_mod_cast Finset.prod_pos fun q hq ↦ (hT q hq).pos
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [show (((p - 2 : ℕ) : ℚ) * ((x : ℚ) / d) *
      (((∏ q ∈ T, (q - 1 : ℕ)) : ℚ) / ((∏ q ∈ T, q : ℕ) : ℚ))) =
      (((p - 2 : ℕ) : ℚ) * x * ((∏ q ∈ T, (q - 1 : ℕ)) : ℚ)) /
        (((d : ℕ) : ℚ) * ((∏ q ∈ T, q : ℕ) : ℚ)) by ring]
  apply (le_div_iff₀ (mul_pos hdq hden)).2
  norm_cast
  simpa only [mul_assoc] using hprod

lemma prod_le_pow_card {S : Finset ℕ} {b : ℕ}
    (h : ∀ a ∈ S, a ≤ b) :
    (∏ a ∈ S, a) ≤ b ^ S.card := by
  calc
    (∏ a ∈ S, a) ≤ ∏ _a ∈ S, b := by
      apply Finset.prod_le_prod
      · intro a ha
        omega
      · intro a ha
        exact h a ha
    _ = b ^ S.card := by simp

lemma pow_card_le_prod {S : Finset ℕ} {b : ℕ}
    (h : ∀ a ∈ S, b ≤ a) :
    b ^ S.card ≤ (∏ a ∈ S, a) := by
  calc
    b ^ S.card = ∏ _a ∈ S, b := by simp
    _ ≤ (∏ a ∈ S, a) := by
      apply Finset.prod_le_prod
      · intro a ha
        omega
      · intro a ha
        exact h a ha

lemma two_pow_card_erase_two_le_prod_pred {T : Finset ℕ}
    (hT : ∀ q ∈ T, q.Prime) :
    2 ^ (T.erase 2).card ≤ ∏ q ∈ T, (q - 1) := by
  have hbase : 2 ^ (T.erase 2).card ≤ ∏ q ∈ T.erase 2, (q - 1) := by
    calc
      2 ^ (T.erase 2).card = ∏ _q ∈ T.erase 2, 2 := by simp
      _ ≤ ∏ q ∈ T.erase 2, (q - 1) := by
        apply Finset.prod_le_prod
        · intro q hq
          omega
        · intro q hq
          have hqT := Finset.mem_of_mem_erase hq
          have hqne : q ≠ 2 := Finset.ne_of_mem_erase hq
          have hq3 : 3 ≤ q :=
            (hT q hqT).two_le.lt_or_eq.resolve_right hqne.symm
          omega
  rw [← Finset.prod_erase T (f := fun q ↦ q - 1) (a := 2) (by omega)]
  exact hbase

lemma two_pow_card_sub_one_le_prod_pred {T : Finset ℕ}
    (hT : ∀ q ∈ T, q.Prime) :
    2 ^ (T.card - 1) ≤ ∏ q ∈ T, (q - 1) := by
  refine (Nat.pow_le_pow_right (by omega) ?_).trans
    (two_pow_card_erase_two_le_prod_pred hT)
  by_cases h2 : 2 ∈ T
  · rw [Finset.card_erase_of_mem h2]
  · rw [Finset.erase_eq_of_notMem h2]
    omega

theorem card_sifted_quotient_doubling_of_many_large_primes
    {T : Finset ℕ} {x d p s : ℕ}
    (hT : ∀ q ∈ T, q.Prime) (hd : 0 < d)
    (hp : p.Prime) (hpT : p ∉ T)
    (hpIndex : Nat.primeCounting p = s) (hs : 3 ≤ s)
    (hmany : 2 * s ≤ (T.filter fun q ↦ p < q).card)
    (hcover : d * (∏ q ∈ T, q) ≤
      x * (∏ q ∈ Nat.primesLE p, q)) :
    2 * (sifted T (x / d)).card ≤
      (sifted T (p * x / d)).card := by
  classical
  let Tsmall := T.filter fun q ↦ q < p
  let Tlarge := T.filter fun q ↦ p < q
  have hpart : T = Tsmall ∪ Tlarge := by
    ext q
    simp only [Tsmall, Tlarge, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      have hqne : q ≠ p := by
        intro h
        exact hpT (h ▸ hq)
      by_cases hlt : q < p
      · exact Or.inl ⟨hq, hlt⟩
      · exact Or.inr ⟨hq, by omega⟩
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
  have hdisj : Disjoint Tsmall Tlarge := by
    rw [Finset.disjoint_left]
    intro q hqs hql
    have hsml := (Finset.mem_filter.mp hqs).2
    have hlrg := (Finset.mem_filter.mp hql).2
    omega
  have hcard : T.card = Tsmall.card + Tlarge.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  have hlargeCard : 2 * s ≤ Tlarge.card := hmany
  have hp5 : 5 ≤ p := by
    have hpCount : 3 ≤ Nat.primeCounting p := by simpa [hpIndex]
    by_contra hp5
    have hmono := Nat.monotone_primeCounting (by omega : p ≤ 4)
    have hfour : Nat.primeCounting 4 = 2 := by decide
    rw [hfour] at hmono
    omega
  have hprimorial : (∏ q ∈ Nat.primesLE p, q) ≤ p ^ s := by
    rw [← hpIndex, ← Nat.primesLE_card_eq_primeCounting]
    apply prod_le_pow_card
    intro q hq
    exact (Nat.mem_primesLE.mp hq).1
  have hlargeProd : p ^ Tlarge.card ≤
      ∏ q ∈ Tlarge, (q - 1) := by
    calc
      p ^ Tlarge.card = ∏ _q ∈ Tlarge, p := by simp
      _ ≤ ∏ q ∈ Tlarge, (q - 1) := by
        apply Finset.prod_le_prod
        · intro q hq
          omega
        · intro q hq
          have hqp := (Finset.mem_filter.mp hq).2
          omega
  have hsmallPrime : ∀ q ∈ Tsmall, q.Prime := by
    intro q hq
    exact hT q (Finset.mem_filter.mp hq).1
  have hsmallProd : 2 ^ (Tsmall.card - 1) ≤
      ∏ q ∈ Tsmall, (q - 1) :=
    two_pow_card_sub_one_le_prod_pred hsmallPrime
  have hpowExponent : 2 ^ Tlarge.card ≤ p ^ (Tlarge.card - s) := by
    have hExp : Tlarge.card ≤ 2 * (Tlarge.card - s) := by omega
    have hTwo : 2 ^ Tlarge.card ≤ 2 ^ (2 * (Tlarge.card - s)) :=
      Nat.pow_le_pow_right (by omega) hExp
    have hFour : 2 ^ (2 * (Tlarge.card - s)) =
        4 ^ (Tlarge.card - s) := by
      rw [pow_mul]
      norm_num
    rw [hFour] at hTwo
    exact hTwo.trans (Nat.pow_le_pow_left (by omega : 4 ≤ p) _)
  have hsle : s ≤ Tlarge.card := by omega
  have hpowSplit : 2 ^ Tlarge.card * p ^ s ≤ p ^ Tlarge.card := by
    calc
      2 ^ Tlarge.card * p ^ s ≤
          p ^ (Tlarge.card - s) * p ^ s :=
        Nat.mul_le_mul_right _ hpowExponent
      _ = p ^ Tlarge.card := by
        rw [← pow_add]
        congr 1
        omega
  have hlargeNumerical :
      3 * 2 ^ Tlarge.card * (∏ q ∈ Nat.primesLE p, q) ≤
        (p - 2) * p ^ Tlarge.card := by
    calc
      3 * 2 ^ Tlarge.card * (∏ q ∈ Nat.primesLE p, q) ≤
          3 * 2 ^ Tlarge.card * p ^ s :=
        Nat.mul_le_mul_left _ hprimorial
      _ = 3 * (2 ^ Tlarge.card * p ^ s) := by ring
      _ ≤ 3 * p ^ Tlarge.card := Nat.mul_le_mul_left 3 hpowSplit
      _ ≤ (p - 2) * p ^ Tlarge.card :=
        Nat.mul_le_mul_right _ (by omega)
  have hpowCard : 2 ^ (T.card - 1) ≤
      2 ^ Tlarge.card * 2 ^ (Tsmall.card - 1) := by
    rw [hcard]
    by_cases hzero : Tsmall.card = 0
    · rw [hzero]
      simp only [zero_add, zero_tsub, pow_zero, mul_one]
      exact Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    · rw [show Tsmall.card + Tlarge.card - 1 =
          Tlarge.card + (Tsmall.card - 1) by omega, pow_add]
  have hprodSplit : (∏ q ∈ T, (q - 1)) =
      (∏ q ∈ Tsmall, (q - 1)) *
        (∏ q ∈ Tlarge, (q - 1)) := by
    rw [hpart, Finset.prod_union hdisj]
  have hmainProduct :
      3 * 2 ^ (T.card - 1) * (∏ q ∈ Nat.primesLE p, q) ≤
        (p - 2) * (∏ q ∈ T, (q - 1)) := by
    calc
      3 * 2 ^ (T.card - 1) * (∏ q ∈ Nat.primesLE p, q) ≤
          3 * (2 ^ Tlarge.card * 2 ^ (Tsmall.card - 1)) *
            (∏ q ∈ Nat.primesLE p, q) := by
        gcongr
      _ = (3 * 2 ^ Tlarge.card *
            (∏ q ∈ Nat.primesLE p, q)) *
          2 ^ (Tsmall.card - 1) := by ring
      _ ≤ ((p - 2) * p ^ Tlarge.card) *
          (∏ q ∈ Tsmall, (q - 1)) :=
        Nat.mul_le_mul hlargeNumerical hsmallProd
      _ ≤ ((p - 2) * (∏ q ∈ Tlarge, (q - 1))) *
          (∏ q ∈ Tsmall, (q - 1)) := by
        gcongr
      _ = (p - 2) * (∏ q ∈ T, (q - 1)) := by
        rw [hprodSplit]
        ring
  apply card_sifted_quotient_doubling_of_nat_product hT hd hp.two_le
  calc
    3 * 2 ^ (T.card - 1) * d * (∏ q ∈ T, q) =
        3 * 2 ^ (T.card - 1) * (d * (∏ q ∈ T, q)) := by ring
    _ ≤ 3 * 2 ^ (T.card - 1) *
        (x * (∏ q ∈ Nat.primesLE p, q)) := by gcongr
    _ = x * (3 * 2 ^ (T.card - 1) *
        (∏ q ∈ Nat.primesLE p, q)) := by ring
    _ ≤ x * ((p - 2) * (∏ q ∈ T, (q - 1))) := by gcongr
    _ = (p - 2) * x * (∏ q ∈ T, (q - 1)) := by ring

lemma signature_product_cover {N r : ℕ} {S : Finset ℕ}
    (hN : N ≠ 0) (hSscope : S ⊆ coreScope N r) :
    (∏ q ∈ S, q) * (∏ q ∈ signatureForbidden N r S, q) ≤
      N * (∏ q ∈ Nat.primesLE r, q) := by
  classical
  have hpartition :
      (∏ q ∈ S, q) * (∏ q ∈ signatureForbidden N r S, q) =
        ∏ q ∈ coreScope N r, q := by
    rw [signatureForbidden]
    simpa [mul_comm] using
      (Finset.prod_sdiff hSscope (f := fun q : ℕ ↦ q))
  have hscopeDvd : (∏ q ∈ coreScope N r, q) ∣
      (∏ q ∈ Nat.primesLE r, q) *
        (∏ q ∈ N.primeFactors, q) := by
    refine ⟨∏ q ∈ Nat.primesLE r ∩ N.primeFactors, q, ?_⟩
    simpa [coreScope] using
      (Finset.prod_union_inter (s₁ := Nat.primesLE r)
        (s₂ := N.primeFactors) (f := fun q : ℕ ↦ q)).symm
  have hradDvd :
      (∏ q ∈ Nat.primesLE r, q) * (∏ q ∈ N.primeFactors, q) ∣
        (∏ q ∈ Nat.primesLE r, q) * N :=
    Nat.mul_dvd_mul_left _ (Nat.prod_primeFactors_dvd N)
  have hfinalDvd : (∏ q ∈ coreScope N r, q) ∣
      N * (∏ q ∈ Nat.primesLE r, q) := by
    rw [mul_comm]
    exact hscopeDvd.trans hradDvd
  rw [hpartition]
  apply Nat.le_of_dvd
  exact Nat.mul_pos (Nat.pos_of_ne_zero hN) (Finset.prod_pos fun q hq ↦
    (Nat.mem_primesLE.mp hq).2.pos)
  exact hfinalDvd

lemma card_sifted_doubling_of_insert_small {T : Finset ℕ}
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqT : q ∉ T)
    (hT : ∀ r ∈ T, r.Prime)
    (hinsert : ∀ U,
      2 * (sifted (insert q T) U).card ≤
        (sifted (insert q T) (p * U)).card) :
    ∀ U, 2 * (sifted T U).card ≤ (sifted T (p * U)).card := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      by_cases hU : U = 0
      · subst U
        simp [sifted]
      have hUpos : 0 < U := Nat.pos_of_ne_zero hU
      have hqdivlt : U / q < U := Nat.div_lt_self hUpos hq.one_lt
      have hsmall := ih (U / q) hqdivlt
      have hscale : p * (U / q) ≤ (p * U) / q := by
        apply (Nat.le_div_iff_mul_le hq.pos).2
        calc
          p * (U / q) * q = p * ((U / q) * q) := by ring
          _ ≤ p * U := Nat.mul_le_mul_left p (Nat.div_mul_le_self U q)
      have hsmall' : 2 * (sifted T (U / q)).card ≤
          (sifted T ((p * U) / q)).card :=
        hsmall.trans (Finset.card_le_card (sifted_mono_cutoff T hscale))
      have hlowLe : (sifted T (U / q)).card ≤ (sifted T U).card :=
        Finset.card_le_card (sifted_mono_cutoff T (Nat.div_le_self U q))
      have hhighLe : (sifted T ((p * U) / q)).card ≤
          (sifted T (p * U)).card :=
        Finset.card_le_card (sifted_mono_cutoff T (Nat.div_le_self (p * U) q))
      have hrecLow : (sifted T U).card =
          (sifted (insert q T) U).card + (sifted T (U / q)).card := by
        have hrec := card_sifted_insert hq hqT hT (U := U)
        omega
      have hrecHigh : (sifted T (p * U)).card =
          (sifted (insert q T) (p * U)).card +
            (sifted T ((p * U) / q)).card := by
        have hrec := card_sifted_insert hq hqT hT (U := p * U)
        omega
      have htop := hinsert U
      omega

lemma primeIntervalExpansion_insert_lt {T : Finset ℕ} {p q : ℕ}
    (hqp : q < p) (hexpand : PrimeIntervalExpansion T p) :
    PrimeIntervalExpansion (insert q T) p := by
  intro X hpX
  have hold : oldPrimeBand (insert q T) p X = oldPrimeBand T p X := by
    ext r
    simp only [mem_oldPrimeBand, Finset.mem_insert]
    constructor
    · rintro ⟨hrPrime, hpr, hrX, hnot⟩
      exact ⟨hrPrime, hpr, hrX, fun hrT ↦ hnot (Or.inr hrT)⟩
    · rintro ⟨hrPrime, hpr, hrX, hrT⟩
      refine ⟨hrPrime, hpr, hrX, ?_⟩
      rintro (hrq | hrT')
      · omega
      · exact hrT hrT'
  have hnew : newPrimeBand (insert q T) p X = newPrimeBand T p X := by
    ext r
    simp only [mem_newPrimeBand, Finset.mem_insert]
    constructor
    · rintro ⟨hrPrime, hXr, hrTop, hnot⟩
      exact ⟨hrPrime, hXr, hrTop, fun hrT ↦ hnot (Or.inr hrT)⟩
    · rintro ⟨hrPrime, hXr, hrTop, hrT⟩
      refine ⟨hrPrime, hXr, hrTop, ?_⟩
      rintro (hrq | hrT')
      · omega
      · exact hrT hrT'
  rw [hold, hnew]
  exact hexpand X hpX

theorem card_sifted_doubling_of_primeIntervalExpansion_general
    {T : Finset ℕ} {p U : ℕ}
    (hp : p.Prime) (hpT : p ∉ T) (hT : ∀ q ∈ T, q.Prime)
    (hexpand : PrimeIntervalExpansion T p) :
    2 * (sifted T U).card ≤ (sifted T (p * U)).card := by
  classical
  induction hmeasure : (Nat.primesLE (p - 1) \ T).card using
      Nat.strong_induction_on generalizing T U with
  | h k ih =>
      let missing := Nat.primesLE (p - 1) \ T
      by_cases hempty : missing = ∅
      · apply card_sifted_doubling_of_primeIntervalExpansion
          hp hpT hT
        · intro q hqPrime hqp
          have hqSmall : q ∈ Nat.primesLE (p - 1) :=
            Nat.mem_primesLE.mpr ⟨by omega, hqPrime⟩
          by_contra hqT
          have : q ∈ missing := Finset.mem_sdiff.mpr ⟨hqSmall, hqT⟩
          rw [hempty] at this
          simp at this
        · exact hexpand
      · obtain ⟨q, hqMissing⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hqData := Finset.mem_sdiff.mp hqMissing
        have hqPrime : q.Prime := (Nat.mem_primesLE.mp hqData.1).2
        have hqp : q < p := by
          have := (Nat.mem_primesLE.mp hqData.1).1
          have := hp.two_le
          omega
        have hqT : q ∉ T := hqData.2
        have hmissingEq : Nat.primesLE (p - 1) \ insert q T =
            missing.erase q := by
          ext a
          simp only [missing, Finset.mem_sdiff, Finset.mem_insert,
            Finset.mem_erase]
          aesop
        have hcardLt : (Nat.primesLE (p - 1) \ insert q T).card < k := by
          have hpos : 0 < missing.card := Finset.card_pos.mpr
            (Finset.nonempty_iff_ne_empty.mpr hempty)
          have hk : missing.card = k := by
            simpa [missing] using hmeasure
          rw [hmissingEq, Finset.card_erase_of_mem hqMissing, hk]
          omega
        have hinsertPrime : ∀ a ∈ insert q T, a.Prime := by
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hqPrime
          · exact hT a ha
        have hinsertExpand : PrimeIntervalExpansion (insert q T) p :=
          primeIntervalExpansion_insert_lt hqp hexpand
        have hinsert : ∀ V,
            2 * (sifted (insert q T) V).card ≤
              (sifted (insert q T) (p * V)).card := by
          intro V
          exact ih _ hcardLt (T := insert q T) (U := V)
            (by simpa [Ne.symm (ne_of_lt hqp)]) hinsertPrime hinsertExpand rfl
        exact card_sifted_doubling_of_insert_small hp hqPrime hqT hT
          hinsert U

theorem card_sifted_quotient_doubling_three_of_three_large
    {T : Finset ℕ} {x d : ℕ}
    (hT : ∀ q ∈ T, q.Prime) (hd : 0 < d) (hthree : 3 ∉ T)
    (hmany : 3 ≤ (T.filter fun q ↦ 3 < q).card)
    (hcover : d * (∏ q ∈ T, q) ≤
      x * (∏ q ∈ Nat.primesLE 3, q)) :
    2 * (sifted T (x / d)).card ≤
      (sifted T (3 * x / d)).card := by
  classical
  let Tsmall := T.filter fun q ↦ q < 3
  let Tlarge := T.filter fun q ↦ 3 < q
  have hpart : T = Tsmall ∪ Tlarge := by
    ext q
    simp only [Tsmall, Tlarge, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      have hqne : q ≠ 3 := by
        intro h
        exact hthree (h ▸ hq)
      by_cases hlt : q < 3
      · exact Or.inl ⟨hq, hlt⟩
      · exact Or.inr ⟨hq, by omega⟩
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
  have hdisj : Disjoint Tsmall Tlarge := by
    rw [Finset.disjoint_left]
    intro q hqs hql
    have := (Finset.mem_filter.mp hqs).2
    have := (Finset.mem_filter.mp hql).2
    omega
  have hsmallSub : Tsmall ⊆ {2} := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    have hqPrime := hT q hqData.1
    have hqTwo := hqPrime.two_le
    have : q = 2 := by omega
    simpa [this]
  have hsmallCard : Tsmall.card ≤ 1 := by
    simpa using Finset.card_le_card hsmallSub
  have hsmallProd : (∏ q ∈ Tsmall, (q - 1)) = 1 := by
    apply Finset.prod_eq_one
    intro q hq
    have hq2 : q = 2 := by simpa using hsmallSub hq
    simp [hq2]
  have hcard : T.card = Tsmall.card + Tlarge.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  have hlargeCard : 3 ≤ Tlarge.card := hmany
  have hprodSplit : (∏ q ∈ T, (q - 1)) =
      ∏ q ∈ Tlarge, (q - 1) := by
    rw [hpart, Finset.prod_union hdisj, hsmallProd, one_mul]
  have hrest : 6 ^ (Tlarge.erase 5).card ≤
      ∏ q ∈ Tlarge.erase 5, (q - 1) := by
    calc
      6 ^ (Tlarge.erase 5).card =
          ∏ _q ∈ Tlarge.erase 5, 6 := by simp
      _ ≤ ∏ q ∈ Tlarge.erase 5, (q - 1) := by
        apply Finset.prod_le_prod
        · intro q hq
          omega
        · intro q hq
          have hqLarge := (Finset.mem_filter.mp
            (Finset.mem_of_mem_erase hq)).2
          have hqne : q ≠ 5 := Finset.ne_of_mem_erase hq
          have hqPrime := hT q (Finset.mem_filter.mp
            (Finset.mem_of_mem_erase hq)).1
          have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
          rcases hqOdd with ⟨a, ha⟩
          omega
  have hlargeProd : 4 * 6 ^ (Tlarge.card - 1) ≤
      ∏ q ∈ Tlarge, (q - 1) := by
    by_cases hfive : 5 ∈ Tlarge
    · rw [Finset.card_erase_of_mem hfive] at hrest
      calc
        4 * 6 ^ (Tlarge.card - 1) ≤
            4 * (∏ q ∈ Tlarge.erase 5, (q - 1)) :=
          Nat.mul_le_mul_left 4 hrest
        _ = ∏ q ∈ Tlarge, (q - 1) := by
          rw [mul_comm, Finset.prod_erase_mul Tlarge
            (fun q ↦ q - 1) hfive]
    · rw [Finset.erase_eq_of_notMem hfive] at hrest
      calc
        4 * 6 ^ (Tlarge.card - 1) ≤
            6 * 6 ^ (Tlarge.card - 1) :=
          Nat.mul_le_mul_right _ (by norm_num)
        _ = 6 ^ Tlarge.card := by
          rw [mul_comm, ← pow_succ]
          congr 1
          omega
        _ ≤ ∏ q ∈ Tlarge, (q - 1) := hrest
  have hpower : 18 * 2 ^ Tlarge.card ≤
      4 * 6 ^ (Tlarge.card - 1) := by
    have hbasePow : 2 ^ (Tlarge.card - 3) ≤
        6 ^ (Tlarge.card - 3) :=
      Nat.pow_le_pow_left (by omega) _
    have hpowTwo : 2 ^ Tlarge.card =
        8 * 2 ^ (Tlarge.card - 3) := by
      conv_lhs => rw [show Tlarge.card = 3 + (Tlarge.card - 3) by omega]
      rw [pow_add]
      norm_num
    have hpowSix : 6 ^ (Tlarge.card - 1) =
        36 * 6 ^ (Tlarge.card - 3) := by
      conv_lhs => rw [show Tlarge.card - 1 =
        2 + (Tlarge.card - 3) by omega]
      rw [pow_add]
      norm_num
    calc
      18 * 2 ^ Tlarge.card = 144 * 2 ^ (Tlarge.card - 3) := by
        rw [hpowTwo]
        ring
      _ ≤ 144 * 6 ^ (Tlarge.card - 3) :=
        Nat.mul_le_mul_left 144 hbasePow
      _ = 4 * 6 ^ (Tlarge.card - 1) := by
        rw [hpowSix]
        ring
  have hpowCard : 2 ^ (T.card - 1) ≤ 2 ^ Tlarge.card := by
    apply Nat.pow_le_pow_right (by omega)
    rw [hcard]
    omega
  have hprim : (∏ q ∈ Nat.primesLE 3, q) = 6 := by decide
  apply card_sifted_quotient_doubling_of_nat_product hT hd (by omega)
  calc
    3 * 2 ^ (T.card - 1) * d * (∏ q ∈ T, q) =
        3 * 2 ^ (T.card - 1) * (d * (∏ q ∈ T, q)) := by ring
    _ ≤ 3 * 2 ^ (T.card - 1) *
        (x * (∏ q ∈ Nat.primesLE 3, q)) := by gcongr
    _ ≤ 3 * 2 ^ Tlarge.card *
        (x * (∏ q ∈ Nat.primesLE 3, q)) := by gcongr
    _ = x * (18 * 2 ^ Tlarge.card) := by rw [hprim]; ring
    _ ≤ x * (4 * 6 ^ (Tlarge.card - 1)) := by gcongr
    _ ≤ x * (∏ q ∈ Tlarge, (q - 1)) := by gcongr
    _ = (3 - 2) * x * (∏ q ∈ T, (q - 1)) := by
      rw [hprodSplit]
      ring

lemma card_sifted_singleton_two (U : ℕ) :
    (sifted ({2} : Finset ℕ) U).card = U - U / 2 := by
  rw [show ({2} : Finset ℕ) = insert 2 ∅ by simp,
    card_sifted_insert (by norm_num : (2 : ℕ).Prime) (by simp) (by simp),
    card_sifted_empty, card_sifted_empty]

lemma card_sifted_pair_two_three_doubling {q U : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) :
    2 * (sifted ({2, q} : Finset ℕ) U).card ≤
      (sifted ({2, q} : Finset ℕ) (3 * U)).card := by
  have hq2 : q ≠ 2 := by omega
  have hqOdd : Odd q := hq.odd_of_ne_two hq2
  rcases hqOdd with ⟨qhalf, hqhalf⟩
  have hq5 : 5 ≤ q := by omega
  rw [show ({2, q} : Finset ℕ) = insert q {2} by
      ext a; simp [or_comm]]
  rw [card_sifted_insert hq (by simpa using hq2) (by
      intro p hp
      simp only [Finset.mem_singleton] at hp
      simpa [hp] using (show (2 : ℕ).Prime by norm_num)),
    card_sifted_insert hq (by simpa using hq2) (by
      intro p hp
      simp only [Finset.mem_singleton] at hp
      simpa [hp] using (show (2 : ℕ).Prime by norm_num)),
    card_sifted_singleton_two, card_sifted_singleton_two,
    card_sifted_singleton_two, card_sifted_singleton_two]
  have hquot : (3 * U) / q ≤ 3 * (U / q) + 2 := by
    apply Nat.lt_succ_iff.mp
    rw [Nat.div_lt_iff_lt_mul hq.pos]
    nth_rw 1 [← Nat.div_add_mod U q]
    have hmod := Nat.mod_lt U hq.pos
    nlinarith
  by_cases hU : U ≤ 2
  · interval_cases U
    · norm_num
    · norm_num [Nat.div_eq_of_lt (by omega : 1 < q),
        Nat.div_eq_of_lt (by omega : 3 < q)]
    · by_cases hq6 : q ≤ 6
      · interval_cases q <;> norm_num at hq
        norm_num
      · norm_num [Nat.div_eq_of_lt (by omega : 2 < q),
          Nat.div_eq_of_lt (by omega : 6 < q)]
  have hVle : U / q ≤ U / 5 :=
    Nat.div_le_div_left hq5 (by omega)
  have hcountTwo : 2 ≤
      (U - U / 2) - (U / q - (U / q) / 2) := by
    apply Nat.le_sub_of_add_le
    have hA : U / 5 + 2 ≤ U - U / 2 := by omega
    have hB : U / q - (U / q) / 2 ≤ U / 5 :=
      (Nat.sub_le _ _).trans hVle
    omega
  have hoddScale : 3 * (U - U / 2) ≤
      (3 * U - (3 * U) / 2) + 1 := by omega
  have hremoveScale :
      (3 * U) / q - ((3 * U) / q) / 2 ≤
        3 * (U / q - (U / q) / 2) + 1 := by omega
  omega

def oddMultipleBalance (d V : ℕ) : ℤ :=
  ((V / d : ℕ) : ℤ) - ((V / (2 * d) : ℕ) : ℤ)

lemma oddMultipleBalance_scale_three {d V : ℕ} (hd : 0 < d) :
    oddMultipleBalance d V - 2 * oddMultipleBalance d (V / 3) =
        ((V / (6 * d) : ℕ) : ℤ) ∨
      oddMultipleBalance d V - 2 * oddMultipleBalance d (V / 3) =
        ((V / (6 * d) : ℕ) : ℤ) + 1 := by
  let k := V / (6 * d)
  let rem := V % (6 * d)
  have hsixd : 0 < 6 * d := Nat.mul_pos (by norm_num) hd
  have hrem : rem < 6 * d := Nat.mod_lt V hsixd
  have hdecomp : d * (6 * k) + rem = V := by
    have h := (Nat.div_add_mod V (6 * d)).symm
    dsimp only [k, rem]
    nlinarith
  have hdiv1 : V / d = 6 * k + rem / d := by
    rw [← hdecomp]
    exact Nat.mul_add_div hd (6 * k) rem
  have hdiv2 : V / (2 * d) = 3 * k + rem / (2 * d) := by
    have heq : (2 * d) * (3 * k) + rem = V := by
      rw [← hdecomp]
      ring
    rw [← heq]
    exact Nat.mul_add_div (Nat.mul_pos (by norm_num) hd) (3 * k) rem
  have hdiv3 : V / (3 * d) = 2 * k + rem / (3 * d) := by
    have heq : (3 * d) * (2 * k) + rem = V := by
      rw [← hdecomp]
      ring
    rw [← heq]
    exact Nat.mul_add_div (Nat.mul_pos (by norm_num) hd) (2 * k) rem
  have hdiv6 : V / (6 * d) = k := by rfl
  let a := rem / d
  let b := rem / (2 * d)
  let c := rem / (3 * d)
  have ha6 : a < 6 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    exact hrem
  have hb3 : b < 3 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (by norm_num) hd)]
    nlinarith
  have hc2 : c < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (by norm_num) hd)]
    nlinarith
  have haL : a * d ≤ rem := Nat.div_mul_le_self rem d
  have haU : rem < (a + 1) * d := by
    rw [← Nat.div_lt_iff_lt_mul hd]
    exact Nat.lt_succ_self _
  have hbL : b * (2 * d) ≤ rem := Nat.div_mul_le_self rem (2 * d)
  have hbU : rem < (b + 1) * (2 * d) := by
    rw [← Nat.div_lt_iff_lt_mul (Nat.mul_pos (by norm_num) hd)]
    exact Nat.lt_succ_self _
  have hcL : c * (3 * d) ≤ rem := Nat.div_mul_le_self rem (3 * d)
  have hcU : rem < (c + 1) * (3 * d) := by
    rw [← Nat.div_lt_iff_lt_mul (Nat.mul_pos (by norm_num) hd)]
    exact Nat.lt_succ_self _
  have hresidual : (a : ℤ) - b - 2 * c = 0 ∨
      (a : ℤ) - b - 2 * c = 1 := by
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      norm_num at * <;> omega
  rw [oddMultipleBalance, oddMultipleBalance,
    Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  rw [show 3 * d = 3 * d by rfl,
    show 3 * (2 * d) = 6 * d by ring]
  rw [hdiv1, hdiv2, hdiv3, hdiv6]
  dsimp only [a, b, c] at hresidual
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rcases hresidual with hresidual | hresidual
  · left
    dsimp only [k]
    omega
  · right
    dsimp only [k]
    omega

lemma oddMultipleBalance_eq_card_singleton_two {d V : ℕ} (hd : 0 < d) :
    oddMultipleBalance d V =
      ((sifted ({2} : Finset ℕ) (V / d)).card : ℤ) := by
  rw [card_sifted_singleton_two, oddMultipleBalance,
    Nat.div_div_eq_div_mul]
  rw [show d * 2 = 2 * d by ring]
  have hle : V / (2 * d) ≤ V / d :=
    Nat.div_le_div_left (by omega) hd
  rw [Nat.cast_sub hle]

lemma cast_card_sifted_pair_two {q V : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    ((sifted ({2, q} : Finset ℕ) V).card : ℤ) =
      oddMultipleBalance 1 V - oddMultipleBalance q V := by
  have hprimeTwo : ∀ p ∈ ({2} : Finset ℕ), p.Prime := by
    intro p hp
    simpa [Finset.mem_singleton.mp hp] using (show (2 : ℕ).Prime by norm_num)
  have hsub : (sifted ({2} : Finset ℕ) (V / q)).card ≤
      (sifted ({2} : Finset ℕ) V).card :=
    Finset.card_le_card (sifted_mono_cutoff _ (Nat.div_le_self V q))
  have hbalanceOne : oddMultipleBalance 1 V =
      ((sifted ({2} : Finset ℕ) V).card : ℤ) := by
    simpa using oddMultipleBalance_eq_card_singleton_two
      (d := 1) (V := V) (by norm_num)
  have hbalanceQ : oddMultipleBalance q V =
      ((sifted ({2} : Finset ℕ) (V / q)).card : ℤ) :=
    oddMultipleBalance_eq_card_singleton_two hq.pos
  rw [show ({2, q} : Finset ℕ) = insert q {2} by
      ext a; simp [or_comm],
    card_sifted_insert hq (by simpa using hq2) hprimeTwo,
    Nat.cast_sub hsub,
    ← hbalanceOne, ← hbalanceQ]

lemma cast_card_sifted_triple_two {q r V : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hqr : q ≠ r) :
    ((sifted ({2, q, r} : Finset ℕ) V).card : ℤ) =
      oddMultipleBalance 1 V - oddMultipleBalance q V -
        oddMultipleBalance r V + oddMultipleBalance (q * r) V := by
  have hpairPrime : ∀ p ∈ ({2, q} : Finset ℕ), p.Prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · norm_num
    · exact hq
  have hrpair : r ∉ ({2, q} : Finset ℕ) := by
    simp [hr2, hqr.symm]
  have hsub : (sifted ({2, q} : Finset ℕ) (V / r)).card ≤
      (sifted ({2, q} : Finset ℕ) V).card :=
    Finset.card_le_card (sifted_mono_cutoff _ (Nat.div_le_self V r))
  rw [show ({2, q, r} : Finset ℕ) = insert r {2, q} by
      ext a; simp [or_assoc, or_comm, or_left_comm],
    card_sifted_insert hr hrpair hpairPrime,
    Nat.cast_sub hsub,
    cast_card_sifted_pair_two hq hq2,
    cast_card_sifted_pair_two hq hq2]
  simp only [oddMultipleBalance, Nat.div_div_eq_div_mul]
  congr 1 <;> ring_nf

lemma cast_natDiv_lt_add_one (a b : ℕ) (hb : 0 < b) :
    (a : ℚ) / b < ((a / b : ℕ) : ℚ) + 1 := by
  apply (div_lt_iff₀ (by exact_mod_cast hb : (0 : ℚ) < b)).2
  have hnat : a < (a / b + 1) * b := by
    rw [← Nat.div_lt_iff_lt_mul hb]
    exact Nat.lt_succ_self _
  exact_mod_cast hnat

lemma three_le_floor_six_sub_two_floors {q r V : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq3 : 3 < q) (hr3 : 3 < r)
    (hqr : q ≠ r) (hV : q * r ≤ V) :
    3 ≤ ((V / 6 : ℕ) : ℤ) - (V / (6 * q) : ℕ) -
      (V / (6 * r) : ℕ) := by
  have hq5 : 5 ≤ q := by
    by_contra h
    interval_cases q <;> norm_num at hq
  have hr5 : 5 ≤ r := by
    by_contra h
    interval_cases r <;> norm_num at hr
  have hgap : q + r + 23 ≤ q * r := by
    rcases lt_or_gt_of_ne hqr with hlt | hgt
    · have hqOdd := hq.odd_of_ne_two (by omega)
      have hrOdd := hr.odd_of_ne_two (by omega)
      rcases hqOdd with ⟨a, ha⟩
      rcases hrOdd with ⟨b, hb⟩
      have : q + 2 ≤ r := by omega
      nlinarith
    · have hqOdd := hq.odd_of_ne_two (by omega)
      have hrOdd := hr.odd_of_ne_two (by omega)
      rcases hqOdd with ⟨a, ha⟩
      rcases hrOdd with ⟨b, hb⟩
      have : r + 2 ≤ q := by omega
      nlinarith
  have hdiff : 23 ≤ q * r - q - r := by omega
  have hmul : 18 * (q * r) < V * (q * r - q - r) := by
    calc
      18 * (q * r) < 23 * (q * r) := by
        have : 0 < q * r := Nat.mul_pos hq.pos hr.pos
        nlinarith
      _ = (q * r) * 23 := by ring
      _ ≤ V * (q * r - q - r) := Nat.mul_le_mul hV hdiff
  have hmulSub : q ≤ q * r := by
    simpa using Nat.mul_le_mul_left q hr.one_le
  have hrSub : r ≤ q * r - q := by
    omega
  have hdiffCast : (((q * r - q - r : ℕ) : ℚ)) =
      (q : ℚ) * r - q - r := by
    rw [Nat.cast_sub hrSub, Nat.cast_sub hmulSub, Nat.cast_mul]
  have hratio : (3 : ℚ) <
      (V : ℚ) / 6 - (V : ℚ) / (6 * q) - (V : ℚ) / (6 * r) := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
    have hden : (0 : ℚ) < 6 * q * r := by positivity
    rw [show (V : ℚ) / 6 - (V : ℚ) / (6 * q) -
        (V : ℚ) / (6 * r) =
        (V * ((q * r - q - r : ℕ) : ℚ)) / (6 * q * r) by
          rw [hdiffCast]
          field_simp
          ring]
    apply (lt_div_iff₀ hden).2
    norm_num only [Nat.cast_ofNat]
    have hmulQ : (((18 * (q * r) : ℕ) : ℚ)) <
        (V : ℚ) * ((q * r - q - r : ℕ) : ℚ) := by
      exact_mod_cast hmul
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hmulQ
    rw [show (3 : ℚ) * (6 * q * r) = 18 * (q * r) by ring]
    exact hmulQ
  have hfloor : (V : ℚ) / 6 < ((V / 6 : ℕ) : ℚ) + 1 :=
    cast_natDiv_lt_add_one V 6 (by norm_num)
  have hqfloor : ((V / (6 * q) : ℕ) : ℚ) ≤
      (V : ℚ) / (6 * q) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_div_le (α := ℚ) (m := V) (n := 6 * q))
  have hrfloor : ((V / (6 * r) : ℕ) : ℚ) ≤
      (V : ℚ) / (6 * r) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_div_le (α := ℚ) (m := V) (n := 6 * r))
  have hmainQ : (2 : ℚ) <
      ((V / 6 : ℕ) : ℚ) - ((V / (6 * q) : ℕ) : ℚ) -
        ((V / (6 * r) : ℕ) : ℚ) := by
    linarith
  have hmainZ : (2 : ℤ) <
      ((V / 6 : ℕ) : ℤ) - (V / (6 * q) : ℕ) -
        (V / (6 * r) : ℕ) := by
    have hmainZQ : (((2 : ℤ) : ℚ)) <
        ((((V / 6 : ℕ) : ℤ) - (V / (6 * q) : ℕ) -
          (V / (6 * r) : ℕ) : ℤ) : ℚ) := by
      norm_num only [Int.cast_ofNat, Int.cast_sub]
      exact hmainQ
    exact_mod_cast hmainZQ
  omega

theorem card_sifted_triple_two_doubling_three {q r V : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq3 : 3 < q) (hr3 : 3 < r)
    (hqr : q ≠ r) (hV : q * r ≤ V) :
    2 * (sifted ({2, q, r} : Finset ℕ) (V / 3)).card ≤
      (sifted ({2, q, r} : Finset ℕ) V).card := by
  have hq2 : q ≠ 2 := by omega
  have hr2 : r ≠ 2 := by omega
  have hbase := three_le_floor_six_sub_two_floors hq hr hq3 hr3 hqr hV
  have h1 := oddMultipleBalance_scale_three (d := 1) (V := V) (by norm_num)
  have hqBal := oddMultipleBalance_scale_three (d := q) (V := V) hq.pos
  have hrBal := oddMultipleBalance_scale_three (d := r) (V := V) hr.pos
  have hqrBal := oddMultipleBalance_scale_three (d := q * r) (V := V)
    (Nat.mul_pos hq.pos hr.pos)
  have hlastNonneg : (0 : ℤ) ≤ ((V / (6 * (q * r)) : ℕ) : ℤ) := by
    positivity
  have hhigh := cast_card_sifted_triple_two hq hr hq2 hr2 hqr (V := V)
  have hlow := cast_card_sifted_triple_two hq hr hq2 hr2 hqr (V := V / 3)
  have hnonneg : (0 : ℤ) ≤
      ((sifted ({2, q, r} : Finset ℕ) V).card : ℤ) -
        2 * ((sifted ({2, q, r} : Finset ℕ) (V / 3)).card : ℤ) := by
    rw [hhigh, hlow]
    rcases h1 with h1 | h1 <;>
      rcases hqBal with hqBal | hqBal <;>
      rcases hrBal with hrBal | hrBal <;>
      rcases hqrBal with hqrBal | hqrBal <;>
      omega
  exact_mod_cast (sub_nonneg.mp hnonneg)

def multipleBalance (d V : ℕ) : ℤ := ((V / d : ℕ) : ℤ)

lemma multipleBalance_scale_three {d V : ℕ} (hd : 0 < d) :
    multipleBalance d V - 2 * multipleBalance d (V / 3) =
        ((V / (3 * d) : ℕ) : ℤ) ∨
      multipleBalance d V - 2 * multipleBalance d (V / 3) =
        ((V / (3 * d) : ℕ) : ℤ) + 1 ∨
      multipleBalance d V - 2 * multipleBalance d (V / 3) =
        ((V / (3 * d) : ℕ) : ℤ) + 2 := by
  let k := V / (3 * d)
  let rem := V % (3 * d)
  have hthreed : 0 < 3 * d := Nat.mul_pos (by norm_num) hd
  have hrem : rem < 3 * d := Nat.mod_lt V hthreed
  have hdecomp : d * (3 * k) + rem = V := by
    have h := (Nat.div_add_mod V (3 * d)).symm
    dsimp only [k, rem]
    nlinarith
  have hdiv1 : V / d = 3 * k + rem / d := by
    rw [← hdecomp]
    exact Nat.mul_add_div hd (3 * k) rem
  have hdiv3 : V / (3 * d) = k := by rfl
  have ha3 : rem / d < 3 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    exact hrem
  rw [multipleBalance, multipleBalance, Nat.div_div_eq_div_mul]
  rw [show 3 * d = 3 * d by rfl, hdiv1, hdiv3]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  interval_cases rem / d <;> omega

lemma cast_card_sifted_pair {q r V : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    ((sifted ({q, r} : Finset ℕ) V).card : ℤ) =
      multipleBalance 1 V - multipleBalance q V -
        multipleBalance r V + multipleBalance (q * r) V := by
  have hqEmpty : q ∉ (∅ : Finset ℕ) := by simp
  have hEmptyPrime : ∀ p ∈ (∅ : Finset ℕ), p.Prime := by simp
  have hqSetPrime : ∀ p ∈ ({q} : Finset ℕ), p.Prime := by
    intro p hp
    simpa [Finset.mem_singleton.mp hp] using hq
  have hrSet : r ∉ ({q} : Finset ℕ) := by simpa [hqr.symm]
  have hsubEmpty : (sifted (∅ : Finset ℕ) (V / q)).card ≤
      (sifted (∅ : Finset ℕ) V).card :=
    Finset.card_le_card (sifted_mono_cutoff _ (Nat.div_le_self V q))
  have hsubEmptyR : (sifted (∅ : Finset ℕ) ((V / r) / q)).card ≤
      (sifted (∅ : Finset ℕ) (V / r)).card :=
    Finset.card_le_card (sifted_mono_cutoff _ (Nat.div_le_self (V / r) q))
  have hsubQ : (sifted ({q} : Finset ℕ) (V / r)).card ≤
      (sifted ({q} : Finset ℕ) V).card :=
    Finset.card_le_card (sifted_mono_cutoff _ (Nat.div_le_self V r))
  rw [show ({q, r} : Finset ℕ) = insert r {q} by
      ext a; simp [or_comm],
    card_sifted_insert hr hrSet hqSetPrime,
    Nat.cast_sub hsubQ,
    show ({q} : Finset ℕ) = insert q ∅ by simp,
    card_sifted_insert hq hqEmpty hEmptyPrime,
    card_sifted_insert hq hqEmpty hEmptyPrime,
    Nat.cast_sub hsubEmpty, Nat.cast_sub hsubEmptyR]
  rw [card_sifted_empty, card_sifted_empty, card_sifted_empty,
    card_sifted_empty]
  simp only [multipleBalance, Nat.div_div_eq_div_mul, Nat.div_one]
  ring_nf

lemma four_le_floor_three_sub_two_floors {q r V : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq3 : 3 < q) (hr3 : 3 < r)
    (hqr : q ≠ r) (hV : q * r ≤ 2 * V + 1) :
    4 ≤ V / 3 - V / (3 * q) - V / (3 * r) := by
  have hq5 : 5 ≤ q := by
    by_contra h
    interval_cases q <;> norm_num at hq
  have hr5 : 5 ≤ r := by
    by_contra h
    interval_cases r <;> norm_num at hr
  let A := V / 3
  have hVdecomp : V ≤ 3 * A + 2 := by
    have hmod := Nat.mod_lt V (by norm_num : 0 < 3)
    have hdecomp := Nat.div_add_mod V 3
    dsimp only [A]
    omega
  have hprod35 : 35 ≤ q * r := by
    rcases lt_or_gt_of_ne hqr with hlt | hgt
    · have hqOdd := hq.odd_of_ne_two (by omega)
      have hrOdd := hr.odd_of_ne_two (by omega)
      rcases hqOdd with ⟨a, ha⟩
      rcases hrOdd with ⟨b, hb⟩
      have : 7 ≤ r := by omega
      exact Nat.mul_le_mul hq5 this
    · have hqOdd := hq.odd_of_ne_two (by omega)
      have hrOdd := hr.odd_of_ne_two (by omega)
      rcases hqOdd with ⟨a, ha⟩
      rcases hrOdd with ⟨b, hb⟩
      have : 7 ≤ q := by omega
      exact Nat.mul_le_mul this hr5
  have hA5 : 5 ≤ A := by
    nlinarith
  have hconst : A / 5 + A / 7 + 4 ≤ A := by omega
  have hrewriteQ : V / (3 * q) = A / q := by
    dsimp only [A]
    rw [Nat.div_div_eq_div_mul]
  have hrewriteR : V / (3 * r) = A / r := by
    dsimp only [A]
    rw [Nat.div_div_eq_div_mul]
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · have hqOdd := hq.odd_of_ne_two (by omega)
    have hrOdd := hr.odd_of_ne_two (by omega)
    rcases hqOdd with ⟨a, ha⟩
    rcases hrOdd with ⟨b, hb⟩
    have hr7 : 7 ≤ r := by omega
    have hB : A / q ≤ A / 5 := Nat.div_le_div_left hq5 (by norm_num)
    have hC : A / r ≤ A / 7 := Nat.div_le_div_left hr7 (by norm_num)
    rw [hrewriteQ, hrewriteR]
    omega
  · have hqOdd := hq.odd_of_ne_two (by omega)
    have hrOdd := hr.odd_of_ne_two (by omega)
    rcases hqOdd with ⟨a, ha⟩
    rcases hrOdd with ⟨b, hb⟩
    have hq7 : 7 ≤ q := by omega
    have hB : A / q ≤ A / 7 := Nat.div_le_div_left hq7 (by norm_num)
    have hC : A / r ≤ A / 5 := Nat.div_le_div_left hr5 (by norm_num)
    rw [hrewriteQ, hrewriteR]
    omega

theorem card_sifted_pair_doubling_three {q r V : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq3 : 3 < q) (hr3 : 3 < r)
    (hqr : q ≠ r) (hV : q * r ≤ 2 * V + 1) :
    2 * (sifted ({q, r} : Finset ℕ) (V / 3)).card ≤
      (sifted ({q, r} : Finset ℕ) V).card := by
  have hbase := four_le_floor_three_sub_two_floors hq hr hq3 hr3 hqr hV
  have h1 := multipleBalance_scale_three (d := 1) (V := V) (by norm_num)
  have hqBal := multipleBalance_scale_three (d := q) (V := V) hq.pos
  have hrBal := multipleBalance_scale_three (d := r) (V := V) hr.pos
  have hqrBal := multipleBalance_scale_three (d := q * r) (V := V)
    (Nat.mul_pos hq.pos hr.pos)
  have hlastNonneg : (0 : ℤ) ≤ ((V / (3 * (q * r)) : ℕ) : ℤ) := by
    positivity
  have hhigh := cast_card_sifted_pair hq hr hqr (V := V)
  have hlow := cast_card_sifted_pair hq hr hqr (V := V / 3)
  have hnonneg : (0 : ℤ) ≤
      ((sifted ({q, r} : Finset ℕ) V).card : ℤ) -
        2 * ((sifted ({q, r} : Finset ℕ) (V / 3)).card : ℤ) := by
    rw [hhigh, hlow]
    rcases h1 with h1 | h1 <;>
      rcases hqBal with hqBal | hqBal <;>
      rcases hrBal with hrBal | hrBal <;>
      rcases hqrBal with hqrBal | hqrBal <;>
      omega
  exact_mod_cast (sub_nonneg.mp hnonneg)

lemma oneBasedPrime_eq_of_primeCounting {p s : ℕ}
    (hp : p.Prime) (hcount : Nat.primeCounting p = s) :
    p = oneBasedPrime s := by
  have hsucc : Nat.count Nat.Prime p + 1 = s := by
    rw [Nat.primeCounting_eq_primeCounting'_succ,
      Nat.primeCounting', Nat.count_succ, if_pos hp] at hcount
    exact hcount
  rw [oneBasedPrime, ← show Nat.count Nat.Prime p = s - 1 by omega]
  exact (Nat.nth_count hp).symm

lemma scaled_signature_cutoff_le {N r : ℕ} {S : Finset ℕ}
    (hrS : r ∈ S) (hSprime : ∀ p ∈ S, p.Prime) :
    r * (N / ∏ p ∈ S, p) ≤ N / ∏ p ∈ S.erase r, p := by
  let B := ∏ p ∈ S.erase r, p
  have hBpos : 0 < B := signature_prod_pos fun p hp ↦
    hSprime p (Finset.mem_of_mem_erase hp)
  have hprod : B * r = ∏ p ∈ S, p :=
    Finset.prod_erase_mul S id hrS
  apply (Nat.le_div_iff_mul_le hBpos).2
  calc
    r * (N / ∏ p ∈ S, p) * B =
        (∏ p ∈ S, p) * (N / ∏ p ∈ S, p) := by
      rw [← hprod]
      ring
    _ ≤ N := Nat.mul_div_le N _

lemma card_sifted_signature_doubling
    {N r : ℕ} {S : Finset ℕ}
    (hN : N ≠ 0) (hr : r.Prime) (hr3 : 3 ≤ r)
    (hrS : r ∈ S) (hSscope : S ⊆ coreScope N r) :
    2 * (sifted (signatureForbidden N r S)
      (N / ∏ p ∈ S, p)).card ≤
      (sifted (signatureForbidden N r S)
        (N / ∏ p ∈ S.erase r, p)).card := by
  classical
  let T := signatureForbidden N r S
  let d := ∏ p ∈ S, p
  let B := ∏ p ∈ S.erase r, p
  change 2 * (sifted T (N / d)).card ≤ (sifted T (N / B)).card
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp ↦
    prime_of_mem_coreScope (hSscope hp)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp ↦
    prime_of_mem_coreScope (mem_signatureForbidden.mp hp).1
  have hrT : r ∉ T := by
    intro h
    exact (mem_signatureForbidden.mp h).2 hrS
  have hdpos : 0 < d := signature_prod_pos hSprime
  have hBpos : 0 < B := signature_prod_pos fun p hp ↦
    hSprime p (Finset.mem_of_mem_erase hp)
  have hprod : B * r = d := by
    exact Finset.prod_erase_mul S id hrS
  have hscale : r * (N / d) ≤ N / B := by
    exact scaled_signature_cutoff_le hrS hSprime
  have hscaleMul : r * N / d = N / B := by
    rw [← hprod, mul_comm r N]
    exact Nat.mul_div_mul_right N B hr.pos
  have hcover : d * (∏ q ∈ T, q) ≤
      N * (∏ q ∈ Nat.primesLE r, q) :=
    signature_product_cover hN hSscope
  by_cases hrEq : r = 3
  · subst r
    have hthree : (3 : ℕ).Prime := by norm_num
    have hlow : N / d = (N / B) / 3 := by
      rw [Nat.div_div_eq_div_mul, hprod]
    let C := T.filter fun q ↦ 3 < q
    have hTCases : ∀ q ∈ T, q = 2 ∨ q ∈ C := by
      intro q hq
      by_cases hq3 : 3 < q
      · exact Or.inr (Finset.mem_filter.mpr ⟨hq, hq3⟩)
      · left
        have hqPrime := hTprime q hq
        have hqTwo := hqPrime.two_le
        have hqne3 : q ≠ 3 := by
          intro h
          exact hrT (h ▸ hq)
        omega
    have hTInsert (h2 : 2 ∈ T) : T = insert 2 C := by
      ext q
      constructor
      · intro hq
        rcases hTCases q hq with rfl | hqC
        · simp
        · exact Finset.mem_insert_of_mem hqC
      · intro hq
        rcases Finset.mem_insert.mp hq with rfl | hqC
        · exact h2
        · exact (Finset.mem_filter.mp hqC).1
    have hTEq (h2 : 2 ∉ T) : T = C := by
      ext q
      constructor
      · intro hq
        rcases hTCases q hq with rfl | hqC
        · exact (h2 hq).elim
        · exact hqC
      · exact fun hq ↦ (Finset.mem_filter.mp hq).1
    by_cases hmany : 3 ≤ C.card
    · have hdensity := card_sifted_quotient_doubling_three_of_three_large
          hTprime hdpos hrT hmany hcover
      exact hdensity.trans (Finset.card_le_card
        (sifted_mono_cutoff T hscaleMul.le))
    · have hcardLe : C.card ≤ 2 := by omega
      have hcardCases : C.card = 0 ∨ C.card = 1 ∨ C.card = 2 := by omega
      rcases hcardCases with hzero | hone | htwo
      · have hC : C = ∅ := Finset.card_eq_zero.mp hzero
        by_cases h2 : 2 ∈ T
        · have hT : T = ({2} : Finset ℕ) := by simpa [hC] using hTInsert h2
          rw [hT, hlow, card_sifted_singleton_two,
            card_sifted_singleton_two]
          omega
        · have hT : T = ∅ := by simpa [hC] using hTEq h2
          simp [hT, hlow]
          have hmul := Nat.mul_div_le (N / B) 3
          omega
      · obtain ⟨q, hC⟩ := Finset.card_eq_one.mp hone
        have hqC : q ∈ C := by simp [hC]
        have hqPrime : q.Prime := hTprime q (Finset.mem_filter.mp hqC).1
        have hq3 : 3 < q := (Finset.mem_filter.mp hqC).2
        let V := N / B
        have hhighMono : 3 * (V / 3) ≤ V := Nat.mul_div_le V 3
        by_cases h2 : 2 ∈ T
        · have hT : T = ({2, q} : Finset ℕ) := by
            simpa [hC] using hTInsert h2
          rw [hT, hlow]
          exact (card_sifted_pair_two_three_doubling hqPrime hq3).trans
            (Finset.card_le_card (sifted_mono_cutoff _ hhighMono))
        · have hT : T = ({q} : Finset ℕ) := by simpa [hC] using hTEq h2
          have hq2 : q ≠ 2 := by omega
          have hdelete : ∀ U,
              2 * (sifted ({q} : Finset ℕ) U).card ≤
                (sifted ({q} : Finset ℕ) (3 * U)).card := by
            apply card_sifted_doubling_of_insert_small hthree
              (show (2 : ℕ).Prime by norm_num) (by
                simp only [Finset.mem_singleton]
                exact hq2.symm)
              (by intro a ha; simpa [Finset.mem_singleton.mp ha] using hqPrime)
            intro U
            simpa [Finset.pair_comm] using
              card_sifted_pair_two_three_doubling (q := q) (U := U)
                hqPrime hq3
          rw [hT, hlow]
          exact (hdelete (V / 3)).trans
            (Finset.card_le_card (sifted_mono_cutoff _ hhighMono))
      · obtain ⟨q, r, hqr, hC⟩ := Finset.card_eq_two.mp htwo
        have hqC : q ∈ C := by simp [hC]
        have hrC : r ∈ C := by simp [hC]
        have hqPrime : q.Prime := hTprime q (Finset.mem_filter.mp hqC).1
        have hrPrime : r.Prime := hTprime r (Finset.mem_filter.mp hrC).1
        have hq3 : 3 < q := (Finset.mem_filter.mp hqC).2
        have hr3' : 3 < r := (Finset.mem_filter.mp hrC).2
        let V := N / B
        by_cases h2 : 2 ∈ T
        · have hT : T = ({2, q, r} : Finset ℕ) := by
            simpa [hC, hqr] using hTInsert h2
          have hq2 : q ≠ 2 := by omega
          have hr2 : r ≠ 2 := by omega
          have hprodT : (∏ a ∈ ({2, q, r} : Finset ℕ), a) =
              2 * (q * r) := by
            simp [hqr, hqr.symm, hq2, hq2.symm, hr2, hr2.symm]
          have hprim : (∏ a ∈ Nat.primesLE 3, a) = 6 := by decide
          have hsharp : B * (q * r) ≤ N := by
            have hc := hcover
            rw [← hprod, hT] at hc
            rw [hprodT, hprim] at hc
            nlinarith
          have hV : q * r ≤ V :=
            (Nat.le_div_iff_mul_le hBpos).2 (by
              simpa only [mul_assoc, mul_comm, mul_left_comm] using hsharp)
          rw [hT, hlow]
          exact card_sifted_triple_two_doubling_three
            hqPrime hrPrime hq3 hr3' hqr hV
        · have hT : T = ({q, r} : Finset ℕ) := by
            simpa [hC] using hTEq h2
          have hprodT : (∏ a ∈ ({q, r} : Finset ℕ), a) = q * r := by
            simp [hqr, hqr.symm]
          have hprim : (∏ a ∈ Nat.primesLE 3, a) = 6 := by decide
          have hsharp : B * (q * r) ≤ 2 * N := by
            have hc := hcover
            rw [← hprod, hT] at hc
            rw [hprodT, hprim] at hc
            nlinarith
          have hquot : q * r ≤ (2 * N) / B :=
            (Nat.le_div_iff_mul_le hBpos).2 (by
              simpa only [mul_assoc, mul_comm, mul_left_comm] using hsharp)
          have htwoDiv : (2 * N) / B ≤ 2 * V + 1 := by
            apply Nat.lt_succ_iff.mp
            rw [Nat.div_lt_iff_lt_mul hBpos]
            have hmod := Nat.mod_lt N hBpos
            have hdecomp := Nat.div_add_mod N B
            dsimp only [V]
            nlinarith
          have hV : q * r ≤ 2 * V + 1 := hquot.trans htwoDiv
          rw [hT, hlow]
          exact card_sifted_pair_doubling_three
            hqPrime hrPrime hq3 hr3' hqr hV
  · have hr5 : 5 ≤ r := by
      have hrOdd := hr.odd_of_ne_two (by omega)
      rcases hrOdd with ⟨a, ha⟩
      omega
    let s := Nat.primeCounting r
    let rho := (T.filter fun q ↦ r < q).card
    have hs : 3 ≤ s := by
      have hmono := Nat.monotone_primeCounting hr5
      have hfive : Nat.primeCounting 5 = 3 := by decide
      dsimp only [s]
      omega
    have hpValue : r = oneBasedPrime s :=
      oneBasedPrime_eq_of_primeCounting hr rfl
    by_cases hsmall : rho ≤ 2 * s - 1
    · have hexpand : PrimeIntervalExpansion T r :=
        primeIntervalExpansion_of_small_rho hs hr rfl hpValue (by rfl) hsmall
      have hdouble := card_sifted_doubling_of_primeIntervalExpansion_general
        hr hrT hTprime hexpand (U := N / d)
      exact hdouble.trans (Finset.card_le_card
        (sifted_mono_cutoff T hscale))
    · have hmany : 2 * s ≤ (T.filter fun q ↦ r < q).card := by
        dsimp only [rho] at hsmall
        omega
      have hdouble := card_sifted_quotient_doubling_of_many_large_primes
        hTprime hdpos hr hrT rfl hs hmany hcover
      exact hdouble.trans (Finset.card_le_card
        (sifted_mono_cutoff T hscaleMul.le))

end Erdos534
