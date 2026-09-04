import ErdosProblems.Erdos587.RootDensity

/-!
# Complete square-root counts

The zero-modulus value is a harmless convention. Positive moduli are counted
in `ZMod`, and the Chinese remainder theorem gives exact multiplicativity.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def squareRootCount (q n : ℕ) : ℕ := by
  classical
  exact if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    Fintype.card {z : ZMod q // z ^ 2 = (n : ZMod q)}

lemma squareRootCount_eq_card (q n : ℕ) [NeZero q] :
    squareRootCount q n = Fintype.card {z : ZMod q // z ^ 2 = (n : ZMod q)} := by
  classical
  simp only [squareRootCount, dif_neg (NeZero.ne q)]

lemma squareRootCount_one (n : ℕ) : squareRootCount 1 n = 1 := by
  classical
  rw [squareRootCount_eq_card]
  have h : ∀ z : ZMod 1, z ^ 2 = (n : ZMod 1) := fun _ => Subsingleton.elim _ _
  simp [h]

lemma squareRootCount_pos_of_isSquare {q n : ℕ} [NeZero q]
    (hsq : IsSquare (n : ZMod q)) : 0 < squareRootCount q n := by
  classical
  rw [squareRootCount_eq_card, Fintype.card_pos_iff]
  obtain ⟨z, hz⟩ := hsq
  exact ⟨⟨z, by simpa only [pow_two] using hz.symm⟩⟩

noncomputable def squareRootCRTEquiv (m n a : ℕ) [NeZero m] [NeZero n]
    (hcop : m.Coprime n) :
    {z : ZMod (m * n) // z ^ 2 = (a : ZMod (m * n))} ≃
      ({x : ZMod m // x ^ 2 = (a : ZMod m)} × {y : ZMod n // y ^ 2 = (a : ZMod n)}) := by
  let e := ZMod.chineseRemainder hcop
  refine
    { toFun := fun z => (⟨(e z.val).1, ?_⟩, ⟨(e z.val).2, ?_⟩)
      invFun := fun w => ⟨e.symm (w.1.val, w.2.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hz := congrArg e z.property
    simpa using congrArg (RingHom.fst (ZMod m) (ZMod n)) hz
  · have hz := congrArg e z.property
    simpa using congrArg (RingHom.snd (ZMod m) (ZMod n)) hz
  · apply e.injective
    rw [map_pow, e.apply_symm_apply, map_natCast]
    exact Prod.ext w.1.property w.2.property
  · intro z
    apply Subtype.ext
    exact e.symm_apply_apply z.val
  · intro w
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (e.apply_symm_apply (w.1.val, w.2.val))
    · exact congrArg Prod.snd (e.apply_symm_apply (w.1.val, w.2.val))

lemma squareRootCount_mul (m n a : ℕ) [NeZero m] [NeZero n] (hcop : m.Coprime n) :
    squareRootCount (m * n) a = squareRootCount m a * squareRootCount n a := by
  classical
  rw [squareRootCount_eq_card, squareRootCount_eq_card, squareRootCount_eq_card]
  exact (Fintype.card_congr (squareRootCRTEquiv m n a hcop)).trans (Fintype.card_prod _ _)

lemma two_le_squareRootCount_of_unit_square {q n : ℕ} [NeZero q]
    (hq : 1 < q) (h2 : (2 : ℕ).Coprime q) (hn : n.Coprime q)
    (hsq : IsSquare (n : ZMod q)) : 2 ≤ squareRootCount q n := by
  classical
  let : Fact (1 < q) := ⟨hq⟩
  have h2unit : IsUnit (2 : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr h2
  have hnunit : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
  obtain ⟨z, hz⟩ := hsq
  have hzsq : z ^ 2 = (n : ZMod q) := by simpa only [pow_two] using hz.symm
  have hzneg : (-z) ^ 2 = (n : ZMod q) := by rw [neg_sq, hzsq]
  have hne : z ≠ -z := by
    intro heq
    have hh : (2 : ZMod q) * z = 0 := by linear_combination heq
    have hz0 : z = 0 := h2unit.mul_left_cancel (by simpa only [mul_zero] using hh)
    apply hnunit.ne_zero
    rw [← hzsq, hz0, zero_pow (by norm_num : 2 ≠ 0)]
  rw [squareRootCount_eq_card]
  exact Fintype.one_lt_card_iff.mpr
    ⟨⟨z, hzsq⟩, ⟨-z, hzneg⟩, fun heq => hne (congrArg Subtype.val heq)⟩

lemma squareRootCount_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (m : ι → ℕ) (a : ℕ) (hpos : ∀ i ∈ s, 0 < m i)
    (hpair : Set.Pairwise (s : Set ι) fun i j => (m i).Coprime (m j)) :
    squareRootCount (∏ i ∈ s, m i) a = ∏ i ∈ s, squareRootCount (m i) a := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, squareRootCount_one]
  | @insert i s hi ih =>
    have hpos' : ∀ j ∈ s, 0 < m j := fun j hj => hpos j (Finset.mem_insert_of_mem hj)
    have hmi : 0 < m i := hpos i (Finset.mem_insert_self i s)
    have hspos : 0 < ∏ j ∈ s, m j := Finset.prod_pos hpos'
    let : NeZero (m i) := ⟨hmi.ne'⟩
    let : NeZero (∏ j ∈ s, m j) := ⟨hspos.ne'⟩
    rw [Finset.coe_insert, Set.pairwise_insert] at hpair
    have hcop : (m i).Coprime (∏ j ∈ s, m j) :=
      Nat.Coprime.prod_right (fun j hj =>
        (hpair.2 j hj (ne_of_mem_of_not_mem hj hi).symm).1)
    rw [Finset.prod_insert hi, squareRootCount_mul _ _ _ hcop,
      ih hpos' hpair.1, Finset.prod_insert hi]

lemma two_pow_primeFactors_le_squareRootCount {q n : ℕ} [NeZero q]
    (hodd : ∀ p ∈ q.primeFactors, p ≠ 2) (hn : n.Coprime q)
    (hsq : IsSquare (n : ZMod q)) : 2 ^ q.primeFactors.card ≤ squareRootCount q n := by
  let m : ℕ → ℕ := fun p => p ^ q.factorization p
  have hq : q ≠ 0 := NeZero.ne q
  have hpos : ∀ p ∈ q.primeFactors, 0 < m p := fun p hp =>
    pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hpair : Set.Pairwise (q.primeFactors : Set ℕ) fun p r => (m p).Coprime (m r) := by
    intro p hp r hr hpr
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hr)).mpr hpr).pow _ _
  have hproduct : (∏ p ∈ q.primeFactors, m p) = q :=
    (Nat.prod_primeFactors_pow_factorization hq).symm
  have hlocal : ∀ p ∈ q.primeFactors, 2 ≤ squareRootCount (m p) n := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have he : 0 < q.factorization p := by
      apply Nat.pos_of_ne_zero
      simpa only [← Finsupp.mem_support_iff, Nat.support_factorization] using hp
    have hpowge : p ≤ m p := by
      change p ≤ p ^ q.factorization p
      calc
        p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ q.factorization p := pow_le_pow_right₀ hprime.pos he
    have hm1 : 1 < m p := hprime.one_lt.trans_le hpowge
    let : NeZero (m p) := ⟨(hpos p hp).ne'⟩
    have hmdvd : m p ∣ q := by
      rw [← hproduct]
      exact Finset.dvd_prod_of_mem m hp
    have h2 : (2 : ℕ).Coprime (m p) :=
      ((Nat.coprime_primes Nat.prime_two hprime).mpr (hodd p hp).symm).pow_right _
    have hlocalSquare : IsSquare (n : ZMod (m p)) := by
      obtain ⟨z, hz⟩ := hsq
      let f := ZMod.castHom hmdvd (ZMod (m p))
      refine ⟨f z, ?_⟩
      have hh := congrArg f hz
      simpa only [map_natCast, map_mul] using hh
    exact two_le_squareRootCount_of_unit_square hm1 h2 (hn.of_dvd_right hmdvd) hlocalSquare
  calc
    2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ q.primeFactors, squareRootCount (m p) n :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hlocal
    _ = squareRootCount (∏ p ∈ q.primeFactors, m p) n :=
      (squareRootCount_prod q.primeFactors m n hpos hpair).symm
    _ = squareRootCount q n := by rw [hproduct]

lemma unitSquareExpansionValue_le_squareRootCount_odd {q : ℕ} [NeZero q]
    (hodd : ∀ p ∈ q.primeFactors, p ≠ 2) (n : ℕ) :
    unitSquareExpansionValue (primeSetModulus q.primeFactors) n ≤ (squareRootCount q n : ℝ) := by
  classical
  have hprime : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  by_cases h : n.Coprime (primeSetModulus q.primeFactors) ∧
      IsSquare (n : ZMod (primeSetModulus q.primeFactors))
  · rw [unitSquareExpansionValue, if_pos h, primeFactors_primeSetModulus q.primeFactors hprime]
    have hn : n.Coprime q := by
      rw [Nat.prod_primeFactors_pow_factorization (NeZero.ne q)]
      exact Nat.Coprime.prod_right fun p hp =>
        (h.1.of_dvd_right (dvd_primeSetModulus hp)).pow_right _
    exact_mod_cast two_pow_primeFactors_le_squareRootCount hodd hn
      (isSquare_zmod_of_coprime_square_primeSet (NeZero.ne q) hodd h.1 h.2)
  · simp only [unitSquareExpansionValue, if_neg h]
    exact Nat.cast_nonneg _

theorem exists_large_radical_odd_root_density_threshold :
    ∃ Q₀ : ℕ, ∀ (q : ℕ), 0 < q → (∀ p ∈ q.primeFactors, p ≠ 2) →
      Q₀ ≤ primeSetModulus q.primeFactors →
      ∀ (D R M H : ℕ), R.Coprime (primeSetModulus q.primeFactors) →
        D ≡ R * M [MOD primeSetModulus q.primeFactors] → 0 < H →
        (primeSetModulus q.primeFactors : ℝ) ≤ (H : ℝ) ^ 2 →
        (H : ℝ) * primeSetUnitDensity q.primeFactors / 2 ≤
          ∑ i ∈ Finset.range H, (squareRootCount q (D + R * i) : ℝ) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_unitSquareAffineDensityThreshold
  refine ⟨Q₀, ?_⟩
  intro q hq hodd hQ D R M H hR hDM hH hroot
  let : NeZero q := ⟨hq.ne'⟩
  apply (hQ₀ q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    hodd hQ D R M H hR hDM hH hroot).trans
  exact Finset.sum_le_sum (fun i hi => unitSquareExpansionValue_le_squareRootCount_odd hodd _)

lemma squareRootCount_two_pow_pos_of_modEq_eight (e n : ℕ)
    (hn : n ≡ 1 [MOD 8]) : 0 < squareRootCount (2 ^ e) n := by
  let : NeZero (2 ^ e) := ⟨by positivity⟩
  apply squareRootCount_pos_of_isSquare
  have hnZ : (n : ℤ) ≡ 1 [ZMOD (8 : ℤ)] := by exact_mod_cast hn
  obtain ⟨z, hz⟩ := exists_square_modEq_two_pow_of_modEq_eight e hnZ
  refine ⟨(z : ZMod (2 ^ e)), ?_⟩
  have hzcast := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hz
  simpa only [Int.cast_natCast, Int.cast_pow, pow_two, Int.cast_mul] using hzcast

lemma unitSquareExpansionValue_le_squareRootCount_two_mul_odd
    (e Q n : ℕ) (hQ : 0 < Q) (hodd : ∀ p ∈ Q.primeFactors, p ≠ 2)
    (h2 : (2 : ℕ).Coprime Q) (hn : n ≡ 1 [MOD 8]) :
    unitSquareExpansionValue (primeSetModulus Q.primeFactors) n ≤
      (squareRootCount (2 ^ e * Q) n : ℝ) := by
  let : NeZero Q := ⟨hQ.ne'⟩
  let : NeZero (2 ^ e) := ⟨by positivity⟩
  apply (unitSquareExpansionValue_le_squareRootCount_odd hodd n).trans
  apply Nat.cast_le.mpr
  rw [squareRootCount_mul _ _ _ (h2.pow_left e)]
  have hh := Nat.mul_le_mul_right (squareRootCount Q n)
    (show 1 ≤ squareRootCount (2 ^ e) n from squareRootCount_two_pow_pos_of_modEq_eight e n hn)
  simpa only [one_mul] using hh

end Erdos587
