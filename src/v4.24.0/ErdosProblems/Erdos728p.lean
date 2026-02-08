/-
We have formalized the main results of the paper "A Remark on the Middle Binomial Coefficient" by Carl Pomerance.
Specifically, we have defined the properties and bad sets for Theorems 1.1 and 1.2, and stated the density results.
We have also formalized the intermediate lemmas and bounds required for the proofs.
The final theorems are `theorem_1_1` and `theorem_1_2`.
-/

import Mathlib

namespace Erdos728p

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

open scoped Classical

set_option maxHeartbeats 0

/-
Legendre's formula for the p-adic valuation of n!.
-/
def s_p (p n : ℕ) : ℕ := (Nat.digits p n).sum

theorem lemma_legendre_digit (p n : ℕ) [Fact p.Prime] :
    padicValNat p (Nat.factorial n) = (n - s_p p n) / (p - 1) := by
  have h_legendre : (p - 1) * padicValNat p (n.factorial) = n - s_p p n := by
    rw [ sub_one_mul_padicValNat_factorial ];
    rfl;
  rw [ ← h_legendre, Nat.mul_div_cancel_left _ ( Nat.sub_pos_of_lt ( Nat.Prime.one_lt Fact.out ) ) ]

/-
Carry interpretation: v_p(choose(2m, m)) equals the number of carries, which is given by the formula involving digit sums.
-/
theorem lemma_carry (p m : ℕ) [Fact p.Prime] :
    padicValNat p (Nat.choose (2 * m) m) = (2 * s_p p m - s_p p (2 * m)) / (p - 1) := by
  -- Using the lemma from the provided solution, we can rewrite the p-adic valuation of the binomial coefficient.
  have h_val : (padicValNat p ((Nat.choose (2 * m) m))) = (padicValNat p ((Nat.factorial (2 * m)))) - 2 * (padicValNat p ((Nat.factorial m))) := by
    simp +decide [ two_mul, Nat.choose_eq_factorial_div_factorial ];
    rw [ padicValNat.div_of_dvd ];
    · rw [ padicValNat.mul ( Nat.factorial_ne_zero _ ) ( Nat.factorial_ne_zero _ ) ];
    · exact Nat.factorial_mul_factorial_dvd_factorial_add _ _;
  rw [ h_val, lemma_legendre_digit, lemma_legendre_digit ];
  rw [ eq_comm, Nat.div_eq_of_eq_mul_left ];
  · exact Nat.sub_pos_of_lt ( Fact.out : p > 1 );
  · rw [ tsub_mul, eq_comm ];
    rw [ Nat.div_mul_cancel, Nat.mul_assoc, Nat.div_mul_cancel ];
    · rw [ Nat.mul_sub_left_distrib ] ; ring_nf!;
      rw [ tsub_right_comm, tsub_tsub_cancel_of_le ];
      exact Nat.mul_le_mul_right _ ( Nat.digit_sum_le _ _ );
    · -- Applying the modular equivalence to each term in the sum, we get $m \equiv s_p(m) \pmod{p-1}$.
      have h_sum_mod : m ≡ s_p p m [MOD (p - 1)] := by
        rw [ ← Nat.ofDigits_digits p m, Nat.ModEq, Nat.ofDigits_mod ];
        rcases p with ( _ | _ | _ | p ) <;> simp_all +decide
        · norm_num [ Nat.mod_one ];
        · simp +decide [ Nat.ofDigits_digits, Nat.ofDigits_one, s_p ];
      cases le_total m ( s_p p m ) <;> simp_all +decide [ ← Int.natCast_dvd_natCast, Nat.modEq_iff_dvd ];
      rwa [ dvd_sub_comm ];
    · have h_div : ∀ n : ℕ, (p - 1) ∣ (n - s_p p n) := by
        intro n
        have h_div : n ≡ s_p p n [MOD (p - 1)] := by
          conv_lhs => rw [ ← Nat.ofDigits_digits p n ];
          cases p <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          unfold s_p; simp +decide
          induction ( Nat.digits ( Nat.succ ‹_› ) n ) <;> simp_all +decide [ Nat.ofDigits ];
        rw [ ← Nat.modEq_zero_iff_dvd ];
        cases le_total n ( s_p p n ) <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      exact h_div _

/-
The p-adic valuation of choose(2m, m) is at least the number of large digits in m.
-/
def count_large_digits (p m : ℕ) : ℕ :=
  (Nat.digits p m).filter (fun d => p ≤ 2 * d) |>.length

theorem valuation_ge_large_digits (p m : ℕ) [Fact p.Prime] :
    padicValNat p (Nat.choose (2 * m) m) ≥ count_large_digits p m := by
  -- We need to show that the number of large digits in $m$ is at most the number of carries when adding $m$ and $m$ in base $p$.
  have h_carries : ∀ k ∈ Finset.range (Nat.digits p m).length, (2 * (Nat.digits p m).get! k ≥ p) → padicValNat p (Nat.choose (2 * m) m) ≥ Finset.card (Finset.filter (fun k => 2 * (Nat.digits p m).get! k ≥ p) (Finset.range (Nat.digits p m).length)) := by
    -- By definition of $v_p$, we know that $v_p(\binom{2m}{m})$ is the number of carries when adding $m$ and $m$ in base $p$.
    have h_carries : padicValNat p (Nat.choose (2 * m) m) = Finset.card (Finset.filter (fun i => 2 * (m % p ^ i) ≥ p ^ i) (Finset.Ico 1 (Nat.log p (2 * m) + 1))) := by
      rw [ padicValNat_choose ];
      any_goals exact Nat.lt_succ_self _;
      · norm_num [ two_mul ];
      · linarith;
    -- If $2 * (Nat.digits p m).get! k ≥ p$, then $2 * (m % p^{k+1}) ≥ p^{k+1}$.
    have h_large_digit_carries : ∀ k ∈ Finset.range (Nat.digits p m).length, (2 * (Nat.digits p m).get! k ≥ p) → 2 * (m % p ^ (k + 1)) ≥ p ^ (k + 1) := by
      intro k hk h_large_digit
      have h_mod : m % p ^ (k + 1) = (Nat.ofDigits p (List.take (k + 1) (Nat.digits p m))) := by
        conv_lhs => rw [ ← Nat.ofDigits_digits p m ];
        rw [ ← List.take_append_drop ( k + 1 ) ( Nat.digits p m ), Nat.ofDigits_append ] ; norm_num [ Nat.ofDigits_digits, Nat.mod_eq_of_lt ];
        cases min_cases ( k + 1 ) ( List.length ( Nat.digits p m ) ) <;> simp_all +decide
        · rw [ Nat.mod_eq_of_lt ];
          refine' Nat.ofDigits_lt_base_pow_length _ _ |> lt_of_lt_of_le <| Nat.pow_le_pow_right ( Nat.Prime.pos Fact.out ) <| by simp +decide [ * ] ;
          · exact Nat.Prime.one_lt Fact.out;
          · exact fun x hx => Nat.digits_lt_base ( Fact.out : Nat.Prime p ).one_lt <| List.mem_of_mem_take hx;
        · linarith;
      -- Since $2 * (Nat.digits p m).get! k ≥ p$, we have $2 * (Nat.ofDigits p (List.take (k + 1) (Nat.digits p m))) ≥ p^{k+1}$.
      have h_ofDigits : 2 * (Nat.ofDigits p (List.take (k + 1) (Nat.digits p m))) ≥ p ^ (k + 1) := by
        have h_digit : (Nat.ofDigits p (List.take (k + 1) (Nat.digits p m))) = (Nat.ofDigits p (List.take k (Nat.digits p m))) + (Nat.digits p m).get! k * p ^ k := by
          rw [ List.take_succ ];
          simp +decide [ Nat.ofDigits_append, mul_comm ];
          rw [ min_eq_left ( Finset.mem_range_le hk ) ] ; aesop
        rw [ pow_succ' ];
        nlinarith [ pow_pos ( Fact.out ( p := p.Prime ) ).pos k, show Nat.ofDigits p ( List.take k ( Nat.digits p m ) ) ≥ 0 from Nat.zero_le _ ];
      aesop;
    -- Therefore, the number of large digits in $m$ is at most the number of carries when adding $m$ and $m$ in base $p$.
    intros k hk h_large_digit
    have h_carries_count : Finset.card (Finset.filter (fun i => 2 * (m % p ^ i) ≥ p ^ i) (Finset.Ico 1 (Nat.log p (2 * m) + 1))) ≥ Finset.card (Finset.image (fun k => k + 1) (Finset.filter (fun k => 2 * (Nat.digits p m).get! k ≥ p) (Finset.range (Nat.digits p m).length))) := by
      refine Finset.card_le_card ?_;
      simp_all +decide [ Finset.subset_iff ];
      rintro _ k hk₁ hk₂ rfl; refine' ⟨ ⟨ Nat.succ_pos _, Nat.lt_succ_of_le <| Nat.le_log_of_pow_le ( Fact.out ( p := p.Prime ) |> Nat.Prime.one_lt ) _ ⟩, h_large_digit_carries _ hk₁ hk₂ ⟩ ;
      refine le_trans ( h_large_digit_carries k hk₁ hk₂ ) ?_;
      exact Nat.mul_le_mul_left _ ( Nat.mod_le _ _ );
    rw [ Finset.card_image_of_injective _ Nat.succ_injective ] at h_carries_count ; aesop;
  unfold count_large_digits;
  have h_filter_eq : List.filter (fun d => p ≤ 2 * d) (Nat.digits p m) = List.map (fun k => (Nat.digits p m).get! k) (List.filter (fun k => p ≤ 2 * (Nat.digits p m).get! k) (List.range (Nat.digits p m).length)) := by
    induction ( Nat.digits p m ) <;> simp_all +decide [ List.range_succ_eq_map ];
    by_cases h : p ≤ 2 * ‹_› <;> simp_all +decide
    · rw [ List.filter_map ] ; aesop;
    · simp +decide [ List.filter_map, List.map_map ];
      exact rfl;
  by_cases h_empty : (List.filter (fun k => p ≤ 2 * (Nat.digits p m).get! k) (List.range (Nat.digits p m).length)).length = 0;
  · grind;
  · obtain ⟨ k, hk ⟩ := List.length_pos_iff_exists_mem.mp ( Nat.pos_of_ne_zero h_empty ) ; aesop;

/-
The number of sequences of length D with at most B large digits is bounded by the sum of binomial coefficients times powers of the number of large and small digits.
-/
theorem count_sequences_with_large_digits_bound (p D B : ℕ) (L : ℕ) (hL : L ≤ p) :
    let sequences := (Finset.univ : Finset (Fin D → Fin p)).filter (fun f => (Finset.univ.filter (fun i => (f i).val ≥ L)).card ≤ B)
    sequences.card ≤ ∑ j ∈ Finset.range (B + 1), (Nat.choose D j) * (p - L) ^ j * L ^ (D - j) := by
  -- Let's count the number of sequences with exactly $j$ large digits.
  have h_exact : ∀ j ∈ Finset.range (B + 1), (Finset.filter (fun f : Fin D → Fin p => (Finset.card (Finset.filter (fun i => (f i).val ≥ L) Finset.univ) = j)) (Finset.univ : Finset (Fin D → Fin p))).card = Nat.choose D j * (p - L) ^ j * L ^ (D - j) := by
    intro j hj
    have h_count : (Finset.filter (fun f : Fin D → Fin p => (Finset.filter (fun i => (f i).val ≥ L) Finset.univ).card = j) (Finset.univ : Finset (Fin D → Fin p))).card = ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin D)), (Finset.filter (fun f : Fin D → Fin p => ∀ i, (f i).val ≥ L ↔ i ∈ s) (Finset.univ : Finset (Fin D → Fin p))).card := by
      rw [ ← Finset.card_biUnion ] ; congr ; ext s ; aesop;
      intro s hs t ht hst; simp_all +decide [ Finset.disjoint_left ] ; contrapose! hst; aesop;
    -- For each subset $s$ of size $j$, the number of sequences where exactly the elements of $s$ are large is $(p - L)^j * L^{D - j}$.
    have h_subset_count : ∀ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin D)), (Finset.filter (fun f : Fin D → Fin p => ∀ i, (f i).val ≥ L ↔ i ∈ s) (Finset.univ : Finset (Fin D → Fin p))).card = (p - L) ^ j * L ^ (D - j) := by
      intro s hs
      have h_subset_count : (Finset.filter (fun f : Fin D → Fin p => ∀ i, (f i).val ≥ L ↔ i ∈ s) (Finset.univ : Finset (Fin D → Fin p))).card = (∏ i ∈ s, (Finset.filter (fun x : Fin p => x.val ≥ L) (Finset.univ : Finset (Fin p))).card) * (∏ i ∈ Finset.univ \ s, (Finset.filter (fun x : Fin p => x.val < L) (Finset.univ : Finset (Fin p))).card) := by
        have h_subset_count : (Finset.filter (fun f : Fin D → Fin p => ∀ i, (f i).val ≥ L ↔ i ∈ s) (Finset.univ : Finset (Fin D → Fin p))).card = (∏ i ∈ Finset.univ, (Finset.filter (fun x : Fin p => (x.val ≥ L ↔ i ∈ s)) (Finset.univ : Finset (Fin p))).card) := by
          rw [ Finset.card_filter ];
          rw [ Finset.prod_congr rfl fun _ _ => Finset.card_filter _ _ ];
          rw [ Finset.prod_sum ];
          refine' Finset.sum_bij ( fun f _ => fun i _ => f i ) _ _ _ _ <;> simp +decide [ Finset.prod_ite ];
          · simp +decide [ funext_iff ];
          · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), funext fun i => rfl ⟩;
          · intro a; split_ifs <;> simp_all +decide [ Finset.ext_iff ] ;
        rw [ h_subset_count, ← Finset.prod_sdiff <| Finset.subset_univ s ];
        rw [ mul_comm ] ; refine' congrArg₂ _ _ _ <;> refine' Finset.prod_congr rfl fun i hi => _ <;> aesop;
      -- The number of elements in the set $\{x \in \{0, 1, \ldots, p-1\} \mid x \geq L\}$ is $p - L$, and the number of elements in the set $\{x \in \{0, 1, \ldots, p-1\} \mid x < L\}$ is $L$.
      have h_card_large : (Finset.filter (fun x : Fin p => x.val ≥ L) (Finset.univ : Finset (Fin p))).card = p - L := by
        rw [ Finset.card_eq_of_bijective ];
        use fun i hi => ⟨ L + i, by linarith [ Nat.sub_add_cancel hL ] ⟩;
        · exact fun x hx => ⟨ x - L, by rw [ tsub_lt_tsub_iff_right ( by linarith [ Finset.mem_filter.mp hx ] ) ] ; exact x.2, by erw [ Fin.ext_iff ] ; simp +decide [ add_tsub_cancel_of_le ( show L ≤ x from by linarith [ Finset.mem_filter.mp hx ] ) ] ⟩;
        · grind;
        · simp +contextual [ Fin.ext_iff ]
      have h_card_small : (Finset.filter (fun x : Fin p => x.val < L) (Finset.univ : Finset (Fin p))).card = L := by
        rw [ Finset.card_eq_of_bijective ];
        use fun i hi => ⟨ i, by linarith ⟩;
        · exact fun x hx => ⟨ x, Finset.mem_filter.mp hx |>.2, rfl ⟩;
        · aesop;
        · simp +contextual [ Fin.ext_iff ];
      simp_all +decide [ Finset.card_sdiff ];
    rw [ h_count, Finset.sum_congr rfl h_subset_count, Finset.sum_const, Finset.card_powersetCard, Finset.card_fin, smul_eq_mul, mul_assoc ];
  rw [ ← Finset.sum_congr rfl h_exact ];
  rw [ ← Finset.card_biUnion ];
  · exact Finset.card_le_card fun x hx => Finset.mem_biUnion.mpr ⟨ Finset.card ( Finset.filter ( fun i => L ≤ ( x i : ℕ ) ) Finset.univ ), Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Finset.mem_filter.mp hx |>.2 ) ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, rfl ⟩ ⟩;
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun f hf1 hf2 => hxy <| by aesop;

/-
For a prime p, p - ceil(p/2) <= ceil(p/2).
-/
theorem p_sub_L_le_L (p : ℕ) [Fact p.Prime] :
    p - Nat.ceil (p / 2 : ℝ) ≤ Nat.ceil (p / 2 : ℝ) := by
  rw [ tsub_le_iff_left ];
  exact_mod_cast ( by linarith [ Nat.le_ceil ( ( p : ℝ ) / 2 ) ] : ( p : ℝ ) ≤ ⌈ ( p : ℝ ) / 2⌉₊ + ⌈ ( p : ℝ ) / 2⌉₊ )

/-
Bound on the sum of binomial coefficients: sum_{j=0}^B binom(D, j) <= 2 * D^B for D >= 2.
-/
theorem sum_binomial_bound (D B : ℕ) (hD : D ≥ 2) :
    ∑ j ∈ Finset.range (B + 1), (Nat.choose D j) ≤ 2 * D ^ B := by
  induction' B with B ih <;> simp_all +decide [ Finset.sum_range_succ ];
  -- Since $D \geq 2$, we have $D.choose (B + 1) \leq D^{B + 1}$.
  have h_choose : D.choose (B + 1) ≤ D ^ (B + 1) := by
    exact Nat.choose_le_pow D (B + 1);
  nlinarith [ pow_succ' D B ]

/-
Bound on the number of integers less than p^D with at most B large digits.
-/
theorem bound_N (p D B : ℕ) [Fact p.Prime] (hD : D ≥ 2) :
    let L := Nat.ceil (p / 2 : ℝ)
    let N := (Finset.Iio (p ^ D)).filter (fun m => count_large_digits p m ≤ B)
    N.card ≤ 2 * L ^ D * D ^ B := by
  -- Let $L = \lceil p/2 \rceil$. The number of $m < p^D$ with at most $B$ large digits is bounded by the number of sequences of length $D$ with at most $B$ large digits.
  let L := Nat.ceil ((p : ℝ) / 2)
  have h_bound : (Finset.filter (fun m => count_large_digits p m ≤ B) (Finset.range (p ^ D))).card ≤ ∑ j ∈ Finset.range (B + 1), (Nat.choose D j) * (p - L) ^ j * L ^ (D - j) := by
    have h_bound : (Finset.filter (fun m => count_large_digits p m ≤ B) (Finset.range (p ^ D))).card ≤ (Finset.filter (fun f : Fin D → Fin p => (Finset.univ.filter (fun i => (f i).val ≥ L)).card ≤ B) (Finset.univ : Finset (Fin D → Fin p))).card := by
      -- Each number $m < p^D$ can be represented as a sequence of $D$ digits in base $p$.
      have h_digit_rep : Finset.image (fun m => Nat.digits p m ++ List.replicate (D - (Nat.digits p m).length) 0) (Finset.filter (fun m => count_large_digits p m ≤ B) (Finset.range (p ^ D))) ⊆ Finset.image (fun f : Fin D → Fin p => List.map (fun i => (f i).val) (List.finRange D)) (Finset.filter (fun f : Fin D → Fin p => (Finset.univ.filter (fun i => (f i).val ≥ L)).card ≤ B) (Finset.univ : Finset (Fin D → Fin p))) := by
        intro;
        simp +zetaDelta at *;
        rintro x hx₁ hx₂ rfl;
        -- Let $a$ be the function that maps each index $i$ to the $i$-th digit of $x$ in base $p$.
        obtain ⟨a, ha⟩ : ∃ a : Fin D → Fin p, List.map (fun i => (a i).val) (List.finRange D) = Nat.digits p x ++ List.replicate (D - (Nat.digits p x).length) 0 := by
          have h_digits_len : (Nat.digits p x).length ≤ D := by
            have := @Nat.digits_len p x;
            exact if hx₃ : x = 0 then by simp +decide [ hx₃ ] else by rw [ this ( Nat.Prime.one_lt Fact.out ) hx₃ ] ; exact Nat.log_lt_of_lt_pow ( by positivity ) hx₁;
          use fun i => ⟨ (Nat.digits p x ++ List.replicate (D - (Nat.digits p x).length) 0)[i]!, by
            by_cases hi : i.val < (Nat.digits p x).length <;> simp_all +decide
            · exact Nat.digits_lt_base ( Fact.out : p.Prime ).one_lt ( List.getElem_mem _ );
            · exact Nat.Prime.pos Fact.out ⟩
          generalize_proofs at *;
          refine' List.ext_get _ _ <;> aesop;
        -- By definition of $a$, we know that the number of large digits in $x$ is equal to the number of indices $i$ such that $(a i).val \geq L$.
        have h_large_digits : count_large_digits p x = (Finset.univ.filter (fun i => (a i).val ≥ L)).card := by
          have h_large_digits : count_large_digits p x = List.length (List.filter (fun d => p ≤ 2 * d) (Nat.digits p x ++ List.replicate (D - (Nat.digits p x).length) 0)) := by
            simp +decide [ count_large_digits ];
            exact fun _ => Nat.Prime.pos Fact.out;
          rw [ h_large_digits, ← ha, List.filter_map ];
          simp +zetaDelta at *;
          field_simp;
          norm_cast;
        aesop;
      have := Finset.card_mono h_digit_rep;
      rwa [ Finset.card_image_of_injOn, Finset.card_image_of_injOn ] at this;
      · intro f hf g hg; aesop;
      · intro m hm m' hm' h_eq; have := congr_arg List.length h_eq; norm_num at this;
        replace h_eq := congr_arg ( fun l => Nat.ofDigits p l ) h_eq ; simp_all +decide [ Nat.ofDigits_append, Nat.ofDigits_digits ];
    refine le_trans h_bound ?_;
    convert count_sequences_with_large_digits_bound p D B L ( Nat.ceil_le.mpr <| by rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ show p ≥ 2 from Nat.Prime.two_le Fact.out ] ) using 1;
  -- Since $p-L \le L$ (by `p_sub_L_le_L`), this is $\le L^D \sum_{j=0}^B \binom{D}{j}$.
  have h_sum_bound : ∑ j ∈ Finset.range (B + 1), (Nat.choose D j) * (p - L) ^ j * L ^ (D - j) ≤ L ^ D * ∑ j ∈ Finset.range (B + 1), (Nat.choose D j) := by
    -- Since $p - L \leq L$, we have $(p - L)^j \leq L^j$ for all $j$.
    have h_term_bound : ∀ j ∈ Finset.range (B + 1), (p - L) ^ j ≤ L ^ j := by
      intros j hj
      have h_ineq : p - L ≤ L := by
        exact p_sub_L_le_L p
      have h_pow : (p - L) ^ j ≤ L ^ j := by
        exact Nat.pow_le_pow_left h_ineq _
      exact h_pow;
    -- Apply the term bound to each term in the sum.
    have h_sum_le : ∑ j ∈ Finset.range (B + 1), (Nat.choose D j) * (p - L) ^ j * L ^ (D - j) ≤ ∑ j ∈ Finset.range (B + 1), (Nat.choose D j) * L ^ j * L ^ (D - j) := by
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_term_bound i hi ) ( Nat.zero_le _ ) ) ( Nat.zero_le _ );
    convert h_sum_le using 1;
    rw [ Finset.mul_sum _ _ _, Finset.sum_congr rfl ] ; intros ; ring_nf;
    by_cases h : ‹_› ≤ D <;> simp_all +decide [ ← pow_add, add_tsub_cancel_of_le ];
    exact Or.inr <| Nat.choose_eq_zero_of_lt h;
  -- By `sum_binomial_bound`, $\sum \binom{D}{j} \le 2 D^B$.
  have h_binom_bound : ∑ j ∈ Finset.range (B + 1), (Nat.choose D j) ≤ 2 * D ^ B := by
    exact sum_binomial_bound D B hD;
  simpa only [ mul_assoc, mul_comm, mul_left_comm, Finset.range_eq_Ico ] using h_bound.trans ( h_sum_bound.trans ( Nat.mul_le_mul_left _ h_binom_bound ) )

/-
Bound on D^B.
-/
theorem D_pow_B_bound (p : ℕ) [Fact p.Prime] (x : ℝ) (hx : x ≥ p) :
    let D := Nat.floor (1 + Real.log x / Real.log p)
    let B := Nat.floor (D / (5 * Real.log D))
    (D : ℝ) ^ B ≤ Real.exp (1 / 5) * x ^ (1 / (5 * Real.log p)) := by
  -- Using the bounds from Lemma 5, we have D^B ≤ Real.exp (D / 5).
  have h_exp : (Nat.floor (1 + Real.log x / Real.log p)) ^ (Nat.floor ((Nat.floor (1 + Real.log x / Real.log p)) / (5 * Real.log (Nat.floor (1 + Real.log x / Real.log p))))) ≤ Real.exp ((Nat.floor (1 + Real.log x / Real.log p)) / 5) := by
    by_cases hD : ⌊1 + Real.log x / Real.log p⌋₊ ≤ 1;
    · interval_cases _ : ⌊1 + Real.log x / Real.log p⌋₊ <;> norm_num;
    · rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
      · have := Nat.floor_le ( show 0 ≤ ( ⌊1 + Real.log x / Real.log p⌋₊ : ℝ ) / ( 5 * Real.log ⌊1 + Real.log x / Real.log p⌋₊ ) by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ) ) ) ; rw [ le_div_iff₀ ( mul_pos ( by norm_num ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( lt_of_not_ge hD ) ) ) ) ] at this; nlinarith [ Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) : 0 < ⌊1 + Real.log x / Real.log p⌋₊ ) ) ] ;
      · linarith;
  -- Using the bounds from Lemma 5, we have $\exp(D/5) \leq \exp(1/5) \exp((\log x / \log p) / 5)$.
  have h_exp_bound : Real.exp ((Nat.floor (1 + Real.log x / Real.log p)) / 5) ≤ Real.exp (1 / 5) * Real.exp ((Real.log x / Real.log p) / 5) := by
    rw [ ← Real.exp_add ] ; gcongr ; linarith [ Nat.floor_le ( show 0 ≤ 1 + Real.log x / Real.log p by exact add_nonneg zero_le_one <| div_nonneg ( Real.log_nonneg <| by linarith [ show ( p :ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| Nat.Prime.pos Fact.out ] ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.Prime.pos Fact.out ) ] ;
  convert h_exp.trans h_exp_bound using 1 ; rw [ Real.rpow_def_of_pos ( show 0 < x from lt_of_lt_of_le ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) hx ) ] ; ring_nf

/-
Bound on L^D.
-/
theorem L_pow_D_bound (p : ℕ) [Fact p.Prime] (x : ℝ) (hx : x ≥ p) :
    let D := Nat.floor (1 + Real.log x / Real.log p)
    let L := Nat.ceil (p / 2 : ℝ)
    (L : ℝ) ^ D ≤ p * x ^ (1 - Real.log (3 / 2) / Real.log p) := by
  -- We have $D \le 1 + \frac{\log x}{\log p}$ and $D > \frac{\log x}{\log p}$.
  set D := Nat.floor (1 + Real.log x / Real.log p)
  set L := Nat.ceil (p / 2 : ℝ)
  have hD : (D : ℝ) ≤ 1 + Real.log x / Real.log p ∧ (D : ℝ) > Real.log x / Real.log p := by
    exact ⟨ Nat.floor_le <| by exact add_nonneg zero_le_one <| div_nonneg ( Real.log_nonneg <| by linarith [ show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le Fact.out ] ) <| Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos Fact.out, by linarith [ Nat.lt_floor_add_one <| 1 + Real.log x / Real.log p ] ⟩;
  -- We have $L \le \frac{2}{3}p$.
  have hL : (L : ℝ) ≤ (2 / 3 : ℝ) * p := by
    field_simp;
    have := Nat.ceil_lt_add_one ( show 0 ≤ ( p : ℝ ) / 2 by positivity );
    rw [ div_add_one, lt_div_iff₀ ] at this <;> norm_cast at * ; linarith [ show p > 1 from Fact.out ];
  -- Then $L^D \le (\frac{2}{3}p)^D = p^D (\frac{2}{3})^D$.
  have hLD : (L : ℝ) ^ D ≤ (p : ℝ) ^ D * (2 / 3 : ℝ) ^ D := by
    rw [ ← mul_pow ] ; gcongr ; linarith;
  -- We have $p^D \le p x$.
  have hpD : (p : ℝ) ^ D ≤ (p : ℝ) * x := by
    have hpD : (p : ℝ) ^ D ≤ (p : ℝ) ^ (1 + Real.log x / Real.log p) := by
      exact_mod_cast Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.mpr <| Nat.Prime.pos Fact.out ) hD.1;
    convert hpD using 1 ; rw [ Real.rpow_add ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ), Real.rpow_one ] ; rw [ Real.rpow_def_of_pos <| Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ] ; ring_nf ; norm_num [ Real.logb, Real.log_pow, ne_of_gt <| Nat.Prime.pos Fact.out ] ;
    rw [ mul_right_comm, mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Fact.out : p > 1 ) ) ) ), one_mul, Real.exp_log ( by linarith [ show ( p : ℝ ) > 0 from Nat.cast_pos.mpr ( Nat.Prime.pos Fact.out ) ] ) ];
  -- We have $(\frac{2}{3})^D \le x^{-\frac{\log(3/2)}{\log p}}$.
  have h23D : (2 / 3 : ℝ) ^ D ≤ x ^ (-Real.log (3 / 2) / Real.log p) := by
    rw [ Real.le_rpow_iff_log_le ] <;> norm_num;
    · rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_num [ Real.log_div ] at *;
      · rw [ div_lt_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Fact.out ) ] at hD ; nlinarith [ Real.log_pos one_lt_two, Real.log_lt_log ( by norm_num ) ( by norm_num : ( 3 : ℝ ) > 2 ) ];
      · exact Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out;
    · linarith [ show ( p : ℝ ) > 0 from Nat.cast_pos.mpr ( Nat.Prime.pos Fact.out ) ];
  convert le_trans hLD ( mul_le_mul hpD h23D ( by positivity ) ( by exact mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ show ( p :ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.Prime.pos Fact.out ) ] ) ) ) using 1 ; ring_nf;
  rw [ Real.rpow_sub ( by linarith [ show ( p : ℝ ) > 0 by exact Nat.cast_pos.mpr ( Nat.Prime.pos Fact.out ) ] ), Real.rpow_one ] ; ring_nf;
  rw [ Real.rpow_neg ( by linarith [ show ( p : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.Prime.pos Fact.out ) ] ) ]

/-
Numerical bound: log(3/2) > 2/5.
-/
theorem log_three_halves_gt_two_fifths : Real.log (3 / 2) > 2 / 5 := by
  rw [ gt_iff_lt, div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  have := Real.exp_one_lt_d9 ; norm_num at * ; rw [ show ( 2 : ℝ ) = 1 + 1 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos 1 ]

/-
Numerical bound: 2 * exp(1/5) <= 3.
-/
theorem two_mul_exp_one_fifth_le_three : 2 * Real.exp (1 / 5) ≤ 3 := by
  -- We'll use the exponential property: $e^{1/5} \leq \frac{3}{2}$
  have h_exp_bound : Real.exp (1 / 5) ≤ 3 / 2 := by
    rw [ ← Real.log_le_log_iff ( by positivity ) ] <;> norm_num;
    rw [ div_le_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.le_log_iff_exp_le ];
    exact Real.exp_one_lt_d9.le.trans ( by norm_num );
  linarith

/-
Bound on the number of integers m <= x with small valuation of binomial coefficient.
-/
theorem lemma_3_1 (p : ℕ) [Fact p.Prime] (x : ℝ) (hx : x ≥ p) :
    let D : ℕ := Nat.floor (1 + Real.log x / Real.log p)
    let count := (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
      (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ (D : ℝ) / (5 * Real.log D))
    (count.card : ℝ) ≤ 3 * p * x ^ (1 - 1 / (5 * Real.log p)) := by
      -- Let's bound the number of $m$ with $v_p(\binom{2m}{m}) \leq \frac{D}{5 \ln D}$.
      have h_bound : (Finset.filter (fun m => ((padicValNat p (Nat.choose (2 * m) m)) : ℝ) ≤ (Nat.floor (1 + Real.log x / Real.log p)) / (5 * Real.log (Nat.floor (1 + Real.log x / Real.log p)))) (Finset.Icc 1 (⌊x⌋₊))).card ≤ 2 * Nat.ceil (p / 2 : ℝ) ^ (Nat.floor (1 + Real.log x / Real.log p)) * (Nat.floor (1 + Real.log x / Real.log p)) ^ Nat.floor ((Nat.floor (1 + Real.log x / Real.log p)) / (5 * Real.log (Nat.floor (1 + Real.log x / Real.log p)))) := by
        refine' le_trans ( Finset.card_le_card _ ) _;
        exact Finset.filter ( fun m => count_large_digits p m ≤ Nat.floor ( ( Nat.floor ( 1 + Real.log x / Real.log p ) : ℝ ) / ( 5 * Real.log ( Nat.floor ( 1 + Real.log x / Real.log p ) ) ) ) ) ( Finset.Iio ( p ^ ( Nat.floor ( 1 + Real.log x / Real.log p ) ) ) );
        · simp +decide [ Finset.subset_iff ];
          intro m hm₁ hm₂ hm₃;
          refine' ⟨ _, Nat.le_floor _ ⟩;
          · have h_exp : (p : ℝ) ^ (Nat.floor (1 + Real.log x / Real.log p)) > x := by
              have := Nat.lt_floor_add_one ( 1 + Real.log x / Real.log p );
              rw [ add_div', div_lt_iff₀ ] at this <;> norm_num at *;
              · rw [ ← Real.log_lt_log_iff ( by linarith [ show ( p : ℝ ) > 0 from Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ] ) ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ), Real.log_pow ];
                rw [ add_div', div_eq_mul_inv ] at *;
                · grind;
                · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out;
                · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out;
              · exact Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out;
              · exact ⟨ Nat.Prime.ne_zero Fact.out, Nat.Prime.ne_one Fact.out, by linarith ⟩;
            exact_mod_cast lt_of_le_of_lt hm₂ ( Nat.floor_lt ( by linarith ) |>.2 <| h_exp.trans_le <| by norm_num );
          · refine' le_trans _ hm₃;
            exact_mod_cast valuation_ge_large_digits p m;
        · convert bound_N p _ _ _ using 2;
          exact Nat.le_floor ( by norm_num; nlinarith [ show 1 ≤ Real.log x / Real.log p from by rw [ one_le_div ( Real.log_pos <| mod_cast Nat.Prime.one_lt Fact.out ) ] ; exact Real.log_le_log ( mod_cast Nat.Prime.pos Fact.out ) hx ] );
      -- Let's simplify the bound using the results from the previous steps.
      have h_simplify : 2 * Nat.ceil (p / 2 : ℝ) ^ (Nat.floor (1 + Real.log x / Real.log p)) * (Nat.floor (1 + Real.log x / Real.log p)) ^ Nat.floor ((Nat.floor (1 + Real.log x / Real.log p)) / (5 * Real.log (Nat.floor (1 + Real.log x / Real.log p)))) ≤ 2 * p * x ^ (1 - (Real.log (3 / 2)) / (Real.log p)) * (Real.exp (1 / 5) * x ^ (1 / (5 * Real.log p))) := by
        refine' mul_le_mul _ _ _ _;
        · convert mul_le_mul_of_nonneg_left ( L_pow_D_bound p x hx ) zero_le_two using 1 ; ring;
        · convert D_pow_B_bound p x ( show x ≥ p by assumption ) using 1;
        · positivity;
        · exact mul_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) ( Real.rpow_nonneg ( by linarith ) _ );
      -- Let's simplify the right-hand side of the inequality.
      have h_final : 2 * p * x ^ (1 - (Real.log (3 / 2)) / (Real.log p)) * (Real.exp (1 / 5) * x ^ (1 / (5 * Real.log p))) ≤ 3 * p * x ^ (1 - 1 / (5 * Real.log p)) := by
        -- Combine the exponents of $x$.
        have h_exp : x ^ (1 - (Real.log (3 / 2)) / (Real.log p)) * x ^ (1 / (5 * Real.log p)) = x ^ (1 - (Real.log (3 / 2)) / (Real.log p) + 1 / (5 * Real.log p)) := by
          rw [ Real.rpow_add ( by linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le Fact.out ] ) ];
        -- Combine the exponents of $x$ and simplify.
        have h_exp_simplified : x ^ (1 - (Real.log (3 / 2)) / (Real.log p) + 1 / (5 * Real.log p)) ≤ x ^ (1 - 1 / (5 * Real.log p)) := by
          have h_exp_simplified : Real.log (3 / 2) > 2 / 5 := by
            exact log_three_halves_gt_two_fifths;
          exact Real.rpow_le_rpow_of_exponent_le ( by linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le Fact.out ] ) ( by ring_nf at *; nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( p : ℝ ) > 1 by exact_mod_cast Nat.Prime.one_lt Fact.out ) ) ] );
        -- Substitute the simplified exponent back into the inequality.
        have h_final : 2 * p * x ^ (1 - (Real.log (3 / 2)) / (Real.log p) + 1 / (5 * Real.log p)) * Real.exp (1 / 5) ≤ 3 * p * x ^ (1 - 1 / (5 * Real.log p)) := by
          have h_final : 2 * Real.exp (1 / 5) ≤ 3 := by
            exact two_mul_exp_one_fifth_le_three;
          nlinarith [ show 0 ≤ ( p : ℝ ) * x ^ ( 1 - Real.log ( 3 / 2 ) / Real.log p + 1 / ( 5 * Real.log p ) ) by exact mul_nonneg ( Nat.cast_nonneg _ ) ( Real.rpow_nonneg ( by linarith [ show ( p : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.Prime.pos Fact.out ) ] ) _ ) ];
        convert h_final using 1 ; rw [ ← h_exp ] ; ring;
      exact le_trans ( mod_cast h_bound ) ( le_trans h_simplify h_final )

/-
Definition of K as a function of x.
-/
noncomputable def K_func (x : ℝ) : ℕ := Nat.floor (Real.exp (Real.sqrt (Real.log x)))

/-
Definition of D as a function of p and x.
-/
noncomputable def D_func (p : ℕ) (x : ℝ) : ℕ := 1 + Nat.floor (Real.log x / Real.log p)

/-
The set of integers m <= x such that for some prime p <= 2K, v_p(binom(2m, m)) <= D / (5 log D).
-/
noncomputable def bad_set_cor_3_2 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_func x + 1), p.Prime ∧
      (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ (D_func p x : ℝ) / (5 * Real.log (D_func p x)))

/-
The upper bound from the paper's proof actually grows superlinearly, contradicting the o(x) claim.
-/
theorem bound_diverges :
    Filter.Tendsto (fun x => (2 * K_func x)^2 * x ^ (1 - 1 / (5 * Real.log (2 * K_func x))) / x) Filter.atTop Filter.atTop := by
      -- We can rewrite the expression as $4 * (K_func x)^2 * x^{-1/(5 * Real.log (2 * K_func x))}$.
      suffices h_rewrite : Filter.Tendsto (fun x : ℝ => 4 * (K_func x)^2 * x^(-1 / (5 * Real.log (2 * K_func x)))) Filter.atTop Filter.atTop by
        refine h_rewrite.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx;
        rw [ show ( -1 : ℝ ) / ( 5 * Real.log ( 2 * K_func x ) ) = 1 - 1 / ( 5 * Real.log ( 2 * K_func x ) ) - 1 by ring ] ; rw [ Real.rpow_sub hx, Real.rpow_one ] ; ring;
      -- Taking the natural logarithm of the expression, we get $\log(4) + 2 \log(K_func x) - \frac{1}{5 \log(2K_func x)} \log(x)$.
      suffices h_log : Filter.Tendsto (fun x => Real.log 4 + 2 * Real.log (K_func x) - (Real.log x) / (5 * Real.log (2 * K_func x))) Filter.atTop Filter.atTop by
        have h_exp : Filter.Tendsto (fun x => Real.exp (Real.log 4 + 2 * Real.log (K_func x) - (Real.log x) / (5 * Real.log (2 * K_func x)))) Filter.atTop Filter.atTop := by
          aesop;
        refine h_exp.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
        rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
        rw [ Real.exp_add, Real.exp_add, Real.exp_mul, Real.exp_log ( by positivity ), Real.exp_log ( by norm_cast; exact Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| Real.one_le_exp <| Real.sqrt_nonneg _ ) ] ; ring_nf;
        norm_cast;
      -- We'll use that $Real.log (K_func x) \approx \sqrt{Real.log x}$ and $Real.log (2 * K_func x) \approx \sqrt{Real.log x}$.
      have h_log_approx : Filter.Tendsto (fun x => Real.log (K_func x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun x => Real.log (2 * K_func x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 1) := by
        -- We'll use that $Real.log (K_func x) \approx \sqrt{Real.log x}$.
        have h_log_approx : Filter.Tendsto (fun x => Real.log (K_func x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 1) := by
          -- We'll use the fact that $K_func x = \lfloor \exp(\sqrt{\log x}) \rfloor$ to simplify the expression.
          have h_K_func : Filter.Tendsto (fun x : ℝ => Real.log (Nat.floor (Real.exp (Real.sqrt (Real.log x)))) / Real.sqrt (Real.log x)) Filter.atTop (nhds 1) := by
            -- We'll use the fact that $\log(\lfloor e^{\sqrt{\log x}} \rfloor) = \sqrt{\log x} + O(1)$.
            have h_log_floor : Filter.Tendsto (fun x => Real.log (Nat.floor (Real.exp (Real.sqrt (Real.log x)))) - Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
              have h_log_floor : Filter.Tendsto (fun x => Real.log (⌊Real.exp (Real.sqrt (Real.log x))⌋₊) - Real.log (Real.exp (Real.sqrt (Real.log x)))) Filter.atTop (nhds 0) := by
                have h_log_floor : Filter.Tendsto (fun x => Real.log (⌊Real.exp (Real.sqrt (Real.log x))⌋₊ / Real.exp (Real.sqrt (Real.log x)))) Filter.atTop (nhds 0) := by
                  have h_log_floor : Filter.Tendsto (fun x => (⌊Real.exp (Real.sqrt (Real.log x))⌋₊ : ℝ) / Real.exp (Real.sqrt (Real.log x))) Filter.atTop (nhds 1) := by
                    have h_floor : Filter.Tendsto (fun y : ℝ => (Nat.floor y : ℝ) / y) Filter.atTop (nhds 1) := by
                      rw [ Metric.tendsto_nhds ];
                      intro ε hε; filter_upwards [ Filter.eventually_gt_atTop ( ε⁻¹ + 1 ), Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using abs_lt.mpr ⟨ by nlinarith [ Nat.floor_le hx₂.le, Nat.lt_floor_add_one x, mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( Nat.floor x : ℝ ) hx₂.ne' ], by nlinarith [ Nat.floor_le hx₂.le, Nat.lt_floor_add_one x, mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( Nat.floor x : ℝ ) hx₂.ne' ] ⟩ ;
                    exact h_floor.comp <| Real.tendsto_exp_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩;
                  simpa using Filter.Tendsto.log h_log_floor;
                refine h_log_floor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_div ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| Real.one_le_exp <| Real.sqrt_nonneg _ ) <| ne_of_gt <| Real.exp_pos _ ] );
              aesop;
            have := h_log_floor.div_atTop ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt ( Real.log x ) ) Filter.atTop ( Filter.atTop ) from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩ );
            simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ sub_div, div_self <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ] ; ring );
          convert h_K_func using 1;
        -- We'll use that $Real.log (2 * K_func x) = Real.log 2 + Real.log (K_func x)$.
        have h_log_split : Filter.Tendsto (fun x => (Real.log 2 + Real.log (K_func x)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 1) := by
          simpa [ add_div ] using Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.sqrt.comp ( Real.tendsto_log_atTop ) ) ) h_log_approx;
        exact ⟨ h_log_approx, h_log_split.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by exact Nat.cast_ne_zero.mpr <| ne_of_gt <| Nat.floor_pos.mpr <| Real.one_le_exp <| Real.sqrt_nonneg _ ) ] ⟩;
      -- Using the approximations, we can simplify the expression.
      have h_simplify : Filter.Tendsto (fun x => 2 * Real.log (K_func x) - (Real.log x) / (5 * Real.log (2 * K_func x))) Filter.atTop Filter.atTop := by
        -- We can factor out $\sqrt{\log x}$ from the expression.
        suffices h_factor : Filter.Tendsto (fun x => Real.sqrt (Real.log x) * (2 * (Real.log (K_func x) / Real.sqrt (Real.log x)) - 1 / (5 * (Real.log (2 * K_func x) / Real.sqrt (Real.log x))))) Filter.atTop Filter.atTop by
          refine h_factor.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
          field_simp [mul_comm, mul_assoc, mul_left_comm];
          rw [ mul_div_cancel_left₀ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( Real.log_pos hx ) ) ), Real.sq_sqrt ( Real.log_nonneg hx.le ) ];
        apply Filter.Tendsto.atTop_mul_pos;
        exacts [ show 0 < 2 * 1 - 1 / ( 5 * 1 ) by norm_num, Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩, by simpa using Filter.Tendsto.sub ( h_log_approx.1.const_mul 2 ) ( h_log_approx.2.const_mul 5 |> Filter.Tendsto.inv₀ <| by norm_num ) ];
      simpa only [ add_sub_assoc ] using Filter.Tendsto.add_atTop tendsto_const_nhds h_simplify

/-
The number of multiples of q in {n+1, ..., n+k} is at most k/q + 1.
-/
theorem count_multiples_bound (n k q : ℕ) (hq : q > 0) :
    ((Finset.Icc (n + 1) (n + k)).filter (fun x => q ∣ x)).card ≤ k / q + 1 := by
      -- Let's count the number of multiples of $q$ in the interval $[n+1, n+k]$.
      have h_multiples : Finset.filter (fun x => q ∣ x) (Finset.Icc (n + 1) (n + k)) ⊆ Finset.image (fun m => q * m) (Finset.Icc ((n + 1 + q - 1) / q) ((n + k) / q)) := by
        simp +decide [ Finset.subset_iff ];
        intro x hx₁ hx₂ hx₃; obtain ⟨ a, rfl ⟩ := hx₃; exact ⟨ a, ⟨ by nlinarith [ Nat.div_mul_le_self ( n + q ) q, Nat.div_add_mod ( n + q ) q, Nat.mod_lt ( n + q ) hq ], by nlinarith [ Nat.div_mul_le_self ( n + k ) q, Nat.div_add_mod ( n + k ) q, Nat.mod_lt ( n + k ) hq ] ⟩, by ring ⟩ ;
      refine le_trans ( Finset.card_le_card h_multiples ) ?_;
      rw [ Finset.card_image_of_injective _ fun a b h => mul_left_cancel₀ hq.ne' h ];
      simp +arith +decide [ Nat.add_div, hq ];
      split_ifs <;> linarith

/-
If x_0 is a multiple of q in the interval {n+1, ..., n+k}, then the number of other multiples of q in the interval is at most k/q.
-/
theorem count_multiples_removed (n k q : ℕ) (hq : q > 0) (x₀ : ℕ) (hx₀ : x₀ ∈ Finset.Icc (n + 1) (n + k)) (hdiv : q ∣ x₀) :
    ((Finset.Icc (n + 1) (n + k)).filter (fun x => q ∣ x) \ {x₀}).card ≤ k / q := by
      -- We know that the number of multiples of $q$ in the interval is at most $k / q + 1$.
      have h_mult_count : ((Finset.Icc (n + 1) (n + k)).filter (fun x => q ∣ x)).card ≤ k / q + 1 := by
        convert count_multiples_bound n k q hq using 1;
      rw [ Finset.card_sdiff ] ; aesop

/-
The sum of p-adic valuations of elements in {m+1, ..., m+k} excluding a maximal element is at most v_p(k!).
-/
theorem valuation_sum_le_factorial_valuation (m k : ℕ) (p : ℕ) [Fact p.Prime]
    (x₀ : ℕ) (hx₀ : x₀ ∈ Finset.Icc (m + 1) (m + k))
    (hmax : ∀ x ∈ Finset.Icc (m + 1) (m + k), padicValNat p x ≤ padicValNat p x₀) :
    ∑ x ∈ (Finset.Icc (m + 1) (m + k)).erase x₀, padicValNat p x ≤ padicValNat p (Nat.factorial k) := by
      -- For j <= v_p(x_0), the number of multiples of p^j in the set excluding x_0 is at most floor(k/p^j).
      have h_multiples_j_v_le : ∀ j : ℕ, j ≤ padicValNat p x₀ → ((Finset.Icc (m + 1) (m + k)).filter (fun x => p ^ j ∣ x) \ {x₀}).card ≤ k / p ^ j := by
        intro j hj;
        apply count_multiples_removed;
        · exact pow_pos ( Nat.Prime.pos Fact.out ) _;
        · assumption;
        · rw [ padicValNat_dvd_iff ] at * ; aesop;
      -- Summing over j using the bounds from h_multiples_j_v_le gives us the desired inequality.
      have h_sum_multiples_j_v_le : ∑ x ∈ (Finset.Icc (m + 1) (m + k)).erase x₀, padicValNat p x ≤ ∑ j ∈ Finset.Icc 1 (padicValNat p x₀), ((Finset.Icc (m + 1) (m + k)).filter (fun x => p ^ j ∣ x) \ {x₀}).card := by
        have h_sum_multiples_j_v_le : ∀ x ∈ (Finset.Icc (m + 1) (m + k)).erase x₀, padicValNat p x ≤ ∑ j ∈ Finset.Icc 1 (padicValNat p x₀), (if p ^ j ∣ x then 1 else 0) := by
          intro x hx
          have h_div : ∀ j ∈ Finset.Icc 1 (padicValNat p x), p ^ j ∣ x := by
            simp +zetaDelta at *;
            intro j hj₁ hj₂; rw [ padicValNat_dvd_iff_le ] ; aesop;
            linarith;
          rw [ ← Finset.sum_filter ];
          exact le_trans ( by simp ) ( Finset.sum_le_sum_of_subset ( show Finset.Icc 1 ( padicValNat p x ) ⊆ Finset.filter ( fun a => p ^ a ∣ x ) ( Finset.Icc 1 ( padicValNat p x₀ ) ) from fun j hj => Finset.mem_filter.mpr ⟨ Finset.Icc_subset_Icc_right ( hmax x ( Finset.mem_of_mem_erase hx ) ) hj, h_div j hj ⟩ ) );
        refine le_trans ( Finset.sum_le_sum h_sum_multiples_j_v_le ) ?_;
        rw [ Finset.sum_comm ];
        simp +decide [ Finset.filter_erase, Finset.sdiff_singleton_eq_erase ];
      -- Applying the lemma about the sum of p-adic valuations to the set {m+1, ..., m+k} excluding x_0.
      have h_sum_multiples_j_v_le_final : ∑ j ∈ Finset.Icc 1 (padicValNat p x₀), ((Finset.Icc (m + 1) (m + k)).filter (fun x => p ^ j ∣ x) \ {x₀}).card ≤ ∑ j ∈ Finset.Icc 1 (Nat.log p k), (k / p ^ j) := by
        by_cases h_cases : padicValNat p x₀ ≤ Nat.log p k;
        · exact le_trans ( Finset.sum_le_sum fun _ _ => h_multiples_j_v_le _ <| Finset.mem_Icc.mp ‹_› |>.2 ) ( Finset.sum_le_sum_of_subset <| Finset.Icc_subset_Icc_right h_cases );
        · rw [ Finset.sum_subset ( Finset.Icc_subset_Icc_right ( le_of_not_ge h_cases ) ) ];
          · exact Finset.sum_le_sum fun j hj => h_multiples_j_v_le j <| Finset.mem_Icc.mp hj |>.2;
          · exact fun x hx₁ hx₂ => Nat.div_eq_of_lt <| Nat.lt_pow_of_log_lt ( Fact.out ( p := p.Prime ) |> Nat.Prime.one_lt ) <| by aesop;
      rw [ padicValNat_factorial ];
      exacts [ h_sum_multiples_j_v_le.trans h_sum_multiples_j_v_le_final, Nat.lt_succ_self _ ]

/-
For all integers m > k > 0 and primes p, v_p(binom(m+k, k)) <= max {v_p(m+i) : 1 <= i <= k}.
-/
theorem lemma_3_3 (m k : ℕ) (p : ℕ) [Fact p.Prime] (hm : m > k) (hk : k > 0) :
    padicValNat p (Nat.choose (m + k) k) ≤ Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
      -- Let $S$ be the set $\{m+1, \ldots, m+k\}$. Let $x_0 \in S$ be an element with maximal $p$-adic valuation.
      let S := Finset.Icc (m + 1) (m + k)
      obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ S, ∀ x ∈ S, padicValNat p x ≤ padicValNat p x₀ := by
        exact Finset.exists_max_image _ _ ⟨ m + 1, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩;
      -- We have $v_p(\binom{m+k}{k}) = v_p((m+k)!/m!) - v_p(k!) = (sum_{x in S} v_p(x)) - v_p(k!)$.
      have h_val : padicValNat p (Nat.choose (m + k) k) = (∑ x ∈ S, padicValNat p x) - padicValNat p (Nat.factorial k) := by
        -- Using the properties of the p-adic valuation, we can rewrite the expression as follows:
        have h_sum : (∑ x ∈ S, padicValNat p x) = padicValNat p (Nat.factorial (m + k)) - padicValNat p (Nat.factorial m) := by
          have h_sum : ∀ n, (∑ x ∈ Finset.Icc 1 n, padicValNat p x) = padicValNat p (Nat.factorial n) := by
            intro n;
            induction n <;> simp_all +decide [ Nat.factorial_succ, Finset.sum_Ioc_succ_top, Nat.Icc_succ_left ];
            rw [ mul_comm, padicValNat.mul ] <;> positivity;
          have h_sum_split : ∑ x ∈ Finset.Icc 1 (m + k), padicValNat p x = (∑ x ∈ Finset.Icc 1 m, padicValNat p x) + (∑ x ∈ Finset.Icc (m + 1) (m + k), padicValNat p x) := by
            erw [ Finset.sum_Ico_consecutive ] <;> linarith!;
          aesop;
        rw [ h_sum, Nat.choose_eq_factorial_div_factorial ( by linarith ), padicValNat.div_of_dvd ];
        · rw [ Nat.sub_sub, Nat.add_comm ];
          rw [ Nat.add_comm, padicValNat.mul ( by positivity ) ( by positivity ) ] ; simp +decide [ add_comm ];
        · exact Nat.factorial_mul_factorial_dvd_factorial ( by linarith );
      -- The sum is $v_p(x_0) + \sum_{x \in S \ {x_0}} v_p(x)$.
      have h_sum : ∑ x ∈ S, padicValNat p x = padicValNat p x₀ + ∑ x ∈ S.erase x₀, padicValNat p x := by
        rw [ add_comm, Finset.sum_erase_add _ _ hx₀.1 ];
      -- By valuation_sum_le_factorial_valuation, $\sum_{x \in S \ {x_0}} v_p(x) \leq v_p(k!)$.
      have h_sum_le : ∑ x ∈ S.erase x₀, padicValNat p x ≤ padicValNat p (Nat.factorial k) := by
        apply valuation_sum_le_factorial_valuation m k p x₀ hx₀.left hx₀.right;
      -- Therefore, $v_p(\binom{m+k}{k}) \leq v_p(x_0)$.
      have h_final : padicValNat p (Nat.choose (m + k) k) ≤ padicValNat p x₀ := by
        grind;
      simp +zetaDelta at *;
      exact h_final.trans ( Finset.le_sup ( f := fun i => padicValNat p ( m + i ) ) ( show x₀ - m ∈ Finset.Icc 1 k from Finset.mem_Icc.mpr ⟨ Nat.sub_pos_of_lt hx₀.1.1, Nat.sub_le_of_le_add <| by linarith ⟩ ) |> le_trans ( by simp +decide [ Nat.add_sub_of_le ( by linarith : m ≤ x₀ ) ] ) )

/-
The set of integers m <= x such that for some p < 2K, max{v_p(m+i) : 1 <= i <= K} > D / (6 log D).
-/
noncomputable def bad_set_former_lemma_2_4 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_func x), p.Prime ∧
      ∃ i ∈ Finset.Icc 1 (K_func x), (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (6 * Real.log (D_func p x)))

/-
If m % p^j = p^j - i with 1 <= i < p/2, then v_p(binom(2m, m)) >= j.
-/
theorem lemma_carry_prop (p : ℕ) [Fact p.Prime] (m j i : ℕ) (hi : 1 ≤ i) (hip : 2 * i < p) (hcong : m % p^j = p^j - i) :
    padicValNat p (Nat.choose (2 * m) m) ≥ j := by
      -- Since $p^j - 1$ has all its base $p$ digits as $p-1$, which is not less than $p/2$, it has at least $j$ large digits.
      have h_large_digits_count : count_large_digits p (p ^ j - i) ≥ j := by
        -- Since $p^j - i$ has all its base $p$ digits as $p-1$, which is not less than $p/2$, it has at least $j$ large digits.
        have h_large_digits_count : ∀ j ≥ 1, count_large_digits p (p ^ j - i) ≥ j := by
          -- By definition of $p^j - i$, its base $p$ digits are all $p-1$ except the last digit, which is $p-i$.
          intros j hj
          have h_digits : Nat.digits p (p ^ j - i) = (p - i) :: List.replicate (j - 1) (p - 1) := by
            have h_digits : Nat.ofDigits p ((p - i) :: List.replicate (j - 1) (p - 1)) = p ^ j - i := by
              rcases p with ( _ | _ | p ) <;> rcases j with ( _ | _ | j ) <;> simp_all +decide [ Nat.ofDigits ];
              induction j + 1 <;> simp_all +decide [ Nat.pow_succ', Nat.ofDigits_eq_foldr ];
              simp_all +decide [ List.replicate ];
              exact eq_tsub_of_add_eq ( by nlinarith [ Nat.sub_add_cancel ( by linarith : i ≤ p + 1 + 1 ), Nat.sub_add_cancel ( by nlinarith [ pow_pos ( by linarith : 0 < p + 1 + 1 ) ‹_› ] : i ≤ ( p + 1 + 1 ) * ( p + 1 + 1 ) ^ ‹_› ) ] );
            rw [ ← h_digits, Nat.digits_ofDigits ];
            · linarith;
            · grind;
            · grind;
          rcases j <;> simp_all +decide [ count_large_digits ];
          grind;
        by_cases hj : 1 ≤ j <;> aesop;
      -- By Lemma 3.1, $v_p(\binom{2m}{m}) \geq \text{count_large_digits}(p, m)$.
      have h_lemma_3_1 : padicValNat p (Nat.choose (2 * m) m) ≥ count_large_digits p m := by
        convert valuation_ge_large_digits p m;
      -- Since $m \equiv p^j - i \pmod{p^j}$, the base $p$ representation of $m$ ends with the base $p$ representation of $p^j - i$.
      have h_digits_end : (Nat.digits p m).take j = (Nat.digits p (p ^ j - i)) := by
        rw [ ← hcong ];
        have h_digits_eq : Nat.ofDigits p (Nat.digits p m |>.take j) = m % p ^ j := by
          conv_rhs => rw [ ← Nat.ofDigits_digits p m ];
          rw [ ← List.take_append_drop j ( Nat.digits p m ), Nat.ofDigits_append ];
          cases min_cases j ( List.length ( Nat.digits p m ) ) <;> simp +decide [ * ];
          · rw [ Nat.mod_eq_of_lt ];
            refine' Nat.ofDigits_lt_base_pow_length _ _ |> lt_of_lt_of_le <| Nat.pow_le_pow_right ( Nat.Prime.pos Fact.out ) <| by aesop;
            · linarith;
            · exact fun x hx => Nat.digits_lt_base ( Fact.out : Nat.Prime p ).one_lt <| List.mem_of_mem_take hx;
          · rw [ List.drop_eq_nil_of_le ( by linarith ) ] ; norm_num;
            rw [ Nat.mod_eq_of_lt ];
            refine' Nat.ofDigits_lt_base_pow_length _ _ |> lt_of_lt_of_le <| Nat.pow_le_pow_right ( Nat.Prime.pos Fact.out ) <| by aesop;
            · linarith;
            · exact fun x hx => Nat.digits_lt_base ( Fact.out : p.Prime ).one_lt ( List.mem_of_mem_take hx );
        rw [ ← h_digits_eq, Nat.digits_ofDigits ];
        · linarith;
        · exact fun l hl => Nat.digits_lt_base ( Fact.out : p.Prime ).one_lt <| List.mem_of_mem_take hl;
        · intro h_nonempty h_last_zero
          have h_contra : m % p ^ j < p ^ (j - 1) := by
            have h_contra : Nat.ofDigits p (List.take (j - 1) (Nat.digits p m)) < p ^ (j - 1) := by
              refine' Nat.ofDigits_lt_base_pow_length _ _ |> lt_of_lt_of_le <| Nat.pow_le_pow_right ( Nat.Prime.pos Fact.out ) <| by aesop;
              · linarith;
              · exact fun x hx => Nat.digits_lt_base ( Fact.out : p.Prime ).one_lt ( List.mem_of_mem_take hx );
            rcases j <;> simp_all +decide [ Nat.ofDigits_append, List.take_succ ];
            cases h : ( p.digits m)[‹_›]? <;> aesop;
          rcases j with ( _ | j ) <;> simp_all +decide [ pow_succ' ];
          · contradiction;
          · rw [ tsub_lt_iff_left ] at h_contra <;> nlinarith [ pow_pos ( show 0 < p by linarith ) j ];
      -- Since the base $p$ representation of $m$ ends with the base $p$ representation of $p^j - i$, the number of large digits in $m$ is at least the number of large digits in $p^j - i$.
      have h_large_digits_m : count_large_digits p m ≥ count_large_digits p (p ^ j - i) := by
        have h_large_digits_m : (List.filter (fun d => p ≤ 2 * d) (Nat.digits p m)).length ≥ (List.filter (fun d => p ≤ 2 * d) (List.take j (Nat.digits p m))).length := by
          have h_large_digits_m : ∀ {L L' : List ℕ}, List.length (List.filter (fun d => p ≤ 2 * d) (L ++ L')) ≥ List.length (List.filter (fun d => p ≤ 2 * d) L) := by
            grind;
          convert h_large_digits_m using 1;
          rw [ List.take_append_drop ];
        unfold count_large_digits at *; aesop;
      linarith

/-
If p > 2k, then v_p(binom(m+k, k)) <= v_p(binom(2m, m)).
-/
theorem lemma_large_primes (m k : ℕ) (p : ℕ) [Fact p.Prime] (hk : k > 0) (hp : p > 2 * k) :
    padicValNat p (Nat.choose (m + k) k) ≤ padicValNat p (Nat.choose (2 * m) m) := by
      -- If $m \leq k$, then $\binom{m+k}{k} = \binom{m+k}{m}$. Since $p > 2k \geq m+k$, $p$ does not divide $\binom{m+k}{k}$, so LHS is 0.
      by_cases hm : m ≤ k;
      · rw [ padicValNat_choose ];
        any_goals exact Nat.lt_succ_self _;
        · rw [ Nat.log_of_lt ] <;> norm_num ; linarith;
        · grind;
      · -- By lemma_3_3, LHS <= max_{1<=i<=k} v_p(m+i). Let this max be j, achieved at i_0.
        obtain ⟨j, i₀, hi₀⟩ : ∃ j i₀, i₀ ∈ Finset.Icc 1 k ∧ padicValNat p (m + i₀) = j ∧ ∀ i ∈ Finset.Icc 1 k, padicValNat p (m + i) ≤ j := by
          have := Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ 1, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩ ; aesop;
        -- If $j=0$, LHS=0, trivial.
        by_cases hj : j = 0;
        · have h_lhs_zero : padicValNat p (Nat.choose (m + k) k) = 0 := by
            have h_lhs_zero : padicValNat p (Nat.choose (m + k) k) ≤ Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
              convert lemma_3_3 m k p ( by linarith ) hk using 1;
            exact le_antisymm ( h_lhs_zero.trans <| Finset.sup_le fun i hi => by aesop ) ( Nat.zero_le _ );
          exact h_lhs_zero.symm ▸ Nat.zero_le _;
        · -- If $j > 0$, then $p^j | m + i₀$. So $m = A p^j - i₀$.
          obtain ⟨A, hA⟩ : ∃ A, m = A * p^j - i₀ := by
            have h_div : p^j ∣ m + i₀ := by
              rw [ ← hi₀.2.1, padicValNat_dvd_iff ] ; aesop;
            exact ⟨ ( m + i₀ ) / p ^ j, by rw [ Nat.div_mul_cancel h_div, Nat.add_sub_cancel ] ⟩;
          -- Thus $m \equiv -i₀ \pmod{p^j}$. So $m \equiv p^j - i₀ \pmod{p^j}$.
          have h_cong : m % p^j = p^j - i₀ := by
            rw [ hA, Nat.ModEq.symm ];
            exact Nat.mod_eq_of_lt ( Nat.sub_lt ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) ( Finset.mem_Icc.mp hi₀.1 |>.1 ) );
            rw [ Nat.modEq_iff_dvd ];
            rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num;
            · contrapose! hj;
              exact Nat.eq_zero_of_not_pos fun hj' => by nlinarith [ Nat.pow_le_pow_right ( show 1 ≤ p by exact Nat.Prime.pos Fact.out ) hj', Finset.mem_Icc.mp hi₀.1 ] ;
            · exact le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop_cat ) );
          -- By lemma_carry_prop with i=i₀, v_p(binom(2m, m)) >= j.
          have h_carry : padicValNat p (Nat.choose (2 * m) m) ≥ j := by
            apply lemma_carry_prop p m j i₀ (Finset.mem_Icc.mp hi₀.left |>.1) (by
            linarith [ Finset.mem_Icc.mp hi₀.1 ]) h_cong;
          -- By lemma_3_3, LHS <= max_{1<=i<=k} v_p(m+i). Let this max be j, achieved at i_0. So LHS <= j.
          have h_lhs_le_j : padicValNat p (Nat.choose (m + k) k) ≤ j := by
            have := lemma_3_3 m k p ( by linarith ) hk;
            exact this.trans ( Finset.sup_le fun i hi => hi₀.2.2 i hi );
          linarith

/-
If p > 2k, 1 <= i <= k, j >= 1, and p^j | m+i, then v_p(binom(2m, m)) >= j.
-/
theorem lemma_valuation_ge_j (m k p j i : ℕ) [Fact p.Prime] (hk : k > 0) (hp : p > 2 * k) (hi : 1 ≤ i) (hik : i ≤ k) (hj : j ≥ 1) (hdiv : p^j ∣ m + i) :
    padicValNat p (Nat.choose (2 * m) m) ≥ j := by
      -- By lemma_carry_prop, we have v_p(binom(2m, m)) ≥ j.
      apply lemma_carry_prop p m j i hi (by linarith) (by
      obtain ⟨ a, ha ⟩ := hdiv;
      rw [ show m = p ^ j * a - i by rw [ ← ha, Nat.add_sub_cancel ] ];
      rw [ Nat.ModEq.symm, Nat.mod_eq_of_lt ];
      · exact Nat.sub_lt ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) hi;
      · norm_num [ Nat.modEq_iff_dvd ];
        rw [ Nat.cast_sub, Nat.cast_sub ] <;> push_cast <;> repeat nlinarith [ pow_le_pow_right₀ ( show 1 ≤ p by linarith ) hj ] ;
        exact ⟨ a - 1, by ring ⟩)

/-
The bound function for former Lemma 2.4.
-/
noncomputable def bound_former_lemma_2_4_func (x : ℝ) : ℝ :=
  (K_func x : ℝ)^2 * x ^ (1 - 1 / (6 + 6 * Real.log (Real.log x)))

/-
The bound function is o(x).
-/
theorem bound_former_lemma_2_4_is_little_o :
    bound_former_lemma_2_4_func =o[Filter.atTop] (fun x => x) := by
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · unfold bound_former_lemma_2_4_func;
        -- We'll use the fact that $K_func x \approx \exp(\sqrt{\log x})$ to simplify the expression.
        have h_K_approx : Filter.Tendsto (fun x : ℝ => (K_func x : ℝ) ^ 2 * x ^ (-1 / (6 + 6 * Real.log (Real.log x)))) Filter.atTop (nhds 0) := by
          -- We'll use that $K_func x \approx \exp(\sqrt{\log x})$ to bound the expression.
          have h_bound : Filter.Tendsto (fun x => (Real.exp (Real.sqrt (Real.log x)))^2 * x ^ (-1 / (6 + 6 * Real.log (Real.log x)) : ℝ)) Filter.atTop (nhds 0) := by
            -- Simplify the expression inside the limit.
            suffices h_simplify : Filter.Tendsto (fun x => Real.exp (2 * Real.sqrt (Real.log x) - Real.log x / (6 + 6 * Real.log (Real.log x)))) Filter.atTop (nhds 0) by
              refine h_simplify.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx ; rw [ ← Real.exp_nat_mul ] ; rw [ Real.rpow_def_of_pos <| by linarith ] ; ring_nf;
              rw [ ← Real.exp_add, sub_eq_add_neg ];
            -- We'll use the fact that $2 * \sqrt{\log x} - \frac{\log x}{6 + 6 * \log \log x}$ tends to $-\infty$ as $x$ tends to infinity.
            have h_lim : Filter.Tendsto (fun x : ℝ => 2 * Real.sqrt (Real.log x) - Real.log x / (6 + 6 * Real.log (Real.log x))) Filter.atTop Filter.atBot := by
              -- We'll use the fact that $Real.log x / (6 + 6 * Real.log (Real.log x))$ grows faster than $2 * Real.sqrt (Real.log x)$.
              have h_log_growth : Filter.Tendsto (fun x : ℝ => Real.log x / (6 + 6 * Real.log (Real.log x)) / Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
                -- Let $y = \log x$, therefore the expression becomes $\frac{y}{6 + 6 \log y} / \sqrt{y}$.
                suffices h_log : Filter.Tendsto (fun y : ℝ => y / (6 + 6 * Real.log y) / Real.sqrt y) Filter.atTop Filter.atTop by
                  exact h_log.comp ( Real.tendsto_log_atTop );
                -- Let $z = \log y$, therefore the expression becomes $\frac{e^z}{6 + 6z} / e^{z/2} = \frac{e^{z/2}}{6 + 6z}$.
                suffices h_log : Filter.Tendsto (fun z : ℝ => Real.exp (z / 2) / (6 + 6 * z)) Filter.atTop Filter.atTop by
                  have h_log : Filter.Tendsto (fun y : ℝ => Real.exp (Real.log y / 2) / (6 + 6 * Real.log y)) Filter.atTop Filter.atTop := by
                    exact h_log.comp Real.tendsto_log_atTop;
                  refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ show Real.exp ( Real.log y / 2 ) = Real.sqrt y by rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy ] ; ring_nf ] ; rw [ div_right_comm ] ; rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_sub' hy.le ] <;> norm_num );
                -- We can factor out $e^{z/2}$ and use the fact that $e^{z/2} / z \to \infty$ as $z \to \infty$.
                have h_factor : Filter.Tendsto (fun z : ℝ => Real.exp (z / 2) / z) Filter.atTop Filter.atTop := by
                  -- Let $w = \frac{z}{2}$, therefore the expression becomes $\frac{e^w}{2w}$.
                  suffices h_w : Filter.Tendsto (fun w : ℝ => Real.exp w / (2 * w)) Filter.atTop Filter.atTop by
                    convert h_w.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
                  have := Real.tendsto_exp_div_pow_atTop 1;
                  convert this.const_mul_atTop ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) using 2 ; ring;
                rw [ Filter.tendsto_atTop_atTop ] at *;
                exact fun b => by obtain ⟨ i, hi ⟩ := h_factor ( b * 12 ) ; exact ⟨ Max.max i 6, fun a ha => by have := hi a ( le_trans ( le_max_left _ _ ) ha ) ; rw [ le_div_iff₀ ] at * <;> nlinarith [ le_max_right i 6, Real.exp_pos ( a / 2 ) ] ⟩ ;
              have h_exp_neg_inf : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x) * (2 - Real.log x / (6 + 6 * Real.log (Real.log x)) / Real.sqrt (Real.log x))) Filter.atTop Filter.atBot := by
                -- Since $2 - \frac{\log x}{6 + 6 \log \log x} / \sqrt{\log x}$ tends to $-\infty$, multiplying by $\sqrt{\log x}$ (which tends to $\infty$) will also tend to $-\infty$.
                have h_neg_inf : Filter.Tendsto (fun x : ℝ => 2 - Real.log x / (6 + 6 * Real.log (Real.log x)) / Real.sqrt (Real.log x)) Filter.atTop Filter.atBot := by
                  rw [ Filter.tendsto_atTop_atBot ];
                  exact fun b => Filter.eventually_atTop.mp ( h_log_growth.eventually_gt_atTop ( 2 - b ) ) |> fun ⟨ i, hi ⟩ => ⟨ i, fun x hx => by linarith [ hi x hx ] ⟩;
                exact Filter.Tendsto.atTop_mul_atBot₀ ( by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) h_neg_inf;
              refine h_exp_neg_inf.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_sub, mul_div_cancel₀ _ ( ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ) ] ; ring );
            aesop;
          refine' squeeze_zero_norm' _ h_bound ; norm_num [ K_func ];
          exact ⟨ 1, fun x hx => by rw [ abs_of_nonneg ( Real.rpow_nonneg ( by positivity ) _ ) ] ; exact mul_le_mul ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.floor_le ( by positivity ) ) _ ) le_rfl ( by positivity ) ( by positivity ) ⟩;
        refine h_K_approx.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ show ( 1 - 1 / ( 6 + 6 * Real.log ( Real.log x ) ) ) = ( -1 / ( 6 + 6 * Real.log ( Real.log x ) ) ) + 1 by ring ] ; rw [ Real.rpow_add hx, Real.rpow_one ] ; ring_nf; norm_num [ hx.ne' ] );
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
The exponent of p such that p^E divides m+i.
-/
noncomputable def E_func (p : ℕ) (x : ℝ) : ℕ := Nat.floor ((D_func p x : ℝ) / (6 * Real.log (D_func p x))) + 1

/-
If the p-adic valuation is large, then m+i is divisible by a large power of p.
-/
theorem lemma_divisibility_condition (p : ℕ) (x : ℝ) (m i : ℕ) :
    (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (6 * Real.log (D_func p x)) →
    p ^ (E_func p x) ∣ (m + i) := by
      intro h_div;
      have h_padic_ge_E : (padicValNat p (m + i)) ≥ E_func p x := by
        exact Nat.succ_le_of_lt ( Nat.floor_lt ( by positivity ) |>.2 <| by simpa using h_div );
      simp_all +decide [ padicValNat ];
      unfold E_func at *; aesop;

/-
The set of m <= x such that v_p(m+i) is large.
-/
noncomputable def bad_set_p_i (x : ℝ) (p i : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m => (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (6 * Real.log (D_func p x)))

/-
The size of bad_set_p_i is at most x / p^E + 1.
-/
theorem bad_set_p_i_bound (x : ℝ) (p i : ℕ) [Fact p.Prime] (hx : x ≥ 1) :
    ((bad_set_p_i x p i).card : ℝ) ≤ x / (p ^ (E_func p x) : ℝ) + 1 := by
      -- Elements m in bad_set_p_i satisfy v_p(m+i) > ... which implies p^E | m+i.
      -- The number of such m in [1, floor(x)] is at most floor(x)/q + 1 <= x/q + 1.
      have h_count : (bad_set_p_i x p i).card ≤ (Nat.floor x) / p ^ (E_func p x) + 1 := by
        have h_count : ((Finset.Icc 1 (Nat.floor x)).filter (fun m => p ^ (E_func p x) ∣ m + i)).card ≤ (Nat.floor x) / p ^ (E_func p x) + 1 := by
          -- The number of elements in the set $\{m \in \mathbb{N} \mid 1 \leq m \leq \lfloor x \rfloor \text{ and } p^{E_func p x} \mid m + i \}$ is at most $\frac{\lfloor x \rfloor}{p^{E_func p x}} + 1$.
          have h_count_multiples : Finset.card (Finset.filter (fun m => p ^ (E_func p x) ∣ m + i) (Finset.Icc 1 (Nat.floor x))) ≤ Finset.card (Finset.image (fun m => p ^ (E_func p x) * m - i) (Finset.Icc ((i + 1 + p ^ (E_func p x) - 1) / p ^ (E_func p x)) ((Nat.floor x + i) / p ^ (E_func p x)))) := by
            refine Finset.card_mono ?_;
            intro m hm;
            simp +zetaDelta at *;
            obtain ⟨ a, ha ⟩ := hm.2;
            exact ⟨ a, ⟨ Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith, Nat.le_div_iff_mul_le ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) |>.2 <| by linarith ⟩, Nat.sub_eq_of_eq_add <| by linarith ⟩;
          refine le_trans h_count_multiples <| Finset.card_image_le.trans ?_;
          rw [ add_right_comm, Nat.add_div ] <;> norm_num [ Nat.Prime.pos Fact.out ];
          grind;
        exact le_trans ( Finset.card_mono fun m hm => by exact Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hm |>.1, lemma_divisibility_condition p x m i <| Finset.mem_filter.mp hm |>.2 ⟩ ) h_count;
      refine le_trans ( Nat.cast_le.mpr h_count ) ?_;
      simp +zetaDelta at *;
      rw [ le_div_iff₀ ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ) ] ; exact le_trans ( mod_cast Nat.div_mul_le_self _ _ ) <| Nat.floor_le <| by positivity;

/-
The sum of the upper bounds for the size of bad_set_p_i.
-/
noncomputable def sum_upper_bound (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_func x)), ∑ _ ∈ Finset.Icc 1 (K_func x), (x / (p ^ (E_func p x) : ℝ) + 1)

/-
The cardinality of bad_set_former_lemma_2_4 is at most sum_upper_bound.
-/
theorem card_le_sum_upper_bound (x : ℝ) (hx : x ≥ 1) :
    ((bad_set_former_lemma_2_4 x).card : ℝ) ≤ sum_upper_bound x := by
      have h_union : (bad_set_former_lemma_2_4 x).card ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_func x)), ∑ i ∈ Finset.Icc 1 (K_func x), (bad_set_p_i x p i).card := by
        have h_union : (bad_set_former_lemma_2_4 x) ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (2 * K_func x))) (fun p => Finset.biUnion (Finset.Icc 1 (K_func x)) (fun i => bad_set_p_i x p i)) := by
          intro m hm;
          unfold bad_set_former_lemma_2_4 bad_set_p_i at *; aesop;
        exact le_trans ( Finset.card_le_card h_union ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_sum fun p hp => Finset.card_biUnion_le.trans ( Finset.sum_le_sum fun i hi => le_rfl ) ) );
      refine' le_trans ( Nat.cast_le.mpr h_union ) _;
      simp [sum_upper_bound];
      refine' Finset.sum_le_sum fun p hp => _;
      refine' le_trans ( Finset.sum_le_sum fun i hi => show ( Finset.card ( bad_set_p_i x p i ) : ℝ ) ≤ x / p ^ E_func p x + 1 from _ ) _;
      · convert bad_set_p_i_bound x p i _;
        · exact ⟨ Finset.mem_filter.mp hp |>.2 ⟩;
        · linarith;
      · norm_num [ mul_add ]

/-
Simplify sum_upper_bound by evaluating the inner sum.
-/
theorem sum_upper_bound_simpl (x : ℝ) :
    sum_upper_bound x = (K_func x : ℝ) * ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_func x)), (x / (p ^ (E_func p x) : ℝ) + 1) := by
      erw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun p hp => by simp +decide ; ring;

/-
The exponent used in the bound for Lemma 2.4.
-/
noncomputable def exponent_bound (x : ℝ) : ℝ := 1 / (6 + 6 * Real.log (Real.log x))

/-
D_func is bounded by 1 + log x / log 2.
-/
theorem D_le_bound (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 2) :
    (D_func p x : ℝ) ≤ 1 + Real.log x / Real.log 2 := by
      unfold D_func;
      norm_num +zetaDelta at *;
      exact le_trans ( Nat.floor_le ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.log_nonneg ( mod_cast Nat.Prime.pos Fact.out ) ) ) ) ( div_le_div_of_nonneg_left ( Real.log_nonneg ( by linarith ) ) ( Real.log_pos ( by norm_num ) ) ( Real.log_le_log ( by norm_num ) ( mod_cast Nat.Prime.two_le Fact.out ) ) )

/-
For x >= 3, D_func p x <= e * log x.
-/
theorem D_le_e_log_x (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) :
    (D_func p x : ℝ) ≤ Real.exp 1 * Real.log x := by
      -- We know D <= 1 + log x / log 2.
      have h_bound : (D_func p x : ℝ) ≤ 1 + Real.log x / Real.log 2 := by
        convert D_le_bound x p _ using 1 ; linarith [ Real.log_pos one_lt_two ];
      -- Since $x \geq 3$, we have $\log x \geq \log 3 > 1$.
      have h_log_x_ge_one : 1 ≤ Real.log x := by
        rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith );
      have h_exp_log_two : Real.exp 1 * Real.log 2 > 1 + Real.log 2 := by
        have := Real.exp_one_gt_d9.le ; norm_num1 at * ; have := Real.log_two_gt_d9 ; norm_num1 at * ; nlinarith [ Real.add_one_le_exp 1 ];
      nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( Real.log x ) ( ne_of_gt ( Real.log_pos one_lt_two ) ) ]

/-
For sufficiently large x, p^E >= x^exponent.
-/
theorem p_pow_E_ge_x_pow_exponent (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) :
    (p : ℝ) ^ (E_func p x) ≥ x ^ (exponent_bound x) := by
      have h_case2 : (D_func p x : ℝ) ≥ 2 → (p : ℝ) ^ (E_func p x) ≥ x ^ (1 / (6 * Real.log (D_func p x) : ℝ)) := by
        intro hD
        have h_exp : (p : ℝ) ^ (D_func p x) > x := by
          -- Since $D_func p x = 1 + \lfloor \log x / \log p \rfloor$, we have $p^{D_func p x} > x$ by definition of $D_func$.
          have h_p_D_gt_x : (p : ℝ) ^ (Nat.floor (Real.log x / Real.log p) + 1) > x := by
            have := Nat.lt_floor_add_one ( Real.log x / Real.log p );
            rw [ div_lt_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out ) ] at this;
            rw [ gt_iff_lt, ← Real.log_lt_log_iff ( by positivity ) ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ), Real.log_pow ] ; aesop;
          convert h_p_D_gt_x using 1;
          unfold D_func; ring;
        have h_exp : (p : ℝ) ^ (E_func p x) ≥ (p ^ (D_func p x)) ^ (1 / (6 * Real.log (D_func p x) : ℝ)) := by
          have h_exp : (E_func p x : ℝ) ≥ (D_func p x : ℝ) / (6 * Real.log (D_func p x) : ℝ) := by
            exact le_trans ( Nat.lt_floor_add_one _ |> le_of_lt ) ( mod_cast Nat.le_refl _ );
          rw [ ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ];
          exact Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.Prime.pos Fact.out ) ( by ring_nf at *; linarith );
        exact le_trans ( Real.rpow_le_rpow ( by positivity ) ( le_of_lt ‹_› ) ( by exact one_div_nonneg.mpr ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ) ) ) h_exp;
      by_cases hD : (D_func p x : ℝ) ≥ 2;
      · refine le_trans ?_ ( h_case2 hD );
        refine' Real.rpow_le_rpow_of_exponent_le ( by linarith ) _;
        rw [ exponent_bound, div_le_div_iff₀ ] <;> norm_num;
        · have := D_le_e_log_x x p ( by linarith );
          have := Real.log_le_log ( by positivity ) this;
          rw [ Real.log_mul ( by positivity ) ( by linarith [ Real.log_pos ( by linarith : ( 1 : ℝ ) < x ) ] ), Real.log_exp ] at this ; linarith;
        · exact add_pos_of_pos_of_nonneg ( by norm_num ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) );
        · exact Real.log_pos ( by linarith );
      · -- Since $D_func p x < 2$, we have $D_func p x = 1$.
        have hD_eq_1 : D_func p x = 1 := by
          norm_cast at hD; interval_cases _ : D_func p x <;> simp_all +decide ;
          unfold D_func at * ; aesop;
        -- Since $D_func p x = 1$, we have $p > x$.
        have hp_gt_x : (p : ℝ) > x := by
          contrapose! hD_eq_1;
          exact ne_of_gt <| Nat.lt_add_of_pos_right <| Nat.floor_pos.mpr <| by rw [ le_div_iff₀ <| Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out ] ; linarith [ Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) hD_eq_1 ] ;
        refine' le_trans _ ( pow_le_pow_right₀ ( mod_cast Nat.Prime.pos Fact.out ) <| Nat.succ_le_succ <| Nat.zero_le _ );
        refine' le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) _ ) _;
        exact 1;
        · exact div_le_self zero_le_one ( by linarith [ Real.log_nonneg ( show 1 ≤ Real.log x by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ] );
        · norm_num; linarith

/-
If D >= 2, then exponent_bound x <= 1 / (6 log D).
-/
theorem exponent_inequality (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) (hD : (D_func p x : ℝ) ≥ 2) :
    exponent_bound x ≤ 1 / (6 * Real.log (D_func p x)) := by
      rw [ exponent_bound ];
      gcongr;
      · exact mul_pos ( by norm_num ) ( Real.log_pos ( by linarith ) );
      · have := D_le_e_log_x x p ( by linarith );
        have := Real.log_le_log ( by positivity ) this;
        rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.log_pos ( by linarith ) ) ), Real.log_exp ] at this ; linarith

/-
x / p^E <= x^(1 - exponent).
-/
theorem lemma_term_bound (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) (hp : p ∈ Finset.range (2 * K_func x)) :
    x / (p : ℝ) ^ (E_func p x) ≤ x ^ (1 - exponent_bound x) := by
      -- From Lemma~\ref{lem:divisibility_condition} and Definition~\ref{def:E_func}, we have $p^E \ge x^{\text{exponent}}$.
      have h_exp : (p : ℝ) ^ (E_func p x) ≥ x ^ (exponent_bound x) := by
        exact p_pow_E_ge_x_pow_exponent x p hx;
      rw [ Real.rpow_sub ] <;> try positivity;
      gcongr ; aesop

/-
sum_upper_bound is bounded by 2 K^2 (x^(1-exponent) + 1).
-/
theorem sum_upper_bound_le (x : ℝ) (hx : x ≥ 3) :
    sum_upper_bound x ≤ (2 * K_func x : ℝ)^2 * (x ^ (1 - exponent_bound x) + 1) := by
      -- We'll use that $\sum_{p \leq 2K} 1 \leq 2K$.
      have h_sum_primes : (∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_func x)), 1 : ℝ) ≤ (2 * K_func x : ℝ) := by
        norm_num +zetaDelta at *;
        exact_mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num );
      -- Applying the bound from Lemma 2.4 to each term in the sum.
      have h_term_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_func x)), (x / (p : ℝ) ^ (E_func p x) + 1) ≤ (x ^ (1 - exponent_bound x) + 1) := by
        simp +zetaDelta at *;
        intro p hp₁ hp₂; exact (by
        convert lemma_term_bound x p ( by linarith ) ( Finset.mem_range.mpr hp₁ ) using 1;
        exact ⟨ hp₂ ⟩);
      have h_sum_upper_bound_bound : sum_upper_bound x ≤ (K_func x : ℝ) * (2 * K_func x) * (x ^ (1 - exponent_bound x) + 1) := by
        have h_sum_upper_bound_bound : sum_upper_bound x ≤ (K_func x : ℝ) * (∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_func x)), (x ^ (1 - exponent_bound x) + 1)) := by
          rw [ sum_upper_bound_simpl ];
          exact mul_le_mul_of_nonneg_left ( Finset.sum_le_sum h_term_bound ) ( Nat.cast_nonneg _ );
        simp_all +decide [ mul_assoc ];
        exact h_sum_upper_bound_bound.trans ( mul_le_mul_of_nonneg_left ( by nlinarith [ show 0 ≤ x ^ ( 1 - exponent_bound x ) by positivity ] ) ( Nat.cast_nonneg _ ) );
      exact h_sum_upper_bound_bound.trans ( mul_le_mul_of_nonneg_right ( by nlinarith ) ( by positivity ) )

/-
The size of the bad set in Lemma 2.4 is o(x).
-/
theorem former_lemma_2_4 :
    (fun x => ((bad_set_former_lemma_2_4 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      -- Applying the lemma that sum_upper_bound x is bounded by a constant times bound_former_lemma_2_4_func x.
      have h_sum_upper_bound_le : ∀ x : ℝ, x ≥ 3 → sum_upper_bound x ≤ 4 * (bound_former_lemma_2_4_func x + (K_func x)^2) := by
        intro x hx
        have h_sum_upper_bound_le : sum_upper_bound x ≤ (2 * K_func x : ℝ)^2 * (x ^ (1 - exponent_bound x) + 1) := by
          exact sum_upper_bound_le x hx;
        exact h_sum_upper_bound_le.trans_eq ( by rw [ show bound_former_lemma_2_4_func x = ( K_func x : ℝ ) ^ 2 * x ^ ( 1 - exponent_bound x ) by rfl ] ; ring );
      -- Since $bound_former_lemma_2_4_func x$ and $(K_func x)^2$ are both $o(x)$, their sum is also $o(x)$.
      have h_sum_o_x : (fun x : ℝ => bound_former_lemma_2_4_func x + (K_func x)^2) =o[Filter.atTop] (fun x => x) := by
        have h_sum_o_x : (fun x : ℝ => bound_former_lemma_2_4_func x) =o[Filter.atTop] (fun x => x) ∧ (fun x : ℝ => (K_func x : ℝ)^2) =o[Filter.atTop] (fun x => x) := by
          constructor;
          · convert bound_former_lemma_2_4_is_little_o using 1;
          · -- We'll use the fact that $K_func x = \lfloor \exp(\sqrt{\log x}) \rfloor$ to show that $(K_func x)^2$ grows slower than $x$.
            have h_K_func_sq : ∀ x : ℝ, x ≥ 3 → (K_func x : ℝ)^2 ≤ Real.exp (2 * Real.sqrt (Real.log x)) := by
              intros x hx
              have h_K_func_sq : (K_func x : ℝ) ≤ Real.exp (Real.sqrt (Real.log x)) := by
                exact Nat.floor_le ( Real.exp_nonneg _ );
              exact le_trans ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) h_K_func_sq 2 ) ( by rw [ ← Real.exp_nat_mul ] ; ring_nf; norm_num );
            -- We'll use the fact that $Real.exp (2 * Real.sqrt (Real.log x))$ grows slower than $x$.
            have h_exp_growth : Filter.Tendsto (fun x : ℝ => Real.exp (2 * Real.sqrt (Real.log x)) / x) Filter.atTop (nhds 0) := by
              -- Let $y = \sqrt{\log x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{e^{2y}}{e^{y^2}}$.
              suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (2 * y) / Real.exp (y^2)) Filter.atTop (nhds 0) by
                have := h_log.comp ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt ( Real.log x ) ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩ );
                refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Function.comp_apply, Real.sq_sqrt ( Real.log_nonneg hx.le ) ] ; rw [ Real.exp_log ( by positivity ) ] );
              norm_num [ ← Real.exp_sub ];
              exact Filter.tendsto_atTop_atBot.mpr fun x => ⟨ |x| + 2, fun y hy => by cases abs_cases x <;> nlinarith ⟩;
            rw [ Asymptotics.isLittleO_iff_tendsto' ];
            · refine' squeeze_zero_norm' _ h_exp_growth;
              filter_upwards [ Filter.eventually_ge_atTop 3 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( h_K_func_sq x hx ) ( by positivity ) ;
            · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne';
        exact h_sum_o_x.1.add h_sum_o_x.2;
      have h_card_le_sum_upper_bound : ∀ x : ℝ, x ≥ 3 → (bad_set_former_lemma_2_4 x).card ≤ sum_upper_bound x := by
        exact fun x hx => card_le_sum_upper_bound x <| by linarith;
      rw [ Asymptotics.isLittleO_iff_tendsto' ] at *;
      · refine' squeeze_zero_norm' _ ( by simpa using h_sum_o_x.const_mul 4 );
        filter_upwards [ Filter.eventually_ge_atTop 3 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; simpa only [ mul_div_assoc ] using div_le_div_of_nonneg_right ( h_card_le_sum_upper_bound x hx |> le_trans <| h_sum_upper_bound_le x hx ) <| by positivity;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne';
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
K^2 is o(x).
-/
theorem K_sq_is_little_o :
    (fun x => (K_func x : ℝ)^2) =o[Filter.atTop] (fun x => x) := by
      -- We'll use the fact that $K_func x \leq e^{\sqrt{\log x}}$ and $e^{\sqrt{\log x}} \in O(x^{1/2})$.
      have h_bound : ∀ᶠ x in Filter.atTop, (K_func x : ℝ) ≤ Real.exp (Real.sqrt (Real.log x)) := by
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using Nat.floor_le <| by positivity;
      -- Since $e^{2\sqrt{\log x}} / x \to 0$ as $x \to \infty$, we have $K_func x^2 / x \to 0$.
      have h_limit : Filter.Tendsto (fun x : ℝ => Real.exp (2 * Real.sqrt (Real.log x)) / x) Filter.atTop (nhds 0) := by
        -- Let $y = \sqrt{\log x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{e^{2y}}{e^{y^2}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (2 * y) / Real.exp (y^2)) Filter.atTop (nhds 0) by
          have h_subst : Filter.Tendsto (fun x : ℝ => Real.exp (2 * Real.sqrt (Real.log x)) / Real.exp (Real.sqrt (Real.log x)^2)) Filter.atTop (nhds 0) := by
            exact h_log.comp ( by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop );
          refine h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.sq_sqrt ( Real.log_nonneg hx.le ), Real.exp_log ( by positivity ) ] );
        norm_num [ ← Real.exp_sub ];
        exact Filter.tendsto_atTop_atBot.mpr fun x => ⟨ |x| + 2, fun y hy => by cases abs_cases x <;> nlinarith ⟩;
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · refine' squeeze_zero_norm' _ h_limit;
        filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; convert pow_le_pow_left₀ ( by positivity ) hx₁ 2 using 1 ; rw [ ← Real.exp_nat_mul ] ; ring_nf;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
sum_upper_bound is o(x).
-/
theorem sum_upper_bound_is_little_o :
    sum_upper_bound =o[Filter.atTop] (fun x => x) := by
      -- We have sum_upper_bound x ≤ 2 * K^2 * (x^(1-exponent) + 1) ≤ 4 * K^2 * x^(1-exponent) + 4 * K^2.
      have sum_upper_bound_le : ∀ x ≥ 3, sum_upper_bound x ≤ 4 * (K_func x : ℝ)^2 * x ^ (1 - exponent_bound x) + 4 * (K_func x : ℝ)^2 := by
        intro x hx
        have h_le : sum_upper_bound x ≤ (2 * K_func x : ℝ)^2 * (x ^ (1 - exponent_bound x) + 1) := by
          convert sum_upper_bound_le x hx using 1;
        linarith;
      -- Since $bound_former_lemma_2_4_func = o(x)$ and $K^2 = o(x)$, it follows that sum_upper_bound is also $o(x)$.
      have bound_former_lemma_2_4_func_is_little_o : (fun x => (K_func x : ℝ)^2 * x ^ (1 - exponent_bound x)) =o[Filter.atTop] (fun x => x) := by
        have := @bound_former_lemma_2_4_is_little_o;
        convert this using 1;
      have bound_sum_upper_bound : (fun x => 4 * (K_func x : ℝ)^2 * x ^ (1 - exponent_bound x) + 4 * (K_func x : ℝ)^2) =o[Filter.atTop] (fun x => x) := by
        simpa [ mul_assoc ] using Asymptotics.IsLittleO.add ( bound_former_lemma_2_4_func_is_little_o.const_mul_left 4 ) ( K_sq_is_little_o.const_mul_left 4 );
      rw [ Asymptotics.isLittleO_iff ] at *;
      intros c hc; filter_upwards [ bound_sum_upper_bound hc, Filter.eventually_ge_atTop 3 ] with x hx₁ hx₂; rw [ Real.norm_of_nonneg ( show ( sum_upper_bound x : ℝ ) ≥ 0 from ?_ ) ] ; exact le_trans ( sum_upper_bound_le x hx₂ ) ( by simpa only [ Real.norm_of_nonneg ( show ( 0 : ℝ ) ≤ 4 * ( K_func x : ℝ ) ^ 2 * x ^ ( 1 - exponent_bound x ) + 4 * ( K_func x : ℝ ) ^ 2 from by positivity ) ] using hx₁ ) ;
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity;

/-
The property that binom(m+k, k) divides binom(2m, m) for all k <= K(m).
-/
def property_P (m : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (K_func m), Nat.choose (m + k) k ∣ Nat.choose (2 * m) m

/-
The set of integers m <= x that do not satisfy property P.
-/
noncomputable def bad_set_thm (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬ property_P m)

/-
The upper bound for the size of the bad set in Corollary 3.2.
-/
noncomputable def bound_cor_3_2_func (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_func x + 1)), 3 * p * x ^ (1 - 1 / (5 * Real.log p))

/-
The size of bad_set_cor_3_2 is at most bound_cor_3_2_func.
-/
theorem corollary_2_2_card_bound (x : ℝ) (hx : x ≥ 2) :
    ((bad_set_cor_3_2 x).card : ℝ) ≤ bound_cor_3_2_func x := by
      -- The cardinality of the union is at most the sum of the cardinalities.
      have h_union_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_func x + 1)), ((Finset.filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ (D_func p x : ℝ) / (5 * Real.log (D_func p x)))) (Finset.Icc 1 (Nat.floor x))).card ≤ 3 * p * x ^ (1 - 1 / (5 * Real.log p)) := by
        simp +zetaDelta at *;
        field_simp;
        intro p hp hp';
        by_cases hp'' : p ≤ x;
        · convert lemma_3_1 p x hp'' using 1;
          · congr! 2;
            unfold D_func; norm_num [ div_mul_eq_div_div ] ;
            congr! 2 ; ring_nf;
            rw [ show ⌊1 + Real.log x * ( Real.log p ) ⁻¹⌋₊ = ⌊Real.log x * ( Real.log p ) ⁻¹⌋₊ + 1 from Nat.floor_eq_iff ( by exact add_nonneg zero_le_one <| mul_nonneg ( Real.log_nonneg <| by linarith ) <| inv_nonneg.2 <| Real.log_nonneg <| Nat.one_le_cast.2 hp'.pos ) |>.2 ⟨ by norm_num; linarith [ Nat.floor_le <| show 0 ≤ Real.log x * ( Real.log p ) ⁻¹ by exact mul_nonneg ( Real.log_nonneg <| by linarith ) <| inv_nonneg.2 <| Real.log_nonneg <| Nat.one_le_cast.2 hp'.pos ], by norm_num; linarith [ Nat.lt_floor_add_one <| Real.log x * ( Real.log p ) ⁻¹ ] ⟩ ] ; norm_num ; ring_nf;
            constructor <;> intro <;> linarith;
          · ring_nf;
          · exact ⟨ hp' ⟩;
        · refine' le_trans ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) _ ; norm_num;
          refine' le_trans _ ( le_mul_of_one_le_right _ _ );
          · exact le_trans ( Nat.floor_le ( by positivity ) ) ( by linarith );
          · positivity;
          · exact Real.one_le_rpow ( by linarith ) ( div_nonneg ( sub_nonneg.2 <| inv_le_of_inv_le₀ ( by positivity ) <| by linarith [ Real.log_two_gt_d9, Real.log_le_log ( by positivity ) <| show ( p : ℝ ) ≥ 2 by exact_mod_cast hp'.two_le ] ) <| by positivity );
      refine' le_trans _ ( Finset.sum_le_sum h_union_bound );
      norm_cast;
      convert Finset.card_biUnion_le;
      ext; simp [bad_set_cor_3_2];
      · aesop;
      · infer_instance

/-
D / (6 log D) < D / (5 log D) for D >= 2.
-/
theorem inequality_D (y : ℝ) (hy : y ≥ 2) : y / (6 * Real.log y) < y / (5 * Real.log y) := by
  gcongr <;> linarith [ Real.log_pos ( by linarith : 1 < y ) ]

/-
The set of m <= x such that for some k <= K(x), binom(m+k, k) does not divide binom(2m, m).
-/
noncomputable def bad_set_fixed_K (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ k ∈ Finset.Icc 1 (K_func x), ¬ (Nat.choose (m + k) k ∣ Nat.choose (2 * m) m))

/-
Helper lemma: If the valuation conditions for the bad sets hold, we get a contradiction.
-/
theorem lemma_contradiction_core (x : ℝ) (m k p : ℕ) [Fact p.Prime]
    (hx : x ≥ 3) (hm : m ≤ x) (hk : k ∈ Finset.Icc 1 (K_func x))
    (h_val_gt : padicValNat p (Nat.choose (m + k) k) > padicValNat p (Nat.choose (2 * m) m))
    (h_val_large : (padicValNat p (Nat.choose (2 * m) m) : ℝ) > (D_func p x : ℝ) / (5 * Real.log (D_func p x)))
    (h_small_factors : ∀ i ∈ Finset.Icc 1 (K_func x), (padicValNat p (m + i) : ℝ) ≤ (D_func p x : ℝ) / (6 * Real.log (D_func p x))) :
    False := by
      have h_contradiction : padicValNat p (Nat.choose (m + k) k) ≤ D_func p x / (6 * Real.log (D_func p x)) := by
        -- By lemma_3_3, the p-adic valuation of (m+k choose k) is less than or equal to the maximum of the p-adic valuations of m+i for i from 1 to k.
        have h_max : padicValNat p (Nat.choose (m + k) k) ≤ Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
          have h_max : ∀ m k : ℕ, m > k → k > 0 → padicValNat p (Nat.choose (m + k) k) ≤ Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
            exact fun m k a a_1 => lemma_3_3 m k p a a_1;
          by_cases hmk : m > k;
          · exact h_max m k hmk ( Finset.mem_Icc.mp hk |>.1 );
          · rw [ Nat.add_comm, Nat.choose_symm_add ];
            by_cases hmk : m < k;
            · specialize h_max k m hmk;
              rcases m with ( _ | m ) <;> simp_all +decide [ add_comm ];
              refine le_trans h_max ?_;
              simp +arith +decide [ Finset.sup_le_iff ];
              intro i hi₁ hi₂; exact (by
              refine' le_trans _ ( Finset.le_sup ( f := fun i => padicValNat p ( i + ( m + 1 ) ) ) ( show i + ( k - ( m + 1 ) ) ∈ Finset.Icc 1 k from Finset.mem_Icc.mpr ⟨ by linarith [ Nat.sub_add_cancel ( by linarith : m + 1 ≤ k ) ], by linarith [ Nat.sub_add_cancel ( by linarith : m + 1 ≤ k ) ] ⟩ ) );
              grind);
            · grind;
        refine' le_trans ( Nat.cast_le.mpr h_max ) _;
        field_simp;
        refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.sup_le fun i hi => show padicValNat p ( m + i ) ≤ _ from _ ) <| by norm_num ) _;
        exact ⌊ ( D_func p x : ℝ ) / ( 6 * Real.log ( D_func p x ) ) ⌋₊;
        · exact Nat.le_floor <| h_small_factors i <| Finset.Icc_subset_Icc_right ( Finset.mem_Icc.mp hk |>.2 ) hi;
        · convert mul_le_mul_of_nonneg_right ( Nat.floor_le <| show 0 ≤ ( D_func p x : ℝ ) / ( 6 * Real.log ( D_func p x ) ) from div_nonneg ( Nat.cast_nonneg _ ) <| mul_nonneg ( by norm_num ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.pos_of_ne_zero <| ?_ ) <| show ( 0 :ℝ ) ≤ 6 by norm_num using 1 ; ring;
          exact ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| Nat.zero_le _;
      have h_contradiction : (D_func p x : ℝ) / (5 * Real.log (D_func p x)) ≥ (D_func p x : ℝ) / (6 * Real.log (D_func p x)) := by
        field_simp;
        gcongr ; norm_num;
      linarith [ ( by norm_cast : ( padicValNat p ( Nat.choose ( m + k ) k ) : ℝ ) > padicValNat p ( Nat.choose ( 2 * m ) m ) ) ]

/-
If m is not in the bad sets, it satisfies property P.
-/
theorem property_P_of_not_bad (x : ℝ) (m : ℕ) (hx : x ≥ 3) (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (h1 : m ∉ bad_set_cor_3_2 x) (h2 : m ∉ bad_set_former_lemma_2_4 x) : property_P m := by
      intro k hk;
      -- If there exists a prime $p$ such that $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$, then $p \leq 2k$.
      by_contra h_contra
      obtain ⟨p, hp_prime, hp_gt, hp_val⟩ : ∃ p : ℕ, p.Prime ∧ p ≤ 2 * k ∧ padicValNat p (Nat.choose (m + k) k) > padicValNat p (Nat.choose (2 * m) m) := by
        obtain ⟨p, hp_prime, hp_gt⟩ : ∃ p : ℕ, p.Prime ∧ padicValNat p (Nat.choose (m + k) k) > padicValNat p (Nat.choose (2 * m) m) := by
          have h_val_gt : ∃ p, Nat.Prime p ∧ (Nat.factorization (Nat.choose (m + k) k)) p > (Nat.factorization (Nat.choose (2 * m) m)) p := by
            contrapose! h_contra;
            rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
            · exact fun p => if hp : Nat.Prime p then h_contra p hp else by aesop;
            · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ Finset.mem_Icc.mp hm, Finset.mem_Icc.mp hk ] ;
            · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ Finset.mem_Icc.mp hm ] ;
          simp_all +decide [ Nat.factorization ];
          aesop;
        refine ⟨ p, hp_prime, ?_, hp_gt ⟩;
        -- If $p > 2k$, then by lemma_large_primes, we have $padicValNat p (Nat.choose (m + k) k) \leq padicValNat p (Nat.choose (2 * m) m)$.
        by_contra hp_gt_2k
        have h_lemma : padicValNat p (Nat.choose (m + k) k) ≤ padicValNat p (Nat.choose (2 * m) m) := by
          haveI := Fact.mk hp_prime; exact lemma_large_primes m k p ( by linarith [ Finset.mem_Icc.mp hk ] ) ( by linarith [ Finset.mem_Icc.mp hk ] ) ;
        linarith;
      -- Since $p \leq 2k$ and $k \leq K(x)$, we have $p \leq 2K(x)$.
      have hp_le_2K : p ≤ 2 * K_func x := by
        refine' le_trans hp_gt ( Nat.mul_le_mul_left _ <| Nat.le_trans ( Finset.mem_Icc.mp hk |>.2 ) <| Nat.floor_mono <| Real.exp_le_exp.mpr <| Real.sqrt_le_sqrt <| Real.log_le_log _ _ ) <;> norm_num;
        · linarith [ Finset.mem_Icc.mp hm ];
        · exact le_trans ( Nat.cast_le.mpr ( Finset.mem_Icc.mp hm |>.2 ) ) ( Nat.floor_le ( by positivity ) );
      -- Since $p \leq 2K(x)$, we have $v_p(\binom{2m}{m}) > D/(5 \log D)$.
      have hp_val_large : (padicValNat p (Nat.choose (2 * m) m) : ℝ) > (D_func p x : ℝ) / (5 * Real.log (D_func p x)) := by
        simp_all +decide [ bad_set_cor_3_2 ];
        exact h1 p ( by linarith ) hp_prime;
      -- Since $p \leq 2K(x)$, we have $v_p(m+i) \leq D/(6 \log D)$ for all $i \in [1, K(x)]$.
      have hp_val_small : ∀ i ∈ Finset.Icc 1 (K_func x), (padicValNat p (m + i) : ℝ) ≤ (D_func p x : ℝ) / (6 * Real.log (D_func p x)) := by
        simp_all +decide [ bad_set_former_lemma_2_4 ];
        by_cases hp_eq_2K : p = 2 * K_func x;
        · simp_all +decide [ Nat.prime_mul_iff ];
          unfold K_func at hp_prime
          rw [ Nat.floor_eq_iff ( by positivity ) ] at hp_prime ; norm_num at hp_prime;
          exact absurd hp_prime ( not_lt_of_ge ( by exact le_trans ( by norm_num ) ( Real.add_one_le_exp _ ) |> le_trans <| Real.exp_le_exp.mpr <| Real.sqrt_le_sqrt <| show Real.log x ≥ 1 by rw [ ge_iff_le ] ; rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ) );
        · exact h2 p ( lt_of_le_of_ne hp_le_2K hp_eq_2K ) hp_prime;
      have := @lemma_contradiction_core x m k p; simp_all +decide ;
      exact absurd ( this ( Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hm.2 ) ) ) ( by linarith [ show K_func x ≥ K_func m from Nat.floor_mono <| Real.exp_le_exp.mpr <| Real.sqrt_le_sqrt <| Real.log_le_log ( by norm_num; linarith ) <| Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hm.2 ) ] )

/-
The bound for the second bad set is o(x).
-/
noncomputable def E_safe (p : ℕ) (x : ℝ) : ℕ := Nat.floor ((D_func p x : ℝ) / (6 * Real.log (D_func p x))) + 1

/-
The sum of digits of 2m in base 2 is the same as for m.
-/
theorem lemma_s_2_double (m : ℕ) : s_p 2 (2 * m) = s_p 2 m := by
  unfold s_p;
  cases m <;> norm_num

/-
The 2-adic valuation of m+1 is at most the sum of binary digits of m.
-/
theorem lemma_v2_le_s2 (m : ℕ) : padicValNat 2 (m + 1) ≤ s_p 2 m := by
  -- Let j = v_2(m+1). Then 2^j | m+1.
  set j := padicValNat 2 (m + 1) with hj
  have h_div : 2^j ∣ m + 1 := by
    exact Nat.ordProj_dvd _ _;
  -- So m = k 2^j + (2^j - 1) for some k.
  obtain ⟨k, hk⟩ : ∃ k, m = k * 2^j + (2^j - 1) := by
    exact Exists.elim h_div fun k hk => ⟨ k - 1, by nlinarith [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr ( show 2 ^ j ≠ 0 by positivity ) ), Nat.sub_add_cancel ( show 1 ≤ k from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.pos_of_ne_zero ( show m + 1 ≠ 0 by positivity ) ] ) ) ] ⟩;
  -- The binary representation of $m$ ends with $j$ ones.
  have h_binary : Nat.digits 2 m = List.replicate j 1 ++ Nat.digits 2 (k) := by
    rw [ hk ];
    refine Nat.recOn j ?_ fun n hn => ?_ <;> norm_num [ Nat.pow_succ', Nat.mul_mod, Nat.add_mod ] at *;
    rw [ show k * ( 2 * 2 ^ n ) + ( 2 * 2 ^ n - 1 ) = 2 * ( k * 2 ^ n + ( 2 ^ n - 1 ) ) + 1 by zify ; norm_num ; ring ] ; norm_num [ Nat.add_div, Nat.add_mod, Nat.mul_div_assoc, Nat.mul_mod, hn ] ;
    exact rfl;
  unfold s_p; simp +arith +decide [ h_binary ] ;

/-
Lower bound for D_func.
-/
theorem D_ge_sqrt_log_x_div_2 (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 100) (hp : p ∈ Finset.range (2 * K_func x + 1)) :
    (D_func p x : ℝ) ≥ Real.sqrt (Real.log x) / 2 := by
      -- Using the bound for D_func, we have $D \ge \frac{\log x}{\log 2 + \sqrt{\log x}}$.
      have hD_bound : (D_func p x : ℝ) ≥ (Real.log x) / (Real.log 2 + Real.sqrt (Real.log x)) := by
        -- Since $p \leq 2K(x)$, we have $\log p \leq \log(2K(x))$.
        have h_log_p : Real.log p ≤ Real.log 2 + Real.sqrt (Real.log x) := by
          have h_log_p : Real.log p ≤ Real.log (2 * Real.exp (Real.sqrt (Real.log x))) := by
            gcongr ; norm_cast;
            · exact Nat.Prime.pos Fact.out;
            · exact le_trans ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp hp ) ) ( by push_cast [ K_func ] ; exact mul_le_mul_of_nonneg_left ( Nat.floor_le ( by positivity ) ) zero_le_two );
          rwa [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] at h_log_p;
        have h_D_ge_sqrt : (D_func p x : ℝ) ≥ Real.log x / Real.log p := by
          unfold D_func;
          norm_num +zetaDelta at *;
          linarith [ Nat.lt_floor_add_one ( Real.log x / Real.log p ) ];
        exact le_trans ( div_le_div_of_nonneg_left ( Real.log_nonneg ( by linarith ) ) ( Real.log_pos ( by norm_cast; linarith [ Fact.out ( p := p.Prime ) |> Nat.Prime.two_le ] ) ) h_log_p ) h_D_ge_sqrt;
      refine le_trans ?_ hD_bound;
      rw [ div_le_div_iff₀ ] <;> nlinarith only [ Real.sqrt_nonneg ( Real.log x ), Real.sq_sqrt ( show 0 ≤ Real.log x by exact Real.log_nonneg ( by linarith ) ), Real.log_pos one_lt_two, Real.log_le_sub_one_of_pos zero_lt_two, Real.log_le_log ( by positivity ) ( show x ≥ 2 by linarith ) ]

/-
Definition of the property and bad set for Theorem 1.1, and a lemma comparing K_safe with 0.7 log m.
-/
def property_thm_1_1 (m : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)), Nat.descFactorial (m + k) k ∣ Nat.choose (2 * m) m

noncomputable def bad_set_thm_1_1 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬ property_thm_1_1 m)

/-
Definition of the bad set for Lemma 2.1: integers m <= x such that for some prime p < 2 log m, v_p(binom(2m, m)) < 0.49 log m / log p.
-/
noncomputable def bad_set_lemma_2_1 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (Nat.floor (2 * Real.log m)), p.Prime ∧
      (padicValNat p (Nat.choose (2 * m) m) : ℝ) < 0.49 * Real.log m / Real.log p)

/-
Definition of the bad set for a specific prime p: integers m <= x such that p < 2 log m and v_p(binom(2m, m)) is small.
-/
noncomputable def bad_set_p (x : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    (p : ℝ) < 2 * Real.log m ∧ (padicValNat p (Nat.choose (2 * m) m) : ℝ) < 0.49 * Real.log m / Real.log p)

/-
The bad set for Lemma 2.1 is contained in the union of bad sets for each prime p.
-/
theorem bad_set_subset_union (x : ℝ) (hx : x ≥ 1) :
    bad_set_lemma_2_1 x ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1))) (bad_set_p x) := by
      intro m hm;
      unfold bad_set_lemma_2_1 bad_set_p at *;
      field_simp;
      simp +zetaDelta at *;
      rcases hm with ⟨ ⟨ hm₁, hm₂ ⟩, p, hp₁, hp₂, hp₃ ⟩ ; refine' ⟨ p, ⟨ _, hp₂ ⟩, ⟨ hm₁, hm₂ ⟩, _, _ ⟩ <;> norm_num at *;
      · exact Nat.lt_succ_of_le ( Nat.le_trans hp₁.le <| Nat.floor_mono <| mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) <| Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hm₂ ) ) zero_le_two );
      · exact lt_of_lt_of_le ( Nat.cast_lt.mpr hp₁ ) ( Nat.floor_le ( mul_nonneg zero_le_two ( Real.log_nonneg ( Nat.one_le_cast.mpr hm₁ ) ) ) );
      · convert hp₃ using 1 ; ring

/-
The 2-adic valuation of binom(2m, m) is equal to the sum of the binary digits of m.
-/
theorem valuation_two_eq_popcount (m : ℕ) :
    padicValNat 2 (Nat.choose (2 * m) m) = (Nat.digits 2 m).sum := by
      -- Apply the lemma that relates the p-adic valuation of the binomial coefficient to the sum of the digits.
      have h_val : padicValNat 2 (Nat.choose (2 * m) m) = (2 * m - s_p 2 (2 * m)) / (2 - 1) - 2 * (m - s_p 2 m) / (2 - 1) := by
        have h_val : padicValNat 2 (Nat.factorial (2 * m)) = (2 * m - s_p 2 (2 * m)) / (2 - 1) ∧ padicValNat 2 (Nat.factorial m) = (m - s_p 2 m) / (2 - 1) := by
          convert lemma_legendre_digit 2 ( 2 * m ) |> And.intro <| lemma_legendre_digit 2 m;
        rw [ Nat.choose_eq_factorial_div_factorial ( by linarith ) ];
        rw [ padicValNat.div_of_dvd ] <;> norm_num [ two_mul, h_val ];
        · rw [ padicValNat.mul ( by positivity ) ( by positivity ) ] ; ring_nf at * ; aesop;
        · exact Nat.factorial_mul_factorial_dvd_factorial_add _ _;
      -- By definition of $s_p$, we know that $s_p(2m) = s_p(m)$.
      have h_s_p : s_p 2 (2 * m) = s_p 2 m := by
        unfold s_p;
        cases m <;> norm_num;
      simp_all +decide [ Nat.mul_sub_left_distrib ];
      rw [ tsub_right_comm, tsub_tsub_assoc ] <;> norm_num;
      · exact Nat.sub_eq_of_eq_add <| by ring!;
      · exact Nat.digit_sum_le _ _

/-
The number of integers less than 2^D with binary digit sum k is binom(D, k).
-/
theorem card_popcount_eq_choose (D k : ℕ) :
    ((Finset.range (2 ^ D)).filter (fun m => (Nat.digits 2 m).sum = k)).card = Nat.choose D k := by
      -- We'll use induction on $D$. The base case is when $D = 0$.
      induction' D with D ih generalizing k;
      · cases k <;> simp +decide [ Nat.choose ];
      · rcases k with ( _ | k );
        · induction' D + 1 with D ih <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod, Nat.mul_div_assoc ];
          rw [ Finset.card_eq_one ] at ih ⊢;
          use 0; ext m; simp [Finset.mem_filter, Finset.mem_range];
          induction' m using Nat.strong_induction_on with m ih;
          rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.pow_succ' ];
          grind;
        · -- For the inductive step, we can split the set into two parts: those numbers where the least significant bit is 0 and those where it is 1.
          have h_split : Finset.filter (fun m => (Nat.digits 2 m).sum = k + 1) (Finset.range (2 ^ (D + 1))) = Finset.image (fun m => 2 * m) (Finset.filter (fun m => (Nat.digits 2 m).sum = k + 1) (Finset.range (2 ^ D))) ∪ Finset.image (fun m => 2 * m + 1) (Finset.filter (fun m => (Nat.digits 2 m).sum = k) (Finset.range (2 ^ D))) := by
            ext m; simp [Finset.mem_union, Finset.mem_image];
            constructor <;> intro h;
            · rcases Nat.even_or_odd' m with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ pow_succ' ];
              · cases c <;> aesop_cat;
              · exact Or.inr ⟨ by linarith, by norm_num [ Nat.add_div ] at h; linarith ⟩;
            · rcases h with ( ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp_all +decide [ pow_succ' ];
              · cases a <;> simp_all +decide;
              · norm_num [ Nat.add_div ] ; constructor <;> linarith;
          rw [ h_split, Finset.card_union_of_disjoint ];
          · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> simp +arith +decide [ Function.Injective ];
            rw [ ih, ih, Nat.choose_succ_succ, add_comm ];
          · norm_num [ Finset.disjoint_right ];
            intros; omega;

/-
The number of integers less than 2^D with binary digit sum at most K is the sum of binomial coefficients.
-/
theorem card_filter_popcount_le_eq_sum_choose (D K : ℕ) :
    ((Finset.range (2 ^ D)).filter (fun m => (Nat.digits 2 m).sum ≤ K)).card =
    ∑ k ∈ Finset.range (K + 1), Nat.choose D k := by
      -- The set of integers m < 2^D with popcount at most K is the disjoint union of sets with popcount k for k from 0 to K.
      have h_union : (Finset.filter (fun m => (Nat.digits 2 m).sum ≤ K) (Finset.range (2 ^ D))) = Finset.biUnion (Finset.range (K + 1)) (fun k => Finset.filter (fun m => (Nat.digits 2 m).sum = k) (Finset.range (2 ^ D))) := by
        ext m; simp [Finset.mem_biUnion, Finset.mem_filter];
        exact ⟨ fun h => ⟨ Nat.lt_succ_of_le h.2, h.1 ⟩, fun h => ⟨ h.2, Nat.le_of_lt_succ h.1 ⟩ ⟩;
      rw [ h_union, Finset.card_biUnion ];
      · exact Finset.sum_congr rfl fun i hi => by rw [ card_popcount_eq_choose ] ;
      · exact fun i hi j hj hij => Finset.disjoint_filter.2 fun k => by aesop;

/-
Bound for the tail of the binomial sum.
-/
theorem binomial_tail_bound (n : ℕ) :
    ∑ k ∈ Finset.range (Nat.floor ((0.49 : ℝ) * n) + 1), (Nat.choose n k : ℝ) ≤ 2 ^ n * Real.exp (-0.0002 * n) := by
      -- Let $X$ be a binomial random variable with parameters $n$ and $p = \frac{1}{2}$.
      set X : ℕ → ℝ := fun k => (Nat.choose n k : ℝ) / 2 ^ n;
      -- We'll use the fact that $P(X \leq k) \leq \exp(-2n\epsilon^2)$ for $k = \lfloor (1/2 - \epsilon)n \rfloor$.
      have h_tail_bound : ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), (∑ k ∈ Finset.range (Nat.floor ((1 / 2 - ε) * n) + 1), X k) ≤ Real.exp (-2 * ε ^ 2 * n) := by
        intro ε hε
        have h_tail_bound : ∀ t > 0, (∑ k ∈ Finset.range (Nat.floor ((1 / 2 - ε) * n) + 1), X k) ≤ Real.exp (-t * ε * n) * (∑ k ∈ Finset.range (n + 1), X k * Real.exp (-t * (k - n / 2))) := by
          intros t ht
          have h_tail_bound : (∑ k ∈ Finset.range (Nat.floor ((1 / 2 - ε) * n) + 1), X k) ≤ Real.exp (-t * ε * n) * (∑ k ∈ Finset.range (Nat.floor ((1 / 2 - ε) * n) + 1), X k * Real.exp (-t * (k - n / 2))) := by
            rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun i hi => ?_ ; rw [ mul_left_comm ] ; rw [ ← Real.exp_add ] ; ring_nf ; norm_num;
            exact le_mul_of_one_le_right ( by positivity ) ( Real.one_le_exp ( by nlinarith [ show ( i : ℝ ) ≤ ⌊ ( 1 / 2 - ε ) * n⌋₊ by exact_mod_cast Finset.mem_range_succ_iff.mp hi, Nat.floor_le ( show 0 ≤ ( 1 / 2 - ε ) * n by nlinarith [ hε.1, hε.2 ] ), hε.1, hε.2 ] ) );
          refine le_trans h_tail_bound <| mul_le_mul_of_nonneg_left ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono <| Nat.succ_le_succ <| Nat.floor_le_of_le <| by nlinarith [ hε.1, hε.2 ] ) fun _ _ _ => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) <| pow_nonneg zero_le_two _ ) <| Real.exp_nonneg _ ) <| Real.exp_nonneg _;
        -- We'll use the fact that $\sum_{k=0}^{n} \binom{n}{k} \exp(-t(k - n/2)) = (1 + \exp(-t))^n \exp(tn/2)$.
        have h_sum_exp : ∀ t > 0, (∑ k ∈ Finset.range (n + 1), X k * Real.exp (-t * (k - n / 2))) = (1 + Real.exp (-t)) ^ n * Real.exp (t * n / 2) / 2 ^ n := by
          intro t ht; rw [ add_comm 1, add_pow ] ; ring_nf;
          rw [ Finset.sum_mul _ _ _ ] ; rw [ Finset.sum_mul _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ ← Real.exp_nat_mul ] ; ring_nf;
          rw [ Real.exp_add ] ; ring_nf!;
          norm_num ; ring;
        -- We'll use the fact that $(1 + \exp(-t))^n \exp(tn/2) / 2^n \leq \exp(t^2 n / 8)$ for $t > 0$.
        have h_exp_bound : ∀ t > 0, (1 + Real.exp (-t)) ^ n * Real.exp (t * n / 2) / 2 ^ n ≤ Real.exp (t ^ 2 * n / 8) := by
          -- We'll use the fact that $(1 + \exp(-t)) \exp(t/2) / 2 \leq \exp(t^2 / 8)$ for $t > 0$.
          have h_exp_bound : ∀ t > 0, (1 + Real.exp (-t)) * Real.exp (t / 2) / 2 ≤ Real.exp (t ^ 2 / 8) := by
            intro t ht
            have h_exp_bound : (1 + Real.exp (-t)) * Real.exp (t / 2) / 2 ≤ Real.exp (t ^ 2 / 8) := by
              have h_exp_bound_step : Real.cosh (t / 2) ≤ Real.exp (t ^ 2 / 8) := by
                -- We'll use the fact that $\cosh(x) \leq \exp(x^2 / 2)$ for all $x$.
                have h_cosh_exp : ∀ x : ℝ, Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by
                  exact fun x ↦ Real.cosh_le_exp_half_sq x;
                convert h_cosh_exp ( t / 2 ) using 1 ; ring_nf
              convert h_exp_bound_step using 1 ; rw [ Real.cosh_eq ] ; ring_nf;
              rw [ ← Real.exp_add ] ; ring_nf;
            exact h_exp_bound;
          intro t ht; convert pow_le_pow_left₀ ( by positivity ) ( h_exp_bound t ht ) n using 1 <;> ring_nf;
          · rw [ show ( Real.exp ( -t ) * Real.exp ( t * ( 1 / 2 ) ) * ( 1 / 2 ) + Real.exp ( t * ( 1 / 2 ) ) * ( 1 / 2 ) ) = ( Real.exp ( t * ( 1 / 2 ) ) * ( 1 / 2 ) ) * ( 1 + Real.exp ( -t ) ) by ring ] ; rw [ mul_pow ] ; ring_nf;
            rw [ ← Real.exp_nat_mul ] ; ring_nf;
          · rw [ ← Real.exp_nat_mul ] ; ring_nf;
        -- Let's choose $t = 4\epsilon$.
        set t : ℝ := 4 * ε;
        refine le_trans ( h_tail_bound t ( mul_pos zero_lt_four hε.1 ) ) ?_;
        rw [ h_sum_exp t ( mul_pos zero_lt_four hε.1 ) ] ; convert mul_le_mul_of_nonneg_left ( h_exp_bound t ( mul_pos zero_lt_four hε.1 ) ) ( Real.exp_nonneg ( -t * ε * n ) ) using 1 ; rw [ ← Real.exp_add ] ; ring_nf;
        exact congr_arg Real.exp ( by ring );
      specialize h_tail_bound 0.01 ; norm_num at *;
      rw [ ← Finset.sum_div _ _ _, div_le_iff₀ ] at * <;> first | positivity | linarith;

/-
The sum of exponentials of the sum of digits factors into a product.
-/
open Real

lemma sum_exp_digit_sum (p D : ℕ) (t : ℝ) :
    ∑ f : Fin D → Fin p, exp (t * ∑ i, (f i).val) = (∑ v : Fin p, exp (t * v.val)) ^ D := by
      simp +decide [ Finset.mul_sum _ _ _, Real.exp_sum ];
      rw [ eq_comm, ← Fin.prod_const ];
      rw [ Finset.prod_sum ];
      refine' Finset.sum_bij ( fun f _ => fun i => f i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +contextual;
      · simp +contextual [ funext_iff ];
      · exact fun b => ⟨ fun i _ => b i, rfl ⟩

/-
Hoeffding's lemma for the uniform distribution on {0, ..., p-1}.
-/
open Real

lemma hoeffding_lemma_bounded (p : ℕ) (t : ℝ) (hp : p ≥ 1) :
    let μ := (p - 1 : ℝ) / 2
    (∑ v : Fin p, exp (t * (v.val - μ))) ≤ p * exp (t ^ 2 * (p - 1) ^ 2 / 8) := by
      -- Let $X$ be a random variable uniformly distributed on $\{0, \dots, p-1\}$. The mean of $X$ is $\mu = \frac{p-1}{2}$.
      set μ : ℝ := (p - 1) / 2
      have h_mean : (∑ v : Fin p, (v.val : ℝ)) = p * μ := by
        simp +zetaDelta at *;
        exact Nat.recOn p ( by norm_num ) fun n ih => by norm_num [ Fin.sum_univ_castSucc ] at * ; linarith;
      -- The sum of exponentials can be bounded using the inequality $\exp(x) + \exp(-x) \leq 2 \exp(x^2 / 2)$.
      have h_exp_bound : ∀ v : Fin p, Real.exp (t * (v.val - μ)) + Real.exp (-t * (v.val - μ)) ≤ 2 * Real.exp (t^2 * (p - 1)^2 / 8) := by
        -- Apply the inequality $\exp(x) + \exp(-x) \leq 2 \exp(x^2 / 2)$ to each term in the sum.
        intros v
        have h_exp_ineq : Real.exp (t * (v.val - μ)) + Real.exp (-t * (v.val - μ)) ≤ 2 * Real.exp (t^2 * (v.val - μ)^2 / 2) := by
          have h_exp_ineq : ∀ x : ℝ, Real.exp x + Real.exp (-x) ≤ 2 * Real.exp (x^2 / 2) := by
            intro x
            have h_exp_bound : Real.cosh x ≤ Real.exp (x^2 / 2) := by
              exact cosh_le_exp_half_sq x;
            rw [ Real.cosh_eq ] at h_exp_bound ; linarith;
          convert h_exp_ineq ( t * ( v - μ ) ) using 2 <;> ring_nf;
        refine le_trans h_exp_ineq ?_;
        norm_num +zetaDelta at *;
        nlinarith only [ show ( v : ℝ ) ^ 2 ≤ ( p - 1 ) * v by nlinarith only [ show ( v : ℝ ) + 1 ≤ p by norm_cast; linarith [ Fin.is_lt v ] ], show ( v : ℝ ) ^ 2 ≥ 0 by positivity, show ( p : ℝ ) ≥ 1 by norm_cast ];
      have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_exp_bound i; simp_all +decide [ Finset.sum_add_distrib ] ;
      have h_sum_exp : ∑ v : Fin p, Real.exp (-(t * (v.val - μ))) = ∑ v : Fin p, Real.exp (t * (v.val - μ)) := by
        apply Finset.sum_bij (fun v _ => Fin.rev v);
        · simp;
        · aesop;
        · exact fun b _ => ⟨ Fin.rev b, Finset.mem_univ _, Fin.rev_rev b ⟩;
        · simp +zetaDelta at *;
          intro a; rw [ Nat.cast_sub ( by linarith [ Fin.is_lt a ] ) ] ; push_cast; ring;
      linarith

/-
Hoeffding's inequality for the sum of digits.
-/
open Real

theorem hoeffding_digit_sum_bound (p D : ℕ) (ε : ℝ) (hε : ε > 0) (hp : p ≥ 2) :
    ((Finset.univ : Finset (Fin D → Fin p)).filter (fun f => (∑ i, (f i).val : ℝ) - D * (p - 1) / 2 ≥ ε * D)).card ≤ (p ^ D : ℝ) * exp (-2 * ε ^ 2 * D / (p - 1)^2) := by
      -- Apply Hoeffding's lemma to bound the sum of exponentials.
      have h_hoeffding_bound : (∑ f : Fin D → Fin p, Real.exp (4 * ε * (∑ i, (f i : ℝ) - D * (p - 1) / 2) / (p - 1) ^ 2)) ≤ (p : ℝ) ^ D * Real.exp (2 * ε ^ 2 * D / (p - 1) ^ 2) := by
        have h_hoeffding_bound : (∑ f : Fin D → Fin p, Real.exp (4 * ε * (∑ i, (f i : ℝ) - D * (p - 1) / 2) / (p - 1) ^ 2)) ≤ (∑ v : Fin p, Real.exp (4 * ε * (v.val - (p - 1) / 2) / (p - 1) ^ 2)) ^ D := by
          have := @sum_exp_digit_sum p D ( 4 * ε / ( p - 1 ) ^ 2 );
          convert mul_le_mul_of_nonneg_left this.le ( Real.exp_nonneg ( - ( 4 * ε * D * ( p - 1 ) ) / ( 2 * ( p - 1 ) ^ 2 ) ) ) using 1;
          · rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; rw [ ← Real.exp_add ] ; push_cast ; ring_nf;
            rw [ show ( 2 - p * 4 + p ^ 2 * 2 : ℝ ) = 2 * ( 1 - p * 2 + p ^ 2 ) by ring ] ; norm_num ; ring;
          · rw [ show ( ∑ v : Fin p, Real.exp ( 4 * ε * ( v.val - ( p - 1 ) / 2 ) / ( p - 1 ) ^ 2 ) ) = ( ∑ v : Fin p, Real.exp ( 4 * ε / ( p - 1 ) ^ 2 * v.val ) ) * Real.exp ( - ( 4 * ε * ( p - 1 ) ) / ( 2 * ( p - 1 ) ^ 2 ) ) from ?_ ];
            · rw [ mul_pow, ← Real.exp_nat_mul ] ; ring_nf;
            · rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; rw [ ← Real.exp_add ] ; ring_nf;
              rw [ show ( 2 - p * 4 + p ^ 2 * 2 : ℝ ) = 2 * ( 1 - p * 2 + p ^ 2 ) by ring ] ; norm_num ; ring;
        -- Apply Hoeffding's lemma to the sum of exponentials.
        have h_hoeffding_lemma : (∑ v : Fin p, Real.exp (4 * ε * (v.val - (p - 1) / 2) / (p - 1) ^ 2)) ≤ (p : ℝ) * Real.exp (2 * ε ^ 2 / (p - 1) ^ 2) := by
          have := hoeffding_lemma_bounded p ( 4 * ε / ( p - 1 ) ^ 2 ) ( by linarith );
          grind;
        exact h_hoeffding_bound.trans ( le_trans ( pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) h_hoeffding_lemma _ ) ( by rw [ mul_pow, ← Real.exp_nat_mul ] ; ring_nf; norm_num ) );
      -- Apply the exponential bound to relate the sum of exponentials to the cardinality of the set.
      have h_card_bound : (∑ f : Fin D → Fin p, Real.exp (4 * ε * (∑ i, (f i : ℝ) - D * (p - 1) / 2) / (p - 1) ^ 2)) ≥ (Finset.filter (fun f : Fin D → Fin p => (∑ i, (f i : ℝ)) - D * (p - 1) / 2 ≥ ε * D) Finset.univ).card * Real.exp (4 * ε * (ε * D) / (p - 1) ^ 2) := by
        have h_card_bound : (∑ f : Fin D → Fin p, Real.exp (4 * ε * (∑ i, (f i : ℝ) - D * (p - 1) / 2) / (p - 1) ^ 2)) ≥ (∑ f ∈ Finset.filter (fun f : Fin D → Fin p => (∑ i, (f i : ℝ)) - D * (p - 1) / 2 ≥ ε * D) Finset.univ, Real.exp (4 * ε * (ε * D) / (p - 1) ^ 2)) := by
          exact le_trans ( Finset.sum_le_sum fun x hx => Real.exp_le_exp.mpr <| by gcongr ; aesop ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Real.exp_nonneg _ );
        aesop;
      rw [ show ( -2 * ε ^ 2 * ( D : ℝ ) / ( p - 1 ) ^ 2 ) = ( 2 * ε ^ 2 * ( D : ℝ ) / ( p - 1 ) ^ 2 ) - ( 4 * ε * ( ε * ( D : ℝ ) ) / ( p - 1 ) ^ 2 ) by ring, Real.exp_sub ];
      rw [ mul_div, le_div_iff₀ ( Real.exp_pos _ ) ] ; linarith

/-
Definitions of carries in base p addition of m+m.
-/
def carries (p : ℕ) (D : ℕ) (d : Fin D → Fin p) : Fin D → ℕ
| i =>
  if h : i.val = 0 then
    if 2 * (d i).val ≥ p then 1 else 0
  else
    let c_prev := carries p D d ⟨i.val - 1, by
      exact lt_of_le_of_lt ( Nat.pred_le _ ) i.2⟩
    if 2 * (d i).val + c_prev ≥ p then 1 else 0
termination_by i => i.val

def num_carries (p : ℕ) (D : ℕ) (d : Fin D → Fin p) : ℕ :=
  ∑ i, carries p D d i

/-
Definition of the i-th digit of m in base p.
-/
def digits_of (p D m : ℕ) [Fact p.Prime] : Fin D → Fin p :=
  fun i => ⟨(m / p ^ i.val) % p, by
    exact Nat.mod_lt _ ( Nat.Prime.pos Fact.out )⟩

/-
The carry at position i corresponds to the overflow of the sum modulo p^(i+1).
-/
theorem carry_eq_one_iff (p : ℕ) [Fact p.Prime] (D : ℕ) (m : ℕ) (i : Fin D) (hm : m < p ^ D) :
    carries p D (digits_of p D m) i = 1 ↔ p ^ (i.val + 1) ≤ 2 * (m % p ^ (i.val + 1)) := by
      induction' i with i ih;
      induction' i with i ih generalizing m;
      · unfold carries digits_of; aesop;
      · unfold carries;
        simp +zetaDelta at *;
        rw [ show m % p ^ ( i + 1 + 1 ) = ( m % p ^ ( i + 1 ) ) + p ^ ( i + 1 ) * ( m / p ^ ( i + 1 ) % p ) from ?_, Nat.mul_comm ];
        · rw [ show carries p D ( digits_of p D m ) ⟨ i, by linarith ⟩ = if p ^ ( i + 1 ) ≤ 2 * ( m % p ^ ( i + 1 ) ) then 1 else 0 from ?_ ];
          · split_ifs;
            · constructor <;> intro <;> norm_num [ pow_succ, digits_of ] at *;
              · nlinarith [ Nat.zero_le ( m % ( p ^ i * p ) ), Nat.zero_le ( m / ( p ^ i * p ) % p ), Nat.mod_lt m ( show p ^ i * p > 0 from mul_pos ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) ( Nat.Prime.pos Fact.out ) ), Nat.mod_lt ( m / ( p ^ i * p ) ) ( show p > 0 from Nat.Prime.pos Fact.out ) ];
              · nlinarith [ pow_pos ( Fact.out ( p := p.Prime ) |> Nat.Prime.pos ) i, pow_succ' p i, Nat.zero_le ( m % ( p ^ i * p ) ), Nat.mod_lt m ( show p ^ i * p > 0 from mul_pos ( pow_pos ( Fact.out ( p := p.Prime ) |> Nat.Prime.pos ) i ) ( Fact.out ( p := p.Prime ) |> Nat.Prime.pos ) ), Nat.zero_le ( m / ( p ^ i * p ) % p ) ];
            · rw [ show digits_of p D m ⟨ i + 1, ih ⟩ = ⟨ m / p ^ ( i + 1 ) % p, Nat.mod_lt _ ( Nat.Prime.pos Fact.out ) ⟩ from ?_ ];
              · constructor <;> intro <;> nlinarith [ pow_pos ( Fact.out ( p := p.Prime ) |> Nat.Prime.pos ) ( i + 1 ), pow_succ' p ( i + 1 ), Nat.zero_le ( m % p ^ ( i + 1 ) ), Nat.zero_le ( m / p ^ ( i + 1 ) % p ), Nat.mod_lt ( m / p ^ ( i + 1 ) ) ( Fact.out ( p := p.Prime ) |> Nat.Prime.pos ) ];
              · exact rfl;
          · split_ifs <;> simp_all +decide [ Nat.pow_succ' ];
            contrapose! ih;
            refine' ⟨ m, hm, _, _ ⟩;
            (expose_names; exact Nat.lt_of_succ_lt ih_1);
            exact Or.inl ⟨ by exact Nat.le_antisymm ( by
              -- By definition of `carries`, each carry is either 0 or 1.
              have h_carries_le_one : ∀ i : Fin D, carries p D (digits_of p D m) i ≤ 1 := by
                intro i; induction' i with i ih; unfold carries; aesop;
              exact h_carries_le_one _ ) ( Nat.pos_of_ne_zero ih ), by assumption ⟩;
        · exact Nat.mod_pow_succ

/-
The number of carries is the number of indices satisfying the carry condition.
-/
theorem num_carries_eq_card (p : ℕ) [Fact p.Prime] (D : ℕ) (m : ℕ) (hm : m < p ^ D) :
    num_carries p D (digits_of p D m) = ((Finset.range D).filter (fun i => p ^ (i + 1) ≤ 2 * (m % p ^ (i + 1)))).card := by
      have h_num_carries_eq_sum_carries : num_carries p D (digits_of p D m) = Finset.card (Finset.filter (fun i => carries p D (digits_of p D m) i = 1) (Finset.univ : Finset (Fin D))) := by
        have h_num_carries_eq_sum_carries : ∀ (f : Fin D → ℕ), (∀ i, f i ≤ 1) → (Finset.univ.filter (fun i => f i = 1)).card = ∑ i, f i := by
          intro f hf; rw [ Finset.card_filter ] ; exact Finset.sum_congr rfl fun i hi => by have := hf i; interval_cases f i <;> trivial;
        rw [ h_num_carries_eq_sum_carries ];
        · exact rfl;
        · intro i; unfold carries; aesop;
      rw [ h_num_carries_eq_sum_carries, Finset.card_filter ];
      rw [ Finset.card_filter, Finset.sum_range ];
      congr! 2;
      (expose_names; exact carry_eq_one_iff p D m x hm)

/-
The number of carries equals the p-adic valuation.
-/
theorem num_carries_eq_valuation (p : ℕ) [Fact p.Prime] (D : ℕ) (m : ℕ) (hm : m < p ^ D) :
    num_carries p D (digits_of p D m) = padicValNat p (Nat.choose (2 * m) m) := by
      rw [ padicValNat_choose ];
      any_goals exact Nat.lt_succ_self _;
      · rw [ num_carries_eq_card ];
        · refine' Finset.card_bij ( fun i hi => i + 1 ) _ _ _ <;> simp +decide;
          · intro a ha h; refine' ⟨ _, _ ⟩ <;> norm_num [ two_mul, Nat.add_mod ] at *;
            · refine' Nat.le_log_of_pow_le ( Nat.Prime.one_lt Fact.out ) _;
              exact le_trans h ( add_le_add ( Nat.mod_le _ _ ) ( Nat.mod_le _ _ ) );
            · exact h;
          · intro b hb₁ hb₂ hb₃; use b - 1; rcases b with ( _ | b ) <;> simp_all +decide [ two_mul ] ;
            refine' lt_of_lt_of_le hb₂ _;
            exact Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ( by linarith [ show m > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ] ) ( by rw [ pow_succ' ] ; nlinarith [ show p > 1 from Nat.Prime.one_lt Fact.out ] ) );
        · exact hm;
      · grind

/-
Concentration of valuation for p=2.
-/
theorem valuation_concentration_p_2 (D : ℕ) :
    ((Finset.range (2 ^ D)).filter (fun m => (padicValNat 2 (Nat.choose (2 * m) m) : ℝ) < 0.49 * D)).card ≤ 2 ^ D * Real.exp (-0.0002 * D) := by
      -- Apply the binomial tail bound to the sum in the Hoeffding bound.
      have h_binom_tail : ∑ k ∈ Finset.range (Nat.floor ((0.49 : ℝ) * D) + 1), (Nat.choose D k : ℝ) ≤ 2 ^ D * Real.exp (-0.0002 * D) := by
        convert binomial_tail_bound D using 1;
      have h_card_popcount : ((Finset.range (2 ^ D)).filter (fun m => (Nat.digits 2 m).sum ≤ Nat.floor ((0.49 : ℝ) * D))).card = ∑ k ∈ Finset.range (Nat.floor ((0.49 : ℝ) * D) + 1), (Nat.choose D k : ℝ) := by
        rw_mod_cast [ card_filter_popcount_le_eq_sum_choose ];
      refine le_trans ?_ h_binom_tail;
      rw [ ← h_card_popcount ];
      gcongr;
      intro m hm; exact Nat.le_floor <| by simpa [ valuation_two_eq_popcount ] using hm.le;

/-
The larger root of the characteristic polynomial is an eigenvalue.
-/
noncomputable def matrix_T (p : ℕ) (z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  !![H, L; z * L, z * H]

noncomputable def lambda_plus (p : ℕ) (z : ℝ) : ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  (H * (1 + z) + Real.sqrt ((H * (1 + z)) ^ 2 - 4 * z * (H ^ 2 - L ^ 2))) / 2

theorem lambda_plus_is_eigenvalue (p : ℕ) (z : ℝ) (hp : p ≥ 2) (hz : z > 0) :
    let M := matrix_T p z
    let lam := lambda_plus p z
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ Matrix.mulVec M v = lam • v := by
      -- A non-trivial solution to (M - lam*I)v = 0 exists if and only if the determinant of (M - lam*I) is zero, which is the characteristic polynomial evaluated at lam, which is zero by definition.
      have h_det : Matrix.det (matrix_T p z - Matrix.diagonal ![lambda_plus p z, lambda_plus p z]) = 0 := by
        unfold lambda_plus matrix_T;
        norm_num [ Matrix.det_fin_two ];
        linarith [ Real.mul_self_sqrt ( show 0 <= ( ↑ ( ( p + 1 ) / 2 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ↑ ( ( p + 1 ) / 2 ) ^ 2 - ↑ ( p / 2 ) ^ 2 ) by nlinarith [ sq_nonneg ( ( ↑ ( ( p + 1 ) / 2 ) * ( 1 + z ) ) - 2 * z * ↑ ( ( p + 1 ) / 2 ) ) ] ) ];
      obtain ⟨ v, hv ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h_det;
      use v;
      simp_all +decide [ sub_eq_iff_eq_add, Matrix.sub_mulVec ];
      ext i; fin_cases i <;> norm_num [ Matrix.mulVec ] ;

/-
Weighted sum of carries.
-/
noncomputable def weighted_sum (p D : ℕ) (z : ℝ) [Fact p.Prime] : ℝ :=
  ∑ m ∈ Finset.range (p ^ D), z ^ (num_carries p D (digits_of p D m))

/-
Definitions for the matrix recurrence proof.
-/
def carry_out (p D : ℕ) (d : Fin D → Fin p) : ℕ :=
  if h : D = 0 then 0 else carries p D d ⟨D - 1, by apply Nat.sub_lt; exact Nat.pos_of_ne_zero h; exact Nat.one_pos⟩

noncomputable def weighted_vector (p D : ℕ) (z : ℝ) [Fact p.Prime] : Fin 2 → ℝ :=
  fun c => ∑ d : Fin D → Fin p, if carry_out p D d = c.val then z ^ num_carries p D d else 0

/-
Base case for the weighted vector.
-/
open Matrix

theorem weighted_vector_zero (p : ℕ) (z : ℝ) [Fact p.Prime] :
    weighted_vector p 0 z = ![1, 0] := by
      ext c;
      unfold weighted_vector;
      fin_cases c <;> norm_num [ carry_out, num_carries ]

/-
The carry out is at most 1.
-/
theorem carry_out_le_one (p D : ℕ) (d : Fin D → Fin p) : carry_out p D d ≤ 1 := by
  unfold carry_out;
  unfold carries; aesop;

/-
The number of carries for D+1 digits decomposes into the carries for the first D digits plus the last carry.
-/
theorem num_carries_succ (p D : ℕ) (d : Fin (D + 1) → Fin p) :
    let d_init := d ∘ Fin.castSucc
    num_carries p (D + 1) d = num_carries p D d_init + carries p (D + 1) d (Fin.last D) := by
      -- By definition of `num_carries`, we can split the sum into the sum for `d_init` and the carry at the last position.
      simp [num_carries, Fin.sum_univ_castSucc];
      congr! 1;
      -- By definition of carries, we can split the sum into the sum for the first D digits plus the carry from the last digit. We'll use induction on D.
      induction' ‹Fin D› with i ih;
      -- By definition of `carries`, the carry at position `i` in `D + 1` digits is the same as the carry at position `i` in `D` digits.
      have h_carries_eq : ∀ (i : Fin D), carries p (D + 1) d (Fin.castSucc i) = carries p D (d ∘ Fin.castSucc) i := by
        intros i
        induction' i with i ih;
        induction' i using Nat.strong_induction_on with i ih;
        unfold carries;
        rcases i with ( _ | i ) <;> simp_all +decide
        rw [ ih i ( Nat.lt_succ_self i ) ( by linarith ) ];
      exact h_carries_eq ⟨ i, ih ⟩

/-
The carry out of D+1 digits is the carry at the last position.
-/
theorem carry_out_succ (p D : ℕ) (d : Fin (D + 1) → Fin p) :
    carry_out p (D + 1) d = carries p (D + 1) d (Fin.last D) := by
      unfold carry_out carries; aesop;

/-
The carry at the last position is determined by the last digit and the carry out from the previous digits.
-/
theorem carries_last_eq (p D : ℕ) (d : Fin (D + 1) → Fin p) :
    let d_init := d ∘ Fin.castSucc
    let c := carry_out p D d_init
    let x := (d (Fin.last D)).val
    carries p (D + 1) d (Fin.last D) = if 2 * x + c ≥ p then 1 else 0 := by
      -- By definition of `carries`, we know that `carries p (D + 1) d (Fin.last D)` is determined by the last digit and the carry out from the previous digits.
      unfold carries;
      rcases D with ( _ | D ) <;> simp_all +decide [ carry_out ];
      congr! 3;
      -- By definition of `carries`, we know that `carries p (D + 2) d ⟨D, by sorry⟩` is equal to `carries p (D + 1) (d ∘ Fin.castSucc) ⟨D, by sorry⟩` because the first `D + 1` digits are the same.
      have h_carries_eq : ∀ (i : Fin (D + 1)), carries p (D + 2) d ⟨i.val, by
        linarith [ Fin.is_lt i ]⟩ = carries p (D + 1) (d ∘ Fin.castSucc) ⟨i.val, by
        exact i.2⟩ := by
        intro i;
        induction' i using Fin.inductionOn with i IH;
        · unfold carries; aesop;
        · unfold carries; aesop;
      generalize_proofs at *;
      exact h_carries_eq ⟨ D, by linarith ⟩

/-
The number of digits x producing a specific carry given a previous carry.
-/
theorem count_transitions (p : ℕ) [Fact p.Prime] (c_prev : ℕ) (c : ℕ) (hp : p ≥ 2) (hc_prev : c_prev ≤ 1) (hc : c ≤ 1) :
    let H := (p + 1) / 2
    let L := p / 2
    ((Finset.univ : Finset (Fin p)).filter (fun x => (if 2 * x.val + c_prev >= p then 1 else 0) = c)).card =
    if c = 0 then
      if c_prev = 0 then H else L
    else
      if c_prev = 0 then L else H := by
        interval_cases c <;> interval_cases c_prev <;> norm_num;
        · rw [ Finset.card_eq_of_bijective ];
          use fun i hi => ⟨ i, by linarith [ Nat.div_mul_le_self ( p + 1 ) 2 ] ⟩;
          · grind;
          · exact fun i hi => by norm_num; linarith [ Nat.div_mul_le_self ( p + 1 ) 2 ] ;
          · aesop;
        · rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
          · have := Nat.prime_mul_iff.mp ( Fact.out : Nat.Prime ( 2 * k ) ) ; aesop;
          · rw [ show Finset.filter ( fun x : Fin ( 2 * k + 1 ) => ( x : ℕ ) < k ) Finset.univ = Finset.Iio ⟨ k, by linarith ⟩ by ext x; aesop ] ; norm_num [ Nat.add_div ];
        · rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num;
          · rw [ show ( { x : Fin ( 2 * k ) | k ≤ ( x : ℕ ) } : Finset ( Fin ( 2 * k ) ) ) = Finset.Ici ⟨ k, by linarith ⟩ by ext; aesop ] ; simp +decide [ * ];
            rw [ two_mul, Nat.add_sub_cancel ];
          · rw [ show ( Finset.filter ( fun x : Fin ( 2 * k + 1 ) => 2 * k + 1 ≤ 2 * ( x : ℕ ) ) Finset.univ : Finset ( Fin ( 2 * k + 1 ) ) ) = Finset.Ici ⟨ k + 1, by linarith ⟩ from ?_ ];
            · simp +arith +decide [ Nat.add_div ];
              rw [ two_mul, Nat.add_sub_cancel ];
            · ext ⟨ x, hx ⟩ ; simp +decide [ Nat.succ_le_iff ] ;
        · rw [ show ( { x : Fin p | p ≤ 2 * ( x : ℕ ) + 1 } : Finset ( Fin p ) ) = Finset.Ici ⟨ p / 2, Nat.div_lt_of_lt_mul <| by linarith [ Nat.div_add_mod p 2, Nat.mod_lt p two_pos ] ⟩ from ?_ ];
          · norm_num [ Nat.add_div ];
            grind;
          · ext ⟨ x, hx ⟩ ; simp +decide [ Nat.div_le_iff_le_mul_add_pred ]

/-
The entries of the transition matrix correspond to the weighted counts of digit transitions.
-/
theorem matrix_entries (p : ℕ) [Fact p.Prime] (z : ℝ) (c c_prev : Fin 2) (hp : p ≥ 2) :
    ((Finset.univ : Finset (Fin p)).filter (fun x => (if 2 * x.val + c_prev.val >= p then 1 else 0) = c.val)).card * z ^ c.val = matrix_T p z c c_prev := by
      -- Apply the count_transitions lemma to count the transitions.
      have h_card : ((Finset.univ : Finset (Fin p)).filter (fun x => (if 2 * x.val + c_prev.val >= p then 1 else 0) = c.val)).card =
        if c.val = 0 then
          if c_prev.val = 0 then (p + 1) / 2 else p / 2
        else
          if c_prev.val = 0 then p / 2 else (p + 1) / 2 := by
            convert count_transitions p c_prev c hp ( Fin.is_le c_prev ) ( Fin.is_le c ) using 1;
      fin_cases c <;> fin_cases c_prev <;> simp_all +decide;
      · unfold matrix_T; aesop;
      · unfold matrix_T; aesop;
      · unfold matrix_T; norm_num; ring;
      · unfold matrix_T; ring_nf;
        exact rfl

/-
The weighted vector satisfies the matrix recurrence relation.
-/
theorem weighted_vector_recurrence (p D : ℕ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) :
    weighted_vector p (D + 1) z = Matrix.mulVec (matrix_T p z) (weighted_vector p D z) := by
      unfold weighted_vector matrix_T;
      ext c; simp +decide [ Matrix.mulVec, dotProduct ] ;
      -- We can split the sum into two parts: one where the carry out from the first D digits is 0 and one where it's 1.
      have h_split : ∑ d : Fin (D + 1) → Fin p, (if (carry_out p (D + 1) d : ℕ) = c then z ^ (num_carries p (D + 1) d) else 0) =
        ∑ d_init : Fin D → Fin p, ∑ d_last : Fin p, (if (if 2 * (d_last : ℕ) + (carry_out p D d_init : ℕ) ≥ p then 1 else 0) = c then z ^ (num_carries p D d_init + (if 2 * (d_last : ℕ) + (carry_out p D d_init : ℕ) ≥ p then 1 else 0)) else 0) := by
          rw [ ← Finset.sum_product' ];
          refine' Finset.sum_bij ( fun x _ => ( x ∘ Fin.castSucc, x ( Fin.last _ ) ) ) _ _ _ _ <;> simp +decide;
          · exact fun a₁ a₂ h₁ h₂ => funext fun i => by cases i using Fin.lastCases <;> simpa [ * ] using congr_fun h₁ ‹_›;
          · exact fun a b => ⟨ Fin.snoc a b, by ext i; simp +decide, by simp +decide ⟩;
          · intro a; rw [ num_carries_succ, carry_out_succ ] ;
            rw [ carries_last_eq ];
            fin_cases c <;> simp +decide [ Fin.ext_iff ];
      -- We can split the sum into two parts: one where the carry out from the first D digits is 0 and one where it's 1, and then factor out the common terms.
      have h_split_sum : ∑ d_init : Fin D → Fin p, ∑ d_last : Fin p, (if (if 2 * (d_last : ℕ) + (carry_out p D d_init : ℕ) ≥ p then 1 else 0) = c then z ^ (num_carries p D d_init + (if 2 * (d_last : ℕ) + (carry_out p D d_init : ℕ) ≥ p then 1 else 0)) else 0) =
        ∑ d_init : Fin D → Fin p, (if (carry_out p D d_init : ℕ) = 0 then z ^ (num_carries p D d_init) * (∑ d_last : Fin p, if (if 2 * (d_last : ℕ) ≥ p then 1 else 0) = c then z ^ (if 2 * (d_last : ℕ) ≥ p then 1 else 0) else 0) else 0) +
        ∑ d_init : Fin D → Fin p, (if (carry_out p D d_init : ℕ) = 1 then z ^ (num_carries p D d_init) * (∑ d_last : Fin p, if (if 2 * (d_last : ℕ) + 1 ≥ p then 1 else 0) = c then z ^ (if 2 * (d_last : ℕ) + 1 ≥ p then 1 else 0) else 0) else 0) := by
          rw [ ← Finset.sum_add_distrib ];
          refine' Finset.sum_congr rfl fun x hx => _;
          have := carry_out_le_one p D x; interval_cases carry_out p D x <;> simp +decide [ Finset.mul_sum _ _ _ ] ;
          · exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp +decide [ *, pow_add ] ;
          · exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp_all +decide [ pow_add ] ;
      -- Apply the matrix_entries theorem to replace the sums over d_last with the matrix entries.
      have h_matrix_entries : ∀ c_prev c : Fin 2, (∑ d_last : Fin p, if (if 2 * (d_last : ℕ) + c_prev.val ≥ p then 1 else 0) = c then z ^ (if 2 * (d_last : ℕ) + c_prev.val ≥ p then 1 else 0) else 0) = (matrix_T p z) c c_prev := by
        intro c_prev c; exact (by
        have := matrix_entries p z c c_prev hp; simp_all +decide [ Finset.sum_ite ] ;
        fin_cases c <;> fin_cases c_prev <;> simp_all +decide [ Finset.filter_filter ]);
      simp_all +decide [ Finset.sum_ite ];
      fin_cases c <;> simp +decide [ Finset.mul_sum _ _ _, h_matrix_entries ];
      · simp_all +decide [ mul_comm, matrix_T ];
      · unfold matrix_T; norm_num; ring_nf;

/-
The weighted sum is the sum of the components of the weighted vector.
-/
theorem weighted_sum_eq_sum_components (p D : ℕ) (z : ℝ) [Fact p.Prime] :
    weighted_sum p D z = (weighted_vector p D z 0) + (weighted_vector p D z 1) := by
      unfold weighted_vector;
      rw [ ← Finset.sum_add_distrib ];
      refine' Finset.sum_bij ( fun x _ => digits_of p D x ) _ _ _ _ <;> simp +decide;
      · intro a₁ ha₁ a₂ ha₂ h; simp_all +decide [ funext_iff, digits_of ] ;
        -- By induction on $D$, we can show that if the digits of $a₁$ and $a₂$ are the same, then $a₁ = a₂$.
        have h_ind : ∀ D : ℕ, ∀ a₁ a₂ : ℕ, a₁ < p ^ D → a₂ < p ^ D → (∀ x : Fin D, a₁ / p ^ (x : ℕ) % p = a₂ / p ^ (x : ℕ) % p) → a₁ = a₂ := by
          intro D a₁ a₂ ha₁ ha₂ h; induction' D with D ih generalizing a₁ a₂ <;> simp_all +decide [ Nat.pow_succ', Nat.div_div_eq_div_mul ] ;
          -- By the induction hypothesis, since $a₁ < p * p^D$ and $a₂ < p * p^D$, and their digits are the same, we have $a₁ / p = a₂ / p$.
          have h_div : a₁ / p = a₂ / p := by
            apply ih (a₁ / p) (a₂ / p);
            · exact Nat.div_lt_of_lt_mul <| by linarith;
            · exact Nat.div_lt_of_lt_mul <| by linarith;
            · intro x; specialize h ⟨ x + 1, by linarith [ Fin.is_lt x ] ⟩ ; simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ;
          have := h ⟨ 0, Nat.zero_lt_succ _ ⟩ ; simp_all +decide [ Nat.div_eq_of_lt ] ;
          nlinarith [ Nat.mod_add_div a₁ p, Nat.mod_add_div a₂ p ];
        exact h_ind D a₁ a₂ ha₁ ha₂ h;
      · intro b
        use Nat.ofDigits p (List.ofFn (fun i => (b i).val));
        constructor;
        · convert Nat.ofDigits_lt_base_pow_length _ _ using 1;
          · norm_num;
          · exact Nat.Prime.one_lt Fact.out;
          · grind;
        · ext i; simp +decide [ List.ofFn_eq_map ] ;
          have h_digit : ∀ (L : List ℕ), (∀ d ∈ L, d < p) → ∀ i < List.length L, (Nat.ofDigits p L / p ^ i) % p = L.get! i := by
            intros L hL i hi;
            induction' L with d L ih generalizing i <;> simp_all +decide [ Nat.ofDigits ];
            rcases i with ( _ | i ) <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
            · exact Nat.mod_eq_of_lt hL.1;
            · rw [ Nat.add_mul_div_left _ _ ( Nat.Prime.pos Fact.out ) ];
              rw [ Nat.div_eq_of_lt hL.1 ] ; aesop;
          convert h_digit _ _ _ _ <;> aesop;
      · intro a ha; have := carry_out_le_one p D ( digits_of p D a ) ; interval_cases carry_out p D ( digits_of p D a ) <;> simp +decide ;

/-
The weighted vector at step D is the D-th power of the transition matrix applied to the initial vector.
-/
theorem weighted_vector_eq_matrix_pow (p D : ℕ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) :
    weighted_vector p D z = Matrix.mulVec (matrix_T p z ^ D) (weighted_vector p 0 z) := by
      induction D <;> simp_all +decide [ pow_succ' ];
      rw [ ← Matrix.mulVec_mulVec, ← ‹weighted_vector p _ z = matrix_T p z ^ _ *ᵥ weighted_vector p 0 z›, weighted_vector_recurrence ] ; aesop_cat

/-
lambda_plus is a root of the characteristic polynomial.
-/
theorem lambda_plus_is_root (p : ℕ) (z : ℝ) (hp : p ≥ 2) :
    let H : ℝ := ((p + 1) / 2 : ℕ)
    let L : ℝ := (p / 2 : ℕ)
    let lam := lambda_plus p z
    lam ^ 2 - H * (1 + z) * lam + z * (H ^ 2 - L ^ 2) = 0 := by
      unfold lambda_plus; ring_nf;
      rw [ Real.sq_sqrt ] <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] <;> ring_nf at * ; norm_num at *;
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
      · norm_num [ Nat.add_div ] ; nlinarith [ sq_nonneg ( z - 1 ), sq_nonneg ( z + 1 ) ];
      · norm_num [ Nat.add_div ] ; ring_nf;
        nlinarith [ sq_nonneg ( z - 1 ), sq_nonneg ( z + 1 ), show ( k : ℝ ) ≥ 1 by norm_cast; linarith ]

/-
The larger eigenvalue is at least H.
-/
theorem lam_ge_H (p : ℕ) (z : ℝ) (hp : p ≥ 2) (hz : z ≥ 0) :
    lambda_plus p z ≥ ((p + 1) / 2 : ℕ) := by
      refine' le_div_iff₀' ( by norm_num ) |>.2 _;
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
      · norm_num [ Nat.add_div ];
        rw [ Real.sqrt_sq ] <;> nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ k ) ];
      · norm_num [ Nat.add_div ] ; ring_nf;
        nlinarith [ sq_nonneg ( z - 1 ), Real.sqrt_nonneg ( 1 + ( k * 2 - k * z * 4 ) + k * z ^ 2 * 2 + k ^ 2 + k ^ 2 * z * 2 + ( k ^ 2 * z ^ 2 - z * 2 ) + z ^ 2 ), Real.mul_self_sqrt ( show 0 <= 1 + ( k * 2 - k * z * 4 ) + k * z ^ 2 * 2 + k ^ 2 + k ^ 2 * z * 2 + ( k ^ 2 * z ^ 2 - z * 2 ) + z ^ 2 by nlinarith [ sq_nonneg ( z - 1 ) ] ) ]

/-
L is positive for p >= 2.
-/
theorem L_pos (p : ℕ) (hp : p ≥ 2) : (p / 2 : ℝ) > 0 := by
  positivity

/-
The vector [L, lam - H] is an eigenvector of the transition matrix.
-/
theorem eigenvector_components (p : ℕ) (z : ℝ) (hp : p ≥ 2) (hz : z ≥ 0) :
    let H : ℝ := ((p + 1) / 2 : ℕ)
    let L : ℝ := (p / 2 : ℕ)
    let lam := lambda_plus p z
    let u : Fin 2 → ℝ := ![L, lam - H]
    Matrix.mulVec (matrix_T p z) u = lam • u := by
      ext i;
      fin_cases i;
      · unfold matrix_T; norm_num [ Matrix.mulVec ] ; ring;
      · unfold matrix_T; norm_num [ dotProduct ] ; ring_nf;
        rw [ show ( ( 1 + p ) / 2 : ℕ ) = ( p + 1 ) / 2 by ring_nf ] ; have := lambda_plus_is_root p z hp; norm_num at * ; nlinarith;

/-
lambda_minus is the other root of the characteristic polynomial.
-/
noncomputable def lambda_minus (p : ℕ) (z : ℝ) : ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  (H * (1 + z) - Real.sqrt ((H * (1 + z)) ^ 2 - 4 * z * (H ^ 2 - L ^ 2))) / 2

theorem lambda_minus_is_root (p : ℕ) (z : ℝ) (hp : p ≥ 2) :
    let H : ℝ := ((p + 1) / 2 : ℕ)
    let L : ℝ := (p / 2 : ℕ)
    let lam := lambda_minus p z
    lam ^ 2 - H * (1 + z) * lam + z * (H ^ 2 - L ^ 2) = 0 := by
      unfold lambda_minus; ring_nf;
      rw [ Real.sq_sqrt ] <;> norm_num [ Nat.add_div ] ; ring;
      split_ifs <;> ring_nf <;> norm_num at * <;> nlinarith [ sq_nonneg ( z - 1 ), sq_nonneg ( z + 1 ) ]

/-
The discriminant of the characteristic polynomial is positive for z >= 0.
-/
theorem discriminant_pos (p : ℕ) (z : ℝ) (hp : p ≥ 2) (hz : z ≥ 0) :
    let H : ℝ := ((p + 1) / 2 : ℕ)
    let L : ℝ := (p / 2 : ℕ)
    (H * (1 + z)) ^ 2 - 4 * z * (H ^ 2 - L ^ 2) > 0 := by
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
      · norm_num [ Nat.add_div ] ; ring_nf ; positivity;
      · norm_num [ Nat.add_div ] ; ring_nf;
        nlinarith [ sq_nonneg ( z - 1 ), show ( k : ℝ ) ≥ 1 by norm_cast; linarith ]

/-
u_minus is an eigenvector for lambda_minus.
-/
noncomputable def u_plus (p : ℕ) (z : ℝ) : Fin 2 → ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  ![L, lambda_plus p z - H]

noncomputable def u_minus (p : ℕ) (z : ℝ) : Fin 2 → ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  ![L, lambda_minus p z - H]

theorem eigenvector_minus (p : ℕ) (z : ℝ) (hp : p ≥ 2) :
    Matrix.mulVec (matrix_T p z) (u_minus p z) = (lambda_minus p z) • (u_minus p z) := by
      unfold matrix_T u_minus; ext i; fin_cases i <;> norm_num ; ring;
      unfold lambda_minus; ring_nf;
      rw [ Real.sq_sqrt ] <;> ring_nf;
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.add_div ] <;> ring_nf;
      · nlinarith [ sq_nonneg ( k * z + k ) ];
      · nlinarith [ sq_nonneg ( z - 1 ), sq_nonneg ( z + 1 ), show ( k : ℝ ) ≥ 1 by norm_cast; linarith ]

/-
The initial vector [1, 0] can be decomposed into a linear combination of the eigenvectors.
-/
noncomputable def c_plus (p : ℕ) (z : ℝ) : ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  let lam_plus := lambda_plus p z
  let lam_minus := lambda_minus p z
  (H - lam_minus) / (L * (lam_plus - lam_minus))

noncomputable def c_minus (p : ℕ) (z : ℝ) : ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  let lam_plus := lambda_plus p z
  let lam_minus := lambda_minus p z
  (lam_plus - H) / (L * (lam_plus - lam_minus))

theorem vector_decomposition (p : ℕ) (z : ℝ) (hp : p ≥ 2) (hz : z ≥ 0) :
    let u_p := u_plus p z
    let u_m := u_minus p z
    let c_p := c_plus p z
    let c_m := c_minus p z
    ![1, 0] = c_p • u_p + c_m • u_m := by
      have h_c_plus : ((p / 2 : ℕ) : ℝ) ≠ 0 := by
        exact ne_of_gt <| Nat.cast_pos.mpr <| Nat.div_pos ( by linarith ) zero_lt_two;
      have h_discriminant : let H : ℝ := ((p + 1) / 2 : ℕ) ; let L : ℝ := (p / 2 : ℕ) ; (H * (1 + z)) ^ 2 - 4 * z * (H ^ 2 - L ^ 2) > 0 := by
        apply discriminant_pos p z hp hz;
      unfold u_plus u_minus c_plus c_minus;
      unfold lambda_plus lambda_minus; norm_num; ring_nf;
      grind

/-
The weighted vector has a closed form expression in terms of eigenvalues and eigenvectors.
-/
theorem weighted_vector_closed_form (p D : ℕ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hz : z ≥ 0) :
    let u_p := u_plus p z
    let u_m := u_minus p z
    let c_p := c_plus p z
    let c_m := c_minus p z
    let lam_p := lambda_plus p z
    let lam_m := lambda_minus p z
    weighted_vector p D z = (c_p * lam_p ^ D) • u_p + (c_m * lam_m ^ D) • u_m := by
      -- We use the matrix power formula `weighted_vector p D z = (matrix_T p z ^ D) *v (weighted_vector p 0 z)`.
      have h_matrix : weighted_vector p D z = (Matrix.mulVec (matrix_T p z ^ D) ![1, 0]) := by
        convert weighted_vector_eq_matrix_pow p D z hp;
        ext i ; fin_cases i <;> norm_num [ weighted_vector_zero ];
      -- We decompose `![1, 0] = c_p • u_p + c_m • u_m`.
      have h_decomp : ![1, 0] = c_plus p z • u_plus p z + c_minus p z • u_minus p z := by
        exact vector_decomposition p z hp hz;
      -- Since `u_p` and `u_m` are eigenvectors, `(matrix_T p z ^ D) *v u_p = lam_p ^ D • u_p` and similarly for `u_m`.
      have h_eigen : Matrix.mulVec (matrix_T p z ^ D) (u_plus p z) = lambda_plus p z ^ D • u_plus p z ∧ Matrix.mulVec (matrix_T p z ^ D) (u_minus p z) = lambda_minus p z ^ D • u_minus p z := by
        have h_eigen : Matrix.mulVec (matrix_T p z) (u_plus p z) = lambda_plus p z • u_plus p z ∧ Matrix.mulVec (matrix_T p z) (u_minus p z) = lambda_minus p z • u_minus p z := by
          exact ⟨ eigenvector_components p z hp hz, eigenvector_minus p z hp ⟩;
        refine' Nat.recOn D _ _ <;> simp_all +decide [ pow_succ' ];
        intro n hn hn'; simp_all +decide [ ← Matrix.mulVec_mulVec ] ;
        simp_all +decide [ Matrix.mulVec_smul ];
        exact ⟨ by rw [ smul_smul, mul_comm ], by rw [ smul_smul, mul_comm ] ⟩;
      rw [ h_matrix, h_decomp, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h_eigen.1, h_eigen.2 ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, smul_smul ]

/-
The weighted vector has a closed form expression in terms of eigenvalues and eigenvectors.
-/
theorem weighted_vector_closed_form_v2 (p D : ℕ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hz : z ≥ 0) :
    let u_p := u_plus p z
    let u_m := u_minus p z
    let c_p := c_plus p z
    let c_m := c_minus p z
    let lam_p := lambda_plus p z
    let lam_m := lambda_minus p z
    weighted_vector p D z = (c_p * lam_p ^ D) • u_p + (c_m * lam_m ^ D) • u_m := by
      convert weighted_vector_closed_form p D z hp hz using 1

/-
The weighted sum for p=2 is (1+z)^D.
-/
theorem weighted_sum_two (D : ℕ) (z : ℝ) (hz : z ≥ 0) :
    weighted_sum 2 D z = (1 + z) ^ D := by
      rw [ weighted_sum_eq_sum_components ];
      rw [ weighted_vector_closed_form_v2 ];
      · unfold c_plus c_minus lambda_plus lambda_minus u_plus u_minus; norm_num; ring_nf;
        unfold lambda_plus lambda_minus; ring_nf;
        rw [ show 1 + z * 2 + z ^ 2 = ( 1 + z ) ^ 2 by ring, Real.sqrt_sq ( by positivity ) ] ; ring_nf;
        nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( 1 + z ) ≠ 0 ) ( ( 1 + z ) ^ D ) ];
      · norm_num;
      · exact hz

/-
Chernoff bound for the number of integers with small 2-adic valuation of the middle binomial coefficient.
-/
theorem chernoff_bound_p2 (D : ℕ) (k : ℝ) (z : ℝ) (hz : 0 < z) (hz1 : z ≤ 1) :
    ((Finset.range (2 ^ D)).filter (fun m => (padicValNat 2 (Nat.choose (2 * m) m) : ℝ) ≤ k)).card ≤ (1 + z) ^ D * z ^ (-k) := by
      -- By the definition of `bad_set_lemma_2_1`, for each `m` in the bad set, the binary digit sum of `m` is at most `k`.
      have h_bad_set : ∀ m ∈ ((Finset.range (2 ^ D)).filter (fun m => (padicValNat 2 (Nat.choose (2 * m) m) : ℝ) ≤ k)), z ^ (padicValNat 2 (Nat.choose (2 * m) m) : ℝ) ≥ z ^ k := by
        exact fun m hm => Real.rpow_le_rpow_of_exponent_ge hz hz1 <| by aesop;
      have h_sum_bound : (∑ m ∈ (Finset.range (2 ^ D)).filter (fun m => (padicValNat 2 (Nat.choose (2 * m) m) : ℝ) ≤ k), z ^ (padicValNat 2 (Nat.choose (2 * m) m) : ℝ)) ≤ (1 + z) ^ D := by
        have h_sum_bound : (∑ m ∈ (Finset.range (2 ^ D)), z ^ (padicValNat 2 (Nat.choose (2 * m) m) : ℝ)) = (1 + z) ^ D := by
          convert weighted_sum_two D z hz.le using 1;
          refine' Finset.sum_congr rfl fun m hm => _;
          rw [ num_carries_eq_valuation ];
          · norm_cast;
          · exact Finset.mem_range.mp hm;
        exact h_sum_bound ▸ Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => by positivity;
      have := Finset.sum_le_sum h_bad_set; simp_all +decide [ Real.rpow_neg hz.le ] ;
      nlinarith [ Real.rpow_pos_of_pos hz k, mul_inv_cancel_left₀ ( ne_of_gt ( Real.rpow_pos_of_pos hz k ) ) ( ( 1 + z ) ^ D ) ]

/-
The largest eigenvalue at z=1 is p.
-/
theorem lambda_plus_at_one (p : ℕ) (hp : p ≥ 2) : lambda_plus p 1 = p := by
  unfold lambda_plus;
  rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num <;> ring_nf <;> norm_num;
  · norm_num [ Nat.add_div ] ; ring;
  · norm_num [ Nat.add_div ] ; ring

/-
General Chernoff bound for p-adic valuation.
-/
theorem weighted_sum_bound_general (p D : ℕ) (k : ℝ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    ((Finset.range (p ^ D)).filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ k)).card ≤ weighted_sum p D z * z ^ (-k) := by
      rw [ Real.rpow_neg hz.le ];
      rw [ ← div_eq_mul_inv, le_div_iff₀ ( Real.rpow_pos_of_pos hz _ ) ];
      have h_card_le_sum : ((Finset.filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ k) (Finset.range (p ^ D))).card : ℝ) * z ^ k ≤ ∑ m ∈ Finset.filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ k) (Finset.range (p ^ D)), z ^ (num_carries p D (digits_of p D m)) := by
        have h_card_le_sum : ∀ m ∈ Finset.filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ k) (Finset.range (p ^ D)), z ^ k ≤ z ^ (num_carries p D (digits_of p D m)) := by
          intros m hm
          have h_num_carries : num_carries p D (digits_of p D m) ≤ k := by
            have := num_carries_eq_valuation p D m ( by aesop ) ; aesop;
          exact_mod_cast Real.rpow_le_rpow_of_exponent_ge hz hz1 h_num_carries;
        simpa using Finset.sum_le_sum h_card_le_sum;
      refine le_trans h_card_le_sum ?_;
      refine' Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => by positivity;
      exact Finset.filter_subset _ _

/-
Definition of the discriminant of the characteristic polynomial.
-/
noncomputable def discriminant (p : ℕ) (z : ℝ) : ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  (H * (1 + z)) ^ 2 - 4 * z * (H ^ 2 - L ^ 2)

/-
The value of the discriminant at z=1.
-/
theorem discriminant_at_one (p : ℕ) (hp : p ≥ 2) :
    discriminant p 1 = (2 * (p / 2 : ℕ) : ℝ) ^ 2 := by
      unfold discriminant; ring;

/-
The derivative of the discriminant at z=1.
-/
theorem deriv_discriminant_at_one (p : ℕ) (hp : p ≥ 2) :
    deriv (discriminant p) 1 = (2 * (p / 2 : ℕ) : ℝ) ^ 2 := by
      unfold discriminant; norm_num [ mul_add ] ; ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm ]

/-
The derivative of the largest eigenvalue at z=1 is p/2.
-/
theorem deriv_lambda_plus_at_one (p : ℕ) (hp : p ≥ 2) :
    deriv (lambda_plus p) 1 = (p : ℝ) / 2 := by
      unfold lambda_plus;
      ring_nf;
      norm_num [ mul_assoc ];
      erw [ deriv_add ] <;> norm_num;
      · rw [ deriv_sqrt ] <;> norm_num <;> ring_nf;
        · rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num <;> ring_nf;
          · norm_num [ Nat.add_div ] ; ring_nf;
            simpa [ sq ] using by ring;
          · norm_num [ Nat.add_div ] ; ring_nf;
            simpa [ sq ] using by ring;
        · aesop;
      · field_simp;
        apply_rules [ DifferentiableAt.div, DifferentiableAt.sqrt ] <;> norm_num;
        linarith

/-
The derivative of the smaller eigenvalue at z=1.
-/
theorem deriv_lambda_minus_at_one (p : ℕ) (hp : p ≥ 2) :
    deriv (lambda_minus p) 1 = (((p + 1) / 2 : ℕ) - (p / 2 : ℕ) : ℝ) / 2 := by
      apply HasDerivAt.deriv;
      convert HasDerivAt.div_const ( HasDerivAt.sub ( HasDerivAt.const_mul _ <| hasDerivAt_id 1 |> HasDerivAt.const_add _ ) <| HasDerivAt.sqrt ( show HasDerivAt ( fun z : ℝ => ( ( ( p + 1 ) / 2 : ℕ ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( ( p + 1 ) / 2 : ℕ ) ^ 2 - ( p / 2 : ℕ ) ^ 2 ) ) _ _ from hasDerivAt_deriv_iff.mpr ?_ ) ?_ ) _ using 1 <;> norm_num;
      · norm_num [ add_comm, mul_comm ];
        rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num <;> ring_nf <;> norm_num;
        · simpa [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < c by linarith ) ] using by ring;
        · grind;
      · fun_prop;
      · norm_num [ Nat.add_div ] ; ring_nf ; aesop

/-
If f(x0) = g(x0) and f'(x0) > g'(x0), then f(x) < g(x) for some x < x0.
-/
theorem local_inequality_left (f g : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableAt ℝ f x₀) (hg : DifferentiableAt ℝ g x₀)
    (heq : f x₀ = g x₀) (hderiv : deriv f x₀ > deriv g x₀) :
    ∃ x < x₀, f x < g x := by
      have h_lim : Filter.Tendsto (fun x => (f x - g x) / (x - x₀)) (nhdsWithin x₀ (Set.Iio x₀)) (nhds (deriv f x₀ - deriv g x₀)) := by
        have h_lim : HasDerivAt (fun x => f x - g x) (deriv f x₀ - deriv g x₀) x₀ := by
          exact HasDerivAt.sub ( hf.hasDerivAt ) ( hg.hasDerivAt );
        rw [ hasDerivAt_iff_tendsto_slope ] at h_lim;
        refine' Filter.Tendsto.congr' _ ( h_lim.mono_left <| nhdsWithin_mono _ <| by simp +decide );
        filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ slope_def_field ] ; aesop;
      have := h_lim.eventually ( lt_mem_nhds ( sub_pos.mpr hderiv ) ) ; have := this.and self_mem_nhdsWithin; obtain ⟨ x, hx₁, hx₂ ⟩ := this.exists; exact ⟨ x, hx₂, by rw [ div_eq_mul_inv ] at hx₁; nlinarith [ mul_inv_cancel₀ ( sub_ne_zero_of_ne hx₂.ne ) ] ⟩ ;

/-
The derivative of the bound function at z=1.
-/
noncomputable def bound_func (p : ℕ) (alpha : ℝ) (z : ℝ) : ℝ :=
  lambda_plus p z * z ^ (-alpha)

theorem deriv_bound_func_at_one (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) :
    deriv (bound_func p alpha) 1 = p * (1 / 2 - alpha) := by
      unfold bound_func; norm_num [ mul_comm, mul_assoc, mul_left_comm, hp ] ; ring_nf;
      -- Apply the product rule to find the derivative.
      have h_deriv : deriv (fun z => lambda_plus p z * z ^ (-alpha : ℝ)) 1 = deriv (lambda_plus p) 1 * 1 ^ (-alpha : ℝ) + lambda_plus p 1 * deriv (fun z => z ^ (-alpha : ℝ)) 1 := by
        apply_rules [ deriv_mul ];
        · apply_rules [ DifferentiableAt.div, DifferentiableAt.add, DifferentiableAt.sqrt, DifferentiableAt.mul, DifferentiableAt.rpow ] <;> norm_num;
          · exact differentiableAt_const _;
          · norm_num [ mul_assoc ];
          · rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num <;> ring_nf <;> norm_num;
            · linarith;
            · linarith;
        · exact DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) ( by norm_num );
      norm_num [ h_deriv, deriv_const_mul, deriv_pow ];
      rw [ deriv_lambda_plus_at_one ] ; rw [ lambda_plus_at_one ] ; ring;
      · linarith;
      · linarith

/-
For alpha < 1/2, the bound function takes a value less than p for some z < 1.
-/
theorem exists_z_lt_one_bound_lt_p (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) (halpha : alpha < 1 / 2) :
    ∃ z ∈ Set.Ioo 0 1, bound_func p alpha z < p := by
      have h_deriv : deriv (bound_func p alpha) 1 > 0 := by
        have := deriv_bound_func_at_one p alpha hp; norm_num at *; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ p ) ] ;
      have h_ineq : ∃ z ∈ Set.Ioo 0 1, bound_func p alpha z < p := by
        have h_cont : ContinuousAt (bound_func p alpha) 1 := by
          exact differentiableAt_of_deriv_ne_zero ( ne_of_gt h_deriv ) |> DifferentiableAt.continuousAt
        have h_lim : Filter.Tendsto (fun z => (bound_func p alpha z - p) / (z - 1)) (nhdsWithin 1 (Set.Iio 1)) (nhds (deriv (bound_func p alpha) 1)) := by
          have h_lim : HasDerivAt (bound_func p alpha) (deriv (bound_func p alpha) 1) 1 := by
            exact hasDerivAt_deriv_iff.mpr ( show DifferentiableAt ℝ ( bound_func p alpha ) 1 from differentiableAt_of_deriv_ne_zero ( by linarith ) );
          rw [ hasDerivAt_iff_tendsto_slope ] at h_lim;
          convert h_lim.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num [ slope_def_field ];
          unfold bound_func; norm_num [ lambda_plus_at_one p hp ] ;
        have := h_lim.eventually ( lt_mem_nhds h_deriv );
        have := this.and ( Ioo_mem_nhdsLT zero_lt_one ) ; obtain ⟨ z, hz₁, hz₂ ⟩ := this.exists; exact ⟨ z, hz₂, by rw [ lt_div_iff_of_neg ] at hz₁ <;> linarith ⟩ ;
      exact h_ineq

/-
The weighted sum is bounded by a constant times the D-th power of the largest eigenvalue.
-/
theorem weighted_sum_upper_bound (p D : ℕ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ weighted_sum p D z ≤ C * (lambda_plus p z) ^ D := by
      refine' ⟨ ( weighted_sum p D z ) / ( lambda_plus p z ) ^ D + 1, _, _ ⟩ <;> norm_num at *;
      · exact add_pos_of_nonneg_of_pos ( div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( pow_nonneg ( by exact div_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg zero_le_one ( by positivity ) ) ) ( Real.sqrt_nonneg _ ) ) zero_le_two ) _ ) ) zero_lt_one;
      · rw [ add_mul, div_mul_cancel₀ ] <;> norm_num [ show lambda_plus p z ≠ 0 from ne_of_gt ( div_pos ( add_pos_of_pos_of_nonneg ( mul_pos ( Nat.cast_pos.mpr ( Nat.div_pos ( by linarith ) zero_lt_two ) ) ( by positivity ) ) ( Real.sqrt_nonneg _ ) ) zero_lt_two ) ];
        exact pow_nonneg ( div_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg zero_le_one hz.le ) ) ( Real.sqrt_nonneg _ ) ) zero_le_two ) _

/-
Choice of z for the bound.
-/
noncomputable def z_choice (p : ℕ) (alpha : ℝ) : ℝ :=
  if h : p ≥ 2 ∧ alpha < 1 / 2 then
    Classical.choose (exists_z_lt_one_bound_lt_p p alpha h.1 h.2)
  else 1/2

theorem z_choice_prop (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) (halpha : alpha < 1 / 2) :
    z_choice p alpha ∈ Set.Ioo 0 1 ∧ bound_func p alpha (z_choice p alpha) < p := by
      unfold z_choice;
      split_ifs <;> simp_all +decide [ Classical.choose_spec ( exists_z_lt_one_bound_lt_p p alpha hp halpha ) ]

/-
The base of the exponential bound is strictly less than p.
-/
noncomputable def rho (p : ℕ) (alpha : ℝ) : ℝ :=
  bound_func p alpha (z_choice p alpha)

theorem rho_lt_p (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) (halpha : alpha < 1 / 2) :
    rho p alpha < p := by
      have := z_choice_prop p alpha hp halpha;
      convert this.2 using 1

/-
The exponent gamma is strictly less than 1.
-/
noncomputable def gamma (p : ℕ) (alpha : ℝ) : ℝ :=
  Real.log (rho p alpha) / Real.log p

theorem gamma_lt_one (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) (halpha : alpha < 1 / 2) :
    gamma p alpha < 1 := by
      -- Since $\rho < p$, we have $\log \rho < \log p$.
      have h_log_rho_lt_log_p : Real.log (rho p alpha) < Real.log p := by
        have h_log_rho_lt_log_p : rho p alpha < p := by
          -- By definition of rho, we have rho p alpha = bound_func p alpha (z_choice p alpha).
          apply rho_lt_p p alpha hp halpha;
        gcongr;
        -- Since $z_choice p alpha$ is positive and $\lambda_plus p (z_choice p alpha)$ is positive, their product is positive.
        have h_lambda_pos : 0 < lambda_plus p (z_choice p alpha) := by
          refine' lt_of_lt_of_le _ ( lam_ge_H p ( z_choice p alpha ) hp _ );
          · exact Nat.cast_pos.mpr ( Nat.div_pos ( by linarith ) zero_lt_two );
          · exact le_of_lt ( z_choice_prop p alpha hp halpha |>.1.1 );
        exact mul_pos h_lambda_pos ( Real.rpow_pos_of_pos ( show 0 < z_choice p alpha from by have := z_choice_prop p alpha hp halpha; exact this.1.1 ) _ );
      unfold gamma; rw [ div_lt_one ( Real.log_pos ( by norm_cast ) ) ] ; exact h_log_rho_lt_log_p;

/-
alpha_val is less than 1/2.
-/
noncomputable def alpha_val : ℝ := 0.49

theorem alpha_val_lt_half : alpha_val < 1 / 2 := by
  exact show ( 0.49 : ℝ ) < 1 / 2 by norm_num;

/-
The exponent gamma is less than 1 for alpha = 0.49.
-/
noncomputable def gamma_exponent (p : ℕ) : ℝ := gamma p alpha_val

theorem gamma_exponent_lt_one (p : ℕ) (hp : p ≥ 2) : gamma_exponent p < 1 := by
  convert gamma_lt_one p 0.49 hp _ using 1;
  norm_num

/-
The cardinality of the bad set for a prime p is bounded by the Chernoff bound.
-/
noncomputable def bound_bad_set_p_val (x : ℝ) (p : ℕ) [Fact p.Prime] : ℝ :=
  let z := z_choice p alpha_val
  let D := D_func p x
  let K := alpha_val * Real.log x / Real.log p
  weighted_sum p D z * z ^ (-K)

theorem bad_set_p_card_bound (x : ℝ) (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) :
    ((bad_set_p x p).card : ℝ) ≤ bound_bad_set_p_val x p := by
      -- By the Chernoff bound, the cardinality of the bad set is bounded by the weighted sum times the exponential term.
      have h_chernoff : ((Finset.range (p ^ (Nat.floor (Real.log x / Real.log p) + 1))).filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) < 0.49 * (Real.log x / Real.log p))).card ≤ weighted_sum p (Nat.floor (Real.log x / Real.log p) + 1) (z_choice p alpha_val) * z_choice p alpha_val ^ (-0.49 * (Real.log x / Real.log p)) := by
        have := @weighted_sum_bound_general p ( Nat.floor ( Real.log x / Real.log p ) + 1 ) ( 0.49 * ( Real.log x / Real.log p ) ) ( z_choice p 0.49 );
        convert le_trans _ ( this hp _ _ ) using 1;
        · norm_num [ alpha_val ];
        · exact_mod_cast Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, le_of_lt <| Finset.mem_filter.mp hx |>.2 ⟩;
        · exact z_choice_prop p 0.49 hp ( by norm_num ) |>.1 |>.1;
        · exact le_of_lt ( z_choice_prop p 0.49 hp ( by norm_num ) |>.1 |>.2 );
      -- Since `bad_set_p` is a subset of `{m < p^D | v_p <= K}`, we can apply the Chernoff bound.
      have h_subset : bad_set_p x p ⊆ Finset.filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) < 0.49 * (Real.log x / Real.log p)) (Finset.range (p ^ (Nat.floor (Real.log x / Real.log p) + 1))) := by
        intro m hm; simp_all +decide [ bad_set_p ] ; (
        refine' ⟨ _, _ ⟩;
        · have h_log : Real.log m < (Nat.floor (Real.log x / Real.log p) + 1) * Real.log p := by
            have := Nat.lt_floor_add_one ( Real.log x / Real.log p );
            rw [ div_lt_iff₀ ( Real.log_pos ( Nat.one_lt_cast.mpr hp ) ) ] at this;
            exact lt_of_le_of_lt ( Real.log_le_log ( by norm_cast; linarith ) ( Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hm.1.2 ) ) ) this;
          rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; rw [ ← Real.log_lt_log_iff ( by norm_cast; linarith ) ( by positivity ) ] ; simpa using h_log;
        · field_simp;
          refine' lt_of_lt_of_le hm.2.2 _;
          gcongr ; norm_cast ; linarith [ Nat.floor_le ( show 0 ≤ x by positivity ) ];
          exact le_trans ( Nat.cast_le.mpr hm.1.2 ) ( Nat.floor_le ( by positivity ) ));
      refine le_trans ( Nat.cast_le.mpr <| Finset.card_mono h_subset ) ?_;
      convert h_chernoff using 1;
      unfold bound_bad_set_p_val; norm_num [ Real.rpow_def_of_pos ] ;
      unfold D_func; ring_nf;
      unfold alpha_val; ring_nf;

/-
The cardinality of the bad set for a prime p is bounded by the Chernoff bound.
-/
noncomputable def bound_bad_set_p_val_v2 (x : ℝ) (p : ℕ) [Fact p.Prime] : ℝ :=
  let z := z_choice p alpha_val
  let D := D_func p x
  let K := alpha_val * Real.log x / Real.log p
  weighted_sum p D z * z ^ (-K)

theorem bad_set_p_card_bound_v2 (x : ℝ) (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) :
    ((bad_set_p x p).card : ℝ) ≤ bound_bad_set_p_val_v2 x p := by
      convert bad_set_p_card_bound x p hp hx using 1

/-
The smaller eigenvalue is non-negative.
-/
theorem lambda_minus_nonneg (p : ℕ) (z : ℝ) (hp : p ≥ 2) (hz : z ≥ 0) :
    lambda_minus p z ≥ 0 := by
      refine' div_nonneg _ zero_le_two;
      rw [ sub_nonneg, Real.sqrt_le_left ] <;> norm_num;
      · exact mul_nonneg ( mul_nonneg zero_le_four hz ) ( sub_nonneg_of_le ( by gcongr ; omega ) );
      · positivity

/-
The cardinality of the bad set for a prime p is bounded by the Chernoff bound.
-/
noncomputable def bound_bad_set_p_val_v3 (x : ℝ) (p : ℕ) [Fact p.Prime] : ℝ :=
  let z := z_choice p alpha_val
  let D := D_func p x
  let K := alpha_val * Real.log x / Real.log p
  weighted_sum p D z * z ^ (-K)

theorem bad_set_p_card_bound_v3 (x : ℝ) (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) :
    ((bad_set_p x p).card : ℝ) ≤ bound_bad_set_p_val_v3 x p := by
      convert bad_set_p_card_bound_v2 x p hp hx

/-
The weighted sum is bounded by a constant times the D-th power of the largest eigenvalue, uniformly in D.
-/
theorem weighted_sum_uniform_bound (p : ℕ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, weighted_sum p D z ≤ C * (lambda_plus p z) ^ D := by
      use ( |(c_plus p z * (u_plus p z 0 + u_plus p z 1))| + |(c_minus p z * (u_minus p z 0 + u_minus p z 1))| ) + 1
      generalize_proofs at *; (
      have h_closed_form : ∀ D : ℕ, weighted_sum p D z = (c_plus p z * (u_plus p z 0 + u_plus p z 1)) * (lambda_plus p z) ^ D + (c_minus p z * (u_minus p z 0 + u_minus p z 1)) * (lambda_minus p z) ^ D := by
        intro D
        have h_closed_form : weighted_vector p D z = (c_plus p z * (lambda_plus p z) ^ D) • u_plus p z + (c_minus p z * (lambda_minus p z) ^ D) • u_minus p z := by
          apply weighted_vector_closed_form_v2 p D z hp hz.le
        generalize_proofs at *; (
        rw [ weighted_sum_eq_sum_components, h_closed_form ] ; norm_num ; ring;);
      -- We know that $0 \leq \lambda_m \leq \lambda_p$.
      have h_lambda_bounds : 0 ≤ lambda_minus p z ∧ lambda_minus p z ≤ lambda_plus p z := by
        apply And.intro;
        · apply lambda_minus_nonneg p z hp hz.le;
        · unfold lambda_minus lambda_plus; ring_nf; norm_num;
      refine' ⟨ by positivity, fun D => _ ⟩;
      -- Using the bounds on the eigenvalues, we can bound the terms involving lambda_minus p z.
      have h_lambda_minus_bound : |c_minus p z * (u_minus p z 0 + u_minus p z 1) * (lambda_minus p z) ^ D| ≤ |c_minus p z * (u_minus p z 0 + u_minus p z 1)| * (lambda_plus p z) ^ D := by
        rw [ abs_mul, abs_pow, abs_of_nonneg h_lambda_bounds.1 ] ; gcongr ; aesop ( simp_config := { decide := true } ) ;
        linarith;
      cases abs_cases ( c_plus p z * ( u_plus p z 0 + u_plus p z 1 ) ) <;> cases abs_cases ( c_minus p z * ( u_minus p z 0 + u_minus p z 1 ) ) <;> nlinarith [ abs_le.mp h_lambda_minus_bound, h_closed_form D, pow_nonneg ( show 0 ≤ lambda_plus p z by linarith ) D ] ;)

/-
The constant C_p bounds the weighted sum uniformly in D.
-/
noncomputable def C_p (p : ℕ) (z : ℝ) [Fact p.Prime] : ℝ :=
  if h : p ≥ 2 ∧ 0 < z ∧ z ≤ 1 then
    Classical.choose (weighted_sum_uniform_bound p z h.1 h.2.1 h.2.2)
  else 1

theorem C_p_prop (p : ℕ) (z : ℝ) (D : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    weighted_sum p D z ≤ C_p p z * (lambda_plus p z) ^ D := by
      rw [ C_p ];
      split_ifs <;> simp_all +decide [ Classical.choose_spec ( weighted_sum_uniform_bound p z hp hz hz1 ) ]

/-
The constant C_p bounds the weighted sum uniformly in D.
-/
noncomputable def C_p_v2 (p : ℕ) (z : ℝ) [hprime : Fact p.Prime] : ℝ :=
  if h : p ≥ 2 ∧ 0 < z ∧ z ≤ 1 then
    Classical.choose (@weighted_sum_uniform_bound p z hprime h.1 h.2.1 h.2.2)
  else 1

theorem C_p_prop_v2 (p : ℕ) (z : ℝ) (D : ℕ) [hprime : Fact p.Prime] (hp : p ≥ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    weighted_sum p D z ≤ C_p_v2 p z * (lambda_plus p z) ^ D := by
      convert C_p_prop p z D hp hz hz1 using 1

/-
Asymptotic bound for the bad set size.
-/
theorem bad_set_p_bound_asymptotic (x : ℝ) (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) :
    bound_bad_set_p_val_v3 x p ≤ C_p_v2 p (z_choice p alpha_val) * (lambda_plus p (z_choice p alpha_val)) * x ^ (gamma_exponent p) := by
      -- Substitute the bound from C_p_prop_v2 into the expression for bound_bad_set_p_val_v3.
      have h_subst : bound_bad_set_p_val_v3 x p ≤ C_p_v2 p (z_choice p alpha_val) * (lambda_plus p (z_choice p alpha_val)) ^ (Nat.floor ((Real.log x) / (Real.log p)) + 1) * (z_choice p alpha_val) ^ (- (alpha_val * Real.log x / Real.log p)) := by
        have := @C_p_prop_v2 p ( z_choice p alpha_val );
        convert mul_le_mul_of_nonneg_right ( this ( ⌊Real.log x / Real.log p⌋₊ + 1 ) hp ( z_choice_prop p alpha_val hp ( alpha_val_lt_half ) |>.1 |>.1 ) ( z_choice_prop p alpha_val hp ( alpha_val_lt_half ) |>.1 |>.2.le ) ) ( Real.rpow_nonneg ( z_choice_prop p alpha_val hp ( alpha_val_lt_half ) |>.1 |>.1.le ) _ ) using 1;
        unfold bound_bad_set_p_val_v3; norm_num [ D_func ] ;
        exact Or.inl ( by rw [ add_comm ] );
      -- Using the properties of exponents, we can simplify the right-hand side of the inequality.
      have h_exp : (lambda_plus p (z_choice p alpha_val)) ^ (Nat.floor ((Real.log x) / (Real.log p)) + 1) * (z_choice p alpha_val) ^ (- (alpha_val * Real.log x / Real.log p)) ≤ (lambda_plus p (z_choice p alpha_val)) * (lambda_plus p (z_choice p alpha_val) * (z_choice p alpha_val) ^ (-alpha_val)) ^ ((Real.log x) / Real.log p) := by
        have h_exp : (lambda_plus p (z_choice p alpha_val)) ^ (Nat.floor ((Real.log x) / (Real.log p)) + 1) * (z_choice p alpha_val) ^ (- (alpha_val * Real.log x / Real.log p)) ≤ (lambda_plus p (z_choice p alpha_val)) * (lambda_plus p (z_choice p alpha_val)) ^ ((Real.log x) / (Real.log p)) * (z_choice p alpha_val) ^ (- (alpha_val * Real.log x / Real.log p)) := by
          gcongr;
          · refine' Real.rpow_nonneg _ _;
            unfold z_choice;
            split_ifs <;> norm_num;
            exact Classical.choose_spec ( exists_z_lt_one_bound_lt_p p alpha_val hp ( by tauto ) ) |>.1 |>.1.le;
          · rw [ pow_succ' ];
            -- Since $\lambda_+ \geq 1$, we have $\lambda_+^{\lfloor \log x / \log p \rfloor} \leq \lambda_+^{\log x / \log p}$.
            have h_exp : 1 ≤ lambda_plus p (z_choice p alpha_val) := by
              apply le_trans _ ( lam_ge_H p ( z_choice p alpha_val ) hp ( show 0 ≤ z_choice p alpha_val from _ ) );
              · exact_mod_cast Nat.div_pos ( by linarith ) zero_lt_two;
              · unfold z_choice;
                split_ifs <;> norm_num;
                exact Classical.choose_spec ( exists_z_lt_one_bound_lt_p p alpha_val hp ( by tauto ) ) |>.1 |>.1.le;
            exact mul_le_mul_of_nonneg_left ( by exact_mod_cast Real.rpow_le_rpow_of_exponent_le h_exp ( Nat.floor_le ( div_nonneg ( Real.log_nonneg hx ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ) ) ( by positivity );
        convert h_exp using 1 ; rw [ Real.mul_rpow ( _ ) ( _ ) ] ; ring_nf;
        · rw [ ← Real.rpow_mul ( _ ) ] ; ring_nf;
          exact le_of_lt ( z_choice_prop p alpha_val hp ( show alpha_val < 1 / 2 by exact alpha_val_lt_half ) |>.1 |>.1 );
        · exact div_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg zero_le_one ( show 0 ≤ z_choice p alpha_val from by exact le_of_lt ( z_choice_prop p alpha_val hp ( show alpha_val < 1 / 2 from by norm_num [ alpha_val ] ) |>.1 |>.1 ) ) ) ) ( Real.sqrt_nonneg _ ) ) zero_le_two;
        · exact Real.rpow_nonneg ( le_of_lt ( z_choice_prop p alpha_val hp ( by linarith [ show alpha_val < 1 / 2 by exact show ( 0.49 : ℝ ) < 1 / 2 by norm_num ] ) |>.1 |>.1 ) ) _;
      -- Using the properties of exponents, we can simplify the right-hand side of the inequality further.
      have h_exp_simplified : (lambda_plus p (z_choice p alpha_val) * (z_choice p alpha_val) ^ (-alpha_val)) ^ ((Real.log x) / Real.log p) ≤ x ^ (gamma_exponent p) := by
        rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos ];
        · rw [ Real.rpow_def_of_pos ( by positivity ) ];
          unfold gamma_exponent;
          unfold gamma;
          unfold rho; ring_nf; norm_num;
          unfold bound_func; ring_nf;
          rw [ Real.rpow_def_of_pos ( show 0 < z_choice p alpha_val from _ ) ] ; ring_nf ; norm_num;
          exact z_choice_prop p alpha_val hp ( alpha_val_lt_half ) |>.1.1;
        · exact z_choice_prop p alpha_val hp ( alpha_val_lt_half ) |>.1.1;
        · refine' mul_pos _ _;
          · refine' div_pos _ _ <;> norm_num;
            exact add_pos_of_pos_of_nonneg ( mul_pos ( Nat.cast_pos.mpr ( Nat.div_pos ( by linarith ) zero_lt_two ) ) ( by linarith [ show 0 < z_choice p alpha_val from by have := z_choice_prop p alpha_val hp ( by exact alpha_val_lt_half ) ; exact this.1.1 ] ) ) ( Real.sqrt_nonneg _ );
          · exact Real.rpow_pos_of_pos ( z_choice_prop p alpha_val hp ( by norm_num [ alpha_val ] ) |>.1 |>.1 ) _;
      refine le_trans h_subst ?_;
      convert mul_le_mul_of_nonneg_left ( h_exp.trans ( mul_le_mul_of_nonneg_left h_exp_simplified <| _ ) ) ( show 0 ≤ C_p_v2 p ( z_choice p alpha_val ) by
                                                                                                                unfold C_p_v2;
                                                                                                                split_ifs <;> norm_num;
                                                                                                                exact le_of_lt ( Classical.choose_spec ( weighted_sum_uniform_bound p ( z_choice p alpha_val ) hp ( by linarith ) ( by linarith ) ) |>.1 ) ) using 1 ; ring;
      · ring;
      · apply_rules [ add_nonneg, div_nonneg, Real.sqrt_nonneg, pow_nonneg ] <;> norm_num [ hp ];
        exact mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg zero_le_one ( le_of_lt ( z_choice_prop p alpha_val ( show p ≥ 2 by linarith ) ( show alpha_val < 1 / 2 by exact alpha_val_lt_half ) |>.1.1 ) ) )

/-
The total bound for the bad set size, summing over all relevant primes.
-/
noncomputable def total_bad_set_bound (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1)),
    if h : p.Prime then
      haveI : Fact p.Prime := ⟨h⟩
      C_p_v2 p (z_choice p alpha_val) * (lambda_plus p (z_choice p alpha_val)) * x ^ (gamma_exponent p)
    else 0

/-
z_zero is in (0, 1) for alpha in (0, 1/2).
-/
noncomputable def z_zero (alpha : ℝ) : ℝ := alpha / (1 - alpha)

theorem z_zero_mem_Ioo (alpha : ℝ) (h1 : 0 < alpha) (h2 : alpha < 1/2) :
    z_zero alpha ∈ Set.Ioo 0 1 := by
      exact ⟨ by unfold z_zero; rw [ lt_div_iff₀ ] <;> linarith, by unfold z_zero; rw [ div_lt_iff₀ ] <;> linarith ⟩

/-
Upper bound for the largest eigenvalue.
-/
theorem lambda_plus_le_bound (p : ℕ) (z : ℝ) (hp : p ≥ 2) (hz : z ≥ 0) :
    lambda_plus p z ≤ ((p + 1) / 2 : ℝ) * (1 + z) := by
      unfold lambda_plus;
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
      · norm_num [ Nat.add_div ];
        rw [ Real.sqrt_sq ] <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ];
      · rw [ div_le_iff₀ ] <;> norm_num [ Nat.add_div ];
        -- Simplify the expression under the square root.
        have h_sqrt : Real.sqrt ((k + 1) ^ 2 * (1 + z) ^ 2 - 4 * z * (k + 1) ^ 2 + 4 * z * k ^ 2) ≤ (k + 1) * (1 + z) := by
          rw [ Real.sqrt_le_left ] <;> nlinarith [ sq ( k : ℝ ), mul_nonneg hz ( sq_nonneg ( k : ℝ ) ) ];
        ring_nf at * ; linarith

/-
The asymptotic ratio is less than 1.
-/
noncomputable def limit_ratio (alpha : ℝ) : ℝ :=
  let z := z_zero alpha
  (1 + z) / 2 * z ^ (-alpha)

theorem limit_ratio_lt_one (alpha : ℝ) (h1 : 0 < alpha) (h2 : alpha < 1/2) :
    limit_ratio alpha < 1 := by
      unfold limit_ratio;
      -- Since $f(\alpha)$ is minimized at $\alpha = 1/2$ and $f(1/2) = 1/2$, we have $f(\alpha) > 1/2$ for $0 < \alpha < 1/2$.
      have h_min : ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 / 2 → alpha ^ alpha * (1 - alpha) ^ (1 - alpha) > 1 / 2 := by
        -- Let's choose any $\alpha$ in the interval $(0, 1/2)$ and show that $f(\alpha) > 1/2$.
        intros alpha h1 h2
        have h_min : alpha * Real.log alpha + (1 - alpha) * Real.log (1 - alpha) > Real.log (1 / 2) := by
          have h_convex : StrictConvexOn ℝ (Set.Ioi 0) (fun x => x * Real.log x) := by
            exact ( Real.strictConvexOn_mul_log.subset Set.Ioi_subset_Ici_self <| convex_Ioi _ );
          have := h_convex.2 ( show 0 < alpha by linarith ) ( show 0 < 1 - alpha by linarith ) ( by linarith );
          have := @this ( 1 / 2 ) ( 1 / 2 ) ( by norm_num ) ( by norm_num ) ( by norm_num ) ; norm_num at * ; ring_nf at * ; linarith;
        rw [ gt_iff_lt, ← Real.log_lt_log_iff ( by positivity ) ( by exact mul_pos ( Real.rpow_pos_of_pos h1 _ ) ( Real.rpow_pos_of_pos ( by linarith ) _ ) ), Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( by linarith ) _ ) ), Real.log_rpow h1, Real.log_rpow ( by linarith ) ] ; linarith;
      convert inv_lt_one_of_one_lt₀ ( show 1 < 2 * ( alpha ^ alpha * ( 1 - alpha ) ^ ( 1 - alpha ) ) from by linarith [ h_min h1 h2 ] ) using 1 ; norm_num [ z_zero ] ; ring_nf;
      rw [ Real.mul_rpow ( by linarith ) ( by nlinarith [ mul_inv_cancel₀ ( by linarith : ( 1 - alpha ) ≠ 0 ) ] ), Real.inv_rpow ( by linarith ) ] ; ring_nf;
      rw [ show ( 1 - alpha ) ^ ( 1 - alpha ) = ( 1 - alpha ) ^ ( -alpha ) * ( 1 - alpha ) by rw [ ← Real.rpow_add_one ( by linarith ) ] ; ring_nf ] ; norm_num [ Real.rpow_neg ( by linarith : 0 ≤ alpha ), Real.rpow_neg ( by linarith : 0 ≤ 1 - alpha ) ] ; ring_nf;
      nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( 1 - alpha ) ≠ 0 ) ( ( alpha ^ alpha ) ⁻¹ * ( 1 - alpha ) ^ alpha * ( 1 / 2 ) ) ]

/-
z_final is in (0, 1) and provides a bound less than p.
-/
noncomputable def z_final (p : ℕ) (alpha : ℝ) : ℝ :=
  if h : p ≥ 2 ∧ alpha < 1 / 2 then
    if bound_func p alpha (z_zero alpha) < p ∧ z_zero alpha < 1 then
      z_zero alpha
    else
      z_choice p alpha
  else 1/2

theorem z_final_prop (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) (halpha : alpha < 1 / 2) (halpha_pos : 0 < alpha) :
    z_final p alpha ∈ Set.Ioo 0 1 ∧ bound_func p alpha (z_final p alpha) < p := by
      unfold z_final;
      field_simp;
      split_ifs <;> norm_num;
      · exact ⟨ ⟨ div_pos halpha_pos ( by linarith ), by linarith ⟩, by linarith ⟩;
      · exact ⟨ ⟨ z_choice_prop p alpha hp halpha |>.1 |>.1, z_choice_prop p alpha hp halpha |>.1 |>.2 ⟩, z_choice_prop p alpha hp halpha |>.2 ⟩;
      · exact False.elim <| ‹¬ ( p ≥ 2 ∧ alpha * 2 < 1 ) › ⟨ hp, by linarith ⟩

/-
The cardinality of the bad set for a prime p is bounded by the Chernoff bound using z_final.
-/
noncomputable def bound_bad_set_p_val_v4 (x : ℝ) (p : ℕ) [Fact p.Prime] : ℝ :=
  let z := z_final p alpha_val
  let D := D_func p x
  let K := alpha_val * Real.log x / Real.log p
  weighted_sum p D z * z ^ (-K)

theorem bad_set_p_card_bound_v4 (x : ℝ) (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) :
    ((bad_set_p x p).card : ℝ) ≤ bound_bad_set_p_val_v4 x p := by
      -- Apply the Chernoff bound with $z = z_final p alpha_val$.
      have h_bound : ∀ z ∈ Set.Ioo 0 1, ((bad_set_p x p).card : ℝ) ≤ weighted_sum p (D_func p x) z * z ^ (-alpha_val * Real.log x / Real.log p) := by
        -- Apply the Chernoff bound with $z = z_final p alpha_val$ and use the fact that the set bad_set_p x p is a subset of {m < p^D | v_p(m) ≤ K}.
        intros z hz
        have h_subset : (bad_set_p x p).card ≤ ((Finset.filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ alpha_val * Real.log x / Real.log p) (Finset.range (p ^ (D_func p x)))).card : ℝ) := by
          refine' mod_cast Finset.card_le_card _;
          intro m hm;
          refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
          · refine' Finset.mem_range.mpr _;
            refine' lt_of_le_of_lt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.2 ) _;
            refine' Nat.floor_lt ( by positivity ) |>.2 _;
            unfold D_func;
            have := Nat.lt_floor_add_one ( Real.log x / Real.log p );
            rw [ div_lt_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hp ) ] at this ; rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ) ] ; norm_num ; linarith [ Real.log_pow ( p : ℝ ) ( 1 + ⌊Real.log x / Real.log p⌋₊ ) ];
          · have := Finset.mem_filter.mp hm |>.2;
            refine' le_trans this.2.le _;
            exact div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at this ) <| show ( m : ℝ ) ≤ x from by exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity ) <| by norm_num ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.Prime.pos Fact.out;
        refine le_trans h_subset ?_;
        have := weighted_sum_bound_general p ( D_func p x ) ( alpha_val * Real.log x / Real.log p ) z ( by linarith [ hz.1, hz.2 ] ) ( by linarith [ hz.1, hz.2 ] );
        simpa only [ neg_div, neg_mul ] using this hz.2.le;
      unfold bound_bad_set_p_val_v4;
      convert h_bound ( z_final p alpha_val ) ( z_final_prop p alpha_val hp ( by norm_num [ alpha_val ] ) ( by norm_num [ alpha_val ] ) |>.1 ) using 1 ; ring_nf

/-
Bound for bound_func at z_zero.
-/
theorem bound_func_z_zero_bound (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) (h1 : 0 < alpha) (h2 : alpha < 1/2) :
    bound_func p alpha (z_zero alpha) ≤ (1 + 1 / (p : ℝ)) * limit_ratio alpha * p := by
      unfold bound_func limit_ratio;
      have := lambda_plus_le_bound p ( z_zero alpha ) hp ( show 0 ≤ z_zero alpha from div_nonneg h1.le ( by linarith ) );
      refine le_trans ( mul_le_mul_of_nonneg_right this ( Real.rpow_nonneg ( show 0 ≤ z_zero alpha from div_nonneg h1.le ( by linarith ) ) _ ) ) ?_;
      field_simp;
      norm_cast

/-
A sequence strictly less than 1 converging to a limit less than 1 is uniformly bounded by a constant less than 1.
-/
theorem bounded_of_convergent_lt_one (f : ℕ → ℝ) (L : ℝ) (h_conv : Filter.Tendsto f Filter.atTop (nhds L)) (h_lt : ∀ n ≥ 2, f n < 1) (h_lim : L < 1) :
    ∃ c < 1, ∀ n ≥ 2, f n ≤ c := by
      -- Since $f(n) \to L$, there exists $N$ such that for $n \ge N$, $f(n) < L + \epsilon = (1+L)/2 < 1$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, f n < (1 + L) / 2 := by
        simpa using h_conv.eventually ( gt_mem_nhds <| by linarith );
      -- Let $S = \{n \mid 2 \le n < N\}$. This set is finite.
      set S := Finset.Ico 2 N with hS_def;
      -- Let $M = \max_{n \in S} f(n)$. If $S$ is empty, take $M = 0$.
      obtain ⟨M, hM⟩ : ∃ M, (∀ n ∈ S, f n ≤ M) ∧ (M < 1) := by
        by_cases hS_empty : S.Nonempty;
        · exact ⟨ Finset.max' ( S.image f ) ⟨ _, Finset.mem_image_of_mem f hS_empty.choose_spec ⟩, fun n hn => Finset.le_max' _ _ ( Finset.mem_image_of_mem f hn ), by have := Finset.max'_mem ( S.image f ) ⟨ _, Finset.mem_image_of_mem f hS_empty.choose_spec ⟩ ; aesop ⟩;
        · exact ⟨ 0, by aesop, by norm_num ⟩;
      exact ⟨ Max.max M ( ( 1 + L ) / 2 ), max_lt hM.2 ( by linarith ), fun n hn => if h : n < N then le_trans ( hM.1 n ( Finset.mem_Ico.mpr ⟨ hn, h ⟩ ) ) ( le_max_left _ _ ) else le_trans ( le_of_lt ( hN n ( le_of_not_gt h ) ) ) ( le_max_right _ _ ) ⟩

/-
The upper bound for the ratio converges to the limit ratio.
-/
theorem upper_bound_converges (alpha : ℝ) (h1 : 0 < alpha) (h2 : alpha < 1/2) :
    Filter.Tendsto (fun p : ℕ => (1 + 1 / (p : ℝ)) * limit_ratio alpha) Filter.atTop (nhds (limit_ratio alpha)) := by
      exact le_trans ( Filter.Tendsto.mul ( tendsto_const_nhds.add <| tendsto_one_div_atTop_nhds_zero_nat ) tendsto_const_nhds ) ( by norm_num )

/-
Eventually, the bound function at z_zero is less than p.
-/
theorem eventually_bound_func_lt_p (alpha : ℝ) (h1 : 0 < alpha) (h2 : alpha < 1/2) :
    ∀ᶠ p in Filter.atTop, bound_func p alpha (z_zero alpha) < p := by
      -- The upper bound for the ratio converges to the limit ratio.
      have upper_bound_converges : Filter.Tendsto (fun p : ℕ => (1 + 1 / (p : ℝ)) * limit_ratio alpha) Filter.atTop (nhds (limit_ratio alpha)) := by
        convert Filter.Tendsto.mul ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) tendsto_const_nhds using 2 ; ring;
      -- Since the limit ratio is less than 1, there exists some $N$ such that for all $p \geq N$, $(1 + 1 / (p : ℝ)) * limit_ratio alpha < 1$.
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ≥ N, (1 + 1 / (p : ℝ)) * limit_ratio alpha < 1 := by
        simpa using upper_bound_converges.eventually ( gt_mem_nhds <| limit_ratio_lt_one alpha h1 h2 );
      filter_upwards [ Filter.eventually_ge_atTop N, Filter.eventually_ge_atTop 2 ] with p hp hp';
      have := bound_func_z_zero_bound p alpha hp' h1 h2; specialize hN p hp; norm_num at *; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ p ), one_div_mul_cancel ( by positivity : ( p : ℝ ) ≠ 0 ) ] ;

/-
rho_v2 is bounded by c * p for some c < 1.
-/
noncomputable def rho_v2 (p : ℕ) (alpha : ℝ) : ℝ :=
  bound_func p alpha (z_final p alpha)

theorem rho_v2_le_c_mul_p (p : ℕ) (hp : p ≥ 2) :
    ∃ c < 1, ∀ p ≥ 2, rho_v2 p alpha_val ≤ c * p := by
      have h_bound : ∀ᶠ p in Filter.atTop, bound_func p alpha_val (z_final p alpha_val) ≤ (limit_ratio alpha_val + (1 - limit_ratio alpha_val) / 2) * p := by
        have h_bound : ∀ᶠ p in Filter.atTop, bound_func p alpha_val (z_zero alpha_val) ≤ (limit_ratio alpha_val + (1 - limit_ratio alpha_val) / 2) * p := by
          have h_bound : ∀ᶠ p in Filter.atTop, bound_func p alpha_val (z_zero alpha_val) ≤ (1 + 1 / (p : ℝ)) * limit_ratio alpha_val * p := by
            have h_bound : ∀ p ≥ 2, bound_func p alpha_val (z_zero alpha_val) ≤ (1 + 1 / (p : ℝ)) * limit_ratio alpha_val * p := by
              intros p hp
              apply bound_func_z_zero_bound p alpha_val hp (by norm_num [alpha_val]) (by norm_num [alpha_val]);
            exact Filter.eventually_atTop.mpr ⟨ 2, h_bound ⟩;
          have h_bound : ∀ᶠ p in Filter.atTop, (1 + 1 / (p : ℝ)) * limit_ratio alpha_val ≤ limit_ratio alpha_val + (1 - limit_ratio alpha_val) / 2 := by
            filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( 2 / ( 1 - limit_ratio alpha_val ) ) ] with p hp₁ hp₂ using by nlinarith [ one_div_mul_cancel ( ne_of_gt hp₁ ), mul_div_cancel₀ 2 ( show ( 1 - limit_ratio alpha_val ) ≠ 0 from sub_ne_zero_of_ne <| Ne.symm <| by linarith [ show limit_ratio alpha_val < 1 from by exact limit_ratio_lt_one alpha_val ( show 0 < alpha_val from by norm_num [ alpha_val ] ) ( show alpha_val < 1 / 2 from by norm_num [ alpha_val ] ) ] ), show limit_ratio alpha_val < 1 from by exact limit_ratio_lt_one alpha_val ( show 0 < alpha_val from by norm_num [ alpha_val ] ) ( show alpha_val < 1 / 2 from by norm_num [ alpha_val ] ) ] ;
          filter_upwards [ ‹∀ᶠ p : ℕ in Filter.atTop, bound_func p alpha_val ( z_zero alpha_val ) ≤ ( 1 + 1 / ( p : ℝ ) ) * limit_ratio alpha_val * p›, h_bound.natCast_atTop ] with p hp₁ hp₂ using le_trans hp₁ ( mul_le_mul_of_nonneg_right hp₂ <| Nat.cast_nonneg _ );
        filter_upwards [ h_bound, eventually_bound_func_lt_p alpha_val ( show 0 < alpha_val by norm_num [ alpha_val ] ) ( show alpha_val < 1 / 2 by norm_num [ alpha_val ] ) ] with p hp hp';
        unfold z_final;
        split_ifs <;> try linarith;
        · unfold z_zero at *; norm_num at *;
          exact absurd ( ‹bound_func p alpha_val ( alpha_val / ( 1 - alpha_val ) ) < p → 1 ≤ alpha_val / ( 1 - alpha_val ) › hp' ) ( by rw [ le_div_iff₀ ] <;> norm_num [ alpha_val ] );
        · unfold alpha_val at * ; norm_num at *;
          interval_cases p <;> norm_num [ bound_func, limit_ratio, z_zero ] at *;
          · unfold lambda_plus at * ; norm_num at *;
          · unfold lambda_plus at * ; norm_num at *;
            norm_num [ Real.rpow_def_of_pos ] at *;
            exact False.elim <| hp'.not_ge <| Real.log_nonpos ( by norm_num ) <| by norm_num;
      obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp h_bound;
      -- Let's choose any $c$ such that $c < 1$ and derive a contradiction for $p \geq M$.
      obtain ⟨ c, hc ⟩ : ∃ c < 1, ∀ p ∈ Finset.Icc 2 M, bound_func p alpha_val (z_final p alpha_val) ≤ c * p := by
        have h_bound : ∀ p ∈ Finset.Icc 2 M, bound_func p alpha_val (z_final p alpha_val) / p < 1 := by
          intros p hp_range
          have h_bound : bound_func p alpha_val (z_final p alpha_val) < p := by
            have := z_final_prop p alpha_val ( by linarith [ Finset.mem_Icc.mp hp_range ] ) ( by norm_num [ alpha_val ] ) ( by norm_num [ alpha_val ] ) ; aesop;
          rwa [ div_lt_one ( Nat.cast_pos.mpr ( by linarith [ Finset.mem_Icc.mp hp_range ] ) ) ];
        have h_max : ∃ c < 1, ∀ p ∈ Finset.Icc 2 M, bound_func p alpha_val (z_final p alpha_val) / p ≤ c := by
          by_cases h_empty : Finset.Icc 2 M = ∅;
          · exact ⟨ 0, by norm_num, by aesop ⟩;
          · have h_max : ∃ c ∈ Finset.image (fun p : ℕ => bound_func p alpha_val (z_final p alpha_val) / p) (Finset.Icc 2 M), ∀ y ∈ Finset.image (fun p : ℕ => bound_func p alpha_val (z_final p alpha_val) / p) (Finset.Icc 2 M), c ≥ y := by
              exact ⟨ Finset.max' _ ⟨ _, Finset.mem_image_of_mem _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty h_empty ) ) ⟩, Finset.max'_mem _ _, fun y hy => Finset.le_max' _ _ hy ⟩;
            aesop;
        exact ⟨ h_max.choose, h_max.choose_spec.1, fun p hp => by have := h_max.choose_spec.2 p hp; rwa [ div_le_iff₀ ( Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hp ] ) ] at this ⟩;
      exact ⟨ Max.max c ( limit_ratio alpha_val + ( 1 - limit_ratio alpha_val ) / 2 ), max_lt hc.1 ( by linarith [ show limit_ratio alpha_val < 1 from limit_ratio_lt_one alpha_val ( by norm_num [ alpha_val ] ) ( by norm_num [ alpha_val ] ) ] ), fun p hp => if h : p ≤ M then hc.2 p ( Finset.mem_Icc.mpr ⟨ hp, h ⟩ ) |> le_trans <| mul_le_mul_of_nonneg_right ( le_max_left _ _ ) <| Nat.cast_nonneg _ else hM p ( le_of_not_ge h ) |> le_trans <| mul_le_mul_of_nonneg_right ( le_max_right _ _ ) <| Nat.cast_nonneg _ ⟩

/-
The total bound for the bad set size using the improved z_final.
-/
noncomputable def total_bad_set_bound_v2 (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1)),
    if h : p.Prime then
      @bound_bad_set_p_val_v4 x p ⟨h⟩
    else 0

/-
Definition of the constant c_rho bounding rho_v2.
-/
noncomputable def c_rho : ℝ := Classical.choose (rho_v2_le_c_mul_p 2 (by norm_num))

theorem c_rho_prop : c_rho < 1 ∧ ∀ p ≥ 2, rho_v2 p alpha_val ≤ c_rho * p :=
  Classical.choose_spec (rho_v2_le_c_mul_p 2 (by norm_num))

/-
The cardinality of the bad set for a prime p is bounded by a constant times x to the power of gamma_final.
-/
noncomputable def gamma_final (p : ℕ) (alpha : ℝ) : ℝ :=
  Real.log (rho_v2 p alpha) / Real.log p

theorem bad_set_p_bound_asymptotic_v4 (x : ℝ) (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) :
    bound_bad_set_p_val_v4 x p ≤ C_p_v2 p (z_final p alpha_val) * (lambda_plus p (z_final p alpha_val)) * x ^ (gamma_final p alpha_val) := by
      unfold C_p_v2;
      split_ifs <;> norm_num at *;
      · have := Classical.choose_spec ( weighted_sum_uniform_bound p ( z_final p alpha_val ) hp ( by linarith ) ( by linarith ) );
        refine le_trans ( mul_le_mul_of_nonneg_right ( this.2 _ ) ( Real.rpow_nonneg ( by linarith ) _ ) ) ?_;
        -- Substitute the definitions of `D_func` and `gamma_final`.
        have h_subst : (lambda_plus p (z_final p alpha_val)) ^ (Nat.floor (1 + Real.log x / Real.log p)) * (z_final p alpha_val) ^ (-(alpha_val * Real.log x / Real.log p)) ≤ (lambda_plus p (z_final p alpha_val)) * x ^ (gamma_final p alpha_val) := by
          have h_subst : (lambda_plus p (z_final p alpha_val)) ^ (Nat.floor (1 + Real.log x / Real.log p)) * (z_final p alpha_val) ^ (-(alpha_val * Real.log x / Real.log p)) ≤ (lambda_plus p (z_final p alpha_val)) * (lambda_plus p (z_final p alpha_val) * (z_final p alpha_val) ^ (-alpha_val)) ^ (Real.log x / Real.log p) := by
            have h_subst : (lambda_plus p (z_final p alpha_val)) ^ (Nat.floor (1 + Real.log x / Real.log p)) * (z_final p alpha_val) ^ (-(alpha_val * Real.log x / Real.log p)) ≤ (lambda_plus p (z_final p alpha_val)) ^ (1 + Real.log x / Real.log p) * (z_final p alpha_val) ^ (-(alpha_val * Real.log x / Real.log p)) := by
              gcongr;
              · exact Real.rpow_nonneg ( by linarith ) _;
              · refine' le_trans _ ( Real.rpow_le_rpow_of_exponent_le _ <| Nat.floor_le <| by exact add_nonneg zero_le_one <| div_nonneg ( Real.log_nonneg hx ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.Prime.pos Fact.out );
                · norm_cast;
                · refine' le_trans _ ( lam_ge_H p ( z_final p alpha_val ) hp ( by linarith ) );
                  exact_mod_cast Nat.div_pos ( by linarith ) zero_lt_two;
            convert h_subst using 1;
            rw [ Real.mul_rpow ( by linarith [ show 0 ≤ lambda_plus p ( z_final p alpha_val ) from by
                                                exact le_trans ( by norm_num ) ( lam_ge_H p ( z_final p alpha_val ) hp ( by linarith ) ) ] ) ( by exact Real.rpow_nonneg ( by linarith ) _ ), ← Real.rpow_mul ( by linarith ) ] ; ring_nf;
            rw [ Real.rpow_add ( by linarith [ show 0 < lambda_plus p ( z_final p alpha_val ) from by
                                                exact lt_of_lt_of_le ( by norm_num; linarith ) ( lam_ge_H p ( z_final p alpha_val ) hp ( by linarith ) ) ] ), Real.rpow_one ] ; ring;
          convert h_subst using 2;
          rw [ Real.rpow_def_of_pos ( show 0 < x from by positivity ), Real.rpow_def_of_pos ( show 0 < lambda_plus p ( z_final p alpha_val ) * z_final p alpha_val ^ ( -alpha_val ) from ?_ ) ];
          · rw [ show gamma_final p alpha_val = Real.log ( lambda_plus p ( z_final p alpha_val ) * z_final p alpha_val ^ ( -alpha_val ) ) / Real.log p from rfl ] ; ring_nf;
          · exact mul_pos ( by
              exact lt_of_lt_of_le ( Nat.cast_pos.mpr ( Nat.div_pos ( by linarith ) zero_lt_two ) ) ( lam_ge_H p ( z_final p alpha_val ) hp ( by linarith ) ) ) ( Real.rpow_pos_of_pos ( by linarith ) _ );
        convert mul_le_mul_of_nonneg_left h_subst this.1.le using 1 ; ring_nf!;
        · unfold D_func; ring_nf;
          rw [ show ⌊1 + log x * ( Real.log p ) ⁻¹⌋₊ = ⌊log x * ( Real.log p ) ⁻¹⌋₊ + 1 from Nat.floor_eq_iff ( by nlinarith [ Real.log_nonneg hx, inv_nonneg.2 ( Real.log_nonneg ( show ( p : ℝ ) ≥ 1 by norm_cast; linarith ) ) ] ) |>.2 ⟨ by norm_num; linarith [ Nat.floor_le ( show 0 ≤ log x * ( Real.log p ) ⁻¹ by exact mul_nonneg ( Real.log_nonneg hx ) ( inv_nonneg.2 ( Real.log_nonneg ( show ( p : ℝ ) ≥ 1 by norm_cast; linarith ) ) ) ) ], by norm_num; linarith [ Nat.lt_floor_add_one ( log x * ( Real.log p ) ⁻¹ ) ] ⟩ ] ; ring;
        · ring;
      · rename_i h;
        contrapose! h;
        unfold z_final;
        split_ifs <;> norm_num at *;
        · exact ⟨ by linarith, by unfold z_zero; norm_num [ alpha_val ], by unfold z_zero; norm_num [ alpha_val ] ⟩;
        · exact ⟨ hp, z_choice_prop p alpha_val hp ( by linarith ) |>.1.1, z_choice_prop p alpha_val hp ( by linarith ) |>.1.2.le ⟩;
        · linarith

/-
The bad set for Lemma 2.1 is contained in the union of bad sets for each prime p < 2 log x.
-/
theorem bad_set_lemma_2_1_subset_union (x : ℝ) (hx : x ≥ 1) :
    bad_set_lemma_2_1 x ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1))) (bad_set_p x) := by
      exact bad_set_subset_union x hx

/-
The cardinality of the bad set for Lemma 2.1 is bounded by the total bound.
-/
theorem bad_set_lemma_2_1_card_le_total (x : ℝ) (hx : x ≥ 1) :
    ((bad_set_lemma_2_1 x).card : ℝ) ≤ total_bad_set_bound_v2 x := by
      have := @bad_set_lemma_2_1_subset_union x hx;
      refine' le_trans ( Nat.cast_le.mpr ( Finset.card_le_card this ) ) _;
      refine' le_trans _ ( Finset.sum_le_sum fun p hp => _ );
      rotate_left;
      use fun p => if h : Nat.Prime p then ( bad_set_p x p |> Finset.card : ℝ ) else 0;
      · split_ifs <;> norm_cast;
        convert bad_set_p_card_bound_v4 x p ( Nat.Prime.two_le ‹_› ) hx using 1;
      · refine' le_trans ( Nat.cast_le.mpr ( Finset.card_biUnion_le ) ) _;
        norm_num +zetaDelta at *;
        exact Finset.sum_le_sum fun p hp => by aesop;

/-
gamma_final is bounded by 1 + log c_rho / log p.
-/
theorem gamma_final_bound (p : ℕ) (hp : p ≥ 2) :
    gamma_final p alpha_val ≤ 1 + Real.log c_rho / Real.log p := by
      have := @c_rho_prop;
      rw [ add_div', le_div_iff₀ ];
      · rw [ one_mul, mul_comm ];
        rw [ mul_comm, ← Real.log_rpow, ← Real.log_mul ] <;> norm_num;
        · -- By definition of $gamma_final$, we know that $p^{gamma_final p alpha_val} = rho_v2 p alpha_val$.
          have h_exp : (p : ℝ) ^ gamma_final p alpha_val = rho_v2 p alpha_val := by
            rw [ Real.rpow_def_of_pos ( by positivity ), mul_comm ];
            rw [ show gamma_final p alpha_val = Real.log ( rho_v2 p alpha_val ) / Real.log p from rfl, div_mul_cancel₀ _ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hp ) ) ), Real.exp_log ( _ ) ];
            refine' mul_pos _ _;
            · refine' lt_of_lt_of_le _ ( lam_ge_H p ( z_final p alpha_val ) hp _ ) <;> norm_num;
              · linarith;
              · unfold z_final;
                split_ifs <;> norm_num;
                · exact div_nonneg ( by unfold alpha_val; norm_num ) ( by unfold alpha_val; norm_num );
                · exact le_of_lt ( z_choice_prop p alpha_val hp ( by linarith ) |>.1 |>.1 );
            · exact Real.rpow_pos_of_pos ( z_final_prop p alpha_val hp ( by norm_num [ alpha_val ] ) ( by norm_num [ alpha_val ] ) |>.1 |>.1 ) _;
          exact Real.log_le_log ( by positivity ) ( by linarith [ this.2 p hp ] );
        · linarith;
        · have := this.2 2 ( by norm_num ) ; norm_num at this;
          linarith [ show 0 < rho_v2 2 alpha_val from by
                      apply_rules [ mul_pos, Real.rpow_pos_of_pos ];
                      · exact add_pos_of_pos_of_nonneg ( mul_pos ( by norm_num ) ( add_pos_of_pos_of_nonneg zero_lt_one ( z_final_prop 2 alpha_val ( by norm_num ) ( by norm_num [ alpha_val ] ) ( by norm_num [ alpha_val ] ) |>.1.1.le ) ) ) ( Real.sqrt_nonneg _ );
                      · norm_num;
                      · unfold z_final; norm_num [ alpha_val ];
                        unfold z_choice; norm_num [ alpha_val ];
                        split_ifs <;> norm_num [ z_zero ];
                        have := Classical.choose_spec ( exists_z_lt_one_bound_lt_p 2 ( 49 / 100 ) ( by norm_num ) ( by norm_num ) ) ; aesop; ];
        · linarith;
      · exact Real.log_pos <| Nat.one_lt_cast.mpr hp;
      · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hp

/-
C_decay is positive because c_rho is in (0, 1).
-/
noncomputable def C_decay : ℝ := -Real.log c_rho

theorem C_decay_pos : C_decay > 0 := by
  have hc_rho_pos : 0 < c_rho := by
    have := c_rho_prop.2 2 ( by norm_num );
    unfold rho_v2 at this; norm_num at this;
    unfold bound_func at this; unfold z_final at this; norm_num at this;
    unfold alpha_val z_zero bound_func at this; norm_num at this;
    split_ifs at this <;> norm_num [ lambda_plus ] at this ⊢;
    · linarith [ Real.rpow_pos_of_pos ( by norm_num : ( 0 : ℝ ) < 49 / 51 ) ( - ( 49 / 100 ) ) ];
    · rw [ Real.sqrt_sq ] at this <;> nlinarith [ show 0 < z_choice 2 ( 49 / 100 ) from ( z_choice_prop 2 ( 49 / 100 ) ( by norm_num ) ( by norm_num ) ) |>.1 |>.1, Real.rpow_pos_of_pos ( show 0 < z_choice 2 ( 49 / 100 ) from ( z_choice_prop 2 ( 49 / 100 ) ( by norm_num ) ( by norm_num ) ) |>.1 |>.1 ) ( - ( 49 / 100 ) ) ];
  exact neg_pos_of_neg ( Real.log_neg hc_rho_pos ( c_rho_prop.1 ) )

/-
x^gamma_final is bounded by x * exp(-C_decay * log x / log p).
-/
theorem x_pow_gamma_bound (x : ℝ) (p : ℕ) (hp : p ≥ 2) (hx : x ≥ 1) :
    x ^ (gamma_final p alpha_val) ≤ x * Real.exp (-C_decay * Real.log x / Real.log p) := by
      rw [ Real.rpow_def_of_nonneg ( by positivity ) ];
      -- Using the bound on gamma_final, we can rewrite the exponent in the exponential term.
      have h_exp_bound : log x * gamma_final p alpha_val ≤ log x - (C_decay * log x) / Real.log p := by
        have := gamma_final_bound p hp;
        unfold C_decay;
        convert mul_le_mul_of_nonneg_left this ( Real.log_nonneg hx ) using 1 ; ring;
      rw [ if_neg ( by linarith ) ] ; convert Real.exp_le_exp.mpr h_exp_bound using 1 ; rw [ ← Real.exp_log ( by linarith : 0 < x ) ] ; rw [ ← Real.exp_add ] ; ring_nf;
      norm_num ; ring

/-
C_p_explicit bounds the weighted sum.
-/
noncomputable def C_p_explicit (p : ℕ) (z : ℝ) : ℝ :=
  let H : ℝ := ((p + 1) / 2 : ℕ)
  let L : ℝ := (p / 2 : ℕ)
  let lam_p := lambda_plus p z
  let lam_m := lambda_minus p z
  let c_p := c_plus p z
  let c_m := c_minus p z
  let u_p_sum := L + lam_p - H
  let u_m_sum := L + lam_m - H
  abs c_p * abs u_p_sum + abs c_m * abs u_m_sum

theorem C_p_explicit_works (p : ℕ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    ∀ D : ℕ, weighted_sum p D z ≤ C_p_explicit p z * (lambda_plus p z) ^ D := by
      -- Apply the closed form of the weighted vector.
      have h_closed_form : ∀ D : ℕ, weighted_sum p D z ≤ (abs (c_plus p z) * abs (u_plus p z 0 + u_plus p z 1) + abs (c_minus p z) * abs (u_minus p z 0 + u_minus p z 1)) * (lambda_plus p z) ^ D := by
        have h_closed_form : ∀ D : ℕ, weighted_sum p D z ≤ (abs (c_plus p z * (lambda_plus p z) ^ D * (u_plus p z 0 + u_plus p z 1)) + abs (c_minus p z * (lambda_minus p z) ^ D * (u_minus p z 0 + u_minus p z 1))) := by
          intro D
          have h_closed_form : weighted_sum p D z = c_plus p z * (lambda_plus p z) ^ D * (u_plus p z 0 + u_plus p z 1) + c_minus p z * (lambda_minus p z) ^ D * (u_minus p z 0 + u_minus p z 1) := by
            rw [ weighted_sum_eq_sum_components, weighted_vector_closed_form ];
            · simpa using by ring;
            · linarith;
            · linarith;
          cases abs_cases ( c_plus p z * lambda_plus p z ^ D * ( u_plus p z 0 + u_plus p z 1 ) ) <;> cases abs_cases ( c_minus p z * lambda_minus p z ^ D * ( u_minus p z 0 + u_minus p z 1 ) ) <;> linarith;
        -- Apply the properties of absolute values and the fact that $|\lambda_minus p z^D| \leq \lambda_plus p z^D$.
        have h_abs : ∀ D : ℕ, abs (c_plus p z * lambda_plus p z ^ D * (u_plus p z 0 + u_plus p z 1)) ≤ abs (c_plus p z) * abs (u_plus p z 0 + u_plus p z 1) * (lambda_plus p z) ^ D ∧ abs (c_minus p z * (lambda_minus p z) ^ D * (u_minus p z 0 + u_minus p z 1)) ≤ abs (c_minus p z) * abs (u_minus p z 0 + u_minus p z 1) * (lambda_plus p z) ^ D := by
          intros D
          have h_abs_lambda : abs (lambda_minus p z) ≤ lambda_plus p z := by
            rw [ abs_of_nonneg ( lambda_minus_nonneg p z hp hz.le ) ];
            exact div_le_div_of_nonneg_right ( by linarith [ Real.sqrt_nonneg ( ( ( ( p + 1 ) / 2 : ℕ ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( ( p + 1 ) / 2 : ℕ ) ^ 2 - ( p / 2 : ℕ ) ^ 2 ) ) ] ) ( by norm_num );
          norm_num [ abs_mul, mul_assoc, mul_comm, mul_left_comm ];
          exact ⟨ by rw [ abs_of_nonneg ( show 0 ≤ lambda_plus p z by exact le_trans ( abs_nonneg _ ) h_abs_lambda ) ], by gcongr ⟩;
        exact fun D => by linarith [ h_closed_form D, h_abs D ] ;
      convert h_closed_form using 1;
      unfold C_p_explicit; norm_num [ ← abs_mul ] ;
      unfold u_plus u_minus; norm_num [ abs_mul ] ;
      ring_nf

/-
C_p_explicit is bounded by p^3.
-/
theorem C_p_explicit_bound_loose (p : ℕ) (z : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    C_p_explicit p z ≤ (p : ℝ) ^ 3 := by
      -- Let's simplify the expression for C_p_explicit.
      unfold C_p_explicit;
      unfold c_plus c_minus lambda_plus lambda_minus;
      rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num [ Nat.add_div ] at *;
      · have := Fact.out ( p := Nat.Prime ( 2 * c ) ) ; simp_all +decide [ Nat.prime_mul_iff ] ;
        rw [ Real.sqrt_sq ( by linarith ) ] ; ring_nf ; norm_num [ hz.le, hz1 ];
        rw [ inv_mul_cancel₀ ( by positivity ) ] ; norm_num;
      · rw [ abs_of_nonneg, abs_of_nonneg, abs_of_nonneg ];
        · rw [ abs_of_nonpos ];
          · rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_iff₀ ] <;> ring_nf <;> norm_num;
            · rw [ Real.sq_sqrt ];
              · have h_sqrt_bound : Real.sqrt (1 + (c * 2 - c * z * 4) + c * z ^ 2 * 2 + c ^ 2 + c ^ 2 * z * 2 + (c ^ 2 * z ^ 2 - z * 2) + z ^ 2) ≥ 1 := by
                  exact Real.le_sqrt_of_sq_le ( by nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, mul_le_mul_of_nonneg_left hz1 ( show ( 0 : ℝ ) ≤ c by positivity ) ] );
                nlinarith [ show ( 0 : ℝ ) ≤ c ^ 3 by positivity, show ( 0 : ℝ ) ≤ c ^ 4 by positivity, show ( 0 : ℝ ) ≤ c ^ 5 by positivity, show ( 0 : ℝ ) ≤ c ^ 6 by positivity, show ( 0 : ℝ ) ≤ c ^ 7 by positivity, show ( 0 : ℝ ) ≤ c ^ 8 by positivity, show ( 0 : ℝ ) ≤ c ^ 9 by positivity, show ( 0 : ℝ ) ≤ c ^ 10 by positivity ];
              · nlinarith [ sq_nonneg ( z - 1 ), show ( c : ℝ ) ≥ 1 by norm_cast; linarith ];
            · exact mul_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.sqrt_pos.mpr ( by nlinarith [ sq_nonneg ( z - 1 ), show ( c : ℝ ) ≥ 1 by norm_cast; linarith ] ) );
          · ring_nf;
            nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, Real.sqrt_nonneg ( 1 + ( c * 2 - c * z * 4 ) + c * z ^ 2 * 2 + c ^ 2 + c ^ 2 * z * 2 + ( c ^ 2 * z ^ 2 - z * 2 ) + z ^ 2 ), Real.mul_self_sqrt ( show 0 <= 1 + ( c * 2 - c * z * 4 ) + c * z ^ 2 * 2 + c ^ 2 + c ^ 2 * z * 2 + ( c ^ 2 * z ^ 2 - z * 2 ) + z ^ 2 by nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, sq_nonneg ( z - 1 ), mul_le_mul_of_nonneg_left hz1 <| show ( 0 :ℝ ) ≤ c by positivity ] ) ];
        · exact div_nonneg ( by nlinarith [ Real.sqrt_nonneg ( ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) ), Real.mul_self_sqrt ( show 0 <= ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) from by nlinarith [ sq_nonneg ( ( c + 1 ) * ( 1 + z ) - 2 * z * ( c + 1 ) ) ] ) ] ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by nlinarith [ Real.sqrt_nonneg ( ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) ), Real.mul_self_sqrt ( show 0 <= ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) from by nlinarith [ sq_nonneg ( ( c + 1 ) * ( 1 + z ) - 2 * z * ( c + 1 ) ) ] ) ] ) );
        · nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, Real.sqrt_nonneg ( ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) ), Real.mul_self_sqrt ( show 0 <= ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) by nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, sq_nonneg ( ( c + 1 ) * ( 1 + z ) - 2 * z * ( c + 1 ) ) ] ) ];
        · exact div_nonneg ( sub_nonneg.2 <| by nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, Real.sqrt_nonneg ( ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) ), Real.mul_self_sqrt ( show 0 <= ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) by nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, sq_nonneg ( ( c + 1 ) * ( 1 + z ) - 2 * z * ( c + 1 ) ) ] ) ] ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.2 <| by nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, Real.sqrt_nonneg ( ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) ), Real.mul_self_sqrt ( show 0 <= ( ( c + 1 ) * ( 1 + z ) ) ^ 2 - 4 * z * ( ( c + 1 ) ^ 2 - c ^ 2 ) by nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, sq_nonneg ( ( c + 1 ) * ( 1 + z ) - 2 * z * ( c + 1 ) ) ] ) ] ;

/-
lambda_plus p z is at most p for z in [0, 1].
-/
theorem lambda_plus_le_p (p : ℕ) (z : ℝ) (hp : p ≥ 2) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    lambda_plus p z ≤ p := by
      unfold lambda_plus;
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
      · norm_num [ Nat.add_div ];
        rw [ Real.sqrt_sq ] <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ];
      · norm_num [ Nat.add_div ] ; ring_nf ; norm_num;
        nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith, mul_le_mul_of_nonneg_left hz1 <| show ( 0 : ℝ ) ≤ k by positivity, Real.mul_self_sqrt <| show 0 <= 1 + ( ( k : ℝ ) * 2 - ( k : ℝ ) * z * 4 ) + ( k : ℝ ) * z ^ 2 * 2 + ( k : ℝ ) ^ 2 + ( k : ℝ ) ^ 2 * z * 2 + ( ( k : ℝ ) ^ 2 * z ^ 2 - z * 2 ) + z ^ 2 by nlinarith [ sq_nonneg ( z - 1 ), show ( k : ℝ ) ≥ 1 by norm_cast; linarith ] ]

/-
The bound for the bad set size using the explicit constant.
-/
theorem bad_set_p_bound_asymptotic_explicit (x : ℝ) (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) :
    bound_bad_set_p_val_v4 x p ≤ C_p_explicit p (z_final p alpha_val) * (lambda_plus p (z_final p alpha_val)) * x ^ (gamma_final p alpha_val) := by
      have := C_p_explicit_works p ( z_final p alpha_val ) hp ?_ ?_;
      · refine le_trans ( mul_le_mul_of_nonneg_right ( this _ ) <| ?_ ) ?_;
        · apply_rules [ Real.rpow_nonneg ];
          unfold z_final; split_ifs <;> norm_num;
          · unfold z_zero; norm_num [ alpha_val ];
          · exact le_of_lt ( z_choice_prop p alpha_val hp ( by tauto ) |>.1 |>.1 );
        · unfold D_func gamma_final; norm_num [ Real.rpow_def_of_pos ( show 0 < x by linarith ) ] ; ring_nf;
          rw [ Real.rpow_def_of_pos ] <;> norm_num;
          · rw [ show rho_v2 p alpha_val = lambda_plus p ( z_final p alpha_val ) * ( z_final p alpha_val ) ^ ( -alpha_val ) by
                  exact rfl ] ; rw [ Real.log_mul ( by
                  unfold lambda_plus; norm_num;
                  exact ne_of_gt ( add_pos_of_pos_of_nonneg ( mul_pos ( Nat.cast_pos.mpr ( Nat.div_pos ( by linarith ) zero_lt_two ) ) ( by linarith [ show 0 < z_final p alpha_val from by
                                                                                                                                                        exact ( z_final_prop p alpha_val hp ( by norm_num : ( 0.49 : ℝ ) < 1 / 2 ) ( by norm_num : ( 0 : ℝ ) < 0.49 ) ) |>.1 |>.1 ] ) ) ( Real.sqrt_nonneg _ ) ) ) ( by
                  exact ne_of_gt ( Real.rpow_pos_of_pos ( by
                    exact ( z_final_prop p alpha_val hp ( by norm_num : ( 0.49 : ℝ ) < 1 / 2 ) ( by norm_num : ( 0 : ℝ ) < 0.49 ) ) |>.1 |>.1 ) _ ) ), Real.log_rpow ( by
                  exact ( z_final_prop p alpha_val hp ( by norm_num : ( 0.49 : ℝ ) < 1 / 2 ) ( by norm_num : ( 0 : ℝ ) < 0.49 ) ) |>.1 |>.1 ) ] ; ring_nf
            rw [ Real.exp_add, mul_assoc ];
            rw [ mul_comm ( Real.exp _ ) ];
            gcongr;
            · refine mul_nonneg ?_ ?_;
              · exact add_nonneg ( mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) );
              · unfold lambda_plus; norm_num;
                exact div_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg zero_le_one ( z_final_prop p alpha_val hp ( by
                  exact alpha_val_lt_half ) ( by
                  exact show 0 < 0.49 by norm_num; ) |>.1.1.le ) ) ) ( Real.sqrt_nonneg _ ) ) zero_le_two;
            · rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
              · nlinarith [ Nat.floor_le ( show 0 ≤ Real.log x * ( Real.log p ) ⁻¹ by exact mul_nonneg ( Real.log_nonneg hx ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos Fact.out ) ) ) ) ), Real.log_nonneg ( show 1 ≤ lambda_plus p ( z_final p alpha_val ) by
                                                                                                                                                                                                                                              refine' le_trans _ ( lam_ge_H p ( z_final p alpha_val ) hp ( _ ) );
                                                                                                                                                                                                                                              · exact_mod_cast Nat.div_pos ( by linarith ) zero_lt_two;
                                                                                                                                                                                                                                              · field_simp;
                                                                                                                                                                                                                                                unfold z_final;
                                                                                                                                                                                                                                                split_ifs <;> norm_num;
                                                                                                                                                                                                                                                · unfold z_zero; norm_num [ alpha_val ];
                                                                                                                                                                                                                                                · exact le_of_lt ( z_choice_prop p alpha_val hp ( by tauto ) |>.1 |>.1 ) ) ];
              · unfold lambda_plus; norm_num;
                exact add_pos_of_pos_of_nonneg ( mul_pos ( Nat.cast_pos.mpr ( Nat.div_pos ( by linarith ) zero_lt_two ) ) ( by linarith [ show 0 < z_final p alpha_val from by
                                                                                                                                            exact ( z_final_prop p alpha_val hp ( by norm_num : ( 0.49 : ℝ ) < 1 / 2 ) ( by norm_num : ( 0 : ℝ ) < 0.49 ) ) |>.1 |>.1 ] ) ) ( Real.sqrt_nonneg _ );
          · exact z_final_prop p alpha_val hp ( by norm_num [ alpha_val ] ) ( by norm_num [ alpha_val ] ) |>.1 |>.1;
      · unfold z_final;
        split_ifs <;> norm_num at *;
        · exact div_pos ( by norm_num [ alpha_val ] ) ( by norm_num [ alpha_val ] );
        · have := z_choice_prop p alpha_val hp ( by linarith ) ; aesop;
      · unfold z_final;
        split_ifs <;> norm_num [ alpha_val ];
        · exact le_of_lt ( by unfold z_zero; norm_num );
        · exact z_choice_prop p ( 49 / 100 ) hp ( by norm_num [ alpha_val ] ) |>.1.2.le

/-
The explicit term bound is valid.
-/
noncomputable def term_bound_explicit (x : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ 4 * x * Real.exp (-C_decay * Real.log x / Real.log p)

theorem term_bound_explicit_works (x : ℝ) (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) :
    C_p_explicit p (z_final p alpha_val) * (lambda_plus p (z_final p alpha_val)) * x ^ (gamma_final p alpha_val) ≤ term_bound_explicit x p := by
      -- Apply the bounds from `C_p_explicit_bound_loose`, `lambda_plus_le_p`, and `x_pow_gamma_bound`.
      have h_bound : C_p_explicit p (z_final p alpha_val) * lambda_plus p (z_final p alpha_val) * x ^ (gamma_final p alpha_val) ≤ (p ^ 3) * p * (x * Real.exp (-C_decay * Real.log x / Real.log p)) := by
        gcongr;
        · exact le_trans ( by positivity ) ( lam_ge_H p ( z_final p alpha_val ) hp ( by
            unfold z_final;
            unfold alpha_val z_zero; split_ifs <;> norm_num;
            exact le_of_lt ( z_choice_prop p ( 49 / 100 ) hp ( by norm_num ) |>.1 |>.1 ) ) );
        · apply_rules [ C_p_explicit_bound_loose ];
          · have := z_final_prop p alpha_val hp ( show alpha_val < 1 / 2 by exact show 0.49 < 1 / 2 by norm_num ) ( show 0 < alpha_val by exact show 0 < 0.49 by norm_num ) ; aesop;
          · unfold z_final;
            split_ifs <;> norm_num;
            · linarith;
            · exact z_choice_prop p alpha_val hp ( by tauto ) |>.1 |>.2.le;
        · apply_rules [ lambda_plus_le_p ];
          · unfold z_final;
            unfold z_zero; norm_num;
            unfold alpha_val; norm_num; split_ifs <;> norm_num;
            · exact ( z_choice_prop p ( 49 / 100 ) hp ( by norm_num ) ) |>.1 |>.1.le;
            · linarith;
          · unfold z_final;
            split_ifs <;> norm_num [ z_zero ];
            · unfold alpha_val; norm_num;
            · exact z_choice_prop p alpha_val hp ( by tauto ) |>.1 |>.2.le;
        · convert x_pow_gamma_bound x p hp hx using 1;
      exact h_bound.trans ( by unfold term_bound_explicit; ring_nf; norm_num )

/-
The explicit total bound is an upper bound for the total bad set bound.
-/
noncomputable def total_bad_set_bound_explicit (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1)),
    term_bound_explicit x p

theorem total_bad_set_bound_v2_le_explicit (x : ℝ) (hx : x ≥ 1) :
    total_bad_set_bound_v2 x ≤ total_bad_set_bound_explicit x := by
      apply Finset.sum_le_sum;
      intro p hp;
      split_ifs <;> simp_all +decide [ Nat.Prime.ne_zero, Nat.Prime.ne_one ];
      convert bad_set_p_bound_asymptotic_explicit x p ( Nat.Prime.two_le ‹_› ) hx |> le_trans <| term_bound_explicit_works x p ( Nat.Prime.two_le ‹_› ) hx using 1;
      exact ⟨ by assumption ⟩

/-
The explicit total bound is bounded by the uniform bound.
-/
noncomputable def uniform_bound_explicit (x : ℝ) : ℝ :=
  3 * (2 * Real.log x)^5 * x * Real.exp (-C_decay * Real.log x / Real.log (2 * Real.log x))

theorem total_bad_set_bound_explicit_le_uniform (x : ℝ) (hx : x ≥ 3) :
    total_bad_set_bound_explicit x ≤ uniform_bound_explicit x := by
      -- By definition of total_bad_set_bound_explicit and uniform_bound_explicit, we can show that each term in the sum for total_bad_set_bound_explicit is less than or equal to the corresponding term in uniform_bound_explicit.
      have h_term_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1)), term_bound_explicit x p ≤ (2 * Real.log x) ^ 4 * x * Real.exp (-C_decay * Real.log x / Real.log (2 * Real.log x)) := by
        refine fun p hp => mul_le_mul ?_ ?_ ?_ ?_;
        · gcongr;
          exact le_trans ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ) ( Nat.floor_le ( by linarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ x ) ] ) );
        · field_simp;
          gcongr;
          · exact mul_nonneg ( le_of_lt ( C_decay_pos ) ) ( Real.log_nonneg ( by linarith ) );
          · exact Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) );
          · exact Nat.cast_pos.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) );
          · exact le_trans ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ) ( Nat.floor_le ( by linarith [ Real.log_nonneg ( by linarith : ( 1:ℝ ) ≤ x ) ] ) ) |> le_trans <| by linarith;
        · positivity;
        · positivity;
      refine' le_trans ( Finset.sum_le_sum h_term_bound ) _;
      rw [ Finset.sum_const, Finset.card_filter ];
      rw [ Finset.sum_range_succ' ];
      norm_num [ uniform_bound_explicit ];
      refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by positivity ) _ ; norm_num ; ring_nf;
      nlinarith [ show 0 < Real.log x ^ 4 * x * Real.exp ( - ( Real.log x * C_decay * ( Real.log ( Real.log x * 2 ) ) ⁻¹ ) ) by exact mul_pos ( mul_pos ( pow_pos ( Real.log_pos ( by linarith ) ) 4 ) ( by linarith ) ) ( Real.exp_pos _ ), show ( ⌊Real.log x * 2⌋₊ : ℝ ) ≤ Real.log x * 2 by exact Nat.floor_le ( by linarith [ Real.log_nonneg ( by linarith : ( 1 :ℝ ) ≤ x ) ] ), Real.log_pos ( by linarith : ( 1 :ℝ ) < x ) ]

/-
The uniform bound is o(x).
-/
theorem uniform_bound_is_little_o :
    uniform_bound_explicit =o[Filter.atTop] (fun x => x) := by
      -- We want to show `uniform_bound_explicit / x` tends to 0.
      -- `uniform_bound_explicit / x = 3 * (2 log x)^5 * exp(-C_decay * log x / log(2 log x))`.
      -- Let `y = log x`. As `x -> infinity`, `y -> infinity`.
      -- The expression is `3 * (2y)^5 * exp(-C_decay * y / log(2y))`.
      -- Taking the logarithm: `log(3) + 5 log(2y) - C_decay * y / log(2y)`.
      have h_limit : Filter.Tendsto (fun y : ℝ => Real.log 3 + 5 * Real.log (2 * y) - C_decay * y / Real.log (2 * y)) Filter.atTop Filter.atBot := by
        -- We want to show that $5 \log(2y) - \frac{C_decay \cdot y}{\log(2y)}$ tends to $-\infty$ as $y \to \infty$.
        suffices h_tendsto : Filter.Tendsto (fun y : ℝ => 5 * Real.log (2 * y) - C_decay * y / Real.log (2 * y)) Filter.atTop Filter.atBot by
          simpa only [ add_sub_assoc ] using Filter.Tendsto.add_atBot tendsto_const_nhds h_tendsto;
        -- We'll use the fact that $C_decay > 0$ and $\log(2y)$ grows slower than $y$.
        have h_log_growth : Filter.Tendsto (fun y => y / Real.log (2 * y) / Real.log (2 * y)) Filter.atTop Filter.atTop := by
          -- We can use the change of variables $u = \log(2y)$ to transform the limit expression.
          suffices h_change : Filter.Tendsto (fun u => Real.exp u / u ^ 2) Filter.atTop Filter.atTop by
            have h_subst : Filter.Tendsto (fun y => Real.exp (Real.log (2 * y)) / (Real.log (2 * y)) ^ 2) Filter.atTop Filter.atTop := by
              exact h_change.comp ( Real.tendsto_log_atTop.comp <| Filter.tendsto_id.const_mul_atTop zero_lt_two );
            have h_subst : Filter.Tendsto (fun y => (2 * y) / (Real.log (2 * y)) ^ 2) Filter.atTop Filter.atTop := by
              refine h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Real.exp_log ( by positivity ) ] );
            convert h_subst.const_mul_atTop ( show ( 0 : ℝ ) < 1 / 2 by norm_num ) using 2 ; ring;
          exact Real.tendsto_exp_div_pow_atTop 2;
        have h_log_growth : Filter.Tendsto (fun y => 5 * Real.log (2 * y) - C_decay * (y / Real.log (2 * y) / Real.log (2 * y)) * Real.log (2 * y)) Filter.atTop Filter.atBot := by
          have h_log_growth : Filter.Tendsto (fun y => (5 - C_decay * (y / Real.log (2 * y) / Real.log (2 * y))) * Real.log (2 * y)) Filter.atTop Filter.atBot := by
            have h_log_growth : Filter.Tendsto (fun y => 5 - C_decay * (y / Real.log (2 * y) / Real.log (2 * y))) Filter.atTop Filter.atBot := by
              exact Filter.Tendsto.add_atBot tendsto_const_nhds ( Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.const_mul_atTop ( show 0 < C_decay by exact C_decay_pos ) h_log_growth );
            exact Filter.Tendsto.atBot_mul_atTop₀ h_log_growth ( Real.tendsto_log_atTop.comp <| Filter.tendsto_id.const_mul_atTop zero_lt_two );
          exact h_log_growth.congr fun x => by ring;
        grind;
      -- Since the logarithm of the expression tends to negative infinity, the expression itself tends to 0.
      have h_exp_zero : Filter.Tendsto (fun x : ℝ => Real.exp (Real.log 3 + 5 * Real.log (2 * Real.log x) - C_decay * Real.log x / Real.log (2 * Real.log x))) Filter.atTop (nhds 0) := by
        norm_num +zetaDelta at *;
        exact h_limit.comp ( Real.tendsto_log_atTop );
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · refine' squeeze_zero_norm' _ h_exp_zero;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
        unfold uniform_bound_explicit; norm_num [ Real.exp_add, Real.exp_sub, Real.exp_nat_mul, Real.exp_log, hx.le ] ; ring_nf ;
        rw [ abs_of_pos ( Real.log_pos hx ), abs_of_pos ( by positivity ) ] ; norm_num [ Real.exp_neg, Real.exp_mul, Real.exp_log, hx.le ] ; ring_nf;
        rw [ Real.exp_log ( by nlinarith [ Real.log_pos hx ] ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans hx ) ] ; ring_nf ; norm_num;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
The bad set for Lemma 2.1 has asymptotic density 0.
-/
theorem bad_set_lemma_2_1_density_zero :
    (fun x => ((bad_set_lemma_2_1 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      -- Combining the bounds, we get `|bad_set_lemma_2_1| =o(x)`.
      have upper_bound_combined : (fun x : ℝ => (bad_set_lemma_2_1 x).card : ℝ → ℝ) =o[Filter.atTop] (fun x : ℝ => x) := by
        have := @uniform_bound_is_little_o
        -- Combining the bounds, we get `|bad_set_lemma_2_1| ≤ uniform_bound_explicit`.
        have upper_bound_combined : ∀ x : ℝ, x ≥ 3 → ((bad_set_lemma_2_1 x).card : ℝ) ≤ uniform_bound_explicit x := by
          intros x hx
          have := bad_set_lemma_2_1_card_le_total x (by linarith)
          have := total_bad_set_bound_v2_le_explicit x (by linarith)
          have := total_bad_set_bound_explicit_le_uniform x (by linarith)
          linarith;
        rw [ Asymptotics.isLittleO_iff_tendsto' ] at *;
        · refine' squeeze_zero_norm' _ this;
          filter_upwards [ Filter.eventually_ge_atTop 3 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( upper_bound_combined x hx ) ( by positivity ) ;
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne';
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using False.elim <| hx.ne' hx';
      grind

/-
The size of the bad set for Lemma 2.2 is bounded by the sum of bounds for each condition.
-/
noncomputable def K_min (x : ℝ) : ℕ := Nat.floor (Real.log x)

noncomputable def bad_set_lemma_2_2 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ k ∈ Finset.Icc (K_min x) (Nat.floor (0.7 * Real.log x)),
      ∃ p ∈ Finset.range (2 * k + 1), p.Prime ∧
        ∃ i ∈ Finset.Icc 1 k, (padicValNat p (m + i) : ℝ) > 3 * Real.log k / Real.log p)

theorem bad_set_lemma_2_2_bound (x : ℝ) (hx : x ≥ 3) :
    ((bad_set_lemma_2_2 x).card : ℝ) ≤
    ∑ k ∈ Finset.Icc (K_min x) (Nat.floor (0.7 * Real.log x)),
      ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * k + 1)),
        ∑ i ∈ Finset.Icc 1 k, (x / (k : ℝ)^3 + 1) := by
          unfold bad_set_lemma_2_2;
          -- For each $k$, $p$, and $i$, the number of $m$ satisfying the conditions is at most $x / k^3 + 1$. Therefore, we can bound the cardinality of the bad set by summing these bounds over all $k$, $p$, and $i$.
          have h_bound : ∀ k ∈ Finset.Icc (K_min x) (Nat.floor (0.7 * Real.log x)), ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * k + 1)), ∀ i ∈ Finset.Icc 1 k, ((Finset.filter (fun m => (padicValNat p (m + i) : ℝ) > 3 * Real.log k / Real.log p) (Finset.Icc 1 (Nat.floor x))).card : ℝ) ≤ x / k^3 + 1 := by
            intro k hk p hp i hi
            have h_count : ((Finset.filter (fun m => p^(Nat.ceil (3 * Real.log k / Real.log p)) ∣ (m + i)) (Finset.Icc 1 (Nat.floor x))).card : ℝ) ≤ x / k^3 + 1 := by
              -- The number of integers $m$ such that $p^{⌈3 \log k / \log p⌉} \mid (m + i)$ is at most $x / p^{⌈3 \log k / \log p⌉} + 1$.
              have h_div_count : ((Finset.filter (fun m => p^(Nat.ceil (3 * Real.log k / Real.log p)) ∣ (m + i)) (Finset.Icc 1 (Nat.floor x))).card : ℝ) ≤ (Nat.floor x : ℝ) / p^(Nat.ceil (3 * Real.log k / Real.log p)) + 1 := by
                have h_div_count : ((Finset.filter (fun m => p^(Nat.ceil (3 * Real.log k / Real.log p)) ∣ (m + i)) (Finset.Icc 1 (Nat.floor x))).card : ℝ) ≤ (Nat.floor x : ℝ) / p^(Nat.ceil (3 * Real.log k / Real.log p)) + 1 := by
                  have h_div_count_aux : Finset.filter (fun m => p^(Nat.ceil (3 * Real.log k / Real.log p)) ∣ (m + i)) (Finset.Icc 1 (Nat.floor x)) ⊆ Finset.image (fun m => p^(Nat.ceil (3 * Real.log k / Real.log p)) * m - i) (Finset.Icc 1 ((Nat.floor x + i) / p^(Nat.ceil (3 * Real.log k / Real.log p)))) := by
                    intro m hm;
                    norm_num +zetaDelta at *;
                    exact ⟨ ( m + i ) / p ^ ⌈3 * Real.log k / Real.log p⌉₊, ⟨ Nat.div_pos ( Nat.le_of_dvd ( by linarith ) hm.2 ) ( pow_pos hp.2.pos _ ), Nat.div_le_div_right ( by linarith ) ⟩, Nat.sub_eq_of_eq_add <| by linarith [ Nat.div_mul_cancel hm.2 ] ⟩
                  have := Finset.card_mono h_div_count_aux;
                  refine le_trans ( Nat.cast_le.mpr this ) ?_;
                  refine' le_trans ( Nat.cast_le.mpr <| Finset.card_image_le ) _ ; norm_num;
                  rw [ div_add_one, le_div_iff₀ ] <;> norm_cast <;> norm_num;
                  · linarith [ Nat.div_mul_le_self ( ⌊x⌋₊ + i ) ( p ^ ⌈3 * Real.log k / Real.log p⌉₊ ), show i ≤ p ^ ⌈3 * Real.log k / Real.log p⌉₊ from le_trans ( Finset.mem_Icc.mp hi |>.2 ) ( show k ≤ p ^ ⌈3 * Real.log k / Real.log p⌉₊ from le_trans ( show k ≤ p ^ ( Nat.ceil ( 3 * Real.log k / Real.log p ) ) from by
                                                                                                                                                                                                                                                                have := Nat.le_ceil ( 3 * Real.log k / Real.log p );
                                                                                                                                                                                                                                                                rw [ div_le_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) ] at this;
                                                                                                                                                                                                                                                                rw [ ← @Nat.cast_le ℝ ] ; push_cast ; rw [ ← Real.log_le_log_iff ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop ) ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) _ ) ] ; simpa using this.trans' <| by linarith [ Real.log_nonneg <| show ( k :ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hk, Finset.mem_Icc.mp hi ] ] ; ) le_rfl ) ];
                  · exact pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _;
                  · aesop;
                convert h_div_count using 1;
              -- Since $p^{⌈3 \log k / \log p⌉} \geq k^3$, we have $x / p^{⌈3 \log k / \log p⌉} \leq x / k^3$.
              have h_exp_bound : (p : ℝ)^(Nat.ceil (3 * Real.log k / Real.log p)) ≥ k^3 := by
                have h_exp : (Nat.ceil (3 * Real.log k / Real.log p)) * Real.log p ≥ 3 * Real.log k := by
                  have := Nat.le_ceil ( 3 * Real.log k / Real.log p ) ; rw [ div_le_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) ] at this; linarith;
                rw [ ge_iff_le, ← Real.log_le_log_iff ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop_cat ) _ ) ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) _ ), Real.log_pow ] ; aesop;
              refine le_trans h_div_count ?_;
              field_simp;
              rw [ div_add_one, div_le_div_iff₀ ] <;> nlinarith [ Nat.floor_le ( show 0 ≤ x by linarith ), show ( k : ℝ ) ^ 3 > 0 by exact pow_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop_cat ) 3 ];
            refine le_trans ?_ h_count;
            gcongr;
            intro m hm; haveI := Fact.mk ( Finset.mem_filter.mp hp |>.2 ) ; simp_all +decide [ padicValNat_dvd_iff ] ;
            exact Or.inr hm.le;
          refine' le_trans ( Nat.cast_le.mpr <| Finset.card_le_card _ ) _;
          exact Finset.biUnion ( Finset.Icc ( K_min x ) ⌊0.7 * Real.log x⌋₊ ) fun k => Finset.biUnion ( Finset.filter Nat.Prime ( Finset.range ( 2 * k + 1 ) ) ) fun p => Finset.biUnion ( Finset.Icc 1 k ) fun i => Finset.filter ( fun m => ( padicValNat p ( m + i ) : ℝ ) > 3 * Real.log k / Real.log p ) ( Finset.Icc 1 ⌊x⌋₊ );
          · simp +contextual [ Finset.subset_iff ];
            exact fun m hm₁ hm₂ k hk₁ hk₂ p hp₁ hp₂ i hi₁ hi₂ hi₃ => ⟨ k, ⟨ hk₁, hk₂ ⟩, p, ⟨ hp₁, hp₂ ⟩, i, ⟨ hi₁, hi₂ ⟩, hi₃ ⟩;
          · refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
            push_cast;
            refine' Finset.sum_le_sum fun k hk => le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
            push_cast;
            exact Finset.sum_le_sum fun p hp => le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) <| by simpa using Finset.sum_le_sum fun i hi => h_bound k hk p hp i hi;

/-
The size of the corrected bad set for Lemma 2.2 is bounded.
-/
noncomputable def K_max (x : ℝ) : ℕ := Nat.floor (0.7 * Real.log x)

noncomputable def bad_set_lemma_2_2_v3 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_max x + 1), p.Prime ∧
      ∃ i ∈ Finset.Icc 1 (K_max x), (padicValNat p (m + i) : ℝ) > 3 * Real.log (K_max x) / Real.log p)

theorem bad_set_lemma_2_2_v3_bound (x : ℝ) (hx : x ≥ 3) :
    ((bad_set_lemma_2_2_v3 x).card : ℝ) ≤
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_max x + 1)),
      ∑ i ∈ Finset.Icc 1 (K_max x), (x / (K_max x : ℝ)^3 + 1) := by
        have h_union : (bad_set_lemma_2_2_v3 x : Finset ℕ) ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (2 * K_max x + 1))) (fun p => Finset.biUnion (Finset.Icc 1 (K_max x)) (fun i => Finset.filter (fun m => (padicValNat p (m + i) : ℝ) > 3 * Real.log (K_max x) / Real.log p) (Finset.Icc 1 (Nat.floor x)))) := by
          intro m hm;
          unfold bad_set_lemma_2_2_v3 at hm; aesop;
        -- Apply the cardinality bound to each term in the union.
        have h_card_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_max x + 1)), ∀ i ∈ Finset.Icc 1 (K_max x), ((Finset.filter (fun m => (padicValNat p (m + i) : ℝ) > 3 * Real.log (K_max x) / Real.log p) (Finset.Icc 1 (Nat.floor x))).card : ℝ) ≤ (x / (K_max x)^3 + 1) := by
          intros p hp i hi;
          -- For fixed `p` and `i`, the number of `m` is at most `x / p^(3 log K / log p) + 1`.
          have h_card_filter : ((Finset.filter (fun m => p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1) ∣ m + i) (Finset.Icc 1 (Nat.floor x))).card : ℝ) ≤ (x / (K_max x)^3 + 1) := by
            -- The number of multiples of $p^{3 \log K / \log p}$ in the range $1$ to $x$ is at most $x / p^{3 \log K / \log p} + 1$.
            have h_multiples : ((Finset.filter (fun m => p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1) ∣ m + i) (Finset.Icc 1 (Nat.floor x))).card : ℝ) ≤ (Nat.floor x) / (p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1)) + 1 := by
              have h_multiples : ((Finset.filter (fun m => p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1) ∣ m + i) (Finset.Icc 1 (Nat.floor x))).card : ℝ) ≤ (Nat.floor x + i) / (p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1)) := by
                have h_multiples : Finset.filter (fun m => p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1) ∣ m + i) (Finset.Icc 1 (Nat.floor x)) ⊆ Finset.image (fun m => m * p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1) - i) (Finset.Icc 1 ((Nat.floor x + i) / p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1))) := by
                  intro m hm;
                  obtain ⟨ k, hk ⟩ := Finset.mem_filter.mp hm |>.2;
                  simp +zetaDelta at *;
                  exact ⟨ k, ⟨ by nlinarith [ pow_pos hp.2.pos ( ⌊3 * Real.log ( K_max x ) / Real.log p⌋₊ + 1 ) ], Nat.le_div_iff_mul_le ( pow_pos hp.2.pos _ ) |>.2 <| by nlinarith [ pow_pos hp.2.pos ( ⌊3 * Real.log ( K_max x ) / Real.log p⌋₊ + 1 ) ] ⟩, Nat.sub_eq_of_eq_add <| by linarith ⟩;
                refine' le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_multiples ) _;
                exact le_trans ( Nat.cast_le.mpr <| Finset.card_image_le ) <| by norm_num; rw [ le_div_iff₀ <| pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) _ ] ; norm_cast ; nlinarith [ Nat.div_mul_le_self ( ⌊x⌋₊ + i ) ( p ^ ( ⌊3 * Real.log ( K_max x ) / Real.log p⌋₊ + 1 ) ) ] ;
              simp +zetaDelta at *;
              refine le_trans h_multiples ?_;
              rw [ div_add_one, div_le_div_iff_of_pos_right ] <;> norm_cast <;> norm_num [ hp.2.pos ];
              · refine' le_trans hi.2 _;
                have := Nat.lt_floor_add_one ( 3 * Real.log ( K_max x ) / Real.log p );
                rw [ div_lt_iff₀ ( Real.log_pos <| mod_cast hp.2.one_lt ) ] at this;
                rw [ ← @Nat.cast_le ℝ ] ; push_cast ; rw [ ← Real.log_le_log_iff ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop ) ( pow_pos ( Nat.cast_pos.mpr hp.2.pos ) _ ) ] ; simpa using by nlinarith [ Real.log_pos <| show ( p :ℝ ) > 1 from mod_cast hp.2.one_lt ] ;
              · exact hp.2.ne_zero;
            -- Since $p^{Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1} \geq (K_max x)^3$, we have $(Nat.floor x) / (p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1)) \leq (Nat.floor x) / (K_max x)^3$.
            have h_div_bound : (Nat.floor x) / (p^(Nat.floor (3 * Real.log (K_max x) / Real.log p) + 1) : ℝ) ≤ (Nat.floor x) / (K_max x)^3 := by
              gcongr;
              · exact pow_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) ) ) _;
              · have := Nat.lt_floor_add_one ( 3 * Real.log ( K_max x ) / Real.log p );
                rw [ div_lt_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) ] at this;
                rw [ ← Real.log_le_log_iff ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop ) _ ) ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) _ ), Real.log_pow, Real.log_pow ] ; norm_num ; linarith;
            exact h_multiples.trans ( add_le_add_right ( h_div_bound.trans ( by gcongr ; exact Nat.floor_le <| by positivity ) ) _ );
          refine le_trans ?_ h_card_filter;
          gcongr;
          intro m hm;
          refine' Nat.dvd_trans ( pow_dvd_pow _ _ ) ( Nat.ordProj_dvd _ _ );
          refine' Nat.succ_le_of_lt ( Nat.floor_lt ( _ ) |>.2 _ );
          · exact div_nonneg ( mul_nonneg zero_le_three ( Real.log_natCast_nonneg _ ) ) ( Real.log_natCast_nonneg _ );
          · rw [ Nat.factorization ] ; aesop;
        refine le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_union ) ?_;
        refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
        push_cast;
        refine' Finset.sum_le_sum fun p hp => _;
        exact le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) <| by simpa using Finset.sum_le_sum fun i hi => h_card_bound p hp i hi;

/-
The bound for Lemma 2.2 is o(x).
-/
noncomputable def bound_lemma_2_2_v3_func (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_max x + 1)),
    ∑ i ∈ Finset.Icc 1 (K_max x), (x / (K_max x : ℝ)^3 + 1)

theorem bound_lemma_2_2_v3_is_little_o :
    bound_lemma_2_2_v3_func =o[Filter.atTop] (fun x => x) := by
      unfold bound_lemma_2_2_v3_func;
      rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
      · -- The number of terms in the outer sum is `pi(2 * K_max x)`, which is bounded by `2 * K_max x`.
        have h_outer_sum : ∀ x : ℝ, x ≥ 3 → ((Finset.filter Nat.Prime (Finset.range (2 * K_max x + 1))).card : ℝ) ≤ 2 * K_max x := by
          intro x hx; norm_cast; refine' le_trans ( Finset.card_le_card <| show Finset.filter Nat.Prime ( Finset.range ( 2 * K_max x + 1 ) ) ⊆ Finset.Ico 2 ( 2 * K_max x + 1 ) from fun p hp => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2, Finset.mem_range.mp <| Finset.mem_filter.mp hp |>.1 ⟩ ) _ ; simp +arith +decide;
        -- The term `2 * x / K_max x` tends to 0 because `1 / log x` tends to 0.
        have h_term1 : Filter.Tendsto (fun x : ℝ => 2 * x / (K_max x : ℝ) / x) Filter.atTop (nhds 0) := by
          -- We can simplify the expression $2 * x / (K_max x : ℝ) / x$ to $2 / (K_max x : ℝ)$.
          suffices h_simplified : Filter.Tendsto (fun x : ℝ => 2 / (K_max x : ℝ)) Filter.atTop (nhds 0) by
            refine h_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ div_right_comm, mul_div_cancel_right₀ _ hx.ne' ] );
          refine' tendsto_const_nhds.div_atTop _;
          exact tendsto_natCast_atTop_atTop.comp ( tendsto_nat_floor_atTop.comp <| Filter.Tendsto.const_mul_atTop ( by norm_num ) <| Real.tendsto_log_atTop );
        -- The term `2 * K_max x ^ 2 / x` tends to 0 because `(log x)^2 / x` tends to 0.
        have h_term2 : Filter.Tendsto (fun x : ℝ => 2 * (K_max x : ℝ) ^ 2 / x) Filter.atTop (nhds 0) := by
          -- We can use the fact that $(\log x)^2 / x$ tends to $0$ as $x$ tends to infinity.
          have h_log_sq_div_x : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) Filter.atTop (nhds 0) := by
            -- Let $y = \log x$, therefore the expression becomes $\frac{y^2}{e^y}$.
            suffices h_log_sq_div_exp : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp y) Filter.atTop (nhds 0) by
              have := h_log_sq_div_exp.comp Real.tendsto_log_atTop;
              exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
            simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
          -- Since $K_{\text{max}} x \leq 0.7 \log x$, we have $(K_{\text{max}} x)^2 \leq (0.7 \log x)^2$.
          have h_K_max_sq_le : ∀ x : ℝ, x ≥ 3 → (K_max x : ℝ) ^ 2 ≤ (0.7 * Real.log x) ^ 2 := by
            intro x hx; gcongr ; norm_num [ K_max ] ;
            exact Nat.floor_le ( by linarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ x ) ] );
          refine' squeeze_zero_norm' _ _;
          exacts [ fun x => 2 * ( 0.7 * Real.log x ) ^ 2 / x, Filter.eventually_atTop.mpr ⟨ 3, fun x hx => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( by nlinarith [ h_K_max_sq_le x hx ] ) ( by positivity ) ⟩, by convert h_log_sq_div_x.const_mul ( 2 * ( 0.7 : ℝ ) ^ 2 ) using 2 <;> ring ];
        -- Using the bounds from h_outer_sum, we can show that the expression is bounded above by the sum of the two terms.
        have h_bound : ∀ x : ℝ, x ≥ 3 → ((Finset.filter Nat.Prime (Finset.range (2 * K_max x + 1))).card * (K_max x * (x / K_max x ^ 3)) + (Finset.filter Nat.Prime (Finset.range (2 * K_max x + 1))).card * K_max x) / x ≤ (2 * x / (K_max x : ℝ) / x) + (2 * (K_max x : ℝ) ^ 2 / x) := by
          intro x hx; specialize h_outer_sum x hx; by_cases h : K_max x = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_succ' ] ;
          -- By simplifying, we can see that the left-hand side is indeed less than or equal to the right-hand side.
          field_simp [h] at *; (
          exact_mod_cast h_outer_sum);
        refine' squeeze_zero_norm' _ ( by simpa using h_term1.add h_term2 );
        filter_upwards [ Filter.eventually_ge_atTop 3 ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( div_nonneg ( by positivity ) ( by positivity ) ) ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ) ( by positivity ) ) ] ; exact h_bound x hx;
      · exact ⟨ 1, by intros; linarith ⟩

/-
The bad set for Lemma 2.2 (v3) has asymptotic density 0.
-/
theorem bad_set_lemma_2_2_v3_density_zero :
    (fun x => ((bad_set_lemma_2_2_v3 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      refine' Asymptotics.isLittleO_iff.mpr _;
      norm_num +zetaDelta at *;
      intro c hc_pos
      obtain ⟨a, ha⟩ : ∃ a, ∀ b, a ≤ b → bound_lemma_2_2_v3_func b ≤ c * |b| := by
        have := bound_lemma_2_2_v3_is_little_o;
        rw [ Asymptotics.isLittleO_iff ] at this;
        exact Filter.eventually_atTop.mp ( this hc_pos ) |> fun ⟨ a, ha ⟩ => ⟨ a, fun b hb => le_of_abs_le ( ha b hb ) ⟩;
      refine' ⟨ Max.max a 3, fun x hx => le_trans _ ( ha x ( le_trans ( le_max_left _ _ ) hx ) ) ⟩;
      convert bad_set_lemma_2_2_v3_bound x ( by linarith [ le_max_right a 3 ] ) using 1

/-
The function 0.7 * log p / (p-1) is bounded by 0.486 for all primes p.
-/
theorem log_p_div_p_sub_one_bound (p : ℕ) [Fact p.Prime] :
    0.7 * Real.log p / (p - 1) ≤ 0.486 := by
      rcases p with ( _ | _ | _ | p ) <;> norm_num at *;
      · have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
      · rw [ div_le_iff₀ ( by positivity ) ];
        have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( p + 1 + 1 + 1 : ℝ ) / 2 );
        rw [ Real.log_div ] at this <;> norm_num at *;
        · have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
        · linarith

/-
The p-adic valuation of k! is strictly less than k/(p-1).
-/
theorem legendre_bound_strict (k p : ℕ) [Fact p.Prime] (hk : k > 0) :
    (padicValNat p (Nat.factorial k) : ℝ) < k / (p - 1) := by
      have h_legendre : padicValNat p (Nat.factorial k) = ∑ i ∈ Finset.Ico 1 (Nat.log p k + 1), (k / p ^ i) := by
        rw [ padicValNat_factorial ];
        grind;
      -- We can bound the sum $\sum_{i=1}^{\infty} \frac{k}{p^i}$ by a geometric series.
      have h_geo_series : ∑ i ∈ Finset.Ico 1 (Nat.log p k + 1), (k / p ^ i : ℝ) < k * (∑' i : ℕ, (1 / p : ℝ) ^ (i + 1)) := by
        rw [ Finset.sum_Ico_eq_sum_range ];
        norm_num [ div_eq_mul_inv, pow_add, tsum_mul_left ];
        rw [ ← Finset.mul_sum _ _ _ ];
        gcongr;
        exact lt_of_lt_of_le ( by simpa [ Finset.sum_range_succ ] using by exact mul_pos ( inv_pos.mpr ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ) ) <| inv_pos.mpr <| Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) <| Summable.sum_le_tsum ( Finset.range ( Nat.log p k + 1 ) ) ( fun _ _ => by positivity ) <| by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out ) |> Summable.mul_right _;
      have h_geo_series_sum : ∑' i : ℕ, (1 / p : ℝ) ^ (i + 1) = 1 / (p - 1) := by
        ring_nf at *;
        rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( mod_cast Fact.out ) ) ] ; ring_nf;
        rw [ ← mul_inv, mul_sub, mul_inv_cancel₀ ] <;> ring_nf ; norm_num [ Nat.Prime.ne_zero Fact.out ];
      simp_all +decide [ div_eq_mul_inv ];
      exact lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => by rw [ ← div_eq_mul_inv ] ; rw [ le_div_iff₀ ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ) ] ; norm_cast; linarith [ Nat.div_mul_le_self k ( p ^ ‹_› ) ] ) h_geo_series

/-
For p > 2k, the p-adic valuation of the descending factorial is bounded by the valuation of the binomial coefficient.
-/
theorem valuation_large_p (m k p : ℕ) [Fact p.Prime] (hk : k > 0) (hp : p > 2 * k) :
    padicValNat p (Nat.descFactorial (m + k) k) ≤ padicValNat p (Nat.choose (2 * m) m) := by
      -- If there are no multiples, then $v_p(descFact) = 0$, and the inequality holds trivially.
      by_cases h_mult : ∃ i ∈ Finset.Icc 1 k, p ∣ (m + i);
      · obtain ⟨i, hi₁, hi₂⟩ : ∃ i ∈ Finset.Icc 1 k, p ∣ (m + i) := h_mult
        have h_vp_descFact : padicValNat p (Nat.descFactorial (m + k) k) = padicValNat p (m + i) := by
          have h_vp_descFact : ∀ j ∈ Finset.Icc 1 k, j ≠ i → ¬(p ∣ (m + j)) := by
            intros j hj₁ hj₂ hj₃; have := Nat.dvd_sub' hi₂ hj₃; simp_all +decide
            exact hj₂ ( by obtain ⟨ x, hx ⟩ := hi₂; obtain ⟨ y, hy ⟩ := hj₃; nlinarith [ show x = y by nlinarith ] );
          have h_vp_descFact : padicValNat p (Nat.descFactorial (m + k) k) = padicValNat p (∏ j ∈ Finset.Icc 1 k, (m + j)) := by
            rw [ Nat.descFactorial_eq_prod_range ];
            erw [ Finset.prod_Ico_eq_prod_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
            rw [ ← Finset.prod_range_reflect ];
            exact congr_arg _ ( Finset.prod_congr rfl fun x hx => by cases k <;> norm_num at * ; omega );
          have h_vp_descFact : padicValNat p (∏ j ∈ Finset.Icc 1 k, (m + j)) = padicValNat p (m + i) + padicValNat p (∏ j ∈ Finset.Icc 1 k \ {i}, (m + j)) := by
            rw [ ← padicValNat.mul ];
            · rw [ Finset.prod_eq_mul_prod_diff_singleton hi₁ ];
            · aesop;
            · exact Finset.prod_ne_zero_iff.mpr fun x hx => by linarith [ Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hx |>.1 ) ] ;
          simp_all +decide [ Nat.Prime.dvd_iff_not_coprime Fact.out ];
          exact Or.inr <| Or.inr <| Nat.Coprime.prod_right fun x hx => by aesop;
        -- Let $j = v_p(m+i)$. Then $p^j | m+i$.
        set j := padicValNat p (m + i)
        have h_div : p ^ j ∣ m + i := by
          exact pow_padicValNat_dvd;
        -- Since $p > 2k$, we have $2i \leq 2k < p \leq p^j$. So $m+i = 0 \mod p^j$ implies $m = -i \mod p^j$.
        have h_mod : m % p ^ j = p ^ j - i := by
          have h_mod : m % p ^ j = (p ^ j - i) % p ^ j := by
            refine Nat.modEq_of_dvd ?_;
            obtain ⟨ a, ha ⟩ := h_div; use -a + 1; rw [ Nat.cast_sub ( show i ≤ p ^ j from _ ) ] ; push_cast; linarith;
            contrapose! ha;
            rcases a with ( _ | _ | a ) <;> norm_num at * <;> nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_le_pow_right₀ ( show 1 ≤ p by exact Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) ( show j ≥ 1 from Nat.pos_of_ne_zero ( by aesop ) ) ];
          rw [ h_mod, Nat.mod_eq_of_lt ( Nat.sub_lt ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) ( Finset.mem_Icc.mp hi₁ |>.1 ) ) ];
        -- By `lemma_carry_prop`, `v_p(binom(2m, m)) >= j`.
        have h_vp_binom : padicValNat p (Nat.choose (2 * m) m) ≥ j := by
          apply lemma_carry_prop;
          exacts [ Finset.mem_Icc.mp hi₁ |>.1, by linarith [ Finset.mem_Icc.mp hi₁ |>.2 ], h_mod ];
        grind;
      · rw [ padicValNat.eq_zero_of_not_dvd ] ; aesop;
        rw [ Nat.descFactorial_eq_prod_range ];
        simp_all +decide [ Nat.Prime.dvd_iff_not_coprime Fact.out, Nat.coprime_prod_right_iff ];
        exact fun x hx => h_mult ( k - x ) ( Nat.sub_pos_of_lt hx ) ( Nat.sub_le _ _ ) |> fun h => by simpa [ Nat.add_sub_assoc hx.le ] using h;

/-
The inequality holds for sufficiently large m.
-/
theorem inequality_eventually_holds :
    ∀ᶠ m in Filter.atTop, ∀ k ∈ Finset.Icc 1 (K_max m), ∀ p ∈ Finset.range (2 * k + 1), p.Prime →
      (k : ℝ) / (p - 1) + 3 * Real.log k / Real.log p ≤ 0.49 * Real.log m / Real.log p := by
        -- For sufficiently large $m$, the inequality $k \log 2 + 3 \log k \leq 0.49 \log m$ holds.
        have h_ineq : ∀ᶠ m in Filter.atTop, ∀ k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)), k * Real.log 2 + 3 * Real.log k ≤ 0.49 * Real.log m := by
          -- We'll use the fact that $k \leq 0.7 \log m$ to bound the terms involving $k$.
          have h_bound : ∀ᶠ m in Filter.atTop, ∀ k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)), k * Real.log 2 + 3 * Real.log (0.7 * Real.log m) ≤ 0.49 * Real.log m := by
            have h_bound : ∀ᶠ m in Filter.atTop, 0.7 * Real.log m * Real.log 2 + 3 * Real.log (0.7 * Real.log m) ≤ 0.49 * Real.log m := by
              have h_log_growth : Filter.Tendsto (fun m : ℝ => (0.7 * Real.log m * Real.log 2 + 3 * Real.log (0.7 * Real.log m)) / Real.log m) Filter.atTop (nhds ((0.7 * Real.log 2) + 0)) := by
                -- We can use the fact that $\log(ab) = \log(a) + \log(b)$ to simplify the expression.
                suffices h_log_simplified : Filter.Tendsto (fun m : ℝ => (0.7 * Real.log 2 + 3 * (Real.log 0.7 + Real.log (Real.log m)) / Real.log m)) Filter.atTop (nhds (0.7 * Real.log 2 + 0)) by
                  refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with m hm using by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt <| Real.log_pos hm ) ] ; ring_nf; norm_num [ ne_of_gt, Real.log_pos hm ] );
                -- We'll use the fact that $\frac{\log(\log m)}{\log m}$ tends to $0$ as $m$ tends to infinity.
                have h_log_log : Filter.Tendsto (fun m : ℝ => Real.log (Real.log m) / Real.log m) Filter.atTop (nhds 0) := by
                  -- Let $y = \log m$, therefore the limit becomes $\lim_{y \to \infty} \frac{\log y}{y}$.
                  suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
                    exact h_log_y.comp ( Real.tendsto_log_atTop );
                  -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
                  suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
                    exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
                  norm_num;
                  exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
                ring_nf;
                simpa using Filter.Tendsto.add ( tendsto_const_nhds.add ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ) ( h_log_log.mul_const 3 )
              have h_log_growth : ∀ᶠ m in Filter.atTop, (0.7 * Real.log m * Real.log 2 + 3 * Real.log (0.7 * Real.log m)) / Real.log m < 0.49 := by
                have := h_log_growth.eventually ( gt_mem_nhds <| show 0.7 * Real.log 2 + 0 < 0.49 by have := Real.log_two_lt_d9; norm_num1 at *; linarith ) ; aesop;
              filter_upwards [ h_log_growth, Filter.eventually_gt_atTop 1 ] with m hm₁ hm₂ using by rw [ div_lt_iff₀ ( Real.log_pos hm₂ ) ] at hm₁; linarith;
            filter_upwards [ h_bound, Filter.eventually_gt_atTop 1 ] with m hm₁ hm₂ using fun k hk => le_trans ( add_le_add_right ( mul_le_mul_of_nonneg_right ( show ( k : ℝ ) ≤ 0.7 * Real.log m by exact le_trans ( Nat.cast_le.2 <| Finset.mem_Icc.1 hk |>.2 ) <| mod_cast Nat.floor_le <| mul_nonneg ( by norm_num ) <| Real.log_nonneg <| by linarith ) <| Real.log_nonneg <| by norm_num ) _ ) hm₁;
          filter_upwards [ h_bound, Filter.eventually_gt_atTop 1 ] with m hm₁ hm₂;
          exact fun k hk => le_trans ( add_le_add_left ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hk |>.1 ) <| Nat.floor_le ( mul_nonneg ( by norm_num ) <| Real.log_nonneg hm₂.le ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hk |>.2 ) ) <| by norm_num ) _ ) ( hm₁ k hk );
        filter_upwards [ h_ineq, Filter.eventually_gt_atTop 1 ] with m hm₁ hm₂;
        intro k hk p hp hp_prime
        have h_ineq : k * Real.log p / (p - 1) + 3 * Real.log k ≤ 0.49 * Real.log m := by
          have h_ineq : k * Real.log p / (p - 1) ≤ k * Real.log 2 := by
            rw [ div_le_iff₀ ] <;> norm_num;
            · have h_ineq : Real.log p ≤ Real.log 2 * (p - 1) := by
                rcases p with ( _ | _ | p ) <;> norm_num at *;
                rw [ Real.log_le_iff_le_exp ( by positivity ) ];
                rw [ Real.exp_mul, Real.exp_log ] <;> norm_cast;
                exact Nat.recOn p ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at ihn ⊢ ; linarith;
              simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left h_ineq <| Nat.cast_nonneg _;
            · exact hp_prime.one_lt;
          exact add_le_of_add_le_right (hm₁ k hk) h_ineq;
        convert div_le_div_of_nonneg_right h_ineq ( Real.log_nonneg <| Nat.one_le_cast.mpr hp_prime.pos ) using 1 ; ring_nf;
        norm_num [ ne_of_gt, Real.log_pos, hp_prime.one_lt ]

/-
The inequality holds uniformly for m close to x.
-/
theorem inequality_eventually_holds_uniform :
    ∀ᶠ x in Filter.atTop, ∀ m ∈ Finset.Icc (Nat.ceil (x / Real.log x)) (Nat.floor x),
      ∀ k ∈ Finset.Icc 1 (K_max m), ∀ p ∈ Finset.range (2 * k + 1), p.Prime →
        (k : ℝ) / (p - 1) + 3 * Real.log (K_max x) / Real.log p ≤ 0.49 * Real.log m / Real.log p := by
          have h_ineq : ∀ᶠ x in Filter.atTop, ∀ m ∈ Finset.Icc (Nat.ceil (x / Real.log x)) (Nat.floor x), ∀ k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log x)), ∀ p ∈ Finset.range (2 * k + 1), p.Prime → (k : ℝ) / (p - 1) + 3 * Real.log (Nat.floor (0.7 * Real.log x)) / Real.log p ≤ 0.49 * Real.log m / Real.log p := by
            have h_ineq : ∀ᶠ x in Filter.atTop, ∀ m ∈ Finset.Icc (Nat.ceil (x / Real.log x)) (Nat.floor x), ∀ k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log x)), k * Real.log 2 + 3 * Real.log (Nat.floor (0.7 * Real.log x)) ≤ 0.49 * Real.log m := by
              have h_ineq : ∀ᶠ x in Filter.atTop, ∀ m ∈ Finset.Icc (Nat.ceil (x / Real.log x)) (Nat.floor x), 0.7 * Real.log x * Real.log 2 + 3 * Real.log (0.7 * Real.log x) ≤ 0.49 * Real.log m := by
                have h_ineq : ∀ᶠ x in Filter.atTop, 0.7 * Real.log x * Real.log 2 + 3 * Real.log (0.7 * Real.log x) ≤ 0.49 * (Real.log x - Real.log (Real.log x)) := by
                  -- We can divide both sides by $\log x$ (which is positive for $x > 1$) to simplify the inequality.
                  suffices h_div : ∀ᶠ x in Filter.atTop, 0.7 * Real.log 2 + 3 * (Real.log (0.7) + Real.log (Real.log x)) / Real.log x ≤ 0.49 * (1 - Real.log (Real.log x) / Real.log x) by
                    filter_upwards [ h_div, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.log_pos hx₂ ) ) ] ; nlinarith [ Real.log_pos hx₂, mul_div_cancel₀ ( 3 * ( Real.log 0.7 + Real.log ( Real.log x ) ) ) ( ne_of_gt ( Real.log_pos hx₂ ) ), mul_div_cancel₀ ( Real.log ( Real.log x ) ) ( ne_of_gt ( Real.log_pos hx₂ ) ) ] ;
                  -- As $x \to \infty$, $\frac{\log(\log x)}{\log x} \to 0$.
                  have h_log_log_x : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
                    -- Let $y = \log x$, therefore the expression becomes $\frac{\log y}{y}$.
                    suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
                      exact h_log_y.comp ( Real.tendsto_log_atTop );
                    -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} z \log(1/z)$.
                    suffices h_log_recip : Filter.Tendsto (fun z : ℝ => z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
                      exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
                    norm_num +zetaDelta at *;
                    exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
                  have h_log_log_x : Filter.Tendsto (fun x : ℝ => 0.7 * Real.log 2 + 3 * (Real.log 0.7 + Real.log (Real.log x)) / Real.log x) Filter.atTop (nhds (0.7 * Real.log 2 + 3 * 0)) := by
                    ring_nf;
                    simpa using Filter.Tendsto.add ( tendsto_const_nhds.add ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) tendsto_const_nhds ) ) ( h_log_log_x.mul_const 3 );
                  have h_log_log_x : Filter.Tendsto (fun x : ℝ => 0.49 * (1 - Real.log (Real.log x) / Real.log x)) Filter.atTop (nhds (0.49 * (1 - 0))) := by
                    exact tendsto_const_nhds.mul ( tendsto_const_nhds.sub ‹_› );
                  have := h_log_log_x.sub ‹Filter.Tendsto ( fun x : ℝ => 0.7 * log 2 + 3 * ( log 0.7 + log ( log x ) ) / log x ) Filter.atTop ( nhds ( 0.7 * log 2 + 3 * 0 ) ) ›; norm_num at *;
                  exact Filter.eventually_atTop.mp ( this.eventually ( lt_mem_nhds ( show 49 / 100 - 7 / 10 * log 2 > 0 by have := Real.log_two_lt_d9; norm_num1 at *; linarith ) ) ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun x hx => by linarith [ hN x hx ] ⟩;
                filter_upwards [ h_ineq, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
                intro m hm
                have hm_log : Real.log m ≥ Real.log x - Real.log (Real.log x) := by
                  rw [ ← Real.log_div ( by linarith ) ( ne_of_gt ( Real.log_pos hx₂ ) ) ];
                  exact Real.log_le_log ( div_pos ( by positivity ) ( Real.log_pos hx₂ ) ) ( Nat.le_of_ceil_le ( Finset.mem_Icc.mp hm |>.1 ) );
                linarith;
              filter_upwards [ h_ineq, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
              intros m hm k hk;
              refine le_trans ?_ ( hx₁ m hm );
              gcongr <;> norm_num at *;
              · exact le_trans ( Nat.cast_le.mpr hk.2 ) ( Nat.floor_le ( by linarith [ Real.log_nonneg hx₂.le ] ) );
              · linarith;
              · exact Nat.floor_le ( by linarith [ Real.log_pos hx₂ ] );
            filter_upwards [ h_ineq ] with x hx m hm k hk p hp hp_prime;
            have h_log_p : k * Real.log p / (p - 1) + 3 * Real.log (Nat.floor (0.7 * Real.log x)) ≤ 0.49 * Real.log m := by
              have h_log_p : k * Real.log p / (p - 1) ≤ k * Real.log 2 := by
                rw [ div_le_iff₀ ] <;> norm_num;
                · rw [ mul_assoc ] ; gcongr;
                  rw [ mul_comm, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_num <;> try linarith [ hp_prime.two_le ];
                  · rcases p with ( _ | _ | p ) <;> norm_num at *;
                    exact mod_cast Nat.recOn p ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith;
                  · positivity;
                · exact hp_prime.one_lt;
              linarith [ hx m hm k hk ];
            rw [ add_div', div_le_div_iff_of_pos_right ];
            · convert h_log_p using 1 ; ring;
            · exact Real.log_pos ( Nat.one_lt_cast.mpr hp_prime.one_lt );
            · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hp_prime.one_lt;
          filter_upwards [ h_ineq, Filter.eventually_ge_atTop 3 ] with x hx₁ hx₂;
          intro m hm k hk p hp hp_prime
          have hk_le : k ≤ Nat.floor (0.7 * Real.log x) := by
            have hk_le : Real.log m ≤ Real.log x := by
              exact Real.log_le_log ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hm |>.1.trans_lt' <| Nat.ceil_pos.mpr <| div_pos ( by positivity ) <| Real.log_pos <| by linarith ) <| Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hm |>.2 );
            exact le_trans ( Finset.mem_Icc.mp hk |>.2 ) ( Nat.floor_mono <| mul_le_mul_of_nonneg_left hk_le <| by norm_num );
          convert hx₁ m hm k ( Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hk |>.1, hk_le ⟩ ) p hp hp_prime using 1

/-
If m is not in the bad set, the valuation is bounded.
-/
theorem bound_from_not_bad (x : ℝ) (m : ℕ) (p : ℕ) (i : ℕ) [Fact p.Prime]
    (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (h_not_bad : m ∉ bad_set_lemma_2_2_v3 x)
    (hp : p ∈ Finset.range (2 * K_max x + 1))
    (hi : i ∈ Finset.Icc 1 (K_max x)) :
    (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max x) / Real.log p := by
      -- Since $m$ is not in the bad set, by definition, there are no $p$ and $i$ such that $v_p(m+i) > 3 * \log(K_{\text{max}} x) / \log(p)$.
      have h_not_bad_def : ¬∃ p ∈ Finset.range (2 * K_max x + 1), p.Prime ∧ ∃ i ∈ Finset.Icc 1 (K_max x), (padicValNat p (m + i) : ℝ) > 3 * Real.log (K_max x) / Real.log p := by
        unfold bad_set_lemma_2_2_v3 at h_not_bad; aesop;
      exact le_of_not_gt fun h => h_not_bad_def ⟨ p, hp, Fact.out, i, hi, h ⟩

/-
If m is not in the bad set, the valuation of the descending factorial is bounded.
-/
theorem valuation_bound_small_p (x : ℝ) (m k p : ℕ) [Fact p.Prime] (hx : x ≥ 3) (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hk : k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)))
    (hp : p ∈ Finset.range (2 * k + 1))
    (h_not_bad_2_2 : m ∉ bad_set_lemma_2_2_v3 x) :
    (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) < (k : ℝ) / (p - 1) + 3 * Real.log (K_max x) / Real.log p := by
      -- By Lemma 3.3, we have $v_p(\text{descFact}) \leq v_p(\binom{m+k}{k}) + v_p(k!)$.
      have h_val_descFact : (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) ≤ (padicValNat p (Nat.choose (m + k) k) : ℝ) + (padicValNat p (Nat.factorial k) : ℝ) := by
        have h_max_val : (Nat.descFactorial (m + k) k : ℕ) = (Nat.choose (m + k) k : ℕ) * (Nat.factorial k : ℕ) := by
          rw [ Nat.descFactorial_eq_factorial_mul_choose, mul_comm ];
        rw [ h_max_val, padicValNat.mul ] <;> aesop;
      -- By Lemma 3.3, we have $v_p(\binom{m+k}{k}) \leq \max_{1 \leq i \leq k} v_p(m+i)$.
      have h_val_binom : (padicValNat p (Nat.choose (m + k) k) : ℝ) ≤ 3 * Real.log (K_max x) / Real.log p := by
        -- By Lemma 3.3, we have $v_p(\binom{m+k}{k}) \leq \max_{1 \leq i \leq k} v_p(m+i)$ for $p \leq 2k$ and $m \notin \text{bad\_set\_lemma\_2\_2\_v3}$.
        have h_val_binom_le_max : ∀ i ∈ Finset.Icc 1 k, (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max x) / Real.log p := by
          intros i hi
          have h_not_bad_i : m ∉ bad_set_lemma_2_2_v3 x := by
            assumption;
          apply bound_from_not_bad x m p i hm h_not_bad_i (by
          norm_num at *;
          refine' lt_of_lt_of_le hp _;
          refine' Nat.succ_le_succ ( Nat.mul_le_mul_left 2 _ );
          refine' hk.2.trans ( Nat.floor_mono _ );
          norm_num; linarith [ Real.log_le_log ( by norm_cast; linarith ) ( show ( m : ℝ ) ≤ x by exact le_trans ( Nat.cast_le.mpr hm.2 ) ( Nat.floor_le ( by positivity ) ) ) ] ;) (by
          have h_k_le_K_max : k ≤ K_max x := by
            norm_num +zetaDelta at *;
            refine' hk.2.trans ( Nat.floor_mono _ );
            norm_num; linarith [ Real.log_le_log ( by norm_cast; linarith ) ( show ( m : ℝ ) ≤ x by exact le_trans ( Nat.cast_le.mpr hm.2 ) ( Nat.floor_le ( by positivity ) ) ) ] ;
          exact Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hi |>.1, le_trans ( Finset.mem_Icc.mp hi |>.2 ) h_k_le_K_max ⟩);
        have h_val_binom_le_max : (padicValNat p (Nat.choose (m + k) k) : ℝ) ≤ Finset.sup' (Finset.Icc 1 k) (by
        exact Finset.nonempty_Icc.mpr ( by linarith [ Finset.mem_Icc.mp hk ] )) (fun i => (padicValNat p (m + i) : ℝ)) := by
          have := lemma_3_3 m k p (by
          norm_num +zetaDelta at *;
          rw [ Nat.le_floor_iff ( by positivity ) ] at hk;
          rcases m with ( _ | _ | m ) <;> norm_num at *;
          · linarith;
          · exact_mod_cast ( by nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < ( m : ℝ ) + 1 + 1 ) ] : ( k : ℝ ) < m + 1 + 1 )) (by
          linarith [ Finset.mem_Icc.mp hk ])
          generalize_proofs at *;
          exact_mod_cast le_trans this ( Finset.sup_le fun i hi => Finset.le_sup' ( fun i => padicValNat p ( m + i ) ) hi )
        generalize_proofs at *;
        exact h_val_binom_le_max.trans ( Finset.sup'_le _ _ fun i hi => by solve_by_elim );
      -- By Lemma 3.3, we have $v_p(k!) < \frac{k}{p-1}$.
      have h_val_factorial : (padicValNat p (Nat.factorial k) : ℝ) < k / (p - 1) := by
        convert legendre_bound_strict k p _ using 1;
        linarith [ Finset.mem_Icc.mp hk ];
      linarith

/-
If m is not in the bad set, the valuation of the descending factorial is bounded.
-/
theorem valuation_bound_small_p_v2 (x : ℝ) (m k p : ℕ) [Fact p.Prime] (hx : x ≥ 3) (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hk : k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)))
    (hp : p ∈ Finset.range (2 * k + 1))
    (h_not_bad_2_2 : m ∉ bad_set_lemma_2_2_v3 x) :
    (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) < (k : ℝ) / (p - 1) + 3 * Real.log (K_max x) / Real.log p := by
      convert valuation_bound_small_p x m k p hx hm hk hp h_not_bad_2_2 using 1

/-
If m is not in the bad set, the valuation of the descending factorial is bounded.
-/
theorem valuation_bound_small_p_v3 (x : ℝ) (m k p : ℕ) [Fact p.Prime] (hx : x ≥ 3) (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hk : k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)))
    (hp : p ∈ Finset.range (2 * k + 1))
    (h_not_bad_2_2 : m ∉ bad_set_lemma_2_2_v3 x) :
    (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) < (k : ℝ) / (p - 1) + 3 * Real.log (K_max x) / Real.log p := by
      exact valuation_bound_small_p x m k p hx hm hk hp h_not_bad_2_2

/-
If m is not in the bad set, the valuation of the descending factorial is bounded.
-/
theorem valuation_bound_small_p_v4 (x : ℝ) (m k p : ℕ) [Fact p.Prime] (hx : x ≥ 3) (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hk : k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)))
    (hp : p ∈ Finset.range (2 * k + 1))
    (h_not_bad_2_2 : m ∉ bad_set_lemma_2_2_v3 x) :
    (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) < (k : ℝ) / (p - 1) + 3 * Real.log (K_max x) / Real.log p := by
      exact valuation_bound_small_p_v3 x m k p hx hm hk hp h_not_bad_2_2

/-
The inequality required for the main theorem holds for sufficiently large m.
-/
theorem inequality_eventually_holds_v2 :
    ∀ᶠ m in Filter.atTop, ∀ k ∈ Finset.Icc 1 (K_max m), ∀ p ∈ Finset.range (2 * k + 1), p.Prime →
      (k : ℝ) / (p - 1) + 3 * Real.log (K_max m) / Real.log p ≤ 0.49 * Real.log m / Real.log p := by
        simp +zetaDelta at *;
        have := inequality_eventually_holds;
        obtain ⟨ m, hm ⟩ := Filter.eventually_atTop.mp this;
        use Max.max m 3;
        intros b hb k hk₁ hk₂ p hp₁ hp₂;
        refine' le_trans _ ( hm b ( le_trans ( le_max_left _ _ ) hb ) ( K_max b ) ( Finset.mem_Icc.mpr ⟨ _, le_rfl ⟩ ) p ( Finset.mem_range.mpr ( by linarith ) ) hp₂ );
        · gcongr ; norm_cast;
          rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith [ hp₂.two_le ];
        · exact le_trans hk₁ hk₂

/-
The size of the bad set with fixed parameters is bounded by the sum of bounds for each condition.
-/
noncomputable def bad_set_fixed_param (x : ℝ) (K : ℕ) (L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * L + 1), p.Prime ∧
      ∃ i ∈ Finset.Icc 1 L, (padicValNat p (m + i) : ℝ) > 3 * Real.log K / Real.log p)

theorem bad_set_fixed_param_bound (x : ℝ) (K L : ℕ) (hx : x ≥ 1) (hK : K ≥ 2) :
    ((bad_set_fixed_param x K L).card : ℝ) ≤
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * L + 1)),
      ∑ i ∈ Finset.Icc 1 L, (x / (K : ℝ)^3 + 1) := by
        -- For each prime $p$ and each $i \in \{1, \ldots, L\}$, the number of $m \leq x$ such that $m + i$ is divisible by $p^E$ is at most $x / p^E + 1$.
        have h_tile_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * L + 1)), ∀ i ∈ Finset.Icc 1 L, ((Finset.Icc 1 (Nat.floor x)).filter (fun m => p.Prime ∧ m + i ≡ 0 [MOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)])).card ≤ x / (p : ℝ) ^ (Nat.floor (3 * Real.log K / Real.log p) + 1) + 1 := by
          -- The set of $m$ such that $m + i$ is divisible by $p^E$ is an arithmetic progression with common difference $p^E$.
          intro p hp i hi
          have h_arith_prog : Finset.card (Finset.filter (fun m => Nat.Prime p ∧ m + i ≡ 0 [MOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)]) (Finset.Icc 1 (Nat.floor x))) ≤ Finset.card (Finset.filter (fun m => m ≡ -i [ZMOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)]) (Finset.Icc 1 (Nat.floor x))) := by
            have h_arith_prog : Finset.filter (fun m => Nat.Prime p ∧ m + i ≡ 0 [MOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)]) (Finset.Icc 1 (Nat.floor x)) ⊆ Finset.image (fun m : ℤ => m.toNat) (Finset.filter (fun m => m ≡ -i [ZMOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)]) (Finset.Icc 1 (Nat.floor x))) := by
              simp +decide [ Finset.subset_iff, ← Int.natCast_modEq_iff ];
              exact fun m hm₁ hm₂ hm₃ hm₄ => ⟨ m, ⟨ ⟨ mod_cast hm₁, mod_cast hm₂ ⟩, by simpa [ Int.modEq_iff_dvd ] using hm₄ ⟩, rfl ⟩;
            exact le_trans ( Finset.card_le_card h_arith_prog ) ( Finset.card_image_le );
          -- The number of elements in an arithmetic progression with common difference $d$ and length $n$ is at most $n/d + 1$.
          have h_arith_prog_card : Finset.card (Finset.filter (fun m : ℤ => m ≡ -i [ZMOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)]) (Finset.Icc 1 (Nat.floor x))) ≤ (Nat.floor x) / (p^(Nat.floor (3 * Real.log K / Real.log p) + 1)) + 1 := by
            have h_arith_prog_card : Finset.card (Finset.filter (fun m : ℤ => m ≡ -i [ZMOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)]) (Finset.Icc 1 (Nat.floor x))) ≤ Finset.card (Finset.image (fun m : ℤ => m * p^(Nat.floor (3 * Real.log K / Real.log p) + 1) + (-i % p^(Nat.floor (3 * Real.log K / Real.log p) + 1))) (Finset.Icc 0 ((Nat.floor x) / p^(Nat.floor (3 * Real.log K / Real.log p) + 1)))) := by
              refine Finset.card_le_card ?_;
              intro m hm; simp_all +decide [ Int.ModEq ] ;
              refine' ⟨ m / p ^ ( ⌊3 * Real.log K / Real.log p⌋₊ + 1 ), ⟨ Int.ediv_nonneg ( by linarith ) ( by exact pow_nonneg ( Nat.cast_nonneg _ ) _ ), Int.le_ediv_of_mul_le ( pow_pos ( Nat.cast_pos.mpr hp.2.pos ) _ ) ( by linarith [ Int.emod_add_mul_ediv m ( p ^ ( ⌊3 * Real.log K / Real.log p⌋₊ + 1 ) ), Int.emod_nonneg m ( pow_ne_zero ( ⌊3 * Real.log K / Real.log p⌋₊ + 1 ) ( Nat.cast_ne_zero.mpr hp.2.ne_zero ) ), Int.emod_lt_of_pos m ( pow_pos ( Nat.cast_pos.mpr hp.2.pos ) ( ⌊3 * Real.log K / Real.log p⌋₊ + 1 ) ) ] ) ⟩, _ ⟩ ; linarith [ Int.emod_add_mul_ediv m ( p ^ ( ⌊3 * Real.log K / Real.log p⌋₊ + 1 ) ), Int.emod_nonneg m ( pow_ne_zero ( ⌊3 * Real.log K / Real.log p⌋₊ + 1 ) ( Nat.cast_ne_zero.mpr hp.2.ne_zero ) ), Int.emod_lt_of_pos m ( pow_pos ( Nat.cast_pos.mpr hp.2.pos ) ( ⌊3 * Real.log K / Real.log p⌋₊ + 1 ) ) ];
            exact h_arith_prog_card.trans ( Finset.card_image_le.trans ( by norm_num ) );
          refine le_trans ( Nat.cast_le.mpr ( h_arith_prog.trans h_arith_prog_card ) ) ?_;
          norm_num +zetaDelta at *;
          rw [ le_div_iff₀ ( pow_pos ( Nat.cast_pos.mpr hp.2.pos ) _ ) ] ; exact le_trans ( mod_cast Nat.div_mul_le_self _ _ ) ( Nat.floor_le ( by positivity ) );
        -- The cardinality of the union of sets is less than or equal to the sum of their cardinalities.
        have h_union_bound : (bad_set_fixed_param x K L).card ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * L + 1)), ∑ i ∈ Finset.Icc 1 L, ((Finset.Icc 1 (Nat.floor x)).filter (fun m => p.Prime ∧ m + i ≡ 0 [MOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)])).card := by
          have h_union_bound : (bad_set_fixed_param x K L).card ≤ Finset.card (Finset.biUnion (Finset.filter Nat.Prime (Finset.range (2 * L + 1))) (fun p => Finset.biUnion (Finset.Icc 1 L) (fun i => (Finset.Icc 1 (Nat.floor x)).filter (fun m => p.Prime ∧ m + i ≡ 0 [MOD p^(Nat.floor (3 * Real.log K / Real.log p) + 1)])))) := by
            refine Finset.card_le_card ?_;
            unfold bad_set_fixed_param;
            simp +contextual [ Finset.subset_iff ];
            intro m hm₁ hm₂ p hp₁ hp₂ i hi₁ hi₂ hi₃; use p, ⟨ hp₁, hp₂ ⟩, i, ⟨ hi₁, hi₂ ⟩, hp₂; rw [ Nat.modEq_zero_iff_dvd ] ;
            refine' Nat.dvd_trans ( pow_dvd_pow _ ( Nat.succ_le_of_lt ( Nat.floor_lt ( by positivity ) |>.2 hi₃ ) ) ) _;
            exact pow_padicValNat_dvd;
          refine le_trans h_union_bound ?_;
          exact le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun p hp => Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun i hi => by aesop );
        refine le_trans ( Nat.cast_le.mpr h_union_bound ) ?_;
        -- Since $p \geq 2$, we have $p^{Nat.floor (3 * Real.log K / Real.log p) + 1} \geq K^3$.
        have h_prime_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * L + 1)), (p : ℝ) ^ (Nat.floor (3 * Real.log K / Real.log p) + 1) ≥ K ^ 3 := by
          intros p hp
          have h_exp : (Nat.floor (3 * Real.log K / Real.log p) + 1) * Real.log p ≥ 3 * Real.log K := by
            nlinarith [ Nat.lt_floor_add_one ( 3 * Real.log K / Real.log p ), show 0 < Real.log p from Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ), mul_div_cancel₀ ( 3 * Real.log K ) ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ) ];
          rw [ ge_iff_le, ← Real.log_le_log_iff ( by positivity ) ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) _ ), Real.log_pow ] ; aesop;
        push_cast;
        exact Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun i hi => le_trans ( h_tile_bound p hp i hi ) ( add_le_add_right ( div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( h_prime_bound p hp ) ) _ )

/-
The bad set is contained in the union of small m and the fixed parameter bad set.
-/
noncomputable def bad_set_lemma_2_2_intrinsic (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_max m + 1), p.Prime ∧
      ∃ i ∈ Finset.Icc 1 (K_max m), (padicValNat p (m + i) : ℝ) > 3 * Real.log (K_max m) / Real.log p)

noncomputable def K_lower (x : ℝ) : ℕ := K_max (x / Real.log x)

theorem bad_set_subset_lemma (x : ℝ) (hx : x ≥ 10) :
    bad_set_lemma_2_2_intrinsic x ⊆
    (Finset.Icc 1 (Nat.floor (x / Real.log x))) ∪
    bad_set_fixed_param x (K_lower x) (K_max x) := by
      apply Finset.subset_iff.mpr
      intro m hm
      by_cases hm_case : m ≤ x / Real.log x;
      · exact Finset.mem_union_left _ <| Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero <| by rintro rfl; exact absurd hm <| by unfold bad_set_lemma_2_2_intrinsic; aesop, Nat.le_floor <| mod_cast hm_case ⟩;
      · simp_all +decide [ bad_set_lemma_2_2_intrinsic, bad_set_fixed_param ];
        refine Or.inr ⟨ hm.2.choose, ?_, hm.2.choose_spec.2.1, ?_ ⟩;
        · refine lt_of_lt_of_le hm.2.choose_spec.1 ?_;
          unfold K_max; gcongr;
          · exact Nat.cast_pos.mpr hm.1.1;
          · exact Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hm.1.2 );
        · have h_i_bound : K_max m ≤ K_max x := by
            apply Nat.floor_mono;
            exact mul_le_mul_of_nonneg_left ( Real.log_le_log ( Nat.cast_pos.mpr hm.1.1 ) ( Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hm.1.2 ) ) ) ( by positivity );
          have h_i_bound : K_lower x ≤ K_max m := by
            refine' Nat.floor_mono _;
            exact mul_le_mul_of_nonneg_left ( Real.log_le_log ( div_pos ( by positivity ) ( Real.log_pos ( by linarith ) ) ) hm_case.le ) ( by positivity );
          have h_log_bound : Real.log (K_lower x) ≤ Real.log (K_max m) := by
            by_cases hK_lower_zero : K_lower x = 0;
            · norm_num [ hK_lower_zero ];
              exact Real.log_natCast_nonneg _;
            · exact Real.log_le_log ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hK_lower_zero ) ) ( Nat.cast_le.mpr h_i_bound );
          have := hm.2.choose_spec.2.2;
          obtain ⟨ i, hi₁, hi₂ ⟩ := this;
          exact ⟨ i, ⟨ hi₁.1, hi₁.2.trans ‹_› ⟩, lt_of_le_of_lt ( by gcongr ) hi₂ ⟩

/-
K_lower is asymptotically equivalent to 0.7 log x.
-/
theorem K_lower_asymptotics :
    Asymptotics.IsEquivalent Filter.atTop (fun x => (K_lower x : ℝ)) (fun x => 0.7 * Real.log x) := by
      -- We'll use the fact that $K_lower x = \lfloor 0.7 \log (x / \log x) \rfloor$.
      have h_K_lower : ∀ᶠ x in Filter.atTop, abs ((K_lower x : ℝ) - 0.7 * Real.log x) / (0.7 * Real.log x) ≤ (Real.log (Real.log x) / Real.log x + 1 / (0.7 * Real.log x)) := by
        -- We'll use the fact that $K_lower(x) = \lfloor 0.7 \log(x / \log x) \rfloor$.
        have h_K_lower_floor : ∀ᶠ x in Filter.atTop, abs ((K_lower x : ℝ) - 0.7 * Real.log (x / Real.log x)) ≤ 1 := by
          have h_K_lower_floor : ∀ᶠ x in Filter.atTop, abs ((Nat.floor (0.7 * Real.log (x / Real.log x)) : ℝ) - 0.7 * Real.log (x / Real.log x)) ≤ 1 := by
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using abs_sub_le_iff.mpr ⟨ by linarith [ Nat.floor_le ( show 0 ≤ 0.7 * Real.log ( x / Real.log x ) by exact mul_nonneg ( by norm_num ) ( Real.log_nonneg ( show x / Real.log x ≥ 1 by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ( Real.log_pos hx ) ] ; linarith [ Real.log_le_sub_one_of_pos ( zero_lt_one.trans hx ) ] ) ) ) ], by linarith [ Nat.lt_floor_add_one ( 0.7 * Real.log ( x / Real.log x ) ) ] ⟩;
          convert h_K_lower_floor using 1;
        filter_upwards [ h_K_lower_floor, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃;
        field_simp;
        gcongr;
        · exact Real.log_nonneg hx₂.le;
        · rw [ Real.log_div ( by linarith ) ( ne_of_gt ( Real.log_pos hx₂ ) ) ] at hx₁;
          exact abs_le.mpr ⟨ by linarith [ abs_le.mp hx₁, Real.log_nonneg ( show 1 ≤ log x from by rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.add_one_le_exp 1 ] ) ], by linarith [ abs_le.mp hx₁, Real.log_nonneg ( show 1 ≤ log x from by rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.add_one_le_exp 1 ] ) ] ⟩;
      -- We'll use the fact that $\frac{\log \log x}{\log x} \to 0$ and $\frac{1}{0.7 \log x} \to 0$ as $x \to \infty$.
      have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
        -- Let $y = \log x$, therefore the expression becomes $\frac{\log y}{y}$.
        suffices h_log_y : Filter.Tendsto (fun y => Real.log y / y) Filter.atTop (nhds 0) by
          exact h_log_y.comp ( Real.tendsto_log_atTop );
        -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} z \log(1/z)$.
        suffices h_log_recip : Filter.Tendsto (fun z => z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
          exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
        norm_num +zetaDelta at *;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 )
      have h_one_log : Filter.Tendsto (fun x => 1 / (0.7 * Real.log x)) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( Filter.Tendsto.const_mul_atTop ( by norm_num ) ( Real.tendsto_log_atTop ) );
      rw [ Asymptotics.IsEquivalent ];
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · refine' squeeze_zero_norm' _ ( by simpa using h_log_log.add h_one_log );
        simp +zetaDelta at *;
        exact ⟨ Max.max h_K_lower.choose 2, fun x hx => by simpa only [ abs_of_nonneg ( show ( 0.7 : ℝ ) ≥ 0 by norm_num ), abs_of_nonneg ( show ( 0 : ℝ ) ≤ log x by exact Real.log_nonneg ( by linarith [ le_max_right h_K_lower.choose 2 ] ) ) ] using h_K_lower.choose_spec x ( le_trans ( le_max_left _ _ ) hx ) ⟩;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx hx' using absurd hx' <| ne_of_gt <| mul_pos ( by norm_num ) <| Real.log_pos hx

/-
The explicit bound function is o(x).
-/
noncomputable def explicit_bound_lemma_2_2 (x : ℝ) : ℝ :=
  (Nat.floor (x / Real.log x) : ℝ) +
  (2 * K_max x + 1) * (K_max x) * (x / (K_lower x : ℝ)^3 + 1)

theorem explicit_bound_is_little_o :
    explicit_bound_lemma_2_2 =o[Filter.atTop] (fun x => x) := by
      -- We'll use the fact that if the denominator grows faster than the numerator, the quotient tends to zero.
      have h_tendsto_zero : Filter.Tendsto (fun x => (explicit_bound_lemma_2_2 x : ℝ) / x) Filter.atTop (nhds 0) := by
        unfold explicit_bound_lemma_2_2;
        -- We'll use the fact that $K_{\text{lower}}(x) \sim 0.7 \log x$ and $K_{\text{max}}(x) \sim 0.7 \log x$ as $x \to \infty$.
        have h_asymptotic : Filter.Tendsto (fun x => (K_lower x : ℝ) / Real.log x) Filter.atTop (nhds 0.7) ∧ Filter.Tendsto (fun x => (K_max x : ℝ) / Real.log x) Filter.atTop (nhds 0.7) := by
          have h_asymptotic : Filter.Tendsto (fun x => (K_lower x : ℝ) / Real.log x) Filter.atTop (nhds 0.7) := by
            have := K_lower_asymptotics;
            rw [ Asymptotics.IsEquivalent ] at this;
            rw [ Asymptotics.isLittleO_iff_tendsto' ] at this <;> norm_num at *;
            · have := this.const_mul ( 7 / 10 ) |> Filter.Tendsto.add_const ( 7 / 10 : ℝ );
              simpa using this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_div, div_add', div_eq_div_iff ] <;> ring_nf <;> nlinarith [ Real.log_pos hx ] );
            · exact ⟨ 2, fun x hx hx' => by rcases hx' with ( rfl | rfl | hx' ) <;> linarith ⟩;
          have h_asymptotic_max : Filter.Tendsto (fun x => (Nat.floor (0.7 * Real.log x) : ℝ) / Real.log x) Filter.atTop (nhds 0.7) := by
            refine' ( Metric.tendsto_nhds.mpr _ );
            intro ε hε; refine' Filter.eventually_atTop.mpr ⟨ Real.exp ( ε⁻¹ * 10 ), fun x hx => abs_lt.mpr ⟨ _, _ ⟩ ⟩ <;> nlinarith [ Nat.floor_le ( show 0 ≤ 0.7 * Real.log x by exact mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith [ Real.add_one_le_exp ( ε⁻¹ * 10 ), inv_pos.mpr hε ] ) ) ), Nat.lt_floor_add_one ( 0.7 * Real.log x ), Real.log_exp ( ε⁻¹ * 10 ), Real.log_le_log ( by positivity ) hx, mul_inv_cancel₀ ( ne_of_gt hε ), div_mul_cancel₀ ( Nat.floor ( 0.7 * Real.log x ) : ℝ ) ( show Real.log x ≠ 0 from ne_of_gt <| Real.log_pos <| by linarith [ Real.add_one_le_exp ( ε⁻¹ * 10 ), inv_pos.mpr hε ] ) ] ;
          exact ⟨ h_asymptotic, h_asymptotic_max ⟩;
        -- We'll use the fact that $K_{\text{lower}}(x) \sim 0.7 \log x$ and $K_{\text{max}}(x) \sim 0.7 \log x$ as $x \to \infty$ to simplify the expression.
        have h_simplify : Filter.Tendsto (fun x => (2 * (K_max x : ℝ) + 1) * (K_max x : ℝ) / (K_lower x : ℝ) ^ 3) Filter.atTop (nhds 0) := by
          have h_simplify : Filter.Tendsto (fun x => ((2 * (K_max x : ℝ) + 1) * (K_max x : ℝ)) / (Real.log x)^3) Filter.atTop (nhds 0) := by
            have h_simplify : Filter.Tendsto (fun x => ((2 * (K_max x : ℝ) + 1) / Real.log x) * ((K_max x : ℝ) / Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
              have h_simplify : Filter.Tendsto (fun x => ((2 * (K_max x : ℝ) + 1) / Real.log x)) Filter.atTop (nhds (2 * 0.7)) := by
                simpa [ add_div, mul_div_assoc ] using Filter.Tendsto.add ( h_asymptotic.2.const_mul 2 ) ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) );
              simpa using Filter.Tendsto.div_atTop ( h_simplify.mul h_asymptotic.2 ) ( Real.tendsto_log_atTop );
            exact h_simplify.congr fun x => by ring;
          have h_simplify : Filter.Tendsto (fun x => ((2 * (K_max x : ℝ) + 1) * (K_max x : ℝ)) / (Real.log x)^3 * ((Real.log x)^3 / (K_lower x : ℝ)^3)) Filter.atTop (nhds 0) := by
            convert h_simplify.mul ( h_asymptotic.1.inv₀ _ |> Filter.Tendsto.pow <| 3 ) using 2 <;> norm_num;
            exact Or.inl <| by ring;
          refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ div_mul_div_cancel₀ ( pow_ne_zero _ <| ne_of_gt <| Real.log_pos hx ) ] );
        -- We'll use the fact that $⌊x / log x⌋₊ / x$ tends to $0$ as $x$ tends to infinity.
        have h_floor : Filter.Tendsto (fun x => (Nat.floor (x / Real.log x) : ℝ) / x) Filter.atTop (nhds 0) := by
          -- We'll use the fact that $\frac{\lfloor x / \log x \rfloor}{x} \leq \frac{x / \log x}{x} = \frac{1}{\log x}$.
          have h_floor_le : ∀ x : ℝ, x ≥ 2 → (Nat.floor (x / Real.log x) : ℝ) / x ≤ 1 / Real.log x := by
            intro x hx; rw [ div_le_div_iff₀ ] <;> nlinarith [ Nat.floor_le ( show 0 ≤ x / Real.log x by exact div_nonneg ( by linarith ) ( Real.log_nonneg ( by linarith ) ) ), Real.log_pos ( by linarith : 1 < x ), mul_div_cancel₀ x ( ne_of_gt ( Real.log_pos ( by linarith : 1 < x ) ) ) ] ;
          exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, fun x hx => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_floor_le x hx ⟩ ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) );
        -- We can split the limit into two parts and apply the fact that the sum of limits holds.
        have h_split : Filter.Tendsto (fun x => (Nat.floor (x / Real.log x) : ℝ) / x + (2 * (K_max x : ℝ) + 1) * (K_max x : ℝ) / (K_lower x : ℝ) ^ 3 * (x / x) + (2 * (K_max x : ℝ) + 1) * (K_max x : ℝ) / x) Filter.atTop (nhds 0) := by
          have h_split : Filter.Tendsto (fun x => (2 * (K_max x : ℝ) + 1) * (K_max x : ℝ) / x) Filter.atTop (nhds 0) := by
            have h_split : Filter.Tendsto (fun x => (2 * (K_max x : ℝ) + 1) * (K_max x : ℝ) / Real.log x ^ 2 * (Real.log x ^ 2 / x)) Filter.atTop (nhds 0) := by
              have h_split : Filter.Tendsto (fun x => (2 * (K_max x : ℝ) + 1) * (K_max x : ℝ) / Real.log x ^ 2) Filter.atTop (nhds (2 * 0.7 ^ 2)) := by
                convert Filter.Tendsto.mul ( Filter.Tendsto.add ( h_asymptotic.2.const_mul 2 ) ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) h_asymptotic.2 using 2 <;> ring_nf;
                norm_num ; ring;
              convert h_split.mul ( show Filter.Tendsto ( fun x : ℝ => Real.log x ^ 2 / x ) Filter.atTop ( nhds 0 ) from ?_ ) using 2 <;> norm_num;
              -- Let $y = \log x$, therefore the expression becomes $\frac{y^2}{e^y}$.
              suffices h_log : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp y) Filter.atTop (nhds 0) by
                have := h_log.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
              simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
            refine h_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ div_mul_div_cancel₀ ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos hx ) ) ) ] );
          simpa using Filter.Tendsto.add ( Filter.Tendsto.add h_floor ( h_simplify.mul ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with x hx; aesop ) ) ) ) h_split;
        grind;
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · convert h_tendsto_zero using 1;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using False.elim <| hx.ne' hx'

/-
K_lower is eventually at least 2.
-/
theorem K_lower_ge_two : ∀ᶠ x in Filter.atTop, K_lower x ≥ 2 := by
  -- We'll use that $Real.log (x / Real.log x)$ grows without bound as $x$ tends to infinity.
  have h_log_growth : Filter.Tendsto (fun x : ℝ => Real.log (x / Real.log x)) Filter.atTop Filter.atTop := by
    refine Real.tendsto_log_atTop.comp ?_;
    -- We can use the change of variables $u = \log x$ to transform the limit expression.
    suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
      have := h_log.comp Real.tendsto_log_atTop;
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
    simpa using Real.tendsto_exp_div_pow_atTop 1;
  filter_upwards [ h_log_growth.eventually_gt_atTop 20, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using Nat.le_floor <| by norm_num; nlinarith [ Real.log_le_sub_one_of_pos <| show 0 < x / Real.log x from div_pos ( by linarith ) <| Real.log_pos <| by linarith ] ;

/-
The cardinality of the bad set is eventually bounded by the explicit bound function.
-/
theorem bad_set_lemma_2_2_intrinsic_card_le_explicit_bound :
    ∀ᶠ x in Filter.atTop, ((bad_set_lemma_2_2_intrinsic x).card : ℝ) ≤ explicit_bound_lemma_2_2 x := by
      have h_subset : ∀ᶠ x in Filter.atTop, bad_set_lemma_2_2_intrinsic x ⊆ Finset.Icc 1 (Nat.floor (x / Real.log x)) ∪ bad_set_fixed_param x (K_lower x) (K_max x) := by
        filter_upwards [ Filter.eventually_ge_atTop 10 ] with x hx using bad_set_subset_lemma x hx;
      have h_card_bound : ∀ᶠ x in Filter.atTop, (bad_set_fixed_param x (K_lower x) (K_max x)).card ≤ explicit_bound_lemma_2_2 x - (Nat.floor (x / Real.log x) : ℝ) := by
        have h_card_bound : ∀ᶠ x in Filter.atTop, (bad_set_fixed_param x (K_lower x) (K_max x)).card ≤ (2 * K_max x + 1) * (K_max x) * (x / (K_lower x : ℝ)^3 + 1) := by
          filter_upwards [ Filter.eventually_gt_atTop 3, K_lower_ge_two ] with x hx₁ hx₂;
          have := bad_set_fixed_param_bound x ( K_lower x ) ( K_max x ) ( by linarith ) ( by linarith );
          refine le_trans this ?_;
          norm_num [ mul_assoc ];
          nlinarith [ show ( Finset.card ( Finset.filter Nat.Prime ( Finset.range ( 2 * K_max x + 1 ) ) ) : ℝ ) ≤ 2 * K_max x + 1 by exact_mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ), show ( K_max x : ℝ ) * ( x / ( K_lower x : ℝ ) ^ 3 ) ≥ 0 by positivity, show ( K_max x : ℝ ) ≥ 0 by positivity ];
        filter_upwards [ h_card_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
        unfold explicit_bound_lemma_2_2; norm_num; linarith;
      filter_upwards [ h_subset, h_card_bound ] with x hx₁ hx₂;
      have := Finset.card_mono hx₁;
      exact le_trans ( Nat.cast_le.mpr this ) ( le_trans ( Nat.cast_le.mpr ( Finset.card_union_le _ _ ) ) ( by norm_num; linarith ) )

/-
The set of integers m where the valuation condition fails for k = K_max m has density 0.
-/
theorem bad_set_lemma_2_2_intrinsic_density_zero :
    (fun x => ((bad_set_lemma_2_2_intrinsic x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      refine' Asymptotics.IsLittleO.of_isBigOWith _;
      intro c hc;
      -- Apply the fact that the explicit bound function is o(x) to conclude the proof.
      have h_o : Asymptotics.IsLittleO Filter.atTop (fun x => explicit_bound_lemma_2_2 x) (fun x => x) := by
        exact explicit_bound_is_little_o;
      rw [ Asymptotics.IsLittleO ] at h_o;
      have := h_o hc;
      rw [ Asymptotics.IsBigOWith ] at *;
      filter_upwards [ this, Filter.eventually_ge_atTop 10, bad_set_lemma_2_2_intrinsic_card_le_explicit_bound ] with x hx₁ hx₂ hx₃;
      exact le_trans ( by rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ) ( hx₃.trans ( le_trans ( le_abs_self _ ) hx₁ ) )

/-
The p-adic valuation of the descending factorial is bounded by the valuation of k! plus the maximum valuation of the terms.
-/
theorem lemma_2_3_descFactorial (m k p : ℕ) [Fact p.Prime] (hk : k > 0) :
    padicValNat p (Nat.descFactorial (m + k) k) ≤ padicValNat p (Nat.factorial k) + Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
      -- By definition of descending factorial, we have $(m+k)!/m! = \prod_{i=1}^k (m+i)$.
      have h_desc_factorial : Nat.descFactorial (m + k) k = ∏ i ∈ Finset.Icc 1 k, (m + i) := by
        erw [ Finset.prod_Ico_eq_prod_range, Nat.descFactorial_eq_prod_range ];
        rw [ ← Finset.prod_range_reflect ];
        exact Finset.prod_congr rfl fun x hx => by cases k <;> norm_num at * ; omega;
      -- Applying the lemma that states the valuation of a product is the sum of the valuations.
      have h_val_prod : padicValNat p (∏ i ∈ Finset.Icc 1 k, (m + i)) ≤ ∑ i ∈ Finset.Icc 1 k, padicValNat p (m + i) := by
        have h_val_prod : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ i ∈ S, f i ≠ 0) → padicValNat p (∏ i ∈ S, f i) ≤ ∑ i ∈ S, padicValNat p (f i) := by
          intros S f hf_nonzero
          induction' S using Finset.induction with i S hiS ih;
          · norm_num;
          · rw [ Finset.prod_insert hiS, Finset.sum_insert hiS ];
            rw [ padicValNat.mul ( hf_nonzero i ( Finset.mem_insert_self i S ) ) ( Finset.prod_ne_zero_iff.mpr fun x hx => hf_nonzero x ( Finset.mem_insert_of_mem hx ) ) ] ; aesop;
        exact h_val_prod fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
      have := @valuation_sum_le_factorial_valuation m k p;
      obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ Finset.Icc (m + 1) (m + k), ∀ x ∈ Finset.Icc (m + 1) (m + k), padicValNat p x ≤ padicValNat p x₀ := by
        exact Finset.exists_max_image _ _ ⟨ m + 1, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩;
      have h_sum_le_factorial_valuation : ∑ i ∈ Finset.Icc 1 k, padicValNat p (m + i) ≤ padicValNat p k.factorial + padicValNat p x₀ := by
        have h_sum_le_factorial_valuation : ∑ i ∈ Finset.Icc 1 k, padicValNat p (m + i) = ∑ x ∈ Finset.Icc (m + 1) (m + k), padicValNat p x := by
          erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm m, add_assoc ];
        rw [ h_sum_le_factorial_valuation, ← Finset.sum_erase_add _ _ hx₀.1 ] ; linarith [ this x₀ hx₀.1 hx₀.2 ] ;
      have h_max_le_sup : padicValNat p x₀ ≤ Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
        obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc 1 k, x₀ = m + i := by
          exact ⟨ x₀ - m, Finset.mem_Icc.mpr ⟨ Nat.sub_pos_of_lt ( by linarith [ Finset.mem_Icc.mp hx₀.1 ] ), Nat.sub_le_of_le_add ( by linarith [ Finset.mem_Icc.mp hx₀.1 ] ) ⟩, by rw [ Nat.add_sub_cancel' ( by linarith [ Finset.mem_Icc.mp hx₀.1 ] ) ] ⟩;
        exact Finset.le_sup ( f := fun i => padicValNat p ( m + i ) ) hi.1 |> le_trans ( by aesop );
      grind +ring

/-
The p-adic valuation of the descending factorial is bounded by the valuation of k! plus the maximum valuation of the terms.
-/
theorem lemma_2_3_descFactorial_v2 (m k p : ℕ) [Fact p.Prime] (hk : k > 0) :
    padicValNat p (Nat.descFactorial (m + k) k) ≤ padicValNat p (Nat.factorial k) + Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
      exact lemma_2_3_descFactorial m k p hk

/-
For small primes, the valuation of the descending factorial is bounded by the valuation of the middle binomial coefficient.
-/
theorem lemma_small_p_case (m : ℕ) (k : ℕ) (p : ℕ) [Fact p.Prime]
    (hm_large : m ≥ 10)
    (hk_bound : k ≤ K_max m)
    (hk_pos : k > 0)
    (hp : p ∈ Finset.range (2 * k + 1))
    (h_ineq : (k : ℝ) / (p - 1) + 3 * Real.log (K_max m) / Real.log p ≤ 0.49 * Real.log m / Real.log p)
    (h_val_choose : (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log m / Real.log p)
    (h_val_mi : ∀ i ∈ Finset.Icc 1 (K_max m), (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max m) / Real.log p) :
    padicValNat p (Nat.descFactorial (m + k) k) ≤ padicValNat p (Nat.choose (2 * m) m) := by
      have h_val_desc : padicValNat p (Nat.descFactorial (m + k) k) ≤ padicValNat p (Nat.factorial k) + 3 * Real.log (K_max m) / Real.log p := by
        have h_val_desc : padicValNat p (Nat.descFactorial (m + k) k) ≤ padicValNat p (Nat.factorial k) + Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
          exact lemma_2_3_descFactorial_v2 m k p hk_pos;
        have h_val_desc : Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) ≤ 3 * Real.log (K_max m) / Real.log p := by
          have h_val_desc : ∀ i ∈ Finset.Icc 1 k, padicValNat p (m + i) ≤ 3 * Real.log (K_max m) / Real.log p := by
            exact fun i hi => h_val_mi i <| Finset.Icc_subset_Icc_right hk_bound hi;
          have h_val_desc : ∀ {S : Finset ℕ}, S.Nonempty → (∀ i ∈ S, padicValNat p (m + i) ≤ 3 * Real.log (K_max m) / Real.log p) → (Finset.sup S (fun i => padicValNat p (m + i))) ≤ 3 * Real.log (K_max m) / Real.log p := by
            intros S hS_nonempty hS_bound; induction hS_nonempty using Finset.Nonempty.cons_induction <;> aesop;
          exact h_val_desc ⟨ 1, Finset.mem_Icc.mpr ⟨ by norm_num, by linarith ⟩ ⟩ ‹_›;
        exact le_trans ( mod_cast by assumption ) ( add_le_add_left h_val_desc _ );
      have := @legendre_bound_strict k p;
      exact_mod_cast ( by linarith [ this hk_pos ] : ( padicValNat p ( Nat.descFactorial ( m + k ) k ) : ℝ ) ≤ padicValNat p ( Nat.choose ( 2 * m ) m ) )

/-
If the p-adic valuation of a is less than or equal to the p-adic valuation of b for all primes p, then a divides b.
-/
theorem dvd_of_forall_padicValNat_le' {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, p.Prime → padicValNat p a ≤ padicValNat p b) : a ∣ b := by
      -- Apply the fundamental theorem of arithmetic, which states that if the exponents of all primes in the prime factorization of a are less than or equal to those in the factorization of b, then a divides b.
      have h_div : ∀ p : ℕ, Nat.Prime p → (Nat.factorization a p) ≤ (Nat.factorization b p) := by
        intro p pp; specialize h p pp; rw [ Nat.factorization_def, Nat.factorization_def ] ; aesop;
        · assumption;
        · assumption
      generalize_proofs at *;
      exact Nat.factorization_le_iff_dvd ( by positivity ) ( by positivity ) |>.1 fun p => by by_cases hp : Nat.Prime p <;> aesop;

/-
If the conditions hold for a fixed m, then the property holds.
-/
theorem lemma_property_holds_for_fixed_m (m : ℕ)
    (hm_ge_10 : m ≥ 10)
    (h_ineq : ∀ k ∈ Finset.Icc 1 (K_max m), ∀ p ∈ Finset.range (2 * k + 1), p.Prime →
      (k : ℝ) / (p - 1) + 3 * Real.log (K_max m) / Real.log p ≤ 0.49 * Real.log m / Real.log p)
    (h_val_choose : ∀ p ∈ Finset.range (Nat.floor (2 * Real.log m)), p.Prime →
      (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log m / Real.log p)
    (h_val_mi : ∀ p ∈ Finset.range (2 * K_max m + 1), p.Prime → ∀ i ∈ Finset.Icc 1 (K_max m),
      (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max m) / Real.log p) :
    property_thm_1_1 m := by
      simp +zetaDelta at *;
      -- For p > 2k, we use lemma_large_primes.
      have h_large_p : ∀ k ∈ Finset.Icc 1 (K_max m), ∀ p, Nat.Prime p → p > 2 * k → padicValNat p (Nat.descFactorial (m + k) k) ≤ padicValNat p (Nat.choose (2 * m) m) := by
        norm_num +zetaDelta at *;
        intros k hk1 hk2 p hp hp_gt; exact (by
        convert valuation_large_p m k p ( by linarith ) ( by linarith ) using 1;
        exact ⟨ hp ⟩);
      -- For p ≤ 2k, we use lemma_small_p_case.
      have h_small_p : ∀ k ∈ Finset.Icc 1 (K_max m), ∀ p, Nat.Prime p → p ≤ 2 * k → (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) ≤ (padicValNat p (Nat.choose (2 * m) m) : ℝ) := by
        intros k hk p hp hp_le_2k
        have h_ineq_k : (k : ℝ) / (p - 1) + 3 * Real.log (K_max m) / Real.log p ≤ 0.49 * Real.log m / Real.log p := by
          exact h_ineq k ( Finset.mem_Icc.mp hk |>.1 ) ( Finset.mem_Icc.mp hk |>.2 ) p ( by linarith ) hp
        have h_val_choose_k : (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log m / Real.log p := by
          refine' h_val_choose p _ hp |> le_trans <| _;
          · refine' Nat.le_floor _;
            have h_log_m_ge_2 : Real.log m ≥ 2 := by
              rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
              exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 2 : ℝ ) = 1 + 1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ] ) ( Nat.cast_le.mpr hm_ge_10 );
            have h_k_le_0_7_log_m : (k : ℝ) ≤ 0.7 * Real.log m := by
              exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hk |>.2 ) <| Nat.floor_le <| by positivity;
            norm_num at * ; linarith [ show ( p : ℝ ) ≤ 2 * k by norm_cast ];
          · norm_cast
        have h_val_mi_k : ∀ i ∈ Finset.Icc 1 (K_max m), (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max m) / Real.log p := by
          exact fun i hi => h_val_mi p ( by linarith [ Finset.mem_Icc.mp hk, Finset.mem_Icc.mp hi ] ) hp i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 )
        exact (by
        have h_val_descFactorial : (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) ≤ (padicValNat p (Nat.factorial k) : ℝ) + 3 * Real.log (K_max m) / Real.log p := by
          have h_val_descFactorial : (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) ≤ (padicValNat p (Nat.factorial k) : ℝ) + Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
            have h_val_descFactorial : (padicValNat p (Nat.descFactorial (m + k) k) : ℝ) ≤ (padicValNat p (Nat.factorial k) : ℝ) + Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
              have h_val_descFactorial : padicValNat p (Nat.descFactorial (m + k) k) ≤ padicValNat p (Nat.factorial k) + Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
                convert lemma_2_3_descFactorial_v2 m k p _ using 1;
                · exact ⟨ hp ⟩;
                · linarith [ Finset.mem_Icc.mp hk ]
              exact_mod_cast h_val_descFactorial;
            convert h_val_descFactorial using 1;
          refine le_trans h_val_descFactorial ?_;
          simp +zetaDelta at *;
          exact le_trans ( Nat.cast_le.mpr <| Finset.sup_le fun i hi => show padicValNat p ( m + i ) ≤ ⌊3 * Real.log ( K_max m ) / Real.log p⌋₊ from Nat.le_floor <| h_val_mi_k i ( Finset.mem_Icc.mp hi |>.1 ) <| Finset.mem_Icc.mp hi |>.2.trans hk.2 ) <| Nat.floor_le <| by positivity;
        have h_val_factorial : (padicValNat p (Nat.factorial k) : ℝ) < k / (p - 1) := by
          convert legendre_bound_strict k p _ using 1
          generalize_proofs at *;
          · exact ⟨ hp ⟩;
          · linarith [ Finset.mem_Icc.mp hk ];
        linarith);
      intro k hk;
      rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
      · intro p; by_cases hp : Nat.Prime p <;> simp_all +decide [ Nat.factorization ] ;
        exact if h : p ≤ 2 * k then h_small_p k hk.1 hk.2 p hp h else h_large_p k hk.1 hk.2 p hp ( not_le.mp h );
      · exact ne_of_gt <| Nat.choose_pos <| by linarith;

/-
If an integer m is not in the bad sets, then it satisfies the divisibility property for the main theorem.
-/
theorem property_holds_for_large_m :
    ∀ᶠ m : ℕ in Filter.atTop,
      (∀ p ∈ Finset.range (Nat.floor (2 * Real.log (m : ℝ))), p.Prime → (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log (m : ℝ) / Real.log p) →
      (∀ p ∈ Finset.range (2 * K_max (m : ℝ) + 1), p.Prime → ∀ i ∈ Finset.Icc 1 (K_max (m : ℝ)), (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max (m : ℝ)) / Real.log p) →
      property_thm_1_1 m := by
        have h_ineq : ∀ᶠ m in Filter.atTop, ∀ k ∈ Finset.Icc 1 (K_max m), ∀ p ∈ Finset.range (2 * k + 1), p.Prime → (k : ℝ) / (p - 1) + 3 * Real.log (K_max m) / Real.log p ≤ 0.49 * Real.log m / Real.log p := by
          exact inequality_eventually_holds_v2;
        filter_upwards [ Filter.eventually_gt_atTop 9, h_ineq.natCast_atTop ] with m hm₁ hm₂ hm₃ hm₄; exact
          lemma_property_holds_for_fixed_m m hm₁ hm₂ hm₃ hm₄;

/-
The bad set for the main theorem is contained in the union of the auxiliary bad sets and the set where the implication fails.
-/
theorem bad_set_thm_1_1_subset (x : ℝ) :
    bad_set_thm_1_1 x ⊆
    bad_set_lemma_2_1 x ∪
    bad_set_lemma_2_2_intrinsic x ∪
    (Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬ (
      (∀ p ∈ Finset.range (Nat.floor (2 * Real.log (m : ℝ))), p.Prime → (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log (m : ℝ) / Real.log p) →
      (∀ p ∈ Finset.range (2 * K_max (m : ℝ) + 1), p.Prime → ∀ i ∈ Finset.Icc 1 (K_max (m : ℝ)), (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max (m : ℝ)) / Real.log p) →
      property_thm_1_1 m)) := by
        simp +decide [ Finset.subset_iff, bad_set_thm_1_1, bad_set_lemma_2_1, bad_set_lemma_2_2_intrinsic ];
        intro m hm₁ hm₂ hm₃; by_cases hm₄ : ∃ p < ⌊2 * Real.log m⌋₊, p.Prime ∧ (padicValNat p (Nat.choose (2 * m) m) : ℝ) < 0.49 * Real.log m / Real.log p <;> by_cases hm₅ : ∃ p < 2 * K_max m + 1, p.Prime ∧ ∃ i ∈ Finset.Icc 1 (K_max m), (padicValNat p (m + i) : ℝ) > 3 * Real.log (K_max m) / Real.log p <;> simp_all +decide ;

/-
The set of integers m for which the divisibility property fails has asymptotic density 0.
-/
theorem theorem_1_1 :
    (fun x => ((bad_set_thm_1_1 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      -- The third set is finite because `property_holds_for_large_m` holds eventually.
      have finite_third_set : Set.Finite {m : ℕ | ¬((∀ p ∈ Finset.range (Nat.floor (2 * Real.log (m : ℝ))), p.Prime → (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log (m : ℝ) / Real.log p) →
        (∀ p ∈ Finset.range (2 * K_max (m : ℝ) + 1), p.Prime → ∀ i ∈ Finset.Icc 1 (K_max (m : ℝ)), (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max (m : ℝ)) / Real.log p) → property_thm_1_1 m)} := by
          exact Set.finite_iff_bddAbove.mpr ( by rcases Filter.eventually_atTop.mp ( property_holds_for_large_m ) with ⟨ N, hN ⟩ ; exact ⟨ N, fun m hm => not_lt.1 fun contra => hm <| by simpa using hN m contra.le ⟩ );
      have h_union_zero_density : (fun x => ((bad_set_thm_1_1 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
        have h_union : (fun x => ((bad_set_thm_1_1 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
          have h_union : (fun x => ((bad_set_lemma_2_1 x).card : ℝ)) =o[Filter.atTop] (fun x => x) ∧ (fun x => ((bad_set_lemma_2_2_intrinsic x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
            exact ⟨ bad_set_lemma_2_1_density_zero, bad_set_lemma_2_2_intrinsic_density_zero ⟩
          have h_union : ∀ᶠ x in Filter.atTop, ((bad_set_thm_1_1 x).card : ℝ) ≤ ((bad_set_lemma_2_1 x).card : ℝ) + ((bad_set_lemma_2_2_intrinsic x).card : ℝ) + finite_third_set.toFinset.card := by
            have h_union : ∀ x : ℝ, ((bad_set_thm_1_1 x).card : ℝ) ≤ ((bad_set_lemma_2_1 x).card : ℝ) + ((bad_set_lemma_2_2_intrinsic x).card : ℝ) + finite_third_set.toFinset.card := by
              intro x
              have h_union : (bad_set_thm_1_1 x).card ≤ (bad_set_lemma_2_1 x ∪ bad_set_lemma_2_2_intrinsic x ∪ finite_third_set.toFinset).card := by
                exact Finset.card_le_card fun m hm => by have := bad_set_thm_1_1_subset x hm; aesop;
              exact_mod_cast h_union.trans ( Finset.card_union_le _ _ |> le_trans <| add_le_add_right ( Finset.card_union_le _ _ ) _ );
            exact Filter.Eventually.of_forall h_union;
          rw [ Asymptotics.isLittleO_iff_tendsto' ];
          · -- Using the fact that the sum of little-o functions is little-o, we can conclude.
            have h_sum : Filter.Tendsto (fun x => ((bad_set_lemma_2_1 x).card : ℝ) / x + ((bad_set_lemma_2_2_intrinsic x).card : ℝ) / x + (finite_third_set.toFinset.card : ℝ) / x) Filter.atTop (nhds 0) := by
              have h_sum : Filter.Tendsto (fun x => ((bad_set_lemma_2_1 x).card : ℝ) / x) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => ((bad_set_lemma_2_2_intrinsic x).card : ℝ) / x) Filter.atTop (nhds 0) := by
                exact ⟨ by simpa using ‹ ( ( fun x : ℝ => ( bad_set_lemma_2_1 x |> Finset.card : ℝ ) ) =o[Filter.atTop] fun x : ℝ => x ) ∧ ( fun x : ℝ => ( bad_set_lemma_2_2_intrinsic x |> Finset.card : ℝ ) ) =o[Filter.atTop] fun x : ℝ => x ›.1.tendsto_div_nhds_zero, by simpa using ‹ ( ( fun x : ℝ => ( bad_set_lemma_2_1 x |> Finset.card : ℝ ) ) =o[Filter.atTop] fun x : ℝ => x ) ∧ ( fun x : ℝ => ( bad_set_lemma_2_2_intrinsic x |> Finset.card : ℝ ) ) =o[Filter.atTop] fun x : ℝ => x ›.2.tendsto_div_nhds_zero ⟩;
              simpa using Filter.Tendsto.add ( Filter.Tendsto.add h_sum.1 h_sum.2 ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id );
            refine' squeeze_zero_norm' _ h_sum;
            filter_upwards [ h_union, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ ← add_div, ← add_div, div_le_div_iff_of_pos_right ] <;> first | positivity | linarith;
          · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'
        exact h_union;
      convert h_union_zero_density using 1

/-
Generalized bad set for Lemma 2.1 depending on alpha.
-/
noncomputable def bad_set_lemma_2_1_gen (x : ℝ) (alpha : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (Nat.floor (2 * Real.log m)), p.Prime ∧
      (padicValNat p (Nat.choose (2 * m) m) : ℝ) < alpha * Real.log m / Real.log p)

/-
Generalized bad set for a specific prime p and parameter alpha.
-/
noncomputable def bad_set_p_gen (x : ℝ) (p : ℕ) (alpha : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    (p : ℝ) < 2 * Real.log m ∧ (padicValNat p (Nat.choose (2 * m) m) : ℝ) < alpha * Real.log m / Real.log p)

/-
The bound value from the Chernoff inequality for the generalized bad set.
-/
noncomputable def bound_bad_set_p_val_gen (x : ℝ) (p : ℕ) (alpha : ℝ) [Fact p.Prime] : ℝ :=
  let z := z_final p alpha
  let D := D_func p x
  let K := alpha * Real.log x / Real.log p
  weighted_sum p D z * z ^ (-K)

/-
The generalized bad set is contained in the set of integers less than p^D with small valuation.
-/
theorem bad_set_p_gen_subset (x : ℝ) (p : ℕ) (alpha : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) (halpha_pos : 0 < alpha) :
    bad_set_p_gen x p alpha ⊆ (Finset.range (p ^ (D_func p x))).filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) < alpha * Real.log x / Real.log p) := by
      intro m hm
      obtain ⟨hm1, hm2⟩ : m ∈ Finset.Icc 1 (Nat.floor x) ∧ (p : ℝ) < 2 * Real.log m ∧ (padicValNat p (Nat.choose (2 * m) m) : ℝ) < alpha * Real.log m / Real.log p := by
        unfold bad_set_p_gen at hm; aesop;
      have hm3 : m < p ^ (1 + ⌊Real.log x / Real.log p⌋₊) := by
        have hm3 : m < p ^ (Nat.floor (Real.log x / Real.log p) + 1) := by
          have hm3 : Real.log m < (Nat.floor (Real.log x / Real.log p) + 1) * Real.log p := by
            have hm3 : Real.log m ≤ Real.log x := by
              exact Real.log_le_log ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hm1 |>.1 ) <| Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hm1 |>.2 );
            nlinarith [ Nat.lt_floor_add_one ( Real.log x / Real.log p ), Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ), mul_div_cancel₀ ( Real.log x ) ( ne_of_gt ( Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ) ) ) ]
          rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; rw [ ← Real.log_lt_log_iff ( by norm_cast; linarith [ Finset.mem_Icc.mp hm1 ] ) ( by positivity ) ] ; simpa using hm3;
        rwa [ add_comm ];
      refine' Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hm3, _ ⟩;
      exact hm2.2.trans_le ( by rw [ div_le_div_iff_of_pos_right ( Real.log_pos <| Nat.one_lt_cast.mpr hp ) ] ; exact mul_le_mul_of_nonneg_left ( Real.log_le_log ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hm1 |>.1 ) <| Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hm1 |>.2 ) ) halpha_pos.le )

/-
The cardinality of the generalized bad set is bounded by the Chernoff bound.
-/
theorem bad_set_p_gen_card_bound (x : ℝ) (p : ℕ) (alpha : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    ((bad_set_p_gen x p alpha).card : ℝ) ≤ bound_bad_set_p_val_gen x p alpha := by
      -- Apply the Chernoff bound to the set of integers `m < p^D` with `v_p(binom(2m, m)) < alpha * log x / log p`.
      have h_chernoff : ((Finset.range (p ^ (D_func p x))).filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) < alpha * Real.log x / Real.log p)).card ≤ weighted_sum p (D_func p x) (z_final p alpha) * (z_final p alpha) ^ (-((alpha * Real.log x) / Real.log p)) := by
        -- Apply the weighted_sum_bound_general theorem with z = z_final p alpha.
        have h_weighted_sum : ((Finset.range (p ^ (D_func p x))).filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) < alpha * Real.log x / Real.log p)).card ≤ weighted_sum p (D_func p x) (z_final p alpha) * (z_final p alpha) ^ (-((alpha * Real.log x) / Real.log p)) := by
          have hz : 0 < z_final p alpha ∧ z_final p alpha ≤ 1 := by
            exact ⟨ z_final_prop p alpha hp halpha halpha_pos |>.1.1, z_final_prop p alpha hp halpha halpha_pos |>.1.2.le ⟩
          apply weighted_sum_bound_general p (D_func p x) (alpha * Real.log x / Real.log p) (z_final p alpha) hp hz.left hz.right |> le_trans (by
          exact_mod_cast Finset.card_mono <| fun m hm => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hm |>.1, le_of_lt <| Finset.mem_filter.mp hm |>.2 ⟩);
        convert h_weighted_sum using 1;
      refine le_trans ?_ h_chernoff;
      exact_mod_cast Finset.card_le_card ( bad_set_p_gen_subset x p alpha hp hx halpha_pos )

/-
Logarithmic power identity: a^(log b / log c) = b^(log a / log c).
-/
theorem log_pow_identity (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hc1 : c ≠ 1) :
    a ^ (Real.log b / Real.log c) = b ^ (Real.log a / Real.log c) := by
      rw [ Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb ] ; ring_nf

/-
Bound for lambda^D.
-/
theorem lambda_pow_bound (lambda : ℝ) (D : ℕ) (x : ℝ) (p : ℕ)
    (hlambda : lambda ≥ 1)
    (hD : (D : ℝ) ≤ 1 + Real.log x / Real.log p) :
    lambda ^ D ≤ lambda * lambda ^ (Real.log x / Real.log p) := by
      convert Real.rpow_le_rpow_of_exponent_le hlambda hD using 1 ; norm_num [ mul_comm, Real.rpow_add' ] ; ring_nf;
      rw [ Real.rpow_add ( by positivity ), Real.rpow_one ]

/-
Algebraic simplification for the asymptotic bound, with K_val inlined.
-/
theorem asymptotic_simplification (x : ℝ) (p : ℕ) (alpha : ℝ) (z : ℝ) (lambda : ℝ) (rho : ℝ)
    (hx : x ≥ 1) (hp : p ≥ 2) (hz : z > 0) (hlambda : lambda ≥ 1)
    (hrho_pos : rho > 0)
    (h_rho : rho = lambda * z ^ (-alpha))
    (h_D : (D_func p x : ℝ) ≤ 1 + Real.log x / Real.log p) :
    lambda ^ (D_func p x) * z ^ (-(alpha * Real.log x / Real.log p)) ≤ lambda * x ^ (Real.log rho / Real.log p) := by
      -- Applying `lambda_pow_bound` with `hlambda`.
      have h_lambda_pow : lambda ^ (D_func p x) ≤ lambda *lambda ^ (Real.log x / Real.log p) := by
        exact lambda_pow_bound lambda (D_func p x) x p hlambda h_D;
      -- Applying `h_rho` to rewrite `z^(-(alpha * log x / log p))`.
      have h_z_pow : z ^ (-(alpha * Real.log x / Real.log p)) = (z ^ (-alpha)) ^ (Real.log x / Real.log p) := by
        rw [ ← Real.rpow_mul ( by positivity ), neg_mul ] ; ring_nf;
      convert mul_le_mul_of_nonneg_right h_lambda_pow ( by positivity : 0 ≤ z ^ ( - ( alpha * Real.log x / Real.log p ) ) ) using 1 ; rw [ h_z_pow ] ; ring_nf;
      rw [ h_rho, Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] ; ring_nf;
      repeat rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
      norm_num [ mul_assoc, ← Real.exp_add ] ; ring_nf;
      norm_num

/-
Asymptotic bound for the generalized bad set value using the simplified algebraic bound.
-/
theorem bad_set_p_bound_asymptotic_gen (x : ℝ) (p : ℕ) (alpha : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    bound_bad_set_p_val_gen x p alpha ≤ C_p_v2 p (z_final p alpha) * (lambda_plus p (z_final p alpha)) * x ^ (gamma_final p alpha) := by
      -- Apply the C_p_prop_v2 theorem to bound the weighted_sum.
      have h_weighted_sum : weighted_sum p (D_func p x) (z_final p alpha) ≤ C_p_v2 p (z_final p alpha) * (lambda_plus p (z_final p alpha)) ^ (D_func p x) := by
        apply C_p_prop_v2;
        · exact hp;
        · exact z_final_prop p alpha hp halpha halpha_pos |>.1 |>.1;
        · exact z_final_prop p alpha hp halpha halpha_pos |>.1 |>.2.le;
      -- Apply the asymptotic_simplification lemma to bound the term.
      have h_asymptotic : (lambda_plus p (z_final p alpha)) ^ (D_func p x) * (z_final p alpha) ^ (-(alpha * Real.log x / Real.log p)) ≤ (lambda_plus p (z_final p alpha)) * x ^ (gamma_final p alpha) := by
        convert asymptotic_simplification x p alpha ( z_final p alpha ) ( lambda_plus p ( z_final p alpha ) ) ( rho_v2 p alpha ) hx hp _ _ _ _ _ using 1 <;> norm_num;
        · exact z_final_prop p alpha hp halpha halpha_pos |>.1 |>.1;
        · unfold lambda_plus;
          have hz_final_pos : 0 < z_final p alpha := by
            exact z_final_prop p alpha hp halpha halpha_pos |>.1.1;
          rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
          · norm_num [ Nat.add_div ];
            rw [ Real.sqrt_sq ( by positivity ) ] ; nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast ];
          · norm_num [ Nat.add_div ];
            ring_nf;
            nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, show ( z_final ( 1 + c * 2 ) alpha : ℝ ) ≥ 0 by exact le_of_lt ( by simpa [ add_comm, mul_comm ] using hz_final_pos ), Real.sqrt_nonneg ( 1 + ( c * 2 - c * z_final ( 1 + c * 2 ) alpha * 4 ) + c * z_final ( 1 + c * 2 ) alpha ^ 2 * 2 + c ^ 2 + c ^ 2 * z_final ( 1 + c * 2 ) alpha * 2 + ( c ^ 2 * z_final ( 1 + c * 2 ) alpha ^ 2 - z_final ( 1 + c * 2 ) alpha * 2 ) + z_final ( 1 + c * 2 ) alpha ^ 2 ) ];
        · apply_rules [ mul_pos, Real.rpow_pos_of_pos ];
          · refine' add_pos_of_pos_of_nonneg ( mul_pos ( Nat.cast_pos.mpr ( Nat.div_pos ( by linarith ) zero_lt_two ) ) ( by linarith [ show 0 < z_final p alpha from z_final_prop p alpha hp halpha halpha_pos |>.1.1 ] ) ) ( Real.sqrt_nonneg _ );
          · norm_num;
          · exact z_final_prop p alpha hp halpha halpha_pos |>.1 |>.1;
        · exact rfl;
        · unfold D_func;
          simpa using Nat.floor_le ( div_nonneg ( Real.log_nonneg hx ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) );
      have h_combined : bound_bad_set_p_val_gen x p alpha ≤ C_p_v2 p (z_final p alpha) * (lambda_plus p (z_final p alpha) ^ (D_func p x)) * (z_final p alpha) ^ (-(alpha * Real.log x / Real.log p)) := by
        exact mul_le_mul_of_nonneg_right h_weighted_sum ( Real.rpow_nonneg ( show 0 ≤ z_final p alpha from le_of_lt ( z_final_prop p alpha hp halpha halpha_pos |>.1 |>.1 ) ) _ );
      refine le_trans h_combined ?_;
      convert mul_le_mul_of_nonneg_left h_asymptotic _ using 1;
      rw [ mul_assoc ];
      · ring;
      · unfold C_p_v2;
        split_ifs <;> norm_num;
        have := Classical.choose_spec ( weighted_sum_uniform_bound p ( z_final p alpha ) hp ( by linarith ) ( by linarith ) );
        linarith

/-
Eventually, z_final equals z_zero.
-/
theorem z_final_eventually_eq_z_zero (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    ∀ᶠ p in Filter.atTop, z_final p alpha = z_zero alpha := by
      -- By definition of $z_final$, we know that if $bound_func p alpha (z_zero alpha) < p$ and $z_zero alpha < 1$, then $z_final p alpha = z_zero alpha$.
      have h_eventually : ∀ᶠ p in Filter.atTop, bound_func p alpha (z_zero alpha) < p ∧ z_zero alpha < 1 := by
        filter_upwards [ Filter.eventually_gt_atTop 2, eventually_bound_func_lt_p alpha halpha_pos halpha ] with p hp₁ hp₂ using ⟨ hp₂, z_zero_mem_Ioo alpha halpha_pos halpha |>.2 ⟩;
      filter_upwards [ h_eventually, Filter.eventually_ge_atTop 2 ] with p hp hp' ; unfold z_final ; aesop;

/-
The ratio lambda_plus(p, z) / p converges to (1+z)/2 as p -> infinity.
-/
theorem lambda_plus_div_p_converges (z : ℝ) (hz : z ≥ 0) :
    Filter.Tendsto (fun p => lambda_plus p z / p) Filter.atTop (nhds ((1 + z) / 2)) := by
      -- We can divide the numerator and the denominator by $p$ and then take the limit as $p \to \infty$.
      suffices h_div : Filter.Tendsto (fun p : ℕ => ((Nat.ceil ((p : ℝ) / 2)) * (1 + z) + Real.sqrt (((Nat.ceil ((p : ℝ) / 2)) * (1 + z)) ^ 2 - 4 * z * ((Nat.ceil ((p : ℝ) / 2)) ^ 2 - (Nat.floor ((p : ℝ) / 2)) ^ 2))) / (2 * (p : ℝ))) Filter.atTop (nhds ((1 + z) / 2)) by
        unfold lambda_plus; convert h_div using 2 ; ring_nf;
        norm_num [ Nat.add_div ] ; ring_nf;
        cases Nat.mod_two_eq_zero_or_one ‹_› <;> simp +decide [ * ] <;> ring_nf;
        · rename_i k hk; rw [ ← Nat.mod_add_div k 2 ] ; norm_num [ hk ] ; ring_nf;
          norm_num [ show ⌈ ( k / 2 : ℕ ) ⌉₊ = k / 2 from Nat.ceil_natCast _ ] ; ring_nf;
        · field_simp;
          rw [ show ( ⌈ ( _:ℝ ) / 2⌉₊ : ℕ ) = ( ‹ℕ› / 2 ) + 1 from ?_, show ( ⌊ ( _:ℝ ) / 2⌋₊ : ℕ ) = ( ‹ℕ› / 2 ) from ?_ ] <;> norm_num ; ring_nf;
          · erw [ Nat.floor_div_natCast, Nat.floor_natCast ];
          · rw [ Nat.ceil_eq_iff ] <;> norm_num ; ring_nf ; norm_num [ Nat.add_mod, Nat.mul_mod, ‹_› ];
            constructor <;> linarith [ show ( ↑‹ℕ› : ℝ ) = 2 * ( ↑ ( ‹ℕ› / 2 ) : ℝ ) + 1 by norm_cast; linarith [ Nat.mod_add_div ‹ℕ› 2 ], show ( ↑ ( ‹ℕ› / 2 ) : ℝ ) ≥ 0 by positivity ];
      -- We'll use the fact that $\frac{\lceil p/2 \rceil}{p}$ and $\frac{\lfloor p/2 \rfloor}{p}$ both tend to $\frac{1}{2}$ as $p \to \infty$.
      have h_ceil_floor : Filter.Tendsto (fun p : ℕ => (Nat.ceil ((p : ℝ) / 2)) / (p : ℝ)) Filter.atTop (nhds (1 / 2)) ∧ Filter.Tendsto (fun p : ℕ => (Nat.floor ((p : ℝ) / 2)) / (p : ℝ)) Filter.atTop (nhds (1 / 2)) := by
        constructor;
        · refine' ( Metric.tendsto_nhds.mpr _ );
          intro ε ε_pos; refine' Filter.eventually_atTop.mpr ⟨ ⌈ε⁻¹⌉₊ + 1, fun x hx => abs_lt.mpr ⟨ _, _ ⟩ ⟩ <;> nlinarith [ Nat.le_ceil ( x / 2 : ℝ ), Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ε_pos.ne', show ( x : ℝ ) ≥ ⌈ε⁻¹⌉₊ + 1 by exact_mod_cast hx, Nat.ceil_lt_add_one ( show 0 ≤ ( x : ℝ ) / 2 by positivity ), mul_div_cancel₀ ( ⌈ ( x : ℝ ) / 2⌉₊ : ℝ ) ( show ( x : ℝ ) ≠ 0 by norm_cast; linarith ) ] ;
        · rw [ Metric.tendsto_nhds ] ; norm_num;
          intro ε hε; use ⌈ε⁻¹ * 2⌉₊ + 1; intro b hb; rw [ dist_eq_norm ] ; rw [ Real.norm_of_nonpos ] <;> norm_num;
          · rw [ sub_div', div_lt_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * 2 ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( b : ℝ ) ≥ ⌈ε⁻¹ * 2⌉₊ + 1 by exact_mod_cast hb, Nat.floor_le ( show 0 ≤ ( b : ℝ ) / 2 by positivity ), Nat.lt_floor_add_one ( ( b : ℝ ) / 2 ) ];
          · rw [ div_le_div_iff₀ ] <;> norm_num <;> linarith [ Nat.floor_le ( by positivity : 0 ≤ ( b : ℝ ) / 2 ), Nat.le_ceil ( ε⁻¹ * 2 ), ( by norm_cast : ( ⌈ε⁻¹ * 2⌉₊ : ℝ ) + 1 ≤ b ) ];
      -- We can divide the numerator and the denominator by $p$ and then take the limit as $p \to \infty$. We'll use the fact that $\frac{\lceil p/2 \rceil}{p}$ and $\frac{\lfloor p/2 \rfloor}{p}$ both tend to $\frac{1}{2}$ as $p \to \infty$.
      have h_div : Filter.Tendsto (fun p : ℕ => ((Nat.ceil ((p : ℝ) / 2)) * (1 + z) / (p : ℝ) + Real.sqrt (((Nat.ceil ((p : ℝ) / 2)) * (1 + z) / (p : ℝ)) ^ 2 - 4 * z * (((Nat.ceil ((p : ℝ) / 2)) / (p : ℝ)) ^ 2 - ((Nat.floor ((p : ℝ) / 2)) / (p : ℝ)) ^ 2)))) Filter.atTop (nhds ((1 + z) / 2 + Real.sqrt (((1 + z) / 2) ^ 2 - 4 * z * ((1 / 2) ^ 2 - (1 / 2) ^ 2)))) := by
        refine' Filter.Tendsto.add _ _;
        · convert h_ceil_floor.1.const_mul ( 1 + z ) using 2 <;> ring;
        · refine' Filter.Tendsto.sqrt _;
          exact Filter.Tendsto.sub ( Filter.Tendsto.pow ( by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using h_ceil_floor.1.const_mul ( 1 + z ) ) _ ) ( tendsto_const_nhds.mul ( Filter.Tendsto.sub ( h_ceil_floor.1.pow 2 ) ( h_ceil_floor.2.pow 2 ) ) ) |> fun h => h.trans ( by ring_nf; norm_num );
      convert h_div.div_const 2 using 2 <;> ring_nf;
      · field_simp;
        rw [ Real.sqrt_div' _ ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; ring_nf;
      · nlinarith [ Real.sqrt_nonneg ( 1 / 4 + z * ( 1 / 2 ) + z ^ 2 * ( 1 / 4 ) ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ 1 / 4 + z * ( 1 / 2 ) + z ^ 2 * ( 1 / 4 ) ) ]

/-
The limit ratio is strictly less than 1 for alpha < 1/2.
-/
theorem limit_ratio_lt_one_gen (alpha : ℝ) (h1 : 0 < alpha) (h2 : alpha < 1/2) :
    limit_ratio alpha < 1 := by
      -- By definition of $limit_ratio$, we have $limit_ratio \alpha < 1$ follows directly from $h_limit_ratio_lt_one$.
      apply limit_ratio_lt_one alpha h1 h2

/-
The ratio rho_v2(p, alpha) / p converges to limit_ratio(alpha) as p -> infinity.
-/
theorem rho_v2_div_p_converges (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    Filter.Tendsto (fun p => rho_v2 p alpha / p) Filter.atTop (nhds (limit_ratio alpha)) := by
      have h_le_1 : ∀ᶠ p in Filter.atTop, z_final p alpha = z_zero alpha := by
        exact z_final_eventually_eq_z_zero alpha halpha halpha_pos;
      have h_le_2 : Filter.Tendsto (fun p => (lambda_plus p (z_zero alpha) / p) * (z_zero alpha) ^ (-alpha)) Filter.atTop (nhds ((limit_ratio alpha))) := by
        have h_le_2 : Filter.Tendsto (fun p => (lambda_plus p (z_zero alpha) / p)) Filter.atTop (nhds ((1 + z_zero alpha) / 2)) := by
          convert lambda_plus_div_p_converges ( z_zero alpha ) ( show 0 ≤ z_zero alpha from div_nonneg halpha_pos.le ( sub_nonneg.mpr <| by linarith ) ) using 1;
        convert h_le_2.mul_const _ using 1;
      refine' h_le_2.congr' _;
      field_simp;
      filter_upwards [ h_le_1, Filter.eventually_gt_atTop 1 ] with p hp₁ hp₂ ; unfold rho_v2 ; aesop

/-
Step 2 of asymptotic simplification: equality involving rho.
-/
theorem asymptotic_equality_step2 (x : ℝ) (p : ℕ) (alpha : ℝ) (z : ℝ) (lambda : ℝ) (rho : ℝ)
    (hx : x ≥ 1) (hp : p ≥ 2) (hz : z > 0) (hlambda : lambda > 0)
    (hrho_pos : rho > 0)
    (h_rho : rho = lambda * z ^ (-alpha)) :
    lambda * (lambda * z ^ (-alpha)) ^ (Real.log x / Real.log p) = lambda * x ^ (Real.log rho / Real.log p) := by
      rw [ h_rho, Real.rpow_def_of_pos ( by positivity ) ];
      rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
      rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;

/-
Uniform bound for rho_v2 for general alpha.
-/
theorem rho_v2_le_c_mul_p_gen (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    ∃ c < 1, ∀ p ≥ 2, rho_v2 p alpha ≤ c * p := by
      have h_limit_ratio_lt_one : Filter.Tendsto (fun p => rho_v2 p alpha / p) Filter.atTop (nhds (limit_ratio alpha)) := by
        exact rho_v2_div_p_converges alpha halpha halpha_pos;
      -- By Lemma~\ref{lem:bounded_of_convergent_lt_one}, the sequence `rho_v2 p alpha / p` is uniformly bounded by some `c < 1`.
      obtain ⟨c, hc_lt_one, hc⟩ : ∃ c < 1, ∀ p ≥ 2, rho_v2 p alpha / p ≤ c := by
        apply bounded_of_convergent_lt_one ( fun p : ℕ => rho_v2 p alpha / p ) ( limit_ratio alpha ) h_limit_ratio_lt_one ( fun p hp => ?_ ) ( ?_ );
        · exact limit_ratio_lt_one alpha halpha_pos halpha;
        · have h_rrho_lt_p : ∀ p ≥ 2, rho_v2 p alpha < p := by
            intro p hp; exact (by
            convert z_final_prop p alpha hp halpha halpha_pos |>.2 using 1);
          exact div_lt_one ( by positivity ) |>.2 ( h_rrho_lt_p p hp );
      exact ⟨ c, hc_lt_one, fun p hp => by have := hc p hp; rwa [ div_le_iff₀ ( by positivity ) ] at this ⟩

/-
Definition of the uniform constant c_rho for general alpha, and its properties.
-/
noncomputable def c_rho_gen (alpha : ℝ) : ℝ :=
  if h : alpha < 1/2 ∧ 0 < alpha then
    Classical.choose (rho_v2_le_c_mul_p_gen alpha h.1 h.2)
  else 0.99

theorem c_rho_gen_prop (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    c_rho_gen alpha < 1 ∧ ∀ p ≥ 2, rho_v2 p alpha ≤ c_rho_gen alpha * p := by
  rw [c_rho_gen, dif_pos ⟨halpha, halpha_pos⟩]
  exact Classical.choose_spec (rho_v2_le_c_mul_p_gen alpha halpha halpha_pos)

/-
Uniform bound for rho_v2 for general alpha (renamed to avoid conflict).
-/
theorem rho_v2_le_c_mul_p_gen' (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    ∃ c < 1, ∀ p ≥ 2, rho_v2 p alpha ≤ c * p := by
  have h_conv : Filter.Tendsto (fun p => rho_v2 p alpha / p) Filter.atTop (nhds (limit_ratio alpha)) :=
    rho_v2_div_p_converges alpha halpha halpha_pos
  
  have h_lt : ∀ p ≥ 2, rho_v2 p alpha / p < 1 := by
    intro p hp
    have h_rho : rho_v2 p alpha < p := (z_final_prop p alpha hp halpha halpha_pos).2
    rw [div_lt_iff₀ (by norm_cast; linarith)]
    rw [one_mul]
    exact h_rho

  have h_lim : limit_ratio alpha < 1 := limit_ratio_lt_one_gen alpha halpha_pos halpha

  obtain ⟨c, hc_lt_1, hc_bound⟩ := bounded_of_convergent_lt_one (fun p => rho_v2 p alpha / p) (limit_ratio alpha) h_conv h_lt h_lim
  
  use c, hc_lt_1
  intro p hp
  specialize hc_bound p hp
  rw [div_le_iff₀ (by norm_cast; linarith)] at hc_bound
  exact hc_bound

/-
The total bound for the generalized bad set, summing over all relevant primes.
-/
noncomputable def total_bad_set_bound_gen (x : ℝ) (alpha : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1)),
    if h : p.Prime then
      haveI : Fact p.Prime := ⟨h⟩
      C_p_v2 p (z_final p alpha) * (lambda_plus p (z_final p alpha)) * x ^ (gamma_final p alpha)
    else 0

/-
Definition of the decay constant for general alpha, and proof that it is positive.
-/
noncomputable def C_decay_gen (alpha : ℝ) : ℝ := -Real.log (c_rho_gen alpha)

theorem C_decay_gen_pos (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    C_decay_gen alpha > 0 := by
      -- Since $c_{\text{rho}}$ is in $(0, 1)$, its logarithm is negative. Therefore, $C_{\text{decay}}$ is positive.
      have h_c_rho_pos : 0 < c_rho_gen alpha ∧ c_rho_gen alpha < 1 := by
        have := c_rho_gen_prop alpha halpha halpha_pos;
        have := this.2 2 ( by norm_num ) ; norm_num [ rho_v2 ] at this;
        unfold bound_func at this;
        unfold lambda_plus at this; norm_num at this;
        rw [ Real.sqrt_sq ] at this <;> norm_num [ z_final ] at this ⊢;
        · split_ifs at this;
          · exact ⟨ by nlinarith [ show 0 < ( 1 + z_zero alpha ) * z_zero alpha ^ ( -alpha ) by exact mul_pos ( by linarith [ show 0 < z_zero alpha by exact div_pos halpha_pos ( by linarith ) ] ) ( Real.rpow_pos_of_pos ( show 0 < z_zero alpha by exact div_pos halpha_pos ( by linarith ) ) _ ) ], by linarith ⟩;
          · exact ⟨ by nlinarith [ show 0 < ( 1 + z_choice 2 alpha ) * z_choice 2 alpha ^ ( -alpha ) by exact mul_pos ( add_pos zero_lt_one ( z_choice_prop 2 alpha ( by norm_num ) ( by linarith ) |>.1.1 ) ) ( Real.rpow_pos_of_pos ( z_choice_prop 2 alpha ( by norm_num ) ( by linarith ) |>.1.1 ) _ ) ], by linarith ⟩;
          · linarith;
          · linarith;
        · split_ifs <;> norm_num [ z_zero ] at *;
          · exact add_nonneg zero_le_one ( div_nonneg halpha_pos.le ( by linarith ) );
          · have := z_choice_prop 2 alpha ( by norm_num ) ( by linarith ) ; norm_num at this ; linarith;
          · linarith;
          · linarith;
      exact neg_pos_of_neg ( Real.log_neg h_c_rho_pos.1 h_c_rho_pos.2 )

/-
Definition of the decay constant for general alpha (renamed), and proof that it is positive.
-/
noncomputable def C_decay_gen' (alpha : ℝ) : ℝ := -Real.log (c_rho_gen alpha)

theorem C_decay_gen_pos' (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    C_decay_gen' alpha > 0 := by
      convert C_decay_gen_pos alpha halpha halpha_pos using 1

/-
The exponent gamma is bounded by 1 + log(c_rho) / log p.
-/
theorem gamma_final_bound_gen (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    gamma_final p alpha ≤ 1 + Real.log (c_rho_gen alpha) / Real.log p := by
      -- Using the bound from `rho_v2_le_c_mul_p_gen`, we get `gamma_final p alpha ≤ log (c_rho * p) / log p`.
      have h_gamma_le : gamma_final p alpha ≤ Real.log (c_rho_gen alpha * p) / Real.log p := by
        have h_gamma_le : Real.log (rho_v2 p alpha) ≤ Real.log (c_rho_gen alpha * p) := by
          exact Real.log_le_log ( by exact (by
          apply_rules [ mul_pos, add_pos ];
          all_goals norm_num;
          · linarith;
          · apply (z_final_prop p alpha hp halpha halpha_pos).left.left;
          · rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.add_div ] <;> ring_nf <;> norm_num at *;
            · have := z_final_prop ( k * 2 ) alpha ( by linarith ) ( by linarith ) ( by linarith );
              exact add_pos_of_pos_of_nonneg ( add_pos_of_pos_of_nonneg ( sq_pos_of_pos ( Nat.cast_pos.mpr hp ) ) ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( le_of_lt this.1.1 ) ) zero_le_two ) ) ( mul_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) );
            · have := z_final_prop ( 1 + k * 2 ) alpha ( by linarith ) halpha halpha_pos;
              nlinarith [ this.1.1, this.1.2, show ( k : ℝ ) ≥ 1 by norm_cast; linarith ];
          · apply_rules [ Real.rpow_pos_of_pos ];
            exact z_final_prop p alpha hp halpha halpha_pos |>.1 |>.1) ) ( c_rho_gen_prop alpha halpha halpha_pos |>.2 p hp );
        exact div_le_div_of_nonneg_right h_gamma_le <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith;
      convert h_gamma_le using 1;
      rw [ Real.log_mul ] <;> ring_nf <;> norm_num [ show p ≠ 0 by linarith ];
      · rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast ) ) ), add_comm ];
      · have := c_rho_gen_prop alpha halpha halpha_pos;
        have := this.2 2 ( by norm_num ) ; norm_num at this;
        unfold rho_v2 at this;
        unfold bound_func at this;
        unfold lambda_plus at this; norm_num at this;
        rw [ Real.sqrt_sq ] at this <;> nlinarith [ show 0 < z_final 2 alpha from by exact z_final_prop 2 alpha ( by norm_num ) halpha halpha_pos |>.1.1, show 0 < z_final 2 alpha ^ ( -alpha ) from Real.rpow_pos_of_pos ( show 0 < z_final 2 alpha from by exact z_final_prop 2 alpha ( by norm_num ) halpha halpha_pos |>.1.1 ) _ ]

/-
x^gamma is bounded by x * exp(-C * log x / log p).
-/
theorem x_pow_gamma_bound_gen (x : ℝ) (p : ℕ) (alpha : ℝ) (hp : p ≥ 2) (hx : x ≥ 1) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    x ^ (gamma_final p alpha) ≤ x * Real.exp (-C_decay_gen alpha * Real.log x / Real.log p) := by
      have h_exp_bound : gamma_final p alpha ≤ 1 + Real.log (c_rho_gen alpha) / Real.log p := by
        exact gamma_final_bound_gen p alpha hp halpha halpha_pos;
      rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ];
      rw [ show C_decay_gen alpha = -Real.log ( c_rho_gen alpha ) by rfl ] ; ring_nf at *; nlinarith [ Real.log_nonneg hx ] ;

/-
The generalized bad set bound is bounded by the explicit constants.
-/
theorem bad_set_p_bound_asymptotic_gen_explicit (x : ℝ) (p : ℕ) (alpha : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    bound_bad_set_p_val_gen x p alpha ≤ C_p_explicit p (z_final p alpha) * (lambda_plus p (z_final p alpha)) * x ^ (gamma_final p alpha) := by
      -- Apply the bound from C_p_explicit_works to the weighted sum in bound_bad_set_p_val_gen.
      have h_weighted_sum_bound : weighted_sum p (D_func p x) (z_final p alpha) ≤ C_p_explicit p (z_final p alpha) * (lambda_plus p (z_final p alpha)) ^ (D_func p x) := by
        apply C_p_explicit_works p (z_final p alpha) hp (by
        unfold z_final;
        unfold z_zero z_choice; split_ifs <;> norm_num at *;
        · exact div_pos halpha_pos ( by linarith );
        · have := Classical.choose_spec ( show ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, weighted_sum p D ( alpha / ( 1 - alpha ) ) ≤ C * ( lambda_plus p ( alpha / ( 1 - alpha ) ) ) ^ D from by
                                            apply weighted_sum_uniform_bound p (alpha / (1 - alpha)) hp (div_pos halpha_pos (by linarith)) (div_le_one_of_le₀ (by linarith) (by linarith)) )
          generalize_proofs at *;
          exact Classical.choose_spec ‹∃ x : ℝ, ( 0 < x ∧ x < 1 ) ∧ bound_func p alpha x < p› |>.1 |>.1) (by
        unfold z_final;
        unfold z_zero z_choice; split_ifs <;> norm_num;
        · linarith;
        · have := Classical.choose_spec ( show ∃ c < 1, ∀ p ≥ 2, rho_v2 p alpha ≤ c * p from by
                                            exact rho_v2_le_c_mul_p_gen alpha halpha halpha_pos )
          generalize_proofs at *;
          linarith [ Classical.choose_spec ‹∃ x, ( 0 < x ∧ x < 1 ) ∧ bound_func p alpha x < p› |>.1.2 ]) (D_func p x);
      refine' le_trans ( mul_le_mul_of_nonneg_right h_weighted_sum_bound _ ) _;
      · unfold z_final;
        split_ifs <;> norm_num at *;
        · exact Real.rpow_nonneg ( div_nonneg halpha_pos.le ( sub_nonneg.mpr ( by linarith ) ) ) _;
        · apply Real.rpow_nonneg;
          unfold z_choice;
          split_ifs ; norm_num;
          · have := Classical.choose_spec ( show ∃ c : ℝ, c < 1 ∧ ∀ p ≥ 2, rho_v2 p alpha ≤ c * p from by
                                              exact rho_v2_le_c_mul_p_gen' alpha halpha halpha_pos )
            generalize_proofs at *;
            exact le_of_lt ( Classical.choose_spec ‹∃ x : ℝ, ( 0 < x ∧ x < 1 ) ∧ bound_func p alpha x < p› |>.1 |>.1 );
          · aesop;
        · positivity;
      · have := asymptotic_simplification x p alpha ( z_final p alpha ) ( lambda_plus p ( z_final p alpha ) ) ( rho_v2 p alpha ) hx hp ( show 0 < z_final p alpha from ?_ ) ( show 1 ≤ lambda_plus p ( z_final p alpha ) from ?_ ) ( show 0 < rho_v2 p alpha from ?_ ) rfl ?_;
        · simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left this ( show 0 ≤ C_p_explicit p ( z_final p alpha ) by exact le_of_not_gt fun h => by linarith [ show 0 ≤ C_p_explicit p ( z_final p alpha ) from le_of_not_gt fun h' => by { exact absurd h' ( by { exact not_lt_of_ge ( by { unfold C_p_explicit; exact add_nonneg ( mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) } ) } ) } ] );
        · exact z_final_prop p alpha hp halpha halpha_pos |>.1 |>.1;
        · unfold lambda_plus;
          rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
          · norm_num [ Nat.add_div ];
            rw [ Real.sqrt_sq ] <;> nlinarith [ show ( c : ℝ ) ≥ 1 by norm_cast, show 0 ≤ z_final ( 2 * c ) alpha by exact le_of_lt ( by exact ( z_final_prop ( 2 * c ) alpha ( by linarith ) ( by linarith ) ( by linarith ) ) |>.1 |>.1 ) ];
          · rw [ show ( 2 * c + 1 ) / 2 = c by omega ] ; ring_nf ; norm_num;
            nlinarith only [ show ( c : ℝ ) ≥ 1 by norm_cast; linarith, show ( z_final ( 1 + c * 2 ) alpha : ℝ ) ≥ 0 by exact le_of_lt ( show 0 < z_final ( 1 + c * 2 ) alpha from by exact ( z_final_prop ( 1 + c * 2 ) alpha ( by linarith ) ( by linarith ) ( by linarith ) ) |>.1 |>.1 ), Real.sqrt_nonneg ( 1 + ( ( c : ℝ ) * 2 - ( c : ℝ ) * z_final ( 1 + c * 2 ) alpha * 4 ) + ( c : ℝ ) * z_final ( 1 + c * 2 ) alpha ^ 2 * 2 + ( c : ℝ ) ^ 2 + ( c : ℝ ) ^ 2 * z_final ( 1 + c * 2 ) alpha * 2 + ( ( c : ℝ ) ^ 2 * z_final ( 1 + c * 2 ) alpha ^ 2 - z_final ( 1 + c * 2 ) alpha * 2 ) + z_final ( 1 + c * 2 ) alpha ^ 2 ) ];
        · refine' mul_pos _ _;
          · unfold lambda_plus; norm_num;
            exact add_pos_of_pos_of_nonneg ( mul_pos ( Nat.cast_pos.mpr ( Nat.div_pos ( by linarith ) ( by norm_num ) ) ) ( by linarith [ show 0 < z_final p alpha from z_final_prop p alpha hp halpha halpha_pos |>.1.1 ] ) ) ( Real.sqrt_nonneg _ );
          · exact Real.rpow_pos_of_pos ( z_final_prop p alpha hp halpha halpha_pos |>.1 |>.1 ) _;
        · unfold D_func;
          simpa using Nat.floor_le ( div_nonneg ( Real.log_nonneg hx ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) )

/-
The explicit term bound works for the generalized case using C_p_explicit.
-/
noncomputable def term_bound_explicit_gen (x : ℝ) (p : ℕ) (alpha : ℝ) : ℝ :=
  (p : ℝ) ^ 4 * x * Real.exp (-C_decay_gen alpha * Real.log x / Real.log p)

theorem term_bound_explicit_gen_works (x : ℝ) (p : ℕ) (alpha : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    C_p_explicit p (z_final p alpha) * (lambda_plus p (z_final p alpha)) * x ^ (gamma_final p alpha) ≤ term_bound_explicit_gen x p alpha := by
      have := @C_p_explicit_bound_loose p ( z_final p alpha );
      refine le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( this hp ( ?_ ) ( ?_ ) ) ( ?_ ) ) ( ?_ ) ) ?_;
      · have := @z_final_prop p alpha hp halpha halpha_pos; aesop;
      · have := @z_final_prop p alpha hp halpha halpha_pos;
        linarith [ this.1.2 ];
      · refine' div_nonneg _ _ <;> norm_num;
        exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg zero_le_one ( z_final_prop p alpha hp halpha halpha_pos |>.1.1.le ) ) ) ( Real.sqrt_nonneg _ );
      · positivity;
      · refine le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( lambda_plus_le_p p ( z_final p alpha ) hp ( ?_ ) ( ?_ ) ) ( by positivity ) ) ( by positivity ) ) ?_;
        · exact le_of_lt ( z_final_prop p alpha hp halpha halpha_pos |>.1 |>.1 );
        · unfold z_final;
          unfold z_zero z_choice; split_ifs <;> norm_num;
          · linarith;
          · have := Classical.choose_spec ( show ∃ c : ℝ, c < 1 ∧ ∀ p ≥ 2, rho_v2 p alpha ≤ c * p from by
                                              exact rho_v2_le_c_mul_p_gen' alpha halpha halpha_pos )
            generalize_proofs at *;
            linarith [ Classical.choose_spec ‹∃ x, ( 0 < x ∧ x < 1 ) ∧ bound_func p alpha x < p› |>.1.2 ];
        · convert mul_le_mul_of_nonneg_left ( x_pow_gamma_bound_gen x p alpha hp hx halpha halpha_pos ) ( by positivity : 0 ≤ ( p : ℝ ) ^ 4 ) using 1 ; ring_nf;
          unfold term_bound_explicit_gen; ring_nf;

/-
The generalized bad set is contained in the union of bad sets for each prime.
-/
theorem bad_set_lemma_2_1_gen_subset_union (x : ℝ) (alpha : ℝ) (hx : x ≥ 1) :
    bad_set_lemma_2_1_gen x alpha ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1))) (fun p => bad_set_p_gen x p alpha) := by
      unfold bad_set_p_gen bad_set_lemma_2_1_gen;
      intro m hm;
      norm_num +zetaDelta at *;
      obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := hm.2;
      refine' ⟨ p, ⟨ _, hp₂ ⟩, hm.1, _, hp₃ ⟩;
      · refine' lt_of_lt_of_le hp₁ ( Nat.le_succ_of_le ( Nat.floor_mono _ ) );
        exact mul_le_mul_of_nonneg_left ( Real.log_le_log ( Nat.cast_pos.mpr hm.1.1 ) ( Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hm.1.2 ) ) ) zero_le_two;
      · exact Nat.floor_le ( by positivity ) |> lt_of_lt_of_le ( Nat.cast_lt.mpr hp₁ )

/-
The explicit term bound works for the generalized case using C_p_explicit (v2).
-/
noncomputable def term_bound_explicit_gen_v2 (x : ℝ) (p : ℕ) (alpha : ℝ) : ℝ :=
  (p : ℝ) ^ 4 * x * Real.exp (-C_decay_gen alpha * Real.log x / Real.log p)

theorem term_bound_explicit_gen_works_v2 (x : ℝ) (p : ℕ) (alpha : ℝ) [Fact p.Prime] (hp : p ≥ 2) (hx : x ≥ 1) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    C_p_explicit p (z_final p alpha) * (lambda_plus p (z_final p alpha)) * x ^ (gamma_final p alpha) ≤ term_bound_explicit_gen_v2 x p alpha := by
      convert term_bound_explicit_gen_works x p alpha hp hx halpha halpha_pos using 1

/-
The cardinality of the generalized bad set is bounded by the explicit total bound.
-/
noncomputable def total_bad_set_bound_gen_explicit (x : ℝ) (alpha : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1)),
    term_bound_explicit_gen_v2 x p alpha

theorem bad_set_lemma_2_1_gen_card_le_total_explicit (x : ℝ) (alpha : ℝ) (hx : x ≥ 1) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    ((bad_set_lemma_2_1_gen x alpha).card : ℝ) ≤ total_bad_set_bound_gen_explicit x alpha := by
      have := @bad_set_lemma_2_1_gen_subset_union;
      specialize this x alpha hx;
      refine' le_trans ( Nat.cast_le.mpr ( Finset.card_le_card this ) ) _;
      refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
      rw [ Nat.cast_sum ];
      refine' le_trans ( Finset.sum_le_sum fun p hp => _ ) _;
      use fun p => C_p_explicit p ( z_final p alpha ) * ( lambda_plus p ( z_final p alpha ) ) * x ^ ( gamma_final p alpha );
      · convert bad_set_p_gen_card_bound x p alpha ( Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ) hx halpha halpha_pos |> le_trans <| bad_set_p_bound_asymptotic_gen_explicit x p alpha ( Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ) hx halpha halpha_pos using 1;
        exact ⟨ Finset.mem_filter.mp hp |>.2 ⟩;
      · refine' Finset.sum_le_sum fun p hp => _;
        convert term_bound_explicit_gen_works_v2 x p alpha _ _ _ _ using 1;
        · exact ⟨ Finset.mem_filter.mp hp |>.2 ⟩;
        · exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 );
        · linarith;
        · linarith;
        · linarith

/-
Uniform bound for the generalized bad set size.
-/
noncomputable def uniform_bound_gen_explicit (x : ℝ) (alpha : ℝ) : ℝ :=
  let P := 2 * Real.log x
  (P + 1) * (P ^ 4 * x * Real.exp (-C_decay_gen alpha * Real.log x / Real.log P))

/-
The total explicit bound is bounded by the uniform bound.
-/
theorem total_bad_set_bound_gen_explicit_le_uniform (x : ℝ) (alpha : ℝ) (hx : x ≥ 3) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    total_bad_set_bound_gen_explicit x alpha ≤ uniform_bound_gen_explicit x alpha := by
      -- For each prime $p \leq P$, we have $p^4 \leq P^4$ and $\exp(-C \log x / \log p) \leq \exp(-C \log x / \log P)$.
      have h_term_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1)), (p : ℝ) ^ 4 * x * Real.exp (-C_decay_gen alpha * Real.log x / Real.log p) ≤ (2 * Real.log x) ^ 4 * x * Real.exp (-C_decay_gen alpha * Real.log x / Real.log (2 * Real.log x)) := by
        intro p hp
        have h_p_le_P : (p : ℝ) ≤ 2 * Real.log x := by
          exact le_trans ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ) ( Nat.floor_le ( by linarith [ Real.log_nonneg ( by linarith : ( 1:ℝ ) ≤ x ) ] ) )
        have h_log_p_le_log_P : Real.log p ≤ Real.log (2 * Real.log x) := by
          exact Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) h_p_le_P
        have h_exp_bound : Real.exp (-C_decay_gen alpha * Real.log x / Real.log p) ≤ Real.exp (-C_decay_gen alpha * Real.log x / Real.log (2 * Real.log x)) := by
          have h_exp_bound : -C_decay_gen alpha * Real.log x / Real.log p ≤ -C_decay_gen alpha * Real.log x / Real.log (2 * Real.log x) := by
            -- Since $C_decay_gen alpha$ is positive, multiplying by $-1$ makes it negative. Thus, $-C_decay_gen alpha * log x$ is negative.
            have h_neg : -C_decay_gen alpha * Real.log x < 0 := by
              exact mul_neg_of_neg_of_pos ( neg_neg_of_pos ( C_decay_gen_pos alpha halpha halpha_pos ) ) ( Real.log_pos ( by linarith ) );
            rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.log_pos <| show ( p : ℝ ) > 1 from Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ];
          exact Real.exp_le_exp.mpr h_exp_bound;
        gcongr;
      -- The number of terms in the sum is at most $P + 1$.
      have h_num_terms : (Finset.filter Nat.Prime (Finset.range (Nat.floor (2 * Real.log x) + 1))).card ≤ 2 * Real.log x + 1 := by
        exact le_trans ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by norm_num; linarith [ Nat.floor_le <| show 0 ≤ 2 * Real.log x by exact mul_nonneg zero_le_two <| Real.log_nonneg <| by linarith ] ;
      refine' le_trans ( Finset.sum_le_sum h_term_bound ) _;
      norm_num [ uniform_bound_gen_explicit ];
      exact mul_le_mul_of_nonneg_right h_num_terms <| mul_nonneg ( mul_nonneg ( pow_nonneg ( by linarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ x ) ] ) _ ) <| by linarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ x ) ] ) <| Real.exp_nonneg _

/-
The uniform bound for the generalized bad set is o(x).
-/
theorem uniform_bound_gen_explicit_is_little_o (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    (fun x => uniform_bound_gen_explicit x alpha) =o[Filter.atTop] (fun x => x) := by
      -- Divide the uniform bound by x and show that the resulting expression tends to 0.
      have h_div_x : Filter.Tendsto (fun x => (2 * Real.log x + 1) ^ 5 * Real.exp (-C_decay_gen alpha * Real.log x / Real.log (2 * Real.log x))) Filter.atTop (nhds 0) := by
        -- Let $y = \log x$. Then as $x \to \infty$, $y \to \infty$.
        suffices h_log : Filter.Tendsto (fun y => (2 * y + 1) ^ 5 * Real.exp (-C_decay_gen alpha * y / Real.log (2 * y))) Filter.atTop (nhds 0) by
          exact h_log.comp ( Real.tendsto_log_atTop );
        -- Let $z = \log(2y)$. Then as $y \to \infty$, $z \to \infty$.
        suffices h_log : Filter.Tendsto (fun z => (2 * (Real.exp z / 2) + 1) ^ 5 * Real.exp (-C_decay_gen alpha * (Real.exp z / 2) / z)) Filter.atTop (nhds 0) by
          have h_subst : Filter.Tendsto (fun y => (2 * (Real.exp (Real.log (2 * y)) / 2) + 1) ^ 5 * Real.exp (-C_decay_gen alpha * (Real.exp (Real.log (2 * y)) / 2) / Real.log (2 * y))) Filter.atTop (nhds 0) := by
            exact h_log.comp ( Real.tendsto_log_atTop.comp <| Filter.tendsto_id.const_mul_atTop zero_lt_two )
          generalize_proofs at *; (
          refine h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Real.exp_log ( by positivity ) ] ; ring_nf ));
        -- We can factor out $e^{5z}$ from the expression.
        suffices h_factor : Filter.Tendsto (fun z => Real.exp (5 * z) * Real.exp (-C_decay_gen alpha * (Real.exp z / 2) / z)) Filter.atTop (nhds 0) by
          -- Since $(\exp z + 1)^5 / \exp (5z)$ tends to $1$ as $z \to \infty$, we can use the fact that the product of a function tending to $0$ and a function tending to $1$ also tends to $0$.
          have h_ratio : Filter.Tendsto (fun z => (Real.exp z + 1) ^ 5 / Real.exp (5 * z)) Filter.atTop (nhds 1) := by
            -- We can simplify the expression inside the limit.
            suffices h_simplify : Filter.Tendsto (fun z => (1 + 1 / Real.exp z) ^ 5) Filter.atTop (nhds 1) by
              exact h_simplify.congr fun x => by rw [ one_add_div ( by positivity ), div_pow, ← Real.exp_nat_mul ] ; ring_nf;
            exact le_trans ( Filter.Tendsto.pow ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_exp_atTop ) ) ) _ ) ( by norm_num );
          convert h_ratio.mul h_factor using 2 <;> ring_nf;
          norm_num [ Real.exp_ne_zero ];
        norm_num [ ← Real.exp_add ];
        -- We can factor out $x$ from the expression.
        suffices h_factor : Filter.Tendsto (fun x => x * (5 - C_decay_gen alpha * (Real.exp x / (2 * x^2)))) Filter.atTop Filter.atBot by
          grind;
        -- We can factor out $x$ from the expression inside the limit.
        suffices h_factor : Filter.Tendsto (fun x => 5 - C_decay_gen alpha * (Real.exp x / (2 * x^2))) Filter.atTop Filter.atBot by
          exact Filter.Tendsto.atTop_mul_atBot₀ Filter.tendsto_id h_factor;
        -- We can use the fact that $\frac{e^x}{x^2}$ tends to infinity as $x$ tends to infinity.
        have h_exp_div_x2 : Filter.Tendsto (fun x => Real.exp x / x^2) Filter.atTop Filter.atTop := by
          exact Real.tendsto_exp_div_pow_atTop 2;
        have h_const_mul : Filter.Tendsto (fun x => C_decay_gen alpha * (Real.exp x / (2 * x^2))) Filter.atTop Filter.atTop := by
          convert h_exp_div_x2.const_mul_atTop ( show 0 < C_decay_gen alpha / 2 by exact div_pos ( C_decay_gen_pos alpha halpha halpha_pos ) zero_lt_two ) using 2 ; ring;
        exact Filter.tendsto_atTop_atBot.mpr fun x => by rcases Filter.eventually_atTop.mp ( h_const_mul.eventually_gt_atTop ( 5 - x ) ) with ⟨ y, hy ⟩ ; exact ⟨ y, fun z hz => by linarith [ hy z hz ] ⟩ ;
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · refine' squeeze_zero_norm' _ h_div_x ; norm_num [ uniform_bound_gen_explicit ];
        refine' ⟨ Real.exp 1, fun x hx => _ ⟩ ; rw [ abs_of_nonneg ( by linarith [ Real.log_nonneg ( show x ≥ 1 by linarith [ Real.add_one_le_exp 1 ] ) ] : 0 ≤ 2 * Real.log x + 1 ), abs_of_nonneg ( by linarith [ Real.log_nonneg ( show x ≥ 1 by linarith [ Real.add_one_le_exp 1 ] ) ] : 0 ≤ Real.log x ), abs_of_nonneg ( by linarith [ Real.add_one_le_exp 1 ] : 0 ≤ x ) ] ; ring_nf ;
        norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < x from lt_of_lt_of_le ( by positivity ) hx ) ] ; ring_nf ; nlinarith [ Real.exp_pos ( - ( Real.log x * C_decay_gen alpha * ( Real.log ( Real.log x * 2 ) ) ⁻¹ ) ), Real.log_nonneg ( show x ≥ 1 by linarith [ Real.add_one_le_exp 1 ] ), pow_nonneg ( Real.log_nonneg ( show x ≥ 1 by linarith [ Real.add_one_le_exp 1 ] ) ) 2, pow_nonneg ( Real.log_nonneg ( show x ≥ 1 by linarith [ Real.add_one_le_exp 1 ] ) ) 3, pow_nonneg ( Real.log_nonneg ( show x ≥ 1 by linarith [ Real.add_one_le_exp 1 ] ) ) 4, pow_nonneg ( Real.log_nonneg ( show x ≥ 1 by linarith [ Real.add_one_le_exp 1 ] ) ) 5 ] ;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
The generalized bad set has asymptotic density 0.
-/
theorem bad_set_lemma_2_1_gen_density_zero (alpha : ℝ) (halpha : alpha < 1/2) (halpha_pos : 0 < alpha) :
    (fun x => ((bad_set_lemma_2_1_gen x alpha).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · have := @bad_set_lemma_2_1_gen_card_le_total_explicit;
        have := @total_bad_set_bound_gen_explicit_le_uniform;
        have := @uniform_bound_gen_explicit_is_little_o alpha halpha halpha_pos;
        refine' squeeze_zero_norm' _ ( this.tendsto_div_nhds_zero );
        norm_num +zetaDelta at *;
        exact ⟨ 3, fun x hx => by rw [ abs_of_nonneg ( by positivity ) ] ; gcongr ; linarith [ this x alpha hx halpha halpha_pos, ‹∀ x alpha : ℝ, 1 ≤ x → alpha < 1 / 2 → 0 < alpha → ↑ ( bad_set_lemma_2_1_gen x alpha ).card ≤ total_bad_set_bound_gen_explicit x alpha› x alpha ( by linarith ) halpha halpha_pos ] ⟩;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' <| ne_of_gt hx

/-
The implication holds for sufficiently large m.
-/
def implication_holds (m : ℕ) : Prop :=
  (∀ p ∈ Finset.range (Nat.floor (2 * Real.log (m : ℝ))), p.Prime → (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log (m : ℝ) / Real.log p) →
  (∀ p ∈ Finset.range (2 * K_max (m : ℝ) + 1), p.Prime → ∀ i ∈ Finset.Icc 1 (K_max (m : ℝ)), (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max (m : ℝ)) / Real.log p) →
  property_thm_1_1 m

theorem implication_holds_eventually : ∀ᶠ m in Filter.atTop, implication_holds m := by
  apply property_holds_for_large_m

/-
Definition of the failure predicate for the implication.
-/
def P_fail (m : ℕ) : Prop := ¬ (
      (∀ p ∈ Finset.range (Nat.floor (2 * Real.log (m : ℝ))), p.Prime → (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log (m : ℝ) / Real.log p) →
      (∀ p ∈ Finset.range (2 * K_max (m : ℝ) + 1), p.Prime → ∀ i ∈ Finset.Icc 1 (K_max (m : ℝ)), (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max (m : ℝ)) / Real.log p) →
      property_thm_1_1 m)

/-
The bad set for the theorem is contained in the union of the auxiliary bad sets and the set where the implication fails.
-/
theorem bad_set_thm_1_1_subset_proven (x : ℝ) :
    bad_set_thm_1_1 x ⊆
    bad_set_lemma_2_1 x ∪
    bad_set_lemma_2_2_intrinsic x ∪
    (Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬ (
      (∀ p ∈ Finset.range (Nat.floor (2 * Real.log (m : ℝ))), p.Prime → (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≥ 0.49 * Real.log (m : ℝ) / Real.log p) →
      (∀ p ∈ Finset.range (2 * K_max (m : ℝ) + 1), p.Prime → ∀ i ∈ Finset.Icc 1 (K_max (m : ℝ)), (padicValNat p (m + i) : ℝ) ≤ 3 * Real.log (K_max (m : ℝ)) / Real.log p) →
      property_thm_1_1 m)) := by
        intro m hm
        simp [bad_set_thm_1_1] at hm;
        contrapose! hm;
        unfold bad_set_lemma_2_1 bad_set_lemma_2_2_intrinsic at hm; aesop;

/-
The set of exceptions to the implication has asymptotic density 0.
-/
noncomputable def bad_set_implication (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬ implication_holds m)

theorem bad_set_implication_density_zero :
    (fun x => ((bad_set_implication x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · -- By Lemma 2, the set of exceptions to the implication is finite.
        have h_finite : Set.Finite {m : ℕ | ¬(implication_holds m)} := by
          have := implication_holds_eventually;
          rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ M, hM ⟩ ; exact Set.finite_iff_bddAbove.2 ⟨ M, fun m hm => not_lt.1 fun contra => hm <| hM m contra.le ⟩ ;
        -- Since the set of exceptions is finite, its cardinality is bounded by a constant.
        obtain ⟨C, hC⟩ : ∃ C : ℕ, ∀ x : ℝ, ((Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬implication_holds m)).card ≤ C := by
          exact ⟨ h_finite.toFinset.card, fun x => Finset.card_le_card fun m hm => by aesop ⟩;
        refine' squeeze_zero_norm' _ _;
        exacts [ fun x => C / x, Filter.eventually_atTop.mpr ⟨ 1, fun x hx => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( mod_cast hC x ) ( by positivity ) ⟩, tendsto_const_nhds.div_atTop Filter.tendsto_id ];
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
Helper lemma bounding the cardinality of the bad set.
-/
theorem card_bound_helper (x : ℝ) :
    ((bad_set_thm_1_1 x).card : ℝ) ≤ ((bad_set_lemma_2_1 x).card : ℝ) + ((bad_set_lemma_2_2_intrinsic x).card : ℝ) + ((bad_set_implication x).card : ℝ) := by
      have h_union_bound : (bad_set_thm_1_1 x).card ≤ (bad_set_lemma_2_1 x ∪ bad_set_lemma_2_2_intrinsic x ∪ bad_set_implication x).card := by
        refine Finset.card_mono ?_;
        have := bad_set_thm_1_1_subset_proven x;
        convert this using 1;
        ext; simp [bad_set_implication];
        unfold implication_holds; aesop;
      exact_mod_cast h_union_bound.trans ( Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_union_le _ _ ) le_rfl )


noncomputable def K (x : ℝ) : ℕ := Nat.floor (Real.exp (0.8 * Real.sqrt (Real.log x)))


/-
The property that binom(m+k, k) divides binom(2m, m) for all k <= exp(0.8 * sqrt(log m)).
-/
def property_thm_1_2 (m : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (Nat.floor (Real.exp (0.8 * Real.sqrt (Real.log m)))), Nat.choose (m + k) k ∣ Nat.choose (2 * m) m

/-
Definitions of K_thm and the bad sets for Theorem 1.2.
-/
noncomputable def K_thm (x : ℝ) : ℕ := Nat.floor (Real.exp (0.8 * Real.sqrt (Real.log x)))

noncomputable def bad_set_thm_1_2 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬ property_thm_1_2 m)

noncomputable def bad_set_lemma_3_1_thm (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_thm x + 1), p.Prime ∧
      (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ (D_func p x : ℝ) / (5 * Real.log (D_func p x)))

noncomputable def bad_set_lemma_3_2_thm (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_thm x), p.Prime ∧
      ∃ i ∈ Finset.Icc 1 (K_thm x), (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (6 * Real.log (D_func p x)))

/-
Definition of the bad set for Lemma 3.1 for a specific prime p.
-/
noncomputable def bad_set_lemma_3_1_p (x : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ (D_func p x : ℝ) / (5 * Real.log (D_func p x)))

/-
The bad set for Lemma 3.1 is contained in the set of integers with few large digits.
-/
noncomputable def B_func (p : ℕ) (x : ℝ) : ℝ := (D_func p x : ℝ) / (5 * Real.log (D_func p x))

theorem bad_set_subset_large_digits (x : ℝ) (p : ℕ) [Fact p.Prime] :
    bad_set_lemma_3_1_p x p ⊆ (Finset.Icc 1 (Nat.floor x)).filter (fun m => (count_large_digits p m : ℝ) ≤ B_func p x) := by
      -- By definition of bad_set_lemma_3_1_p x p, if m is in this set, then N_p(m) ≤ B_func p x.
      have h_val_p_le_B : ∀ m ∈ bad_set_lemma_3_1_p x p, (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ B_func p x := by
        unfold bad_set_lemma_3_1_p B_func; aesop;
      -- By the lemma, we know that if the p-adic valuation of the binomial coefficient is less than or equal to B_func p x, then the number of large digits in m's base-p representation is also less than or equal to B_func p x.
      have h_count_le_B : ∀ m, (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ B_func p x → (count_large_digits p m : ℝ) ≤ B_func p x := by
        intros m hm
        have h_count_le_B : (count_large_digits p m : ℝ) ≤ (padicValNat p (Nat.choose (2 * m) m) : ℝ) := by
          simp +zetaDelta at *;
          exact valuation_ge_large_digits p m;
        exact le_trans h_count_le_B hm;
      exact fun m hm => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hm |>.1, h_count_le_B m <| h_val_p_le_B m hm ⟩

/-
Definition of large digits in base p: digits d such that 2d >= p.
-/
def large_digits (p : ℕ) : Finset (Fin p) :=
  (Finset.univ : Finset (Fin p)).filter (fun d => 2 * d.val ≥ p)

/-
Definition of small digits in base p: digits d such that 2d < p.
-/
def small_digits (p : ℕ) : Finset (Fin p) :=
  (Finset.univ : Finset (Fin p)).filter (fun d => 2 * d.val < p)

/-
The cardinality of the set of small digits is ceil(p/2).
-/
theorem card_small_digits (p : ℕ) [Fact p.Prime] :
    (small_digits p).card = Nat.ceil (p / 2 : ℝ) := by
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num [ small_digits ];
      · have := Nat.Prime.eq_two_or_odd ( Fact.out : Nat.Prime ( 2 * k ) ) ; aesop;
      · rw [ show ( { d : Fin ( 2 * k + 1 ) | 2 * ( d : ℕ ) < 2 * k + 1 } : Finset ( Fin ( 2 * k + 1 ) ) ) = Finset.Icc ⟨ 0, by linarith ⟩ ⟨ k, by linarith ⟩ from ?_, Finset.card_eq_sum_ones ] ; norm_num [ Nat.ceil_eq_iff ];
        · exact Eq.symm ( Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; linarith, by norm_num; linarith ⟩ );
        · ext ⟨ d, hd ⟩ ; simp +decide [ Nat.lt_succ_iff ]

/-
The cardinality of the set of large digits is p - ceil(p/2).
-/
theorem card_large_digits (p : ℕ) [Fact p.Prime] :
    (large_digits p).card = p - Nat.ceil (p / 2 : ℝ) := by
      rw [ show large_digits p = Finset.univ \ small_digits p from ?_ ];
      · rw [ Finset.card_sdiff ] ; norm_num [ card_small_digits ];
      · ext d; simp [large_digits, small_digits]

/-
The number of large digits is less than or equal to the number of small digits.
-/
theorem large_digits_le_small (p : ℕ) [Fact p.Prime] :
    (large_digits p).card ≤ (small_digits p).card := by
      rw [ card_large_digits, card_small_digits ];
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num;
      · grind;
      · linarith [ show ⌈ ( 2 * k + 1 : ℝ ) / 2⌉₊ ≥ k + 1 by exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by linarith ) ) ]

/-
Definition of the number of large digits in a sequence.
-/
def count_large_seq (p D : ℕ) (f : Fin D → Fin p) : ℕ :=
  (Finset.univ.filter (fun i => f i ∈ large_digits p)).card

/-
The number of sequences of length D with exactly j large digits is binom(D, j) * |Large|^j * |Small|^(D-j).
-/
def seqs_with_j_large (p D j : ℕ) : Finset (Fin D → Fin p) :=
  (Finset.univ : Finset (Fin D → Fin p)).filter (fun f => count_large_seq p D f = j)

theorem card_seqs_with_j_large (p D j : ℕ) [Fact p.Prime] :
    (seqs_with_j_large p D j).card = Nat.choose D j * (large_digits p).card ^ j * (small_digits p).card ^ (D - j) := by
      have h_count_fibers : Finset.card (seqs_with_j_large p D j) = ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin D)), (large_digits p).card ^ j * (small_digits p).card ^ (D - j) := by
        have h_count_fibers : Finset.card (seqs_with_j_large p D j) = ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin D)), Finset.card (Finset.filter (fun f : Fin D → Fin p => ∀ i, (f i ∈ large_digits p ↔ i ∈ s)) (Finset.univ : Finset (Fin D → Fin p))) := by
          rw [ show seqs_with_j_large p D j = Finset.biUnion ( Finset.powersetCard j ( Finset.univ : Finset ( Fin D ) ) ) ( fun s => Finset.filter ( fun f : Fin D → Fin p => ∀ i : Fin D, f i ∈ large_digits p ↔ i ∈ s ) ( Finset.univ : Finset ( Fin D → Fin p ) ) ) from ?_ ];
          · rw [ Finset.card_biUnion ];
            intros s hs t ht hst; simp_all +decide [ Finset.disjoint_left ] ;
            contrapose! hst; aesop;
          · ext f; simp [seqs_with_j_large];
            unfold count_large_seq; aesop;
        -- For each subset $s$ of size $j$, the number of sequences where the digits in $s$ are large and the digits not in $s$ are small is $(large_digits p).card^j * (small_digits p).card^{D-j}$.
        have h_card_filter : ∀ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin D)), Finset.card (Finset.filter (fun f : Fin D → Fin p => ∀ i, (f i ∈ large_digits p ↔ i ∈ s)) (Finset.univ : Finset (Fin D → Fin p))) = (large_digits p).card^j * (small_digits p).card^(D-j) := by
          intro s hs
          have h_card_filter : Finset.card (Finset.filter (fun f : Fin D → Fin p => ∀ i, (f i ∈ large_digits p ↔ i ∈ s)) (Finset.univ : Finset (Fin D → Fin p))) = (∏ i : Fin D, if i ∈ s then (large_digits p).card else (small_digits p).card) := by
            have h_card_filter : Finset.card (Finset.filter (fun f : Fin D → Fin p => ∀ i, (f i ∈ large_digits p ↔ i ∈ s)) (Finset.univ : Finset (Fin D → Fin p))) = (∏ i : Fin D, Finset.card (Finset.filter (fun d => d ∈ large_digits p ↔ i ∈ s) (Finset.univ : Finset (Fin p)))) := by
              rw [ ← Finset.card_pi ];
              refine' Finset.card_bij _ _ _ _;
              use fun a ha i _ => a i;
              · aesop;
              · simp +contextual [ funext_iff ];
              · simp +decide [ funext_iff ];
                exact fun b hb => ⟨ fun i => b i ( Finset.mem_univ i ), hb, fun i => rfl ⟩;
            convert h_card_filter using 2;
            split_ifs <;> simp_all +decide [ Finset.ext_iff, large_digits, small_digits ];
          simp_all +decide [ Finset.prod_ite ];
          simp +decide [ Finset.filter_not, Finset.card_sdiff, * ];
        exact h_count_fibers.trans ( Finset.sum_congr rfl h_card_filter );
      simp_all +decide [ mul_assoc, Finset.card_univ ]

/-
The number of sequences with at most B large digits is bounded by L^D times the sum of binomial coefficients.
-/
theorem card_seqs_le_bound (p D B : ℕ) [Fact p.Prime] :
    let L := Nat.ceil (p / 2 : ℝ)
    ((Finset.univ : Finset (Fin D → Fin p)).filter (fun f => count_large_seq p D f ≤ B)).card ≤
    L ^ D * ∑ j ∈ Finset.range (B + 1), Nat.choose D j := by
      -- The cardinality of the set of sequences with at most B large digits is the sum of the cardinalities of the sets with exactly j large digits for j from 0 to B.
      have h_card_sum : (Finset.filter (fun f : Fin D → Fin p => count_large_seq p D f ≤ B) (Finset.univ : Finset (Fin D → Fin p))).card = ∑ j ∈ Finset.range (B + 1), (Finset.filter (fun f : Fin D → Fin p => count_large_seq p D f = j) (Finset.univ : Finset (Fin D → Fin p))).card := by
        simp +decide only [Finset.card_eq_sum_ones, Finset.sum_filter];
        rw [ ← Finset.sum_comm ];
        rcongr x ; simp +decide [ Nat.lt_succ_iff ];
      -- By definition of `seqs_with_j_large`, we have that `(Finset.filter (fun f : Fin D → Fin p => count_large_seq p D f = j) (Finset.univ : Finset (Fin D → Fin p))).card = Nat.choose D j * (large_digits p).card ^ j * (small_digits p).card ^ (D - j)`.
      have h_card_filter : ∀ j ∈ Finset.range (B + 1), (Finset.filter (fun f : Fin D → Fin p => count_large_seq p D f = j) (Finset.univ : Finset (Fin D → Fin p))).card ≤ Nat.choose D j * (Nat.ceil (p / 2 : ℝ)) ^ D := by
        intro j hj
        have h_card_filter : (Finset.filter (fun f : Fin D → Fin p => count_large_seq p D f = j) (Finset.univ : Finset (Fin D → Fin p))).card = Nat.choose D j * (large_digits p).card ^ j * (small_digits p).card ^ (D - j) := by
          convert card_seqs_with_j_large p D j using 1;
        -- Since $(large_digits p).card \leq \lceil p / 2 \rceil$ and $(small_digits p).card \leq \lceil p / 2 \rceil$, we can bound the product.
        have h_bound : (large_digits p).card ^ j * (small_digits p).card ^ (D - j) ≤ (Nat.ceil (p / 2 : ℝ)) ^ j * (Nat.ceil (p / 2 : ℝ)) ^ (D - j) := by
          gcongr;
          · convert large_digits_le_small p using 1;
            rw [ card_small_digits ];
          · rw [ card_small_digits ];
        cases le_total D j <;> simp_all +decide [ mul_assoc, ← pow_add ];
        · cases eq_or_lt_of_le ‹_› <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ];
        · exact Nat.mul_le_mul_left _ h_bound;
      simpa only [ h_card_sum, Finset.mul_sum _ _ _, mul_comm ] using Finset.sum_le_sum h_card_filter

/-
The number of large digits in m is equal to the number of large digits in its base-p representation of length D.
-/
theorem count_large_digits_eq_count_large_seq (p D m : ℕ) [Fact p.Prime] (hm : m < p ^ D) :
    count_large_digits p m = count_large_seq p D (digits_of p D m) := by
      unfold count_large_digits digits_of;
      rw [ ← Nat.ofDigits_digits p m ];
      induction' D with D ih generalizing m <;> simp_all +decide [ Nat.ofDigits, pow_succ, mul_assoc ];
      · rfl;
      · convert congr_arg ( fun x : ℕ => x + ( if p ≤ 2 * ( m % p ) then 1 else 0 ) ) ( ih ( m / p ) ( Nat.div_lt_of_lt_mul <| by linarith ) ) using 1;
        · rw [ Nat.ofDigits_digits, Nat.ofDigits_digits ];
          rcases p with ( _ | _ | p ) <;> rcases m with ( _ | _ | m ) <;> norm_num [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ] at *;
          · cases p <;> trivial;
          · split_ifs <;> simp_all +arith +decide [ List.filter_cons ];
        · unfold count_large_seq;
          rw [ Finset.card_filter, Finset.card_filter ];
          rw [ Fin.sum_univ_succ ] ; norm_num [ Nat.ofDigits_digits, Nat.div_eq_of_lt ( show m % p < p from Nat.mod_lt _ ( Nat.Prime.pos Fact.out ) ) ];
          rw [ add_comm ];
          norm_num [ Nat.div_div_eq_div_mul, pow_succ', mul_comm ];
          exact if_congr ( by rw [ large_digits ] ; simp +decide [ mul_comm ] ) rfl rfl

/-
The number of integers with at most B large digits equals the number of sequences with at most B large digits.
-/
theorem card_filter_digits_eq_card_filter_seqs (p D B : ℕ) [Fact p.Prime] :
    ((Finset.range (p ^ D)).filter (fun m => count_large_digits p m ≤ B)).card =
    ((Finset.univ : Finset (Fin D → Fin p)).filter (fun f => count_large_seq p D f ≤ B)).card := by
      refine' Finset.card_bij ( fun m hm => digits_of p D m ) _ _ _;
      · exact fun m hm => by simpa using Finset.mem_filter.mp hm |>.2 |> fun h => by simpa [ count_large_digits_eq_count_large_seq p D m ( Finset.mem_range.mp ( Finset.mem_filter.mp hm |>.1 ) ) ] using h;
      · simp +zetaDelta at *;
        intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; rw [ ← Nat.ofDigits_digits p a₁, ← Nat.ofDigits_digits p a₂ ] ;
        unfold digits_of at h;
        have h_digits_eq : ∀ i : Fin D, a₁ / p ^ (i : ℕ) % p = a₂ / p ^ (i : ℕ) % p := by
          exact fun i => by simpa using congr_fun h i;
        -- Since the digits of $a_1$ and $a_2$ are equal, their base-$p$ representations are equal.
        have h_base_eq : a₁ = ∑ i ∈ Finset.range D, (a₁ / p ^ i % p) * p ^ i ∧ a₂ = ∑ i ∈ Finset.range D, (a₂ / p ^ i % p) * p ^ i := by
          have h_base_eq : ∀ (n : ℕ) (D : ℕ), n < p ^ D → n = ∑ i ∈ Finset.range D, (n / p ^ i % p) * p ^ i := by
            intro n D hn; induction' D with D ih generalizing n <;> simp +decide [ Finset.sum_range_succ', pow_succ, ← Nat.div_div_eq_div_mul ] at *;
            · exact hn;
            · have := ih ( n / p ) ( Nat.div_lt_of_lt_mul <| by linarith );
              convert congr_arg ( · * p + n % p ) this using 1;
              · rw [ Nat.div_add_mod' ];
              · simp +decide [ Finset.sum_mul _ _ _, Nat.div_div_eq_div_mul, mul_assoc, mul_comm, mul_left_comm, pow_succ, Nat.div_eq_of_lt ];
          exact ⟨ h_base_eq a₁ D ha₁, h_base_eq a₂ D ha₃ ⟩;
        rw [ h_base_eq.1, h_base_eq.2 ];
        rw [ show ∑ i ∈ Finset.range D, a₁ / p ^ i % p * p ^ i = ∑ i ∈ Finset.range D, a₂ / p ^ i % p * p ^ i from Finset.sum_congr rfl fun i hi => by rw [ h_digits_eq ⟨ i, Finset.mem_range.mp hi ⟩ ] ];
      · intro f hf;
        use Nat.ofDigits p ( List.ofFn fun i => f i );
        refine' ⟨ _, _ ⟩;
        refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
        all_goals norm_num [ Nat.ofDigits_digits, digits_of ];
        · convert Nat.ofDigits_lt_base_pow_length _ _;
          · rw [ List.length_ofFn ];
          · exact Nat.Prime.one_lt Fact.out;
          · simp +decide [ List.mem_ofFn ];
        · rw [ count_large_digits_eq_count_large_seq ];
          rw [ show digits_of p D ( Nat.ofDigits p ( List.ofFn fun i => ( f i : ℕ ) ) ) = f from ?_ ];
          · aesop;
          · unfold digits_of;
            ext i; simp +decide [ Nat.ofDigits_digits, Nat.mod_eq_of_lt ] ;
            -- By definition of `Nat.ofDigits`, the i-th digit of the number formed by the list of f's values is exactly f i.
            have h_digit : ∀ (l : List ℕ), (∀ d ∈ l, d < p) → ∀ i < l.length, (Nat.ofDigits p l / p ^ i) % p = l.get! i := by
              intro l hl i hi; induction' l with d l ih generalizing i <;> simp_all +decide [ Nat.ofDigits ] ;
              rcases i <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
              · exact Nat.mod_eq_of_lt hl.1;
              · simp_all +decide [ Nat.add_mul_div_left _ _ ( Nat.Prime.pos Fact.out ) ];
                rw [ Nat.div_eq_of_lt hl.1 ] ; aesop;
            convert h_digit _ _ _ _ <;> aesop;
          · refine' Nat.ofDigits_lt_base_pow_length _ _ |> lt_of_lt_of_le <| _;
            · exact Nat.Prime.one_lt Fact.out;
            · aesop;
            · norm_num;
        · refine' funext fun i => _;
          -- By definition of `Nat.ofDigits`, the i-th digit of `Nat.ofDigits p (List.ofFn fun i => f i)` is `f i`.
          have h_digit : (Nat.ofDigits p (List.ofFn fun i => f i)) / p ^ (i : ℕ) % p = f i := by
            -- By definition of `Nat.ofDigits`, the i-th digit of the number formed by the list of f's values is exactly f i.
            have h_digit : ∀ (l : List ℕ), (∀ d ∈ l, d < p) → ∀ i < l.length, (Nat.ofDigits p l / p ^ i) % p = l.get! i := by
              intro l hl i hi; induction' l with d l ih generalizing i <;> simp_all +decide [ Nat.ofDigits ] ;
              rcases i <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
              · exact Nat.mod_eq_of_lt hl.1;
              · simp_all +decide [ Nat.add_mul_div_left _ _ ( Nat.Prime.pos Fact.out ) ];
                rw [ Nat.div_eq_of_lt hl.1 ] ; aesop;
            convert h_digit _ _ _ _ <;> aesop;
          exact Fin.ext h_digit

/-
The number of integers less than p^D with at most B large digits is bounded by L^D times the sum of binomial coefficients.
-/
theorem card_le_sum_binom_mul_pow (p D B : ℕ) [Fact p.Prime] :
    let L := Nat.ceil (p / 2 : ℝ)
    ((Finset.range (p ^ D)).filter (fun m => count_large_digits p m ≤ B)).card ≤
    L ^ D * ∑ j ∈ Finset.range (B + 1), Nat.choose D j := by
      -- Apply the established bounds from `card_filter_digits_eq_card_filter_seqs` and `card_seqs_le_bound`.
      have := card_filter_digits_eq_card_filter_seqs p D B; (
      -- Apply the bound from `card_seqs_le_bound` to conclude the proof.
      have := card_seqs_le_bound p D B;
      aesop)

/-
Redefinition of bad sets with a larger constant (100) to ensure the bounds hold.
-/
noncomputable def bad_set_lemma_3_1_v2 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_thm x + 1), p.Prime ∧
      (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ (D_func p x : ℝ) / (100 * Real.log (D_func p x)))

noncomputable def bad_set_lemma_3_2_v2 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_thm x), p.Prime ∧
      ∃ i ∈ Finset.Icc 1 (K_thm x), (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (100 * Real.log (D_func p x)))

/-
Definitions of B_v2 and bad_set_lemma_3_1_p_v2 with the constant 100.
-/
noncomputable def B_v2 (p : ℕ) (x : ℝ) : ℝ := (D_func p x : ℝ) / (100 * Real.log (D_func p x))

noncomputable def bad_set_lemma_3_1_p_v2 (x : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ B_v2 p x)

/-
The bad set for Lemma 3.1 (v2) is contained in the set of integers with few large digits.
-/
theorem bad_set_subset_large_digits_v2 (x : ℝ) (p : ℕ) [Fact p.Prime] :
    bad_set_lemma_3_1_p_v2 x p ⊆ (Finset.Icc 1 (Nat.floor x)).filter (fun m => (count_large_digits p m : ℝ) ≤ B_v2 p x) := by
      -- By definition of bad_set_lemma_3_1_p_v2, we have that for any m in this set, the p-adic valuation of the binomial coefficient is less than or equal to B_v2 p x.
      intro m hm
      obtain ⟨h_geom_cond, h_val_le⟩ := Finset.mem_filter.mp hm;
      norm_num +zetaDelta at *;
      refine' ⟨ h_geom_cond, le_trans _ h_val_le ⟩;
      have h_geom_cond : padicValNat p (Nat.choose (2 * m) m) ≥ count_large_digits p m := by
        exact valuation_ge_large_digits p m;
      exact_mod_cast h_geom_cond

/-
The sum of binomial coefficients binom(n, i) for i <= k is bounded by (k+1) * binom(n, k) when k <= n/2.
-/
theorem sum_choose_le_mul_max (n k : ℕ) (hk : 2 * k ≤ n) :
    ∑ i ∈ Finset.range (k + 1), Nat.choose n i ≤ (k + 1) * Nat.choose n k := by
      induction' k with k ih <;> simp_all +decide [ Finset.sum_range_succ, Nat.choose_succ_succ ];
      nlinarith [ ih ( by linarith ), Nat.succ_mul_choose_eq n k, Nat.choose_succ_succ n k ]

/-
The cardinality of the bad set for Lemma 3.1 (v2) is bounded by L^D * (B+1) * D^B.
-/
noncomputable def bound_lemma_3_1_p_v3 (x : ℝ) (p : ℕ) : ℝ :=
  let D := D_func p x
  let B := B_v2 p x
  let L := Nat.ceil (p / 2 : ℝ)
  (L : ℝ) ^ D * (B + 1) * (D : ℝ) ^ (Nat.floor B)

theorem lemma_3_1_p_bound_v3 (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) :
    ((bad_set_lemma_3_1_p_v2 x p).card : ℝ) ≤ bound_lemma_3_1_p_v3 x p := by
      have h_card_small_m : ∀ x : ℝ, x ≥ 3 → ((Finset.range (p ^ (D_func p x))).filter (fun m => (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ (D_func p x : ℝ) / (100 * Real.log (D_func p x)))).card ≤
        (Nat.ceil (p / 2 : ℝ)) ^ (D_func p x) * (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1) * (D_func p x : ℝ) ^ (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x)))) := by
          intros x hx
          have h_card_small_m : ((Finset.range (p ^ (D_func p x))).filter (fun m => (count_large_digits p m : ℝ) ≤ (D_func p x : ℝ) / (100 * Real.log (D_func p x)))).card ≤
            (Nat.ceil (p / 2 : ℝ)) ^ (D_func p x) * (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1) * (D_func p x : ℝ) ^ (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x)))) := by
              have h_card_small_m : ((Finset.range (p ^ (D_func p x))).filter (fun m => (count_large_digits p m : ℝ) ≤ (D_func p x : ℝ) / (100 * Real.log (D_func p x)))).card ≤
                (Nat.ceil (p / 2 : ℝ)) ^ (D_func p x) * (∑ j ∈ Finset.range (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1), Nat.choose (D_func p x) j) := by
                  have h_card_small_m : ((Finset.range (p ^ (D_func p x))).filter (fun m => (count_large_digits p m : ℝ) ≤ (D_func p x : ℝ) / (100 * Real.log (D_func p x)))).card ≤
                    (Nat.ceil (p / 2 : ℝ)) ^ (D_func p x) * (∑ j ∈ Finset.range (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1), Nat.choose (D_func p x) j) := by
                    have := card_le_sum_binom_mul_pow p (D_func p x) (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))))
                    refine le_trans ?_ this;
                    exact Finset.card_mono fun m hm => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hm |>.1, Nat.le_floor <| Finset.mem_filter.mp hm |>.2 ⟩;
                  convert h_card_small_m using 1;
              have h_card_small_m : (∑ j ∈ Finset.range (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1), Nat.choose (D_func p x) j) ≤ (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1) * (D_func p x : ℝ) ^ (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x)))) := by
                have h_card_small_m : ∀ j ∈ Finset.range (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1), Nat.choose (D_func p x) j ≤ (D_func p x : ℝ) ^ j := by
                  norm_cast;
                  exact fun j a ↦ Nat.choose_le_pow (D_func p x) j;
                push_cast;
                refine' le_trans ( Finset.sum_le_sum h_card_small_m ) _;
                exact le_trans ( Finset.sum_le_sum fun _ _ => pow_le_pow_right₀ ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by { exact ne_of_gt <| Nat.pos_of_ne_zero fun h => by { simp_all +decide [ D_func ] } } ) <| Finset.mem_range_succ_iff.mp ‹_› ) <| by norm_num;
              norm_cast at * ; simp_all +decide [ mul_assoc ];
              exact le_trans ‹_› ( Nat.mul_le_mul_left _ h_card_small_m );
          refine le_trans ?_ h_card_small_m;
          field_simp;
          gcongr;
          intro m hm;
          refine le_trans ?_ hm;
          rw [ mul_comm ];
          gcongr;
          exact valuation_ge_large_digits p m;
      -- Apply the lemma h_card_small_m to bound the cardinality of the bad set.
      have h_card_le : ((bad_set_lemma_3_1_p_v2 x p).card : ℝ) ≤ (Nat.ceil (p / 2 : ℝ)) ^ (D_func p x) * (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1) * (D_func p x : ℝ) ^ (Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x)))) := by
        refine le_trans ?_ ( h_card_small_m x hx );
        refine' mod_cast Finset.card_le_card _;
        intro m hm;
        simp +zetaDelta at *;
        refine' ⟨ _, _ ⟩;
        · refine' lt_of_le_of_lt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.2 ) _;
          refine' Nat.floor_lt ( by positivity ) |>.2 _;
          -- Since $p^{\log_p x} = x$, we have $x < p^{1 + \log_p x}$.
          have h_exp : x < p ^ (1 + Nat.floor (Real.log x / Real.log p)) := by
            have := Nat.lt_floor_add_one ( Real.log x / Real.log p );
            rw [ div_lt_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out ) ] at this;
            rw [ ← Real.log_lt_log_iff ( by positivity ) ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ), Real.log_pow ] ; norm_num ; linarith;
          convert h_exp using 1;
          norm_cast;
        · unfold bad_set_lemma_3_1_p_v2 at hm; aesop;
      refine le_trans h_card_le ?_;
      refine' mul_le_mul_of_nonneg_right _ _;
      · gcongr;
        exact Nat.floor_le ( div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by unfold D_func; aesop ) ) ) ) ) );
      · positivity

/-
L^D is bounded by 2px^(log L / log p).
-/
noncomputable def exponent_p (p : ℕ) : ℝ := Real.log (Nat.ceil (p / 2 : ℝ)) / Real.log p

theorem bound_L_pow_D (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) :
    let L := Nat.ceil (p / 2 : ℝ)
    let D := D_func p x
    (L : ℝ) ^ D ≤ 2 * p * x ^ (exponent_p p) := by
      unfold D_func exponent_p;
      -- Apply the inequality $L^{\lfloor \log x / \log p \rfloor} \leq x^{\log L / \log p}$.
      have h_exp : ((Nat.ceil (p / 2 : ℝ)) : ℝ) ^ (Nat.floor (Real.log x / Real.log p)) ≤ x ^ (Real.log (Nat.ceil (p / 2 : ℝ)) / Real.log p) := by
        rw [ Real.le_rpow_iff_log_le ] <;> try positivity;
        · field_simp;
          rw [ mul_comm, mul_div_assoc ];
          rw [ Real.log_pow ];
          rw [ mul_comm ] ; gcongr ; exact Nat.floor_le ( by exact div_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos Fact.out ) ) ) );
        · exact pow_pos ( Nat.cast_pos.mpr <| Nat.ceil_pos.mpr <| by exact div_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) zero_lt_two ) _;
      norm_num [ pow_add ];
      exact mul_le_mul ( by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( p : ℝ ) / 2 by positivity ), show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le Fact.out ] ) h_exp ( by positivity ) ( by positivity )

/-
Bound on exponent_p for p >= 3.
-/
theorem exponent_p_bound (p : ℕ) [Fact p.Prime] (hp : p ≥ 3) :
    exponent_p p ≤ 1 - (Real.log 2 - 2 / p) / Real.log p := by
      unfold exponent_p;
      -- Using the inequality $\log(p/2 + 1) \leq \log(p) - \log(2) + 2/p$, we can bound the exponent.
      have h_log_bound : Real.log (Nat.ceil (p / 2 : ℝ)) ≤ Real.log p - Real.log 2 + 2 / p := by
        rw [ ← Real.log_div ( by positivity ) ( by positivity ) ];
        rw [ Real.log_le_iff_le_exp ( by positivity ) ];
        rw [ Real.exp_add, Real.exp_log ( by positivity ) ];
        nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( p : ℝ ) / 2 by positivity ), Real.add_one_le_exp ( 2 / p : ℝ ), mul_div_cancel₀ ( 2 : ℝ ) ( by positivity : ( p : ℝ ) ≠ 0 ) ];
      rw [ one_sub_div ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ];
      bound

/-
Bound for D^floor(B).
-/
theorem bound_D_pow_B (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) :
    let D := D_func p x
    let B := B_v2 p x
    (D : ℝ) ^ (Nat.floor B) ≤ Real.exp (0.02) * x ^ (1 / (100 * Real.log p)) := by
      -- Using the definition of $D_func$, we have $(D_func p x) ^ B_v2 p x \leq \exp(0.02) * x ^ {1/(100 \log p)}$.
      have h_exp_bound : ∀ x : ℝ, x ≥ 3 → ∀ p : ℕ, Nat.Prime p → p ≥ 2 → (D_func p x) ^ B_v2 p x ≤ Real.exp 0.02 * x ^ ((Real.log p)⁻¹ * (1 / 100)) := by
        intros x hx p hp hp_ge_2
        have h_exp_bound : (D_func p x) ^ B_v2 p x ≤ Real.exp (D_func p x / (100 * Real.log (D_func p x)) * Real.log (D_func p x)) := by
          rw [ Real.rpow_def_of_nonneg ];
          · unfold B_v2; ring_nf; aesop;
          · positivity;
        refine le_trans h_exp_bound ?_;
        rw [ Real.rpow_def_of_pos ( by positivity ) ];
        by_cases h : Real.log ( D_func p x ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        · rcases h with ( h | h | h ) <;> norm_cast at * <;> norm_num at *;
          · norm_num [ h ];
            exact one_le_mul_of_one_le_of_one_le ( Real.one_le_exp ( by norm_num ) ) ( Real.one_le_exp ( by exact mul_nonneg ( by norm_num ) ( mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ) ) );
          · norm_num [ h ];
            exact one_le_mul_of_one_le_of_one_le ( Real.one_le_exp ( by positivity ) ) ( Real.one_le_exp ( by exact mul_nonneg ( by positivity ) ( mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ) ) );
        · rw [ ← Real.exp_add ] ; ring_nf ; norm_num;
          unfold D_func; ring_nf; norm_num;
          linarith [ Nat.floor_le ( show 0 ≤ Real.log x * ( Real.log p ) ⁻¹ by exact mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ) ];
      by_cases hp : p ≥ 2;
      · refine le_trans ?_ ( le_trans ( h_exp_bound x hx p ( Fact.out ) hp ) ?_ ) <;> norm_num;
        exact_mod_cast Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by unfold D_func; aesop ) ) ) ) ) ( Nat.floor_le ( show 0 ≤ B_v2 p x from div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( show ( 1 :ℝ ) ≤ D_func p x from Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by unfold D_func; aesop ) ) ) ) ) ) );
      · exact False.elim <| hp <| Nat.Prime.two_le Fact.out

/-
Definition of c_p(p).
-/
noncomputable def c_p (p : ℕ) : ℝ := if p > 100 then 0.66 else 0.1

/-
Inequality for the exponents: c_p(p) + 0.02 <= log(p/ceil(p/2)).
-/
theorem exponent_inequality_aux (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) :
    c_p p + 0.02 ≤ Real.log (p / Nat.ceil (p / 2 : ℝ)) := by
      rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num <;> norm_cast at *;
      · have := Fact.out ( p := Nat.Prime ( 2 * k ) ) ; norm_num [ Nat.prime_mul_iff ] at this;
        unfold c_p; norm_num [ this ];
        exact Real.log_two_gt_d9.le.trans' <| by norm_num;
      · rcases k with ( _ | _ | k ) <;> norm_num at *;
        · unfold c_p; norm_num;
          norm_num [ Real.le_log_iff_exp_le ];
          -- We can raise both sides to the power of 25 to remove the fraction.
          suffices h_exp : Real.exp 3 ≤ (3 / 2) ^ 25 by
            contrapose! h_exp;
            convert pow_lt_pow_left₀ h_exp ( by positivity ) ( by norm_num : ( 25 : ℕ ) ≠ 0 ) using 1 <;> norm_num [ ← Real.exp_nat_mul ];
            norm_num [ show ⌈ ( 3 : ℝ ) / 2⌉₊ = 2 by norm_num [ Nat.ceil_eq_iff ] ];
          have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 3 : ℝ ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ];
        · unfold c_p;
          split_ifs <;> norm_num;
          · rw [ show ( ⌈ ( 2 * ( k + 1 + 1 ) + 1 : ℝ ) / 2⌉₊ : ℝ ) = k + 1 + 1 + 1 by exact_mod_cast Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ] ; ring_nf ; norm_num;
            rw [ Real.le_log_iff_exp_le ( by positivity ) ];
            -- By simplifying, we can see that the inequality holds for $k \geq 49$.
            have h_simp : Real.exp (17 / 25) ≤ 2 - 1 / (k + 3 : ℝ) := by
              have h_simp : Real.exp (17 / 25) ≤ 2 - 1 / (50 : ℝ) := by
                rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
                rw [ div_le_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.le_log_iff_exp_le ];
                have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 17 = ( Real.exp 1 ) ^ 17 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
              exact h_simp.trans ( by gcongr ; norm_cast ; linarith );
            nlinarith [ inv_mul_cancel₀ ( by linarith : ( 3 : ℝ ) + k ≠ 0 ), one_div_mul_cancel ( by linarith : ( k : ℝ ) + 3 ≠ 0 ) ];
          · rw [ show ( ⌈ ( 2 * ( k + 1 + 1 ) + 1 : ℝ ) / 2⌉₊ : ℝ ) = k + 1 + 1 + 1 by exact_mod_cast Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ] ; ring_nf ; norm_num;
            rw [ ← Real.log_exp ( 3 / 25 ) ] ; gcongr;
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 1 : ℝ ) = 3 / 25 + 22 / 25 by norm_num, Real.exp_add ] at this ; norm_num at *;
            nlinarith [ Real.add_one_le_exp ( 3 / 25 ), Real.add_one_le_exp ( 22 / 25 ), inv_pos.mpr ( by linarith : 0 < ( 3 : ℝ ) + k ), mul_inv_cancel₀ ( by linarith : ( 3 : ℝ ) + k ≠ 0 ) ]

/-
Definition of target_bound_v2.
-/
noncomputable def target_bound_v2 (x : ℝ) (p : ℕ) : ℝ :=
  4 * p * x ^ (1 - c_p p / Real.log p)

/-
The difference in exponents is at least 0.01 / log p.
-/
noncomputable def exponent_diff (p : ℕ) : ℝ := 1 - c_p p / Real.log p - exponent_p p - 1 / (100 * Real.log p)

theorem exponent_diff_pos (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) :
    exponent_diff p ≥ 0.01 / Real.log p := by
      norm_num [ exponent_diff ] at *;
      have := exponent_inequality_aux p hp;
      rw [ Real.log_div ] at this <;> norm_num at * <;> try linarith;
      unfold exponent_p; ring_nf at *; nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ) ) ) ] ;

/-
B_v2 + 1 is bounded by 2 * x^(0.01/log p).
-/
theorem B_bound_aux (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) :
    B_v2 p x + 1 ≤ 2 * x ^ (0.01 / Real.log p) := by
      unfold B_v2; norm_num [ Real.rpow_def_of_pos ( zero_lt_three.trans_le hx ) ] ; ring_nf ;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right ( Real.add_one_le_exp _ ) zero_le_two );
      unfold D_func; norm_num; ring_nf; norm_num;
      have h_floor : (Nat.floor (Real.log x * (Real.log p)⁻¹) : ℝ) ≤ Real.log x * (Real.log p)⁻¹ := by
        exact Nat.floor_le ( mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos Fact.out ) ) ) ) );
      by_cases h : ⌊Real.log x * ( Real.log p ) ⁻¹⌋₊ = 0 <;> simp_all +decide;
      · norm_num [ show ⌊Real.log x * ( Real.log p ) ⁻¹⌋₊ = 0 by exact Nat.floor_eq_zero.mpr <| by linarith ] ; linarith;
      · have h_log_bound : Real.log (1 + ↑⌊Real.log x * (Real.log p)⁻¹⌋₊) ≥ Real.log 2 := by
          exact Real.log_le_log ( by norm_num ) ( by linarith [ show ( ⌊Real.log x * ( Real.log p ) ⁻¹⌋₊ : ℝ ) ≥ 1 by exact_mod_cast Nat.floor_pos.mpr h ] );
        have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 1 + ⌊Real.log x * ( Real.log p ) ⁻¹⌋₊ :ℝ ) > 1 by norm_cast; linarith [ Nat.floor_pos.mpr h ] ) ) ) ]

/-
Combining the bounds for the factors of bound_lemma_3_1_p_v3.
-/
theorem bound_lemma_3_1_combined (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) :
    bound_lemma_3_1_p_v3 x p ≤ 4 * Real.exp 0.02 * p * x ^ (exponent_p p + 0.01 / Real.log p + 1 / (100 * Real.log p)) := by
      have := bound_L_pow_D x p hx;
      have := B_bound_aux x p hx;
      have := bound_D_pow_B x p hx;
      convert mul_le_mul ( mul_le_mul ‹ ( ⌈ ( p : ℝ ) / 2⌉₊ : ℝ ) ^ D_func p x ≤ 2 * p * x ^ exponent_p p › ‹ B_v2 p x + 1 ≤ 2 * x ^ ( 1e-2 / Real.log p ) › _ _ ) ‹ ( D_func p x : ℝ ) ^ ⌊B_v2 p x⌋₊ ≤ Real.exp 2e-2 * x ^ ( 1 / ( 100 * Real.log p ) ) › _ _ using 1 <;> ring_nf;
      · rw [ Real.rpow_add ( by positivity ) ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      · exact add_nonneg zero_le_one ( div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( by norm_num ) ( Real.log_natCast_nonneg _ ) ) );
      · positivity;
      · positivity;
      · positivity

/-
Algebraic inequality for the exponent bound.
-/
theorem exponent_ineq_lemma (D : ℝ) (L : ℝ) (hD : D ≥ 1) (hL : L ≥ D - 1) :
    (Nat.floor (D / (100 * Real.log D)) : ℝ) * Real.log D ≤ 0.01 + L / 100 := by
      by_cases hD_log : Real.log D > 0;
      · nlinarith [ Nat.floor_le ( show 0 ≤ D / ( 100 * Real.log D ) by positivity ), mul_div_cancel₀ D ( by positivity : ( 100 * Real.log D ) ≠ 0 ) ];
      · norm_num [ show D = 1 by exact le_antisymm ( le_of_not_gt fun h => hD_log <| Real.log_pos h ) hD ] at * ; linarith

/-
The cardinality of the bad set for Lemma 3.1 is bounded by the sum of the bounds for each prime.
-/
noncomputable def total_bound_lemma_3_1_v2 (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x + 1)),
    bound_lemma_3_1_p_v3 x p

theorem bad_set_lemma_3_1_v2_card_bound (x : ℝ) (hx : x ≥ 3) :
    ((bad_set_lemma_3_1_v2 x).card : ℝ) ≤ total_bound_lemma_3_1_v2 x := by
      -- Apply the lemma that bounds the cardinality of the union of sets.
      have h_union_bound : ((bad_set_lemma_3_1_v2 x).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x + 1)), ((bad_set_lemma_3_1_p_v2 x p).card : ℝ) := by
        have h_union : bad_set_lemma_3_1_v2 x ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (2 * K_thm x + 1))) (fun p => bad_set_lemma_3_1_p_v2 x p) := by
          intro m hm
          simp [bad_set_lemma_3_1_v2, bad_set_lemma_3_1_p_v2] at hm ⊢
          obtain ⟨p, hp_prime, hp_bound⟩ := hm
          aesop
        exact_mod_cast le_trans ( Finset.card_le_card h_union ) ( Finset.card_biUnion_le );
      refine le_trans h_union_bound ?_;
      convert Finset.sum_le_sum fun p hp => lemma_3_1_p_bound_v3 x p ( show x ≥ 3 by linarith ) using 1;
      exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2 ⟩

/-
If the p-adic valuation is large, then the number is divisible by a large power of p.
-/
noncomputable def E_v2 (p : ℕ) (x : ℝ) : ℕ := Nat.floor ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) + 1

theorem lemma_divisibility_condition_v2 (p : ℕ) (x : ℝ) (m i : ℕ) :
    (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (100 * Real.log (D_func p x)) →
    p ^ (E_v2 p x) ∣ (m + i) := by
      -- If the p-adic valuation is strictly greater than X, then it is at least floor(X) + 1. Thus p^(floor(X)+1) divides the number.
      intros h_val
      have h_floor : (padicValNat p (m + i) : ℝ) ≥ (Nat.floor (D_func p x / (100 * Real.log (D_func p x))) + 1) := by
        exact_mod_cast Nat.succ_le_of_lt ( Nat.floor_lt ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( by norm_num ) ( Real.log_natCast_nonneg _ ) ) ) |>.2 h_val );
      have h_exp : p ^ (padicValNat p (m + i)) ∣ m + i := by
        exact pow_padicValNat_dvd;
      exact dvd_trans ( pow_dvd_pow _ ( mod_cast h_floor ) ) h_exp

/-
The number of integers m in [1, N] such that m+i is divisible by q is at most N/q + 1.
-/
theorem count_multiples_shifted_general (N i q : ℕ) (hq : q > 0) :
    ((Finset.Icc 1 N).filter (fun m => q ∣ (m + i))).card ≤ N / q + 1 := by
      -- Let $S$ be the set of $m \in [1, N]$ such that $q \mid (m + i)$.
      set S := Finset.filter (fun m => q ∣ m + i) (Finset.Icc 1 N);
      -- The set $S$ corresponds to multiples of $q$ in the interval $[1 + i, N + i]$.
      have h_mult : S ⊆ Finset.image (fun k => q * k - i) (Finset.Icc ((i + 1 + q - 1) / q) ((N + i) / q)) := by
        -- For any $m \in S$, there exists an integer $k$ such that $m = qk - i$.
        intro m hm
        obtain ⟨k, hk⟩ : ∃ k, m = q * k - i := by
          exact ⟨ ( m + i ) / q, by rw [ Nat.mul_div_cancel' ( Finset.mem_filter.mp hm |>.2 ) ] ; rw [ Nat.add_sub_cancel ] ⟩;
        simp +zetaDelta at *;
        exact ⟨ k, ⟨ by nlinarith [ Nat.div_mul_le_self ( i + q ) q, Nat.sub_add_cancel ( show i ≤ q * k from le_of_lt ( Nat.lt_of_sub_pos ( by linarith ) ) ) ], by nlinarith [ Nat.div_add_mod ( N + i ) q, Nat.mod_lt ( N + i ) hq, Nat.sub_add_cancel ( show i ≤ q * k from le_of_lt ( Nat.lt_of_sub_pos ( by linarith ) ) ) ] ⟩, hk.symm ⟩;
      refine le_trans ( Finset.card_le_card h_mult ) ?_;
      refine' Finset.card_image_le.trans _;
      simp +arith +decide [ Nat.add_div, hq ];
      grind

/-
The bad set for a specific p and i is contained in the set of multiples of p^E.
-/
noncomputable def bad_set_p_i_v2 (x : ℝ) (p i : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m => (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (100 * Real.log (D_func p x)))

theorem bad_set_p_i_v2_subset_multiples (x : ℝ) (p i : ℕ) :
    bad_set_p_i_v2 x p i ⊆ (Finset.Icc 1 (Nat.floor x)).filter (fun m => p ^ (E_v2 p x) ∣ (m + i)) := by
      -- By definition of bad_set_p_i_v2, if m is in this set, then v_p(m + i) is large enough that p^E divides m + i.
      intro m hm
      obtain ⟨hm_range, hm_cond⟩ := Finset.mem_filter.mp hm
      have h_div : p ^ (E_v2 p x) ∣ m + i := by
        convert lemma_divisibility_condition_v2 p x m i hm_cond using 1;
      exact Finset.mem_filter.mpr ⟨ hm_range, h_div ⟩

/-
The cardinality of the bad set for a specific p and i is bounded by x/p^E + 1.
-/
theorem bad_set_p_i_v2_card_bound (x : ℝ) (p i : ℕ) (hp : p ≥ 2) (hx : x ≥ 1) :
    ((bad_set_p_i_v2 x p i).card : ℝ) ≤ x / (p ^ (E_v2 p x) : ℝ) + 1 := by
      have h_card : ((Finset.Icc 1 (Nat.floor x)).filter (fun m => p ^ (E_v2 p x) ∣ (m + i))).card ≤ (Nat.floor x) / (p ^ (E_v2 p x)) + 1 := by
        convert count_multiples_shifted_general ( Nat.floor x ) i ( p ^ E_v2 p x ) ( pow_pos ( zero_lt_two.trans_le hp ) _ ) using 1;
      -- Since the cardinality of the bad set is less than or equal to the cardinality of the set of multiples, and the cardinality of the set of multiples is at most floor(x)/p^E + 1, we can conclude the proof.
      have h_final : ((bad_set_p_i_v2 x p i).card : ℝ) ≤ (Nat.floor x) / (p ^ (E_v2 p x)) + 1 := by
        have h_final : ((bad_set_p_i_v2 x p i).card : ℝ) ≤ ((Finset.Icc 1 (Nat.floor x)).filter (fun m => p ^ (E_v2 p x) ∣ (m + i))).card := by
          exact_mod_cast Finset.card_le_card ( bad_set_p_i_v2_subset_multiples x p i );
        refine le_trans h_final ?_;
        refine' le_trans ( Nat.cast_le.mpr h_card ) _;
        norm_num [ Nat.succ_div ];
        rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast ; exact Nat.div_mul_le_self _ _;
      exact h_final.trans ( add_le_add_right ( div_le_div_of_nonneg_right ( Nat.floor_le ( by positivity ) ) ( by positivity ) ) _ )

/-
The cardinality of the bad set for Lemma 3.2 is bounded by the sum of the bounds for each prime and index.
-/
noncomputable def total_bound_lemma_3_2_v2 (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x)),
    ∑ i ∈ Finset.Icc 1 (K_thm x), (x / (p ^ (E_v2 p x) : ℝ) + 1)

theorem bad_set_lemma_3_2_v2_card_bound (x : ℝ) (hx : x ≥ 3) :
    ((bad_set_lemma_3_2_v2 x).card : ℝ) ≤ total_bound_lemma_3_2_v2 x := by
      have h_bad_set_lemma_3_2_v2_card_le_sum : ((bad_set_lemma_3_2_v2 x).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x)), ∑ i ∈ Finset.Icc 1 (K_thm x), ((Finset.Icc 1 (Nat.floor x)).filter (fun m => padicValNat p (m + i) > B_v2 p x)).card := by
        refine' mod_cast le_trans ( Finset.card_le_card _ ) _;
        exact Finset.biUnion ( Finset.filter Nat.Prime ( Finset.range ( 2 * K_thm x ) ) ) fun p => Finset.biUnion ( Finset.Icc 1 ( K_thm x ) ) fun i => Finset.filter ( fun m => ( padicValNat p ( m + i ) : ℝ ) > B_v2 p x ) ( Finset.Icc 1 ⌊x⌋₊ );
        · intro m hm; unfold bad_set_lemma_3_2_v2 at hm; aesop;
        · refine' le_trans ( Finset.card_biUnion_le ) _;
          exact Finset.sum_le_sum fun p hp => Finset.card_biUnion_le.trans ( by aesop );
      refine le_trans h_bad_set_lemma_3_2_v2_card_le_sum ?_;
      push_cast [ Finset.sum_div, Finset.sum_add_distrib ];
      simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun i hi => bad_set_p_i_v2_card_bound x p i ( Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ) ( by linarith )

/-
Upper bound for D in terms of log x.
-/
theorem D_le_three_log_x (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 10) :
    (D_func p x : ℝ) ≤ 3 * Real.log x := by
      have hD_bound : (D_func p x : ℝ) ≤ 1 + Real.log x / Real.log 2 := by
        have hD_upper : (D_func p x : ℝ) ≤ 1 + Real.log x / Real.log p := by
          unfold D_func;
          norm_num +zetaDelta at *;
          exact Nat.floor_le ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos Fact.out ) ) ) );
        exact hD_upper.trans ( add_le_add_left ( div_le_div_of_nonneg_left ( Real.log_nonneg ( by linarith ) ) ( Real.log_pos ( by norm_num ) ) ( Real.log_le_log ( by norm_num ) ( Nat.cast_le.mpr ( Nat.Prime.two_le Fact.out ) ) ) ) _ );
      have h_log_bound : Real.log 2 > 1 / 2 := by
        exact Real.log_two_gt_d9.trans_le' <| by norm_num;
      nlinarith [ show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ), div_mul_cancel₀ ( Real.log x ) ( ne_of_gt ( Real.log_pos one_lt_two ) ) ]

/-
D is at least 2 for x >= 10.
-/
theorem D_ge_two (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 10) (hp : p ∈ Finset.range (2 * K_thm x)) :
    D_func p x ≥ 2 := by
      -- Since $p < 2 \exp(0.8 \sqrt{\log x})$, we have $\log p < 0.8 \sqrt{\log x} + \log 2$.
      have h_log_p : Real.log p < 0.8 * Real.sqrt (Real.log x) + Real.log 2 := by
        have h_log_p : Real.log p < Real.log (2 * Real.exp (0.8 * Real.sqrt (Real.log x))) := by
          gcongr;
          · exact Nat.cast_pos.mpr ( Nat.Prime.pos Fact.out );
          · exact lt_of_lt_of_le ( Nat.cast_lt.mpr <| Finset.mem_range.mp hp ) <| by norm_num [ K_thm ] ; linarith [ Nat.floor_le <| show 0 ≤ Real.exp ( 0.8 * Real.sqrt ( Real.log x ) ) by positivity ] ;
        rwa [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp, add_comm ] at h_log_p;
      refine' Nat.succ_le_of_lt ( Nat.lt_add_of_pos_right _ );
      refine' Nat.floor_pos.mpr _;
      rw [ one_le_div ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out ) ];
      have h_log_x_ge_2 : Real.log x ≥ 2 := by
        rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
        exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 2:ℝ ) = 1+1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ] ) hx;
      have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.sq_sqrt ( show 0 ≤ Real.log x by linarith ) ]

/-
p^D is strictly greater than x.
-/
noncomputable def exponent_delta_v2 (x : ℝ) : ℝ := 1 / (100 * Real.log (3 * Real.log x))

theorem p_pow_D_gt_x (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 10) :
    (p : ℝ) ^ (D_func p x) > x := by
      have hpD_ineq : (D_func p x : ℝ) * Real.log p > Real.log x := by
        unfold D_func;
        norm_num +zetaDelta at *;
        nlinarith [ Nat.lt_floor_add_one ( Real.log x / Real.log p ), Real.log_pos ( show ( p : ℝ ) > 1 by exact_mod_cast Nat.Prime.one_lt Fact.out ), Real.log_pos ( show ( x : ℝ ) > 1 by linarith ), mul_div_cancel₀ ( Real.log x ) ( ne_of_gt ( Real.log_pos ( show ( p : ℝ ) > 1 by exact_mod_cast Nat.Prime.one_lt Fact.out ) ) ) ];
      rw [ gt_iff_lt, ← Real.log_lt_log_iff ( by positivity ) ( by exact pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ), Real.log_pow ] ; aesop

/-
Lower bound for p^E in terms of x.
-/
noncomputable def exponent_delta_v3 (x : ℝ) : ℝ := 1 / (100 * Real.log (3 * Real.log x))

theorem p_pow_E_lower_bound (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 10) (hp : p ∈ Finset.range (2 * K_thm x)) :
    (p : ℝ) ^ (E_v2 p x) ≥ x ^ (exponent_delta_v3 x) := by
      -- By definition of $E_v2$, we have $p^{E_v2 p x} > (p^D)^{\frac{1}{100 \log D}}$.
      have h_exp : (p : ℝ) ^ (E_v2 p x) > (p ^ (D_func p x) : ℝ) ^ (1 / (100 * Real.log (D_func p x))) := by
        have h_exp : (p : ℝ) ^ (E_v2 p x) > (p : ℝ) ^ ((D_func p x : ℝ) / (100 * Real.log (D_func p x))) := by
          have h_exp : (E_v2 p x : ℝ) > (D_func p x : ℝ) / (100 * Real.log (D_func p x)) := by
            exact Nat.lt_succ_floor (↑(D_func p x) / (100 * log ↑(D_func p x)));
          exact_mod_cast Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out ) h_exp;
        convert h_exp using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
      -- Since $p^D > x$, we have $(p^D)^{\frac{1}{100 \log D}} > x^{\frac{1}{100 \log D}}$.
      have h_exp_gt_x : (p ^ (D_func p x) : ℝ) ^ (1 / (100 * Real.log (D_func p x))) > x ^ (1 / (100 * Real.log (D_func p x))) := by
        exact Real.rpow_lt_rpow ( by positivity ) ( p_pow_D_gt_x x p hx ) ( one_div_pos.mpr <| mul_pos ( by positivity ) <| Real.log_pos <| mod_cast D_ge_two x p hx hp );
      -- Since $D \leq 3 \log x$, we have $\frac{1}{100 \log D} \geq \frac{1}{100 \log(3 \log x)}$.
      have h_log_bound : 1 / (100 * Real.log (D_func p x)) ≥ 1 / (100 * Real.log (3 * Real.log x)) := by
        gcongr;
        · exact mul_pos ( by norm_num ) ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ D_ge_two x p hx hp ] );
        · refine' Nat.cast_pos.mpr ( Nat.pos_of_ne_zero _ ) ; aesop;
        · convert D_le_three_log_x x p ( by linarith ) using 1;
      exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) h_log_bound ) ( le_of_lt ( lt_of_le_of_lt ( by norm_num ) h_exp_gt_x ) |> le_trans <| le_of_lt h_exp )

/-
Split the total bound into two terms.
-/
noncomputable def term_1 (x : ℝ) : ℝ :=
  (K_thm x : ℝ) * x * ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x)), (p : ℝ) ^ (-(E_v2 p x : ℝ))

noncomputable def term_2 (x : ℝ) : ℝ :=
  (K_thm x : ℝ) * (Finset.filter Nat.Prime (Finset.range (2 * K_thm x))).card

theorem total_bound_split (x : ℝ) :
    total_bound_lemma_3_2_v2 x = term_1 x + term_2 x := by
      unfold total_bound_lemma_3_2_v2 term_1 term_2;
      norm_num [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_add, mul_assoc, mul_comm, mul_left_comm, Real.rpow_neg ];
      exact Finset.sum_congr rfl fun _ _ => by ring;

/-
Bound the sum of p^(-E).
-/
theorem sum_p_pow_neg_E_bound (x : ℝ) (hx : x ≥ 10) :
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x)), (p : ℝ) ^ (-(E_v2 p x : ℝ)) ≤ (2 * K_thm x : ℝ) * x ^ (-(exponent_delta_v3 x)) := by
      have h_sum_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x)), (p : ℝ) ^ (-(E_v2 p x : ℝ)) ≤ x ^ (-exponent_delta_v3 x) := by
        intro p hp
        have h_p_pow_E : (p : ℝ) ^ (E_v2 p x) ≥ x ^ (exponent_delta_v3 x) := by
          convert p_pow_E_lower_bound x p _ _;
          · exact ⟨ Finset.mem_filter.mp hp |>.2 ⟩;
          · grind;
          · exact Finset.mem_filter.mp hp |>.1;
        rw [ Real.rpow_neg ( by positivity ), Real.rpow_neg ( by positivity ) ] ; gcongr;
        exact_mod_cast h_p_pow_E;
      refine' le_trans ( Finset.sum_le_sum h_sum_bound ) _;
      norm_num [ mul_comm ];
      exact mul_le_mul_of_nonneg_left ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( by positivity )

/-
Bound for term_1.
-/
theorem term_1_bound (x : ℝ) (hx : x ≥ 10) :
    term_1 x ≤ 2 * (K_thm x : ℝ)^2 * x ^ (1 - exponent_delta_v3 x) := by
      convert mul_le_mul_of_nonneg_left ( sum_p_pow_neg_E_bound x hx ) ( show ( 0 :ℝ ) ≤ ( K_thm x :ℝ ) * x by exact mul_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) using 1 ; ring_nf!;
      rw [ Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring_nf;
      rw [ Real.rpow_neg ( by positivity ) ]

/-
Bound for term_2.
-/
theorem term_2_bound (x : ℝ) (hx : x ≥ 10) :
    term_2 x ≤ 2 * (K_thm x : ℝ)^2 := by
      -- The number of primes less than $2K$ is at most $2K$.
      have h_prime_count : (Finset.filter Nat.Prime (Finset.range (2 * K_thm x))).card ≤ 2 * (K_thm x : ℕ) := by
        exact le_trans ( Finset.card_filter_le _ _ ) ( by simpa );
      exact le_trans ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr h_prime_count ) ( Nat.cast_nonneg _ ) ) ( by norm_num; nlinarith )

/-
K^2 is o(x).
-/
theorem K_sq_is_little_o_v2 :
    (fun x => (K_thm x : ℝ)^2) =o[Filter.atTop] (fun x => x) := by
      refine' Asymptotics.isLittleO_iff.2 fun ε hε => _;
      -- We'll use the fact that $K(x)^2 \leq \exp(1.6 \sqrt{\log x})$ and $\exp(1.6 \sqrt{\log x}) / x \to 0$ as $x \to \infty$.
      have h_exp : Filter.Tendsto (fun x : ℝ => Real.exp (1.6 * Real.sqrt (Real.log x)) / x) Filter.atTop (nhds 0) := by
        -- We can rewrite the limit expression using the substitution $y = \log x$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (1.6 * Real.sqrt y) / Real.exp y) Filter.atTop (nhds 0) by
          have := h_log.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        norm_num [ ← Real.exp_sub ];
        rw [ Filter.tendsto_atTop_atBot ];
        exact fun b => ⟨ 25 * |b| + 25, fun x hx => by cases abs_cases b <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] ⟩;
      -- Since $K(x)^2 \leq \exp(1.6 \sqrt{\log x})$, we can use the fact that $\exp(1.6 \sqrt{\log x}) / x \to 0$ to conclude.
      have h_bound : ∀ᶠ x in Filter.atTop, (K_thm x : ℝ) ^ 2 ≤ Real.exp (1.6 * Real.sqrt (Real.log x)) := by
        refine' Filter.eventually_atTop.mpr ⟨ 10, fun x hx => _ ⟩ ; norm_num [ K_thm ];
        exact le_trans ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.floor_le ( Real.exp_nonneg _ ) ) _ ) ( by rw [ ← Real.exp_nat_mul ] ; ring_nf; norm_num );
      filter_upwards [ h_bound, h_exp.eventually ( gt_mem_nhds <| show 0 < ε by positivity ), Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ hx₃ using by rw [ Real.norm_of_nonneg <| sq_nonneg _, Real.norm_of_nonneg hx₃.le ] ; nlinarith [ mul_div_cancel₀ ( Real.exp ( 1.6 * Real.sqrt ( Real.log x ) ) ) hx₃.ne' ] ;

/-
term_2 is o(x).
-/
theorem term_2_is_little_o :
    term_2 =o[Filter.atTop] (fun x => x) := by
      refine' Asymptotics.isLittleO_iff.mpr _ ; norm_num;
      -- Since $K^2$ is $o(x)$, we have $\lim_{x \to \infty} \frac{K^2}{x} = 0$. Therefore, for any $\epsilon > 0$, there exists $a$ such that for all $b \geq a$, $\frac{K^2}{b} < \epsilon$.
      have h_term2_o_x : Filter.Tendsto (fun x : ℝ => (K_thm x : ℝ)^2 / x) Filter.atTop (nhds 0) := by
        convert K_sq_is_little_o_v2 using 1;
        rw [ Asymptotics.isLittleO_iff_tendsto' ] ; norm_num;
        exact ⟨ 1, by intros; linarith ⟩;
      intro ε hε_pos
      obtain ⟨a, ha⟩ : ∃ a, ∀ b ≥ a, (K_thm b : ℝ)^2 / b < ε / 2 := by
        simpa using h_term2_o_x.eventually ( gt_mem_nhds <| half_pos hε_pos ) |> fun h => Filter.eventually_atTop.mp h |> fun ⟨ a, ha ⟩ => ⟨ a, fun b hb => ha b hb ⟩;
      use Max.max a 10; intro b hb; specialize ha b ( le_trans ( le_max_left _ _ ) hb ) ; rw [ div_lt_iff₀ ] at ha <;> norm_num at * <;> try linarith;
      rw [ abs_of_nonneg, abs_of_nonneg ] <;> nlinarith [ show ( Finset.card ( Finset.filter Nat.Prime ( Finset.range ( 2 * K_thm b ) ) ) : ℝ ) ≤ 2 * K_thm b by exact_mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ), show ( term_2 b : ℝ ) = ( K_thm b : ℝ ) * ( Finset.card ( Finset.filter Nat.Prime ( Finset.range ( 2 * K_thm b ) ) ) : ℝ ) by rfl ]

/-
The exponent in the bound for term_1 goes to -infinity.
-/
theorem exponent_limit :
    Filter.Tendsto (fun x : ℝ => 1.6 * Real.sqrt (Real.log x) - Real.log x / (100 * Real.log (3 * Real.log x))) Filter.atTop Filter.atBot := by
      -- Let $y = \log x$. As $x \to \infty$, $y \to \infty$.
      suffices h_y : Filter.Tendsto (fun y => 1.6 * Real.sqrt y - y / (100 * Real.log (3 * y))) Filter.atTop Filter.atBot by
        exact h_y.comp ( Real.tendsto_log_atTop );
      -- We can factor out $y^{1/2}$ from the expression.
      suffices h_factor : Filter.Tendsto (fun y => y ^ (1 / 2 : ℝ) * (1.6 - 1 / (100 * Real.log (3 * y)) * y ^ (1 / 2 : ℝ))) Filter.atTop Filter.atBot by
        refine h_factor.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx ; norm_num [ ← Real.sqrt_eq_rpow, hx.le ] ; ring_nf;
        rw [ Real.sq_sqrt hx.le ];
      -- We'll use the fact that $1 / (100 * \log(3y)) * y^{1/2}$ tends to infinity as $y$ tends to infinity.
      have h_term : Filter.Tendsto (fun y => 1 / (100 * Real.log (3 * y)) * y ^ (1 / 2 : ℝ)) Filter.atTop Filter.atTop := by
        -- We can factor out $y^{1/2}$ and use the fact that $\frac{1}{\log(3y)}$ tends to $0$ as $y$ tends to infinity.
        suffices h_factor : Filter.Tendsto (fun y => y ^ (1 / 2 : ℝ) / Real.log (3 * y)) Filter.atTop Filter.atTop by
          convert h_factor.const_mul_atTop ( show ( 0 : ℝ ) < 1 / 100 by norm_num ) using 2 ; ring;
        -- We can use the change of variables $u = \log y$ to transform the limit expression.
        suffices h_log : Filter.Tendsto (fun u => Real.exp (u / 2) / (u + Real.log 3)) Filter.atTop Filter.atTop by
          have h_log : Filter.Tendsto (fun y => Real.exp (Real.log y / 2) / (Real.log y + Real.log 3)) Filter.atTop Filter.atTop := by
            exact h_log.comp Real.tendsto_log_atTop;
          refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Real.rpow_def_of_pos hy ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring_nf );
        -- We can use the fact that $\exp(u/2) / u$ tends to infinity as $u$ tends to infinity.
        have h_exp_div_u : Filter.Tendsto (fun u => Real.exp (u / 2) / u) Filter.atTop Filter.atTop := by
          have := Real.tendsto_exp_div_pow_atTop 1;
          have := this.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2⁻¹ : ℝ ) ) );
          convert this.const_mul_atTop ( by norm_num : ( 0 : ℝ ) < 2⁻¹ ) using 2 ; norm_num ; ring_nf;
        -- We can use the fact that $u + \log 3 \sim u$ as $u \to \infty$.
        have h_log : Filter.Tendsto (fun u => (u + Real.log 3) / u) Filter.atTop (nhds 1) := by
          norm_num [ add_div ];
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with u hu; aesop ) ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( by norm_num );
        have h_combined : Filter.Tendsto (fun u => (Real.exp (u / 2) / u) * (u / (u + Real.log 3))) Filter.atTop Filter.atTop := by
          apply Filter.Tendsto.atTop_mul_pos;
          exacts [ zero_lt_one, h_exp_div_u, by simpa using h_log.inv₀ ];
        refine h_combined.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with u hu using by rw [ div_mul_div_cancel₀ hu.ne' ] );
      rw [ Filter.tendsto_atTop_atBot ];
      rw [ Filter.tendsto_atTop_atTop ] at h_term;
      exact fun b => by obtain ⟨ i, hi ⟩ := h_term ( |b| + 1.6 ) ; exact ⟨ Max.max i 1, fun x hx => by cases abs_cases b <;> nlinarith [ hi x ( le_trans ( le_max_left _ _ ) hx ), Real.one_le_rpow ( show 1 ≤ x by linarith [ le_max_right i 1 ] ) ( show ( 1 / 2 : ℝ ) ≥ 0 by norm_num ) ] ⟩ ;

/-
term_1 is o(x).
-/
theorem term_1_is_little_o :
    term_1 =o[Filter.atTop] (fun x => x) := by
      -- Using the bounds from `term_1_bound` and `K_sq_is_little_o_v2`, we conclude `term_1 x = o(x)`.
      have h_term_1_critical : term_1 =O[Filter.atTop] (fun x : ℝ => (K_thm x : ℝ) ^ 2 * x ^ (1 - exponent_delta_v3 x)) := by
        refine' Asymptotics.IsBigO.of_bound 2 _;
        filter_upwards [ Filter.eventually_ge_atTop 10 ] with x hx;
        rw [ Real.norm_of_nonneg, Real.norm_of_nonneg ] <;> try positivity;
        · convert term_1_bound x hx using 1 ; ring;
        · exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
      -- Using the bounds from `K_sq_is_little_o_v2` and `exponent_limit`, we conclude `term_1 x = o(x)`.
      have h_term_1_lim : Filter.Tendsto (fun x : ℝ => ((K_thm x : ℝ) ^ 2 * x ^ (1 - exponent_delta_v3 x)) / x) Filter.atTop (nhds 0) := by
        -- Using the fact that $K_thm x = \exp(0.8 \sqrt{\log x})$, we can rewrite the expression.
        suffices h_exp : Filter.Tendsto (fun x : ℝ => Real.exp (1.6 * Real.sqrt (Real.log x) - Real.log x / (100 * Real.log (3 * Real.log x)))) Filter.atTop (nhds 0) by
          have h_exp : Filter.Tendsto (fun x : ℝ => (Real.exp (0.8 * Real.sqrt (Real.log x))) ^ 2 * x ^ (1 - exponent_delta_v3 x) / x) Filter.atTop (nhds 0) := by
            refine h_exp.congr' ?_;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx ; rw [ ← Real.exp_nat_mul ] ; rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
            rw [ ← Real.exp_add, ← Real.exp_log ( by positivity : 0 < x ) ] ; ring_nf!;
            unfold exponent_delta_v3; norm_num [ ← Real.exp_add, ← Real.exp_neg ] ; ring_nf;
          refine' squeeze_zero_norm' _ h_exp;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx ; rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; norm_num [ K_thm ];
          exact Nat.floor_le <| by positivity;
        exact Real.tendsto_exp_atBot.comp <| by simpa using exponent_limit;
      rw [ Asymptotics.isLittleO_iff ];
      rw [ Asymptotics.isBigO_iff' ] at h_term_1_critical;
      intro ε hε_pos; rcases h_term_1_critical with ⟨ c, hc_pos, hc ⟩ ; filter_upwards [ hc, h_term_1_lim.eventually ( Metric.ball_mem_nhds _ <| show 0 < ε / c by positivity ), Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ hx₃; simp_all +decide [ abs_of_nonneg, div_le_iff₀ ] ;
      rw [ div_lt_div_iff₀ ] at hx₂ <;> cases abs_cases x <;> cases abs_cases ( x ^ ( 1 - exponent_delta_v3 x ) ) <;> first | positivity | nlinarith;

/-
The total bound for Lemma 3.2 is o(x).
-/
theorem total_bound_lemma_3_2_v2_is_little_o :
    total_bound_lemma_3_2_v2 =o[Filter.atTop] (fun x => x) := by
      -- The sum of two little-o functions is also little-o.
      have sum_little_o : ∀ {f g : ℝ → ℝ}, f =o[Filter.atTop] (fun x => x) → g =o[Filter.atTop] (fun x => x) → (fun x => f x + g x) =o[Filter.atTop] (fun x => x) := by
        exact fun { f g } hf hg => hf.add hg;
      exact sum_little_o ( term_1_is_little_o ) ( term_2_is_little_o ) |> fun h => h.congr ( fun x => by rw [ total_bound_split ] ) ( by norm_num )

/-
Define K_small(x) = floor(exp(0.5 * sqrt(log x))).
-/
noncomputable def K_small (x : ℝ) : ℕ := Nat.floor (Real.exp (0.5 * Real.sqrt (Real.log x)))

/-
Define the bad sets for Theorem 1.2 with K_small.
-/
noncomputable def bad_set_lemma_3_1_small (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_small x + 1), p.Prime ∧
      (padicValNat p (Nat.choose (2 * m) m) : ℝ) ≤ (D_func p x : ℝ) / (100 * Real.log (D_func p x)))

noncomputable def bad_set_lemma_3_2_small (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * K_small x + 1), p.Prime ∧
      ∃ i ∈ Finset.Icc 1 (K_small x), (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (100 * Real.log (D_func p x)))

noncomputable def bad_set_thm_1_2_small (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ k ∈ Finset.Icc 1 (K_small x), ¬ (Nat.choose (m + k) k ∣ Nat.choose (2 * m) m))

/-
If divisibility fails, there is a small witnessing prime.
-/
theorem exists_witness_prime_small (m k : ℕ) (hk : k ≥ 1) :
    ¬ (Nat.choose (m + k) k ∣ Nat.choose (2 * m) m) →
    ∃ p, p.Prime ∧ p ≤ 2 * k ∧ padicValNat p (Nat.choose (m + k) k) > padicValNat p (Nat.choose (2 * m) m) := by
      intro hdiv
      obtain ⟨p, hp_prime, hp_val⟩ : ∃ p, Nat.Prime p ∧ (padicValNat p (Nat.choose (m + k) k)) > (padicValNat p (Nat.choose (2 * m) m)) := by
        contrapose! hdiv with h;
        rw [ ← Nat.factorization_le_iff_dvd ];
        · intro p; by_cases pp : Nat.Prime p <;> simp_all +decide [ Nat.factorization ] ;
        · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
        · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
      refine' ⟨ p, hp_prime, _, hp_val ⟩
      have h_p_le_2k : p ≤ 2 * k := by
        have h_div : p ∣ (Nat.choose (m + k) k) := by
          contrapose! hp_val;
          rw [ padicValNat.eq_zero_of_not_dvd hp_val ] ; norm_num
        by_cases h_cases : p > 2 * k;
        · have h_contradiction : (padicValNat p (Nat.choose (2 * m) m)) ≥ (padicValNat p (Nat.choose (m + k) k)) := by
            have h_contradiction : ∀ {m k : ℕ}, k ≥ 1 → Nat.Prime p → p > 2 * k → p ∣ Nat.choose (m + k) k → (padicValNat p (Nat.choose (2 * m) m)) ≥ (padicValNat p (Nat.choose (m + k) k)) := by
              intros m k hk hp_prime hp_gt_2k hp_div
              have h_contradiction : (padicValNat p (Nat.choose (m + k) k)) ≤ (padicValNat p (Nat.choose (2 * m) m)) := by
                convert lemma_large_primes m k p _ _ using 1 <;> tauto
              exact h_contradiction;
            exact h_contradiction hk hp_prime h_cases h_div;
          linarith;
        · linarith
      exact h_p_le_2k

/-
If m is not in the bad sets, the valuation bounds hold.
-/
noncomputable def B_small (p : ℕ) (x : ℝ) : ℝ := (D_func p x : ℝ) / (100 * Real.log (D_func p x))

theorem bounds_of_not_bad (x : ℝ) (m : ℕ) (p : ℕ) [Fact p.Prime]
    (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hp : p ∈ Finset.range (2 * K_small x + 1))
    (h_not_bad_1 : m ∉ bad_set_lemma_3_1_small x)
    (h_not_bad_2 : m ∉ bad_set_lemma_3_2_small x) :
    (padicValNat p (Nat.choose (2 * m) m) : ℝ) > B_small p x ∧
    ∀ i ∈ Finset.Icc 1 (K_small x), (padicValNat p (m + i) : ℝ) ≤ B_small p x := by
      unfold bad_set_lemma_3_1_small bad_set_lemma_3_2_small at *;
      simp +zetaDelta at *;
      exact ⟨ h_not_bad_1 hm.1 hm.2 p hp ( Fact.out ) |> fun h => by unfold B_small; exact h, fun i hi₁ hi₂ => h_not_bad_2 hm.1 hm.2 p hp ( Fact.out ) i hi₁ hi₂ ⟩

/-
General bound for the valuation of the binomial coefficient.
-/
theorem lemma_valuation_binom_le_max_general (m k : ℕ) (p : ℕ) [Fact p.Prime] (hk : k > 0) :
    padicValNat p (Nat.choose (m + k) k) ≤ Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
      -- Using the lemma_2_3_descFactorial, we have v_p((m+k)_k) ≤ v_p(k!) + max v_p(m+i).
      have h_desc_factorial : (padicValNat p (Nat.descFactorial (m + k) k)) ≤ (padicValNat p (Nat.factorial k)) + (Finset.Icc 1 k).sup (fun i => padicValNat p (m + i)) := by
        exact lemma_2_3_descFactorial_v2 m k p hk;
      rw [ Nat.descFactorial_eq_factorial_mul_choose ] at h_desc_factorial;
      rw [ padicValNat.mul ( Nat.factorial_ne_zero _ ) ( Nat.ne_of_gt ( Nat.choose_pos ( by linarith ) ) ) ] at h_desc_factorial ; linarith!

/-
If m is not in the second bad set, the valuation of the binomial coefficient is small.
-/
theorem valuation_binom_small_of_not_bad (x : ℝ) (m : ℕ) (k : ℕ) (p : ℕ) [Fact p.Prime]
    (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hk : k ∈ Finset.Icc 1 (K_small x))
    (hp : p ∈ Finset.range (2 * K_small x + 1))
    (h_not_bad : m ∉ bad_set_lemma_3_2_small x) :
    (padicValNat p (Nat.choose (m + k) k) : ℝ) ≤ B_small p x := by
      -- Unfold `bad_set_lemma_3_2_small`. Since $m$ is not in it, for all $p'$ in range and $i \in [1, K]$, $v_{p'}(m+i) \le B$.
      have h_bound : ∀ p' ∈ Finset.range (2 * K_small x + 1), p'.Prime → ∀ i ∈ Finset.Icc 1 (K_small x), (padicValNat p' (m + i) : ℝ) ≤ B_small p' x := by
        unfold bad_set_lemma_3_2_small at h_not_bad; aesop;
      -- Apply the lemma that states the valuation of a binomial coefficient is less than or equal to the maximum valuation of the factors.
      have h_val_binom_le_max : padicValNat p (Nat.choose (m + k) k) ≤ Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
        convert lemma_valuation_binom_le_max_general m k p _ using 1;
        linarith [ Finset.mem_Icc.mp hk ];
      refine' le_trans ( Nat.cast_le.mpr h_val_binom_le_max ) _;
      simp +zetaDelta at *;
      convert h_bound p hp Fact.out ( Classical.choose ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ k, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩ ) ) ( Classical.choose_spec ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ k, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩ ) |>.1 |> Finset.mem_Icc.mp |>.1 ) ( Classical.choose_spec ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ k, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩ ) |>.1 |> Finset.mem_Icc.mp |>.2.trans ( by linarith ) ) using 1 ; norm_cast;
      exact le_antisymm ( Finset.sup_le fun i hi => Classical.choose_spec ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ k, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩ ) |>.2 i hi ) ( Finset.le_sup ( f := fun i => padicValNat p ( m + i ) ) ( Classical.choose_spec ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ k, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩ ) |>.1 ) )

/-
If m is not in the first bad set, the valuation of the middle binomial coefficient is large.
-/
theorem valuation_binom_large_of_not_bad (x : ℝ) (m : ℕ) (p : ℕ) [Fact p.Prime]
    (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hp : p ∈ Finset.range (2 * K_small x + 1))
    (h_not_bad : m ∉ bad_set_lemma_3_1_small x) :
    (padicValNat p (Nat.choose (2 * m) m) : ℝ) > B_small p x := by
      -- Since $m$ is not in the bad set, there does not exist any prime $p'$ in the range such that the valuation of the binomial coefficient is small.
      have h_no_prime : ∀ p' ∈ Finset.range (2 * K_small x + 1), p'.Prime → (padicValNat p' (Nat.choose (2 * m) m) : ℝ) > B_small p' x := by
        unfold bad_set_lemma_3_1_small at h_not_bad; contrapose! h_not_bad; aesop;
      exact h_no_prime p hp ( Fact.out )

/-
If m is not in the bad sets, the valuation of the small binomial coefficient is strictly less than the valuation of the middle binomial coefficient.
-/
theorem valuation_inequality_of_not_bad (x : ℝ) (m : ℕ) (k : ℕ) (p : ℕ) [Fact p.Prime]
    (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hk : k ∈ Finset.Icc 1 (K_small x))
    (hp : p ∈ Finset.range (2 * K_small x + 1))
    (h_not_bad_1 : m ∉ bad_set_lemma_3_1_small x)
    (h_not_bad_2 : m ∉ bad_set_lemma_3_2_small x) :
    (padicValNat p (Nat.choose (m + k) k) : ℝ) < (padicValNat p (Nat.choose (2 * m) m) : ℝ) := by
      have h_bound : (padicValNat p (Nat.choose (m + k) k) : ℝ) ≤ B_small p x ∧ B_small p x < (padicValNat p (Nat.choose (2 * m) m) : ℝ) := by
        exact ⟨ valuation_binom_small_of_not_bad x m k p hm hk hp h_not_bad_2, valuation_binom_large_of_not_bad x m p hm hp h_not_bad_1 ⟩
      generalize_proofs at *; (
      convert h_bound.1.trans_lt h_bound.2 using 1)

/-
For any prime p, the valuation of the small binomial coefficient is less than or equal to the valuation of the middle binomial coefficient.
-/
theorem valuation_le_for_all_p (x : ℝ) (m : ℕ) (k : ℕ) (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hk : k ∈ Finset.Icc 1 (K_small x))
    (h_not_bad_1 : m ∉ bad_set_lemma_3_1_small x)
    (h_not_bad_2 : m ∉ bad_set_lemma_3_2_small x) :
    ∀ p, p.Prime → padicValNat p (Nat.choose (m + k) k) ≤ padicValNat p (Nat.choose (2 * m) m) := by
      -- Let $p$ be a prime.
      intro p hp;
      by_cases hp_le : p ≤ 2 * K_small x;
      · have h_val_ineq : (padicValNat p (Nat.choose (m + k) k) : ℝ) < (padicValNat p (Nat.choose (2 * m) m) : ℝ) := by
          convert valuation_inequality_of_not_bad x m k p _ _ _ _ _;
          exacts [ ⟨ hp ⟩, hm, hk, Finset.mem_range.mpr ( Nat.lt_succ_of_le hp_le ), h_not_bad_1, h_not_bad_2 ];
        exact_mod_cast h_val_ineq.le;
      · have := @lemma_large_primes;
        convert this m k p ( Finset.mem_Icc.mp hk |>.1 ) ( by linarith [ Finset.mem_Icc.mp hk |>.2 ] ) using 1;
        exact ⟨ hp ⟩

/-
The bad set for Theorem 1.2 is contained in the union of the auxiliary bad sets.
-/
theorem bad_set_thm_1_2_small_subset (x : ℝ) :
    bad_set_thm_1_2_small x ⊆ bad_set_lemma_3_1_small x ∪ bad_set_lemma_3_2_small x := by
      intro m hm; simp_all +decide [ Finset.ext_iff, Set.subset_def ] ;
      by_cases h1 : m ∈ bad_set_lemma_3_1_small x <;> by_cases h2 : m ∈ bad_set_lemma_3_2_small x <;> simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
      have h_div : ∀ p : ℕ, p.Prime → padicValNat p (Nat.choose (m + (Classical.choose (Finset.mem_filter.mp hm).right)) (Classical.choose (Finset.mem_filter.mp hm).right)) ≤ padicValNat p (Nat.choose (2 * m) m) := by
        apply valuation_le_for_all_p;
        any_goals assumption;
        · exact Finset.mem_filter.mp hm |>.1;
        · exact Classical.choose_spec ( Finset.mem_filter.mp hm |>.2 ) |>.1;
      have h_div : Nat.choose (m + (Classical.choose (Finset.mem_filter.mp hm).right)) (Classical.choose (Finset.mem_filter.mp hm).right) ∣ Nat.choose (2 * m) m := by
        rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
        · intro p; by_cases hp : Nat.Prime p <;> simp_all +decide [ Nat.factorization ] ;
        · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ Classical.choose_spec ( Finset.mem_filter.mp hm |>.2 ) |>.1 ] ;
        · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
      have := Classical.choose_spec ( Finset.mem_filter.mp hm |>.2 ) ; aesop;

/-
Define the divisibility property for Theorem 1.2 with K_small.
-/
def property_thm_1_2_small (x : ℝ) (m : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (K_small x), Nat.choose (m + k) k ∣ Nat.choose (2 * m) m

/-
K_small is less than or equal to K_thm.
-/
theorem K_small_le_K_thm (x : ℝ) (hx : x ≥ 1) : K_small x ≤ K_thm x := by
  exact Nat.floor_mono <| Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_right ( by norm_num ) <| Real.sqrt_nonneg _

/-
The cardinality of the small bad set for Lemma 3.1 is bounded by the sum of the bounds.
-/
noncomputable def total_bound_lemma_3_1_small_func (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1)),
    bound_lemma_3_1_p_v3 x p

theorem bad_set_lemma_3_1_small_card_bound (x : ℝ) (hx : x ≥ 3) :
    ((bad_set_lemma_3_1_small x).card : ℝ) ≤ total_bound_lemma_3_1_small_func x := by
      have h_union_bound : ((bad_set_lemma_3_1_small x).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1)), ((bad_set_lemma_3_1_p_v2 x p).card : ℝ) := by
        have h_union : bad_set_lemma_3_1_small x ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1))) (fun p => bad_set_lemma_3_1_p_v2 x p) := by
          intro m hm
          simp [bad_set_lemma_3_1_small, bad_set_lemma_3_1_p_v2, B_v2] at hm ⊢
          obtain ⟨p, hp_prime, hp_bound⟩ := hm
          aesop
        exact_mod_cast le_trans ( Finset.card_le_card h_union ) ( Finset.card_biUnion_le );
      refine le_trans h_union_bound ?_;
      convert Finset.sum_le_sum fun p hp => lemma_3_1_p_bound_v3 x p ( show x ≥ 3 by linarith ) using 1;
      exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2 ⟩

/-
The small bad set is the union of bad sets for each prime.
-/
theorem bad_set_lemma_3_1_small_subset_union (x : ℝ) :
    bad_set_lemma_3_1_small x ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1))) (fun p => bad_set_lemma_3_1_p_v2 x p) := by
      intro m hm;
      unfold bad_set_lemma_3_1_small at hm; unfold bad_set_lemma_3_1_p_v2; aesop;

/-
Bound for the combined exponent.
-/
noncomputable def exponent_combined (p : ℕ) : ℝ :=
  exponent_p p + 0.01 / Real.log p + 1 / (100 * Real.log p)

theorem exponent_combined_bound (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) :
    exponent_combined p ≤ 1 - (Real.log (p / Nat.ceil (p / 2 : ℝ)) - 0.02) / Real.log p := by
      unfold exponent_combined;
      unfold exponent_p;
      rw [ Real.log_div ] <;> ring_nf <;> norm_num [ show p ≠ 0 by linarith ];
      · rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hp ) ) ) ] ; norm_num;
      · linarith

/-
Lower bound for the exponent constant.
-/
theorem c_p_lower_bound_val (p : ℕ) [Fact p.Prime] (hp : p ≥ 2) :
    Real.log (p / Nat.ceil (p / 2 : ℝ)) - 0.02 ≥ 0.38 := by
      by_cases hp_ge_3 : p ≥ 3;
      · -- Since $p \geq 3$, we have $p / \lceil p/2 \rceil \geq 3/2 = 1.5$.
        have h_ratio_ge_1_5 : (p : ℝ) / Nat.ceil (p / 2 : ℝ) ≥ 1.5 := by
          rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
          · exact absurd ( Nat.prime_mul_iff.mp ( Fact.out : Nat.Prime ( 2 * c ) ) ) ( by aesop );
          · rw [ div_le_div_iff₀ ] <;> norm_num <;> try linarith;
            norm_cast ; linarith [ show ⌈ ( 2 * c + 1 : ℝ ) / 2⌉₊ ≤ c + 1 by exact Nat.ceil_le.mpr <| by norm_num; linarith ];
        -- Since $\log$ is a monotonically increasing function, we have $\log(1.5) \leq \log(p / \lceil p/2 \rceil)$.
        have h_log_mono : Real.log (1.5 : ℝ) ≤ Real.log (p / Nat.ceil (p / 2 : ℝ)) := by
          exact Real.log_le_log ( by norm_num ) h_ratio_ge_1_5;
        have h_log_1_5 : Real.log (1.5 : ℝ) > 0.405 := by
          norm_num [ Real.log_lt_log ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 81 = ( Real.exp 1 ) ^ 81 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
        norm_num at * ; linarith;
      · interval_cases p ; norm_num at * ; have := Real.log_two_gt_d9 ; norm_num at * ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ] ;

/-
If m is not in the bad sets, then for any prime p <= 2k, the valuation of binom(m+k, k) is strictly less than the valuation of binom(2m, m).
-/
theorem lemma_valuation_gap (x : ℝ) (m k p : ℕ) [Fact p.Prime]
    (hx : x ≥ 100)
    (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (hk : k ∈ Finset.Icc 1 (K_thm x))
    (hp : p ≤ 2 * k)
    (h1 : m ∉ bad_set_lemma_3_1_thm x)
    (h2 : m ∉ bad_set_lemma_3_2_thm x) :
    padicValNat p (Nat.choose (m + k) k) < padicValNat p (Nat.choose (2 * m) m) := by
      have h_le : ∀ i ∈ Finset.Icc 1 k, padicValNat p (m + i) ≤ D_func p x / (6 * Real.log (D_func p x)) := by
        intro i hi;
        -- Since $p \leq 2k$ and $k \leq K_{thm}(x)$, we have $p \in \text{Finset.range}(2K_{thm}(x))$.
        have hp_range : p ∈ Finset.range (2 * K_thm x) := by
          cases lt_or_eq_of_le hp <;> simp_all +decide [ Nat.Prime.two_le ];
          · grind;
          · have := Fact.out ( p := Nat.Prime ( 2 * k ) ) ; simp_all +decide [ Nat.prime_mul_iff ] ;
            refine' Nat.le_floor _;
            rw [ ← Real.log_le_iff_le_exp ( by positivity ) ];
            have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.sq_sqrt ( Real.log_nonneg ( show x ≥ 1 by linarith ) ), Real.le_log_iff_exp_le ( show x > 0 by linarith ) |>.2 <| show Real.exp 1 ≤ x by exact le_trans ( Real.exp_one_lt_d9.le ) <| by norm_num; linarith ] ;
        have hp_range : ¬∃ p ∈ Finset.range (2 * K_thm x), p.Prime ∧ ∃ i ∈ Finset.Icc 1 (K_thm x), (padicValNat p (m + i) : ℝ) > (D_func p x : ℝ) / (6 * Real.log (D_func p x)) := by
          unfold bad_set_lemma_3_2_thm at h2; aesop;
        generalize_proofs at *; (
        exact le_of_not_gt fun h => hp_range ⟨ p, by assumption, Fact.out, i, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hk, Finset.mem_Icc.mp hi ] ⟩, by ring_nf at *; linarith ⟩);
      -- By Lemma `lemma_valuation_binom_le_max_general`, we have $v_p(\binom{m+k}{k}) \le \max_{1 \le i \le k} v_p(m+i) \le D_p/(6 \log D_p)$.
      have h_le_max : padicValNat p (Nat.choose (m + k) k) ≤ D_func p x / (6 * Real.log (D_func p x)) := by
        have h_le_max : padicValNat p (Nat.choose (m + k) k) ≤ Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i)) := by
          apply_rules [ lemma_valuation_binom_le_max_general ] ; aesop;
        refine' le_trans _ ( h_le _ ( Finset.mem_Icc.mpr ⟨ _, _ ⟩ ) );
        convert Int.ofNat_le.mpr h_le_max;
        rotate_left;
        exact Classical.choose ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ 1, Finset.mem_Icc.mpr ⟨ by norm_num, by linarith [ Finset.mem_Icc.mp hk ] ⟩ ⟩ );
        · exact Finset.mem_Icc.mp ( Classical.choose_spec ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ 1, Finset.mem_Icc.mpr ⟨ by norm_num, by linarith [ Finset.mem_Icc.mp hk ] ⟩ ⟩ ) |>.1 ) |>.1;
        · exact Finset.mem_Icc.mp ( Classical.choose_spec ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ 1, Finset.mem_Icc.mpr ⟨ by norm_num, by linarith [ Finset.mem_Icc.mp hk ] ⟩ ⟩ ) |>.1 ) |>.2;
        · rw [ show ( Finset.Icc 1 k ).sup ( fun i => padicValNat p ( m + i ) ) = padicValNat p ( m + Classical.choose ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ 1, Finset.mem_Icc.mpr ⟨ by norm_num, by linarith [ Finset.mem_Icc.mp hk ] ⟩ ⟩ ) ) from ?_ ];
          · norm_cast;
          · exact le_antisymm ( Finset.sup_le fun i hi => Classical.choose_spec ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ 1, Finset.mem_Icc.mpr ⟨ by norm_num, by linarith [ Finset.mem_Icc.mp hk ] ⟩ ⟩ ) |>.2 i hi ) ( Finset.le_sup ( f := fun i => padicValNat p ( m + i ) ) ( Classical.choose_spec ( Finset.exists_max_image ( Finset.Icc 1 k ) ( fun i => padicValNat p ( m + i ) ) ⟨ 1, Finset.mem_Icc.mpr ⟨ by norm_num, by linarith [ Finset.mem_Icc.mp hk ] ⟩ ⟩ ) |>.1 ) );
      -- Since $m \notin \text{bad\_set\_lemma\_3\_1\_thm}$, we have $v_p(\binom{2m}{m}) > D_p/(5 \log D_p)$.
      have h_gt : padicValNat p (Nat.choose (2 * m) m) > D_func p x / (5 * Real.log (D_func p x)) := by
        simp_all +decide [ bad_set_lemma_3_1_thm ];
        apply h1 p (by
        linarith) (by
        exact Fact.out);
      exact_mod_cast ( by ring_nf at *; linarith : ( padicValNat p ( Nat.choose ( m + k ) k ) : ℝ ) < padicValNat p ( Nat.choose ( 2 * m ) m ) )

/-
If m is not in the bad sets for Lemma 3.1 and 3.2, then the divisibility property holds for all k up to K_thm(x).
-/
theorem lemma_implication_fixed_K (x : ℝ) (m : ℕ) (hx : x ≥ 100) (hm : m ∈ Finset.Icc 1 (Nat.floor x))
    (h1 : m ∉ bad_set_lemma_3_1_thm x) (h2 : m ∉ bad_set_lemma_3_2_thm x) :
    ∀ k ∈ Finset.Icc 1 (K_thm x), Nat.choose (m + k) k ∣ Nat.choose (2 * m) m := by
      -- By definition of divisibility, we need to show that for all primes $p$, $v_p(\binom{m+k}{k}) \le v_p(\binom{2m}{m})$. We consider two cases: $p > 2k$ and $p \le 2k$.
      intros k hk
      apply Nat.factorization_le_iff_dvd (by
      exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ Finset.mem_Icc.mp hm, Finset.mem_Icc.mp hk ] ;) (by
      exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;) |>.1
      intro p
      by_cases hp : p.Prime
      generalize_proofs at *;
      · by_cases hpk : p ≤ 2 * k <;> simp_all +decide [ Nat.factorization ];
        · -- By Lemma 3.3, we know that if $m$ is not in the bad sets, then for any prime $p \leq 2k$, the valuation of $\binom{m+k}{k}$ is strictly less than the valuation of $\binom{2m}{m}$.
          have h_val : padicValNat p (Nat.choose (m + k) k) < padicValNat p (Nat.choose (2 * m) m) := by
            convert lemma_valuation_gap x m k p hx ( Finset.mem_Icc.mpr ⟨ hm.1, hm.2 ⟩ ) ( Finset.mem_Icc.mpr ⟨ hk.1, hk.2 ⟩ ) hpk h1 h2 using 1
            exact ⟨ hp ⟩
          generalize_proofs at *;
          exact le_of_lt h_val;
        · convert lemma_large_primes m k p ( by linarith ) ( by linarith ) using 1;
          exact ⟨ hp ⟩;
      · simp +decide [ hp, Nat.factorization_eq_zero_of_non_prime ]

/-
The bad set for Theorem 1.2 is contained in the union of the bad sets for Lemma 3.1 and Lemma 3.2.
-/
theorem bad_set_thm_1_2_subset (x : ℝ) (hx : x ≥ 100) :
    bad_set_thm_1_2 x ⊆ bad_set_lemma_3_1_thm x ∪ bad_set_lemma_3_2_thm x := by
      rw [ Finset.subset_iff ];
      unfold bad_set_thm_1_2 bad_set_lemma_3_1_thm bad_set_lemma_3_2_thm;
      simp +zetaDelta at *;
      intro m hm₁ hm₂ hm₃;
      -- Suppose for contradiction that $m \notin \text{bad\_set\_lemma\_3\_1\_thm} \cup \text{bad\_set\_lemma\_3\_2\_thm}$.
      by_contra h_contra;
      -- By `lemma_implication_fixed_K`, the divisibility property holds for all $k \le K_{thm}(x)$.
      have h_div : ∀ k ∈ Finset.Icc 1 (K_thm x), Nat.choose (m + k) k ∣ Nat.choose (2 * m) m := by
        apply lemma_implication_fixed_K;
        · linarith;
        · aesop;
        · unfold bad_set_lemma_3_1_thm; aesop;
        · unfold bad_set_lemma_3_2_thm; aesop;
      refine' hm₃ _;
      intro k hk;
      refine' h_div k _;
      refine' Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hk |>.1, le_trans ( Finset.mem_Icc.mp hk |>.2 ) _ ⟩;
      refine' Nat.floor_mono _;
      gcongr;
      exact le_trans ( Nat.cast_le.mpr hm₂ ) ( Nat.floor_le ( by positivity ) )

/-
The bad set for Lemma 3.2 is a subset of the bad set for Lemma 2.4 (from the previous theorem).
-/
theorem bad_set_lemma_3_2_thm_subset_former (x : ℝ) (hx : x ≥ 100) :
    bad_set_lemma_3_2_thm x ⊆ bad_set_former_lemma_2_4 x := by
      unfold bad_set_lemma_3_2_thm bad_set_former_lemma_2_4;
      field_simp;
      intro m hm;
      refine' Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hm |>.1, _ ⟩;
      -- Since $K_{thm}(x) \leq K_{func}(x)$, we can conclude that $p \in \text{Finset.range}(2 * K_{func}(x))$ and $i \in \text{Finset.Icc}(1, K_{func}(x))$.
      have h_subset : K_thm x ≤ K_func x := by
        exact Nat.floor_mono <| Real.exp_le_exp.mpr <| by nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( Real.log_nonneg <| show 1 ≤ x by linarith ) ] ;
      exact Exists.elim ( Finset.mem_filter.mp hm |>.2 ) fun p hp => ⟨ p, Finset.mem_range.mpr ( by linarith [ Finset.mem_range.mp hp.1 ] ), hp.2.1, by obtain ⟨ i, hi, hi' ⟩ := hp.2.2; exact ⟨ i, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩, hi' ⟩ ⟩

/-
The sum of binomial coefficients binom(D, j) for j <= B is bounded by (floor(B) + 1) * D^floor(B).
-/
theorem sum_binom_bound_helper (D : ℕ) (B : ℝ) (hD : D ≥ 1) (hB : B ≥ 0) :
    ∑ j ∈ Finset.range (Nat.floor B + 1), (Nat.choose D j : ℝ) ≤ (Nat.floor B + 1 : ℝ) * (D : ℝ) ^ (Nat.floor B) := by
      exact le_trans ( Finset.sum_le_sum fun _ _ => show ( Nat.choose D _ : ℝ ) ≤ D ^ ⌊B⌋₊ from mod_cast le_trans ( Nat.choose_le_pow _ _ ) ( pow_le_pow_right₀ hD <| Finset.mem_range_succ_iff.mp ‹_› ) ) <| by norm_num;

/-
Definition of the bound for Lemma 3.1 for a prime p.
-/
noncomputable def bound_lemma_3_1_thm_p (x : ℝ) (p : ℕ) : ℝ :=
  let D := D_func p x
  let B := (D : ℝ) / (5 * Real.log D)
  let L := Nat.ceil (p / 2 : ℝ)
  (L : ℝ) ^ D * (B + 1) * (D : ℝ) ^ (Nat.floor B)

/-
The cardinality of the bad set for Lemma 3.1 for a prime p is bounded by the defined function.
-/
theorem lemma_3_1_card_bound (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 100) :
    ((bad_set_lemma_3_1_p x p).card : ℝ) ≤ bound_lemma_3_1_thm_p x p := by
      have h_bad_set_subset : (bad_set_lemma_3_1_p x p) ⊆ (Finset.Icc 1 (Nat.floor x)).filter (fun m => count_large_digits p m ≤ (D_func p x : ℝ) / (5 * Real.log (D_func p x))) := by
        exact bad_set_subset_large_digits x p;
      have h_card_le : ((Finset.range (p ^ (D_func p x))).filter (fun m => count_large_digits p m ≤ (D_func p x : ℝ) / (5 * Real.log (D_func p x)))).card ≤ (Nat.ceil (p / 2 : ℝ)) ^ (D_func p x) * ((Nat.floor ((D_func p x : ℝ) / (5 * Real.log (D_func p x))) + 1 : ℝ) * (D_func p x) ^ (Nat.floor ((D_func p x : ℝ) / (5 * Real.log (D_func p x)))) ) := by
        have h_card_le : ((Finset.range (p ^ (D_func p x))).filter (fun m => count_large_digits p m ≤ (D_func p x : ℝ) / (5 * Real.log (D_func p x)))).card ≤ (Nat.ceil (p / 2 : ℝ)) ^ (D_func p x) * (∑ j ∈ Finset.range (Nat.floor ((D_func p x : ℝ) / (5 * Real.log (D_func p x))) + 1), Nat.choose (D_func p x) j) := by
          convert card_le_sum_binom_mul_pow p ( D_func p x ) ( Nat.floor ( ( D_func p x : ℝ ) / ( 5 * Real.log ( D_func p x ) ) ) ) using 1;
          norm_num [ Nat.le_floor_iff ( show 0 ≤ ( D_func p x : ℝ ) / ( 5 * Real.log ( D_func p x ) ) by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by unfold D_func; aesop ) ) ) ) ) ) ];
        have h_card_le : (∑ j ∈ Finset.range (Nat.floor ((D_func p x : ℝ) / (5 * Real.log (D_func p x))) + 1), Nat.choose (D_func p x) j : ℝ) ≤ (Nat.floor ((D_func p x : ℝ) / (5 * Real.log (D_func p x))) + 1 : ℝ) * (D_func p x) ^ (Nat.floor ((D_func p x : ℝ) / (5 * Real.log (D_func p x)))) := by
          convert sum_binom_bound_helper ( D_func p x ) ( ⌊ ( D_func p x : ℝ ) / ( 5 * Real.log ( D_func p x ) ) ⌋₊ ) _ _ using 1 <;> norm_num;
          exact Nat.le.intro rfl;
        exact le_trans ( Nat.cast_le.mpr ‹_› ) ( by push_cast; exact mul_le_mul_of_nonneg_left ( mod_cast h_card_le ) ( by positivity ) );
      refine' le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_bad_set_subset ) _;
      field_simp;
      refine le_trans ?_ ( h_card_le.trans ?_ );
      · refine' mod_cast Finset.card_mono _;
        intro m hm; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
        refine' ⟨ _, _ ⟩;
        · refine' lt_of_le_of_lt hm.1.2 _;
          have := p_pow_D_gt_x x p ( by linarith );
          exact Nat.floor_lt ( by positivity ) |>.2 ( mod_cast this );
        · norm_num at * ; linarith;
      · unfold bound_lemma_3_1_thm_p; norm_num; ring_nf;
        have := Nat.floor_le ( show 0 ≤ ( D_func p x : ℝ ) * ( Real.log ( D_func p x ) ) ⁻¹ * ( 1 / 5 ) by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by unfold D_func; aesop ) ) ) ) ) ) ( by norm_num ) ) ; norm_num at * ; nlinarith [ show 0 ≤ ( ⌈ ( p : ℝ ) * ( 1 / 2 ) ⌉₊ : ℝ ) ^ D_func p x * ( D_func p x : ℝ ) ^ ⌊ ( D_func p x : ℝ ) * ( Real.log ( D_func p x ) ) ⁻¹ * ( 1 / 5 ) ⌋₊ by positivity ] ;

/-
The cardinality of the bad set for Lemma 3.1 for a prime p is bounded by the defined function (v2).
-/
noncomputable def bound_lemma_3_1_thm_p_v2 (x : ℝ) (p : ℕ) : ℝ :=
  let D := D_func p x
  let B := (D : ℝ) / (5 * Real.log D)
  let L := Nat.ceil (p / 2 : ℝ)
  (L : ℝ) ^ D * (B + 1) * (D : ℝ) ^ (Nat.floor B)

theorem lemma_3_1_card_bound_v2 (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 100) :
    ((bad_set_lemma_3_1_p x p).card : ℝ) ≤ bound_lemma_3_1_thm_p_v2 x p := by
      convert lemma_3_1_card_bound x p ( le_trans ( by norm_num ) hx ) using 1

/-
The cardinality of the bad set for Lemma 3.1 is bounded by the total bound function.
-/
noncomputable def total_bound_lemma_3_1_thm (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x + 1)),
    bound_lemma_3_1_thm_p_v2 x p

theorem bad_set_lemma_3_1_thm_card_bound (x : ℝ) (hx : x ≥ 100) :
    ((bad_set_lemma_3_1_thm x).card : ℝ) ≤ total_bound_lemma_3_1_thm x := by
      -- Apply the Finset.card_biUnion_le lemma to bound the cardinality of the union.
      have h_card_biUnion : (bad_set_lemma_3_1_thm x).card ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_thm x + 1)), (bad_set_lemma_3_1_p x p).card := by
        convert Finset.card_biUnion_le;
        all_goals try infer_instance;
        ext m; simp [bad_set_lemma_3_1_thm, bad_set_lemma_3_1_p];
        exact ⟨ fun ⟨ h₁, p, hp₁, hp₂, hp₃ ⟩ => ⟨ p, ⟨ hp₁, hp₂ ⟩, h₁, hp₃ ⟩, fun ⟨ p, ⟨ hp₁, hp₂ ⟩, h₁, hp₃ ⟩ => ⟨ h₁, p, hp₁, hp₂, hp₃ ⟩ ⟩;
      refine' le_trans ( Nat.cast_le.mpr h_card_biUnion ) _;
      convert Finset.sum_le_sum fun p hp => lemma_3_1_card_bound_v2 x p ( show x ≥ 100 by linarith ) using 1;
      · norm_cast;
      · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2 ⟩

/-
The bound for Lemma 3.1 is bounded by the simplified term bound.
-/
noncomputable def term_bound_lemma_3_1 (x : ℝ) (p : ℕ) : ℝ :=
  4 * Real.exp 0.02 * p * x ^ (1 - c_p p / Real.log p)

theorem bound_lemma_3_1_le_term_bound (x : ℝ) (p : ℕ) [Fact p.Prime] (hx : x ≥ 3) (hp : p ≥ 2) :
    bound_lemma_3_1_p_v3 x p ≤ term_bound_lemma_3_1 x p := by
      -- Apply the bound_lemma_3_1_combined theorem to obtain the inequality.
      have h_combined : bound_lemma_3_1_p_v3 x p ≤ 4 * Real.exp (0.02) * p * x ^ (exponent_p p + 0.01 / Real.log p + 1 / (100 * Real.log p)) := by
        exact bound_lemma_3_1_combined x p hx;
      refine le_trans h_combined ?_;
      refine' mul_le_mul_of_nonneg_left _ ( by positivity );
      refine' Real.rpow_le_rpow_of_exponent_le ( by linarith ) _;
      have := exponent_inequality_aux p hp;
      unfold exponent_p; rw [ Real.log_div ] at * <;> norm_num at * <;> try linarith;
      ring_nf at *; nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ) ) ) ] ;

/-
The total bound is bounded by the sum of the two parts.
-/
noncomputable def bound_part_1 (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range 101).filter Nat.Prime, term_bound_lemma_3_1 x p

noncomputable def bound_part_2 (x : ℝ) : ℝ :=
  ∑ p ∈ ((Finset.range (2 * K_small x + 1)).filter Nat.Prime).filter (fun p => p > 100),
    term_bound_lemma_3_1 x p

theorem total_bound_le_parts (x : ℝ) (hx : x ≥ 3) :
    total_bound_lemma_3_1_small_func x ≤ bound_part_1 x + bound_part_2 x := by
      unfold total_bound_lemma_3_1_small_func bound_part_1 bound_part_2;
      rw [ ← Finset.sum_union ];
      · refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
        convert Finset.sum_le_sum fun p hp => bound_lemma_3_1_le_term_bound x p _ _;
        · linarith;
        · exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 );
        · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2 ⟩;
        · grind;
        · exact fun _ _ _ => by unfold term_bound_lemma_3_1; positivity;
      · exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hp₁ |>.1 ), Finset.mem_filter.mp hp₂ |>.2 ] ;

/-
The first part of the bound for Lemma 3.1 is o(x).
-/
theorem bound_part_1_is_little_o :
    bound_part_1 =o[Filter.atTop] (fun x => x) := by
      -- Each term in the sum is $o(x)$, so their sum is also $o(x)$.
      have h_term_o : ∀ p ∈ Finset.filter Nat.Prime (Finset.range 101), (fun x => term_bound_lemma_3_1 x p) =o[Filter.atTop] (fun x => x) := by
        -- Each term in the sum for bound_part_1 is $o(x)$ because the exponent of $x$ is strictly less than 1.
        intro p hp
        have h_exp : 1 - c_p p / Real.log p < 1 := by
          exact sub_lt_self _ ( div_pos ( by unfold c_p; split_ifs <;> norm_num ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ) ) );
        -- Since $1 - c_p p / \log p < 1$, we have $x^{1 - c_p p / \log p} = o(x)$.
        have h_x_pow : (fun x : ℝ => x ^ (1 - c_p p / Real.log p)) =o[Filter.atTop] (fun x : ℝ => x) := by
          rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
          · have h_x_pow : Filter.Tendsto (fun x : ℝ => x ^ (1 - c_p p / Real.log p - 1)) Filter.atTop (nhds 0) := by
              convert tendsto_rpow_neg_atTop ( show 0 < - ( 1 - c_p p / Real.log p - 1 ) by linarith ) using 1 ; norm_num;
            refine h_x_pow.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ ← Real.rpow_sub_one hx.ne' ] );
          · exact ⟨ 1, by intros; linarith ⟩;
        refine' h_x_pow.const_mul_left _ |> Asymptotics.IsLittleO.trans_isBigO <| _;
        exact Asymptotics.isBigO_refl _ _;
      refine' Asymptotics.IsLittleO.sum _ ; aesop

/-
The second part of the bound is bounded by an explicit function.
-/
noncomputable def bound_part_2_explicit (x : ℝ) : ℝ :=
  let K := 2 * K_small x + 1
  (K : ℝ)^2 * 4 * Real.exp 0.02 * x ^ (1 - 0.66 / Real.log K)

theorem bound_part_2_le_explicit (x : ℝ) (hx : x ≥ 100) :
    bound_part_2 x ≤ bound_part_2_explicit x := by
      -- Since $x \to \infty$, we have $c_p(p) = 0.66$ for $p > 100$.
      simp [bound_part_2, bound_part_2_explicit];
      refine' le_trans ( Finset.sum_le_sum fun p hp => _ ) _;
      use fun p => 4 * Real.exp 0.02 * ( 2 * K_small x + 1 ) * x ^ ( 1 - 0.66 / Real.log ( 2 * K_small x + 1 ) );
      · unfold term_bound_lemma_3_1;
        gcongr <;> norm_num at *;
        any_goals linarith [ show ( p : ℝ ) ≤ 2 * K_small x + 1 by exact_mod_cast hp.1.1.le ];
        · unfold c_p; split_ifs <;> norm_num;
        · exact Real.log_pos ( Nat.one_lt_cast.mpr hp.1.2.one_lt );
        · unfold c_p; split_ifs <;> norm_num ; linarith;
      · norm_num [ Finset.sum_const, nsmul_eq_mul ];
        refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by positivity ) _;
        refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by positivity ) _ ; norm_num ; ring_nf ; norm_num

/-
The explicit bound for the second part is o(x).
-/
theorem bound_part_2_is_little_o :
    bound_part_2_explicit =o[Filter.atTop] (fun x => x) := by
      -- We have `bound_part_2_explicit x = C * K^2 * x ^ (1 - 0.66 / log K)`.
      let C := 4 * Real.exp 0.02
      let K := fun x : ℝ => (2 * K_small x + 1 : ℝ);
      -- We'll use the fact that $K(x) \approx \exp(0.5 \sqrt{\log x})$ to show that $K(x)^2 \cdot x^{1 - 0.66 / \log K(x)}$ is $o(x)$.
      have h_exp : Filter.Tendsto (fun x => K x ^ 2 * x ^ (-0.66 / Real.log (K x) : ℝ)) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $K(x) \approx \exp(0.5 \sqrt{\log x})$ to show that $K(x)^2 \cdot x^{-0.66 / \log K(x)}$ tends to $0$.
        have h_exp : Filter.Tendsto (fun x => Real.exp (2 * Real.log (K x) - 0.66 * Real.log x / Real.log (K x))) Filter.atTop (nhds 0) := by
          -- We'll use the fact that $K(x) \approx \exp(0.5 \sqrt{\log x})$ to show that $2 \log K(x) - \frac{0.66 \log x}{\log K(x)}$ tends to $-\infty$.
          have h_log_K : Filter.Tendsto (fun x => Real.log (K x) / Real.sqrt (Real.log x)) Filter.atTop (nhds (0.5)) := by
            -- We'll use the fact that $K(x) \approx \exp(0.5 \sqrt{\log x})$ to show that $\log(K(x)) \approx 0.5 \sqrt{\log x}$ and thus the limit is $0.5$.
            have h_log_K : Filter.Tendsto (fun x => Real.log (2 * Real.exp (0.5 * Real.sqrt (Real.log x)) + 1) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0.5) := by
              -- We'll use the fact that $Real.log (2 * Real.exp (0.5 * Real.sqrt (Real.log x)) + 1) = Real.log (Real.exp (0.5 * Real.sqrt (Real.log x))) + Real.log (2 + 1 / Real.exp (0.5 * Real.sqrt (Real.log x)))$.
              suffices h_log_split : Filter.Tendsto (fun x => (0.5 * Real.sqrt (Real.log x) + Real.log (2 + 1 / Real.exp (0.5 * Real.sqrt (Real.log x)))) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0.5) by
                refine h_log_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ show ( 2 * Real.exp ( 0.5 * Real.sqrt ( Real.log x ) ) + 1 : ℝ ) = Real.exp ( 0.5 * Real.sqrt ( Real.log x ) ) * ( 2 + 1 / Real.exp ( 0.5 * Real.sqrt ( Real.log x ) ) ) by nlinarith [ Real.exp_pos ( 0.5 * Real.sqrt ( Real.log x ) ), one_div_mul_cancel ( ne_of_gt ( Real.exp_pos ( 0.5 * Real.sqrt ( Real.log x ) ) ) ) ] ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] );
              ring_nf;
              exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( Real.log_pos hx ) ) ), one_mul ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero.comp ( Real.tendsto_exp_atTop.comp ( Filter.Tendsto.atTop_mul_const ( by norm_num ) ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le ( by simpa using Real.log_exp ( x ^ 2 ) ▸ Real.log_le_log ( by positivity ) hy ) ⟩ ) ) ) ) ) ( by positivity ) ) ( tendsto_inv_atTop_zero.comp ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le ( by simpa using Real.log_exp ( x ^ 2 ) ▸ Real.log_le_log ( by positivity ) hy ) ⟩ ) ) ) ) ( by norm_num );
            -- Since $K(x) = \lfloor \exp(0.5 \sqrt{\log x}) \rfloor$ and $\exp(0.5 \sqrt{\log x})$ is very close to $K(x)$ for large $x$, we can bound the difference.
            have h_log_K_diff : ∀ᶠ x in Filter.atTop, |Real.log (2 * Nat.floor (Real.exp (0.5 * Real.sqrt (Real.log x))) + 1) - Real.log (2 * Real.exp (0.5 * Real.sqrt (Real.log x)) + 1)| ≤ Real.log 3 := by
              -- Since $y$ is very large, we have $2 * \lfloor y \rfloor + 1 \leq 2y + 1$ and $2 * \lfloor y \rfloor + 1 \geq 2y - 1$.
              have h_bounds : ∀ᶠ x in Filter.atTop, 2 * Nat.floor (Real.exp (0.5 * Real.sqrt (Real.log x))) + 1 ≤ 2 * Real.exp (0.5 * Real.sqrt (Real.log x)) + 1 ∧ 2 * Nat.floor (Real.exp (0.5 * Real.sqrt (Real.log x))) + 1 ≥ 2 * Real.exp (0.5 * Real.sqrt (Real.log x)) - 1 := by
                filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using ⟨ by linarith [ Nat.floor_le ( Real.exp_nonneg ( 0.5 * Real.sqrt ( Real.log x ) ) ) ], by linarith [ Nat.lt_floor_add_one ( Real.exp ( 0.5 * Real.sqrt ( Real.log x ) ) ) ] ⟩;
              filter_upwards [ h_bounds, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
              rw [ abs_sub_le_iff ];
              constructor <;> rw [ ← Real.log_div ( by positivity ) ( by positivity ) ];
              · exact Real.log_le_log ( div_pos ( by positivity ) ( by positivity ) ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; linarith );
              · exact Real.log_le_log ( div_pos ( by positivity ) ( by positivity ) ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; linarith [ Nat.lt_floor_add_one ( Real.exp ( 0.5 * Real.sqrt ( Real.log x ) ) ) ] );
            -- Using the fact that the difference is bounded, we can show that the limit of the difference divided by $\sqrt{\log x}$ is zero.
            have h_log_K_div : Filter.Tendsto (fun x => (Real.log (2 * Nat.floor (Real.exp (0.5 * Real.sqrt (Real.log x))) + 1) - Real.log (2 * Real.exp (0.5 * Real.sqrt (Real.log x)) + 1)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
              refine' squeeze_zero_norm' _ _;
              use fun x => Real.log 3 / Real.sqrt ( Real.log x );
              · filter_upwards [ h_log_K_diff, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by rw [ Real.norm_eq_abs, abs_div, abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; gcongr;
              · exact tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith [ Real.log_exp ( x ^ 2 ), Real.log_le_log ( by positivity ) hy ] ⟩ );
            convert h_log_K.add h_log_K_div using 2 <;> ring!;
          -- We'll use the fact that $2 \log K(x) - \frac{0.66 \log x}{\log K(x)}$ tends to $-\infty$.
          have h_exp_neg_inf : Filter.Tendsto (fun x => 2 * Real.log (K x) - 0.66 * Real.log x / Real.log (K x)) Filter.atTop Filter.atBot := by
            -- We'll use the fact that $2 \log K(x) - \frac{0.66 \log x}{\log K(x)}$ tends to $-\infty$ as $x \to \infty$.
            have h_exp_neg_inf : Filter.Tendsto (fun x => 2 * Real.log (K x) / Real.sqrt (Real.log x) - 0.66 / (Real.log (K x) / Real.sqrt (Real.log x))) Filter.atTop (nhds (2 * 0.5 - 0.66 / 0.5)) := by
              simpa [ mul_div_assoc ] using Filter.Tendsto.sub ( h_log_K.const_mul 2 ) ( tendsto_const_nhds.div h_log_K ( by norm_num ) );
            -- Since $\sqrt{\log x}$ tends to infinity, the product of the expression and $\sqrt{\log x}$ tends to $-\infty$.
            have h_prod_neg_inf : Filter.Tendsto (fun x => (2 * Real.log (K x) / Real.sqrt (Real.log x) - 0.66 / (Real.log (K x) / Real.sqrt (Real.log x))) * Real.sqrt (Real.log x)) Filter.atTop Filter.atBot := by
              apply_rules [ Filter.Tendsto.neg_mul_atTop, h_exp_neg_inf ];
              · norm_num;
              · exact Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩;
            refine h_prod_neg_inf.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx ; by_cases h : Real.sqrt ( Real.log x ) = 0 <;> simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm ];
            · exact absurd h <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx;
            · grind;
          aesop;
        refine h_exp.congr' ?_;
        field_simp;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
        rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
        rw [ ← Real.exp_log ( show 0 < K x from by positivity ) ] ; ring_nf;
        norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ← Real.exp_add ];
        rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by exact lt_add_of_pos_left _ ( by exact mul_pos zero_lt_two ( Nat.cast_pos.mpr ( Nat.floor_pos.mpr ( Real.one_le_exp ( by positivity ) ) ) ) ) ) ) ) ] ; ring;
      -- By multiplying the limit by a constant $C$, we can conclude that the original function is $o(x)$.
      have h_final : Filter.Tendsto (fun x => C * K x ^ 2 * x ^ (-0.66 / Real.log (K x) : ℝ)) Filter.atTop (nhds 0) := by
        convert h_exp.const_mul C using 2 <;> ring;
      rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num at *;
      · refine h_final.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx ; norm_num [ bound_part_2_explicit ] ; ring_nf ; norm_num [ ne_of_gt ( zero_lt_one.trans hx ) ] ;
        norm_num [ Real.rpow_add ( by positivity : 0 < x ), Real.rpow_neg ( by positivity : 0 ≤ x ) ] ; ring_nf! ; norm_num [ ne_of_gt ( zero_lt_one.trans hx ) ] ;
      · exact ⟨ 1, by intros; linarith ⟩

/-
The total bound for Lemma 3.1 (small version) is o(x).
-/
theorem total_bound_lemma_3_1_small_is_little_o :
    total_bound_lemma_3_1_small_func =o[Filter.atTop] (fun x => x) := by
      have h_total_bound_small : bound_part_1 =o[Filter.atTop] (fun x : ℝ => x) ∧ bound_part_2 =o[Filter.atTop] (fun x : ℝ => x) := by
        refine ⟨ bound_part_1_is_little_o, ?_ ⟩;
        have h_bound_part_2_explicit : bound_part_2_explicit =o[Filter.atTop] (fun x : ℝ => x) := by
          convert bound_part_2_is_little_o using 1;
        refine' Asymptotics.IsBigO.trans_isLittleO _ h_bound_part_2_explicit;
        refine' Asymptotics.isBigO_iff.mpr _;
        use 1;
        filter_upwards [ Filter.eventually_ge_atTop 100 ] with x hx using by rw [ Real.norm_of_nonneg ( show 0 ≤ bound_part_2 x from Finset.sum_nonneg fun _ _ => by exact mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( by positivity ) ), Real.norm_of_nonneg ( show 0 ≤ bound_part_2_explicit x from by exact mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( by positivity ) ) ( by positivity ) ) ] ; exact by simpa using bound_part_2_le_explicit x hx;
      have h_total_bound_small : total_bound_lemma_3_1_small_func =o[Filter.atTop] (fun x : ℝ => x) := by
        have h_le : ∀ x ≥ 3, total_bound_lemma_3_1_small_func x ≤ bound_part_1 x + bound_part_2 x := by
          exact fun x a ↦ total_bound_le_parts x a
        rw [ Asymptotics.isLittleO_iff_tendsto' ] at *;
        · refine' squeeze_zero_norm' _ _;
          use fun x => ( bound_part_1 x + bound_part_2 x ) / x;
          · filter_upwards [ Filter.eventually_ge_atTop 3 ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( show 0 ≤ total_bound_lemma_3_1_small_func x from Finset.sum_nonneg fun _ _ => show 0 ≤ bound_lemma_3_1_p_v3 x _ from by exact mul_nonneg ( mul_nonneg ( by positivity ) ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) |> add_nonneg <| by positivity ) ) <| by positivity ) <| by positivity ) ] ; exact div_le_div_of_nonneg_right ( h_le x hx ) <| by positivity;
          · simpa [ add_div ] using h_total_bound_small.1.add ( h_total_bound_small.2.tendsto_div_nhds_zero );
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using False.elim <| hx.ne' hx';
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' ( by positivity );
      exact h_total_bound_small

/-
The cardinality of the small bad set for Lemma 3.2 is bounded by the total bound function.
-/
noncomputable def total_bound_lemma_3_2_small_func (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1)),
    ∑ i ∈ Finset.Icc 1 (K_small x), (x / (p ^ (E_v2 p x) : ℝ) + 1)

theorem bad_set_lemma_3_2_small_card_bound (x : ℝ) (hx : x ≥ 3) :
    ((bad_set_lemma_3_2_small x).card : ℝ) ≤ total_bound_lemma_3_2_small_func x := by
      have h_card : ((bad_set_lemma_3_2_small x).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1)), ∑ i ∈ Finset.Icc 1 (K_small x), ((bad_set_p_i_v2 x p i).card : ℝ) := by
        have h_card : ((bad_set_lemma_3_2_small x).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1)), ∑ i ∈ Finset.Icc 1 (K_small x), ((Finset.filter (fun m => m ∈ bad_set_p_i_v2 x p i) (Finset.Icc 1 (Nat.floor x))).card : ℝ) := by
          have h_card : ((bad_set_lemma_3_2_small x).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1)), ∑ i ∈ Finset.Icc 1 (K_small x), ((Finset.filter (fun m => m ∈ bad_set_p_i_v2 x p i) (Finset.Icc 1 (Nat.floor x))).card : ℝ) := by
            have h_subset : bad_set_lemma_3_2_small x ⊆ Finset.biUnion (Finset.filter Nat.Prime (Finset.range (2 * K_small x + 1))) (fun p => Finset.biUnion (Finset.Icc 1 (K_small x)) (fun i => Finset.filter (fun m => m ∈ bad_set_p_i_v2 x p i) (Finset.Icc 1 (Nat.floor x)))) := by
              intro m hm; unfold bad_set_lemma_3_2_small at hm; unfold bad_set_p_i_v2 at *; aesop;
            exact_mod_cast le_trans ( Finset.card_le_card h_subset ) ( Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun p hp => Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun i hi => by aesop ) ;
          convert h_card using 1;
        convert h_card using 4;
        rw [ Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr ];
        exact fun m hm => Finset.mem_filter.mp hm |>.1;
      refine le_trans h_card ?_;
      apply Finset.sum_le_sum;
      intro p hp; apply Finset.sum_le_sum; intro i hi; exact (by
      apply bad_set_p_i_v2_card_bound x p i (Nat.Prime.two_le (Finset.mem_filter.mp hp |>.2)) (by linarith) |> le_trans <| by norm_num;);

/-
The total bound for Lemma 3.2 (small version) is o(x).
-/
theorem total_bound_lemma_3_2_small_is_little_o :
    total_bound_lemma_3_2_small_func =o[Filter.atTop] (fun x => x) := by
      have h_o_x_term_2 : total_bound_lemma_3_2_v2 =o[Filter.atTop] (fun x => x) := by
        exact total_bound_lemma_3_2_v2_is_little_o;
      have h_le : ∀ x : ℝ, x ≥ 100 → total_bound_lemma_3_2_small_func x ≤ total_bound_lemma_3_2_v2 x := by
        intros x hx
        simp [total_bound_lemma_3_2_small_func, total_bound_lemma_3_2_v2];
        refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset_filter _ <| Finset.range_mono <| show 2 * K_small x + 1 ≤ 2 * K_thm x from _ ) fun _ _ _ => by positivity ) _;
        · unfold K_small K_thm; norm_num [ Nat.floor_le ] ; ring_nf; norm_num [ Real.exp_pos ] ;
          -- Since $e^{0.8 \sqrt{\log x}} / e^{0.5 \sqrt{\log x}} = e^{0.3 \sqrt{\log x}}$, and $e^{0.3 \sqrt{\log x}} > 1$, we have $e^{0.8 \sqrt{\log x}} > e^{0.5 \sqrt{\log x}} + 1$.
          have h_exp_diff : Real.exp (0.8 * Real.sqrt (Real.log x)) > Real.exp (0.5 * Real.sqrt (Real.log x)) + 1 := by
            have h_exp_diff : Real.exp (0.3 * Real.sqrt (Real.log x)) > 1 + 1 / Real.exp (0.5 * Real.sqrt (Real.log x)) := by
              have h_exp_diff : Real.exp (0.3 * Real.sqrt (Real.log x)) > 1 + 0.3 * Real.sqrt (Real.log x) := by
                linarith [ Real.add_one_lt_exp ( show 0.3 * Real.sqrt ( Real.log x ) ≠ 0 by exact mul_ne_zero ( by norm_num ) ( Real.sqrt_ne_zero'.mpr ( Real.log_pos ( by linarith ) ) ) ) ];
              have h_exp_diff : 0.3 * Real.sqrt (Real.log x) > 1 / Real.exp (0.5 * Real.sqrt (Real.log x)) := by
                field_simp;
                field_simp;
                have h_exp_diff : Real.sqrt (Real.log x) > 2 := by
                  exact Real.lt_sqrt_of_sq_lt ( by have := Real.log_two_gt_d9; norm_num1 at *; rw [ show ( x : ℝ ) = 2 ^ ( Real.logb 2 x ) by rw [ Real.rpow_logb ] <;> linarith ] ; rw [ Real.log_rpow zero_lt_two ] ; nlinarith [ show ( Real.logb 2 x : ℝ ) ≥ 6 by rw [ ge_iff_le, Real.le_logb_iff_rpow_le ] <;> norm_num <;> linarith ] );
                nlinarith [ Real.add_one_le_exp ( Real.sqrt ( Real.log x ) * 0.5 ) ];
              linarith;
            rw [ show ( 0.8 : ℝ ) * Real.sqrt ( Real.log x ) = 0.5 * Real.sqrt ( Real.log x ) + 0.3 * Real.sqrt ( Real.log x ) by ring, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 0.5 * Real.sqrt ( Real.log x ) ), Real.exp_pos ( 0.3 * Real.sqrt ( Real.log x ) ), mul_div_cancel₀ 1 ( ne_of_gt ( Real.exp_pos ( 0.5 * Real.sqrt ( Real.log x ) ) ) ) ] ;
          ring_nf at *;
          exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; linarith [ Nat.lt_floor_add_one <| Real.exp <| Real.sqrt ( Real.log x ) * ( 4 / 5 ), Nat.floor_le <| Real.exp_nonneg <| Real.sqrt ( Real.log x ) * ( 1 / 2 ) ] ;
        · gcongr <;> norm_num [ K_small, K_thm ];
          · exact Nat.floor_mono <| Real.exp_le_exp.mpr <| by nlinarith [ Real.sqrt_nonneg ( Real.log x ) ] ;
          · exact Nat.floor_mono <| Real.exp_le_exp.mpr <| by linarith [ Real.sqrt_nonneg <| Real.log x ] ;
      rw [ Asymptotics.isLittleO_iff_tendsto' ] at *;
      · refine' squeeze_zero_norm' _ h_o_x_term_2;
        filter_upwards [ Filter.eventually_ge_atTop 100 ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( show 0 ≤ total_bound_lemma_3_2_small_func x from Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg ( div_nonneg ( by positivity ) ( by positivity ) ) zero_le_one ) ( by positivity ) ) ] ; exact div_le_div_of_nonneg_right ( h_le x hx ) ( by positivity ) ;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne';
      · filter_upwards [ Filter.eventually_gt_atTop 100 ] with x hx hx' using absurd hx' ( by linarith )

/-
The second part of the bound for Lemma 3.1 (thm version) is bounded by an explicit function.
-/
noncomputable def bound_part_2_thm (x : ℝ) : ℝ :=
  ∑ p ∈ ((Finset.range (2 * K_thm x + 1)).filter Nat.Prime).filter (fun p => p > 100),
    term_bound_lemma_3_1 x p

noncomputable def bound_part_2_thm_explicit (x : ℝ) : ℝ :=
  let K := 2 * K_thm x + 1
  (K : ℝ)^2 * 4 * Real.exp 0.02 * x ^ (1 - 0.66 / Real.log K)

theorem bound_part_2_thm_le_explicit (x : ℝ) (hx : x ≥ 100) :
    bound_part_2_thm x ≤ bound_part_2_thm_explicit x := by
      have h_sum_le : bound_part_2_thm x ≤ ∑ p ∈ ((Finset.range (2 * K_thm x + 1)).filter Nat.Prime).filter (fun p => p > 100), (4 * Real.exp 0.02 * p * x ^ (1 - 0.66 / Real.log p)) := by
        refine Finset.sum_le_sum ?_;
        unfold term_bound_lemma_3_1;
        unfold c_p; aesop;
      refine le_trans h_sum_le ?_;
      have h_sum_le_explicit : ∀ p ∈ ((Finset.range (2 * K_thm x + 1)).filter Nat.Prime).filter (fun p => p > 100), (4 * Real.exp 0.02 * p * x ^ (1 - 0.66 / Real.log p)) ≤ (4 * Real.exp 0.02 * (2 * K_thm x + 1) * x ^ (1 - 0.66 / Real.log (2 * K_thm x + 1))) := by
        intros p hp
        have hp_le : (p : ℝ) ≤ 2 * K_thm x + 1 := by
          exact_mod_cast Finset.mem_range_le ( Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 );
        gcongr;
        · linarith;
        · exact Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) ) );
        · exact Nat.cast_pos.mpr ( Nat.Prime.pos ( by aesop ) );
      refine le_trans ( Finset.sum_le_sum h_sum_le_explicit ) ?_;
      simp +zetaDelta at *;
      refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by positivity ) _ ; norm_num [ bound_part_2_thm_explicit ];
      refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by positivity ) _ ; norm_num ; ring_nf ; norm_num

/-
The set of integers m <= x for which the divisibility fails for some k <= K_small(x) has asymptotic density 0.
-/
theorem bad_set_thm_1_2_small_density_zero :
    (fun x => ((bad_set_thm_1_2_small x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      -- By definition of $bad\_set\_thm\_1\_2\_small$, we have:
      have h_subset : ∀ x, bad_set_thm_1_2_small x ⊆ bad_set_lemma_3_1_small x ∪ bad_set_lemma_3_2_small x := by
        exact fun x ↦ bad_set_thm_1_2_small_subset x;
      -- Using the subset relation, we can bound the cardinality of $bad\_set\_thm\_1\_2\_small$ by the sum of the cardinalities of $bad\_set\_lemma\_3\_1\_small$ and $bad\_set\_lemma\_3\_2\_small$.
      have h_card_bound : ∀ x, ((bad_set_thm_1_2_small x).card : ℝ) ≤ ((bad_set_lemma_3_1_small x).card : ℝ) + ((bad_set_lemma_3_2_small x).card : ℝ) := by
        exact fun x => mod_cast le_trans ( Finset.card_le_card ( h_subset x ) ) ( Finset.card_union_le _ _ );
      -- Using the bounds from the previous steps, we can conclude that the cardinality of $bad\_set\_thm\_1\_2\_small$ is $o(x)$.
      have h_card_bound : ∀ x ≥ 3, ((bad_set_lemma_3_1_small x).card : ℝ) ≤ total_bound_lemma_3_1_small_func x ∧ ((bad_set_lemma_3_2_small x).card : ℝ) ≤ total_bound_lemma_3_2_small_func x := by
        intros x hx
        apply And.intro (bad_set_lemma_3_1_small_card_bound x hx) (bad_set_lemma_3_2_small_card_bound x hx);
      -- Using the bounds from the previous steps, we can conclude that the cardinality of $bad\_set\_thm\_1\_2\_small$ is $o(x)$ by the properties of big O notation.
      have h_card_bound : (fun x => total_bound_lemma_3_1_small_func x) =o[Filter.atTop] (fun x => x) ∧ (fun x => total_bound_lemma_3_2_small_func x) =o[Filter.atTop] (fun x => x) := by
        exact ⟨ total_bound_lemma_3_1_small_is_little_o, total_bound_lemma_3_2_small_is_little_o ⟩;
      rw [ Asymptotics.isLittleO_iff ] at *;
      rw [ Asymptotics.isLittleO_iff ] at *;
      intro c hc; filter_upwards [ h_card_bound.1 ( half_pos hc ), h_card_bound.2 ( half_pos hc ), Filter.eventually_ge_atTop 3 ] with x hx₁ hx₂ hx₃; norm_num at *;
      exact le_trans ( by solve_by_elim ) ( by nlinarith [ abs_of_nonneg ( by positivity : 0 ≤ x ), abs_of_nonneg ( show 0 ≤ total_bound_lemma_3_1_small_func x from by
                                                                                                                      exact le_trans ( Nat.cast_nonneg _ ) ( ‹∀ x : ℝ, 3 ≤ x → ( bad_set_lemma_3_1_small x |> Finset.card : ℝ ) ≤ total_bound_lemma_3_1_small_func x ∧ ( bad_set_lemma_3_2_small x |> Finset.card : ℝ ) ≤ total_bound_lemma_3_2_small_func x› x hx₃ |>.1 ) ), abs_of_nonneg ( show 0 ≤ total_bound_lemma_3_2_small_func x from by
                                                                                                                                                                                                  exact le_trans ( Nat.cast_nonneg _ ) ( ‹∀ x : ℝ, 3 ≤ x → ( bad_set_lemma_3_1_small x |> Finset.card : ℝ ) ≤ total_bound_lemma_3_1_small_func x ∧ ( bad_set_lemma_3_2_small x |> Finset.card : ℝ ) ≤ total_bound_lemma_3_2_small_func x› x hx₃ |>.2 ) ), ‹∀ x : ℝ, 3 ≤ x → ( bad_set_lemma_3_1_small x |> Finset.card : ℝ ) ≤ total_bound_lemma_3_1_small_func x ∧ ( bad_set_lemma_3_2_small x |> Finset.card : ℝ ) ≤ total_bound_lemma_3_2_small_func x› x hx₃ ] )

/-
The number of large digits is additive for concatenation.
-/
theorem count_large_digits_add (p : ℕ) (n : ℕ) (k r : ℕ) (hr : r < p ^ n) (hp : p ≥ 2) :
    count_large_digits p (k * p ^ n + r) = count_large_digits p k + count_large_digits p r := by
      unfold count_large_digits;
      -- By definition of `digits_aux`, we can split the list into the digits of `r` and the digits of `k * p^n`.
      have h_digits_split : Nat.digits p (k * p ^ n + r) = Nat.digits p r ++ Nat.digits p (k * p ^ (n - (Nat.digits p r).length)) := by
        rw [ Nat.add_comm, Nat.digits_append_digits ];
        · rw [ mul_left_comm, ← pow_add, Nat.add_sub_of_le ];
          have := @Nat.digits_len p r;
          exact if hr0 : r = 0 then by simp +decide [ hr0 ] else by rw [ this hp hr0 ] ; exact Nat.log_lt_of_lt_pow ( by positivity ) hr;
        · linarith;
      rw [ h_digits_split, List.filter_append ];
      induction n - List.length ( Nat.digits p r ) <;> simp_all +decide [ pow_succ, ← mul_assoc ];
      · ring;
      · rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod, Nat.mul_div_assoc ];
        cases k <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod, Nat.mul_div_assoc ]

/-
The set of integers m <= x such that the divisibility property fails for some k <= K_small(m).
-/
noncomputable def bad_set_intrinsic_1_2 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ k ∈ Finset.Icc 1 (K_small m), ¬ (Nat.choose (m + k) k ∣ Nat.choose (2 * m) m))

/-
The intrinsic bad set is a subset of the bad set defined with K_small(x).
-/
theorem bad_set_intrinsic_subset_small (x : ℝ) (hx : x ≥ 1) :
    bad_set_intrinsic_1_2 x ⊆ bad_set_thm_1_2_small x := by
      -- Let $m$ be an integer in the intrinsic bad set.
      intro m hm
      obtain ⟨k, hk₁, hk₂⟩ := (Finset.mem_filter.mp hm).right
      have hk_bound : k ≤ K_small x := by
        refine' le_trans ( Finset.mem_Icc.mp hk₁ |>.2 ) _;
        refine' Nat.floor_mono _;
        gcongr;
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) );
        · exact le_trans ( Nat.cast_le.mpr ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.2 ) ) ( Nat.floor_le ( by positivity ) );
      exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) ], Nat.le_floor <| by linarith [ show ( m :ℝ ) ≤ x from Nat.floor_le ( by positivity ) |> le_trans ( mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.2 ) ] ⟩, ⟨ k, Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hk₁ |>.1, hk_bound ⟩, hk₂ ⟩ ⟩

/-
K_small is monotonic.
-/
theorem K_small_mono {x y : ℝ} (hxy : x ≤ y) (hx : x ≥ 1) : K_small x ≤ K_small y := by
  exact Nat.floor_mono <| Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| Real.log_le_log ( by linarith ) hxy ) <| by norm_num;

/-
The set of m where the property fails for k <= K_small(m) has asymptotic density 0.
-/
theorem theorem_1_2 :
    (fun x => ((bad_set_intrinsic_1_2 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
      have h_subset : (fun x => ((bad_set_intrinsic_1_2 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
        have h_subset : ∀ x : ℝ, x ≥ 1 → (bad_set_intrinsic_1_2 x).card ≤ (bad_set_thm_1_2_small x).card := by
          intro x hx; exact Finset.card_le_card (bad_set_intrinsic_subset_small x hx) ;
        refine' Asymptotics.IsLittleO.mono _ _;
        exact Filter.atTop;
        · have := @bad_set_thm_1_2_small_density_zero;
          rw [ Asymptotics.isLittleO_iff ] at *;
          intros c hc; filter_upwards [ this hc, Filter.eventually_ge_atTop 1 ] with x hx₁ hx₂; exact le_trans ( by simpa [ abs_of_nonneg ( show 0 ≤ ( bad_set_intrinsic_1_2 x |> Finset.card : ℝ ) by positivity ), abs_of_nonneg ( show 0 ≤ ( bad_set_thm_1_2_small x |> Finset.card : ℝ ) by positivity ) ] using h_subset x hx₂ ) hx₁;
        · exact Filter.tendsto_id;
      convert h_subset using 1
