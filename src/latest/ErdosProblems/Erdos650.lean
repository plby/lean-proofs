/-
Prompted by Yixin He, Yanyang Li and Quanyu Tang, ChatGPT 5.4 Pro proved that for every positive integer $m$ there exists a set $A = \{a_1 < a_2 < \cdots < a_m \}$ of $m$ positive integers and an interval $I = (x, x + 2a_m)$ such that the maximum number of fully disjoint pairs $(a, b)$ with $a \in A$, $b \in I$ and $a | b$ is at most $\lceil 2 \sqrt{m} \rceil$. Moreover, this bound is essentially tight. More precisely, for every set of positive integers $A = \{a_1 < a_2 < \cdots < a_m \}$ and every interval $I = (x, x + 2a_m)$ one can find at least $\min(m, \lceil 2 \sqrt{m} \rceil)$ fully disjoint pairs $(a, b)$ with $a \in A$, $b \in I$ and $a | b$. This latter proof was obtained in joint work by ChatGPT and Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

These bounds solve Erdős Problem #650 (https://www.erdosproblems.com/650), and the write-up can be found on the arXiv.

W. van Doorn, Y. Li, and Q. Tang, Optimal bounds for an Erdős problem on matching integers to distinct multiples. arXiv:2603.28636 (2026).

Below you can find a formalization of the result in Lean, which is also due to Aristotle.

Lean version: leanprover/lean4:v4.28.0
Mathlib version: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
-/

import Mathlib

namespace Erdos650

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedDecidableInType false
set_option linter.style.cdot false
set_option linter.style.docString false
set_option linter.style.induction false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.refine false

open Finset Real Nat

-- ════════════════════════════════════════════════════════════════════════════════
-- Part 1: Definitions
-- ════════════════════════════════════════════════════════════════════════════════

/-- A matching of size `r` in the bipartite divisibility graph. -/
def HasDivMatching (A : Finset ℕ) (B : Finset ℤ) (r : ℕ) : Prop :=
  ∃ (c : Fin r → ℕ) (b : Fin r → ℤ),
    Function.Injective c ∧ Function.Injective b ∧
    (∀ i, c i ∈ A) ∧ (∀ i, b i ∈ B) ∧
    (∀ i, (c i : ℤ) ∣ b i)

/-- `erdos_f m` is the largest `r` such that for every set `A` of `m`
    positive integers and every real offset `x`, there exists a
    divisibility matching of size `r` in the interval `(x, x + 2·max A)`. -/
noncomputable def erdos_f (m : ℕ) : ℕ :=
  sSup { r : ℕ | ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) → A.card = m →
    ∀ (x : ℝ), HasDivMatching A (Finset.Ioo ⌊x⌋ ⌈x + 2 * ↑(A.sup id)⌉) r }

/-- For integer x, the real interval representation equals the integer one. -/
lemma intIoo_real_eq_int (x : ℤ) (M : ℕ) :
    Finset.Ioo (⌊(x : ℝ)⌋ : ℤ) (⌈(x : ℝ) + 2 * ↑M⌉ : ℤ) = Finset.Ioo x (x + 2 * ↑M) := by
  congr 1
  · exact Int.floor_intCast x
  · rw [show (x : ℝ) + 2 * (M : ℝ) = ↑(x + 2 * (M : ℤ)) by push_cast; ring]
    exact Int.ceil_intCast _

/-- The integer-offset Ioo is contained in the real-offset one for any real x. -/
lemma intIoo_int_sub_real (x : ℝ) (M : ℕ) :
    Finset.Ioo ⌊x⌋ (⌊x⌋ + 2 * ↑M) ⊆ Finset.Ioo ⌊x⌋ ⌈x + 2 * ↑M⌉ := by
  apply Finset.Ioo_subset_Ioo_right
  have : ⌈x + 2 * (M : ℝ)⌉ = ⌈x⌉ + 2 * ↑M := by
    rw [show x + 2 * (M : ℝ) = x + ↑(2 * (M : ℤ)) by push_cast; ring]
    exact Int.ceil_add_intCast x _
  linarith [Int.floor_le_ceil x]

/-- Monotonicity of HasDivMatching in the interval set. -/
lemma HasDivMatching.mono {A : Finset ℕ} {B B' : Finset ℤ} {r : ℕ}
    (h : HasDivMatching A B r) (hBB' : B ⊆ B') : HasDivMatching A B' r := by
  obtain ⟨c, b, hc, hb, hcA, hbB, hcd⟩ := h
  exact ⟨c, b, hc, hb, hcA, fun i => hBB' (hbB i), hcd⟩

/-- lcm of 1, 2, ..., n -/
noncomputable def lcm_range : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (n + 1) (lcm_range n)

/-- Convert a subset-indexed injection into a `HasDivMatching`. -/
lemma HasDivMatching_from_subset (A : Finset ℕ) (B : Finset ℤ)
    (S : Finset ↥A) (f : ↥S → ℤ)
    (hf_inj : Function.Injective f)
    (hf_mem : ∀ x : ↥S, f x ∈ B)
    (hf_div : ∀ x : ↥S, (↑x.1.1 : ℤ) ∣ f x)
    (r : ℕ) (hr : r ≤ S.card) :
    HasDivMatching A B r := by
      obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq hr;
      have h_equiv : Nonempty (Fin r ≃ T) := by
        exact ⟨ Fintype.equivOfCardEq <| by aesop ⟩;
      obtain ⟨ e ⟩ := h_equiv;
      refine' ⟨ fun i => ( e i ).val.val, fun i => f ⟨ ⟨ ( e i ).val.val, ( e i ).val.prop ⟩, hT.1 ( e i |>.2 ) ⟩, _, _, _, _, _ ⟩ <;> simp_all +decide [ Function.Injective ];
      intro i j hij; specialize hf_inj _ _ _ _ _ _ hij; aesop;

noncomputable def largestMultiple (a : ℕ) (y : ℤ) : ℤ :=
  (y / ↑a) * ↑a

lemma largestMultiple_is_multiple (a : ℕ) (y : ℤ) :
    (a : ℤ) ∣ largestMultiple a y :=
  dvd_mul_left _ _

lemma largestMultiple_le (a : ℕ) (ha : 0 < a) (y : ℤ) :
    largestMultiple a y ≤ y :=
  Int.ediv_mul_le _ (by positivity)

lemma largestMultiple_gt (a : ℕ) (ha : 0 < a) (y : ℤ) :
    y - ↑a < largestMultiple a y := by
  unfold largestMultiple
  nlinarith [Int.emod_add_mul_ediv y a,
    Int.emod_nonneg y (by positivity : (a : ℤ) ≠ 0),
    Int.emod_lt_of_pos y (by positivity : (a : ℤ) > 0)]

-- ════════════════════════════════════════════════════════════════════════════════
-- Part 2: Basic properties of erdos_f
-- ════════════════════════════════════════════════════════════════════════════════

-- The trivial upper bound f(m) ≤ m.
lemma erdos_f_le (m : ℕ) : erdos_f m ≤ m := by
  refine' csSup_le' _
  intro r hr
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a) ∧ A.card = m :=
    ⟨Finset.Icc 1 m, fun a ha => by linarith [Finset.mem_Icc.mp ha], by simp⟩
  obtain ⟨c, b, hc, hb, hcA, hbA, hcd⟩ := hr A hA.1 hA.2 (0 : ℝ)
  have := Finset.card_le_card (show Finset.image c Finset.univ ⊆ A from
    Finset.image_subset_iff.mpr fun i _ => hcA i)
  simp_all +decide [Finset.card_image_of_injective _ hc]

-- Monotonicity: f is non-decreasing.
lemma erdos_f_mono : Monotone erdos_f := by
  intros m n hmn
  apply csSup_le_csSup
  · refine' ⟨n, fun r hr => _⟩
    have := hr (Finset.Icc 1 n) (fun a ha => by linarith [Finset.mem_Icc.mp ha]) (by simp) (0 : ℝ)
    obtain ⟨c, b, hc, hb, hc', hb', h⟩ := this
    exact le_trans (by simpa [Finset.card_image_of_injective _ hc] using
      Finset.card_le_card (show Finset.image c Finset.univ ⊆ Finset.Icc 1 n from
        Finset.image_subset_iff.mpr fun i _ => hc' i)) (by simp)
  · use 0
    intros A hA_pos hA_card x
    simp [HasDivMatching]
    simp +decide
  · intro r hr A hA hAn x
    obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, B ⊆ A ∧ B.card = m :=
      Finset.exists_subset_card_eq (by linarith)
    have hB_subset := hr B (fun a ha => hA a (hB.1 ha)) hB.2 x
    have hB_sup : B.sup id ≤ A.sup id := Finset.sup_mono hB.1
    have hB_interval : Finset.Ioo ⌊x⌋ ⌈x + 2 * ↑(B.sup id)⌉ ⊆ Finset.Ioo ⌊x⌋ ⌈x + 2 * ↑(A.sup id)⌉ := by
      apply Finset.Ioo_subset_Ioo_right
      exact Int.ceil_le_ceil (by gcongr)
    obtain ⟨c, b, hc, hb, hc', hb', h⟩ := hB_subset
    exact ⟨c, b, hc, hb, fun i => hB.1 (hc' i), fun i => hB_interval (hb' i), h⟩

/-- If all multiples of elements of A in (x, x+2max(A)) lie in a set S of
    size ≤ k, then erdos_f n ≤ k. -/
lemma erdos_f_le_of_few_multiples (n k : ℕ)
    (A : Finset ℕ) (hA_pos : ∀ a ∈ A, 0 < a) (hA_card : A.card = n)
    (x : ℤ) (S : Finset ℤ) (hS_card : S.card ≤ k)
    (hS_contains : ∀ b ∈ Finset.Ioo x (x + 2 * ↑(A.sup id)),
      (∃ a ∈ A, (a : ℤ) ∣ b) → b ∈ S) :
    erdos_f n ≤ k := by
      by_contra h_contra;
      obtain ⟨r, hr⟩ : ∃ r > k, ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → A.card = n → ∀ x : ℝ, HasDivMatching A (Finset.Ioo ⌊x⌋ ⌈x + 2 * (A.sup id)⌉) r := by
        contrapose! h_contra;
        refine' csSup_le' _;
        exact fun r hr => not_lt.1 fun contra => by obtain ⟨ A, hA_pos, hA_card, x, hx ⟩ := h_contra r contra; exact hx <| hr A hA_pos hA_card x;
      obtain ⟨ c, b, hc, hb, hcA, hbB, hcb ⟩ := hr.2 A hA_pos hA_card (↑x);
      rw [intIoo_real_eq_int] at hbB;
      exact absurd ( Finset.card_le_card ( show Finset.image b Finset.univ ⊆ S from Finset.image_subset_iff.mpr fun i _ => hS_contains _ ( hbB i ) ⟨ _, hcA i, hcb i ⟩ ) ) ( by rw [ Finset.card_image_of_injective _ hb ] ; simpa using by linarith )

-- ════════════════════════════════════════════════════════════════════════════════
-- Part 3: The upper bound  (Section 3)
-- ════════════════════════════════════════════════════════════════════════════════

/-- Every k ≤ n with k ≥ 1 divides lcm_range n -/
lemma dvd_lcm_range (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    k ∣ lcm_range n := by
  induction' n with n ih generalizing k ; aesop;
  by_cases hkn' : k = n + 1;
  · exact hkn'.symm ▸ Nat.dvd_trans ( by norm_num ) ( Nat.dvd_lcm_left _ _ );
  · exact dvd_trans ( ih k hk ( Nat.le_of_lt_succ ( lt_of_le_of_ne hkn hkn' ) ) ) ( Nat.dvd_lcm_right _ _ )

/-- For p ≤ n and q with q² ≤ n, we have v_p(lcm_range n) > v_p(q). -/
lemma emultiplicity_lcm_range_gt
    (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hp_le : p ≤ n)
    (q : ℕ) (hq_pos : 0 < q) (hq_sq : q ^ 2 ≤ n) :
    emultiplicity p (lcm_range n) > emultiplicity p q := by
  by_cases hq : p ∣ q;
  · have hq_sq_div_lcm : q^2 ∣ lcm_range n := by
      convert dvd_lcm_range n ( q ^ 2 ) _ _ using 1 <;> nlinarith;
    have h_emultiplicity : emultiplicity p (q^2) ≤ emultiplicity p (lcm_range n) := by
      rw [ emultiplicity_le_emultiplicity_iff ]
      exact fun k hk => dvd_trans hk hq_sq_div_lcm
    have h_emultiplicity_q_sq : emultiplicity p (q^2) = 2 * emultiplicity p q := by
      rw [ emultiplicity_pow ] ; aesop; exact Nat.prime_iff.mp hp
    cases h : emultiplicity p q <;> simp_all +decide [ two_mul ];
    · exact absurd ( h ( Nat.log p q ) ) ( Nat.not_dvd_of_pos_of_lt hq_pos ( Nat.lt_pow_succ_log_self hp.one_lt _ ) );
    · norm_cast at *
      exact lt_of_lt_of_le ( WithTop.coe_lt_coe.mpr ( by linarith [ show ‹ℕ› > 0 from Nat.pos_of_ne_zero fun h => by simp_all +decide [ emultiplicity_eq_zero ] ] ) ) h_emultiplicity
  · simp_all +decide [emultiplicity_eq_zero.mpr]
    have h_div : p ∣ lcm_range n := dvd_lcm_range n p hp.pos hp_le
    rw [ emultiplicity ] ; aesop

/-- The set of "bad" primes for the upper bound construction -/
def badPrimes (s t D : ℕ) : Set ℕ :=
  { p | Nat.Prime p ∧ p > s * t ∧
    ∃ q r : ℤ, 0 < |q| ∧ |q| < ↑s ∧ |r| < ↑t ∧ (p : ℤ) ∣ (q + r * ↑D) }

/-- The set of bad primes is finite when D ≥ s -/
lemma badPrimes_finite (s t D : ℕ) (hD : s ≤ D) : Set.Finite (badPrimes s t D) := by
  have h_finite_divisors : ∀ q r : ℤ, 0 < |q| ∧ |q| < s ∧ |r| < t → Set.Finite {p : ℕ | Nat.Prime p ∧ (p : ℤ) ∣ q + r * D} := by
    intros q r hqr
    have h_nonzero : q + r * D ≠ 0 := by
      cases abs_cases q <;> cases abs_cases r <;> cases lt_or_ge 0 r <;> nlinarith [ show ( D : ℤ ) ≥ s by norm_cast ] ;
    exact Set.finite_iff_bddAbove.mpr ⟨ Int.natAbs ( q + r * D ), fun p hp => Nat.le_of_dvd ( Int.natAbs_pos.mpr h_nonzero ) ( Int.natCast_dvd.mp hp.2 ) ⟩
  have h_finite_pairs : Set.Finite {p : ℕ | Nat.Prime p ∧ ∃ q r : ℤ, 0 < |q| ∧ |q| < s ∧ |r| < t ∧ (p : ℤ) ∣ q + r * D} := by
    have h_pairs_finite : Set.Finite {pq : ℤ × ℤ | 0 < |pq.1| ∧ |pq.1| < s ∧ |pq.2| < t} := by
      exact Set.Finite.subset ( Set.Finite.prod ( Set.finite_Ioo ( - ( s : ℤ ) ) ( s : ℤ ) ) ( Set.finite_Ioo ( - ( t : ℤ ) ) ( t : ℤ ) ) ) fun p hp => ⟨ abs_lt.mp hp.2.1, abs_lt.mp hp.2.2 ⟩
    exact Set.Finite.subset ( h_pairs_finite.biUnion fun pq hpq => h_finite_divisors pq.1 pq.2 hpq ) fun p hp => by aesop;
  exact h_finite_pairs.subset fun p hp => ⟨ hp.1, hp.2.2.choose, hp.2.2.choose_spec.choose, hp.2.2.choose_spec.choose_spec.1, hp.2.2.choose_spec.choose_spec.2.1, hp.2.2.choose_spec.choose_spec.2.2.1, hp.2.2.choose_spec.choose_spec.2.2.2 ⟩

set_option maxHeartbeats 800000 in
/-- For the construction with α_{i,j} = M + i + jD, where D = lcm(1,...,st),
    we have gcd(α_{i,j}, α_{k,l}) | (i - k). -/
lemma gcd_claim (s t : ℕ) (hs : 2 ≤ s) (hst : s ≤ t)
    (D : ℕ) (hD : D = lcm_range (s * t))
    (M : ℕ) (hM_large : M > 2 * s + 2 * t * D)
    (hM_avoid : ∀ p : ℕ, Nat.Prime p → p > s * t →
      (∃ q r : ℤ, 0 < |q| ∧ |q| < ↑s ∧ |r| < ↑t ∧ (p : ℤ) ∣ (q + r * ↑D)) →
      ∀ i j : ℕ, 1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t →
        ¬((p : ℤ) ∣ (↑M + ↑i + ↑j * ↑D)))
    (i k : ℕ) (hi : 1 ≤ i) (hi' : i ≤ s) (hk : 1 ≤ k) (hk' : k ≤ s)
    (j l : ℕ) (hj : 1 ≤ j) (hj' : j ≤ t) (hl : 1 ≤ l) (hl' : l ≤ t) :
    (Int.gcd (↑M + ↑i + ↑j * ↑D) (↑M + ↑k + ↑l * ↑D) : ℤ) ∣ (↑i - ↑k) := by
  -- Let $g = \gcd(M + i + jD, M + k + lD)$ and $q = i - k$, $r = j - l$.
  set g := Int.gcd (M + i + j * D) (M + k + l * D) with hg
  set q := (i : ℤ) - k with hq
  set r := (j : ℤ) - l with hr
  have hg_div_q_rD : (g : ℤ) ∣ q + r * D := by
    convert dvd_sub ( Int.gcd_dvd_left _ _ ) ( Int.gcd_dvd_right _ _ ) using 1 ; ring
  have hg_div_q : (g : ℤ) ∣ q := by
    -- If $i = k$, then $g | 0$ trivially. Assume $i \neq k$, so $0 < |q| < s$ and $|r| < t$.
    by_cases hq_zero : q = 0
    · simp [hq_zero]
    ·
      have h_prime_factors : ∀ p : ℕ, Nat.Prime p → p ∣ g → p ≤ s * t := by
        intros p hp hp_div_g
        by_contra hp_gt_st
        have hp_bad : ∃ q r : ℤ, (0 < abs q ∧ abs q < s ∧ abs r < t ∧ (p : ℤ) ∣ (q + r * D)) := by
          use q, r
          generalize_proofs at *; (
          exact ⟨ abs_pos.mpr hq_zero, abs_lt.mpr ⟨ by linarith, by linarith ⟩, abs_lt.mpr ⟨ by linarith, by linarith ⟩, dvd_trans ( Int.natCast_dvd_natCast.mpr hp_div_g ) hg_div_q_rD ⟩ ;)
        generalize_proofs at *; (
        exact hM_avoid p hp ( not_le.mp hp_gt_st ) hp_bad i j hi hi' hj hj' ( Int.dvd_trans ( Int.natCast_dvd_natCast.mpr hp_div_g ) ( Int.gcd_dvd_left _ _ ) ))
      -- Since every prime factor of $g$ divides $D$, we have $v_p(D) > v_p(|q|)$ for any prime $p$ dividing $g$.
      have h_valuation : ∀ p : ℕ, Nat.Prime p → p ∣ g → padicValNat p D > padicValNat p (Int.natAbs q) := by
        intros p hp hp_div_g
        have h_valuation_step : padicValNat p D > padicValNat p (Int.natAbs q) := by
          have h_q_sq_le_st : Int.natAbs q ^ 2 ≤ s * t := by
            have h_q_sq_le_st : Int.natAbs q ^ 2 ≤ s ^ 2 := by
              exact Nat.pow_le_pow_left ( by cases abs_cases ( i - k : ℤ ) <;> linarith ) 2
            have h_q_sq_le_st' : s ^ 2 ≤ s * t := by
              nlinarith only [ hs, hst ]
            linarith [h_q_sq_le_st, h_q_sq_le_st']
          have h_valuation_step : emultiplicity p (lcm_range (s * t)) > emultiplicity p (Int.natAbs q) := by
            apply emultiplicity_lcm_range_gt (s * t) p hp (by
            exact h_prime_factors p hp hp_div_g) (Int.natAbs q) (by
            exact Int.natAbs_pos.mpr hq_zero) (by
            exact h_q_sq_le_st);
          haveI : Fact (Nat.Prime p) := ⟨hp⟩
          have hD_ne : D ≠ 0 := by
            rw [hD]
            exact Nat.ne_of_gt <|
              Nat.recOn (s * t) (by decide) fun n ihn => Nat.lcm_pos (Nat.succ_pos _) ihn
          have hq_ne : Int.natAbs q ≠ 0 := Int.natAbs_ne_zero.mpr hq_zero
          have h_enat :
              (padicValNat p D : ℕ∞) > (padicValNat p (Int.natAbs q) : ℕ∞) := by
            rw [padicValNat_eq_emultiplicity (p := p) hD_ne,
              padicValNat_eq_emultiplicity (p := p) hq_ne, hD]
            exact h_valuation_step
          exact ENat.coe_lt_coe.mp h_enat
        exact h_valuation_step;
      -- Since $v_p(D) > v_p(|q|)$ for any prime $p$ dividing $g$, we have $v_p(q + rD) = v_p(q)$.
      have h_valuation_eq : ∀ p : ℕ, Nat.Prime p → p ∣ g → padicValNat p (Int.natAbs (q + r * D)) = padicValNat p (Int.natAbs q) := by
        intros p hp hp_div_g
        have h_valuation_eq_step : padicValNat p (Int.natAbs (q + r * D)) = padicValNat p (Int.natAbs q) := by
          have h_div : p ^ (padicValNat p (Int.natAbs q)) ∣ Int.natAbs q ∧ ¬p ^ (padicValNat p (Int.natAbs q) + 1) ∣ Int.natAbs q := by
            haveI := Fact.mk hp; simp +decide [ padicValNat_dvd_iff ] ;
            exact hq_zero
          have h_div_rD : p ^ (padicValNat p (Int.natAbs q) + 1) ∣ Int.natAbs (r * D) := by
            -- Since $p$ divides $D$, we have $p^{padicValNat p D} \mid D$.
            have h_div_D : p ^ (padicValNat p D) ∣ D := by
              exact pow_padicValNat_dvd
            generalize_proofs at *; (
            rw [ Int.natAbs_mul ] ; exact dvd_mul_of_dvd_right ( dvd_trans ( pow_dvd_pow _ ( Nat.succ_le_of_lt ( h_valuation p hp hp_div_g ) ) ) h_div_D ) _;)
          have h_div_q_rD : p ^ (padicValNat p (Int.natAbs q)) ∣ Int.natAbs (q + r * D) ∧ ¬p ^ (padicValNat p (Int.natAbs q) + 1) ∣ Int.natAbs (q + r * D) := by
            constructor
            all_goals generalize_proofs at *;
            · exact Int.natCast_dvd.mp ( Int.dvd_add ( Int.natCast_dvd.mpr h_div.1 ) ( Int.natCast_dvd.mpr ( dvd_trans ( pow_dvd_pow _ ( Nat.le_succ _ ) ) h_div_rD ) ) ) |> fun x => by simpa [ ← Int.natCast_dvd_natCast ] using x;
            · intro h_div_q_rD
              have h_div_q : p ^ (padicValNat p (Int.natAbs q) + 1) ∣ Int.natAbs q := by
                convert Int.natAbs_dvd_natAbs.mpr ( Int.dvd_sub ( Int.natCast_dvd.mpr h_div_q_rD ) ( Int.natCast_dvd.mpr h_div_rD ) ) using 1 ; norm_num [ add_comm ]
              generalize_proofs at *; (
              exact h_div.2 h_div_q)
          generalize_proofs at *; (
          have h_valuation_eq_step : padicValNat p (Int.natAbs (q + r * D)) = Nat.factorization (Int.natAbs (q + r * D)) p := by
            rw [ Nat.factorization_def ] ; aesop;
          generalize_proofs at *; (
          obtain ⟨ k, hk ⟩ := h_div_q_rD.1; simp_all +decide ;
          rw [ Nat.factorization_mul ] <;> norm_num [ hp.ne_zero ];
          · simp +decide [ hp.factorization ];
            exact Nat.factorization_eq_zero_of_not_dvd fun h => h_div_q_rD <| mul_dvd_mul_left _ h |> fun x => dvd_trans ( by ring_nf; norm_num ) x;
          · rintro rfl; simp_all +decide ;))
        exact h_valuation_eq_step;
      -- Since $v_p(g) \leq v_p(q + rD) = v_p(q)$ for any prime $p$ dividing $g$, we have $g \mid q$.
      have h_divides_q : (g : ℕ) ∣ Int.natAbs q := by
        have h_divides_q : ∀ p : ℕ, Nat.Prime p → p ∣ g → padicValNat p g ≤ padicValNat p (Int.natAbs q) := by
          intros p hp hp_div_g
          have h_div_q_rD : padicValNat p g ≤ padicValNat p (Int.natAbs (q + r * D)) := by
            have h_div_q_rD : g ∣ Int.natAbs (q + r * D) := by
              exact Int.natCast_dvd.mp hg_div_q_rD |> fun h => by simpa [ ← Int.natCast_dvd_natCast ] using h;
            generalize_proofs at *; (
            rw [ ← Nat.factorization_le_iff_dvd ] at h_div_q_rD <;> norm_num at * <;> try positivity;
            · have := h_div_q_rD p; simp_all +decide [ Nat.factorization ] ;
            · intro H; specialize h_valuation p hp hp_div_g; simp_all +decide ;
              specialize h_valuation_eq p hp hp_div_g ; rw [ eq_comm ] at h_valuation_eq ; simp_all +decide  ;
              contrapose! h_valuation_eq; simp_all +decide [ ← Int.natCast_dvd_natCast ] ;
              exact ⟨ hp.ne_one, by simpa using dvd_trans ( Int.natCast_dvd_natCast.mpr ( Nat.dvd_of_mod_eq_zero ( Nat.mod_eq_zero_of_dvd <| by { exact ( by { by_contra h; simp_all +decide  } ) } ) ) ) ( show ( p : ℤ ) ∣ ( i - k : ℤ ) from by { rw [ show ( i - k : ℤ ) = - ( j - l ) * lcm_range ( s * t ) by linarith ] ; exact dvd_mul_of_dvd_right ( Int.natCast_dvd_natCast.mpr <| Nat.dvd_of_mod_eq_zero <| Nat.mod_eq_zero_of_dvd <| by { exact ( by { by_contra h; simp_all +decide [ padicValNat.eq_zero_of_not_dvd ] } ) } ) _ } ) ⟩ ;)
          rw [h_valuation_eq p hp hp_div_g] at h_div_q_rD
          exact h_div_q_rD
        generalize_proofs at *; (
        rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num [ hq_zero ];
        · -- For any prime $p$, if $p$ divides $g$, then by $h_divides_q$, the exponent of $p$ in $g$'s factorization is less than or equal to the exponent of $p$ in $q$'s factorization. If $p$ does not divide $g$, then the exponent of $p$ in $g$'s factorization is zero, which is trivially less than or equal to the exponent of $p$ in $q$'s factorization.
          intros p
          by_cases hp : p ∣ g
          generalize_proofs at *; (
          by_cases hp_prime : Nat.Prime p <;> simp +decide [ hp_prime, Nat.factorization ] at hp ⊢ ; aesop ( simp_config := { singlePass := true } ) ;);
          simp +decide [ hp, Nat.factorization_eq_zero_of_not_dvd ];
        · positivity;);
      simpa [ ← Int.natCast_dvd_natCast ] using h_divides_q
  exact hg_div_q.trans (by norm_num)

-- The elements α_{i,j} = M + i + jD are distinct when D > s.
lemma alpha_distinct (s t D M : ℕ) (hD_large : s < D)
    (i₁ j₁ i₂ j₂ : ℕ) (hi₁' : i₁ ≤ s)
    (hi₂ : 1 ≤ i₂) (hi₂' : i₂ ≤ s) (hj₂ : 1 ≤ j₂) (hj₂' : j₂ ≤ t)
    (h_eq : M + i₁ + j₁ * D = M + i₂ + j₂ * D) :
    i₁ = i₂ ∧ j₁ = j₂ := by
      have h_eq' : i₁ = i₂ := by
        nlinarith only [ h_eq, hD_large, show j₁ = j₂ by nlinarith only [ h_eq, hD_large, hi₁', hi₂', hj₂' ] ];
      aesop

-- The set {M + i + jD : 1 ≤ i ≤ s, 1 ≤ j ≤ t} has exactly s*t elements.
lemma alpha_set_card (s t D M : ℕ) (hD_large : s < D) :
    (Finset.image (fun p : Fin s × Fin t => M + (p.1.val + 1) + (p.2.val + 1) * D) Finset.univ).card = s * t := by
      rw [ Finset.card_image_of_injOn, Finset.card_univ ] ; aesop;
      intro p hp q hq h_eq;
      have := alpha_distinct s t D M hD_large ( p.1 + 1 ) ( p.2 + 1 ) ( q.1 + 1 ) ( q.2 + 1 ) ; aesop;

-- The multiples of α_{i,j} in the interval (x₀-M, x₀-M+2(M+s+tD)) are x₀-i and x₀+M+jD.
lemma multiples_in_interval (M D s t i j : ℕ)
    (_hs : 1 ≤ s) (_ht : 1 ≤ t) (hi : 1 ≤ i) (_hi' : i ≤ s) (hj : 1 ≤ j) (_hj' : j ≤ t)
    (hM : M > 2 * s + 2 * t * D)
    (x₀ : ℤ) (hx₀ : (↑(M + i + j * D) : ℤ) ∣ (x₀ - ↑i))
    (b : ℤ) (hb_lower : x₀ - ↑M < b)
    (hb_upper : b < x₀ - ↑M + 2 * ↑(M + s + t * D))
    (hb_div : (↑(M + i + j * D) : ℤ) ∣ b) :
    b = x₀ - ↑i ∨ b = x₀ + ↑M + ↑j * ↑D := by
      obtain ⟨ k, hk ⟩ := hb_div
      obtain ⟨ m, hm ⟩ := hx₀
      have hk_bounds : k = m ∨ k = m + 1 := by
        norm_num +zetaDelta at *;
        exact Classical.or_iff_not_imp_left.2 fun h => by cases lt_or_gt_of_ne h <;> nlinarith [ show ( M + i + j * D : ℤ ) > 0 by positivity ] ;
      grind

-- The union {x₀ - i : 1 ≤ i ≤ s} ∪ {x₀ + M + jD : 1 ≤ j ≤ t} has card ≤ s + t.
lemma small_set_card (s t M D : ℕ) (x₀ : ℤ) (_hM : 0 < M) :
    (Finset.image (fun i : Fin s => x₀ - ↑(i.val + 1)) Finset.univ ∪
     Finset.image (fun j : Fin t => x₀ + ↑M + ↑(j.val + 1) * ↑D) Finset.univ).card ≤ s + t := by
       refine le_trans ( Finset.card_union_le _ _ ) ?_;
       gcongr <;> simp +decide ;
       · exact Finset.card_image_le.trans ( by simp );
       · exact Finset.card_image_le.trans ( by simp )

-- If gcd(n_i, m) | d for all i in S, then gcd(lcm_S n, m) | d.
lemma gcd_lcm_dvd_of_all_gcd_dvd {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (n : ι → ℕ) (m : ℕ) (d : ℤ)
    (h : ∀ i ∈ S, (Nat.gcd (n i) m : ℤ) ∣ d) :
    (Nat.gcd (S.lcm n) m : ℤ) ∣ d := by
      induction' S using Finset.induction with i S hi ih <;> simp_all +decide ;
      have h_gcd_lcm : ∀ a b m : ℕ, (Nat.gcd (Nat.lcm a b) m : ℤ) ∣ Int.lcm (Nat.gcd a m : ℤ) (Nat.gcd b m : ℤ) := by
        intros a b m
        have h_gcd_lcm : ∀ p : ℕ, Nat.Prime p → (Nat.factorization (Nat.gcd (Nat.lcm a b) m) p) ≤ (Nat.factorization (Nat.lcm (Nat.gcd a m) (Nat.gcd b m)) p) := by
          intro p pp; by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hm : m = 0 <;> simp_all +decide [ Nat.factorization_gcd, Nat.factorization_lcm ] ;
          omega;
        by_cases h : Nat.gcd ( Nat.lcm a b ) m = 0 <;> simp_all +decide ;
        exact_mod_cast Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.1 fun p => by by_cases hp : Nat.Prime p <;> aesop;
      refine' dvd_trans ( h_gcd_lcm _ _ _ ) _;
      exact Int.coe_lcm_dvd h.1 ih

/-- Generalized CRT: given finitely many congruences with pairwise compatible
    moduli, a simultaneous solution exists. -/
lemma generalized_crt (ι : Type*) [DecidableEq ι] (S : Finset ι)
    (n : ι → ℕ) (hn : ∀ i ∈ S, 0 < n i)
    (a : ι → ℤ)
    (compat : ∀ i ∈ S, ∀ j ∈ S, (Int.gcd (n i) (n j) : ℤ) ∣ (a i - a j)) :
    ∃ x₀ : ℤ, ∀ i ∈ S, (↑(n i) : ℤ) ∣ (x₀ - a i) := by
      induction' S using Finset.induction with i S hi ih generalizing a;
      · exact ⟨ 0, by simp +decide ⟩;
      · obtain ⟨ x₁, hx₁ ⟩ := ih ( fun j hj => hn j ( Finset.mem_insert_of_mem hj ) ) a ( fun j hj k hk => compat j ( Finset.mem_insert_of_mem hj ) k ( Finset.mem_insert_of_mem hk ) );
        -- Set L = S.lcm n. For each j ∈ S, gcd(n(j), n(i)) | (x₁ - a(i)) because:
        set L := S.lcm n
        have h_gcd_div : (Nat.gcd L (n i) : ℤ) ∣ (x₁ - a i) := by
          have h_gcd_div : ∀ j ∈ S, (Nat.gcd (n j) (n i) : ℤ) ∣ (x₁ - a i) := by
            exact fun j hj => by simpa using dvd_add ( dvd_trans ( Int.natCast_dvd_natCast.mpr ( Nat.gcd_dvd_left _ _ ) ) ( hx₁ j hj ) ) ( compat j ( Finset.mem_insert_of_mem hj ) i ( Finset.mem_insert_self _ _ ) ) ;
          convert gcd_lcm_dvd_of_all_gcd_dvd S n ( n i ) ( x₁ - a i ) h_gcd_div using 1;
        -- By Nat.gcd_eq_gcd_ab: ↑(gcd L (n i)) = ↑L * gcdA L (n i) + ↑(n i) * gcdB L (n i).
        obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (Nat.gcd L (n i) : ℤ) = u * L + v * (n i) := by
          exact Int.gcd_eq_gcd_ab L ( n i ) ▸ ⟨ Int.gcdA L ( n i ), Int.gcdB L ( n i ), by ring ⟩;
        -- Set x₀ = x₁ - u * L * c.
        obtain ⟨c, hc⟩ : ∃ c : ℤ, x₁ - a i = (Nat.gcd L (n i) : ℤ) * c := h_gcd_div
        use x₁ - u * L * c;
        intro j hj; by_cases hj' : j = i <;> simp_all +decide [ sub_sub ] ;
        · exact ⟨ v * c, by linarith ⟩;
        · convert dvd_sub ( hx₁ j hj ) ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Int.natCast_dvd_natCast.mpr ( Finset.dvd_lcm hj ) ) u ) c ) using 1 ; ring

-- Given gcd(α_{i,j}, α_{k,l}) | (i-k), a simultaneous solution x₀ ≡ i (mod α_{i,j}) exists.
lemma construction_crt (s t D M : ℕ) (hs : 2 ≤ s) (hst : s ≤ t)
    (hD : D = lcm_range (s * t))
    (hM_large : M > 2 * s + 2 * t * D)
    (hM_avoid : ∀ p : ℕ, Nat.Prime p → p > s * t →
      (∃ q r : ℤ, 0 < |q| ∧ |q| < ↑s ∧ |r| < ↑t ∧ (p : ℤ) ∣ (q + r * ↑D)) →
      ∀ i j : ℕ, 1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t →
        ¬((p : ℤ) ∣ (↑M + ↑i + ↑j * ↑D))) :
    ∃ x₀ : ℤ, ∀ i j : ℕ, 1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t →
      (↑(M + i + j * D) : ℤ) ∣ (x₀ - ↑i) := by
        have h_crt : ∃ x₀ : ℤ, ∀ i ∈ Finset.Icc 1 s ×ˢ Finset.Icc 1 t, (↑(M + i.1 + i.2 * D) : ℤ) ∣ (x₀ - (i.1 : ℤ)) := by
          apply generalized_crt;
          · exact fun i hi => by nlinarith [ Finset.mem_Icc.mp ( Finset.mem_product.mp hi |>.1 ), Finset.mem_Icc.mp ( Finset.mem_product.mp hi |>.2 ) ] ;
          · intros i hi j hj
            have h_gcd_div : (Int.gcd (↑(M + i.1 + i.2 * D)) (↑(M + j.1 + j.2 * D)) : ℤ) ∣ (↑i.1 - ↑j.1) := by
              have := @gcd_claim s t hs hst D hD M hM_large hM_avoid i.1 j.1 ( Finset.mem_Icc.mp ( Finset.mem_product.mp hi |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp hi |>.1 ) |>.2 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp hj |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp hj |>.1 ) |>.2 ) i.2 j.2 ( Finset.mem_Icc.mp ( Finset.mem_product.mp hi |>.2 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp hi |>.2 ) |>.2 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp hj |>.2 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp hj |>.2 ) |>.2 ) ; aesop;
            exact h_gcd_div;
        exact ⟨ h_crt.choose, fun i j hi hj hi' hj' => h_crt.choose_spec ( i, j ) ( Finset.mem_product.mpr ⟨ Finset.mem_Icc.mpr ⟨ hi, hj ⟩, Finset.mem_Icc.mpr ⟨ hi', hj' ⟩ ⟩ ) ⟩

-- The existence of M avoiding bad residue classes.
set_option maxHeartbeats 800000 in
lemma M_exists (s t D : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) (_hst : s ≤ t)
    (hD : D = lcm_range (s * t)) :
    ∃ M : ℕ, M > 2 * s + 2 * t * D ∧
    ∀ p : ℕ, Nat.Prime p → p > s * t →
      (∃ q r : ℤ, 0 < |q| ∧ |q| < ↑s ∧ |r| < ↑t ∧ (p : ℤ) ∣ (q + r * ↑D)) →
      ∀ i j : ℕ, 1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t →
        ¬((p : ℤ) ∣ (↑M + ↑i + ↑j * ↑D)) := by
          obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, badPrimes s t D = P := by
            have h_finite : Set.Finite (badPrimes s t D) := by
              exact badPrimes_finite s t D ( hD.symm ▸ by
                refine' Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) _;
                · induction s * t <;> simp_all +decide;
                  exact Nat.lcm_ne_zero ( Nat.succ_ne_zero _ ) ‹_›;
                · exact dvd_lcm_range _ _ ( by linarith ) ( by nlinarith ) );
            exact ⟨ h_finite.toFinset, h_finite.coe_toFinset.symm ⟩;
          -- By the Chinese Remainder Theorem, there exists an M that avoids all the forbidden residue classes modulo each prime in P.
          obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ p ∈ P, ∀ i j : ℕ, 1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t → ¬((p : ℤ) ∣ (M₀ + i + j * D)) := by
            -- For each prime $p \in P$, consider the set of forbidden residues modulo $p$.
            have h_forbidden_residues : ∀ p ∈ P, ∃ r : ℕ, r < p ∧ ∀ i j : ℕ, 1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t → ¬(r ≡ -i - j * D [ZMOD p]) := by
              intro p hp
              have h_forbidden_residues : Finset.card (Finset.image (fun (ij : ℕ × ℕ) => (-ij.1 - ij.2 * D : ℤ) % p) (Finset.product (Finset.Icc 1 s) (Finset.Icc 1 t))) ≤ s * t := by
                exact le_trans ( Finset.card_image_le ) ( by erw [ Finset.card_product ] ; norm_num );
              -- Since there are $p$ possible residues modulo $p$, and at most $s \cdot t$ of them are forbidden, there must be at least one residue that is not forbidden.
              have h_exists_non_forbidden : ∃ r : ℕ, r < p ∧ ¬(r : ℤ) ∈ Finset.image (fun (ij : ℕ × ℕ) => (-ij.1 - ij.2 * D : ℤ) % p) (Finset.product (Finset.Icc 1 s) (Finset.Icc 1 t)) := by
                have h_exists_non_forbidden : Finset.card (Finset.image (fun (ij : ℕ × ℕ) => (-ij.1 - ij.2 * D : ℤ) % p) (Finset.product (Finset.Icc 1 s) (Finset.Icc 1 t))) < p := by
                  nontriviality;
                  exact lt_of_le_of_lt h_forbidden_residues ( by have := hP.symm.subset hp; exact this.2.1 );
                contrapose! h_exists_non_forbidden;
                have h_exists_non_forbidden : Finset.image (fun r : ℕ => (r : ℤ)) (Finset.range p) ⊆ Finset.image (fun (ij : ℕ × ℕ) => (-ij.1 - ij.2 * D : ℤ) % p) (Finset.product (Finset.Icc 1 s) (Finset.Icc 1 t)) := by
                  exact Finset.image_subset_iff.mpr fun r hr => h_exists_non_forbidden r ( Finset.mem_range.mp hr );
                exact le_trans ( by rw [ Finset.card_image_of_injective _ Nat.cast_injective ] ; simp ) ( Finset.card_mono h_exists_non_forbidden );
              simp_all +decide [ Int.ModEq ];
              exact ⟨ h_exists_non_forbidden.choose, h_exists_non_forbidden.choose_spec.1, fun i j hi hj hi' hj' => Ne.symm ( h_exists_non_forbidden.choose_spec.2 i j hi hj hi' hj' ) |> fun h => by simpa [ Int.emod_eq_of_lt, h_exists_non_forbidden.choose_spec.1 ] using h ⟩;
            choose! r hr₁ hr₂ using h_forbidden_residues;
            -- By the Chinese Remainder Theorem, there exists an M₀ that satisfies all the congruences simultaneously.
            obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ p ∈ P, M₀ ≡ r p [MOD p] := by
              have h_crt : ∀ p ∈ P, ∃ x : ℕ, x ≡ r p [MOD p] ∧ ∀ q ∈ P, q ≠ p → x ≡ 0 [MOD q] := by
                -- For each prime $p \in P$, let $y_p$ be the multiplicative inverse of $\prod_{q \in P, q \neq p} q$ modulo $p$.
                intros p hp
                obtain ⟨y_p, hy_p⟩ : ∃ y_p : ℕ, y_p * (∏ q ∈ P.erase p, q) ≡ 1 [MOD p] := by
                  have h_coprime : Nat.gcd (∏ q ∈ P.erase p, q) p = 1 := by
                    refine' Nat.Coprime.prod_left _;
                    intro q hq; have := Nat.coprime_primes ( show Nat.Prime q from ?_ ) ( show Nat.Prime p from ?_ ) ; aesop;
                    · exact hP.symm.subset ( Finset.mem_of_mem_erase hq ) |>.1;
                    · exact hP.symm.subset hp |>.1;
                  have := Nat.exists_mul_mod_eq_one_of_coprime h_coprime;
                  rcases p with ( _ | _ | p ) <;> simp_all +decide [ mul_comm, Nat.ModEq, Nat.mod_one ];
                  · exact h_coprime;
                  · exact ⟨ this.choose, this.choose_spec.2 ⟩;
                use y_p * (∏ q ∈ P.erase p, q) * r p;
                exact ⟨ by simpa using hy_p.mul_right _, fun q hq hqp => Nat.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
              choose! x hx₁ hx₂ using h_crt;
              use ∑ p ∈ P, x p; intro p hp; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
              rw [ Finset.sum_eq_single p ] <;> aesop;
            use M₀; intro p hp i j hi hj hi' hj'; specialize hM₀ p hp; specialize hr₂ p hp i j hi hj hi' hj'; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.natCast_eq_natCast_iff ] ;
            simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
            exact fun h => hr₂ <| by linear_combination' h;
          -- Choose N such that M = M₀ + N * (∏p_i) is greater than 2s + 2tD.
          obtain ⟨N, hN⟩ : ∃ N : ℕ, M₀ + N * (∏ p ∈ P, p) > 2 * s + 2 * t * D := by
            use 2 * s + 2 * t * D + 1;
            -- Since $2s + 2tD + 1$ is positive and the product of primes is at least 1, multiplying them gives something larger than $2s + 2tD$. Adding $M₀$ (which is non-negative) ensures the whole expression is even larger.
            have h_prod_pos : 0 < ∏ p ∈ P, p := by
              apply Finset.prod_pos
              intro p hp
              have hp_prime : Nat.Prime p := by
                exact hP.symm.subset hp |>.1
              exact Nat.Prime.pos hp_prime;
            nlinarith [ mul_pos h_prod_pos ( show 0 < 2 * s + 2 * t * D + 1 by positivity ) ];
          refine' ⟨ M₀ + N * ∏ p ∈ P, p, mod_cast hN, fun p hp₁ hp₂ hp₃ i j hi hj hi' hj' ↦ _ ⟩;
          convert hM₀ p ( hP.subset ⟨ hp₁, hp₂, hp₃ ⟩ ) i j hi hj hi' hj' using 1 ; push_cast ; ring_nf;
          rw [ Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero ] ; norm_num [ Int.add_emod, Int.mul_emod, Finset.prod_eq_prod_diff_singleton_mul ( show p ∈ P from hP.subset ⟨ hp₁, hp₂, hp₃ ⟩ ) ] ;

-- For s, t ≥ 2 with s ≤ t, f(st) ≤ s + t.
lemma erdos_f_upper_bound_ge2 (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) (hst : s ≤ t) :
    erdos_f (s * t) ≤ s + t := by
      -- Apply the lemma M_exists to obtain an M that avoids the bad residue classes.
      obtain ⟨M, hM_large, hM_avoid⟩ := M_exists s t (lcm_range (s * t)) hs ht hst rfl;
      apply erdos_f_le_of_few_multiples ( s * t ) ( s + t ) (Finset.image ( fun p : Fin s × Fin t => M + ( p.1.val + 1 ) + ( p.2.val + 1 ) * lcm_range ( s * t ) ) Finset.univ) ( by
        aesop ) ( by
        convert alpha_set_card s t ( lcm_range ( s * t ) ) M _;
        refine' Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) ( dvd_lcm_range _ _ _ _ ) <;> norm_num [ hs, ht, hst ];
        · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| Nat.ne_of_gt <| Nat.recOn ( s * t ) ( by decide ) fun n ihn => by exact Nat.lcm_pos ( Nat.succ_pos _ ) ihn;
        · nlinarith ) ( ↑ ( Classical.choose ( construction_crt s t ( lcm_range ( s * t ) ) M hs hst rfl hM_large hM_avoid ) ) - ↑M ) (Finset.image ( fun i : Fin s => ↑ ( Classical.choose ( construction_crt s t ( lcm_range ( s * t ) ) M hs hst rfl hM_large hM_avoid ) ) - ↑ ( i.val + 1 ) ) Finset.univ ∪ Finset.image ( fun j : Fin t => ↑ ( Classical.choose ( construction_crt s t ( lcm_range ( s * t ) ) M hs hst rfl hM_large hM_avoid ) ) + ↑M + ↑ ( j.val + 1 ) * ↑ ( lcm_range ( s * t ) ) ) Finset.univ) ( by
        convert small_set_card s t M ( lcm_range ( s * t ) ) ( Classical.choose ( construction_crt s t ( lcm_range ( s * t ) ) M hs hst rfl hM_large hM_avoid ) ) ( by nlinarith ) using 1 ) ( by
        intros b hb hb_div
        obtain ⟨a, haA, ha_div⟩ := hb_div
        obtain ⟨p, hp⟩ := Finset.mem_image.mp haA
        obtain ⟨i, j, hi, hj, rfl⟩ := hp;
        have := Classical.choose_spec ( construction_crt s t ( lcm_range ( s * t ) ) M hs hst rfl hM_large hM_avoid ) ( p.1 + 1 ) ( p.2 + 1 ) ( by linarith [ Fin.is_lt p.1 ] ) ( by linarith [ Fin.is_lt p.1 ] ) ( by linarith [ Fin.is_lt p.2 ] ) ( by linarith [ Fin.is_lt p.2 ] );
        have := multiples_in_interval M ( lcm_range ( s * t ) ) s t ( p.1 + 1 ) ( p.2 + 1 ) ( by linarith [ Fin.is_lt p.1 ] ) ( by linarith [ Fin.is_lt p.2 ] ) ( by linarith [ Fin.is_lt p.1 ] ) ( by linarith [ Fin.is_lt p.1 ] ) ( by linarith [ Fin.is_lt p.2 ] ) ( by linarith [ Fin.is_lt p.2 ] ) hM_large ( Classical.choose ( construction_crt s t ( lcm_range ( s * t ) ) M hs hst rfl hM_large hM_avoid ) ) this b ( by linarith [ Finset.mem_Ioo.mp hb ] ) ( by
          refine' lt_of_lt_of_le ( Finset.mem_Ioo.mp hb |>.2 ) _;
          gcongr;
          simp +zetaDelta at *;
          exact fun a b => by nlinarith [ Fin.is_lt a, Fin.is_lt b, show lcm_range ( s * t ) ≥ 0 by exact Nat.zero_le _ ] ; ) ( by
          exact ha_div );
        rcases this with ( rfl | rfl ) <;> [ exact Finset.mem_union_left _ ( Finset.mem_image.mpr ⟨ p.1, Finset.mem_univ _, rfl ⟩ ) ; exact Finset.mem_union_right _ ( Finset.mem_image.mpr ⟨ p.2, Finset.mem_univ _, rfl ⟩ ) ] )

-- f(st) ≤ s + t for all positive integers s and t.
theorem erdos_f_upper_bound (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    erdos_f (s * t) ≤ s + t := by
      by_cases hs2 : s ≥ 2;
      · by_cases ht2 : t ≥ 2;
        · by_cases hst : s ≤ t;
          · exact erdos_f_upper_bound_ge2 s t hs2 ht2 hst;
          · convert erdos_f_upper_bound_ge2 t s ht2 hs2 ( by linarith ) using 1 ; ring_nf;
            ring;
        · interval_cases t ; simp_all +decide;
          exact le_trans ( erdos_f_le s ) ( by linarith );
      · interval_cases s ; simp_all +decide [ add_comm ];
        exact le_trans ( erdos_f_le _ ) ( by simp +arith +decide )

-- Variant of multiples_in_interval for the wider interval (x₀ - M, x₀ + 2M + 1 + 2D).
lemma multiples_in_interval_wide (M D i j : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j)
    (x₀ : ℤ) (hx₀ : (↑(M + i + j * D) : ℤ) ∣ (x₀ - ↑i))
    (b : ℤ) (hb_lower : x₀ - ↑M < b)
    (hb_upper : b < x₀ + 2 * ↑M + 1 + 2 * ↑D)
    (hb_div : (↑(M + i + j * D) : ℤ) ∣ b) :
    b = x₀ - ↑i ∨ b = x₀ + ↑M + ↑j * ↑D := by
  obtain ⟨ k, hk ⟩ := hb_div
  obtain ⟨ m, hm ⟩ := hx₀;
  have hk_bounds : k = m ∨ k = m + 1 := by
    norm_num +zetaDelta at *;
    exact Classical.or_iff_not_imp_left.2 fun h => by cases lt_or_gt_of_ne h <;> nlinarith [ show ( M + i + j * D : ℤ ) > 0 by positivity ] ;
  grind +ring

-- The sup (maximum) of the construction set is M + s + t * D.
lemma alpha_set_sup (s t D M : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hD_large : s < D) :
    (Finset.image (fun p : Fin s × Fin t => M + (p.1.val + 1) + (p.2.val + 1) * D)
      Finset.univ).sup id = M + s + t * D := by
  refine' le_antisymm _ _;
  · simp +zetaDelta at *;
    exact fun a b => by nlinarith [ Fin.is_lt a, Fin.is_lt b ] ;
  · rcases s with ( _ | s ) <;> rcases t with ( _ | t ) <;> norm_num at *;
    exact ⟨ ⟨ s, by linarith ⟩, ⟨ t, by linarith ⟩, by norm_num ⟩

-- M_exists with an additional lower bound constraint.
lemma M_exists_large (s t D : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) (hst : s ≤ t)
    (hD : D = lcm_range (s * t)) (N : ℕ) :
    ∃ M : ℕ, M > N ∧ M > 2 * s + 2 * t * D ∧
    ∀ p : ℕ, Nat.Prime p → p > s * t →
      (∃ q r : ℤ, 0 < |q| ∧ |q| < ↑s ∧ |r| < ↑t ∧ (p : ℤ) ∣ (q + r * ↑D)) →
      ∀ i j : ℕ, 1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t →
        ¬((p : ℤ) ∣ (↑M + ↑i + ↑j * ↑D)) := by
  obtain ⟨ M₀, hM₀₁, hM₀₂ ⟩ := M_exists s t D hs ht hst hD;
  obtain ⟨ P, hP ⟩ : ∃ P : ℕ, P ≠ 0 ∧ ∀ p : ℕ, Nat.Prime p → p > s * t → (∃ q r : ℤ, 0 < |q| ∧ |q| < s ∧ |r| < t ∧ (p : ℤ) ∣ (q + r * D)) → (p : ℤ) ∣ P := by
    have h_bad_primes_finite : Set.Finite {p : ℕ | Nat.Prime p ∧ p > s * t ∧ ∃ q r : ℤ, 0 < |q| ∧ |q| < s ∧ |r| < t ∧ (p : ℤ) ∣ (q + r * D)} := by
      apply badPrimes_finite;
      rw [ hD ];
      refine' Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) _;
      · induction s * t <;> simp_all +decide;
        exact Nat.lcm_ne_zero ( Nat.succ_ne_zero _ ) ‹_›;
      · exact dvd_lcm_range _ _ ( by nlinarith ) ( by nlinarith );
    exact ⟨ ∏ p ∈ h_bad_primes_finite.toFinset, p, Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| by aesop, fun p hp₁ hp₂ hp₃ => mod_cast Finset.dvd_prod_of_mem _ <| h_bad_primes_finite.mem_toFinset.mpr ⟨ hp₁, hp₂, hp₃ ⟩ ⟩;
  refine' ⟨ M₀ + ( N + 1 ) * P, _, _, _ ⟩;
  · nlinarith [ Nat.pos_of_ne_zero hP.1 ];
  · nlinarith [ Nat.pos_of_ne_zero hP.1 ];
  · intro p pp p2 h; intros i j hi hj hi' hj'; specialize hM₀₂ p pp p2 h i j hi hj hi' hj'
    intro h_dvd; apply hM₀₂
    have hp_dvd_NP : (p : ℤ) ∣ ((↑N + 1) * ↑P : ℤ) := dvd_mul_of_dvd_right (hP.2 p pp p2 h) _
    have h_eq : (↑(M₀ + (N + 1) * P) + ↑i + ↑j * ↑D : ℤ) = ((↑N + 1) * ↑P) + (↑M₀ + ↑i + ↑j * ↑D) := by push_cast; ring
    rw [h_eq] at h_dvd; exact (Int.dvd_add_right hp_dvd_NP).mp h_dvd

-- For s, t ≥ 2 with s ≤ t, the 3maxA construction.
set_option maxHeartbeats 800000 in
lemma Lemma_3maxA_ge2 (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (A : Finset ℕ), (∀ a ∈ A, 0 < a) ∧ A.card = s * t ∧
    ∃ (x : ℤ) (S : Finset ℤ), S.card ≤ s + t ∧
      ∀ b ∈ Finset.Ioo x (x + ⌈((3 : ℝ) - ε) * ↑(A.sup id)⌉),
        (∃ a ∈ A, (a : ℤ) ∣ b) → b ∈ S := by
  obtain ⟨D, hD⟩ : ∃ D, D = lcm_range (s * t) ∧ D > s := by
    norm_num +zetaDelta at *;
    -- By definition of lcm_range, we know that lcm_range (s * t) is divisible by s * t.
    have h_div : s * t ∣ lcm_range (s * t) := by
      exact dvd_lcm_range _ _ ( by nlinarith ) ( by nlinarith );
    nlinarith [ Nat.le_of_dvd ( Nat.pos_of_ne_zero ( show lcm_range ( s * t ) ≠ 0 from Nat.ne_of_gt <| Nat.recOn ( s * t ) ( by decide ) fun n hn => Nat.lcm_pos ( Nat.succ_pos _ ) hn ) ) h_div ];
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, N₀ ≥ Nat.ceil ((3 - ε) * (s + t * D) / ε) ∧ N₀ > 2 * s + 2 * t * D := by
    exact ⟨ Max.max ( Nat.ceil ( ( 3 - ε ) * ( s + t * D ) / ε ) ) ( 2 * s + 2 * t * D + 1 ), le_max_left _ _, by norm_num ⟩;
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M > N₀ ∧ M > 2 * s + 2 * t * D ∧ ∀ p : ℕ, Nat.Prime p → p > s * t → (∃ q r : ℤ, 0 < |q| ∧ |q| < s ∧ |r| < t ∧ (p : ℤ) ∣ (q + r * D)) → ∀ i j : ℕ, 1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t → ¬((p : ℤ) ∣ (M + i + j * D)) := by
    convert M_exists_large s t D hs ht hst hD.1 N₀ using 1;
  use Finset.image (fun p : Fin s × Fin t => M + (p.1.val + 1) + (p.2.val + 1) * D) Finset.univ, by
    aesop, by
    convert alpha_set_card s t D M hD.right using 1, (Classical.choose (construction_crt s t D M hs hst hD.left hM.right.left hM.right.right)) - M, Finset.image (fun i : Fin s => (Classical.choose (construction_crt s t D M hs hst hD.left hM.right.left hM.right.right)) - (i.val + 1)) Finset.univ ∪ Finset.image (fun j : Fin t => (Classical.choose (construction_crt s t D M hs hst hD.left hM.right.left hM.right.right)) + M + (j.val + 1) * D) Finset.univ, by
    convert small_set_card s t M D ( Classical.choose ( construction_crt s t D M hs hst hD.1 hM.2.1 hM.2.2 ) ) ( by linarith ) using 1, by
    intro b hb hb_div
    obtain ⟨a, haA, ha_div⟩ := hb_div
    have ha_form : ∃ i j : ℕ, 1 ≤ i ∧ i ≤ s ∧ 1 ≤ j ∧ j ≤ t ∧ a = M + i + j * D := by
      rw [ Finset.mem_image ] at haA; obtain ⟨ p, hp, rfl ⟩ := haA; exact ⟨ p.1 + 1, p.2 + 1, by linarith [ Fin.is_lt p.1 ], by linarith [ Fin.is_lt p.1 ], by linarith [ Fin.is_lt p.2 ], by linarith [ Fin.is_lt p.2 ], rfl ⟩ ;
    obtain ⟨i, j, hi, hi', hj, hj', rfl⟩ := ha_form
    have hb_cases : b = (Classical.choose (construction_crt s t D M hs hst hD.left hM.right.left hM.right.right)) - i ∨ b = (Classical.choose (construction_crt s t D M hs hst hD.left hM.right.left hM.right.right)) + M + j * D := by
      apply multiples_in_interval_wide M D i j hi hj (Classical.choose (construction_crt s t D M hs hst hD.left hM.right.left hM.right.right)) (Classical.choose_spec (construction_crt s t D M hs hst hD.left hM.right.left hM.right.right) i j hi hi' hj hj') b (by
      linarith [ Finset.mem_Ioo.mp hb ]) (by
      have h_ceil : ⌈(3 - ε) * (M + s + t * D)⌉ ≤ 3 * M + 1 + 2 * D := by
        have h_ceil : (3 - ε) * (M + s + t * D) ≤ 3 * M + 1 + 2 * D := by
          have := Nat.le_ceil ( ( 3 - ε ) * ( s + t * D ) / ε ) ; rw [ div_le_iff₀ hε ] at this; nlinarith [ show ( M : ℝ ) ≥ N₀ + 1 by exact_mod_cast hM.1, show ( N₀ : ℝ ) ≥ ⌈ ( 3 - ε ) * ( s + t * D ) / ε⌉₊ by exact_mod_cast hN₀.1 ] ;
        generalize_proofs at *; (
        exact Int.ceil_le.mpr ( mod_cast h_ceil ))
      generalize_proofs at *;
      have h_sup : (Finset.image (fun p : Fin s × Fin t => M + (p.1.val + 1) + (p.2.val + 1) * D) Finset.univ).sup id = M + s + t * D := by
        apply alpha_set_sup s t D M (by linarith) (by linarith) (by linarith)
      generalize_proofs at *; (
      norm_num [ h_sup ] at * ; linarith [ hb.2 ] ;)) ha_div
    obtain hb_case | hb_case := hb_cases;
    · simp [hb_case];
      exact Or.inl ⟨ ⟨ i - 1, by omega ⟩, by cases i <;> aesop ⟩;
    · simp [hb_case];
      exact Or.inr ⟨ ⟨ j - 1, by omega ⟩, Or.inl <| by cases j <;> norm_num at * ; linarith ⟩;

-- For s=1, the 3maxA result via direct construction.
lemma Lemma_3maxA_s1 (t : ℕ) (ht : 0 < t)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (A : Finset ℕ), (∀ a ∈ A, 0 < a) ∧ A.card = t ∧
    ∃ (x : ℤ) (S : Finset ℤ), S.card ≤ 1 + t ∧
      ∀ b ∈ Finset.Ioo x (x + ⌈((3 : ℝ) - ε) * ↑(A.sup id)⌉),
        (∃ a ∈ A, (a : ℤ) ∣ b) → b ∈ S := by
  -- Choose D = 1 and M large enough such that εM ≥ (3-ε)(1 + tD) and M > 2 + 2tD.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ε * M ≥ (3 - ε) * (1 + t * 1) ∧ M > 2 + 2 * t * 1 := by
    exact ⟨ ⌈ ( 3 - ε ) * ( 1 + t ) / ε⌉₊ + 2 + 2 * t + 1, by push_cast; nlinarith [ Nat.le_ceil ( ( 3 - ε ) * ( 1 + t ) / ε ), mul_div_cancel₀ ( ( 3 - ε ) * ( 1 + t ) ) hε.ne' ], by linarith ⟩;
  refine' ⟨ Finset.image ( fun j : Fin t => M + 1 + ( j.val + 1 ) * 1 ) Finset.univ, _, _, _ ⟩ <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    exact fun i j h => Fin.ext h;
  · refine' ⟨ 1 - M, { 0 } ∪ Finset.image ( fun j : Fin t => ( 1 : ℤ ) + M + ( j.val + 1 ) * 1 ) Finset.univ, _, _ ⟩ <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
    · exact le_trans ( Finset.card_insert_le _ _ ) ( by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ] ; norm_num ) ;
    · intro b hb₁ hb₂ x hx; rcases hx with ⟨ k, rfl ⟩ ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at *;
      · exact Or.inr ⟨ x, by ring ⟩;
      · -- By simplifying, we can see that the expression is indeed less than or equal to $3M + 1 + 2$.
        have h_simplify : ⌈(3 - ε) * (M + 1 + t)⌉ ≤ 3 * M + 1 + 2 := by
          exact Int.ceil_le.mpr ( by norm_num; nlinarith );
        norm_num [ show ( Finset.univ.sup fun j : Fin t => M + 1 + ( j.val + 1 ) ) = M + 1 + t from by
                    refine' le_antisymm _ _ <;> norm_num [ Finset.sup_le_iff ];
                    exact ⟨ ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩, by cases t <;> norm_num at * ⟩ ] at * ; nlinarith [ show ( x : ℝ ) + 1 ≤ t by norm_cast; linarith [ Fin.is_lt x ] ] ;
      · grind

/-- For any ε ∈ (0,1) and any positive integers s, t, there exists a set A with s*t
    elements for which an interval of length (3-ε)·max(A) contains at most s+t
    multiples of elements of A. -/
theorem large_3maxA_version (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (A : Finset ℕ), (∀ a ∈ A, 0 < a) ∧ A.card = s * t ∧
    ∃ (x : ℤ) (S : Finset ℤ), S.card ≤ s + t ∧
      ∀ b ∈ Finset.Ioo x (x + ⌈((3 : ℝ) - ε) * ↑(A.sup id)⌉),
        (∃ a ∈ A, (a : ℤ) ∣ b) → b ∈ S := by
  by_cases hst : s ≥ 2 ∧ t ≥ 2;
  · by_cases hst' : s ≤ t;
    · exact Lemma_3maxA_ge2 s t hst.1 hst.2 hst' ε hε hε1 |> fun ⟨ A, hA₁, hA₂, x, S, hS₁, hS₂ ⟩ => ⟨ A, hA₁, hA₂, x, S, hS₁, hS₂ ⟩;
    · convert Lemma_3maxA_ge2 t s ( by linarith ) ( by linarith ) ( by linarith ) ε hε hε1 using 1 ; ring_nf;
  · by_cases hs_ge2 : 2 ≤ s;
    · rcases t with ( _ | _ | t ) <;> simp_all +decide;
      obtain ⟨ A, hA₁, hA₂, x, S, hS₁, hS₂ ⟩ := Lemma_3maxA_s1 s hs ε hε hε1;
      exact ⟨ A, hA₁, hA₂, x, S, by linarith, fun b hb₁ hb₂ a ha ha' => hS₂ b ( Finset.mem_Ioo.mpr ⟨ hb₁, hb₂ ⟩ ) ⟨ a, ha, ha' ⟩ ⟩;
    · interval_cases s ; simp +decide at *;
      have := Lemma_3maxA_s1 t ht ε hε hε1;
      obtain ⟨ A, hA₁, hA₂, x, S, hS₁, hS₂ ⟩ := this; exact ⟨ A, hA₁, hA₂, x, S, hS₁, fun b hb₁ hb₂ a ha₁ ha₂ => hS₂ b ( Finset.mem_Ioo.mpr ⟨ hb₁, hb₂ ⟩ ) ⟨ a, ha₁, ha₂ ⟩ ⟩ ;

-- ════════════════════════════════════════════════════════════════════════════════
-- Part 4: The lower bound  (Section 4)
-- ════════════════════════════════════════════════════════════════════════════════

/-- The maximum deficiency of a family t of finite sets, defined as
    max_{S ⊆ ι} (|S| - |⋃_{i ∈ S} t(i)|).
    When this is 0, Hall's condition holds. -/
noncomputable def maxDeficiency {α : Type*} {ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (t : ι → Finset α) : ℕ :=
  (Finset.univ : Finset (Finset ι)).sup
    (fun T => T.card - (T.biUnion t).card)

/-- Deficient Hall's theorem: a matching of size |A| − maxDeficiency always exists. -/
lemma deficient_hall {α : Type*} {ι : Type*} [DecidableEq α] [DecidableEq ι] [Fintype ι]
    (t : ι → Finset α) :
    ∃ (S : Finset ι) (f : S → α),
      Function.Injective f ∧
      (∀ x : S, f x ∈ t x.1) ∧
      Fintype.card ι - maxDeficiency t ≤ S.card := by
        -- Let $d = \text{maxDeficiency } t$.
        set d := maxDeficiency t with hd;
        -- Add $d$ fresh dummy elements to the codomain: define $\alpha' = \alpha \oplus \text{Fin } d$, and define $t' : \iota \to \text{Finset } \alpha'$ by $t'(i) = \text{image inl } (t i) \cup \text{image inr } \text{Finset.univ}$.
        set α' : Type _ := α ⊕ Fin d
        set t' : ι → Finset α' := fun i => Finset.image (fun a => Sum.inl a) (t i) ∪ Finset.image (fun _ => Sum.inr ‹_›) (Finset.univ : Finset (Fin d));
        -- By Hall's theorem, there exists an injection $f' : \iota \to \alpha'$ such that $f'(i) \in t'(i)$ for all $i$.
        obtain ⟨f', hf'⟩ : ∃ f' : ι → α', Function.Injective f' ∧ ∀ i, f' i ∈ t' i := by
          have h_hall : ∀ S : Finset ι, S.card ≤ (S.biUnion t').card := by
            intro S
            have h_card : (S.biUnion t').card ≥ (S.biUnion t).card + d - (d - (S.card - (S.biUnion t).card)) := by
              have h_card : (S.biUnion t').card ≥ (S.biUnion t).card + (Finset.univ : Finset (Fin d)).card - (Finset.univ.filter (fun x => ∀ i ∈ S, Sum.inr x ∉ t' i)).card := by
                have h_card : (S.biUnion t').card ≥ (S.biUnion t).card + (Finset.univ : Finset (Fin d)).card - (Finset.univ.filter (fun x => ∀ i ∈ S, Sum.inr x ∉ t' i)).card := by
                  have h_union : S.biUnion t' = Finset.image (fun a => Sum.inl a) (S.biUnion t) ∪ Finset.image (fun x => Sum.inr x) (Finset.univ \ Finset.univ.filter (fun x => ∀ i ∈ S, Sum.inr x ∉ t' i)) := by
                    ext x; aesop;
                  rw [ h_union, Finset.card_union_of_disjoint ];
                  · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
                    · simp +decide [Finset.card_sdiff];
                      omega;
                    · grind +ring;
                    · grind;
                  · simp +decide [ Finset.disjoint_left ];
                exact h_card;
              simp +zetaDelta at *;
              split_ifs at h_card <;> simp_all +decide [ Finset.card_univ ];
              · simp_all +decide [ Finset.eq_empty_of_forall_notMem ‹∀ i, i∉S› ];
              · exact le_add_right h_card;
            have h_card : d ≥ S.card - (S.biUnion t).card := by
              exact Finset.le_sup ( f := fun T => T.card - ( T.biUnion t ).card ) ( Finset.mem_univ S );
            omega;
          have := Finset.all_card_le_biUnion_card_iff_exists_injective t';
          exact this.mp h_hall;
        -- Let $S = \{i \in \iota \mid f'(i) \in \text{image inl } \alpha\}$.
        set S := Finset.univ.filter (fun i => f' i ∈ Finset.image (fun a => Sum.inl a) (t i)) with hS_def;
        have hS_card : S.card ≥ Fintype.card ι - d := by
          have hS_card : (Finset.univ \ S).card ≤ d := by
            have hS_card : (Finset.univ \ S).card ≤ Finset.card (Finset.image (fun i => f' i) (Finset.univ \ S)) := by
              rw [ Finset.card_image_of_injective _ hf'.1 ];
            have hS_card : Finset.image (fun i => f' i) (Finset.univ \ S) ⊆ Finset.image (fun x => Sum.inr x) (Finset.univ : Finset (Fin d)) := by
              grind;
            exact le_trans ‹_› ( le_trans ( Finset.card_le_card hS_card ) ( Finset.card_image_le.trans ( by simp +decide ) ) );
          grind;
        refine' ⟨ S, fun x => Classical.choose ( Finset.mem_image.mp ( Finset.mem_filter.mp ( by aesop : x.val ∈ S ) |>.2 ) ), _, _, hS_card ⟩ <;> simp_all +decide [ Function.Injective ];
        · grind;
        · intro i x hx hx'; have := Classical.choose_spec ( Finset.mem_image.mp ( Finset.mem_filter.mp ( by aesop : i ∈ S ) |>.2 ) ) ; aesop;

/--  min(|A|, |A| − max_{∅ ≠ S ⊆ A}(|S| − |Γ(S)|)). -/
lemma deficientHall {α : Type*} {ι : Type*} [DecidableEq α] [DecidableEq ι] [Fintype ι]
    (t : ι → Finset α) :
    ∃ (S : Finset ι) (f : S → α),
      Function.Injective f ∧
      (∀ x : S, f x ∈ t x.1) ∧
      min (Fintype.card ι) (Fintype.card ι - maxDeficiency t) ≤ S.card := by
  obtain ⟨S, f, hf_inj, hf_mem, hf_card⟩ := deficient_hall t
  exact ⟨S, f, hf_inj, hf_mem, le_trans (min_le_right _ _) hf_card⟩

/-- If every subset S ⊆ A has |Γ(S)| ≥ g(|S|) where g satisfies
    t - g(t) ≤ m - g(m), then there is a matching of size ≥ g(m). -/
lemma matching_from_neighborhood_bound {α : Type*} {ι : Type*} [DecidableEq α] [DecidableEq ι]
    [Fintype ι] (t : ι → Finset α)
    (g : ℕ → ℕ)
    (hg : ∀ S : Finset ι, g S.card ≤ (S.biUnion t).card)
    (hg_le : g (Fintype.card ι) ≤ Fintype.card ι)
    (hg_mono : ∀ s : ℕ, s ≤ Fintype.card ι → s - g s ≤ Fintype.card ι - g (Fintype.card ι)) :
    ∃ (S : Finset ι) (f : S → α),
      Function.Injective f ∧
      (∀ x : S, f x ∈ t x.1) ∧
      g (Fintype.card ι) ≤ S.card := by
        -- By definition of maxDeficiency, we know that maxDeficiency t ≤ Fintype.card ι - g (Fintype.card ι).
        have h_max_deficiency : maxDeficiency t ≤ Fintype.card ι - g (Fintype.card ι) := by
          exact Finset.sup_le fun S _ => le_trans ( Nat.sub_le_sub_left ( hg S ) _ ) ( hg_mono _ ( Finset.card_le_univ S ) );
        -- Apply deficient_hall to get S, f with S.card ≥ |ι| - maxDeficiency ≥ g(|ι|).
        obtain ⟨S, f, hf_inj, hf_mem, hf_card⟩ := deficient_hall t;
        exact ⟨ S, f, hf_inj, hf_mem, le_trans ( by omega ) hf_card ⟩

-- The largest multiple of a in (x, x + amax] exceeds x.
lemma u_gt_x (a amax : ℕ) (ha : 0 < a) (ha_le : a ≤ amax) (x : ℤ) :
    x < largestMultiple a (x + ↑amax) := by
  have := largestMultiple_gt a ha (x + amax)
  linarith [show (a : ℤ) ≤ amax by exact_mod_cast ha_le]

-- When a_m ∤ x, the largest multiple plus a stays below x + 2·amax.
lemma u_plus_a_lt (a amax : ℕ) (ha : 0 < a) (ha_le : a ≤ amax) (x : ℤ)
    (hx : ¬ (↑amax : ℤ) ∣ x) :
    largestMultiple a (x + ↑amax) + ↑a < x + 2 * ↑amax := by
  by_cases ha_eq : a = amax
  · simp_all +decide [largestMultiple]
    cases lt_or_gt_of_ne (show (x + amax : ℤ) % amax ≠ 0 from
      fun h => hx <| Int.dvd_of_emod_eq_zero <| by simpa [Int.add_emod] using h) <;>
    nlinarith [Int.emod_add_mul_ediv (x + amax) amax,
      Int.emod_nonneg (x + amax) (by positivity : (amax : ℤ) ≠ 0)]
  · linarith [largestMultiple_le a ha (x + amax),
      show (a : ℤ) < amax by exact_mod_cast lt_of_le_of_ne ha_le ha_eq]

-- The injection φ: a ↦ (u_a, u_a + a) is injective, giving |S| ≤ |Γ₋|·|Γ₊|.
lemma case1_injection_bound (A : Finset ℕ) (amax : ℕ)
    (hamax : amax = A.sup id)
    (x : ℤ) (hx : ¬ (↑amax : ℤ) ∣ x)
    (S : Finset ℕ) :
    S.card ≤
      (S.image (fun a => largestMultiple a (x + ↑amax))).card *
      (S.image (fun a => largestMultiple a (x + ↑amax) + ↑a)).card := by
        have hu_mono : Finset.card S ≤ Finset.card (Finset.image (fun a => (largestMultiple a (x + amax), largestMultiple a (x + amax) + a)) S) := by
          rw [ Finset.card_image_of_injOn ];
          intro a ha b hb; aesop;
        exact hu_mono.trans ( by rw [ ← Finset.card_product ] ; exact Finset.card_le_card <| Finset.image_subset_iff.mpr fun a ha => Finset.mem_product.mpr ⟨ Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ ha ⟩ )

-- In Case 1, the neighborhood satisfies |Γ(S)| ≥ 2√|S|.
lemma case1_neighborhood_bound (A : Finset ℕ) (amax : ℕ)
    (hamax : amax = A.sup id)
    (hA_pos : ∀ a ∈ A, 0 < a) (_hA_ne : A.Nonempty)
    (x : ℤ) (hx : ¬ (↑amax : ℤ) ∣ x)
    (S : Finset ℕ) (hS : S ⊆ A) (_hS_ne : S.Nonempty) :
    2 * Real.sqrt ↑S.card ≤
      ((Finset.Ioo x (x + 2 * ↑amax)).filter (fun b => ∃ a ∈ S, (a : ℤ) ∣ b)).card := by
        have h_card_bound : S.card ≤ (Finset.image (fun a => largestMultiple a (x + amax)) S).card * (Finset.image (fun a => largestMultiple a (x + amax) + a) S).card := by
          exact case1_injection_bound A amax hamax x hx S
        have h_image_subset : Finset.image (fun a => largestMultiple a (x + amax)) S ⊆ Finset.filter (fun b => ∃ a ∈ S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax)) ∧ Finset.image (fun a => largestMultiple a (x + amax) + a) S ⊆ Finset.filter (fun b => ∃ a ∈ S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax)) := by
          simp_all +decide [ Finset.subset_iff ]
          constructor <;> intro a ha <;> refine' ⟨ _, _ ⟩
          · constructor <;> linarith [ u_gt_x a ( A.sup id ) ( hA_pos a ( hS ha ) ) ( Finset.le_sup ( f := id ) ( hS ha ) ) x, largestMultiple_le a ( hA_pos a ( hS ha ) ) ( x + A.sup id ), Finset.le_sup ( f := id ) ( hS ha ) ]
          · exact ⟨ a, ha, largestMultiple_is_multiple a _ ⟩
          · constructor <;> linarith [ u_gt_x a ( A.sup id ) ( hA_pos a ( hS ha ) ) ( Finset.le_sup ( f := id ) ( hS ha ) ) x, u_plus_a_lt a ( A.sup id ) ( hA_pos a ( hS ha ) ) ( Finset.le_sup ( f := id ) ( hS ha ) ) x hx ]
          · exact ⟨ a, ha, dvd_add ( largestMultiple_is_multiple _ _ ) ( dvd_refl _ ) ⟩
        have h_union_card : (Finset.image (fun a => largestMultiple a (x + amax)) S).card + (Finset.image (fun a => largestMultiple a (x + amax) + a) S).card ≤ (Finset.filter (fun b => ∃ a ∈ S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax))).card := by
          rw [ ← Finset.card_union_of_disjoint ]
          · exact Finset.card_le_card ( Finset.union_subset h_image_subset.1 h_image_subset.2 )
          · norm_num [ Finset.disjoint_right ]
            intro a ha b hb; have := largestMultiple_le a ( hA_pos a ( hS ha ) ) ( x + amax ) ; have := largestMultiple_le b ( hA_pos b ( hS hb ) ) ( x + amax ) ; have := largestMultiple_gt a ( hA_pos a ( hS ha ) ) ( x + amax ) ; have := largestMultiple_gt b ( hA_pos b ( hS hb ) ) ( x + amax ) ; norm_num at * ; linarith [ hA_pos a ( hS ha ), hA_pos b ( hS hb ) ]
        have h_gamma_bound : 2 * Real.sqrt (Finset.card S) ≤ (Finset.image (fun a => largestMultiple a (x + amax)) S).card + (Finset.image (fun a => largestMultiple a (x + amax) + a) S).card := by
          nlinarith only [ sq_nonneg ( ( Finset.card ( Finset.image ( fun a => largestMultiple a ( x + amax ) ) S ) : ℝ ) - ( Finset.card ( Finset.image ( fun a => largestMultiple a ( x + amax ) + a ) S ) : ℝ ) ), show ( Finset.card S : ℝ ) ≤ ( Finset.card ( Finset.image ( fun a => largestMultiple a ( x + amax ) ) S ) : ℝ ) * ( Finset.card ( Finset.image ( fun a => largestMultiple a ( x + amax ) + a ) S ) : ℝ ) by exact_mod_cast h_card_bound, Real.mul_self_sqrt ( Nat.cast_nonneg S.card ) ]
        exact h_gamma_bound.trans ( mod_cast h_union_card )

/-- The injection map φ for Case 2 of the lower bound. For each a ∈ S,
    we define φ(a) = (φ₁(a), φ₂(a)) where the coordinates depend on
    whether a divides b₀ = x + amax and further conditions. -/
noncomputable def case2_phi1 (b₀ : ℤ) (amax : ℕ) (a : ℕ) : ℤ :=
  let u := largestMultiple a b₀
  if ¬((a : ℤ) ∣ b₀) then u  -- T1
  else if 2 * a < amax ∧ ¬((2 * ↑a : ℤ) ∣ b₀) then b₀ - 2 * a  -- T2
  else b₀ - a  -- T3

noncomputable def case2_phi2 (b₀ : ℤ) (amax : ℕ) (a : ℕ) : ℤ :=
  let u := largestMultiple a b₀
  if ¬((a : ℤ) ∣ b₀) then u + a  -- T1
  else if 2 * a < amax ∧ ¬((2 * ↑a : ℤ) ∣ b₀) then b₀ + 2 * a  -- T2
  else b₀ + a  -- T3

-- First coordinate of φ is a multiple of a, lies in (x, x+amax), and ≠ b₀.
lemma case2_phi1_in_range (b₀ x : ℤ) (amax : ℕ) (a : ℕ)
    (ha_pos : 0 < a) (ha_lt : a < amax)
    (hb₀ : b₀ = x + ↑amax) :
    (a : ℤ) ∣ case2_phi1 b₀ amax a ∧
    x < case2_phi1 b₀ amax a ∧
    case2_phi1 b₀ amax a < b₀ := by
      unfold case2_phi1;
      split_ifs <;> simp_all +decide [ dvd_sub_right ];
      · linarith;
      · linarith;
      · exact ⟨ largestMultiple_is_multiple a _, by linarith [ largestMultiple_gt a ha_pos ( x + amax ) ], lt_of_le_of_ne ( largestMultiple_le a ha_pos _ ) fun h => ‹¬ ( a : ℤ ) ∣ x + amax› <| h.symm ▸ largestMultiple_is_multiple a _ ⟩

-- Second coordinate of φ is a multiple of a and lies in (x+amax, x+2*amax).
lemma case2_phi2_in_range (b₀ x : ℤ) (amax : ℕ) (a : ℕ)
    (ha_pos : 0 < a) (ha_lt : a < amax)
    (hb₀ : b₀ = x + ↑amax) :
    (a : ℤ) ∣ case2_phi2 b₀ amax a ∧
    b₀ < case2_phi2 b₀ amax a ∧
    case2_phi2 b₀ amax a < x + 2 * ↑amax := by
      unfold case2_phi2 largestMultiple at *;
      split_ifs <;> simp_all +decide [ dvd_add_right ];
      · grind;
      · grind;
      · constructor <;> nlinarith [ Int.mul_ediv_add_emod ( x + amax ) a, Int.emod_nonneg ( x + amax ) ( by positivity : ( a : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( x + amax ) ( by positivity : ( a : ℤ ) > 0 ) ]

-- The injection φ for Case 2 is injective on S ⊆ A \ {amax}.
lemma case2_phi_injective (b₀ : ℤ) (amax : ℕ)
    (S : Finset ℕ) (hS_lt : ∀ a ∈ S, a < amax) :
    Set.InjOn (fun a => (case2_phi1 b₀ amax a, case2_phi2 b₀ amax a)) ↑S := by
      intro a ha b hb hab;
      by_cases ha' : ( a : ℤ ) ∣ b₀ <;> by_cases hb' : ( b : ℤ ) ∣ b₀ <;> simp_all +decide [ case2_phi1, case2_phi2 ];
      · grind +ring;
      · split_ifs at hab <;> simp_all +decide [ largestMultiple ];
        · -- From the equations in hab, we can derive that $b = 4a$.
          have hb_eq : b = 4 * a := by
            linarith;
          norm_num [ hb_eq ] at *;
          exact False.elim <| ‹2 * a < amax ∧ ¬2 * ( a : ℤ ) ∣ b₀›.2 <| by exact ⟨ b₀ / ( 4 * a ) * 2 + 1, by linarith ⟩ ;
        · grind;
      · split_ifs at hab <;> simp_all +decide [ largestMultiple ];
        · -- From the equations, we can derive that $a = 4b$.
          have h_eq : a = 4 * b := by
            grind +qlia;
          simp_all +decide;
          exact False.elim <| ‹2 * b < amax ∧ ¬2 * ( b : ℤ ) ∣ b₀›.2 <| by exact ⟨ b₀ / ( 4 * b ) * 2 + 1, by linarith ⟩ ;
        · grind;
      · grind +ring

-- In Case 2, the neighborhood of S in the reduced graph satisfies |Γ₀(S)| ≥ 2√|S|.
lemma case2_neighborhood_bound (A : Finset ℕ) (amax : ℕ)
    (hamax : amax = A.sup id)
    (hA_pos : ∀ a ∈ A, 0 < a)
    (x : ℤ) (hx : (↑amax : ℤ) ∣ x)
    (S : Finset ℕ) (hS : S ⊆ A.erase amax) :
    2 * Real.sqrt ↑S.card ≤
      ((Finset.Ioo x (x + 2 * ↑amax) \ {x + ↑amax}).filter
        (fun b => ∃ a ∈ S, (a : ℤ) ∣ b)).card := by
          -- Let $b₀ = x + amax$.
          set b₀ := x + amax with hb₀;
          -- For each $a \in S \subseteq A.erase amax$, we have $a < amax$ and $a > 0$ by $hA_pos$.
          have hS_lt_amax : ∀ a ∈ S, a < amax := by
            exact fun a ha => lt_of_le_of_ne ( hamax.symm ▸ Finset.le_sup ( f := id ) ( Finset.mem_of_mem_erase ( hS ha ) ) ) fun con => by have := hS ha; aesop;
          have hS_pos : ∀ a ∈ S, 0 < a := by
            exact fun a ha => hA_pos a <| Finset.mem_of_mem_erase <| hS ha;
          -- Let im₁ and im₂ be the images of S under case2_phi1 and case2_phi2, respectively.
          set im₁ := S.image (case2_phi1 b₀ amax)
          set im₂ := S.image (case2_phi2 b₀ amax) with him₂_def
          have him₁_subset : im₁ ⊆ Finset.filter (fun b => ∃ a ∈ S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax) \ {b₀}) := by
            intro b hb
            obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hb
            have h_case1 : (a : ℤ) ∣ case2_phi1 b₀ amax a ∧ x < case2_phi1 b₀ amax a ∧ case2_phi1 b₀ amax a < b₀ := by
              exact case2_phi1_in_range b₀ x amax a ( hS_pos a haS ) ( hS_lt_amax a haS ) rfl
            have h_case2 : case2_phi1 b₀ amax a ≠ b₀ := by
              bv_omega
            have h_case3 : case2_phi1 b₀ amax a ∈ Finset.Ioo x (x + 2 * amax) \ {b₀} := by
              grind
            exact Finset.mem_filter.mpr ⟨h_case3, a, haS, h_case1.left⟩
          have him₂_subset : im₂ ⊆ Finset.filter (fun b => ∃ a ∈ S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax) \ {b₀}) := by
            intro;
            simp +zetaDelta at *;
            rintro a ha rfl; exact ⟨ ⟨ ⟨ by linarith [ case2_phi2_in_range ( x + amax ) x amax a ( hS_pos a ha ) ( hS_lt_amax a ha ) rfl ], by linarith [ case2_phi2_in_range ( x + amax ) x amax a ( hS_pos a ha ) ( hS_lt_amax a ha ) rfl ] ⟩, by linarith [ case2_phi2_in_range ( x + amax ) x amax a ( hS_pos a ha ) ( hS_lt_amax a ha ) rfl ] ⟩, a, ha, by exact case2_phi2_in_range ( x + amax ) x amax a ( hS_pos a ha ) ( hS_lt_amax a ha ) rfl |>.1 ⟩ ;
          have him₁_im₂_disjoint : Disjoint im₁ im₂ := by
            -- By definition of $im₁$ and $im₂$, we know that for any $a \in S$, $case2_phi1 b₀ amax a < b₀$ and $case2_phi2 b₀ amax a > b₀$.
            have h_case2_phi1_lt_b₀ : ∀ a ∈ S, case2_phi1 b₀ amax a < b₀ := by
              exact fun a ha => case2_phi1_in_range b₀ x amax a ( hS_pos a ha ) ( hS_lt_amax a ha ) rfl |>.2.2.trans_le ( by linarith ) ;
            have h_case2_phi2_gt_b₀ : ∀ a ∈ S, b₀ < case2_phi2 b₀ amax a := by
              exact fun a ha => case2_phi2_in_range _ _ _ _ ( hS_pos a ha ) ( hS_lt_amax a ha ) rfl |>.2.1 |> lt_of_le_of_lt ( by linarith ) ;
            exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by obtain ⟨ a, ha₁, ha₂ ⟩ := Finset.mem_image.mp hx₁; obtain ⟨ b, hb₁, hb₂ ⟩ := Finset.mem_image.mp hx₂; linarith [ h_case2_phi1_lt_b₀ a ha₁, h_case2_phi2_gt_b₀ b hb₁ ] ;
          have him_card : im₁.card + im₂.card ≤ (Finset.filter (fun b => ∃ a ∈ S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax) \ {b₀})).card := by
            rw [ ← Finset.card_union_of_disjoint him₁_im₂_disjoint ] ; exact Finset.card_mono <| Finset.union_subset him₁_subset him₂_subset;
          have him₁_im₂_card : S.card ≤ im₁.card * im₂.card := by
            have him₁_im₂_card : S.card ≤ (S.image (fun a => (case2_phi1 b₀ amax a, case2_phi2 b₀ amax a))).card := by
              rw [ Finset.card_image_of_injOn ] ; intro a ha b hb ; have := case2_phi_injective b₀ amax S  hS_lt_amax ; aesop;
            exact him₁_im₂_card.trans ( by rw [ ← Finset.card_product ] ; exact Finset.card_le_card <| Finset.image_subset_iff.mpr fun a ha => Finset.mem_product.mpr ⟨ Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ ha ⟩ ) ;
          have him_am_gm : 2 * Real.sqrt S.card ≤ im₁.card + im₂.card := by
            nlinarith only [ sq_nonneg ( #im₁ - #im₂ : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg S.card ), ( by norm_cast : ( S.card : ℝ ) ≤ #im₁ * #im₂ ) ]
          have him_final : 2 * Real.sqrt S.card ≤ (Finset.filter (fun b => ∃ a ∈ S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax) \ {b₀})).card := by
            exact le_trans him_am_gm ( mod_cast him_card )
          exact_mod_cast him_final

set_option maxHeartbeats 1600000 in
lemma lower_bound_case1 (m : ℕ) (hm : 0 < m) (A : Finset ℕ)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_card : A.card = m)
    (x : ℤ) (hx : ¬ (↑(A.sup id) : ℤ) ∣ x) :
    HasDivMatching A (Finset.Ioo x (x + 2 * ↑(A.sup id)))
      (min m ⌈(2 : ℝ) * Real.sqrt ↑m⌉₊) := by
        have g := matching_from_neighborhood_bound ( fun a : A => Finset.filter ( fun b => ( a.1 : ℤ ) ∣ b ) ( Finset.Ioo x ( x + 2 * A.sup id ) ) ) ( fun n => min n ⌈2 * Real.sqrt n⌉₊ ) ?_ ?_ ?_ <;> norm_num at *;
        · obtain ⟨ S, f, hf_inj, hf_mem, hf_div ⟩ := g;
          refine' HasDivMatching_from_subset _ _ S f hf_inj _ _ _ _ <;> aesop;
        · intro S
          by_cases hS : S.Nonempty;
          · refine' Classical.or_iff_not_imp_left.2 fun h => _;
            convert case1_neighborhood_bound A _ rfl hA_pos ?_ x hx ( S.image Subtype.val ) ?_ ?_ using 1 <;> norm_num [ Finset.card_image_of_injective, Function.Injective ] at *;
            · congr with b ; aesop;
            · exact ⟨ _, hS.choose.2 ⟩;
            · exact Finset.image_subset_iff.mpr fun x hx => x.2;
            · assumption;
          · aesop;
        · -- By definition of min, we know that min(s, ⌈2√s⌉₊) is either s or ⌈2√s⌉₊.
          intros s hs
          by_cases h_case : s ≤ ⌈2 * Real.sqrt s⌉₊;
          · omega;
          · -- Since $s > \lceil 2\sqrt{s} \rceil$, we have $s - \lceil 2\sqrt{s} \rceil \leq m - \lceil 2\sqrt{m} \rceil$.
            have h_diff : s - ⌈2 * Real.sqrt s⌉₊ ≤ m - ⌈2 * Real.sqrt m⌉₊ := by
              have h_diff : ∀ t : ℕ, 1 ≤ t → t - ⌈2 * Real.sqrt t⌉₊ ≤ (t + 1) - ⌈2 * Real.sqrt (t + 1)⌉₊ := by
                intros t ht
                have h_diff : ⌈2 * Real.sqrt (t + 1)⌉₊ ≤ ⌈2 * Real.sqrt t⌉₊ + 1 := by
                  exact Nat.ceil_le.mpr ( by push_cast; linarith [ Nat.le_ceil ( 2 * Real.sqrt t ), show Real.sqrt ( t + 1 ) ≤ Real.sqrt t + 1 / 2 by rw [ Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg t, Real.sq_sqrt ( Nat.cast_nonneg t ), ( by norm_cast : ( 1 :ℝ ) ≤ t ) ] ] );
                omega;
              have h_diff : ∀ t : ℕ, 1 ≤ t → ∀ u : ℕ, t ≤ u → t - ⌈2 * Real.sqrt t⌉₊ ≤ u - ⌈2 * Real.sqrt u⌉₊ := by
                intros t ht u hu
                induction' hu with u hu ih;
                · rfl;
                · exact le_trans ih ( mod_cast h_diff u ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
              exact h_diff s ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at h_case ) ) m ( by linarith );
            grind +ring

set_option maxHeartbeats 3200000 in
lemma lower_bound_case2 (m : ℕ) (hm : 0 < m) (A : Finset ℕ)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_card : A.card = m)
    (x : ℤ) (hx : (↑(A.sup id) : ℤ) ∣ x) :
    HasDivMatching A (Finset.Ioo x (x + 2 * ↑(A.sup id)))
      (min m ⌈(2 : ℝ) * Real.sqrt ↑m⌉₊) := by
        let amax := A.sup id
        let t : A → Finset ℤ := fun a => Finset.filter (fun b => (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax));
        have h_neighborhood_bound : ∀ S : Finset A, Finset.card (Finset.biUnion S t) ≥ min S.card (Nat.ceil (2 * Real.sqrt S.card)) := by
          intro S
          have h_case1 : amax ∈ Finset.image Subtype.val S → Finset.card (Finset.biUnion S t) ≥ 2 * Real.sqrt (Finset.card (Finset.image Subtype.val S) - 1) + 1 := by
            intro h_amax_in_S
            have h_neighborhood_bound_case1 : Finset.card (Finset.biUnion S t) ≥ Finset.card (Finset.filter (fun b => ∃ a ∈ (Finset.image Subtype.val S).erase amax, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax) \ {x + amax})) + 1 := by
              refine' Finset.card_lt_card _;
              constructor <;> simp_all +decide [ Finset.subset_iff ];
              · exact fun y hy₁ hy₂ hy₃ a ha₁ ha₂ ha₃ ha₄ => ⟨ a, ha₂, ha₃, Finset.mem_filter.mpr ⟨ Finset.mem_Ioo.mpr ⟨ hy₁, hy₂ ⟩, ha₄ ⟩ ⟩ ;
              · use x + amax, amax ; aesop;
            have h_neighborhood_bound_case1 : Finset.card (Finset.filter (fun b => ∃ a ∈ (Finset.image Subtype.val S).erase amax, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax) \ {x + amax})) ≥ 2 * Real.sqrt (Finset.card ((Finset.image Subtype.val S).erase amax)) := by
              apply case2_neighborhood_bound A amax rfl hA_pos x hx (Finset.image Subtype.val S |> Finset.erase <| amax) (by
              exact Finset.erase_subset_erase _ <| Finset.image_subset_iff.mpr fun x hx => x.2);
            simp_all +decide [ Finset.card_erase_of_mem ];
            rw [ Nat.cast_sub ] at * <;> norm_num at *;
            · linarith [ show ( Finset.card ( Finset.biUnion S t ) : ℝ ) ≥ Finset.card ( Finset.filter ( fun b => ∃ a ∈ ( Finset.image Subtype.val S ).erase amax, ( a : ℤ ) ∣ b ) ( Finset.Ioo x ( x + 2 * amax ) \ { x + amax } ) ) + 1 by exact_mod_cast ‹_› ];
            · exact ⟨ _, h_amax_in_S.choose_spec ⟩
          have h_case2 : amax ∉ Finset.image Subtype.val S → Finset.card (Finset.biUnion S t) ≥ 2 * Real.sqrt (Finset.card (Finset.image Subtype.val S)) := by
            intro h_case2
            have h_case2_subset : Finset.image Subtype.val S ⊆ A.erase amax := by
              exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_erase_of_ne_of_mem ( by aesop ) ( x.2 )
            have h_case2_neighborhood : Finset.card (Finset.filter (fun b => ∃ a ∈ Finset.image Subtype.val S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax) \ {x + amax})) ≥ 2 * Real.sqrt (Finset.card (Finset.image Subtype.val S)) := by
              convert case2_neighborhood_bound A amax _ _ _ _ _ using 1 <;> norm_num [ h_case2_subset ];
              all_goals tauto;
            have h_case2_biUnion : Finset.biUnion S t ⊇ Finset.filter (fun b => ∃ a ∈ Finset.image Subtype.val S, (a : ℤ) ∣ b) (Finset.Ioo x (x + 2 * amax) \ {x + amax}) := by
              grind +splitIndPred
            have h_case2_card : Finset.card (Finset.biUnion S t) ≥ 2 * Real.sqrt (Finset.card (Finset.image Subtype.val S)) := by
              exact h_case2_neighborhood.trans ( mod_cast Finset.card_mono h_case2_biUnion )
            exact h_case2_card.trans' (by
            convert le_rfl using 1)
          have h_combined : Finset.card (Finset.biUnion S t) ≥ min (Finset.card (Finset.image Subtype.val S)) (Nat.ceil (2 * Real.sqrt (Finset.card (Finset.image Subtype.val S)))) := by
            by_cases h : amax ∈ Finset.image Subtype.val S <;> simp_all +decide [ Nat.ceil_le ];
            refine' Classical.or_iff_not_imp_left.2 fun h' => _;
            have h_sqrt : Real.sqrt (Finset.card (Finset.image Subtype.val S)) ≤ Real.sqrt (Finset.card (Finset.image Subtype.val S) - 1) + 1 / 2 := by
              rcases k : Finset.card ( Finset.image Subtype.val S ) with ( _ | _ | k ) <;> norm_num [ k ] at *;
              · grind +splitIndPred;
              · rw [ Real.sqrt_le_left ] <;> nlinarith only [ Real.sqrt_nonneg ( ( ↑‹ℕ› : ℝ ) + 1 ), Real.sq_sqrt ( by positivity : 0 ≤ ( ↑‹ℕ› : ℝ ) + 1 ) ];
            linarith [ show ( Finset.card ( Finset.biUnion S t ) : ℝ ) ≥ 2 * Real.sqrt ( Finset.card ( Finset.image Subtype.val S ) - 1 ) + 1 by exact_mod_cast h_case1 ]
          simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
        have h_monotonicity : ∀ s : ℕ, s ≤ m → s - min s (Nat.ceil (2 * Real.sqrt s)) ≤ m - min m (Nat.ceil (2 * Real.sqrt m)) := by
          intro s hs
          have h_monotonicity_step : ∀ k : ℕ, k ≥ 1 → (k : ℕ) - min k (Nat.ceil (2 * Real.sqrt k)) ≤ (k + 1 : ℕ) - min (k + 1) (Nat.ceil (2 * Real.sqrt (k + 1))) := by
            intro k hk
            have h_monotonicity_step : min (k + 1) (Nat.ceil (2 * Real.sqrt (k + 1))) ≤ min k (Nat.ceil (2 * Real.sqrt k)) + 1 := by
              have h_monotonicity_step : Nat.ceil (2 * Real.sqrt (k + 1)) ≤ Nat.ceil (2 * Real.sqrt k) + 1 := by
                have h_monotonicity_step : 2 * Real.sqrt (k + 1) ≤ 2 * Real.sqrt k + 1 := by
                  nlinarith only [ sq_nonneg ( Real.sqrt ( k + 1 ) - Real.sqrt k ), Real.mul_self_sqrt ( show ( k:ℝ ) + 1 ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( k:ℝ ) ≥ 0 by positivity ), Real.sqrt_nonneg ( k + 1 ), Real.sqrt_nonneg k, show ( k:ℝ ) ≥ 1 by norm_cast ]
                generalize_proofs at *; (
                exact Nat.ceil_le.mpr ( by push_cast; linarith [ Nat.le_ceil ( 2 * Real.sqrt k ) ] ) ;)
              generalize_proofs at *; (
              cases min_cases ( k + 1 ) ⌈2 * Real.sqrt ( k + 1 ) ⌉₊ <;> cases min_cases k ⌈2 * Real.sqrt k⌉₊ <;> linarith [ Nat.ceil_pos.mpr ( show 0 < 2 * Real.sqrt k by positivity ), Nat.ceil_pos.mpr ( show 0 < 2 * Real.sqrt ( k + 1 ) by positivity ) ] ;)
            generalize_proofs at *; (
            omega;)
          generalize_proofs at *; (
          have h_monotonicity_chain : ∀ k : ℕ, s ≤ k → k ≤ m → s - min s (Nat.ceil (2 * Real.sqrt s)) ≤ k - min k (Nat.ceil (2 * Real.sqrt k)) := by
            intro k hk₁ hk₂
            induction' hk₁ with k ih
            generalize_proofs at *; (
            rfl);
            by_cases hk : k ≥ 1 <;> simp_all +decide [ Nat.succ_eq_add_one ];
            grind +ring
          generalize_proofs at *; (
          exact h_monotonicity_chain m hs le_rfl));
        have := matching_from_neighborhood_bound t (fun n => min n (Nat.ceil (2 * Real.sqrt n))) (by
        aesop) (by
        exact min_le_left _ _) (by
        aesop);
        obtain ⟨ S, f, hf₁, hf₂, hf₃ ⟩ := this; simp_all +decide ;
        refine' HasDivMatching_from_subset A ( Finset.Ioo x ( x + 2 * amax ) ) S f hf₁ _ _ _ _ <;> aesop ( simp_config := { singlePass := true } ) ;

/-- Core lower bound combining both cases. -/
lemma lower_bound_core (m : ℕ) (hm : 0 < m) (A : Finset ℕ)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_card : A.card = m) (x : ℤ) :
    HasDivMatching A (Finset.Ioo x (x + 2 * ↑(A.sup id)))
      (min m ⌈(2 : ℝ) * Real.sqrt ↑m⌉₊) := by
  by_cases hx : (↑(A.sup id) : ℤ) ∣ x
  · exact lower_bound_case2 m hm A hA_pos hA_card x hx
  · exact lower_bound_case1 m hm A hA_pos hA_card x hx

-- f(m) ≥ min(m, ⌈2√m⌉) for all positive m.
theorem erdos_f_lower_bound (m : ℕ) (hm : 0 < m) :
    min m ⌈(2 : ℝ) * Real.sqrt ↑m⌉₊ ≤ erdos_f m := by
      refine' le_csSup ⟨ m, fun r hr => _ ⟩ _;
      · contrapose! hr;
        simp +zetaDelta at *;
        refine' ⟨ Finset.Icc 1 m, _, _, (0 : ℝ), _ ⟩ <;> norm_num [ Finset.card_range ] at * ; aesop;
        rintro ⟨ c, b, hc, hb, hc', hb', h ⟩;
        exact absurd ( Finset.card_le_card ( show Finset.image c Finset.univ ⊆ Finset.Icc 1 m from Finset.image_subset_iff.mpr fun i _ => hc' i ) ) ( by rw [ Finset.card_image_of_injective _ hc ] ; simpa using by linarith );
      · -- Apply the lower bound core theorem to conclude the proof.
        intros A hA_pos hA_card x
        exact (lower_bound_core m hm A hA_pos hA_card ⌊x⌋).mono (intIoo_int_sub_real x (A.sup id))

-- ════════════════════════════════════════════════════════════════════════════════
-- Part 5: Statement and deduction of the main result  (Section 2)
-- ════════════════════════════════════════════════════════════════════════════════

/-- Main result: f(m) = min(m, ⌈2√m⌉). -/
theorem erdos_f_eq (m : ℕ) (hm : 0 < m) :
    erdos_f m = min m ⌈(2 : ℝ) * Real.sqrt ↑m⌉₊ := by
      refine le_antisymm ( le_min ( erdos_f_le m ) ?_ ) ( erdos_f_lower_bound m hm );
      -- Apply the upper bound result from Theorem 3.1 with s = t = 1.
      have h_upper_bound : ∀ s t : ℕ, 0 < s → 0 < t → erdos_f (s * t) ≤ s + t := by
        exact fun s t a a_1 => erdos_f_upper_bound s t a a_1;
      -- Let $k = \lceil 2\sqrt{m} \rceil$. Then $k^2 \ge 4m$.
      set k := Nat.ceil (2 * Real.sqrt m) with hk
      have hk_sq : k^2 ≥ 4 * m := by
        exact_mod_cast ( by nlinarith [ Nat.le_ceil ( 2 * Real.sqrt m ), Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ) ] : ( k : ℝ ) ^ 2 ≥ 4 * m );
      -- By the upper bound result, we have $erdos_f m \leq s + t$ for any $s$ and $t$ such that $st \geq m$.
      have h_upper_bound_applied : ∀ s t : ℕ, 0 < s → 0 < t → s * t ≥ m → erdos_f m ≤ s + t := by
        intros s t hs ht hst
        have h_mono : erdos_f m ≤ erdos_f (s * t) := by
          apply_rules [ erdos_f_mono ]
        exact le_trans h_mono (h_upper_bound s t hs ht);
      contrapose! h_upper_bound_applied;
      use k / 2, k / 2 + k % 2;
      cases Nat.mod_two_eq_zero_or_one k <;> simp_all +decide;
      · exact ⟨ Nat.lt_ceil.mpr ( by norm_num; nlinarith only [ show ( m : ℝ ) ≥ 1 by norm_cast, Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ) ] ), by nlinarith only [ Nat.mod_add_div k 2, ‹_›, hk_sq ], by linarith [ Nat.mod_add_div k 2, ‹_› ] ⟩;
      · exact ⟨ Nat.lt_ceil.mpr ( by norm_num; nlinarith only [ show ( m : ℝ ) ≥ 1 by norm_cast, Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ) ] ), by nlinarith only [ Nat.div_add_mod ( ⌈2 * Real.sqrt m⌉₊ ) 2, ‹_›, hk_sq ], by omega ⟩

/-- Corollary: for m ≥ 4, f(m) = ⌈2√m⌉. -/
theorem erdos_f_eq_ge4 (m : ℕ) (hm : 4 ≤ m) :
    erdos_f m = ⌈(2 : ℝ) * Real.sqrt ↑m⌉₊ := by
      rw [ erdos_f_eq m ( by linarith ) ];
      exact min_eq_right <| Nat.ceil_le.mpr <| by nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg m ), ( by norm_cast : ( 4 : ℝ ) ≤ m ) ] ;

#print axioms erdos_f_eq
-- 'Erdos650.erdos_f_eq' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos650
