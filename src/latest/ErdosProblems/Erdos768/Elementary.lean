import ErdosProblems.Erdos768.Defs

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — elementary estimates (Section 2 of the paper)

This file collects the elementary counting and arithmetic estimates used in the
upper bound: the uniform divisor-sum bound, the growing divisor moments, the
restricted growing-moment estimate, the large-`ω` tail, the radical-defect
bound, and the one-bit valuation completion.  It also records the reciprocal
staircase sum `∑ 1/h_r` and the scalar optimisation determining the constant
`c₀`.
-/

open scoped Classical BigOperators
open Finset

set_option maxHeartbeats 4000000

namespace Erdos768

/-
**Lemma 2.1 (a uniform divisor-sum bound).**  For all real `X ≥ 1` and
integers `k ≥ 1`, `∑_{n ≤ X} d_k(n) ≤ X (1 + log X)^{k-1}`.
-/
theorem dk_sum_le (X : ℝ) (hX : 1 ≤ X) (k : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (dk k n : ℝ) ≤ X * (1 + Real.log X) ^ (k - 1) := by
  -- For `n ≥ 1`, the set counted by `dk k n` is in bijection with `{ f : Fin k → ℕ | (∀ i, 1 ≤ f i) ∧ ∏ i, f i = n }`, because `∏ f = n ≥ 1` forces each `f i ∣ n` and `f i ≥ 1`, so `f i ∈ n.divisors` is automatic. Hence
  have h_bij : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊, dk k n = Finset.card (Finset.filter (fun f : Fin k → ℕ => ∏ i, f i = n) (Finset.Icc (fun _ => 1) (fun _ => ⌊X⌋₊))) := by
    intro n hn;
    refine' Finset.card_bij ( fun f hf => fun i => f i ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_Icc ];
    · exact fun a ha₁ ha₂ => ⟨ fun i => Nat.pos_of_dvd_of_pos ( ha₁ i |>.1 ) hn.1, fun i => Nat.le_trans ( Nat.le_of_dvd hn.1 ( ha₁ i |>.1 ) ) hn.2 ⟩;
    · exact fun b hb₁ hb₂ hb₃ a => ⟨ hb₃ ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ), by linarith ⟩;
  -- Thus, we can rewrite the sum as
  have h_sum : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, dk k n = Finset.card (Finset.filter (fun f : Fin k → ℕ => 1 ≤ ∏ i, f i ∧ ∏ i, f i ≤ ⌊X⌋₊) (Finset.Icc (fun _ => 1) (fun _ => ⌊X⌋₊))) := by
    rw [ Finset.sum_congr rfl h_bij, Finset.card_filter ];
    simp +decide only [card_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  -- We bound the count of positive `k`-tuples with product `≤ N` by `∑_{n_1,…,n_{k-1} ≤ N} ⌊N/(n_1⋯n_{k-1})⌋`.
  have h_bound : Finset.card (Finset.filter (fun f : Fin k → ℕ => 1 ≤ ∏ i, f i ∧ ∏ i, f i ≤ ⌊X⌋₊) (Finset.Icc (fun _ => 1) (fun _ => ⌊X⌋₊))) ≤ ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => ⌊X⌋₊), ⌊X / (∏ i, f i)⌋₊ := by
    rcases k with ( _ | k ) <;> simp_all +decide [ Fin.prod_univ_succ ];
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.biUnion ( Finset.Icc ( fun _ => 1 ) fun _ => ⌊X⌋₊ ) fun f => Finset.image ( fun g => Fin.cons g f ) ( Finset.Icc 1 ⌊X / ∏ i, ( f i : ℝ ) ⌋₊ );
    · intro f hf; simp_all +decide ;
      refine' ⟨ Fin.tail f, _, f 0, _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ, Pi.le_def ];
      · exact ⟨ fun i => hf.1.1.2 i, fun i => hf.1.2.2 i ⟩;
      · rw [ Nat.le_floor_iff ( by positivity ), le_div_iff₀ ] <;> norm_cast;
        · exact le_trans ( mod_cast hf.2.2 ) ( Nat.floor_le ( by positivity ) );
        · exact Finset.prod_pos fun i _ => hf.1.1.2 i;
    · refine' le_trans ( Finset.card_biUnion_le ) _;
      exact Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans ( by simp );
  -- We bound the sum $\sum_{f : Fin (k - 1) → ℕ} \frac{1}{\prod_{i} f_i}$ by $(1 + \log X)^{k - 1}$.
  have h_sum_bound : ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => ⌊X⌋₊), (1 / (∏ i, f i) : ℝ) ≤ (1 + Real.log ⌊X⌋₊) ^ (k - 1) := by
    -- We bound the sum $\sum_{f : Fin (k - 1) → ℕ} \frac{1}{\prod_{i} f_i}$ by $(1 + \log X)^{k - 1}$ using the inequality $\sum_{i=1}^{N} \frac{1}{i} \leq 1 + \log N$.
    have h_sum_bound : ∀ N : ℕ, 1 ≤ N → ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => N), (1 / (∏ i, f i) : ℝ) ≤ (∑ i ∈ Finset.Icc 1 N, (1 / (i : ℝ))) ^ (k - 1) := by
      intro N hN
      have h_sum_bound : ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => N), (1 / (∏ i, f i) : ℝ) = ∏ i : Fin (k - 1), (∑ j ∈ Finset.Icc 1 N, (1 / (j : ℝ))) := by
        erw [ Finset.prod_sum ];
        refine' Finset.sum_bij ( fun f hf => fun i _ => f i ) _ _ _ _ <;> simp +decide;
        · exact fun a ha₁ ha₂ i => ⟨ ha₁ i, ha₂ i ⟩;
        · simp +contextual [ funext_iff ];
        · exact fun b hb => ⟨ fun i => b i ( Finset.mem_univ i ), ⟨ fun i => hb i |>.1, fun i => hb i |>.2 ⟩, rfl ⟩;
      aesop;
    -- We bound the sum $\sum_{i=1}^{N} \frac{1}{i}$ by $1 + \log N$.
    have h_harmonic_bound : ∀ N : ℕ, 1 ≤ N → ∑ i ∈ Finset.Icc 1 N, (1 / (i : ℝ)) ≤ 1 + Real.log N := by
      intro N hN; induction' hN with N hN ih <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
      rw [ show ( N : ℝ ) + 1 = N * ( 1 + ( N : ℝ ) ⁻¹ ) by nlinarith only [ mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ) ], Real.log_mul ( by positivity ) ( by positivity ) ];
      nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ), Real.log_inv ( 1 + ( N : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( N : ℝ ) ⁻¹ ) ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ) ];
    exact le_trans ( h_sum_bound _ <| Nat.floor_pos.mpr hX ) ( pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => by positivity ) ( h_harmonic_bound _ <| Nat.floor_pos.mpr hX ) _ );
  -- We combine the bounds to conclude the proof.
  have h_final_bound : ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => ⌊X⌋₊), ⌊X / (∏ i, f i)⌋₊ ≤ X * (1 + Real.log ⌊X⌋₊) ^ (k - 1) := by
    refine' le_trans _ ( mul_le_mul_of_nonneg_left h_sum_bound <| by positivity );
    norm_num [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun _ _ => Nat.floor_le <| div_nonneg ( by positivity ) <| Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _;
  refine le_trans ?_ ( h_final_bound.trans ?_ );
  · norm_cast ; aesop;
  · gcongr;
    · exact Nat.cast_pos.mpr ( Nat.floor_pos.mpr hX );
    · exact Nat.floor_le <| by positivity;

/-
Value of the ordered `K`-fold divisor function at a prime power:
`d_K(p^ν) = C(ν+K-1, ν)` (weak compositions of `ν` into `K` parts).
-/
theorem dk_prime_pow (K p ν : ℕ) (hp : p.Prime) :
    dk K (p ^ ν) = Nat.choose (ν + K - 1) ν := by
  -- The set of functions `f : Fin K → ℕ` with `∏ i, f i = p^ν` is in bijection with the set of `K`-tuples of non-negative integers that sum to `ν`.
  have h_bij : ((Fintype.piFinset (fun _ : Fin K => (p ^ ν).divisors)).filter (fun f => ∏ i, f i = p ^ ν)).card = ((Finset.Iic (fun _ : Fin K => ν)).filter (fun e => ∑ i, e i = ν)).card := by
    refine' Finset.card_bij ( fun f hf => fun i => Nat.factorization ( f i ) p ) _ _ _;
    · simp +zetaDelta at *;
      intro a ha hprod; refine' ⟨ fun i => _, _ ⟩;
      · have := ha i; rw [ Nat.dvd_prime_pow hp ] at this; aesop;
      · replace hprod := congr_arg ( fun x => x.factorization p ) hprod ; simp_all +decide [ Nat.Prime.ne_zero ];
        rw [ ← hprod, Nat.factorization_prod ];
        · rw [ Finset.sum_apply' ];
        · intro i hi; specialize ha i; intro H; simp_all +decide [ Finset.prod_eq_zero hi ] ;
          aesop;
    · intro a₁ ha₁ a₂ ha₂ h; ext i; simp_all +decide [ funext_iff ] ;
      simp_all +decide [ Nat.mem_divisors, Nat.dvd_prime_pow hp ];
      obtain ⟨ ⟨ k₁, hk₁, hk₁' ⟩, hk₁'' ⟩ := ha₁.1 i; obtain ⟨ ⟨ k₂, hk₂, hk₂' ⟩, hk₂'' ⟩ := ha₂.1 i; specialize h i; simp_all +decide [ Nat.factorization_pow, hp.ne_zero ] ;
    · intro b hb; use fun i => p ^ b i; simp_all +decide [ Nat.factorization_pow, Finset.prod_pow_eq_pow_sum ] ;
      exact fun i => ⟨ pow_dvd_pow _ ( hb.1 i ), fun h => absurd h hp.ne_zero ⟩;
  -- The number of `K`-tuples of non-negative integers that sum to `ν` is given by the stars and bars theorem.
  have h_stars_and_bars : ∀ K ν : ℕ, ((Finset.Iic (fun _ : Fin K => ν)).filter (fun e => ∑ i, e i = ν)).card = Nat.choose (ν + K - 1) ν := by
    intro K ν; induction' K with K ih generalizing ν <;> simp_all +decide [ Fin.sum_univ_succ ] ;
    · cases ν <;> simp +decide;
    · -- We can split the sum into two parts: one over the first coordinate and one over the rest.
      have h_split : Finset.filter (fun e : Fin (K + 1) → ℕ => e 0 + ∑ i : Fin K, e (Fin.succ i) = ν) (Finset.Iic (fun _ => ν)) = Finset.biUnion (Finset.range (ν + 1)) (fun i => Finset.image (fun e : Fin K → ℕ => Fin.cons i e) (Finset.filter (fun e : Fin K → ℕ => ∑ i, e i = ν - i) (Finset.Iic (fun _ => ν - i)))) := by
        ext e; simp [Finset.mem_biUnion, Finset.mem_image];
        constructor <;> intro h;
        · use e 0, h.1 0, fun i => e i.succ;
          exact ⟨ ⟨ fun i => Nat.le_sub_of_add_le <| by linarith [ h.1 i.succ, Finset.single_le_sum ( fun a _ => Nat.zero_le ( e ( Fin.succ a ) ) ) ( Finset.mem_univ i ) ], eq_tsub_of_add_eq <| by linarith ⟩, by ext i; cases i using Fin.inductionOn <;> rfl ⟩;
        · rcases h with ⟨ a, ha, b, hb, rfl ⟩ ; simp_all +decide;
          exact fun i => by cases i using Fin.inductionOn <;> [ exact ha; exact le_trans ( hb.1 _ ) ( Nat.sub_le _ _ ) ] ;
      rw [ h_split, Finset.card_biUnion ];
      · rw [ Finset.sum_congr rfl fun i hi => Finset.card_image_of_injective _ <| fun x y hxy => by simpa [ Fin.ext_iff ] using! hxy ] ; simp_all +decide [ add_comm ];
        exact Nat.recOn ν ( by norm_num ) fun n ih => by simp_all +decide [ Nat.choose, add_comm, add_left_comm, Finset.sum_range_succ' ] ;
      · intro i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; contrapose! hij; aesop;
  exact h_bij.trans ( h_stars_and_bars K ν )

/-
The ordered `K`-fold divisor function is multiplicative on coprime arguments.
-/
theorem dk_coprime_mul (K a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : Nat.Coprime a b) :
    dk K (a * b) = dk K a * dk K b := by
  unfold dk;
  rw [ ← Finset.card_product ];
  refine' Finset.card_bij ( fun f hf => ( fun i => f i |> fun x => x.gcd a, fun i => f i |> fun x => x.gcd b ) ) _ _ _;
  · simp +zetaDelta at *;
    intro f hf hf'; have := hf; simp_all +decide ;
    -- By definition of gcd, we know that $\prod_{i} \gcd(f_i, a) = a$ and $\prod_{i} \gcd(f_i, b) = b$.
    have h_gcd_prod : (∏ i, Nat.gcd (f i) a) * (∏ i, Nat.gcd (f i) b) = a * b := by
      have h_gcd_prod : ∀ i, Nat.gcd (f i) a * Nat.gcd (f i) b = f i := by
        intro i; rw [ ← Nat.Coprime.gcd_mul ] ;
        · exact Nat.gcd_eq_left ( this i |>.1 );
        · assumption;
      rw [ ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun _ _ => h_gcd_prod _, hf' ];
    have h_gcd_prod_a : (∏ i, Nat.gcd (f i) a) ∣ a := by
      have h_gcd_prod_a : (∏ i, Nat.gcd (f i) a) ∣ a * b ∧ Nat.Coprime (∏ i, Nat.gcd (f i) a) b := by
        exact ⟨ h_gcd_prod ▸ dvd_mul_right _ _, Nat.Coprime.prod_left fun i _ => Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_right _ _ ) h ⟩;
      exact h_gcd_prod_a.2.dvd_of_dvd_mul_right h_gcd_prod_a.1
    have h_gcd_prod_b : (∏ i, Nat.gcd (f i) b) ∣ b := by
      refine' Nat.Coprime.dvd_of_dvd_mul_left _ _;
      exact a;
      · exact Nat.Coprime.prod_left fun i _ => Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_right _ _ ) ( h.symm );
      · exact h_gcd_prod ▸ dvd_mul_left _ _;
    exact ⟨ ⟨ fun i => ⟨ Nat.gcd_dvd_right _ _, hf i |>.1 ⟩, Nat.dvd_antisymm h_gcd_prod_a ( Nat.dvd_of_mul_dvd_mul_right ( by positivity ) <| h_gcd_prod ▸ Nat.mul_dvd_mul_left _ h_gcd_prod_b ) ⟩, ⟨ fun i => ⟨ Nat.gcd_dvd_right _ _, hf i |>.2 ⟩, Nat.dvd_antisymm h_gcd_prod_b ( Nat.dvd_of_mul_dvd_mul_left ( by positivity ) <| h_gcd_prod ▸ Nat.mul_dvd_mul_right h_gcd_prod_a _ ) ⟩ ⟩;
  · simp +contextual [ funext_iff ];
    intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ ha₅ ha₆ x; have := ha₁ x; have := ha₃ x; simp_all +decide ;
    have h_eq : a₁ x = Nat.gcd (a₁ x) a * Nat.gcd (a₁ x) b ∧ a₂ x = Nat.gcd (a₂ x) a * Nat.gcd (a₂ x) b := by
      have h_eq : ∀ {n : ℕ}, n ∣ a * b → n = Nat.gcd n a * Nat.gcd n b := by
        intros n hn; rw [ ← Nat.Coprime.gcd_mul ] ;
        · rw [ Nat.gcd_eq_left hn ];
        · assumption;
      exact ⟨ h_eq ( ha₁ x ), h_eq ( ha₃ x ) ⟩;
    grind;
  · simp +zetaDelta at *;
    intro a_1 b_1 ha_1 ha_2 hb_1 hb_2; use fun i => a_1 i * b_1 i; simp_all +decide ;
    refine' ⟨ ⟨ fun i => ⟨ mul_dvd_mul ( ha_1 i |>.1 ) ( hb_1 i |>.1 ), ha_1 i |>.2, hb_1 i |>.2 ⟩, _ ⟩, _, _ ⟩;
    · rw [ Finset.prod_mul_distrib, ha_2, hb_2 ];
    · ext i; simp +decide [ Nat.gcd_comm ] ;
      refine' Nat.dvd_antisymm _ _;
      · refine' Nat.Coprime.dvd_of_dvd_mul_right _ ( Nat.gcd_dvd_right _ _ );
        exact Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_left _ _ ) ( h.coprime_dvd_right ( hb_1 i |>.1 ) );
      · exact Nat.dvd_gcd ( ha_1 i |>.1 ) ( dvd_mul_right _ _ );
    · ext i; simp +decide [ Nat.gcd_comm ] ;
      refine' Nat.dvd_antisymm _ _;
      · refine' Nat.Coprime.dvd_of_dvd_mul_left _ ( Nat.gcd_dvd_right _ _ );
        exact Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_left _ _ ) ( h.symm.coprime_dvd_right ( ha_1 i |>.1 ) );
      · exact Nat.dvd_gcd ( hb_1 i |>.1 ) ( dvd_mul_left _ _ )

/-
The elementary combinatorial injection `(ν+1)^H ≤ C(ν + 2^H - 1, ν)`.
-/
theorem pow_le_choose (H ν : ℕ) :
    (ν + 1) ^ H ≤ Nat.choose (ν + 2 ^ H - 1) ν := by
  induction' H with H ih;
  · norm_num;
  · rw [ Nat.pow_succ' ];
    rw [ pow_succ' ];
    refine' le_trans ( Nat.mul_le_mul_left _ ih ) _;
    refine' Nat.le_induction _ _ _ ( show 2 ^ H ≥ 1 from Nat.one_le_pow _ _ ( by decide ) );
    · simp +arith +decide;
    · intro n hn ih; rw [ show ν + 2 * ( n + 1 ) - 1 = ( ν + 2 * n - 1 ) + 2 by omega, show ν + ( n + 1 ) - 1 = ( ν + n - 1 ) + 1 by omega ] ;
      rcases ν with ( _ | ν ) <;> simp_all +decide [ Nat.choose_succ_succ, add_mul ];
      have := Nat.add_one_mul_choose_eq ( ν + n ) ν; have := Nat.add_one_mul_choose_eq ( ν + 2 * n ) ν; simp_all +decide [ Nat.choose_succ_succ, add_mul ];
      nlinarith [ Nat.choose_pos ( by linarith : ν ≤ ν + n ), Nat.choose_pos ( by linarith : ν ≤ ν + 2 * n ), Nat.choose_le_succ ( ν + 2 * n ) ν ]

/-
Monotone growth of the multichoose ratio: for `1 ≤ J ≤ K` and `ν ≥ 1`,
`K/J ≤ C(ν+K-1, ν) / C(ν+J-1, ν)`.
-/
theorem choose_ratio_ge (J K ν : ℕ) (hJ : 1 ≤ J) (hJK : J ≤ K) (hν : 1 ≤ ν) :
    (K : ℝ) / J ≤ (Nat.choose (ν + K - 1) ν : ℝ) / (Nat.choose (ν + J - 1) ν : ℝ) := by
  have h_prod : (K : ℝ) / J ≤ ∏ j ∈ Finset.range ν, (K + j : ℝ) / (J + j) := by
    induction hν <;> simp_all +decide [ Finset.prod_range_succ ];
    rw [ mul_div_mul_comm ];
    exact le_trans ‹_› ( le_mul_of_one_le_right ( by positivity ) ( by rw [ le_div_iff₀ ] <;> norm_cast <;> linarith ) );
  convert! h_prod using 1;
  have h_binom : ∀ m : ℕ, (Nat.choose (ν + m - 1) ν : ℝ) = (∏ j ∈ Finset.range ν, (m + j : ℝ)) / Nat.factorial ν := by
    intro m; rw [ eq_div_iff ( by positivity ) ] ; norm_cast;
    rw [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
    rw [ Nat.descFactorial_eq_prod_range ];
    rw [ ← Finset.prod_range_reflect ];
    exact Finset.prod_congr rfl fun x hx => by cases ν <;> norm_num at * ; omega;
  rw [ h_binom K, h_binom J, Finset.prod_div_distrib, div_div_div_cancel_right₀ ( by positivity ) ]

/-
**Lemma 2.2 (growing divisor moments).**  Let `H ≥ 0`, `J = 2^H`, `z ≥ 1`
and `K = ⌈zJ⌉`.  Then for every positive integer `n`,
`z^{ω(n)} τ(n)^H ≤ d_K(n)`.
-/
theorem local_moment (H : ℕ) (z : ℝ) (hz : 1 ≤ z) (n : ℕ) (hn : 1 ≤ n) :
    z ^ (omegaCount n) * (tauCount n : ℝ) ^ H ≤ (dk ⌈z * (2 : ℝ) ^ H⌉₊ n : ℝ) := by
  -- By multiplicative property of dk, we have dk K n = ∏_{p ∈ n.primeFactors} dk K (p^{ν_p}).
  have h_mul : (dk ⌈z * 2 ^ H⌉₊ n : ℝ) = (∏ p ∈ n.primeFactors, (dk ⌈z * 2 ^ H⌉₊ (p ^ (Nat.factorization n p)) : ℝ)) := by
    have h_mul : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ p ∈ S, Nat.Prime p) → (dk ⌈z * 2 ^ H⌉₊ (∏ p ∈ S, p ^ f p)) = (∏ p ∈ S, (dk ⌈z * 2 ^ H⌉₊ (p ^ f p) : ℕ)) := by
      intros S f hf; induction S using Finset.induction <;> simp_all +decide ;
      · convert! dk_prime_pow ⌈z * 2 ^ H⌉₊ 2 0 Nat.prime_two using 1 ; norm_num;
      · rw [ ← ‹dk ⌈z * 2 ^ H⌉₊ ( ∏ p ∈ _, p ^ f p ) = ∏ p ∈ _, dk ⌈z * 2 ^ H⌉₊ ( p ^ f p ) ›, dk_coprime_mul ];
        · exact Nat.one_le_pow _ _ hf.1.pos;
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( hf.2 p hp ) ) _;
        · exact Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hf.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hf.1 ( hf.2 p hp ) ; aesop;
    convert! congr_arg ( ( ↑ ) : ℕ → ℝ ) ( @h_mul n.primeFactors ( fun p => n.factorization p ) fun p hp => Nat.prime_of_mem_primeFactors hp ) using 1;
    · exact congr_arg _ ( congr_arg _ ( Eq.symm <| Nat.factorization_prod_pow_eq_self <| by positivity ) );
    · norm_cast;
  -- By definition of `tauCount` and `omegaCount`, we have `tauCount n = ∏_{p ∈ n.primeFactors} (ν_p + 1)` and `omegaCount n = n.primeFactors.card`.
  have h_tau_omega : (tauCount n : ℝ) = (∏ p ∈ n.primeFactors, (Nat.factorization n p + 1 : ℝ)) ∧ (omegaCount n : ℝ) = n.primeFactors.card := by
    norm_cast;
    exact ⟨ by simpa using! Nat.card_divisors ( by positivity ) |> Eq.trans <| by aesop, rfl ⟩;
  -- Apply the per-prime inequality to each term in the product.
  have h_per_prime : ∀ p ∈ n.primeFactors, z * (Nat.factorization n p + 1 : ℝ) ^ H ≤ (Nat.choose (Nat.factorization n p + ⌈z * 2 ^ H⌉₊ - 1) (Nat.factorization n p) : ℝ) := by
    intro p hp
    have h_per_prime_ineq : z * (Nat.factorization n p + 1 : ℝ) ^ H ≤ (Nat.choose (Nat.factorization n p + ⌈z * 2 ^ H⌉₊ - 1) (Nat.factorization n p) : ℝ) := by
      have h_choose_ratio : (⌈z * 2 ^ H⌉₊ : ℝ) / (2 ^ H : ℝ) ≤ (Nat.choose (Nat.factorization n p + ⌈z * 2 ^ H⌉₊ - 1) (Nat.factorization n p) : ℝ) / (Nat.choose (Nat.factorization n p + 2 ^ H - 1) (Nat.factorization n p) : ℝ) := by
        convert! choose_ratio_ge ( 2 ^ H ) ⌈z * 2 ^ H⌉₊ ( Nat.factorization n p ) _ _ _ using 1 <;> norm_num;
        · grind +splitImp;
        · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil ( z * 2 ^ H ), show ( 2 : ℝ ) ^ H > 0 by positivity ] ;
        · exact Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp )
      have h_choose_ratio : (Nat.choose (Nat.factorization n p + 2 ^ H - 1) (Nat.factorization n p) : ℝ) ≥ (Nat.factorization n p + 1 : ℝ) ^ H := by
        exact_mod_cast pow_le_choose H ( Nat.factorization n p );
      rw [ div_le_div_iff₀ ] at * <;> try positivity;
      · nlinarith [ Nat.le_ceil ( z * 2 ^ H ), show ( 0 : ℝ ) < 2 ^ H by positivity, show ( 0 : ℝ ) < ( n.factorization p + 1 ) ^ H by positivity ];
      · exact lt_of_lt_of_le ( by positivity ) h_choose_ratio;
    convert! h_per_prime_ineq using 1;
  convert! Finset.prod_le_prod ?_ h_per_prime using 1 <;> norm_num [ h_mul, h_tau_omega ];
  · norm_num [ Finset.prod_mul_distrib, Finset.prod_pow ];
  · exact Finset.prod_congr rfl fun p hp => mod_cast dk_prime_pow _ _ _ ( Nat.prime_of_mem_primeFactors hp );
  · exact fun _ _ _ _ => by positivity;

/-
**Lemma 2.3 (a restricted growing-moment estimate).**  With
`ℓ_X = log(1+log X)`, `B = 2^H · ℓ_X`, if `u > B` then
`∑_{m ≤ X, ω(m) ≥ u} τ(m)^H ≤ X exp(-u log(u/B) + u)`.
-/
theorem restricted_moment (X : ℝ) (hX : 3 ≤ X) (H : ℕ) (u : ℝ) (hu : 0 < u)
    (huB : (2 : ℝ) ^ H * Real.log (1 + Real.log X) < u) :
    ∑ m ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun m => u ≤ (omegaCount m : ℝ)),
        (tauCount m : ℝ) ^ H
      ≤ X * Real.exp
          (-u * Real.log (u / ((2 : ℝ) ^ H * Real.log (1 + Real.log X))) + u) := by
  set ℓ := Real.log (1 + Real.log X)
  set B := 2 ^ H * ℓ
  set z := u / B
  have hz : 1 < z := by
    rwa [ one_lt_div ( mul_pos ( pow_pos zero_lt_two _ ) ( Real.log_pos ( by linarith [ Real.log_pos ( by linarith : 1 < X ) ] ) ) ) ];
  -- By `local_moment`, we have `tau(m)^H ≤ z^{-u} * dk(K, m)` for each `m` in the filtered set.
  have h_local_moment : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, u ≤ (omegaCount m : ℝ) → (tauCount m : ℝ) ^ H ≤ z ^ (-u) * (dk ⌈z * (2 : ℝ) ^ H⌉₊ m : ℝ) := by
    intros m hm hmu
    have h_local_moment_step : z ^ u * (tauCount m : ℝ) ^ H ≤ (dk ⌈z * (2 : ℝ) ^ H⌉₊ m : ℝ) := by
      refine' le_trans _ ( local_moment H z ( by linarith ) m ( by linarith [ Finset.mem_Icc.mp hm ] ) );
      exact mul_le_mul_of_nonneg_right ( by exact_mod_cast Real.rpow_le_rpow_of_exponent_le hz.le hmu ) ( by positivity );
    convert! mul_le_mul_of_nonneg_left h_local_moment_step ( Real.rpow_nonneg ( by positivity : 0 ≤ ( z : ℝ ) ) ( -u ) ) using 1 ; rw [ ← mul_assoc, ← Real.rpow_add ( by positivity ) ] ; norm_num [ hu.ne' ];
  -- Summing over the filtered set and then enlarging to all m ∈ Icc 1 ⌊X⌋₊ (all summands nonneg):
  have h_sum_le : (∑ m ∈ Finset.Icc 1 ⌊X⌋₊ with u ≤ (omegaCount m : ℝ), (tauCount m : ℝ) ^ H) ≤ z ^ (-u) * X * (1 + Real.log X) ^ (⌈z * (2 : ℝ) ^ H⌉₊ - 1) := by
    refine' le_trans ( Finset.sum_le_sum fun m hm => h_local_moment m ( Finset.mem_filter.mp hm |>.1 ) ( Finset.mem_filter.mp hm |>.2 ) ) _;
    have h_sum_le : (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (dk ⌈z * (2 : ℝ) ^ H⌉₊ m : ℝ)) ≤ X * (1 + Real.log X) ^ (⌈z * (2 : ℝ) ^ H⌉₊ - 1) := by
      convert! dk_sum_le X ( by linarith ) ⌈z * 2 ^ H⌉₊ ( Nat.ceil_pos.mpr ( by positivity ) ) using 1;
    simpa only [ mul_assoc, Finset.mul_sum _ _ _ ] using! mul_le_mul_of_nonneg_left ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Nat.cast_nonneg _ ) h_sum_le ) ( by positivity );
  -- Bound the last factor: `(1 + Real.log X)^(K-1) = Real.exp (ℓ * (K-1)) ≤ Real.exp (ℓ * (u/ℓ)) = Real.exp u` since `1 + Real.log X = Real.exp ℓ` (as ℓ = log(1+logX), 1+logX>0), `ℓ ≥ 0`, and `(K-1) ≤ u/ℓ`.
  have h_exp_bound : (1 + Real.log X) ^ (⌈z * (2 : ℝ) ^ H⌉₊ - 1) ≤ Real.exp u := by
    have h_exp_bound : (⌈z * (2 : ℝ) ^ H⌉₊ - 1) * ℓ ≤ u := by
      nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ u / ( 2 ^ H * Real.log ( 1 + Real.log X ) ) * 2 ^ H by positivity ), show ( 0 : ℝ ) < 2 ^ H by positivity, show ( 0 : ℝ ) < Real.log ( 1 + Real.log X ) by exact Real.log_pos <| by linarith [ Real.log_pos <| show 1 < X by linarith ], mul_div_cancel₀ u <| show ( 2 ^ H * Real.log ( 1 + Real.log X ) ) ≠ 0 by exact ne_of_gt <| mul_pos ( pow_pos zero_lt_two _ ) <| Real.log_pos <| by linarith [ Real.log_pos <| show 1 < X by linarith ] ];
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
    · rw [ Nat.cast_sub ] <;> norm_num ; linarith;
      positivity;
    · linarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ X ) ];
  convert! h_sum_le.trans ( mul_le_mul_of_nonneg_left h_exp_bound <| by positivity ) using 1 ; rw [ Real.rpow_def_of_pos <| by positivity ] ; ring_nf;
  rw [ mul_assoc, ← Real.exp_add ] ; ring_nf

/-
**Corollary 2.4 (large-`ω` tail).**  With `ℓ_X = log(1+log X)` and `u > ℓ_X`,
`#{ m ≤ X : ω(m) ≥ u } ≤ X exp(-u log(u/ℓ_X) + u)`.
-/
theorem omega_tail (X : ℝ) (hX : 3 ≤ X) (u : ℝ)
    (hu : Real.log (1 + Real.log X) < u) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun m => u ≤ (omegaCount m : ℝ))).card : ℝ)
      ≤ X * Real.exp (-u * Real.log (u / Real.log (1 + Real.log X)) + u) := by
  convert! restricted_moment X hX 0 u _ _ using 1 <;> norm_num;
  · exact lt_of_le_of_lt ( Real.log_nonneg ( by linarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ X ) ] ) ) hu;
  · linarith

/-- `d` is *powerful* (squarefull): every prime dividing it divides it to the
second power. -/
def IsPowerful (d : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ d → p ^ 2 ∣ d

/-
Every powerful number can be written as `a^2 * b^3`.
-/
theorem isPowerful_eq_sq_mul_cube (d : ℕ) (hd : IsPowerful d) :
    ∃ a b : ℕ, d = a ^ 2 * b ^ 3 := by
  by_cases hd0 : d = 0;
  · exact ⟨ 0, 0, hd0 ⟩;
  · obtain ⟨a, b, h⟩ : ∃ a b : ℕ, d = a^2 * b^3 := by
      have h_factorization : ∀ p : ℕ, p.Prime → p ∣ d → 2 ≤ Nat.factorization d p := by
        intro p pp dp; specialize hd p pp dp; rw [ ← Nat.factorization_le_iff_dvd ] at hd <;> simp_all +decide [ Nat.factorization_pow ] ;
        exact pp.ne_zero
      rw [ ← Nat.factorization_prod_pow_eq_self hd0 ];
      -- For each prime factor $p$ of $d$, write $e_p = 2k_p + 3m_p$ where $k_p$ and $m_p$ are non-negative integers.
      have h_exp_decomp : ∀ p : ℕ, p.Prime → p ∣ d → ∃ k m : ℕ, Nat.factorization d p = 2 * k + 3 * m := by
        intro p pp dp; rcases Nat.even_or_odd' ( Nat.factorization d p ) with ⟨ k, hk | hk ⟩ <;> [ exact ⟨ k, 0, by linarith ⟩ ; exact ⟨ k - 1, 1, by linarith [ Nat.sub_add_cancel ( show 1 ≤ k from by linarith [ h_factorization p pp dp ] ) ] ⟩ ] ;
      choose! k m h using h_exp_decomp; use ∏ p ∈ Nat.primeFactors d, p ^ k p, ∏ p ∈ Nat.primeFactors d, p ^ m p; simp +decide [ ← Finset.prod_pow, ← Finset.prod_mul_distrib ] ;
      exact Finset.prod_congr rfl fun p hp => by rw [ h p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ] ; ring;
    generalize_proofs at *; (
    use a, b)

/-
Auxiliary double series: `∑_{a,b} 1/(a^{3/2} · b^{9/4})` converges.
-/
theorem aux_prod_summable :
    Summable (fun mn : ℕ × ℕ =>
      (1 : ℝ) / (mn.1 : ℝ) ^ (3 / 2 : ℝ) * (1 / (mn.2 : ℝ) ^ (9 / 4 : ℝ))) := by
  have h_prod : Summable (fun mn : ℕ × ℕ => (1 : ℝ) / mn.1 ^ (3 / 2 : ℝ) * (1 : ℝ) / mn.2 ^ (9 / 4 : ℝ)) := by
    have h_series1 : Summable (fun n : ℕ => (1 : ℝ) / n ^ (3 / 2 : ℝ)) := by
      norm_num
    have h_series2 : Summable (fun n : ℕ => (1 : ℝ) / n ^ (9 / 4 : ℝ)) := by
      exact Real.summable_one_div_nat_rpow.2 ( by norm_num )
    exact .of_norm <| by simpa [ mul_div_assoc ] using! Summable.mul_norm ( h_series1.norm ) ( h_series2.norm ) ;
  simpa only [ mul_div_assoc ] using! h_prod

/-
The sum over powerful numbers of `d^{-3/4}` converges.
-/
theorem powerful_summable :
    Summable (fun d : ℕ =>
      if IsPowerful d then (1 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ) else 0) := by
  refine' summable_of_sum_le _ _;
  exact ∑' mn : ℕ × ℕ, ( 1 : ℝ ) / ( mn.1 : ℝ ) ^ ( 3 / 2 : ℝ ) * ( 1 / ( mn.2 : ℝ ) ^ ( 9 / 4 : ℝ ) );
  · exact fun _ => by positivity;
  · intro u;
    -- Let $s$ be the image of the filtered set under the selection function.
    obtain ⟨s, hs⟩ : ∃ s : Finset (ℕ × ℕ), (∑ x ∈ u.filter IsPowerful, (1 : ℝ) / (x : ℝ) ^ (3 / 4 : ℝ)) ≤ (∑ mn ∈ s, (1 : ℝ) / (mn.1 : ℝ) ^ (3 / 2 : ℝ) * (1 / (mn.2 : ℝ) ^ (9 / 4 : ℝ))) := by
      have h_image : ∀ d ∈ u.filter IsPowerful, ∃ mn : ℕ × ℕ, d = mn.1 ^ 2 * mn.2 ^ 3 ∧ (1 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ) = (1 : ℝ) / (mn.1 : ℝ) ^ (3 / 2 : ℝ) * (1 / (mn.2 : ℝ) ^ (9 / 4 : ℝ)) := by
        intro d hd; obtain ⟨ a, b, rfl ⟩ := isPowerful_eq_sq_mul_cube d ( Finset.mem_filter.mp hd |>.2 ) ; use ( a, b ) ; norm_num ; ring_nf;
        rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      choose! mn hmn₁ hmn₂ using h_image;
      use Finset.image mn (u.filter IsPowerful);
      rw [ Finset.sum_image ];
      · exact Finset.sum_le_sum fun x hx => hmn₂ x hx ▸ le_rfl;
      · intro x hx y hy; have := hmn₁ x hx; have := hmn₁ y hy; norm_num at *;
        grind;
    exact le_trans ( by simpa [ Finset.sum_filter ] using! hs ) ( Summable.sum_le_tsum s ( fun _ _ => by positivity ) ( by simpa using! aux_prod_summable ) )

/-
The Dirichlet series `∑_{r squarefree} 4^{ω(r)}·r^{-3/2}` converges: it is dominated
by the convergent Euler product `∏_p (1 + 4 p^{-3/2})`.
-/
theorem squarefree_omega_summable :
    Summable (fun r : ℕ =>
      if Squarefree r then (4 : ℝ) ^ (omegaCount r) * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) else 0) := by
  refine' summable_of_sum_le _ _;
  exact Real.exp ( ∑' p : ℕ, if p.Prime then 4 * ( p : ℝ ) ^ ( - ( 3 / 2 : ℝ ) ) else 0 );
  · exact fun _ => by positivity;
  · intro u
    have h_sum_le : ∑ x ∈ u, (if Squarefree x then (4 : ℝ) ^ (omegaCount x) * (1 / (x : ℝ) ^ (3 / 2 : ℝ)) else 0) ≤ ∏ p ∈ (u.filter Squarefree).biUnion (fun x => x.primeFactors), (1 + 4 * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      have h_sum_le : ∑ x ∈ u, (if Squarefree x then (4 : ℝ) ^ (omegaCount x) * (1 / (x : ℝ) ^ (3 / 2 : ℝ)) else 0) ≤ ∑ x ∈ (u.filter Squarefree), ∏ p ∈ x.primeFactors, (4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [ Finset.sum_filter ];
        gcongr;
        split_ifs <;> norm_num [ Finset.prod_mul_distrib ];
        rename_i k hk₂;
        rw [ Real.finset_prod_rpow _ _ fun p hp => Nat.cast_nonneg _ ];
        rw [ Real.rpow_neg ( by positivity ), ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hk₂ ];
      refine le_trans h_sum_le ?_;
      have h_sum_le : ∑ x ∈ (u.filter Squarefree), ∏ p ∈ x.primeFactors, (4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ∑ t ∈ Finset.powerset ((u.filter Squarefree).biUnion (fun x => x.primeFactors)), ∏ p ∈ t, (4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
        rotate_left;
        exact Finset.image ( fun x => x.primeFactors ) ( u.filter Squarefree );
        · grind;
        · exact fun _ _ _ => Finset.prod_nonneg fun _ _ => mul_nonneg zero_le_four ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
        · rw [ Finset.sum_image ];
          intro x hx y hy; simp_all +decide ;
          intro h; have := Nat.prod_primeFactors_of_squarefree hx.2; have := Nat.prod_primeFactors_of_squarefree hy.2; aesop;
      convert! h_sum_le using 1;
      simp +decide [ add_comm ( 1 : ℝ ), Finset.prod_add ];
    have h_prod_le : ∏ p ∈ (u.filter Squarefree).biUnion (fun x => x.primeFactors), (1 + 4 * (p : ℝ) ^ (-(3 / 2 : ℝ))) ≤ Real.exp (∑ p ∈ (u.filter Squarefree).biUnion (fun x => x.primeFactors), 4 * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [ Real.exp_sum ];
      exact Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => by rw [ add_comm ] ; exact Real.add_one_le_exp _;
    refine' le_trans h_sum_le ( le_trans h_prod_le _ );
    refine' Real.exp_le_exp.mpr ( le_trans _ ( Summable.sum_le_tsum _ _ _ ) );
    any_goals exact Finset.biUnion ( Finset.filter Squarefree u ) fun x => x.primeFactors;
    · exact Finset.sum_le_sum fun x hx => by aesop;
    · intro p hp; split_ifs <;> positivity;
    · have h_summable : Summable (fun p : ℕ => (4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        exact Summable.mul_left _ <| Real.summable_nat_rpow.2 <| by norm_num;
      exact Summable.of_nonneg_of_le ( fun p => by split_ifs <;> positivity ) ( fun p => by split_ifs <;> first | positivity | aesop ) h_summable

/-
For a powerful number `d`, its radical squared divides it: `(rad d)^2 ∣ d`.
-/
theorem rad_pow_two_dvd (d : ℕ) (hd : IsPowerful d) : (rad d) ^ 2 ∣ d := by
  by_cases hd0 : d = 0;
  · aesop;
  · rw [ ← Nat.factorization_le_iff_dvd ] <;> simp_all +decide [ rad ];
    · rw [ Nat.factorization_prod ];
      · intro p; by_cases hp : p.Prime <;> by_cases hp' : p ∈ d.primeFactors <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
        · rw [ Finset.sum_eq_single p ] <;> simp_all +decide;
          have := hd p hp hp'; rw [ ← Nat.factorization_le_iff_dvd ] at this <;> aesop;
        · intro i hi hi'; rw [ Finsupp.single_apply ] ; aesop;
      · aesop;
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp

/-
Smooth second-moment bound: if every element of a finset `M` of positive integers is
`r`-smooth (all prime factors divide the squarefree `r`), then `∑_{m∈M} m^{-1/2} ≤ 4^{ω(r)}`.
This is the finite Euler factor `∏_{p∣r}(1-p^{-1/2})^{-1} ≤ 4^{ω(r)}`.
-/
theorem smooth_inv_sqrt_sum_le (r : ℕ) (hr : Squarefree r) (M : Finset ℕ)
    (hM0 : ∀ m ∈ M, 0 < m) (hMs : ∀ m ∈ M, ∀ p : ℕ, p.Prime → p ∣ m → p ∣ r) :
    ∑ m ∈ M, (1 : ℝ) / Real.sqrt (m : ℝ) ≤ (4 : ℝ) ^ (omegaCount r) := by
  -- For each $m \in M$, write $m$ as a product of primes raised to their respective powers.
  have h_factor : ∀ m ∈ M, ∃ f : ℕ → ℕ, (∀ p, Nat.Prime p → f p = Nat.factorization m p) ∧ (∀ p, Nat.Prime p → p ∣ r → f p ≥ 0) ∧ (∀ p, Nat.Prime p → ¬p ∣ r → f p = 0) ∧ m = ∏ p ∈ r.primeFactors, p ^ f p := by
    intro m hm; use fun p => Nat.factorization m p; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
    refine' ⟨ fun p pp dp => Or.inl fun h => dp <| hMs m hm p pp h, _ ⟩;
    conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( ne_of_gt ( hM0 m hm ) ) ] ;
    rw [ Finsupp.prod_of_support_subset ] <;> aesop_cat;
  choose! f hf1 hf2 hf3 hf4 using h_factor;
  -- By definition of $f$, we know that $1 / \sqrt{m} = \prod_{p \in r.primeFactors} (1 / \sqrt{p})^{f(m, p)}$.
  have h_sqrt : ∀ m ∈ M, (1 / Real.sqrt m) = ∏ p ∈ r.primeFactors, (1 / Real.sqrt p) ^ f m p := by
    intro m hm; rw [ hf4 m hm ] ; simp +decide [ Real.sqrt_eq_rpow ] ;
    rw [ ← Real.finset_prod_rpow _ _ fun p hp => by positivity ] ; congr ; ext ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
    rw [ ← hf4 m hm, ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
  -- Consider the sum $\sum_{m \in M} \prod_{p \in r.primeFactors} (1 / \sqrt{p})^{f(m, p)}$.
  have h_sum_prod : ∑ m ∈ M, ∏ p ∈ r.primeFactors, (1 / Real.sqrt p) ^ f m p ≤ ∏ p ∈ r.primeFactors, (∑ k ∈ Finset.range (Nat.succ (Finset.sup M (fun m => Nat.factorization m p))), (1 / Real.sqrt p) ^ k) := by
    rw [ Finset.prod_sum ];
    refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => Finset.prod_nonneg fun _ _ => pow_nonneg ( by positivity ) _ );
    rotate_left;
    exact Finset.image ( fun m => fun p hp => f m p ) M;
    · simp +contextual [ Finset.subset_iff ];
      exact fun m hm p hp hpr hr => Finset.le_sup ( f := fun m => m.factorization p ) hm |> le_trans ( by rw [ hf1 m hm p hp ] );
    · rw [ Finset.sum_image ];
      · exact Finset.sum_le_sum fun x hx => by rw [ ← Finset.prod_attach ] ;
      · intro m hm m' hm' h; have := hf4 m hm; have := hf4 m' hm'; simp +decide [ ← this, ← hf4 m hm ] at *;
        rw [ hf4 m hm, hf4 m' hm' ];
        exact Finset.prod_congr rfl fun p hp => congr_arg _ ( congr_fun ( congr_fun h p ) hp );
  -- For each prime $p \in r.primeFactors$, the geometric series $\sum_{k=0}^{K} (1 / \sqrt{p})^k$ is bounded above by $4$.
  have h_geo_series : ∀ p ∈ r.primeFactors, ∑ k ∈ Finset.range (Nat.succ (Finset.sup M (fun m => Nat.factorization m p))), (1 / Real.sqrt p) ^ k ≤ 4 := by
    intro p hp
    have h_geo_series_bound : ∑ k ∈ Finset.range (Nat.succ (Finset.sup M (fun m => Nat.factorization m p))), (1 / Real.sqrt p) ^ k ≤ (1 - 1 / Real.sqrt p)⁻¹ := by
      rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by simpa using! inv_lt_one_of_one_lt₀ <| Real.lt_sqrt_of_sq_lt <| mod_cast Nat.Prime.one_lt <| Nat.prime_of_mem_primeFactors hp ) ];
      exact Summable.sum_le_tsum ( Finset.range _ ) ( fun _ _ => by positivity ) ( summable_geometric_of_lt_one ( by positivity ) ( by simpa using! inv_lt_one_of_one_lt₀ <| Real.lt_sqrt_of_sq_lt <| mod_cast Nat.Prime.one_lt <| Nat.prime_of_mem_primeFactors hp ) );
    refine le_trans h_geo_series_bound ?_;
    rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith only [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ( Nat.prime_of_mem_primeFactors hp ), Real.sqrt_nonneg p, Real.sq_sqrt <| Nat.cast_nonneg p, one_div_mul_cancel <| ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| Nat.Prime.pos <| Nat.prime_of_mem_primeFactors hp ];
  refine le_trans ( Finset.sum_le_sum fun m hm => h_sqrt m hm ▸ le_rfl ) ( h_sum_prod.trans ?_ );
  exact le_trans ( Finset.prod_le_prod ( fun _ _ => Finset.sum_nonneg fun _ _ => by positivity ) h_geo_series ) ( by norm_num [ omegaCount ] )

/-
Grouping powerful numbers by their radical `r = rad d` (writing `d = r²·m` with `m`
`r`-smooth): the `r`-block contributes at most `4^{ω(r)}·r^{-3/2}` because
`∑_{rad m ∣ r} m^{-1/2} = ∏_{p∣r}(1-p^{-1/2})^{-1} ≤ 4^{ω(r)}`.
-/
theorem powerful_sum_le_squarefree {u : Finset ℕ} (hu : ∀ d ∈ u, IsPowerful d) :
    (∑ d ∈ u, (if IsPowerful d then 1 / Real.sqrt ((d : ℝ) * (rad d : ℝ)) else 0))
      ≤ ∑' r : ℕ, (if Squarefree r then (4 : ℝ) ^ (omegaCount r) * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) else 0) := by
  -- Group the sum over u by r = rad d, using `Finset.sum_image`/fiberwise over `u.image rad`:
  have h_group : ∑ d ∈ u, (if IsPowerful d then (1 : ℝ) / Real.sqrt (d * rad d) else 0) = ∑ r ∈ u.image rad, ∑ d ∈ u.filter (fun d => rad d = r), (if IsPowerful d then (1 : ℝ) / Real.sqrt (d * r) else 0) := by
    rw [ Finset.sum_image' ];
    exact fun x hx => Finset.sum_congr rfl fun y hy => by aesop;
  -- For each $r \in u.image rad$, $r$ is squarefree and we can bound the inner sum by $4^{\omega(r)} \cdot r^{-3/2}$.
  have h_inner_bound : ∀ r ∈ u.image rad, ∑ d ∈ u.filter (fun d => rad d = r), (if IsPowerful d then (1 : ℝ) / Real.sqrt (d * r) else 0) ≤ 4 ^ (omegaCount r) * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) := by
    intro r hr
    have hr_sqfree : Squarefree r := by
      obtain ⟨ d, hd, rfl ⟩ := Finset.mem_image.mp hr;
      have h_rad_sqfree : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) := by
        intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
        exact ⟨ Nat.Coprime.prod_right fun p hp => hS.1.coprime_iff_not_dvd.mpr fun h => by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop, hS.1.squarefree ⟩;
      exact h_rad_sqfree fun p hp => Nat.prime_of_mem_primeFactors hp
    have h_block : ∑ d ∈ u.filter (fun d => rad d = r), (if IsPowerful d then (1 : ℝ) / Real.sqrt (d * r) else 0) ≤ (1 / (r : ℝ) ^ (3 / 2 : ℝ)) * ∑ m ∈ (u.filter (fun d => rad d = r)).image (fun d => d / r ^ 2), (if ∀ p, Nat.Prime p → p ∣ m → p ∣ r then (1 : ℝ) / Real.sqrt m else 0) := by
      rw [ Finset.sum_image ];
      · rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun x hx => ?_; split_ifs <;> norm_num at *;
        · -- Since $x$ is powerful and $rad x = r$, we have $x = r^2 * m$ for some $m$.
          obtain ⟨m, hm⟩ : ∃ m, x = r^2 * m := by
            exact hx.2 ▸ rad_pow_two_dvd x ‹_›;
          by_cases hr : r = 0 <;> simp_all +decide [ mul_comm, mul_left_comm ];
          rw [ show ( r : ℝ ) ^ ( 3 / 2 : ℝ ) = r * Real.sqrt r by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring_nf ; norm_num [ hr ];
        · rename_i h₁ h₂; obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h₂; have := Nat.dvd_trans hp₂ ( Nat.div_dvd_of_dvd <| show r ^ 2 ∣ x from ?_ ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
          · contrapose! hp₂;
            refine' Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd _ ) _;
            · exact hx.2 ▸ rad_pow_two_dvd x ( hu x hx.1 );
            · refine' hp₁.coprime_iff_not_dvd.mpr _;
              intro hpx; have := Nat.dvd_gcd ( dvd_refl p ) ( show p ∣ r from ?_ ) ; simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ] ;
              exact hx.2 ▸ Finset.dvd_prod_of_mem _ ( by aesop );
          · exact hx.2 ▸ rad_pow_two_dvd x h₁;
        · positivity;
      · intros x hx y hy; simp_all +decide;
        intro hxy; have := rad_pow_two_dvd x ( hu x hx.1 ) ; have := rad_pow_two_dvd y ( hu y hy.1 ) ; simp_all +decide ;
    -- Apply the smooth_inv_sqrt_sum_le lemma to the inner sum.
    have h_inner_sum : ∑ m ∈ (u.filter (fun d => rad d = r)).image (fun d => d / r ^ 2), (if ∀ p, Nat.Prime p → p ∣ m → p ∣ r then (1 : ℝ) / Real.sqrt m else 0) ≤ 4 ^ (omegaCount r) := by
      convert! smooth_inv_sqrt_sum_le r hr_sqfree ( Finset.image ( fun d => d / r ^ 2 ) ( Finset.filter ( fun d => rad d = r ) u ) |> Finset.filter ( fun m => ∀ p : ℕ, Nat.Prime p → p ∣ m → p ∣ r ) ) _ _ using 1;
      · rw [ Finset.sum_filter ];
      · simp +zetaDelta at *;
        rintro m x hx hx' rfl hm; contrapose! hm; simp_all +decide ;
        cases hm <;> simp_all +decide [ Nat.div_eq_of_lt ];
        exact ⟨ Nat.find ( Nat.exists_infinite_primes ( r + 1 ) ), Nat.find_spec ( Nat.exists_infinite_primes ( r + 1 ) ) |>.2, Nat.not_dvd_of_pos_of_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.find_spec ( Nat.exists_infinite_primes ( r + 1 ) ) |>.1 ) ⟩;
      · aesop;
    exact h_block.trans ( by rw [ mul_comm ] ; gcongr );
  refine' le_trans _ ( Summable.sum_le_tsum _ _ _ );
  any_goals exact Finset.image rad u;
  · convert! Finset.sum_le_sum h_inner_bound using 1;
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ Finset.mem_image ] at hx; obtain ⟨ d, hd, rfl ⟩ := hx; simp +decide [ rad ] ;
    rw [ Nat.squarefree_iff_prime_squarefree ] ; norm_num;
    intro p pp dp; rw [ Finset.prod_eq_prod_diff_singleton_mul <| Nat.mem_primeFactors.mpr ⟨ pp, ?_, ?_ ⟩ ] at dp <;> norm_num at *;
    · rw [ Nat.mul_dvd_mul_iff_right pp.pos ] at dp;
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime pp, Nat.coprime_prod_right_iff ];
      obtain ⟨ q, hq₁, hq₂, hq₃, hq₄, hq₅ ⟩ := dp; have := Nat.coprime_primes pp hq₁; aesop;
    · exact dvd_trans ( dvd_of_mul_left_dvd dp ) ( Nat.prod_primeFactors_dvd _ );
    · intro h; specialize hu 0; simp_all +decide [ IsPowerful ] ;
  · exact fun _ _ => by positivity;
  · convert! squarefree_omega_summable using 1

/-- The multiplicative crux behind the radical-defect bound: the series
`∑_{d powerful} 1/√(d·rad d)` converges (each local Euler factor is `1 + O(p^{-3/2})`). -/
theorem radical_mult_summable :
    Summable (fun d : ℕ =>
      if IsPowerful d then 1 / Real.sqrt ((d : ℝ) * (rad d : ℝ)) else 0) := by
  refine summable_of_sum_le (c := ∑' r : ℕ, (if Squarefree r then (4 : ℝ) ^ (omegaCount r) * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) else 0))
    (fun _ => by positivity) (fun u => ?_)
  have h := powerful_sum_le_squarefree (u := u.filter IsPowerful)
    (fun d hd => (Finset.mem_filter.mp hd).2)
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hd : IsPowerful d <;> simp [hd]

/-
**Lemma 2.5 (radical defect).**  There is an absolute constant `C` such that
`∑_{n ≤ X} (n / rad(n))^{1/2} ≤ C X` for all `X ≥ 1`.
-/
theorem radical_defect_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Real.sqrt ((n : ℝ) / (rad n : ℝ)) ≤ C * X := by
  -- Set $g$ to be the Möbius inversion of $f$, i.e., $g(d) = \sum_{e|d} \mu(d/e) \sqrt{e/\text{rad } e}$.
  set g : ℕ → ℝ := fun d => ∑ e ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / e)) * Real.sqrt ((e : ℝ) / (rad e : ℝ));
  -- Facts about $g$ (all multiplicative bookkeeping; $g$ is multiplicative with $g(p)=f(p)-f(1)=0$, $g(p^a)=f(p^a)-f(p^{a-1})=p^{(a-2)/2}(\sqrt{p}-1)$ for $a \geq 2$):
  have hg_nonneg : ∀ d, 0 ≤ g d := by
    -- By definition of $g$, we know that $g(p^a) \geq 0$ for any prime $p$ and integer $a \geq 0$.
    have hg_prime_pow_nonneg : ∀ p a : ℕ, Nat.Prime p → 0 ≤ g (p^a) := by
      intro p a hp
      have hg_prime_pow_nonneg : g (p^a) = if a = 0 then 1 else if a = 1 then 0 else (Real.sqrt (p^a / p) - Real.sqrt (p^(a-1) / p)) := by
        rcases a with ( _ | _ | a ) <;> simp_all +decide;
        · aesop;
        · simp +zetaDelta at *;
          rw [ hp.sum_divisors ] ; norm_num [ hp.ne_zero, hp.ne_one, ArithmeticFunction.moebius ];
          rcases p with ( _ | _ | p ) <;> simp_all +decide;
          rw [ div_self <| by positivity, if_pos <| hp.squarefree ] ; ring;
        · simp +zetaDelta at *;
          norm_num [ Nat.divisors_prime_pow hp, ArithmeticFunction.moebius ];
          rw [ Finset.sum_eq_add ( a + 1 ) ( a + 1 + 1 ) ] <;> norm_num [ Nat.pow_succ', Nat.mul_div_mul_left, hp.pos ];
          · simp_all +decide [ ← pow_succ', hp.squarefree ];
            rw [ Nat.primeFactors_pow, Nat.primeFactors_pow ] <;> norm_num [ hp.ne_zero, hp.ne_one ] ; ring_nf;
            norm_num [ hp.primeFactors, hp.ne_zero ] ; ring;
          · intro c hc₁ hc₂ hc₃ hc₄; rcases c with ( _ | _ | c ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_div_mul_left, hp.pos ] ;
            · simp_all +decide [ Nat.squarefree_mul_iff ];
              simp_all +decide [ Nat.Coprime ];
            · rw [ ← pow_succ', Nat.squarefree_pow_iff ] at hc₄ <;> aesop;
            · rw [ show p ^ a / p ^ c = p ^ ( a - c ) by rw [ Nat.div_eq_of_eq_mul_left ( pow_pos hp.pos _ ) ] ; rw [ ← pow_add, Nat.sub_add_cancel hc₁ ] ] at hc₄;
              rw [ Nat.squarefree_pow_iff ] at hc₄ <;> norm_num at *;
              · omega;
              · exact hp.ne_one;
              · omega;
      rcases a with ( _ | _ | a ) <;> simp_all +decide [ pow_succ, hp.ne_zero ];
      exact le_mul_of_one_le_right ( Real.sqrt_nonneg _ ) ( Real.le_sqrt_of_sq_le ( mod_cast hp.one_lt.le ) );
    -- Since $g$ is multiplicative, we can extend the non-negativity to all $d$.
    have hg_mul : ∀ d1 d2 : ℕ, Nat.Coprime d1 d2 → g (d1 * d2) = g d1 * g d2 := by
      intros d1 d2 h_coprime
      simp [g];
      -- By definition of divisors, we can write the divisors of $d1 * d2$ as $\{d1' * d2' \mid d1' \mid d1, d2' \mid d2\}$.
      have h_divisors : (d1 * d2).divisors = Finset.image (fun (p : ℕ × ℕ) => p.1 * p.2) (d1.divisors ×ˢ d2.divisors) := by
        exact Nat.divisors_mul _ _;
      rw [ h_divisors, Finset.sum_image, Finset.sum_product ];
      · rw [ Finset.sum_mul ];
        refine' Finset.sum_congr rfl fun i hi => _;
        rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun j hj => _ ; rw [ Nat.mul_div_mul_comm ( Nat.dvd_of_mem_divisors hi ) ( Nat.dvd_of_mem_divisors hj ) ] ;
        rw [ Nat.primeFactors_mul ( by aesop ) ( by aesop ) ] ; simp +decide [ *, ArithmeticFunction.moebius ] ; ring_nf;
        split_ifs <;> simp_all +decide [ Nat.squarefree_mul_iff ];
        · rw [ Finset.prod_union ];
          · rw [ ArithmeticFunction.cardFactors_mul ] <;> simp_all +decide [ Nat.Coprime ] ; ring_nf;
            · rw [ Real.sqrt_mul ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) ] ; ring;
            · exact ⟨ Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hi.1 ( Nat.pos_of_ne_zero hi.2 ) ), Nat.le_of_dvd ( Nat.pos_of_ne_zero hi.2 ) hi.1 ⟩;
            · exact ⟨ by aesop_cat, Nat.le_of_dvd ( Nat.pos_of_ne_zero hj.2 ) hj.1 ⟩;
          · exact Nat.Coprime.disjoint_primeFactors ( h_coprime.coprime_dvd_left hi.1 |> Nat.Coprime.coprime_dvd_right hj.1 );
        · exact False.elim <| ‹¬Nat.gcd ( d1 / i ) ( d2 / j ) = 1› <| h_coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd hi.1 ) |> Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hj.1 );
      · intros p hp q hq h_eq; simp_all +decide [ Nat.coprime_iff_gcd_eq_one ] ;
        -- Since $p.1 \mid d1$ and $q.1 \mid d1$, and $\gcd(d1, d2) = 1$, it follows that $p.1 = q.1$.
        have hp1_eq_q1 : p.1 = q.1 := by
          exact Nat.dvd_antisymm ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hp.1.1 <| Nat.Coprime.coprime_dvd_right hq.2 h_coprime ) <| h_eq.symm ▸ dvd_mul_right _ _ ) ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hq.1 <| Nat.Coprime.coprime_dvd_right hp.2.1 h_coprime ) <| h_eq.symm ▸ dvd_mul_right _ _ );
        aesop;
    intro d; by_cases hd : d = 0; simp +decide [ hd ] ;
    · simp +zetaDelta at *;
    · rw [ ← Nat.factorization_prod_pow_eq_self hd ];
      -- Apply the multiplicative property of $g$ to expand $g(d)$.
      have hg_expand : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → g (∏ p ∈ S, p ^ (Nat.factorization d p)) = ∏ p ∈ S, g (p ^ (Nat.factorization d p)) := by
        intro S hS; induction S using Finset.induction <;> simp_all +decide ;
        · simp +zetaDelta at *;
        · rw [ hg_mul, ‹g ( ∏ p ∈ _, p ^ d.factorization p ) = _› ];
          exact Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
      exact hg_expand ( fun p hp => Nat.prime_of_mem_primeFactors hp ) ▸ Finset.prod_nonneg fun p hp => hg_prime_pow_nonneg p _ ( Nat.prime_of_mem_primeFactors hp )
  have hg_zero : ∀ p : ℕ, Nat.Prime p → g p = 0 := by
    intro p hp; simp +decide [ g ] ;
    rw [ hp.sum_divisors ] ; norm_num [ hp.ne_zero, hp.ne_one, ArithmeticFunction.moebius ];
    rcases p with ( _ | _ | p ) <;> simp_all +decide;
    rw [ div_self <| by positivity, if_pos <| hp.squarefree ] ; norm_num
  have hg_powerful : ∀ d, ¬IsPowerful d → g d = 0 := by
    intro d hd_not_powerful
    have hg_mul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b := by
      intros a b hab_coprime
      simp [g];
      -- By definition of divisors, we can write the divisors of $ab$ as $\{d_1d_2 \mid d_1 \mid a, d_2 \mid b\}$.
      have h_divisors : (a * b).divisors = Finset.image (fun (d : ℕ × ℕ) => d.1 * d.2) (a.divisors ×ˢ b.divisors) := by
        exact Nat.divisors_mul _ _;
      rw [ h_divisors, Finset.sum_image, Finset.sum_product ];
      · rw [ Finset.sum_mul ];
        simp +decide only [mul_comm, Finset.mul_sum _ _ _];
        refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
        rw [ Nat.primeFactors_mul ( by aesop ) ( by aesop ) ];
        rw [ Finset.prod_union ];
        · rw [ show a * b / ( x * y ) = ( a / x ) * ( b / y ) by rw [ Nat.div_mul_div_comm ( Nat.dvd_of_mem_divisors hx ) ( Nat.dvd_of_mem_divisors hy ) ] ] ; norm_num [ ArithmeticFunction.moebius ] ; ring_nf;
          split_ifs <;> simp_all +decide [ Nat.squarefree_mul_iff ];
          · rw [ ArithmeticFunction.cardFactors_mul ] <;> ring_nf <;> norm_num [ hx.1, hy.1, hx.2, hy.2 ];
            · rw [ Real.sqrt_mul ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) ] ; ring;
            · exact ⟨ Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hx.1 ( Nat.pos_of_ne_zero hx.2 ) ), Nat.le_of_dvd ( Nat.pos_of_ne_zero hx.2 ) hx.1 ⟩;
            · exact ⟨ by aesop_cat, Nat.le_of_dvd ( Nat.pos_of_ne_zero hy.2 ) hy.1 ⟩;
          · exact False.elim <| ‹¬Nat.gcd ( a / x ) ( b / y ) = 1› <| hab_coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd hx.1 ) |> Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hy.1 );
        · exact Nat.Coprime.disjoint_primeFactors ( hab_coprime.coprime_dvd_left ( Nat.dvd_of_mem_divisors hx ) |> Nat.Coprime.coprime_dvd_right ( Nat.dvd_of_mem_divisors hy ) );
      · intros x hx y hy; simp_all +decide [ Nat.coprime_iff_gcd_eq_one ] ;
        intro h; have := Nat.dvd_antisymm ( show x.1 ∣ y.1 from Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hx.1.1 <| Nat.Coprime.coprime_dvd_right hy.2 hab_coprime ) <| h.symm ▸ dvd_mul_right _ _ ) ( show y.1 ∣ x.1 from Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hy.1 <| Nat.Coprime.coprime_dvd_right hx.2.1 hab_coprime ) <| h.symm ▸ dvd_mul_right _ _ ) ; aesop;
    -- Since $d$ is not powerful, there exists a prime $p$ such that $p \mid d$ but $p^2 \nmid d$.
    obtain ⟨p, hp_prime, hp_div, hp_not_div⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d ∧ ¬p ^ 2 ∣ d := by
      contrapose! hd_not_powerful; aesop;
    -- Write $d$ as $p \cdot m$ where $m$ is not divisible by $p$.
    obtain ⟨m, rfl, hm_not_div⟩ : ∃ m : ℕ, d = p * m ∧ ¬p ∣ m := by
      exact ⟨ d / p, by rw [ Nat.mul_div_cancel' hp_div ], by rw [ Nat.dvd_div_iff_mul_dvd hp_div ] ; exact fun h => hp_not_div <| by simpa only [ sq ] using! h ⟩;
    rw [ hg_mul p m ( hp_prime.coprime_iff_not_dvd.mpr hm_not_div ), hg_zero p hp_prime, MulZeroClass.zero_mul ]
  have hg_le : ∀ d, g d ≤ Real.sqrt ((d : ℝ) / (rad d : ℝ)) := by
    -- By definition of $g$, we know that $\sum_{e \mid d} g(e) = \sqrt{d / \text{rad } d}$.
    have hg_sum : ∀ d : ℕ, d ≠ 0 → ∑ e ∈ Nat.divisors d, g e = Real.sqrt ((d : ℝ) / (rad d : ℝ)) := by
      intro d hd_ne_zero
      have hg_sum : ∑ e ∈ Nat.divisors d, g e = ∑ e ∈ Nat.divisors d, Real.sqrt ((e : ℝ) / (rad e : ℝ)) * ∑ f ∈ Nat.divisors (d / e), (ArithmeticFunction.moebius f) := by
        simp +decide [ g, mul_comm, Finset.mul_sum _ _ _ ];
        rw [ Finset.sum_sigma', Finset.sum_sigma' ];
        refine' Finset.sum_bij ( fun x hx => ⟨ x.snd, x.fst / x.snd ⟩ ) _ _ _ _ <;> simp +decide;
        · exact fun a ha₁ ha₂ ha₃ ha₄ => ⟨ ⟨ dvd_trans ha₃ ha₁, ha₂ ⟩, Nat.dvd_div_of_mul_dvd <| by simpa only [ Nat.mul_div_cancel' ha₃ ] using! ha₁, Nat.ne_of_gt <| Nat.pos_of_dvd_of_pos ha₃ <| Nat.pos_of_ne_zero ha₄, Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₄ ) ha₃ ) <| Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₂ ) ha₁ ⟩;
        · intro a₁ ha₁ hd_ne_zero ha₂ ha₃ a₂ ha₄ hd_ne_zero' ha₅ ha₆ h₁ h₂; cases a₁; cases a₂; aesop;
        · intro b hb₁ hb₂ hb₃ hb₄ hb₅; use b.fst * b.snd, b.fst; simp_all +decide [ Nat.dvd_div_iff_mul_dvd ] ;
          exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( dvd_of_mul_left_dvd hb₃ ) ( Nat.pos_of_ne_zero hb₂ ) );
      -- Since $\sum_{f \mid m} \mu(f)$ is zero unless $m = 1$, we have:
      have h_moebius_sum : ∀ m : ℕ, m ≠ 0 → (∑ f ∈ Nat.divisors m, (ArithmeticFunction.moebius f)) = if m = 1 then 1 else 0 := by
        intro m hm_ne_zero
        have h_moebius_sum : ∑ f ∈ Nat.divisors m, (ArithmeticFunction.moebius f) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) m := by
          simp +decide [ ArithmeticFunction.moebius, ArithmeticFunction.zeta ];
          rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if Squarefree x then ( -1 : ℤ ) ^ ArithmeticFunction.cardFactors x else 0 ];
          exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hm_ne_zero ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
        aesop;
      rw [ hg_sum, Finset.sum_eq_single d ] <;> simp_all +decide;
      · rw [ Nat.div_self ( Nat.pos_of_ne_zero hd_ne_zero ) ] ; norm_num;
      · exact fun b hb₁ hb₂ => Or.inr <| mod_cast h_moebius_sum ( d / b ) ( Nat.ne_of_gt <| Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hd_ne_zero ) hb₁ ) ( Nat.pos_of_dvd_of_pos hb₁ ( Nat.pos_of_ne_zero hd_ne_zero ) ) ) ▸ if_neg ( by contrapose! hb₂; nlinarith [ Nat.div_mul_cancel hb₁, Nat.pos_of_ne_zero hd_ne_zero ] );
    intro d; specialize hg_sum d; by_cases hd : d = 0 <;> simp_all +decide ;
    · aesop;
    · exact hg_sum ▸ Finset.single_le_sum ( fun x _ => hg_nonneg x ) ( by aesop )
  have hg_summable : Summable (fun d : ℕ => g d / (d : ℝ)) := by
    have hg_summable : Summable (fun d : ℕ => if IsPowerful d then Real.sqrt ((d : ℝ) / (rad d : ℝ)) / (d : ℝ) else 0) := by
      convert! radical_mult_summable using 2 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.sqrt_mul, Real.sqrt_div ];
      grind +qlia;
    refine' hg_summable.of_nonneg_of_le ( fun d => div_nonneg ( hg_nonneg d ) ( Nat.cast_nonneg d ) ) ( fun d => _ );
    split_ifs <;> simp_all +decide;
    exact div_le_div_of_nonneg_right ( hg_le d ) ( Nat.cast_nonneg _ );
  -- Set $C := \max 1 C₀ > 0$.
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ N : ℕ, (∑ d ∈ Finset.Icc 1 N, g d / (d : ℝ)) ≤ C₀ := by
    exact ⟨ _, fun N => Summable.sum_le_tsum ( Finset.Icc 1 N ) ( fun _ _ => div_nonneg ( hg_nonneg _ ) ( Nat.cast_nonneg _ ) ) hg_summable ⟩;
  -- Main estimate for integer $N = \lfloor X \rfloor$ ($X \geq 1$):
  have h_main_estimate : ∀ N : ℕ, 1 ≤ N → (∑ n ∈ Finset.Icc 1 N, Real.sqrt ((n : ℝ) / (rad n : ℝ))) ≤ N * C₀ := by
    intros N hN
    have h_sum_g : (∑ n ∈ Finset.Icc 1 N, Real.sqrt ((n : ℝ) / (rad n : ℝ))) = (∑ d ∈ Finset.Icc 1 N, g d * (Nat.floor (N / d) : ℝ)) := by
      have h_sum_g : ∀ n ∈ Finset.Icc 1 N, Real.sqrt ((n : ℝ) / (rad n : ℝ)) = ∑ d ∈ Nat.divisors n, g d := by
        intros n hn
        have h_sum_g : ∑ d ∈ Nat.divisors n, g d = ∑ e ∈ Nat.divisors n, Real.sqrt ((e : ℝ) / (rad e : ℝ)) * (∑ d ∈ Nat.divisors (n / e), (ArithmeticFunction.moebius d)) := by
          simp +zetaDelta at *;
          simp +decide only [Finset.mul_sum _ _ _];
          rw [ Finset.sum_sigma', Finset.sum_sigma' ];
          refine' Finset.sum_bij ( fun x hx => ⟨ x.snd, x.fst / x.snd ⟩ ) _ _ _ _ <;> simp +decide;
          · exact fun a ha₁ ha₂ ha₃ ha₄ => ⟨ ⟨ dvd_trans ha₃ ha₁, ha₂ ⟩, Nat.dvd_div_of_mul_dvd <| by simpa only [ Nat.mul_div_cancel' ha₃ ] using! ha₁, Nat.ne_of_gt <| Nat.pos_of_dvd_of_pos ha₃ <| Nat.pos_of_ne_zero ha₄, Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₄ ) ha₃ ) <| Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₂ ) ha₁ ⟩;
          · intro a₁ ha₁ hn ha₂ ha₃ a₂ ha₄ hn' ha₅ ha₆ h₁ h₂; cases a₁; cases a₂; aesop;
          · intro b hb₁ hb₂ hb₃ hb₄ hb₅; use b.fst * b.snd, b.fst; simp_all +decide [ Nat.dvd_div_iff_mul_dvd ] ;
            exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( dvd_of_mul_left_dvd hb₃ ) ( pos_of_gt hn.1 ) );
          · exact fun _ _ _ _ _ => mul_comm _ _;
        have h_sum_g : ∀ m : ℕ, m ≠ 0 → (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d)) = if m = 1 then 1 else 0 := by
          intros m hm_nonzero
          have h_sum_g : ∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) m := by
            simp +decide [ ArithmeticFunction.moebius, ArithmeticFunction.zeta ];
            rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if Squarefree x then ( -1 : ℤ ) ^ ArithmeticFunction.cardFactors x else 0 ];
            exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hm_nonzero ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
          aesop;
        simp_all +decide;
        rw [ Finset.sum_eq_single n ] <;> norm_num;
        · norm_num [ Nat.div_self ( by linarith : 0 < n ) ];
        · exact fun b hb₁ hb₂ hb₃ => Or.inr <| mod_cast h_sum_g ( n / b ) ( Nat.ne_of_gt <| Nat.div_pos ( Nat.le_of_dvd hn.1 hb₁ ) <| Nat.pos_of_dvd_of_pos hb₁ hn.1 ) ▸ if_neg ( by contrapose! hb₃; nlinarith [ Nat.div_mul_cancel hb₁ ] );
        · grind +qlia;
      rw [ Finset.sum_congr rfl h_sum_g ];
      have h_sum_g : ∑ x ∈ Finset.Icc 1 N, ∑ d ∈ Nat.divisors x, g d = ∑ d ∈ Finset.Icc 1 N, ∑ x ∈ Finset.Icc 1 N, if d ∣ x then g d else 0 := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl ];
        simp +contextual [ Finset.sum_ite ];
        intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 N ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.le_of_dvd hx₁ ( Nat.dvd_of_mem_divisors hy ) ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop;
      simp_all +decide [ Finset.sum_ite ];
      refine' Finset.sum_congr rfl fun x hx => _;
      rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 N ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( N / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ];
      · norm_num;
      · ext y; simp [Finset.mem_image];
        exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self N x ] ⟩, by simp +decide ⟩ ⟩;
    have h_sum_g_le : (∑ d ∈ Finset.Icc 1 N, g d * (Nat.floor (N / d) : ℝ)) ≤ (∑ d ∈ Finset.Icc 1 N, g d * (N / d : ℝ)) := by
      gcongr;
      · exact hg_nonneg _;
      · exact_mod_cast Nat.cast_div_le ..;
    exact h_sum_g.symm ▸ h_sum_g_le.trans ( by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using! mul_le_mul_of_nonneg_left ( hC₀ N ) ( Nat.cast_nonneg N ) );
  refine' ⟨ Max.max C₀ 1, _, _ ⟩ <;> norm_num;
  intro X hX; specialize h_main_estimate ⌊X⌋₊ ( Nat.floor_pos.mpr hX ) ; simp_all +decide [ rad ] ;
  exact h_main_estimate.trans ( by nlinarith [ Nat.floor_le ( show 0 ≤ X by positivity ), le_max_left C₀ 1, le_max_right C₀ 1 ] )

/-
**Lemma 2.5 (consequence).**  For every `Y ≥ 1`,
`#{ n ≤ X : n / rad(n) > Y } ≤ C X Y^{-1/2}`.
-/
theorem radical_defect_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
      (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n : ℕ => Y < (n : ℝ) / (rad n : ℝ))).card : ℝ)
        ≤ C * X * Y ^ (-(1 : ℝ) / 2) := by
  obtain ⟨ C, hC₀, hC ⟩ := radical_defect_sum;
  refine' ⟨ C, hC₀, fun X Y hX hY => _ ⟩;
  -- For every `n ∈ S`: `Y < (n:ℝ)/(rad n)`, both sides nonneg, so `Real.sqrt Y ≤ Real.sqrt ((n:ℝ)/(rad n))` (`Real.sqrt_le_sqrt` of `le_of_lt`).
  have h_sqrt_le : ∀ n ∈ Finset.filter (fun n : ℕ => Y < (n : ℝ) / (rad n : ℝ)) (Finset.Icc 1 ⌊X⌋₊), Real.sqrt Y ≤ Real.sqrt ((n : ℝ) / (rad n : ℝ)) := by
    exact fun n hn => Real.sqrt_le_sqrt <| le_of_lt <| Finset.mem_filter.mp hn |>.2;
  -- Hence `(S.card : ℝ) * Real.sqrt Y = ∑_{n ∈ S} Real.sqrt Y ≤ ∑_{n ∈ S} Real.sqrt ((n:ℝ)/(rad n))` (Finset.sum_const / card_nsmul, then `Finset.sum_le_sum`).
  have h_card_le_sum : (Finset.filter (fun n : ℕ => Y < (n : ℝ) / (rad n : ℝ)) (Finset.Icc 1 ⌊X⌋₊)).card * Real.sqrt Y ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Real.sqrt ((n : ℝ) / (rad n : ℝ)) := by
    exact le_trans ( by simp ) ( Finset.sum_le_sum h_sqrt_le ) |> le_trans <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Real.sqrt_nonneg _;
  convert! le_div_iff₀ ( Real.sqrt_pos.mpr <| zero_lt_one.trans_le hY ) |>.2 ( h_card_le_sum.trans <| hC X hX ) using 1 ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ( by positivity : 0 ≤ Y ) ];
  ring

/-
**Lemma 6.1 (one-bit valuation completion).**  Let `Q` be squarefree,
`n = m Q`, and `D ∣ n`.  With `a = gcd(D, m)`, for each prime `q ∣ Q` the excess
`v_q(D) - v_q(a)` is `0` or `1`, and `D = a · ∏_{q ∣ Q} q^{v_q(D) - v_q(a)}`.
-/
theorem valuation_bit (Q m n D : ℕ) (hn : n = m * Q) (hQ : Squarefree Q)
    (hm : 0 < m) (hD : D ∣ n) (hDpos : 0 < D) :
    (∀ q ∈ Q.primeFactors,
        D.factorization q - (Nat.gcd D m).factorization q ≤ 1) ∧
      D = (Nat.gcd D m) *
        ∏ q ∈ Q.primeFactors,
          q ^ (D.factorization q - (Nat.gcd D m).factorization q) := by
  constructor;
  · intro q hq;
    rw [ Nat.factorization_gcd ] <;> norm_num [ hDpos.ne', hm.ne' ];
    have h_factorization : D.factorization q ≤ n.factorization q := by
      exact ( Nat.factorization_le_iff_dvd ( by positivity ) ( by aesop ) ) |>.2 hD q;
    simp_all +decide [ Nat.factorization_mul, ne_of_gt ];
    cases min_cases ( D.factorization q ) ( m.factorization q ) <;> linarith [ show Q.factorization q ≤ 1 from Nat.le_of_not_lt fun h => absurd ( hQ.natFactorization_le_one q ) ( by linarith ) ];
  · refine' Nat.factorization_inj _ _ _ <;> norm_num [ hm.ne', hDpos.ne' ];
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ <| Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp;
    · rw [ Nat.factorization_mul ] <;> simp_all +decide [ Nat.factorization_prod, Finset.prod_eq_zero_iff, Nat.ne_of_gt ];
      ext p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∈ Q.primeFactors <;> simp_all +decide [ Nat.factorization_gcd, hm.ne', hDpos.ne' ] ;
      · rw [ Finset.sum_eq_single p ] <;> simp_all +decide;
      · have h_factorization_D_p : D.factorization p ≤ m.factorization p := by
          have h_factorization_D_p : D.factorization p ≤ (m * Q).factorization p := by
            exact ( Nat.factorization_le_iff_dvd ( by positivity ) ( by aesop ) ) |>.2 hD p;
          by_cases hQ : Q = 0 <;> simp_all +decide [ Nat.factorization_mul, hm.ne' ];
          simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd hp' ];
        simp_all +decide [ Nat.Prime.factorization ];
        exact fun i hi hi' hi'' => Or.inr <| Finsupp.single_eq_of_ne <| by rintro rfl; exact absurd ( hp' hi' ) hi'';

/-
**Lemma 9.1 (the reciprocal staircase sum).**  As `t → ∞`,
`∑_{r=2}^t 1/h_r = (2 log 2 + o(1)) · t / log t`.
-/
theorem hr_sum_asymp :
    Filter.Tendsto
      (fun t : ℕ => (∑ r ∈ Finset.Icc 2 t, (1 : ℝ) / (hr r)) / ((t : ℝ) / Real.log t))
      Filter.atTop (nhds (2 * Real.log 2)) := by
  -- To apply the Stolz-Cesàro theorem, we need to show that the sequence $b_t = \frac{t}{\log t}$ is strictly increasing and unbounded, and that the limit of $\frac{a_{t+1} - a_t}{b_{t+1} - b_t}$ exists.
  have h_stolz : Filter.Tendsto (fun t : ℕ => ((∑ r ∈ Finset.Icc 2 (t + 1), (1 / (hr r : ℝ))) - (∑ r ∈ Finset.Icc 2 t, (1 / (hr r : ℝ)))) / ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t)) Filter.atTop (nhds (2 * Real.log 2)) := by
    -- Simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun t : ℕ => (1 / (hr (t + 1) : ℝ)) / ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t)) Filter.atTop (nhds (2 * Real.log 2)) by
      convert! h_simp using 2;
      cases ‹_› <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
    -- We'll use the fact that $hr(t+1) \sim \frac{\log(t+1)}{2\log(2)}$ and $(t+1)/\log(t+1) - t/\log(t) \sim \frac{1}{\log(t)}$.
    have h_hr : Filter.Tendsto (fun t : ℕ => (hr (t + 1) : ℝ) * (1 / Real.log (t + 1))) Filter.atTop (nhds (1 / (2 * Real.log 2))) := by
      -- We'll use the fact that $hr(t+1) = \frac{1 + \log_2(t+1)}{2}$ and $\log_2(t+1) \sim \frac{\log(t+1)}{\log(2)}$.
      have h_hr : Filter.Tendsto (fun t : ℕ => (1 + Nat.log 2 (t + 1) : ℝ) / (2 * Real.log (t + 1))) Filter.atTop (nhds (1 / (2 * Real.log 2))) := by
        -- We'll use the fact that $Nat.log 2 (t + 1) \sim \frac{\log (t + 1)}{\log 2}$ as $t \to \infty$.
        have h_log : Filter.Tendsto (fun t : ℕ => (Nat.log 2 (t + 1) : ℝ) / Real.log (t + 1)) Filter.atTop (nhds (1 / Real.log 2)) := by
          -- We'll use the fact that $Nat.log 2 (t + 1)$ is approximately $\frac{\log (t + 1)}{\log 2}$.
          have h_log_approx : ∀ t : ℕ, t ≥ 1 → (Nat.log 2 (t + 1) : ℝ) ≥ Real.log (t + 1) / Real.log 2 - 1 ∧ (Nat.log 2 (t + 1) : ℝ) ≤ Real.log (t + 1) / Real.log 2 := by
            intro t ht; rw [ ge_iff_le, sub_le_iff_le_add ] ; rw [ div_le_iff₀ ( Real.log_pos one_lt_two ) ] ; rw [ le_div_iff₀ ( Real.log_pos one_lt_two ) ] ; norm_cast;
            exact ⟨ by rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ), by rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self _ ( by positivity ) ) ⟩;
          -- Using the approximation, we can bound the expression.
          have h_bound : ∀ t : ℕ, t ≥ 1 → abs ((Nat.log 2 (t + 1) : ℝ) / Real.log (t + 1) - 1 / Real.log 2) ≤ 1 / Real.log (t + 1) := by
            intro t ht; rw [ abs_le ] ; constructor <;> ring_nf at *;
            · nlinarith [ h_log_approx t ht, inv_pos.mpr ( Real.log_pos ( show ( 1 + t : ℝ ) > 1 by norm_cast; linarith ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 1 + t : ℝ ) > 1 by norm_cast; linarith ) ) ), Real.log_pos one_lt_two, inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ];
            · nlinarith [ h_log_approx t ht, inv_pos.mpr ( Real.log_pos ( show ( 1 + t : ℝ ) > 1 by norm_cast; linarith ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 1 + t : ℝ ) > 1 by norm_cast; linarith ) ) ), inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ];
          exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun t ht => by simpa using! h_bound t ht ⟩ ) <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop;
        convert! h_log.const_mul ( 1 / 2 ) |> Filter.Tendsto.add <| show Filter.Tendsto ( fun t : ℕ => ( 1 : ℝ ) / ( 2 * Real.log ( t + 1 ) ) ) Filter.atTop ( nhds 0 ) from ?_ using 2 <;> ring_nf;
        exact le_trans ( Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| tendsto_const_nhds.add_atTop <| tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ( by norm_num );
      have h_hr_floor : ∀ t : ℕ, t ≥ 1 → (hr (t + 1) : ℝ) ≥ (1 + Nat.log 2 (t + 1) - 1) / 2 ∧ (hr (t + 1) : ℝ) ≤ (1 + Nat.log 2 (t + 1)) / 2 := by
        intro t ht; norm_num [ hr, sr ] ;
        rw [ div_le_iff₀, le_div_iff₀ ] <;> norm_cast;
        omega;
      have h_hr_floor : Filter.Tendsto (fun t : ℕ => ((1 + Nat.log 2 (t + 1) - 1) / 2 : ℝ) / Real.log (t + 1)) Filter.atTop (nhds (1 / (2 * Real.log 2))) := by
        convert! h_hr.sub ( show Filter.Tendsto ( fun t : ℕ => ( 1 : ℝ ) / ( 2 * Real.log ( t + 1 ) ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop <| Filter.Tendsto.const_mul_atTop zero_lt_two <| Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) using 2 <;> ring;
      refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_hr_floor h_hr _ _;
      · filter_upwards [ Filter.eventually_ge_atTop 1 ] with t ht using by rw [ mul_one_div ] ; exact div_le_div_of_nonneg_right ( by aesop ) ( Real.log_nonneg ( by linarith ) ) ;
      · filter_upwards [ Filter.eventually_ge_atTop 1 ] with t ht using by rw [ mul_one_div ] ; exact by rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( t : ℝ ) + 1 > 1 by norm_cast; linarith ), ‹∀ t : ℕ, t ≥ 1 → ( hr ( t + 1 ) : ℝ ) ≥ ( 1 + Nat.log 2 ( t + 1 ) - 1 ) / 2 ∧ ( hr ( t + 1 ) : ℝ ) ≤ ( 1 + Nat.log 2 ( t + 1 ) ) / 2› t ht ] ;
    have h_diff : Filter.Tendsto (fun t : ℕ => ((t + 1) / Real.log (t + 1) - t / Real.log t) * Real.log (t + 1)) Filter.atTop (nhds 1) := by
      -- Simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun t : ℕ => (t + 1) - t * (Real.log (t + 1) / Real.log t)) Filter.atTop (nhds 1) by
        refine h_simplify.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with t ht;
        field_simp;
        rw [ mul_sub, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith ) ) ) ] ; ring;
      -- We'll use the fact that $\log(t+1) = \log t + \log(1 + 1/t)$.
      suffices h_log : Filter.Tendsto (fun t : ℕ => (t : ℝ) * (Real.log (t + 1) - Real.log t) / Real.log t) Filter.atTop (nhds 0) by
        have := h_log.const_sub 1;
        simpa using! this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_sub, sub_div, mul_div_cancel_right₀ _ ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hx ) ] ; ring );
      -- We'll use the fact that $\log(t+1) - \log(t) = \log\left(1 + \frac{1}{t}\right)$.
      suffices h_log : Filter.Tendsto (fun t : ℕ => (t : ℝ) * Real.log (1 + 1 / t) / Real.log t) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ one_add_div ( by positivity ), Real.log_div ( by positivity ) ( by positivity ) ] );
      -- We'll use the fact that $t \log(1 + 1/t) \to 1$ as $t \to \infty$.
      have h_log : Filter.Tendsto (fun t : ℕ => (t : ℝ) * Real.log (1 + 1 / t)) Filter.atTop (nhds 1) := by
        -- We'll use the fact that $(1 + \frac{1}{t})^t \to e$ as $t \to \infty$.
        have h_exp : Filter.Tendsto (fun t : ℕ => (1 + 1 / (t : ℝ)) ^ t) Filter.atTop (nhds (Real.exp 1)) := by
          convert! Real.tendsto_one_add_div_pow_exp 1;
        simpa using! Filter.Tendsto.log h_exp <| by positivity;
      simpa using! h_log.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    convert! h_hr.inv₀ _ |> Filter.Tendsto.mul <| h_diff.inv₀ _ using 2 <;> norm_num;
    by_cases h : Real.log ( ( ‹_› : ℕ ) + 1 ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm ];
    norm_cast at * ; aesop;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε;
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ t ≥ N, dist ((∑ r ∈ Finset.Icc 2 (t + 1), (1 / (hr r : ℝ))) - (∑ r ∈ Finset.Icc 2 t, (1 / (hr r : ℝ)))) ((2 * Real.log 2) * ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t)) < ε / 2 * ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t) := by
    have h_pos : ∀ᶠ t : ℕ in Filter.atTop, 0 < ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t) := by
      filter_upwards [ Filter.eventually_gt_atTop 2 ] with t ht;
      rw [ sub_pos, div_lt_div_iff₀ ] <;> try linarith [ Real.log_pos ( by norm_cast ; linarith : ( 1 :ℝ ) < t ), Real.log_pos ( by norm_cast ; linarith : ( 1 :ℝ ) < t + 1 ) ];
      rw [ ← Real.log_rpow, ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_cast <;> try positivity;
      -- We can divide both sides by $t^t$ to get $(1 + 1/t)^t < t$.
      have h_div : (1 + 1 / t : ℝ) ^ t < t := by
        -- By Bernoulli's inequality, we have $(1 + 1/t)^t \leq e < t$ for $t > 2$.
        have h_bernoulli : (1 + 1 / (t : ℝ)) ^ t ≤ Real.exp 1 := by
          rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ];
          exact Real.exp_le_exp.mpr ( by nlinarith [ one_div_mul_cancel ( by positivity : ( t : ℝ ) ≠ 0 ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 1 + 1 / ( t : ℝ ) ) ) ] );
        exact lt_of_le_of_lt h_bernoulli <| Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( t : ℝ ) ≥ 3 by norm_cast ] ;
      rw [ one_add_div, div_pow, div_lt_iff₀ ] at h_div <;> norm_cast at * <;> ring_nf at * <;> nlinarith [ pow_pos ( by linarith : 0 < t ) t ];
    obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( h_stolz ( ε / 2 ) ( half_pos hε ) |> Filter.Eventually.and <| h_pos );
    exact ⟨ N, fun t ht => by rw [ dist_eq_norm ] ; rw [ Real.norm_eq_abs ] ; rw [ abs_lt ] ; constructor <;> nlinarith [ abs_lt.mp ( hN t ht |>.1 ), hN t ht |>.2, mul_div_cancel₀ ( ∑ r ∈ Finset.Icc 2 ( t + 1 ), 1 / ( hr r : ℝ ) - ∑ r ∈ Finset.Icc 2 t, 1 / ( hr r : ℝ ) ) ( ne_of_gt ( hN t ht |>.2 ) ) ] ⟩;
  -- By summation by parts, we can bound the difference.
  have h_summation_by_parts : ∀ t ≥ N + 2, abs ((∑ r ∈ Finset.Icc 2 t, (1 / (hr r : ℝ))) - (2 * Real.log 2) * (t / Real.log t)) ≤ abs ((∑ r ∈ Finset.Icc 2 (N + 1), (1 / (hr r : ℝ))) - (2 * Real.log 2) * ((N + 1) / Real.log (N + 1))) + (ε / 2) * (t / Real.log t - (N + 1) / Real.log (N + 1)) := by
    intro t ht
    induction' t, ht using Nat.le_induction with t ht ih;
    · have hstep := hN (N + 1) (by omega)
      have hb := abs_le.mp (le_refl |(∑ r ∈ Finset.Icc 2 (N + 1), (1 / (hr r : ℝ))) -
        (2 * Real.log 2) * ((N + 1) / Real.log (N + 1))|)
      norm_num [add_assoc, dist_eq_norm] at hstep hb ⊢
      exact abs_le.mpr ⟨by nlinarith [abs_lt.mp hstep], by nlinarith [abs_lt.mp hstep]⟩
    · have := hN t ( by linarith ) ; norm_num at *;
      exact abs_le.mpr ⟨ by linarith [ abs_le.mp ih, abs_lt.mp this ], by linarith [ abs_le.mp ih, abs_lt.mp this ] ⟩;
  -- Choose $T$ such that for all $t \geq T$, the term $\frac{|∑ r ∈ Finset.Icc 2 (N + 1), (1 / (hr r : ℝ)) - (2 * Real.log 2) * ((N + 1) / Real.log (N + 1))|}{t / Real.log t} < \frac{\epsilon}{2}$.
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ∀ t ≥ T, abs ((∑ r ∈ Finset.Icc 2 (N + 1), (1 / (hr r : ℝ))) - (2 * Real.log 2) * ((N + 1) / Real.log (N + 1))) / (t / Real.log t) < ε / 2 := by
    have h_lim : Filter.Tendsto (fun t : ℕ => (t : ℝ) / Real.log t) Filter.atTop Filter.atTop := by
      -- We can use the change of variables $u = \log t$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
        have := h_log.comp Real.tendsto_log_atTop;
        exact this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.exp_log ( Nat.cast_pos.mpr hx ) ] );
      simpa using! Real.tendsto_exp_div_pow_atTop 1;
    exact Filter.eventually_atTop.mp ( h_lim.eventually_gt_atTop ( |∑ r ∈ Icc 2 ( N + 1 ), 1 / ( hr r : ℝ ) - 2 * Real.log 2 * ( ( N + 1 ) / Real.log ( N + 1 ) )| / ( ε / 2 ) ) ) |> fun ⟨ T, hT ⟩ => ⟨ T, fun t ht => by rw [ div_lt_iff₀ ] <;> nlinarith [ hT t ht, abs_nonneg ( ∑ r ∈ Icc 2 ( N + 1 ), 1 / ( hr r : ℝ ) - 2 * Real.log 2 * ( ( N + 1 ) / Real.log ( N + 1 ) ) ), mul_div_cancel₀ ( |∑ r ∈ Icc 2 ( N + 1 ), 1 / ( hr r : ℝ ) - 2 * Real.log 2 * ( ( N + 1 ) / Real.log ( N + 1 ) )| ) ( ne_of_gt ( half_pos hε ) ) ] ⟩;
  filter_upwards [ Filter.eventually_ge_atTop ( N + 2 ), Filter.eventually_ge_atTop T, Filter.eventually_gt_atTop 1 ] with t ht₁ ht₂ ht₃;
  rw [ dist_eq_norm ];
  rw [ Real.norm_eq_abs, abs_lt ];
  constructor <;> nlinarith [ abs_le.mp ( h_summation_by_parts t ht₁ ), hT t ht₂, show ( t : ℝ ) / Real.log t > 0 from div_pos ( by positivity ) ( Real.log_pos ( by norm_cast ) ), mul_div_cancel₀ ( ∑ r ∈ Finset.Icc 2 t, 1 / ( hr r : ℝ ) ) ( show ( t : ℝ ) / Real.log t ≠ 0 from ne_of_gt ( div_pos ( by positivity ) ( Real.log_pos ( by norm_cast ) ) ) ), mul_div_cancel₀ ( |∑ r ∈ Finset.Icc 2 ( N + 1 ), 1 / ( hr r : ℝ ) - 2 * Real.log 2 * ( ( N + 1 : ℝ ) / Real.log ( N + 1 ) )| ) ( show ( t : ℝ ) / Real.log t ≠ 0 from ne_of_gt ( div_pos ( by positivity ) ( Real.log_pos ( by norm_cast ) ) ) ), show ( N + 1 : ℝ ) / Real.log ( N + 1 ) ≥ 0 from div_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ]

/-
**Optimisation, lower half.**  For every `λ > 0`,
`c₀ ≤ max(λ/2, λ/4 + 1/(4λ log 2))`.
-/
theorem opt_lower (lam : ℝ) (hlam : 0 < lam) :
    c₀ ≤ max (lam / 2) (lam / 4 + 1 / (4 * lam * Real.log 2)) := by
  refine' le_max_of_le_right _;
  unfold c₀;
  rw [ div_add_div, div_le_div_iff₀ ] <;> try positivity;
  nlinarith [ sq_nonneg ( lam * Real.sqrt ( Real.log 2 ) - 1 ), Real.sqrt_nonneg ( Real.log 2 ), Real.mul_self_sqrt ( show 0 ≤ Real.log 2 by positivity ), Real.log_pos one_lt_two, mul_pos hlam ( Real.sqrt_pos.mpr ( show 0 < Real.log 2 by positivity ) ), mul_pos hlam ( Real.log_pos one_lt_two ) ]

/-
**Optimisation, attainment.**  At `λ₀ = 1/√(log 2)` the two branches agree
and equal `c₀`, so the infimum in the optimisation is exactly `c₀`.
-/
theorem opt_attained :
    max ((1 / Real.sqrt (Real.log 2)) / 2)
        ((1 / Real.sqrt (Real.log 2)) / 4
          + 1 / (4 * (1 / Real.sqrt (Real.log 2)) * Real.log 2)) = c₀ := by
  unfold c₀;
  grind

end Erdos768
