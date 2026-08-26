/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied for the problem-specific proof.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 793.
Informal authors: GPT-5.6 Sol Ultra, prompted by Przemek Chojecki;
the upper-bound argument refines Paul Erdős's 1938 proof.
Formal authors: Aristotle, Wouter van Doorn.
Jake Mallen integrated the complete PNT dependency in the selected source.
Source: https://www.erdosproblems.com/793#post-7596
https://github.com/Woett/Lean-files/blob/ce4bcdac98415c60c7a7d7f78ce54c9adb79bc47/ErdosProblem793.lean
https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/793
Selected complete source: Lean 4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
The original single-file upload does not specify a toolchain.
This port reuses the tracked PNT+ library instead of copying its vendored proof.
-/
import ErdosProblems.Erdos793.Definitions

open Filter Real
open scoped BigOperators Topology

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos793

/-- Any strongly 2-primitive subset of `[n]` has cardinality at most `F n`. -/
lemma card_le_F (n : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 n)
    (hA : Strongly2Primitive A) : A.card ≤ F n := by
  classical
  refine' Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hsub, hA ⟩ )

/-- The normalizing quantity `S(n) = n^{2/3} / (log n)^2`. -/
noncomputable def S (n : ℕ) : ℝ := (n : ℝ) ^ ((2:ℝ)/3) / (Real.log n)^2

/-
If every element `a` of a finite strongly 2-primitive set `A` is written as a
product `a = u a * v a` of two elements of a finite set `B`, then `|A| ≤ |B|`.
-/
lemma private_factor (A B : Finset ℕ) (u v : ℕ → ℕ)
    (hu : ∀ a ∈ A, u a ∈ B) (hv : ∀ a ∈ A, v a ∈ B)
    (hfac : ∀ a ∈ A, a = u a * v a)
    (hA : Strongly2Primitive A) : A.card ≤ B.card := by
  -- For `a ∈ A` and `x ∈ B`, let `μ a x = (if u a = x then 1 else 0) + (if v a = x then 1 else 0) : ℕ`, a value in `{0,1,2}`.
  set mu : ℕ → ℕ → ℕ := fun a x => (if u a = x then 1 else 0) + (if v a = x then 1 else 0);
  -- Claim: for each `a ∈ A` there exists `x ∈ B` such that for all `b ∈ A` with `b ≠ a`, `μ b x < μ a x`. Call such `x` a private coordinate for `a`.
  have h_private : ∀ a ∈ A, ∃ x ∈ B, ∀ b ∈ A, b ≠ a → mu b x < mu a x := by
    intro a ha
    by_cases huv : u a = v a;
    · grind +splitIndPred;
    · -- Suppose neither `u a` nor `v a` is private. Not-private for `u a` means there is `b ≠ a` in `A` with `μ b (u a) ≥ μ a (u a) = 1`, i.e. `u a ∈ {u b, v b}`.
      by_contra h_not_private
      push Not at h_not_private
      obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ A, b ≠ a ∧ u a ∈ ({u b, v b} : Finset ℕ) := by
        grind +splitImp
      obtain ⟨c, hc₁, hc₂⟩ : ∃ c ∈ A, c ≠ a ∧ v a ∈ ({u c, v c} : Finset ℕ) := by
        grind;
      -- Then `a = u a * v a` divides `(u b * v b) * (u c * v c) = b * c` (since `u a ∣ b` and `v a ∣ c`, using `a = b`,`a=c` factorizations `hfac`).
      have h_div : a ∣ b * c := by
        rw [ hfac a ha, hfac b hb₁, hfac c hc₁ ];
        norm_num at *;
        rcases hb₂.2 with ( h | h ) <;> rcases hc₂.2 with ( j | j ) <;> rw [ h, j ] <;> ring_nf;
        · exact dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
        · exact dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
        · exact ⟨ u b * v c, by ring ⟩;
        · exact dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
      exact hA a ha b hb₁ c hc₁ ( by tauto ) ( by tauto ) h_div;
  choose! x hx₁ hx₂ using h_private;
  have h_inj : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → x a ≠ x b := by
    grind;
  exact Finset.card_le_card ( show A.image x ⊆ B from Finset.image_subset_iff.mpr hx₁ ) |> le_trans ( by rw [ Finset.card_image_of_injOn fun a ha b hb hab => by contrapose! hab; exact h_inj a ha b hb hab ] )

/-- A finite set `B` is a *two-factor basis for `[n]`* if every `m ∈ [n]` is a
product of two elements of `B`. -/
def TwoFactorBasis (B : Finset ℕ) (n : ℕ) : Prop :=
  ∀ m ∈ Finset.Icc 1 n, ∃ u ∈ B, ∃ v ∈ B, m = u * v

/-
If `B` is a finite two-factor basis for `[n]`, then every strongly 2-primitive
`A ⊆ [n]` satisfies `|A| ≤ |B|`.
-/
lemma basis_bound (B : Finset ℕ) (n : ℕ) (hB : TwoFactorBasis B n)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 n) (hA : Strongly2Primitive A) :
    A.card ≤ B.card := by
  convert private_factor _ _ _ _ _ _ _ _;
  exact fun a => if h : a ∈ A then Classical.choose ( hB a ( hAsub h ) ) else 1;
  exact fun a => if h : a ∈ A then Classical.choose ( Classical.choose_spec ( hB a ( hAsub h ) ) |>.2 ) else 1;
  · intro a ha; have := Classical.choose_spec ( hB a ( hAsub ha ) ) ; aesop;
  · grind +splitImp;
  · grind;
  · assumption

/-
Consequently `F n ≤ |B|` for any two-factor basis `B` of `[n]`.
-/
lemma F_le_basis_card (B : Finset ℕ) (n : ℕ) (hB : TwoFactorBasis B n) :
    F n ≤ B.card := by
  -- Apply `Finset.sup_le` to the set of all strong 2-primitive subsets of `[n]`.
  apply Finset.sup_le;
  intro A hA;
  simp +zetaDelta at *;
  exact basis_bound B n hB A hA.1 hA.2

/-! ## Analytic preliminaries from the prime number theorem -/

/-- The prime number theorem hypothesis (the permitted analytic input): there is
an error function `c = o(1)` with `π(⌊x⌋) = (1 + c x)·x / log x` for all `x`.

This is stated as a `Prop` and threaded as a hypothesis through the analytic
lemmas; it is discharged once via `pi_alt`. -/
def PNT : Prop := ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, (Nat.primeCounting ⌊x⌋₊ : ℝ) = (1 + c x) * x / Real.log x

/-
Reformulation of the PNT hypothesis with the error term expressed as a
limit.
-/
lemma exists_pnt_error (hpnt : PNT) :
    ∃ c : ℝ → ℝ, Tendsto c atTop (𝓝 0) ∧
      ∀ x : ℝ, (Nat.primeCounting ⌊x⌋₊ : ℝ) = (1 + c x) * x / log x := by
  obtain ⟨c, hc, hform⟩ := hpnt;
  exact ⟨ c, by simpa using hc.tendsto_div_nhds_zero, hform ⟩

/-
The prime-counting function is bounded by its argument.
-/
lemma primeCounting_le_self (n : ℕ) : Nat.primeCounting n ≤ n := by
  convert Nat.le_of_lt_succ _;
  rw [ Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
  exact lt_of_lt_of_le ( Finset.card_lt_card <| Finset.filter_ssubset.mpr <| ⟨ 0, by norm_num ⟩ ) <| by norm_num;

/-
The number of primes in `(a, b]` is `π(b) - π(a)`.
-/
lemma card_primes_Ioc (a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card = Nat.primeCounting b - Nat.primeCounting a := by
  have h_card_split : (Finset.filter Nat.Prime (Finset.Ioc a b)).card = (Finset.filter Nat.Prime (Finset.Icc 1 b)).card - (Finset.filter Nat.Prime (Finset.Icc 1 a)).card := by
    rw [ show Finset.filter Nat.Prime ( Finset.Ioc a b ) = Finset.filter Nat.Prime ( Finset.Icc 1 b ) \ Finset.filter Nat.Prime ( Finset.Icc 1 a ) from ?_, Finset.card_sdiff ];
    · rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right hab ) ];
    · grind;
  rw [ h_card_split, Nat.primeCounting, Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ];
  congr 2 <;> ext x <;> simp +arith +decide;
  · exact fun hx _ => hx.pos;
  · exact fun _ _ => Nat.Prime.pos ‹_›

/-- `π(⌊x⌋) ≤ x` for `x ≥ 0`. -/
lemma piR_le (x : ℝ) (hx : 0 ≤ x) : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x := by
  calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
            exact_mod_cast primeCounting_le_self _
    _ ≤ x := Nat.floor_le hx

/-
For every fixed `c > 0`, `π(⌊c·x⌋)·log x / x → c` as `x → ∞`.
-/
lemma pi_mul_ratio (hpnt : PNT) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊c * x⌋₊ : ℝ) * log x / x) atTop (𝓝 c) := by
  obtain ⟨ e, he₁, he₂ ⟩ := exists_pnt_error hpnt;
  -- Substitute the expression for $\pi(\lfloor c \cdot x \rfloor)$ into the limit.
  suffices h_subst : Filter.Tendsto (fun x => ((1 + e (c * x)) * (c * x) / Real.log (c * x)) * Real.log x / x) Filter.atTop (𝓝 c) by
    grind;
  -- Simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun x => (1 + e (c * x)) * c * (Real.log x / Real.log (c * x))) Filter.atTop (𝓝 c) by
    refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ eq_div_iff hx.ne' ] ; ring );
  -- We'll use the fact that $\frac{\log x}{\log (c x)} = \frac{\log x}{\log c + \log x} \to 1$ as $x \to \infty$.
  have h_log_ratio : Filter.Tendsto (fun x => Real.log x / (Real.log c + Real.log x)) Filter.atTop (nhds 1) := by
    -- We can divide the numerator and the denominator by $\log x$.
    suffices h_div : Filter.Tendsto (fun x => 1 / (Real.log c / Real.log x + 1)) Filter.atTop (nhds 1) by
      refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ div_add_one, div_div_eq_mul_div ] ; ring ; linarith [ Real.log_pos hx ] );
    exact le_trans ( tendsto_const_nhds.div ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ( by norm_num ) ) ( by norm_num );
  have hleft := ((he₁.comp (Filter.tendsto_id.const_mul_atTop hc)).const_add 1).mul_const c
  have hratio : Tendsto (fun x => Real.log x / Real.log (c * x)) atTop (𝓝 1) :=
    h_log_ratio.congr' (by
      filter_upwards [Filter.eventually_gt_atTop 0] with x hx
      rw [Real.log_mul hc.ne' hx.ne'])
  simpa using hleft.mul hratio

/-- Basic prime number theorem: `π(⌊x⌋)·log x / x → 1`. -/
lemma pnt (hpnt : PNT) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * log x / x) atTop (𝓝 1) := by
  have := pi_mul_ratio hpnt 1 one_pos
  simpa using this

/-
There is a constant `C > 0` such that `π(⌊x⌋) ≤ C · x / log x` for every real
`x ≥ 2`.
-/
lemma pi_upper (hpnt : PNT) : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 2 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / log x := by
  -- Set `C = max 2 (Real.log x₀)` (note `Real.log x₀ ≥ Real.log 2 > 0` since `x₀ ≥ 2`, so `C > 0`).
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) * (Real.log x) / x ≤ 2 := by
    obtain ⟨ x₀, hx₀ ⟩ := Metric.tendsto_atTop.mp ( pnt hpnt ) 1 zero_lt_one;
    exact ⟨ Max.max x₀ 2, le_max_right _ _, fun x hx => by linarith [ abs_lt.mp ( hx₀ x ( le_trans ( le_max_left _ _ ) hx ) ) ] ⟩;
  have h_log_x₀ : Real.log x₀ > 0 := by
    exact Real.log_pos <| by linarith;
  refine' ⟨ Max.max 2 ( Real.log x₀ ), _, _ ⟩ <;> norm_num;
  intro x hx; rw [ le_div_iff₀ ( Real.log_pos <| by linarith ) ] ; cases le_total x x₀ <;> simp_all +decide [ mul_div_assoc ] ;
  · refine' le_trans ( mul_le_mul_of_nonneg_right ( show ( Nat.primeCounting ⌊x⌋₊ : ℝ ) ≤ x from _ ) ( Real.log_nonneg <| by linarith ) ) _;
    · exact piR_le x ( by linarith );
    · nlinarith [ le_max_left 2 ( Real.log x₀ ), le_max_right 2 ( Real.log x₀ ), Real.log_le_log ( by linarith ) ( by linarith : x ≤ x₀ ) ];
  · have := hx₀.2 x ‹_›; rw [ mul_div, div_le_iff₀ ( by linarith ) ] at this; nlinarith [ le_max_left 2 ( Real.log x₀ ), le_max_right 2 ( Real.log x₀ ) ] ;

/-- Sum of reciprocal squares of the primes in the real interval `(x, A·x]`. -/
noncomputable def primeSqSum (x A : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊A * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2)

/-
For fixed `0 < c ≤ d`, the number of primes in `(cx, dx]`, times `log x / x`,
tends to `d - c`.
-/
lemma pi_diff_ratio (hpnt : PNT) (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun x : ℝ =>
      (((Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime).card : ℝ) * log x / x)
      atTop (𝓝 (d - c)) := by
  convert Tendsto.sub ( pi_mul_ratio hpnt d ( by linarith ) ) ( pi_mul_ratio hpnt c hc ) |> Filter.Tendsto.congr' _ using 2;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx;
  rw [ card_primes_Ioc _ _ ( Nat.floor_mono <| by nlinarith ) ];
  rw [ Nat.cast_sub ( Nat.monotone_primeCounting <| Nat.floor_mono <| by nlinarith ) ] ; ring

/-
For `0 < c ≤ d` and `x > 0`, the reciprocal-square sum over primes in `(cx, dx]`
is between `cnt/(dx)²` and `cnt/(cx)²`, where `cnt` is the number of such
primes.
-/
lemma primeSq_block_bounds (c d x : ℝ) (hc : 0 < c) (hcd : c ≤ d) (hx : 0 < x) :
    (((Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime).card : ℝ) / (d * x) ^ 2 ≤
        (∑ p ∈ (Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ∧
    (∑ p ∈ (Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ≤
        (((Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime).card : ℝ) / (c * x) ^ 2 := by
  constructor;
  · -- Since $p \leq \lfloor d * x \rfloor$, we have $p^2 \leq (\lfloor d * x \rfloor)^2$.
    have h_prime_sq_le : ∀ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊), (p : ℝ) ^ 2 ≤ (d * x) ^ 2 := by
      exact fun p hp => pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) <| Nat.floor_le <| by nlinarith ) _;
    exact le_trans ( by norm_num [ div_eq_mul_inv ] ) ( Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le ( sq_pos_of_pos <| Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) <| h_prime_sq_le p hp );
  · -- Apply the bound to each term in the sum.
    have h_term_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊), (1 / (p : ℝ) ^ 2) ≤ (1 / (c * x) ^ 2) := by
      intro p hp; gcongr ; nlinarith [ Nat.lt_of_floor_lt ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) ] ;
    simpa [div_eq_mul_inv] using Finset.sum_le_sum h_term_bound

/-
Telescoping split of a filtered `Ioc`-sum along a monotone partition.
-/
lemma sum_Ioc_filter_split {M : Type*} [AddCommMonoid M] (a : ℕ → ℕ) (ha : Monotone a)
    (P : ℕ → Prop) [DecidablePred P] (f : ℕ → M) (K : ℕ) :
    ∑ j ∈ Finset.range K, ∑ p ∈ (Finset.Ioc (a j) (a (j + 1))).filter P, f p
      = ∑ p ∈ (Finset.Ioc (a 0) (a K)).filter P, f p := by
  induction K <;> simp_all +decide [ Finset.sum_range_succ ];
  simp +decide only [Finset.sum_filter];
  rw [ Finset.sum_Ioc_consecutive ] <;> aesop

/-
For fixed `A > 1`, `(∑_{x<p≤Ax} 1/p²)·(x·log x) → 1 - 1/A` as `x → ∞`.
-/
lemma primeSq_interval (hpnt : PNT) (A : ℝ) (hA : 1 < A) :
    Tendsto (fun x : ℝ => primeSqSum x A * (x * log x)) atTop (𝓝 (1 - 1 / A)) := by
  -- Fix `A > 1`. For a partition parameter `K : ℕ`, `K ≥ 1`, set `c j = A ^ ((j:ℝ)/K)` (so `c 0 = 1`, `c K = A`, and `c` is strictly increasing in `j`; let `r = A^(1/K) > 1`, so `c (j+1) = r * c j`). Write `S x = primeSqSum x A * (x * Real.log x)`.
  suffices h_suff : ∀ ε > 0, ∃ K : ℕ, K ≥ 1 ∧ ∃ N : ℝ, ∀ x ≥ N, abs (primeSqSum x A * (x * Real.log x) - (1 - 1 / A)) < ε by
    exact Metric.tendsto_atTop.mpr fun ε hε => by obtain ⟨ K, hK₁, N, hN ⟩ := h_suff ε hε; exact ⟨ N, fun x hx => hN x hx ⟩ ;
  intro ε hε_pos
  obtain ⟨K, hK_pos, hK⟩ : ∃ K : ℕ, K ≥ 1 ∧ (A^(2 / (K : ℝ)) - 1) * (1 - 1 / A) < ε / 2 := by
    have h_lim : Filter.Tendsto (fun K : ℕ => (A^(2 / (K : ℝ)) - 1) * (1 - 1 / A)) Filter.atTop (nhds 0) := by
      exact le_trans ( Filter.Tendsto.mul ( Filter.Tendsto.sub ( tendsto_const_nhds.rpow ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) ( Or.inl <| by linarith ) ) tendsto_const_nhds ) tendsto_const_nhds ) ( by norm_num );
    exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds <| half_pos hε_pos ) ) |> fun ⟨ K, hK ⟩ ↦ ⟨ K + 1, by linarith, hK _ <| by linarith ⟩;
  -- Define `c j = A ^ ((j:ℝ)/K)` and `blkCard j x = (((Finset.Ioc ⌊c j*x⌋₊ ⌊c(j+1)*x⌋₊).filter Nat.Prime).card : ℝ)`.
  set c : ℕ → ℝ := fun j => A ^ ((j : ℝ) / K)
  set blkCard : ℕ → ℝ → ℝ := fun j x => (((Finset.Ioc ⌊c j * x⌋₊ ⌊c (j + 1) * x⌋₊).filter Nat.Prime).card : ℝ);
  -- By `pi_diff_ratio hpnt (c j) (c(j+1))` (with `0 < c j ≤ c(j+1)`), `blkCard j x*log x/x → c(j+1)-c j`; dividing by the constant `(c(j+1))^2` resp `(c j)^2` and summing (`Filter.Tendsto.div_const`, `tendsto_finset_sum`), `Tendsto lowS atTop (𝓝 LK)` and `Tendsto uppS atTop (𝓝 UK)`.
  have h_lowS_uppS : Filter.Tendsto (fun x => ∑ j ∈ Finset.range K, (blkCard j x * Real.log x / x) / (c (j + 1))^2) Filter.atTop (nhds (∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c (j + 1))^2)) ∧ Filter.Tendsto (fun x => ∑ j ∈ Finset.range K, (blkCard j x * Real.log x / x) / (c j)^2) Filter.atTop (nhds (∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c j)^2)) := by
    have h_lowS_uppS : ∀ j ∈ Finset.range K, Filter.Tendsto (fun x => blkCard j x * Real.log x / x) Filter.atTop (nhds (c (j + 1) - c j)) := by
      intro j hj; exact pi_diff_ratio hpnt ( c j ) ( c ( j + 1 ) ) ( by positivity ) ( by exact Real.rpow_le_rpow_of_exponent_le hA.le ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; norm_num ) ) ;
    exact ⟨ tendsto_finsetSum _ fun j hj => Filter.Tendsto.div_const ( h_lowS_uppS j hj ) _, tendsto_finsetSum _ fun j hj => Filter.Tendsto.div_const ( h_lowS_uppS j hj ) _ ⟩;
  -- By `primeSq_block_bounds (c j) (c(j+1)) x` per block (times `x*log x ≥ 0`), one gets `lowS x ≤ S x ≤ uppS x`.
  have h_sandwich : ∀ x : ℝ, 1 ≤ x → ∑ j ∈ Finset.range K, (blkCard j x * Real.log x / x) / (c (j + 1))^2 ≤ primeSqSum x A * (x * Real.log x) ∧ primeSqSum x A * (x * Real.log x) ≤ ∑ j ∈ Finset.range K, (blkCard j x * Real.log x / x) / (c j)^2 := by
    intro x hx
    have h_sandwich_step : primeSqSum x A = ∑ j ∈ Finset.range K, ∑ p ∈ (Finset.Ioc ⌊c j * x⌋₊ ⌊c (j + 1) * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2) := by
      convert sum_Ioc_filter_split ( fun j => ⌊c j * x⌋₊ ) ( fun j k hjk => Nat.floor_mono <| mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow_of_exponent_le hA.le <| by gcongr ) <| by positivity ) Nat.Prime ( fun p => 1 / ( p : ℝ ) ^ 2 ) K |> Eq.symm using 1;
      simp +zetaDelta at *;
      norm_num [ show K ≠ 0 by linarith ];
      unfold primeSqSum; aesop;
    have h_sandwich_step : ∀ j ∈ Finset.range K, blkCard j x / (c (j + 1) * x) ^ 2 ≤ ∑ p ∈ (Finset.Ioc ⌊c j * x⌋₊ ⌊c (j + 1) * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2) ∧ ∑ p ∈ (Finset.Ioc ⌊c j * x⌋₊ ⌊c (j + 1) * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2) ≤ blkCard j x / (c j * x) ^ 2 := by
      intros j hj
      apply primeSq_block_bounds (c j) (c (j + 1)) x (by
      positivity) (by
      exact Real.rpow_le_rpow_of_exponent_le hA.le ( by gcongr ; linarith )) (by
      positivity);
    have h_sandwich_step : ∑ j ∈ Finset.range K, blkCard j x / (c (j + 1) * x) ^ 2 ≤ primeSqSum x A ∧ primeSqSum x A ≤ ∑ j ∈ Finset.range K, blkCard j x / (c j * x) ^ 2 := by
      exact ⟨ by rw [ ‹primeSqSum x A = _› ] ; exact Finset.sum_le_sum fun j hj => h_sandwich_step j hj |>.1, by rw [ ‹primeSqSum x A = _› ] ; exact Finset.sum_le_sum fun j hj => h_sandwich_step j hj |>.2 ⟩;
    convert And.intro ( mul_le_mul_of_nonneg_right h_sandwich_step.1 ( show 0 ≤ x * Real.log x by exact mul_nonneg ( by positivity ) ( Real.log_nonneg hx ) ) ) ( mul_le_mul_of_nonneg_right h_sandwich_step.2 ( show 0 ≤ x * Real.log x by exact mul_nonneg ( by positivity ) ( Real.log_nonneg hx ) ) ) using 1 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    · norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hx ) ];
    · field_simp;
  -- By `step2`, we have `LK ≤ 1 - 1/A ≤ UK`.
  have h_bounds : ∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c (j + 1))^2 ≤ 1 - 1 / A ∧ 1 - 1 / A ≤ ∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c j)^2 := by
    have h_bounds : ∀ j ∈ Finset.range K, (c (j + 1) - c j) / (c (j + 1))^2 ≤ 1 / c j - 1 / c (j + 1) ∧ 1 / c j - 1 / c (j + 1) ≤ (c (j + 1) - c j) / (c j)^2 := by
      intro j hj; rw [ div_sub_div, div_le_div_iff₀, div_le_div_iff₀ ] <;> try positivity;
      constructor <;> nlinarith only [ show 0 < c j from by positivity, show 0 < c ( j + 1 ) from by positivity, show c j ≤ c ( j + 1 ) from by exact Real.rpow_le_rpow_of_exponent_le hA.le ( by gcongr ; linarith ), mul_le_mul_of_nonneg_left ( show c j ≤ c ( j + 1 ) from by exact Real.rpow_le_rpow_of_exponent_le hA.le ( by gcongr ; linarith ) ) ( show 0 ≤ c j from by positivity ), mul_le_mul_of_nonneg_left ( show c j ≤ c ( j + 1 ) from by exact Real.rpow_le_rpow_of_exponent_le hA.le ( by gcongr ; linarith ) ) ( show 0 ≤ c ( j + 1 ) from by positivity ) ];
    have h_telescope : ∑ j ∈ Finset.range K, (1 / c j - 1 / c (j + 1)) = 1 - 1 / A := by
      convert Finset.sum_range_sub' _ _ using 3 <;> norm_num [ c ];
      rw [ div_self ( by positivity ), Real.rpow_one ];
    exact ⟨ h_telescope ▸ Finset.sum_le_sum fun j hj => h_bounds j hj |>.1, h_telescope ▸ Finset.sum_le_sum fun j hj => h_bounds j hj |>.2 ⟩;
  -- By `step2`, we have `UK = A^(2/K) * LK`.
  have h_UK_LK : ∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c j)^2 = A^(2 / (K : ℝ)) * ∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c (j + 1))^2 := by
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun j hj => _ ; ring_nf;
    simp +zetaDelta at *;
    field_simp;
    rw [ show ( 1 + j : ℝ ) / K = j / K + 1 / K by ring ] ; rw [ Real.rpow_add ( by positivity ) ] ; ring_nf;
    norm_num [ Real.rpow_mul ( by positivity : 0 ≤ A ) ] ; ring;
  obtain ⟨ N₁, hN₁ ⟩ := Metric.tendsto_atTop.mp h_lowS_uppS.1 ( ε / 2 ) ( half_pos hε_pos );
  obtain ⟨ N₂, hN₂ ⟩ := Metric.tendsto_atTop.mp h_lowS_uppS.2 ( ε / 2 ) ( half_pos hε_pos );
  use K, hK_pos, Max.max N₁ ( Max.max N₂ 1 );
  intro x hx; specialize h_sandwich x ( by linarith [ le_max_right N₁ ( max N₂ 1 ), le_max_right N₂ 1 ] ) ; specialize hN₁ x ( by linarith [ le_max_left N₁ ( max N₂ 1 ), le_max_right N₁ ( max N₂ 1 ) ] ) ; specialize hN₂ x ( by linarith [ le_max_left N₁ ( max N₂ 1 ), le_max_left N₂ 1, le_max_right N₁ ( max N₂ 1 ), le_max_right N₂ 1 ] ) ; norm_num [ abs_lt ] at *;
  constructor <;> nlinarith [ abs_lt.mp hN₁, abs_lt.mp hN₂, inv_pos.mpr ( zero_lt_one.trans hA ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hA ) ), Real.one_le_rpow hA.le ( show 0 ≤ 2 / ( K : ℝ ) by positivity ) ]

/-
There is `C₂ > 0` such that for every real `z ≥ 2` and every `N`, the partial
sum of `1/p²` over primes in `(z, N]` is at most `C₂ / (z·log z)`.
-/
lemma primeSq_tail (hpnt : PNT) : ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ z : ℝ, 2 ≤ z → ∀ N : ℕ,
      (∑ p ∈ (Finset.Ioc ⌊z⌋₊ N).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ≤ C₂ / (z * log z) := by
  -- Set `C₂ = 4 * C_π`, where `C_π` is the constant from `pi_upper`.
  obtain ⟨C_π, hC_π_pos, hC_π⟩ := pi_upper hpnt;
  use 4 * C_π;
  constructor;
  · positivity;
  · intro z hz N
    have h_cover : (∑ p ∈ (Finset.Ioc ⌊z⌋₊ N).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ≤ ∑ j ∈ Finset.range (Nat.log 2 N + 1), (∑ p ∈ (Finset.Ioc (⌊2^j * z⌋₊) (⌊2^(j+1) * z⌋₊)).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) := by
      have h_cover : Finset.filter Nat.Prime (Finset.Ioc ⌊z⌋₊ N) ⊆ Finset.biUnion (Finset.range (Nat.log 2 N + 1)) (fun j => Finset.filter Nat.Prime (Finset.Ioc ⌊2^j * z⌋₊ ⌊2^(j+1) * z⌋₊)) := by
        intro p hp; simp_all +decide ;
        -- Let $a$ be the largest integer such that $2^a z < p$.
        obtain ⟨a, ha⟩ : ∃ a : ℕ, 2^a * z < p ∧ p ≤ 2^(a+1) * z := by
          have h_exists_a : ∃ a : ℕ, 2^a * z < p ∧ p ≤ 2^(a+1) * z := by
            have h_exists_a : ∃ a : ℕ, p ≤ 2^a * z := by
              exact ⟨ p, by nlinarith [ show ( p : ℝ ) ≤ 2 ^ p by exact mod_cast Nat.le_of_lt ( Nat.recOn p ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith [ Nat.Prime.one_lt hp.2 ] ) ] ⟩
            contrapose! h_exists_a;
            intro a; induction a <;> simp_all +decide [ pow_succ', mul_assoc ] ;
            exact lt_of_lt_of_le ( Nat.lt_of_floor_lt hp.1.1 ) ( Nat.cast_le.mpr le_rfl );
          exact h_exists_a;
        refine' ⟨ a, _, _, _ ⟩;
        · refine' Nat.le_log_of_pow_le ( by norm_num ) _;
          exact_mod_cast ( by nlinarith [ show ( p : ℝ ) ≤ N by norm_cast; linarith ] : ( 2 : ℝ ) ^ a ≤ N );
        · exact Nat.floor_lt ( by positivity ) |>.2 ha.1;
        · exact Nat.le_floor <| mod_cast ha.2;
      refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_cover fun _ _ _ => by positivity ) _;
      rw [ Finset.sum_biUnion ];
      intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
      contrapose! hij;
      obtain ⟨ a, ha₁, ha₂, ha₃, ha₄, ha₅ ⟩ := hij; exact le_antisymm ( Nat.le_of_not_lt fun hi' => by linarith [ show ⌊2 ^ i * z⌋₊ ≥ ⌊2 ^ ( j + 1 ) * z⌋₊ by exact Nat.floor_mono <| by exact mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ ( by norm_num ) <| by linarith ) <| by positivity ] ) ( Nat.le_of_not_lt fun hj' => by linarith [ show ⌊2 ^ j * z⌋₊ ≥ ⌊2 ^ ( i + 1 ) * z⌋₊ by exact Nat.floor_mono <| by exact mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ ( by norm_num ) <| by linarith ) <| by positivity ] ) ;
    -- For each block `j`, every prime `p` in it satisfies `p > 2^j z` so `1/p² ≤ 1/(2^j z)²`, and the number of primes in it is `≤ π(2^{j+1}z) ≤ C_π·(2^{j+1}z)/log(2^{j+1}z) ≤ C_π·2^{j+1}z/log z` (since `2^{j+1}z ≥ z ≥ 2` and `log` monotone).
    have h_block_bound : ∀ j : ℕ, (∑ p ∈ (Finset.Ioc (⌊2^j * z⌋₊) (⌊2^(j+1) * z⌋₊)).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ≤ (C_π * 2^(j+1) * z / Real.log z) * (1 / (2^j * z)^2) := by
      intro j
      have h_block_card : ((Finset.Ioc (⌊2^j * z⌋₊) (⌊2^(j+1) * z⌋₊)).filter Nat.Prime).card ≤ C_π * 2^(j+1) * z / Real.log z := by
        have h_block_card : ((Finset.Ioc (⌊2^j * z⌋₊) (⌊2^(j+1) * z⌋₊)).filter Nat.Prime).card ≤ Nat.primeCounting ⌊2^(j+1) * z⌋₊ := by
          rw [ Nat.primeCounting ];
          rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
          exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) ] ), Finset.mem_filter.mp hx |>.2 ⟩;
        refine le_trans ( Nat.cast_le.mpr h_block_card ) ?_;
        refine le_trans ( hC_π _ ?_ ) ?_;
        · exact le_trans hz ( le_mul_of_one_le_left ( by positivity ) ( one_le_pow₀ ( by norm_num ) ) );
        · rw [ mul_assoc ];
          gcongr;
          · exact Real.log_pos <| by linarith;
          · exact le_mul_of_one_le_left ( by positivity ) ( one_le_pow₀ ( by norm_num ) );
      refine' le_trans ( Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le _ <| pow_le_pow_left₀ ( by positivity ) ( show ( p : ℝ ) ≥ 2 ^ j * z by exact le_trans ( Nat.lt_floor_add_one _ |> le_of_lt ) <| mod_cast Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) 2 ) _ <;> norm_num [ h_block_card ];
      · positivity;
      · exact mul_le_mul_of_nonneg_right h_block_card <| by positivity;
    -- Summing over `j < J`: `≤ (2C_π/(z log z))·∑_{j<J} 2^{-j} ≤ (2C_π/(z log z))·2 = 4C_π/(z log z) = C₂/(z log z)`.
    have h_sum_bound : ∑ j ∈ Finset.range (Nat.log 2 N + 1), (C_π * 2^(j+1) * z / Real.log z) * (1 / (2^j * z)^2) ≤ (2 * C_π / (z * Real.log z)) * (∑ j ∈ Finset.range (Nat.log 2 N + 1), (1 / 2 : ℝ)^j) := by
      rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun i hi => ?_; ring_nf; norm_num;
      norm_num [ pow_mul', mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_two.trans_le hz ) ];
      norm_num [ ← mul_assoc, ← mul_pow ] ; ring_nf ; norm_num [ show z ≠ 0 by linarith, show z ^ 2 ≠ 0 by positivity ];
      norm_num [ sq, mul_assoc, mul_comm z, ne_of_gt ( zero_lt_two.trans_le hz ) ];
    refine le_trans h_cover <| le_trans ( Finset.sum_le_sum fun _ _ => h_block_bound _ ) <| h_sum_bound.trans ?_;
    rw [ geom_sum_eq ] <;> ring_nf <;> norm_num;
    exact mul_nonneg ( mul_nonneg hC_π_pos.le ( inv_nonneg.mpr ( by positivity ) ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by linarith ) ) )

/-! ### Growth relations

Here `y = n^{1/3}`, `L = log n`, `M = y/L`, `S = M² = n^{2/3}/(log n)²`. -/

/-
`n^{1/3} → ∞`.
-/
lemma tendsto_y_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/3)) atTop atTop := by
  exact tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop

/-
`M = n^{1/3}/log n → ∞`.
-/
lemma tendsto_M_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/3) / Real.log n) atTop atTop := by
  -- Let $y = \log n$, therefore the expression becomes $\frac{e^{y/3}}{y}$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (y / 3) / y) Filter.atTop Filter.atTop by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
  -- Let $z = \frac{y}{3}$, therefore the expression becomes $\frac{e^z}{3z}$.
  suffices h_z : Filter.Tendsto (fun z : ℝ => Real.exp z / (3 * z)) Filter.atTop Filter.atTop by
    convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 3⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
  ring_nf;
  exact Filter.Tendsto.atTop_mul_const ( by norm_num )
    (by simpa [div_eq_mul_inv] using Real.tendsto_exp_div_pow_atTop 1)

/-
`M / S → 0`, i.e. `M = o(S)`.
-/
lemma M_div_S_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ ((1:ℝ)/3) / Real.log n) / S n) atTop (𝓝 0) := by
  -- Simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun n : ℕ => (Real.log n) / (n : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop (nhds 0) by
    refine h_simp.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
    unfold S; ring_nf;
    norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos, show n > 1 from hn ];
    norm_num [ ← mul_assoc, ← Real.rpow_neg ( Nat.cast_nonneg _ ), ← Real.rpow_add ( Nat.cast_pos.mpr hn.le ) ];
  -- Let $y = \log n$, therefore the expression becomes $\frac{y}{e^{y/3}}$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y / 3)) Filter.atTop (nhds 0) by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
  -- Let $z = \frac{y}{3}$, therefore the expression becomes $\frac{3z}{e^z}$.
  suffices h_z : Filter.Tendsto (fun z : ℝ => 3 * z / Real.exp z) Filter.atTop (nhds 0) by
    convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 3⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
  simpa [Real.exp_neg, div_eq_mul_inv, mul_assoc] using
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (3 : ℝ)

/-
`n^{3/5} / S → 0`, i.e. `n^{3/5} = o(S)`.
-/
lemma n35_div_S_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((3:ℝ)/5) / S n) atTop (𝓝 0) := by
  unfold S; ring_nf; norm_num;
  -- Simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 5 - 2 / 3 : ℝ) * (Real.log n) ^ 2) Filter.atTop (nhds 0) by
    refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ ← Real.rpow_neg ( by positivity ), ← Real.rpow_add ( by positivity ) ] ; ring_nf );
  -- Let $y = \log n$, therefore the expression becomes $\frac{y^2}{e^{y/15}}$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => y^2 * Real.exp (-y / 15)) Filter.atTop (nhds 0) by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
  -- Let $z = \frac{y}{15}$, therefore the expression becomes $\frac{(15z)^2}{e^z} = \frac{225z^2}{e^z}$.
  suffices h_z : Filter.Tendsto (fun z : ℝ => 225 * z^2 * Real.exp (-z)) Filter.atTop (nhds 0) by
    convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 15⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
  simpa [ mul_assoc ] using Filter.Tendsto.const_mul 225 ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 )

/-! ## The multiplicative basis -/

/-- `B₀ = {m : 1 ≤ m ≤ n^{3/5}}`. -/
noncomputable def B0 (n : ℕ) : Finset ℕ := Finset.Icc 1 ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊

/-- `B₁ = {p prime : n^{3/5} < p ≤ n}`. -/
noncomputable def B1 (n : ℕ) : Finset ℕ :=
  (Finset.Ioc ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊ n).filter Nat.Prime

/-- `B₂ = {p·q : p, q prime, p ≤ y, q ≤ y}`, where `y = n^{1/3}`. -/
noncomputable def B2 (n : ℕ) : Finset ℕ :=
  (((Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime) ×ˢ
   ((Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime)).image (fun pq => pq.1 * pq.2)

/-- `B₃ = {q·r : q, r prime, y < q ≤ n^{2/5}, r ≤ n/q²}`. -/
noncomputable def B3 (n : ℕ) : Finset ℕ :=
  ((Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊).filter Nat.Prime).biUnion
    (fun q => ((Finset.Icc 1 (n / (q * q))).filter Nat.Prime).image (fun r => q * r))

/-- The full basis `B = B₀ ∪ B₁ ∪ B₂ ∪ B₃`. -/
noncomputable def Bset (n : ℕ) : Finset ℕ := B0 n ∪ B1 n ∪ B2 n ∪ B3 n

/-
If a product of factors bounded by `U` carries `D` from below `T` to above `T`,
some partial product lands in `[T, T·U]`.
-/
lemma threshold_crossing (D T U : ℝ) (s : ℕ → ℝ) (k : ℕ)
    (hT : 0 < T) (hU : 0 < U) (hD : 0 < D) (hDT : D ≤ T)
    (hs : ∀ j < k, 0 < s j ∧ s j ≤ U)
    (hprod : T < D * ∏ j ∈ Finset.range k, s j) :
    ∃ r ≤ k, T ≤ D * ∏ j ∈ Finset.range r, s j ∧
      D * ∏ j ∈ Finset.range r, s j ≤ T * U := by
  induction' k with k ih generalizing D T U s <;> norm_num [ Finset.prod_range_succ ] at *;
  · linarith;
  · by_cases h : T < D * ∏ j ∈ Finset.range k, s j;
    · obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := ih D T U s hT hU hD hDT ( fun j hj => hs j ( Nat.le_of_lt hj ) ) h; exact ⟨ r, Nat.le_succ_of_le hr₁, hr₂, hr₃ ⟩ ;
    · refine' ⟨ k + 1, _, _, _ ⟩ <;> norm_num [ Finset.prod_range_succ ];
      · linarith;
      · nlinarith [ hs k le_rfl, show 0 ≤ D * ∏ j ∈ Finset.range k, s j from mul_nonneg hD.le <| Finset.prod_nonneg fun _ _ => le_of_lt <| hs _ ( Finset.mem_range_le ‹_› ) |>.1 ]

/-
Every `m ≤ X` factors as `m = u·v` with `v ≤ X^{2/3}` and `u` prime or
`u ≤ X^{2/3}`.
-/
lemma balanced_factorization (X : ℝ) (hX : 1 ≤ X) (m : ℕ) (hm : 1 ≤ m)
    (hmX : (m : ℝ) ≤ X) :
    ∃ u v : ℕ, 1 ≤ u ∧ 1 ≤ v ∧ m = u * v ∧ (v : ℝ) ≤ X ^ ((2:ℝ)/3) ∧
      (Nat.Prime u ∨ (u : ℝ) ≤ X ^ ((2:ℝ)/3)) := by
  simp +zetaDelta at *;
  by_cases h_case : (m : ℝ) ≤ X ^ (2 / 3 : ℝ);
  · use m, hm, 1, by norm_num;
    exact ⟨ by norm_num, by exact le_trans ( by norm_num ) ( Real.one_le_rpow hX ( by norm_num ) ), Or.inr h_case ⟩;
  · -- Case 2: $m > X^{2/3}$. Two subcases.
    by_cases h_prime : ∃ p : ℕ, Nat.Prime p ∧ p ∣ m ∧ (p : ℝ) > X ^ (1 / 3 : ℝ);
    · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h_prime;
      refine' ⟨ p, hp₁.pos, m / p, Nat.div_pos ( Nat.le_of_dvd hm hp₂ ) hp₁.pos, _, _, _ ⟩;
      · rw [ Nat.mul_div_cancel' hp₂ ];
      · rw [ Nat.cast_div ( by assumption ) ( by aesop ) ];
        rw [ div_le_iff₀ ( Nat.cast_pos.mpr hp₁.pos ) ];
        refine' le_trans hmX _;
        exact le_trans ( by rw [ ← Real.rpow_add ( by positivity ) ] ; norm_num ) ( mul_le_mul_of_nonneg_left hp₃.le ( by positivity ) );
      · exact Or.inl hp₁;
    · -- Every prime divisor of $m$ is $\leq X^{1/3}$. List the prime factors of $m$ with multiplicity and multiply them in order until the running product first exceeds $X^{1/3}$; let $u$ be that running product (it exists since $m > X^{2/3} \geq X^{1/3}$).
      obtain ⟨u, hu⟩ : ∃ u : ℕ, 1 ≤ u ∧ u ∣ m ∧ (u : ℝ) > X ^ (1 / 3 : ℝ) ∧ ∀ v : ℕ, 1 ≤ v → v ∣ m → v < u → (v : ℝ) ≤ X ^ (1 / 3 : ℝ) := by
        have h_exists_u : ∃ u : ℕ, 1 ≤ u ∧ u ∣ m ∧ (u : ℝ) > X ^ (1 / 3 : ℝ) := by
          use m;
          exact ⟨ hm, dvd_rfl, lt_of_le_of_lt ( Real.rpow_le_rpow_of_exponent_le hX ( show ( 1 : ℝ ) / 3 ≤ 2 / 3 by norm_num ) ) ( not_le.mp h_case ) ⟩;
        exact ⟨ Nat.find h_exists_u, Nat.find_spec h_exists_u |>.1, Nat.find_spec h_exists_u |>.2.1, Nat.find_spec h_exists_u |>.2.2, fun v hv₁ hv₂ hv₃ => not_lt.1 fun hv₄ => Nat.find_min h_exists_u hv₃ ⟨ hv₁, hv₂, hv₄ ⟩ ⟩;
      -- Since $u$ is the smallest divisor of $m$ greater than $X^{1/3}$, we have $u \leq X^{2/3}$.
      have hu_le : (u : ℝ) ≤ X ^ (2 / 3 : ℝ) := by
        -- Since $u$ is the smallest divisor of $m$ greater than $X^{1/3}$, we have $u = p \cdot v$ for some prime $p$ and divisor $v$ of $m$.
        obtain ⟨p, v, hp, hv, huv⟩ : ∃ p v : ℕ, Nat.Prime p ∧ v ∣ m ∧ u = p * v := by
          obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ u := by
            exact Nat.exists_prime_and_dvd ( by rintro rfl; exact absurd hu.2.2.1 ( by norm_num; linarith [ Real.one_le_rpow hX ( by norm_num : ( 0 : ℝ ) ≤ 1 / 3 ) ] ) );
          exact ⟨ p, u / p, hp.1, Nat.dvd_trans ( Nat.div_dvd_of_dvd hp.2 ) hu.2.1, by rw [ Nat.mul_div_cancel' hp.2 ] ⟩;
        by_cases hv1 : v = 0 <;> simp_all +decide;
        have := hu.2.2.2 v ( Nat.pos_of_dvd_of_pos hv hm ) hv ( by nlinarith [ hp.two_le, Nat.pos_of_ne_zero hv1 ] ) ; norm_num at * ; rw [ show ( 2 / 3 : ℝ ) = 1 / 3 + 1 / 3 by norm_num, Real.rpow_add ] <;> norm_num <;> nlinarith [ h_prime p hp ( dvd_of_mul_right_dvd hu.2.1 ), Real.rpow_pos_of_pos ( zero_lt_one.trans_le hX ) ( 1 / 3 : ℝ ) ] ;
      refine' ⟨ u, hu.1, m / u, _, _, _, _ ⟩ <;> norm_num at *;
      · exact Nat.div_pos ( Nat.le_of_dvd hm hu.2.1 ) hu.1;
      · rw [ Nat.mul_div_cancel' hu.2.1 ];
      · rw [ Nat.cast_div ( hu.2.1 ) ( by norm_cast; linarith ) ];
        rw [ div_le_iff₀ ] <;> nlinarith [ show ( u : ℝ ) ≥ 1 by exact_mod_cast hu.1, show ( m : ℝ ) ≤ X by exact_mod_cast hmX, show ( X : ℝ ) ^ ( 1 / 3 : ℝ ) > 0 by positivity, show ( X : ℝ ) ^ ( 2 / 3 : ℝ ) > 0 by positivity, show ( X : ℝ ) ^ ( 1 / 3 : ℝ ) * ( X : ℝ ) ^ ( 2 / 3 : ℝ ) = X by rw [ ← Real.rpow_add ( by positivity ) ] ; norm_num ];
      · exact Or.inr hu_le

/-- Product over `range r` of `(l[j]?.getD 1 : ℝ)` equals the product of the
first `r` entries of `l` (cast to `ℝ`). -/
lemma prod_range_getD_take (l : List ℕ) (r : ℕ) :
    ∏ j ∈ Finset.range r, ((l[j]?.getD 1 : ℕ) : ℝ) = ((l.take r).prod : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_range_succ, ih, List.take_add_one, List.prod_append]
    push_cast
    by_cases hr : r < l.length
    · rw [List.getElem?_eq_getElem hr]; simp
    · rw [List.getElem?_eq_none (by omega)]; simp

/-
If at least three prime factors of `m` (counted with multiplicity) exceed
`n^{1/5}`, then there are three primes `p ≥ q ≥ r > n^{1/5}` with `p*q*r ∣ m`.
-/
set_option linter.unusedTactic false in
lemma exists_three_large_factors (n m : ℕ) (hm1 : 1 ≤ m)
    (hcount : 3 ≤ ((Nat.primeFactorsList m).filter
      (fun p => (n:ℝ) ^ ((1:ℝ)/5) < (p:ℝ))).length) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      r ≤ q ∧ q ≤ p ∧ (n:ℝ) ^ ((1:ℝ)/5) < (r:ℝ) ∧ p * q * r ∣ m := by
  -- Let `L = Nat.primeFactorsList m` and `F = L.filter (fun p => (n:ℝ)^{1/5} < (p:ℝ))`, with `3 ≤ F.length`.
  set L := m.primeFactorsList
  set F := L.filter (fun p => (n : ℝ) ^ (1 / 5 : ℝ) < p);
  obtain ⟨l, hl⟩ : ∃ l : List ℕ, l.Sublist L ∧ l.length = 3 ∧ (∀ p ∈ l, (n : ℝ) ^ (1 / 5 : ℝ) < p) ∧ (∀ p ∈ l, Nat.Prime p) := by
    have hF_sublist : ∃ l : List ℕ, l.Sublist L ∧ l.length = F.length ∧ (∀ p ∈ l, (n : ℝ) ^ (1 / 5 : ℝ) < p) ∧ (∀ p ∈ l, Nat.Prime p) := by
      have hF_sublist : ∀ {l : List ℕ}, (∀ p ∈ l, Nat.Prime p) → ∃ l' : List ℕ, l'.Sublist l ∧ l'.length = (List.filter (fun p => (n : ℝ) ^ (1 / 5 : ℝ) < p) l).length ∧ (∀ p ∈ l', (n : ℝ) ^ (1 / 5 : ℝ) < p) ∧ (∀ p ∈ l', Nat.Prime p) := by
        intros l hl_prime; induction' l with p l ih;
        · exact ⟨ [ ], by norm_num ⟩;
        · by_cases h : ( n : ℝ ) ^ ( 1 / 5 : ℝ ) < p <;> simp_all +decide;
          · obtain ⟨ l', hl₁, hl₂, hl₃, hl₄ ⟩ := ih; use p :: l'; aesop;
          · exact ⟨ ih.choose, List.Sublist.trans ih.choose_spec.1 ( List.sublist_cons_self _ _ ), ih.choose_spec.2.1, ih.choose_spec.2.2.1, ih.choose_spec.2.2.2 ⟩;
      exact hF_sublist fun p hp => Nat.prime_of_mem_primeFactorsList hp;
    obtain ⟨ l, hl₁, hl₂, hl₃, hl₄ ⟩ := hF_sublist;
    use l.take 3;
    exact ⟨ List.Sublist.trans ( List.take_sublist _ _ ) hl₁, by rw [ List.length_take, hl₂ ] ; omega, fun p hp => hl₃ p <| List.mem_of_mem_take hp, fun p hp => hl₄ p <| List.mem_of_mem_take hp ⟩;
  -- Since `l` is a sublist of `L`, `l.prod ∣ L.prod = m` (product over a sublist divides product over the whole list; use `Nat.prod_primeFactorsList` for `L.prod = m`, `m ≠ 0` from `1 ≤ m`).
  have h_div : l.prod ∣ m := by
    convert Nat.dvd_trans ( hl.1.prod_dvd_prod ) ( Nat.prod_primeFactorsList ( by positivity ) |> fun x => x.dvd ) using 1;
  rcases l with ( _ | ⟨ p, _ | ⟨ q, _ | ⟨ r, _ | l ⟩ ⟩ ⟩ ) <;> simp_all +decide;
  cases le_total p q <;> cases le_total q r <;> cases le_total r p <;> first | exact ⟨ p, hl.2.2.1, q, hl.2.2.2.1, r, hl.2.2.2.2, by linarith, by linarith, by linarith, by simpa only [ mul_assoc ] using h_div ⟩ | skip;
  · exact ⟨ r, hl.2.2.2.2, q, hl.2.2.2.1, p, hl.2.2.1, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩;
  · exact ⟨ q, hl.2.2.2.1, p, hl.2.2.1, r, hl.2.2.2.2, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩;
  · exact ⟨ q, hl.2.2.2.1, r, hl.2.2.2.2, p, hl.2.2.1, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩;
  · exact ⟨ p, hl.2.2.1, r, hl.2.2.2.2, q, hl.2.2.2.1, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩;
  · exact ⟨ r, hl.2.2.2.2, p, hl.2.2.1, q, hl.2.2.2.1, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩

/-- If `m ∈ (n^{9/10}, n]` has all prime factors `≤ n^{2/5}` and at most two
  prime factors (with multiplicity) exceeding `n^{1/5}`, then `m` has a divisor
  `u` with `n^{2/5} ≤ u ≤ n^{3/5}`. -/
lemma exists_mid_divisor (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm1 : 1 ≤ m)
    (hm9 : (n:ℝ) ^ ((9:ℝ)/10) < (m:ℝ))
    (hbig : ∀ p, Nat.Prime p → p ∣ m → (p:ℝ) ≤ (n:ℝ) ^ ((2:ℝ)/5))
    (hcount : ((Nat.primeFactorsList m).filter
      (fun p => (n:ℝ) ^ ((1:ℝ)/5) < (p:ℝ))).length ≤ 2) :
    ∃ u : ℕ, u ∣ m ∧ (n:ℝ) ^ ((2:ℝ)/5) ≤ (u:ℝ) ∧ (u:ℝ) ≤ (n:ℝ) ^ ((3:ℝ)/5) := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hcount' : (m.primeFactorsList.filter (fun (a:ℕ) => decide ((n:ℝ)^((1:ℝ)/5) < (a:ℝ)))).length ≤ 2 := by
    have heq : (m.primeFactorsList.filter (fun (a:ℕ) => decide ((n:ℝ)^((1:ℝ)/5) < (a:ℝ)))).length
        = ((Nat.primeFactorsList m).filter (fun p => (n:ℝ) ^ ((1:ℝ)/5) < (p:ℝ))).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      simp only [bind_pure_comp]
      rw [show (Nat.cast <$> m.primeFactorsList : List ℝ) = m.primeFactorsList.map (Nat.cast : ℕ → ℝ) from rfl,
          List.countP_map]
      rfl
    rw [heq]; exact hcount
  obtain ⟨Lbig, Lsmall, hL⟩ : ∃ Lbig Lsmall : List ℕ,
      m.primeFactorsList.Perm (Lbig ++ Lsmall) ∧
      (∀ p ∈ Lbig, Nat.Prime p ∧ (n : ℝ) ^ ((1:ℝ)/5) < (p:ℝ)) ∧
      (∀ p ∈ Lsmall, Nat.Prime p ∧ (p:ℝ) ≤ (n : ℝ) ^ ((1:ℝ)/5)) ∧ Lbig.length ≤ 2 := by
    refine ⟨m.primeFactorsList.filter (fun (a:ℕ) => decide ((n:ℝ)^((1:ℝ)/5) < (a:ℝ))),
            m.primeFactorsList.filter (fun (a:ℕ) => !decide ((n:ℝ)^((1:ℝ)/5) < (a:ℝ))),
            (List.filter_append_perm _ _).symm, ?_, ?_, hcount'⟩
    · intro p hp; rw [List.mem_filter] at hp
      exact ⟨Nat.prime_of_mem_primeFactorsList hp.1, by simpa using hp.2⟩
    · intro p hp; rw [List.mem_filter] at hp
      exact ⟨Nat.prime_of_mem_primeFactorsList hp.1, not_lt.1 (by simpa using hp.2)⟩
  have hprodm : (Lbig ++ Lsmall).prod = m := by
    rw [← hL.1.prod_eq, Nat.prod_primeFactorsList hm0]
  obtain ⟨D0, hD0⟩ : ∃ D0 : ℕ, (D0:ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5) ∧ D0 ∣ m ∧
      (n : ℝ) ^ ((2 : ℝ) / 5) < (D0 : ℝ) * (Lsmall.prod : ℝ) ∧ D0 * Lsmall.prod ∣ m := by
    by_cases hLbig : Lbig.length ≤ 1
    · refine ⟨Lbig.prod, ?_, ?_, ?_, ?_⟩
      · rcases Lbig with (_ | ⟨p, _ | ⟨q, Lb⟩⟩)
        · simpa using Real.one_le_rpow hn1 (by norm_num)
        · have hpmem : p ∈ Nat.primeFactorsList m := hL.1.symm.subset (by simp)
          simpa using hbig p (hL.2.1 p (by simp)).1 (Nat.dvd_of_mem_primeFactorsList hpmem)
        · simp only [List.length_cons] at hLbig; omega
      · have : Lbig.prod ∣ (Lbig ++ Lsmall).prod := ⟨Lsmall.prod, by rw [List.prod_append]⟩
        rw [hprodm] at this; exact this
      · have hpr : (Lbig.prod : ℝ) * (Lsmall.prod : ℝ) = m := by
          rw [← hprodm, List.prod_append]; push_cast; ring
        rw [hpr]
        exact hm9.trans_le' (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
      · exact ⟨1, by rw [← hprodm, List.prod_append]; ring⟩
    · obtain ⟨q, p, rfl⟩ : ∃ q p : ℕ, Lbig = [q, p] := by
        rcases Lbig with (_ | ⟨a, _ | ⟨b, Lb⟩⟩)
        · exact (hLbig (by simp)).elim
        · exact (hLbig (by simp)).elim
        · have hlb : Lb.length = 0 := by have := hL.2.2.2; simp only [List.length_cons] at this; omega
          rw [List.eq_nil_of_length_eq_zero hlb]; exact ⟨a, b, rfl⟩
      have hqmem : q ∈ Nat.primeFactorsList m := hL.1.symm.subset (by simp)
      have hpmem : p ∈ Nat.primeFactorsList m := hL.1.symm.subset (by simp)
      have hqprime : Nat.Prime q := (hL.2.1 q (by simp)).1
      have hmeq : q * (p * Lsmall.prod) = m := by
        rw [← hprodm]; simp [List.prod_cons]
      refine ⟨p, ?_, ?_, ?_, ?_⟩
      · exact hbig p (hL.2.1 p (by simp)).1 (Nat.dvd_of_mem_primeFactorsList hpmem)
      · exact Nat.dvd_of_mem_primeFactorsList hpmem
      · have hpr : (q : ℝ) * ((p : ℝ) * (Lsmall.prod : ℝ)) = m := by exact_mod_cast hmeq
        have hq2 : (q:ℝ) ≤ (n:ℝ)^((2:ℝ)/5) := hbig q hqprime (Nat.dvd_of_mem_primeFactorsList hqmem)
        have hpL0 : (0:ℝ) ≤ (p:ℝ) * Lsmall.prod := by positivity
        have hid : (n:ℝ)^((2:ℝ)/5) * (n:ℝ)^((1:ℝ)/2) = (n:ℝ)^((9:ℝ)/10) := by
          rw [← Real.rpow_add hnpos]; norm_num
        have hlt : (n:ℝ)^((2:ℝ)/5) < (n:ℝ)^((1:ℝ)/2) :=
          (Real.rpow_lt_rpow_left_iff (by exact_mod_cast hn)).2 (by norm_num)
        have hn25 : (0:ℝ) < (n:ℝ)^((2:ℝ)/5) := Real.rpow_pos_of_pos hnpos _
        have key : (n:ℝ)^((2:ℝ)/5) * (n:ℝ)^((1:ℝ)/2) < (n:ℝ)^((2:ℝ)/5) * ((p:ℝ)*Lsmall.prod) := by
          calc (n:ℝ)^((2:ℝ)/5) * (n:ℝ)^((1:ℝ)/2) = (n:ℝ)^((9:ℝ)/10) := hid
            _ < m := hm9
            _ = (q:ℝ) * ((p:ℝ)*Lsmall.prod) := hpr.symm
            _ ≤ (n:ℝ)^((2:ℝ)/5) * ((p:ℝ)*Lsmall.prod) := mul_le_mul_of_nonneg_right hq2 hpL0
        have hpLgt : (n:ℝ)^((1:ℝ)/2) < (p:ℝ)*Lsmall.prod := lt_of_mul_lt_mul_left key (le_of_lt hn25)
        linarith [hlt, hpLgt]
      · exact ⟨q, by rw [← hmeq]; ring⟩
  obtain ⟨r, hr_le, hr1, hr2⟩ := threshold_crossing (D0 : ℝ) ((n:ℝ)^((2:ℝ)/5)) ((n:ℝ)^((1:ℝ)/5))
      (fun j => ((Lsmall[j]?.getD 1 : ℕ) : ℝ)) Lsmall.length
      (Real.rpow_pos_of_pos hnpos _) (Real.rpow_pos_of_pos hnpos _)
      (by exact_mod_cast Nat.pos_of_dvd_of_pos hD0.2.1 hm1) hD0.1
      (by
        intro j hj
        have hmem : Lsmall[j]?.getD 1 ∈ Lsmall := by
          rw [List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
        refine ⟨?_, ?_⟩
        · exact_mod_cast (hL.2.2.1 _ hmem).1.pos
        · exact (hL.2.2.1 _ hmem).2)
      (by rw [prod_range_getD_take, List.take_length]; exact hD0.2.2.1)
  rw [prod_range_getD_take] at hr1 hr2
  refine ⟨D0 * (Lsmall.take r).prod, ?_, ?_, ?_⟩
  · exact dvd_trans (mul_dvd_mul_left D0
      (by rw [← List.prod_take_mul_prod_drop Lsmall r]; exact dvd_mul_right _ _)) hD0.2.2.2
  · rw [Nat.cast_mul]; exact hr1
  · rw [Nat.cast_mul]
    calc ((D0:ℝ) * ((Lsmall.take r).prod : ℝ)) ≤ (n:ℝ)^((2:ℝ)/5) * (n:ℝ)^((1:ℝ)/5) := hr2
      _ = (n:ℝ)^((3:ℝ)/5) := by rw [← Real.rpow_add hnpos]; norm_num

/-- For every `n ≥ 2`, `B` is a two-factor basis for `[n]`. -/
lemma multiplicative_basis (n : ℕ) (hn : 2 ≤ n) : TwoFactorBasis (Bset n) n := by
  classical
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn35pos : (0:ℝ) < (n:ℝ)^((3:ℝ)/5) := Real.rpow_pos_of_pos hnpos _
  have hid : (n:ℝ)^((3:ℝ)/5) * (n:ℝ)^((2:ℝ)/5) = n := by
    rw [← Real.rpow_add hnpos]; norm_num
  have inB0 : ∀ x : ℕ, 1 ≤ x → (x:ℝ) ≤ (n:ℝ)^((3:ℝ)/5) → x ∈ Bset n := by
    intro x hx1 hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_Icc.mpr ⟨hx1, Nat.le_floor hx⟩)))
  have inB1 : ∀ x : ℕ, Nat.Prime x → (n:ℝ)^((3:ℝ)/5) < (x:ℝ) → x ≤ n → x ∈ Bset n := by
    intro x hxp hx hxn
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨(Nat.floor_lt (by positivity)).2 hx, hxn⟩, hxp⟩
  intro m hm
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm1, hmn⟩ := hm
  have hm0 : m ≠ 0 := by omega
  have hmR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  have quot_le : ∀ d : ℕ, 0 < d → (n:ℝ)^((2:ℝ)/5) ≤ (d:ℝ) → ((m/d:ℕ):ℝ) ≤ (n:ℝ)^((3:ℝ)/5) := by
    intro d hd hdge
    have hdpos : (0:ℝ) < d := by exact_mod_cast hd
    calc ((m/d:ℕ):ℝ) ≤ (m:ℝ)/(d:ℝ) := Nat.cast_div_le
      _ ≤ (n:ℝ)^((3:ℝ)/5) := by
          rw [div_le_iff₀ hdpos]
          nlinarith [hmR, hid, mul_le_mul_of_nonneg_left hdge (le_of_lt hn35pos)]
  by_cases hsmall : (m:ℝ) ≤ (n:ℝ)^((9:ℝ)/10)
  · obtain ⟨u, v, hu1, hv1, huv, hvle, hudisj⟩ :=
      balanced_factorization ((n:ℝ)^((9:ℝ)/10)) (Real.one_le_rpow hn1 (by norm_num)) m hm1 hsmall
    have hexp : ((n:ℝ)^((9:ℝ)/10))^((2:ℝ)/3) = (n:ℝ)^((3:ℝ)/5) := by
      rw [← Real.rpow_mul hnpos.le]; norm_num
    have hvB0 : v ∈ Bset n := inB0 v hv1 (by rw [← hexp]; exact hvle)
    refine ⟨u, ?_, v, hvB0, huv⟩
    rcases hudisj with hup | hule
    · have hun : u ≤ n := le_trans (Nat.le_mul_of_pos_right u (by omega)) (huv ▸ hmn)
      by_cases hule : (u:ℝ) ≤ (n:ℝ)^((3:ℝ)/5)
      · exact inB0 u hu1 hule
      · exact inB1 u hup (not_le.mp hule) hun
    · exact inB0 u hu1 (by rw [← hexp]; exact hule)
  · push Not at hsmall
    by_cases hlp : ∃ p, Nat.Prime p ∧ p ∣ m ∧ (n:ℝ)^((2:ℝ)/5) < (p:ℝ)
    · obtain ⟨p, hpp, hpd, hpbig⟩ := hlp
      have hpn : p ≤ n := le_trans (Nat.le_of_dvd (by omega) hpd) hmn
      refine ⟨p, ?_, m / p, ?_, (Nat.mul_div_cancel' hpd).symm⟩
      · by_cases hple : (p:ℝ) ≤ (n:ℝ)^((3:ℝ)/5)
        · exact inB0 p hpp.pos hple
        · exact inB1 p hpp (not_le.mp hple) hpn
      · exact inB0 (m/p) (Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hpp.pos)
          (quot_le p hpp.pos hpbig.le)
    · push Not at hlp
      by_cases hk : ((Nat.primeFactorsList m).filter (fun p => (n:ℝ)^((1:ℝ)/5) < (p:ℝ))).length ≤ 2
      · obtain ⟨u, hud, hu2, hu3⟩ := exists_mid_divisor n hn m hm1 hsmall hlp hk
        have hupos : 0 < u := Nat.pos_of_dvd_of_pos hud (by omega)
        refine ⟨u, inB0 u hupos hu3, m / u, ?_, (Nat.mul_div_cancel' hud).symm⟩
        exact inB0 (m/u) (Nat.div_pos (Nat.le_of_dvd (by omega) hud) hupos) (quot_le u hupos hu2)
      · have hk3 : 3 ≤ ((Nat.primeFactorsList m).filter (fun p => (n:ℝ)^((1:ℝ)/5) < (p:ℝ))).length := by
          rw [not_le] at hk; omega
        obtain ⟨p, q, r, hpp, hqp, hrp, hrq, hqp', hrbig, hdvd⟩ :=
          exists_three_large_factors n m hm1 hk3
        have hn15pos : (0:ℝ) < (n:ℝ)^((1:ℝ)/5) := Real.rpow_pos_of_pos hnpos _
        have hqbig : (n:ℝ)^((1:ℝ)/5) < (q:ℝ) := lt_of_lt_of_le hrbig (by exact_mod_cast hrq)
        have hn15sq : (n:ℝ)^((1:ℝ)/5) * (n:ℝ)^((1:ℝ)/5) = (n:ℝ)^((2:ℝ)/5) := by
          rw [← Real.rpow_add hnpos]; norm_num
        have hqr_dvd : q * r ∣ m := dvd_trans ⟨p, by ring⟩ hdvd
        have hqrge : (n:ℝ)^((2:ℝ)/5) ≤ ((q*r:ℕ):ℝ) := by
          push_cast; nlinarith [hqbig, hrbig, hn15pos, hn15sq]
        have hqrpos : 0 < q * r := Nat.mul_pos hqp.pos hrp.pos
        have hvB0 : m / (q*r) ∈ Bset n := inB0 (m/(q*r))
          (Nat.div_pos (Nat.le_of_dvd (by omega) hqr_dvd) hqrpos) (quot_le (q*r) hqrpos hqrge)
        refine ⟨q * r, ?_, m / (q*r), hvB0, (Nat.mul_div_cancel' hqr_dvd).symm⟩
        by_cases hqy : (q:ℝ) ≤ (n:ℝ)^((1:ℝ)/3)
        · have hry : (r:ℝ) ≤ (n:ℝ)^((1:ℝ)/3) := le_trans (by exact_mod_cast hrq) hqy
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          refine Finset.mem_image.mpr ⟨(q, r), ?_, rfl⟩
          rw [Finset.mem_product]
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqp.pos, Nat.le_floor hqy⟩, hqp⟩,
                 Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrp.pos, Nat.le_floor hry⟩, hrp⟩⟩
        · have hq_dvd : q ∣ m := dvd_trans ⟨p * r, by ring⟩ hdvd
          have hq25 : (q:ℝ) ≤ (n:ℝ)^((2:ℝ)/5) := hlp q hqp hq_dvd
          have hpqrn : p * q * r ≤ n := le_trans (Nat.le_of_dvd (by omega) hdvd) hmn
          have hqqr : q * q * r ≤ n :=
            le_trans (mul_le_mul_left (mul_le_mul_left hqp' q) r) hpqrn
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, Nat.le_floor hq25⟩, hqp⟩
            exact (Nat.floor_lt (by positivity)).2 (not_le.mp hqy)
          · refine Finset.mem_image.mpr ⟨r, ?_, rfl⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrp.pos, ?_⟩, hrp⟩
            rw [Nat.le_div_iff_mul_le (Nat.mul_pos hqp.pos hqp.pos)]
            calc r * (q * q) = q * q * r := by ring
              _ ≤ n := hqqr

/-- Consequently `F n ≤ |B|`. -/
lemma F_le_Bset_card (n : ℕ) (hn : 2 ≤ n) : F n ≤ (Bset n).card :=
  F_le_basis_card (Bset n) n (multiplicative_basis n hn)

/-! ## Cardinalities of the basis classes -/

/-
The number of primes in `[1, m]` equals `π(m)`.
-/
lemma card_primes_Icc (m : ℕ) :
    ((Finset.Icc 1 m).filter Nat.Prime).card = Nat.primeCounting m := by
  rw [ Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
  congr 1 with ( _ | x ) <;> simp +arith +decide

/-
`|B₀| = ⌊n^{3/5}⌋`.
-/
lemma card_B0 (n : ℕ) : (B0 n).card = ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊ := by
  unfold B0; aesop;

/-
`|B₂| = π(y)(π(y)+1)/2`, where `y = n^{1/3}`.
-/
lemma card_B2 (n : ℕ) :
    (B2 n).card =
      Nat.primeCounting ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ *
        (Nat.primeCounting ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ + 1) / 2 := by
  rw [ ← card_primes_Icc ];
  rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
  unfold Erdos793.B2;
  have h_card : Finset.card (Finset.image (fun pq => pq.1 * pq.2) (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊) ×ˢ Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊))) = Finset.card (Finset.powersetCard 2 (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊))) + Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊)) := by
    have h_card : Finset.image (fun pq : ℕ × ℕ => pq.1 * pq.2) (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n : ℝ) ^ ((1:ℝ)/3)⌋₊) ×ˢ Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n : ℝ) ^ ((1:ℝ)/3)⌋₊)) = Finset.image (fun s : Finset ℕ => s.prod id) (Finset.powersetCard 2 (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n : ℝ) ^ ((1:ℝ)/3)⌋₊))) ∪ Finset.image (fun p : ℕ => p * p) (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n : ℝ) ^ ((1:ℝ)/3)⌋₊)) := by
      ext; simp [Finset.mem_image];
      constructor;
      · rintro ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, ⟨ ⟨ hb₁, hb₂ ⟩, hb₃ ⟩ ⟩, rfl ⟩;
        by_cases hab : a = b;
        · exact Or.inr ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, by rw [ hab ] ⟩;
        · exact Or.inl ⟨ { a, b }, ⟨ by aesop_cat, by aesop_cat ⟩, by rw [ Finset.prod_pair hab ] ⟩;
      · rintro ( ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ | ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, rfl ⟩ );
        · rw [ Finset.card_eq_two ] at ha₂; obtain ⟨ x, y, hxy ⟩ := ha₂; use x, y; simp_all +decide [ Finset.subset_iff ] ;
        · exact ⟨ a, a, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ ⟩, rfl ⟩;
    rw [ h_card, Finset.card_union_of_disjoint ];
    · rw [ Finset.card_image_of_injOn, Finset.card_image_of_injOn ];
      · exact fun x hx y hy hxy => by nlinarith;
      · intro x hx y hy; simp_all +decide [ Finset.mem_powersetCard ] ;
        intro hxy; have := Finset.card_eq_two.mp hx.2; have := Finset.card_eq_two.mp hy.2; obtain ⟨ a, b, ha, hb, hab ⟩ := this; obtain ⟨ c, d, hc, hd, hcd ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
        -- Since $c$ and $d$ are primes and $c * d = a * b$, it follows that $\{c, d\} = \{a, b\}$.
        have h_eq : c ∣ a ∨ c ∣ b := by
          exact hx.1.2.dvd_mul.mp ( hxy ▸ dvd_mul_right _ _ );
        rcases h_eq with ( h | h ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
        · aesop;
        · rw [ mul_comm ] at hxy ; aesop;
    · norm_num [ Finset.disjoint_right ];
      rintro a x hx₁ hx₂ hx₃ rfl y hy₁ hy₂; rw [ Finset.card_eq_two ] at hy₂; obtain ⟨ p, q, hpq ⟩ := hy₂; simp_all +decide [ Finset.subset_iff ] ;
      intro H; have := congr_arg ( ·.factorization ( x : ℕ ) ) H;
      rw [ Nat.factorization_mul, Nat.factorization_mul ] at this <;> simp_all +decide [ Nat.Prime.ne_zero ];
      grind;
  simp_all +decide [ Nat.choose_two_right ];
  cases k : Finset.card ( Finset.filter Nat.Prime ( Finset.Icc 1 ⌊ ( n : ℝ ) ^ ( 3⁻¹ : ℝ ) ⌋₊ ) ) <;> simp_all +decide [Nat.mul_succ] ; linarith [ Nat.div_mul_cancel ( show 2 ∣ Nat.succ ‹_› * ‹_› from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ) ]

/-
`|B₃| = ∑_{y<q≤n^{2/5}} π(n/q²)`.
-/
lemma card_B3 (n : ℕ) :
    (B3 n).card =
      ∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊).filter Nat.Prime,
        Nat.primeCounting (n / (q * q)) := by
  classical
  unfold B3
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( Nat.Prime.ne_zero <| Finset.mem_filter.mp hq |>.2 ) hxy ];
    rw [ ← card_primes_Icc ];
  · intros q hq r hr hqr; simp_all +decide [ Finset.disjoint_left ] ;
    intro a x hx₁ hx₂ hx₃ hx₄ y hy₁ hy₂ hy₃ hy₄; subst_vars;
    -- Since $q$ and $r$ are distinct primes, $q$ must divide $y$ and $r$ must divide $x$.
    have hq_div_y : q ∣ y := by
      exact Or.resolve_left ( hq.2.dvd_mul.mp ( hy₄.symm ▸ dvd_mul_right _ _ ) ) ( by rintro H; have := Nat.prime_dvd_prime_iff_eq hq.2 hr.2; tauto )
    have hr_div_x : r ∣ x := by
      exact Or.resolve_left ( hr.2.dvd_mul.mp ( hy₄ ▸ dvd_mul_right _ _ ) ) ( by rintro h; have := Nat.prime_dvd_prime_iff_eq hr.2 hq.2; tauto );
    simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
    rw [ Nat.le_div_iff_mul_le ] at * <;> try nlinarith only [ hx₁, hy₁, hx₂, hy₂ ];
    rw [ Nat.floor_lt ] at * <;> norm_num at *;
    · -- From the inequalities $n^{1/3} < y$ and $n^{1/3} < x$, we get $n < y^3$ and $n < x^3$.
      have hn_lt_y3 : (n : ℝ) < y^3 := by
        exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_lt_pow_left₀ hq.1 ( by positivity ) ( by positivity ) )
      have hn_lt_x3 : (n : ℝ) < x^3 := by
        exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_lt_pow_left₀ hr.1 ( by positivity ) ( by positivity ) );
      norm_cast at *; nlinarith only [ hx₂, hy₂, hn_lt_y3, hn_lt_x3, hx₃.two_le, hy₃.two_le ] ;
    · positivity;
    · positivity

/-
`|B₂| = (9/2 + o(1)) S`.
-/
lemma card_B2_asymp (hpnt : PNT) :
    Tendsto (fun n : ℕ => ((B2 n).card : ℝ) / S n) atTop (𝓝 (9/2)) := by
  -- By definition of $k$, we know that $k n = \pi(\lfloor n^{1/3} \rfloor)$.
  set k : ℕ → ℕ := fun n => Nat.primeCounting ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊;
  -- By definition of $k$, we know that $k n \sim \frac{n^{1/3}}{\log n}$.
  have h_k : Filter.Tendsto (fun n : ℕ => (k n : ℝ) / ((n : ℝ) ^ ((1:ℝ)/3) / Real.log n)) Filter.atTop (nhds 3) := by
    have := pi_mul_ratio hpnt 1 one_pos;
    convert this.comp ( tendsto_rpow_atTop ( by norm_num : ( 0 : ℝ ) < 1 / 3 ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) |> ( ·.mul_const 3 ) using 2 <;> norm_num ; ring_nf;
    by_cases h : ‹_› = 0 <;> simp +decide [h] ; ring_nf;
    rw [ Real.log_rpow ( by positivity ) ] ; ring!;
  -- By definition of $B2$, we know that $|B2 n| = \frac{k n (k n + 1)}{2}$.
  have h_B2_card : ∀ n : ℕ, (B2 n).card = (k n * (k n + 1)) / 2 := by
    convert card_B2 using 1;
  -- Substitute the expression for $|B2 n|$ into the limit.
  suffices h_subst : Filter.Tendsto (fun n : ℕ => ((k n : ℝ) * (k n + 1)) / (2 * ((n : ℝ) ^ ((2:ℝ)/3) / (Real.log n)^2))) Filter.atTop (nhds (9 / 2)) by
    convert h_subst using 2 ; norm_num [ h_B2_card, S ] ; ring_nf;
    rw [ Nat.cast_div ] <;> norm_num ; ring ; exact even_iff_two_dvd.mp ( by simp +arith +decide [ parity_simps ] ) ;
  convert h_k.mul ( h_k.add ( tendsto_inv_atTop_zero.comp ( show Filter.Tendsto ( fun n : ℕ => ( n : ℝ ) ^ ( 1 / 3 : ℝ ) / Real.log n ) Filter.atTop ( Filter.atTop ) from ?_ ) ) ) |> ( ·.div_const 2 ) using 2 <;> norm_num ; ring_nf;
  · norm_num [ sq, ← Real.rpow_add', ← Real.rpow_neg ] ; ring;
  · convert tendsto_M_atTop using 1

/-
Prime number theorem with a natural-number argument:
`π(m)·log m / m → 1` as `m → ∞`.
-/
lemma pnt_nat (hpnt : PNT) :
    Tendsto (fun m : ℕ => (Nat.primeCounting m : ℝ) * Real.log m / m) atTop (𝓝 1) := by
  convert Tendsto.comp ( pnt hpnt ) tendsto_natCast_atTop_atTop using 1;
  ext; aesop

/-
For fixed `A > 1`, for all large `n` and every prime `q ∈ (y, Ay]`, writing
`m = n/(q*q)`, the basic size bounds hold.
-/
lemma tw_bounds (A : ℝ) (hA : 1 < A) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
        2 ≤ n / (q * q) ∧
        (n:ℝ) ^ ((1:ℝ)/3) / (2 * A ^ 2) ≤ ((n / (q * q) : ℕ) : ℝ) ∧
        ((n / (q * q) : ℕ) : ℝ) < (n:ℝ) ^ ((1:ℝ)/3) ∧
        (n:ℝ) ^ ((1:ℝ)/3) < (q : ℝ) ∧ (q : ℝ) ≤ A * (n:ℝ) ^ ((1:ℝ)/3) ∧
        ((n / (q * q) : ℕ) : ℝ) * ((q : ℝ) * (q : ℝ)) ≤ (n : ℝ) ∧
        (n : ℝ) < (((n / (q * q) : ℕ) : ℝ) + 1) * ((q : ℝ) * (q : ℝ)) := by
  refine' ( Filter.eventually_atTop.mpr _ );
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, (n : ℝ) ^ ((1 : ℝ) / 3) ≥ 4 * A ^ 2 := by
    have hN₁ : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 3)) Filter.atTop Filter.atTop := by
      exact tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
    exact Filter.eventually_atTop.mp ( hN₁.eventually_ge_atTop _ );
  refine' ⟨ N₁ + 1, fun n hn q hq => _ ⟩ ; refine' ⟨ _, _, _, _, _ ⟩ <;> norm_num at *;
  · refine' Nat.le_div_iff_mul_le ( Nat.mul_pos hq.2.pos hq.2.pos ) |>.2 _;
    rw [ ← @Nat.cast_le ℝ ] ; norm_num;
    have := hN₁ n hn.le;
    rw [ Nat.le_floor_iff ( by positivity ) ] at hq;
    rw [ show ( n : ℝ ) = ( n ^ ( 1 / 3 : ℝ ) ) ^ 3 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ] ; nlinarith [ sq_nonneg ( ( n : ℝ ) ^ ( 1 / 3 : ℝ ) - 2 * A ), show ( q : ℝ ) ≥ ⌊ ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ⌋₊ + 1 by exact_mod_cast hq.1.1, Nat.lt_floor_add_one ( ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ) ];
  · rw [ div_le_iff₀ ] <;> try positivity;
    have h_m_lower : (n : ℝ) < ((n / (q * q) : ℕ) + 1) * (q * q) := by
      exact_mod_cast ( by nlinarith [ Nat.div_add_mod n ( q * q ), Nat.mod_lt n ( mul_pos hq.2.pos hq.2.pos ) ] : ( n : ℕ ) < ( n / ( q * q ) + 1 ) * ( q * q ) );
    -- Since $q \leq A * n^{1/3}$, we have $q^2 \leq A^2 * n^{2/3}$.
    have h_q_sq : (q : ℝ) ^ 2 ≤ A ^ 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
      convert pow_le_pow_left₀ ( by positivity ) ( show ( q : ℝ ) ≤ A * ( n : ℝ ) ^ ( 1 / 3 : ℝ ) from le_trans ( Nat.cast_le.mpr hq.1.2 ) ( Nat.floor_le ( by positivity ) ) ) 2 using 1 <;> (try rfl); (try ring_nf);
      norm_num [ sq, ← Real.rpow_add' ];
    rw [ show ( n : ℝ ) ^ ( 2 / 3 : ℝ ) = ( n : ℝ ) ^ ( 1 - 1 / 3 : ℝ ) by norm_num, Real.rpow_sub ] at * <;> norm_num at *;
    · rw [ mul_div, le_div_iff₀ ] at * <;> nlinarith [ hN₁ n hn.le, show ( n : ℝ ) > 0 by norm_cast; linarith ];
    · linarith;
  · refine' lt_of_le_of_lt ( Nat.cast_div_le .. ) _;
    rw [ div_lt_iff₀ ] <;> norm_num;
    · have := Nat.lt_of_floor_lt hq.1.1;
      convert mul_lt_mul_of_pos_left ( mul_lt_mul'' this this ( by positivity ) ( by positivity ) ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ) ( 1 / 3 : ℝ ) ) using 1 ; ring_nf;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
    · linarith [ hq.2.two_le ];
  · exact Nat.lt_of_floor_lt hq.1.1;
  · exact ⟨ Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hq.1.2 ), by norm_cast; exact Nat.div_mul_le_self _ _, by norm_cast; linarith [ Nat.div_add_mod n ( q * q ), Nat.mod_lt n ( mul_pos hq.2.pos hq.2.pos ) ] ⟩

/-
For fixed `A > 1` and `δ > 0`, for all large `n` and every prime `q ∈ (y, Ay]`,
with `m = n/(q*q)`: `P = π(m)·log m/m ∈ [1-δ, 1+δ]`, `Q = m·q²/n ∈ [1-δ, 1]`,
`R = log n/log m ∈ [3, 3+8δ]`.
-/
lemma tw_PQR (hpnt : PNT) (A : ℝ) (hA : 1 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
        let m := n / (q * q)
        (1 - δ) ≤ (Nat.primeCounting m : ℝ) * Real.log m / m ∧
        (Nat.primeCounting m : ℝ) * Real.log m / m ≤ (1 + δ) ∧
        (1 - δ) ≤ (m : ℝ) * ((q : ℝ) * (q : ℝ)) / n ∧
        (m : ℝ) * ((q : ℝ) * (q : ℝ)) / n ≤ 1 ∧
        3 ≤ Real.log n / Real.log m ∧
        Real.log n / Real.log m ≤ 3 + 8 * δ := by
  -- Apply the results from the provided solution to the goal.
  have h_P : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); |((Nat.primeCounting m : ℝ) * Real.log m) / m - 1| ≤ δ := by
    have := pnt_nat hpnt;
    have := Metric.tendsto_atTop.mp this δ hδ;
    obtain ⟨ N, hN ⟩ := this;
    have h_m_ge_N : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/3) / (2 * A ^ 2)) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_div_const ( by positivity ) ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
    filter_upwards [ h_m_ge_N.eventually_gt_atTop N, tw_bounds A hA ] with n hn hn';
    exact fun q hq => le_of_lt ( hN _ <| Nat.cast_le.mp <| hn.le.trans <| hn' q hq |>.2.1 );
  have h_Q : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); 1 - δ ≤ (m : ℝ) * ((q : ℝ) * (q : ℝ)) / (n : ℝ) ∧ (m : ℝ) * ((q : ℝ) * (q : ℝ)) / (n : ℝ) ≤ 1 := by
    have h_Q : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); (q : ℝ) * (q : ℝ) / (n : ℝ) ≤ δ := by
      have h_Q : Filter.Tendsto (fun n : ℕ => (A * (n:ℝ) ^ ((1:ℝ)/3)) * (A * (n:ℝ) ^ ((1:ℝ)/3)) / (n:ℝ)) Filter.atTop (nhds 0) := by
        ring_nf;
        norm_num [ sq, ← Real.rpow_add' ];
        norm_num [ mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add' ];
        simpa using tendsto_const_nhds.mul ( tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) );
      filter_upwards [ h_Q.eventually ( gt_mem_nhds hδ ), Filter.eventually_gt_atTop 0 ] with n hn hn' q hq using le_trans ( by gcongr <;> linarith [ show ( q : ℝ ) ≤ A * ( n : ℝ ) ^ ( 1 / 3 : ℝ ) by exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity ] ) hn.le;
    filter_upwards [ h_Q, tw_bounds A hA ] with n hn hn';
    intro q hq; specialize hn q hq; specialize hn' q hq; rcases eq_or_ne n 0 <;> simp_all +decide ;
    rw [ div_add', le_div_iff₀ ] <;> try positivity;
    exact ⟨ by rw [ div_le_iff₀ ( by positivity ) ] at hn; linarith, by rw [ div_le_iff₀ ( by positivity ) ] ; linarith ⟩;
  have h_R : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); 3 ≤ Real.log n / Real.log m ∧ Real.log n / Real.log m ≤ 3 + 8 * δ := by
    have h_R : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); 3 ≤ Real.log n / Real.log m := by
      have h_R : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); 2 ≤ m ∧ (m : ℝ) < (n:ℝ) ^ ((1:ℝ)/3) := by
        filter_upwards [ tw_bounds A hA ] with n hn q hq using ⟨ hn q hq |>.1, hn q hq |>.2.2.1 ⟩;
      filter_upwards [ h_R, Filter.eventually_gt_atTop 1 ] with n hn hn' ; intro q hq ; specialize hn q hq ; norm_num at *;
      rw [ le_div_iff₀ ( Real.log_pos <| mod_cast hn.1 ), ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> try positivity;
      · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; exact lt_of_lt_of_le ( pow_lt_pow_left₀ hn.2 ( by positivity ) <| by positivity ) <| by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num;
      · exact pow_pos ( pos_of_gt hn.1 ) _;
      · grind;
    have h_R_upper : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); Real.log n ≤ (3 + 8 * δ) * Real.log m := by
      have h_R_upper : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); Real.log m ≥ (1 / 3) * Real.log n - Real.log (2 * A ^ 2) := by
        have h_R_upper : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); (m : ℝ) ≥ (n:ℝ) ^ ((1:ℝ)/3) / (2 * A ^ 2) := by
          filter_upwards [ tw_bounds A hA ] with n hn q hq using hn q hq |>.2.1;
        filter_upwards [ h_R_upper, Filter.eventually_gt_atTop 0 ] with n hn hn' q hq;
        have := hn q hq;
        have := Real.log_le_log ( by positivity ) this;
        rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] at this ; linarith;
      have h_R_upper : ∀ᶠ n : ℕ in atTop, Real.log n ≥ 3 * (3 + 8 * δ) * Real.log (2 * A ^ 2) / (8 * δ) := by
        exact tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |> fun h => h.eventually ( Filter.eventually_ge_atTop _ );
      filter_upwards [ h_R_upper, ‹∀ᶠ n : ℕ in atTop, ∀ q ∈ Finset.filter Nat.Prime ( Finset.Ioc ⌊ ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ⌋₊ ⌊A * ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ⌋₊ ), let m := n / ( q * q ) ; log ↑m ≥ 1 / 3 * log ↑n - log ( 2 * A ^ 2 ) › ] with n hn hn' q hq using by nlinarith [ hn' q hq, mul_div_cancel₀ ( 3 * ( 3 + 8 * δ ) * Real.log ( 2 * A ^ 2 ) ) ( by positivity : ( 8 * δ ) ≠ 0 ) ] ;
    filter_upwards [ h_R, h_R_upper, tw_bounds A hA ] with n hn hn' hn'';
    intro q hq; specialize hn q hq; specialize hn' q hq; specialize hn'' q hq; norm_num at *;
    exact ⟨ hn, by rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] ; linarith ⟩;
  filter_upwards [ h_P, h_Q, h_R ] with n hn hn' hn'' using fun q hq => ⟨ by linarith [ abs_le.mp ( hn q hq ) ], by linarith [ abs_le.mp ( hn q hq ) ], hn' q hq |>.1, hn' q hq |>.2, hn'' q hq |>.1, hn'' q hq |>.2 ⟩

/-
For fixed `A > 1` and `ε > 0`, for all large `n` and every prime `q ∈ (y, Ay]`,
the count `π(n/q²)` is within a factor `(3 ± ε)` of `n / (q² log n)`.
-/
lemma card_B3_main_termwise (hpnt : PNT) (A : ℝ) (hA : 1 < A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
        (3 - ε) * (n:ℝ) / ((q:ℝ)^2 * Real.log n) ≤ (Nat.primeCounting (n / (q * q)) : ℝ) ∧
        (Nat.primeCounting (n / (q * q)) : ℝ) ≤ (3 + ε) * (n:ℝ) / ((q:ℝ)^2 * Real.log n) := by
  -- Choose `δ > 0` with `δ < 1`, `(1-δ)^2*3 ≥ 3-ε`, and `(1+δ)*(3+8*δ) ≤ 3+ε`.
  obtain ⟨δ, hδ_pos, hδ_lt_1, hδ_bound⟩ : ∃ δ > 0, δ < 1 ∧ (1 - δ)^2 * 3 ≥ 3 - ε ∧ (1 + δ) * (3 + 8 * δ) ≤ 3 + ε := by
    use Min.min ( ε / 24 ) ( 1 / 32 );
    cases min_cases ( ε / 24 ) ( 1 / 32 ) <;> exact ⟨ by positivity, by linarith, by nlinarith, by nlinarith ⟩;
  filter_upwards [ tw_PQR hpnt A hA δ hδ_pos, tw_bounds A hA, Filter.eventually_gt_atTop 1 ] with n hn hn' hn'' q hq;
  -- Let `m = n/(q*q)`. From `tw_bounds`: `2 ≤ m` (so `(m:ℝ) ≥ 2 > 0` and `Real.log m > 0` by `Real.log_pos`); `q` is prime so `(q:ℝ) > 0`.
  set m := n / (q * q)
  have hm_pos : 2 ≤ m := by
    exact hn' q hq |>.1
  have hm_log_pos : 0 < Real.log m := by
    exact Real.log_pos <| Nat.one_lt_cast.mpr hm_pos
  have hq_pos : 0 < (q : ℝ) := by
    exact Nat.cast_pos.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hq |>.2 ) );
  -- From `tw_PQR` (unfold the `let m`): abbreviate `P = (π(m):ℝ)*Real.log m/m`, `Q = (m:ℝ)*((q:ℝ)*(q:ℝ))/n`, `R = Real.log n/Real.log m`, with `1-δ ≤ P ≤ 1+δ`, `1-δ ≤ Q ≤ 1`, `3 ≤ R ≤ 3+8*δ`.
  set P := (Nat.primeCounting m : ℝ) * Real.log m / m
  set Q := (m : ℝ) * ((q : ℝ) * (q : ℝ)) / n
  set R := Real.log n / Real.log m
  have hP : 1 - δ ≤ P ∧ P ≤ 1 + δ := by
    exact ⟨ hn q hq |>.1, hn q hq |>.2.1 ⟩
  have hQ : 1 - δ ≤ Q ∧ Q ≤ 1 := by
    exact ⟨ hn q hq |>.2.2.1, hn q hq |>.2.2.2.1 ⟩
  have hR : 3 ≤ R ∧ R ≤ 3 + 8 * δ := by
    exact ⟨ hn q hq |>.2.2.2.2.1, hn q hq |>.2.2.2.2.2 ⟩;
  -- Key identity: `(π(m):ℝ) * ((q:ℝ)*(q:ℝ)) * Real.log n / n = P * Q * R`.
  have hV : (Nat.primeCounting m : ℝ) * ((q : ℝ) * (q : ℝ)) * Real.log n / n = P * Q * R := by
    simp +zetaDelta at *;
    field_simp;
  -- Bound `V = P*Q*R`: since `P,Q,R > 0` (as `δ < 1`, `R ≥ 3`), `V ≥ (1-δ)*(1-δ)*3 ≥ 3-ε` and `V ≤ (1+δ)*1*(3+8*δ) ≤ 3+ε`.
  have hV_bounds : 3 - ε ≤ P * Q * R ∧ P * Q * R ≤ 3 + ε := by
    constructor;
    · refine le_trans ?_ ( mul_le_mul ( mul_le_mul hP.1 hQ.1 ?_ ?_ ) hR.1 ?_ ?_ ) <;> nlinarith;
    · exact le_trans ( mul_le_mul ( mul_le_mul hP.2 hQ.2 ( by nlinarith ) ( by nlinarith ) ) hR.2 ( by nlinarith ) ( by nlinarith ) ) ( by nlinarith );
  rw [ div_le_iff₀, le_div_iff₀ ];
  · rw [ div_eq_iff ] at hV <;> norm_num at *;
    · constructor <;> nlinarith [ show ( n : ℝ ) > 0 by positivity ];
    · linarith;
  · exact mul_pos ( sq_pos_of_pos hq_pos ) ( Real.log_pos ( Nat.one_lt_cast.mpr hn'' ) );
  · exact mul_pos ( sq_pos_of_pos hq_pos ) ( Real.log_pos ( Nat.one_lt_cast.mpr hn'' ) )

/-
The normalized main term `(n/log n)·∑_{y<q≤Ay} 1/q²` divided by `S`
tends to `3(1 - 1/A)`.
-/
lemma card_B3_main_Tratio (hpnt : PNT) (A : ℝ) (hA : 1 < A) :
    Tendsto (fun n : ℕ =>
      ((n:ℝ) / Real.log n *
        (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
          (1 / (q:ℝ)^2))) / S n) atTop (𝓝 (3 * (1 - 1/A))) := by
  norm_num [ S ];
  convert Filter.Tendsto.const_mul 3 ( Erdos793.primeSq_interval hpnt A hA |> Filter.Tendsto.comp <| Erdos793.tendsto_y_atTop ) using 2 ; norm_num ; ring_nf;
  · unfold primeSqSum; norm_num [ Real.log_rpow ] ; ring_nf;
    by_cases h : ‹_› = 0 <;> simp +decide [ h, sq, mul_assoc, mul_comm, mul_left_comm ];
    by_cases h' : Real.log ‹ℕ› = 0 <;> simp_all +decide [← mul_assoc, ← Real.rpow_neg] ; ring_nf;
    · norm_cast at * ; aesop;
    · rw [ Real.log_rpow ( by positivity ) ] ; rw [ ← Real.rpow_one_add' ( by positivity ) ] <;> norm_num ; ring_nf ; aesop;
  · norm_num

/-
For fixed `A > 1`, the primes `q` in the main range `(y, Ay]` contribute
`(9(1 - 1/A) + o(1)) S`.
-/
lemma card_B3_main (hpnt : PNT) (A : ℝ) (hA : 1 < A) :
    Tendsto (fun n : ℕ =>
      (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
        Nat.primeCounting (n / (q * q)) : ℝ) / S n) atTop (𝓝 (9 * (1 - 1/A))) := by
  -- Using the bounds from card_B3_main_termwise and the fact that R n tends to L, we can show that the ratio tends to 3L.
  have h_ratio : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |((∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) / S n) - 3 * ((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n)| ≤ ε := by
    intro ε hε_pos
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (3 - ε / 8) * (n:ℝ) / ((q:ℝ)^2 * Real.log n) ≤ (Nat.primeCounting (n / (q * q)) : ℝ) ∧ (Nat.primeCounting (n / (q * q)) : ℝ) ≤ (3 + ε / 8) * (n:ℝ) / ((q:ℝ)^2 * Real.log n) := by
      exact Filter.eventually_atTop.mp ( card_B3_main_termwise hpnt A hA ( ε / 8 ) ( by positivity ) ) |> fun ⟨ N₁, hN₁ ⟩ => ⟨ N₁, fun n hn q hq => hN₁ n hn q hq ⟩;
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, |((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n) - 3 * (1 - 1 / A)| ≤ 1 := by
      have := card_B3_main_Tratio hpnt A hA;
      exact Filter.eventually_atTop.mp ( this.eventually ( Metric.closedBall_mem_nhds _ zero_lt_one ) );
    refine' ⟨ Max.max N₁ N₂ + 2, fun n hn => _ ⟩ ; specialize hN₁ n ( by linarith [ le_max_left N₁ N₂ ] ) ; specialize hN₂ n ( by linarith [ le_max_right N₁ N₂ ] ) ; simp_all +decide [ Finset.sum_div _ _ _ ];
    -- Applying the bounds from hN₁ and hN₂, we can bound the difference.
    have h_diff_bound : |(∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) / S n - 3 * ((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n)| ≤ ε / 8 * ((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n) := by
      have h_diff_bound : (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) ≥ (3 - ε / 8) * (n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) ∧ (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) ≤ (3 + ε / 8) * (n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) := by
        simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        exact ⟨ Finset.sum_le_sum fun x hx => hN₁ x ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ( Finset.mem_filter.mp hx |>.2 ) |>.1, Finset.sum_le_sum fun x hx => hN₁ x ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ( Finset.mem_filter.mp hx |>.2 ) |>.2 ⟩;
      rw [ abs_le ] ; constructor <;> ring_nf at * <;> nlinarith [ inv_pos.mpr ( show 0 < S n from div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) _ ) <| sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) ] ;
    simp_all +decide [ ← Finset.sum_div _ _ _ ];
    refine le_trans h_diff_bound ?_;
    refine' le_trans ( mul_le_mul_of_nonneg_left ( show ( ( n : ℝ ) / Real.log n * ∑ x ∈ Finset.Ioc ⌊ ( n : ℝ ) ^ ( 3⁻¹ : ℝ ) ⌋₊ ⌊A * ( n : ℝ ) ^ ( 3⁻¹ : ℝ ) ⌋₊ with Nat.Prime x, ( x ^ 2 : ℝ ) ⁻¹ ) / S n ≤ 4 by linarith [ abs_le.mp hN₂, show ( 3 : ℝ ) * ( 1 - A⁻¹ ) ≤ 3 by nlinarith [ inv_mul_cancel₀ ( by linarith : A ≠ 0 ) ] ] ) ( by positivity ) ) ( by linarith );
  have h_tendsto : Filter.Tendsto (fun n : ℕ => 3 * ((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n)) Filter.atTop (nhds (3 * (3 * (1 - 1 / A)))) := by
    exact tendsto_const_nhds.mul ( card_B3_main_Tratio hpnt A hA );
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε; rcases h_ratio ( ε / 2 ) ( half_pos hε ) with ⟨ N, hN ⟩ ; filter_upwards [ h_tendsto ( ε / 2 ) ( half_pos hε ), Filter.Ici_mem_atTop N ] with n hn hn' using abs_lt.mpr ⟨ by linarith [ abs_lt.mp hn, abs_le.mp ( hN n hn' ) ], by linarith [ abs_lt.mp hn, abs_le.mp ( hN n hn' ) ] ⟩ ;

/-
There is a constant `C₃ > 0` such that for every fixed `A > 1` and all large
`n`, the primes `q` in the tail range `(Ay, n^{2/5}]` contribute at most
`(C₃/A) S`.
-/
lemma card_B3_tail (hpnt : PNT) : ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ A : ℝ, 1 < A →
    ∀ᶠ n : ℕ in atTop,
      (∑ q ∈ (Finset.Ioc ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊).filter Nat.Prime,
        Nat.primeCounting (n / (q * q)) : ℝ) / S n ≤ C₃ / A := by
  revert hpnt;
  intro hpnt
  obtain ⟨C_π, hC_π_pos, hC_π⟩ := pi_upper hpnt
  obtain ⟨C₂, hC₂_pos, hC₂⟩ := primeSq_tail hpnt;
  refine' ⟨ 18 * C_π * C₂, by positivity, fun A hA => _ ⟩;
  -- For large enough `n`, `y ≥ 2`, `A*y ≥ 2`, `log n > 0`, and for every prime `q ≤ ⌊n^{2/5}⌋` the natural number `m := n/(q*q)` satisfies `log (m:ℝ) ≥ (log n)/6` and `m ≥ 2`.
  have h_large_n : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (1 / 3 : ℝ) ∧ 2 ≤ A * (n : ℝ) ^ (1 / 3 : ℝ) ∧ 0 < Real.log n ∧ ∀ q : ℕ, Nat.Prime q → q ≤ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ → Real.log (n / (q * q) : ℝ) ≥ Real.log n / 6 ∧ 2 ≤ n / (q * q) := by
    refine' Filter.eventually_atTop.mpr ⟨ 2 ^ 30, fun n hn => ⟨ _, _, _, _ ⟩ ⟩ <;> norm_num at *;
    · exact le_trans ( by norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( Nat.cast_le.mpr hn ) ( by norm_num ) );
    · exact le_trans ( by nlinarith [ show ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ≥ 2 by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( Nat.cast_le.mpr hn ) ( by norm_num ) ) ] ) ( mul_le_mul_of_nonneg_right hA.le ( by positivity ) );
    · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith;
    · intro q hq hq'; rw [ Real.log_div ( by positivity ) ( by norm_cast; nlinarith [ hq.two_le ] ) ];
      constructor;
      · rw [ Nat.le_floor_iff ( by positivity ), Real.le_rpow_iff_log_le ] at * <;> norm_num at *;
        · rw [ Real.log_mul ( by norm_cast; linarith [ hq.pos ] ) ( by norm_cast; linarith [ hq.pos ] ) ] ; linarith [ Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ];
        · exact hq.pos;
        · linarith;
      · rw [ Nat.le_floor_iff ( by positivity ), Real.le_rpow_iff_log_le ] at * <;> norm_num at * <;> try linarith;
        · rw [ Nat.le_div_iff_mul_le ( Nat.mul_pos hq.pos hq.pos ) ];
          rw [ ← @Nat.cast_le ℝ ] ; push_cast ; rw [ ← Real.log_le_log_iff ( by norm_cast; nlinarith [ hq.two_le ] ) ( by positivity ) ];
          rw [ Real.log_mul ( by positivity ) ( by norm_cast; nlinarith [ hq.two_le ] ), Real.log_mul ( by norm_cast; nlinarith [ hq.two_le ] ) ( by norm_cast; nlinarith [ hq.two_le ] ) ];
          linarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, show ( Real.log n : ℝ ) ≥ 30 * Real.log 2 by rw [ ← Real.log_rpow, ge_iff_le, Real.log_le_log_iff ] <;> norm_cast ; linarith [ Nat.pow_le_pow_right two_pos ( show 30 ≤ 30 by norm_num ) ] ];
        · exact hq.pos;
  filter_upwards [ h_large_n, Filter.eventually_gt_atTop 1 ] with n hn hn';
  -- Applying the per-term bound to each term in the sum.
  have h_sum_bound : (∑ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ with Nat.Prime q, (Nat.primeCounting (n / (q * q)) : ℝ)) ≤ 6 * C_π * (n : ℝ) / (Real.log n) * (∑ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ with Nat.Prime q, (1 / (q : ℝ) ^ 2)) := by
    have h_sum_bound : ∀ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊, Nat.Prime q → (Nat.primeCounting (n / (q * q)) : ℝ) ≤ 6 * C_π * (n : ℝ) / ((q : ℝ) ^ 2 * Real.log n) := by
      intros q hq hq_prime
      have h_pi_bound : (Nat.primeCounting (n / (q * q)) : ℝ) ≤ C_π * (n / (q * q) : ℝ) / Real.log (n / (q * q) : ℝ) := by
        convert hC_π ( n / ( q * q ) ) _ using 1;
        · rw_mod_cast [ Nat.floor_div_natCast, Nat.floor_natCast ];
        · rw [ le_div_iff₀ ] <;> norm_cast;
          · have := hn.2.2.2 q hq_prime ( Finset.mem_Ioc.mp hq |>.2 );
            nlinarith [ Nat.div_mul_le_self n ( q * q ) ];
          · nlinarith [ hq_prime.two_le ];
      refine le_trans h_pi_bound ?_;
      rw [ div_le_div_iff₀ ];
      · have := hn.2.2.2 q hq_prime ( Finset.mem_Ioc.mp hq |>.2 );
        field_simp;
        rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr hq_prime.ne_zero ) ] ; ring_nf at * ; linarith;
      · exact lt_of_lt_of_le ( by linarith ) ( hn.2.2.2 q hq_prime ( Finset.mem_Ioc.mp hq |>.2 ) |>.1 );
      · exact mul_pos ( sq_pos_of_pos ( Nat.cast_pos.mpr hq_prime.pos ) ) hn.2.2.1;
    rw [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun x hx => by convert h_sum_bound x ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hx |>.2 ) using 1 <;> first | rfl | ring;
  -- Applying the primeSq_tail bound to the sum.
  have h_primeSq_tail_bound : (∑ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ with Nat.Prime q, (1 / (q : ℝ) ^ 2)) ≤ C₂ / ((A * (n : ℝ) ^ (1 / 3 : ℝ)) * Real.log (A * (n : ℝ) ^ (1 / 3 : ℝ))) := by
    exact hC₂ _ hn.2.1 _;
  -- Combining the bounds and simplifying.
  have h_combined : (∑ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ with Nat.Prime q, (Nat.primeCounting (n / (q * q)) : ℝ)) ≤ 18 * C_π * C₂ * (n : ℝ) / (A * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log n) ^ 2) := by
    refine le_trans h_sum_bound <| le_trans ( mul_le_mul_of_nonneg_left h_primeSq_tail_bound <| by exact div_nonneg ( by positivity ) <| by linarith ) ?_;
    rw [ div_mul_div_comm, div_le_div_iff₀ ];
    · rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] ; ring_nf ; norm_num;
      exact mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg hC_π_pos.le ( Nat.cast_nonneg _ ) ) hC₂_pos.le ) ( by positivity ) ) ( by positivity ) ) ( by exact Real.log_nonneg ( by norm_cast; linarith ) ) ) ( Real.log_nonneg ( by linarith ) );
    · exact mul_pos hn.2.2.1 ( mul_pos ( by positivity ) ( Real.log_pos ( by linarith ) ) );
    · exact mul_pos ( by positivity ) ( sq_pos_of_pos hn.2.2.1 );
  rw [ div_le_iff₀ ];
  · convert h_combined using 1 <;> (try rfl); norm_num [ S ]; (try ring_nf);
    rw [ show ( 2 / 3 : ℝ ) = 1 - 1 / 3 by norm_num, Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring;
  · exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( pos_of_gt hn' ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) )

/-
`|B₃| = (9 + o(1)) S`.
-/
lemma card_B3_asymp (hpnt : PNT) :
    Tendsto (fun n : ℕ => ((B3 n).card : ℝ) / S n) atTop (𝓝 9) := by
  obtain ⟨ C₃, hC₃_pos, hC₃ ⟩ := Erdos793.card_B3_tail hpnt; norm_num at *; (
  -- For any fixed `A > 1`, we have `main n + tail n - 9 = (main n - 9*(1-1/A)) + tail n - 9/A`.
  have h_split : ∀ A : ℝ, 1 < A → ∀ᶠ n in atTop,
    ((B3 n).card : ℝ) / S n = (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) / S n + (∑ q ∈ (Finset.Ioc ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) / S n := by
      intro A hA;
      -- For large enough `n`, we have `⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊ ≤ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊`.
      have h_floor : ∀ᶠ n in atTop, ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊ ≤ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊ := by
        -- We'll use that $A * n^{1/3} < n^{2/5}$ for sufficiently large $n$.
        have h_ineq : ∀ᶠ n in atTop, A * (n : ℝ) ^ ((1:ℝ)/3) < (n : ℝ) ^ ((2:ℝ)/5) := by
          -- We can divide both sides by $n^{1/3}$ to get $A < n^{2/5 - 1/3} = n^{1/15}$.
          suffices h_div : ∀ᶠ n in atTop, A < (n : ℝ) ^ ((1:ℝ)/15) by
            filter_upwards [ h_div, Filter.eventually_gt_atTop 0 ] with n hn hn' using by convert mul_lt_mul_of_pos_right hn ( Real.rpow_pos_of_pos hn' ( 1 / 3 : ℝ ) ) using 1 <;> (try rfl); rw [ ← Real.rpow_add hn' ]; norm_num;
          exact tendsto_rpow_atTop ( by norm_num ) |> fun h => h.eventually_gt_atTop A;
        filter_upwards [ h_ineq ] with n hn using Nat.floor_mono hn.le;
      filter_upwards [ h_floor.natCast_atTop ] with n hn;
      rw [ ← add_div, ← Finset.sum_union ];
      · rw [ ← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc ] <;> norm_num [ hn ];
        · rw [ Erdos793.card_B3 ];
          norm_cast;
        · exact Nat.floor_mono <| le_mul_of_one_le_left ( by positivity ) hA.le;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε_pos
  obtain ⟨A, hA⟩ : ∃ A : ℝ, 1 < A ∧ 9 / A < ε / 2 ∧ C₃ / A < ε / 2 := by
    exact ⟨ 1 + 9 / ( ε / 2 ) + C₃ / ( ε / 2 ), by linarith [ show 0 < 9 / ( ε / 2 ) by positivity, show 0 < C₃ / ( ε / 2 ) by positivity ], by rw [ div_lt_iff₀ ] <;> nlinarith [ show 0 < 9 / ( ε / 2 ) by positivity, show 0 < C₃ / ( ε / 2 ) by positivity, mul_div_cancel₀ 9 ( by positivity : ( ε / 2 ) ≠ 0 ) ], by rw [ div_lt_iff₀ ] <;> nlinarith [ show 0 < 9 / ( ε / 2 ) by positivity, show 0 < C₃ / ( ε / 2 ) by positivity, mul_div_cancel₀ C₃ ( by positivity : ( ε / 2 ) ≠ 0 ) ] ⟩;
  obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp ( Erdos793.card_B3_main hpnt A hA.1 ) ( ε / 2 ) ( half_pos hε_pos ) ; simp_all +decide [ dist_eq_norm ] ;
  obtain ⟨ M, hM ⟩ := hC₃ A hA.1; obtain ⟨ K, hK ⟩ := h_split A hA.1; use Max.max N ( Max.max M K ) ; intros n hn; specialize hN n ( le_trans ( le_max_left _ _ ) hn ) ; specialize hM n ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hn ) ; specialize hK n ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hn ) ; simp_all +decide [ abs_lt ] ;
  constructor <;> nlinarith [ inv_mul_cancel₀ ( by linarith : A ≠ 0 ), div_mul_cancel₀ 9 ( by linarith : A ≠ 0 ), div_mul_cancel₀ C₃ ( by linarith : A ≠ 0 ), show 0 ≤ ( ∑ x ∈ Finset.Ioc ⌊A * ( n : ℝ ) ^ ( 3⁻¹ : ℝ ) ⌋₊ ⌊ ( n : ℝ ) ^ ( 2 / 5 : ℝ ) ⌋₊ with Nat.Prime x, ( n / ( x * x ) |> Nat.primeCounting : ℝ ) ) / S n from div_nonneg ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ( show 0 ≤ S n from div_nonneg ( by positivity ) ( sq_nonneg _ ) ) ]);

/-
`|B₀| + |B₁| = π(n) + o(S)`.
-/
lemma card_B0B1_sub :
    Tendsto (fun n : ℕ =>
      (((B0 n).card + (B1 n).card : ℝ) - Nat.primeCounting n) / S n) atTop (𝓝 0) := by
  -- By definition of $B0$ and $B1$, we know that for $n \geq 2$, $(B0 n).card + (B1 n).card = \lfloor (n:ℝ)^{3/5} \rfloor + (\pi(n) - \pi(\lfloor (n:ℝ)^{3/5} \rfloor))$.
  have h_card : ∀ n ≥ 2, (B0 n).card + (B1 n).card = Nat.primeCounting n + (⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊ - Nat.primeCounting ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊) := by
    intros n hn; rw [ card_B0, show B1 n = ( Finset.Ioc ⌊ ( n : ℝ ) ^ ( 3 / 5 : ℝ ) ⌋₊ n ).filter Nat.Prime from rfl ] ; rw [ card_primes_Ioc ] ; ring_nf;
    · have h_card : Nat.primeCounting n ≥ Nat.primeCounting ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊ := by
        exact Nat.monotone_primeCounting <| Nat.floor_le_of_le <| by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) <| show ( 3 : ℝ ) / 5 ≤ 1 by norm_num ) <| by norm_num;
      linarith [ Nat.sub_add_cancel h_card, Nat.sub_add_cancel ( show ⌊ ( n : ℝ ) ^ ( 3 / 5 : ℝ ) ⌋₊.primeCounting ≤ ⌊ ( n : ℝ ) ^ ( 3 / 5 : ℝ ) ⌋₊ from primeCounting_le_self _ ) ];
    · exact Nat.floor_le_of_le ( le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show ( 3 : ℝ ) / 5 ≤ 1 by norm_num ) ) ( by norm_num ) );
  -- Using the fact that $|B₀| + |B₁| = π(n) + o(S)$, we can bound the expression.
  have h_bound : ∀ n ≥ 2, |((B0 n).card + (B1 n).card - Nat.primeCounting n : ℝ)| ≤ (n:ℝ) ^ ((3:ℝ)/5) := by
    intro n hn; rw [ abs_of_nonneg ] <;> norm_cast <;> norm_num [ h_card n hn ];
    · exact le_trans ( Nat.cast_le.mpr ( Nat.sub_le _ _ ) ) ( Nat.floor_le ( by positivity ) );
    · grind +qlia;
  refine' squeeze_zero_norm' _ _;
  use fun n => ( n : ℝ ) ^ ( 3 / 5 : ℝ ) / S n;
  · filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn using by rw [ Real.norm_eq_abs, abs_div, abs_of_nonneg ( show 0 ≤ S n from div_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sq_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_right ( h_bound n hn ) ( div_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sq_nonneg _ ) ) ;
  · convert n35_div_S_tendsto_zero using 1

/-
For every `ε > 0`, eventually `F(n) - π(n) ≤ (27/2 + ε) S`.
-/
lemma F_upper (hpnt : PNT) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (F n : ℝ) - Nat.primeCounting n ≤ (27/2 + ε) * S n := by
  -- By added TestTendsto.tendsto_add, we know that
  have h_add : Filter.Tendsto (fun n : ℕ => (((B0 n).card + (B1 n).card : ℝ) - Nat.primeCounting n) / S n + ((B2 n).card : ℝ) / S n + ((B3 n).card : ℝ) / S n) Filter.atTop (nhds ((0 : ℝ) + (9 / 2 : ℝ) + 9)) := by
    exact Filter.Tendsto.add ( Filter.Tendsto.add ( by simpa using card_B0B1_sub ) ( by simpa using card_B2_asymp hpnt ) ) ( by simpa using card_B3_asymp hpnt );
  -- By added TestTendsto.tendsto_add, we know that for sufficiently large n, the sum is less than 27/2 + ε.
  have h_bound : ∀ᶠ n in Filter.atTop, (((B0 n).card + (B1 n).card : ℝ) - Nat.primeCounting n) / S n + ((B2 n).card : ℝ) / S n + ((B3 n).card : ℝ) / S n < (27 / 2 + ε) := by
    exact h_add.eventually ( gt_mem_nhds <| by linarith );
  filter_upwards [ h_bound, Filter.eventually_ge_atTop 2 ] with n hn hn';
  -- By definition of $F$, we know that $F(n) \leq (Bset n).card$.
  have h_F_le_Bset : (F n : ℝ) ≤ ((B0 n).card + (B1 n).card + (B2 n).card + (B3 n).card : ℝ) := by
    exact_mod_cast le_trans ( F_le_Bset_card n hn' ) ( by exact_mod_cast Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_union_le _ _ ) le_rfl ) le_rfl );
  rw [ ← add_div, ← add_div, div_lt_iff₀ ] at hn <;> nlinarith [ show 0 < S n from by exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ( sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ]

end Erdos793
