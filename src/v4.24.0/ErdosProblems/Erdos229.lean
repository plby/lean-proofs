/-

This is a Lean formalization of a solution to Erdős Problem 229.
https://www.erdosproblems.com/forum/thread/229

The original proof was found by: Barth and Schneider

[BaSc72] Barth, K. F. and Schneider, W. J., On a problem of Erdős
concerning the zeros of the derivatives of an entire
function. Proc. Amer. Math. Soc. (1972), 229--232.


A proof of ChatGPT's choice was auto-formalized by Aristotle (from
Harmonic).  The final theorem statement was available at the Formal
Conjectures project (organized by Google DeepMind).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
Formalization of a theorem by Polya (or similar) about the existence of a transcendental entire function with prescribed zeros of derivatives on a sequence of discrete sets.

The main result is `thm_main`, which states that given a sequence of sets `S_n` with no finite limit point, there exists a transcendental entire function `f` and a sequence of integers `k_n` such that `f^{(k_n)}` vanishes on `S_n` for each `n`.

The proof follows the inductive construction described in the provided LaTeX text:
1.  We define `HasNoFiniteLimitPoint` and prove basic properties.
2.  We use `exists_radii` and `exists_auxiliary_points` to set up the geometric constraints.
3.  We define a `history_seq` of polynomials `T_n` (and their sums `F_n`) inductively using `next_step`, which relies on `exists_next_step_final` (based on `small_polynomial_with_prescribed_jets`).
4.  We prove the validity of the construction (`history_seq_valid`).
5.  We define the limit function `f` as a series `∑ T_n`.
6.  We prove `f` is entire (`f_entire`) and transcendental (`f_transcendental`).
7.  We prove the derivative conditions (`f_deriv_vanishes_on_Sn`).
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped Classical

set_option maxHeartbeats 0

/-
A set S has no finite limit point if its intersection with every compact set is finite.
-/
open Complex Polynomial Set Filter Topology Metric

def HasNoFiniteLimitPoint (S : Set ℂ) : Prop :=
  ∀ K, IsCompact K → (S ∩ K).Finite

/-
Let $b_1,\dots,b_m\in\mathbb{C}$ be distinct and let $L\ge 0$. For each $1\le j\le m$ and $0\le \ell\le L$, choose complex numbers $\gamma_{j,\ell}$. Then there exists a polynomial $H$ such that $H^{(\ell)}(b_j)=\gamma_{j,\ell}$ for all $j, \ell$.
-/
lemma hermite_interpolation (m : ℕ) (b : Fin m → ℂ) (hb : Function.Injective b) (L : ℕ)
    (γ : Fin m → Fin (L + 1) → ℂ) :
    ∃ H : Polynomial ℂ, ∀ (j : Fin m) (l : Fin (L + 1)),
      (derivative^[l] H).eval (b j) = γ j l := by
  by_contra! h_not_ex;
  obtain ⟨H, hH⟩ : ∃ H : Polynomial ℂ, ∀ j : Fin m, ∀ l : Fin (L + 1), (Polynomial.derivative^[l] H).eval (b j) = γ j l := by
    -- For each $j$, set $T_j(z) = \sum_{\ell=0}^{L} \gamma_{j,\ell} \frac{(z - b_j)^\ell}{\ell!}$.
    set T : Fin m → Polynomial ℂ := fun j => Finset.sum (Finset.univ : Finset (Fin (L + 1))) (fun l => Polynomial.C (γ j l / Nat.factorial l.val) * (Polynomial.X - Polynomial.C (b j)) ^ l.val);
    -- By the Chinese Remainder Theorem, there exists a polynomial $H$ such that $H \equiv T_j \pmod{(z - b_j)^{L+1}}$ for all $j$.
    obtain ⟨H, hH⟩ : ∃ H : Polynomial ℂ, ∀ j : Fin m, H - T j ∈ Ideal.span {(Polynomial.X - Polynomial.C (b j)) ^ (L + 1)} := by
      -- By the Chinese Remainder Theorem, there exists a polynomial $H$ such that $H \equiv T_j \pmod{(z - b_j)^{L+1}}$ for all $j$. This follows from the fact that the ideals $(z - b_j)^{L+1}$ are pairwise coprime.
      have h_crt : ∀ j : Fin m, ∃ H_j : Polynomial ℂ, H_j - T j ∈ Ideal.span {(Polynomial.X - Polynomial.C (b j)) ^ (L + 1)} ∧ ∀ k : Fin m, k ≠ j → H_j ∈ Ideal.span {(Polynomial.X - Polynomial.C (b k)) ^ (L + 1)} := by
        -- For each $j$, let $Q_j = \prod_{k \neq j} (z - b_k)^{L+1}$.
        set Q : Fin m → Polynomial ℂ := fun j => ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (b k)) ^ (L + 1);
        -- Since $Q_j$ and $(z - b_j)^{L+1}$ are coprime, there exists a polynomial $R_j$ such that $Q_j R_j \equiv 1 \pmod{(z - b_j)^{L+1}}$.
        have h_coprime : ∀ j : Fin m, ∃ R_j : Polynomial ℂ, Q j * R_j - 1 ∈ Ideal.span {(Polynomial.X - Polynomial.C (b j)) ^ (L + 1)} := by
          -- Since $Q_j$ and $(z - b_j)^{L+1}$ are coprime, there exists a polynomial $R_j$ such that $Q_j R_j \equiv 1 \pmod{(z - b_j)^{L+1}}$ by Bezout's identity.
          intro j
          have h_coprime : IsCoprime (Q j) ((Polynomial.X - Polynomial.C (b j)) ^ (L + 1)) := by
            refine' IsCoprime.prod_left fun k hk => _;
            exact IsCoprime.pow ( Polynomial.irreducible_X_sub_C ( b k ) |> fun h => h.coprime_iff_not_dvd.mpr fun h' => by have := Polynomial.dvd_iff_isRoot.mp h'; simp_all +decide [ sub_eq_iff_eq_add, hb.eq_iff ] );
          rcases h_coprime with ⟨ R_j, S_j, h ⟩;
          exact ⟨ R_j, by rw [ Ideal.mem_span_singleton ] ; exact ⟨ -S_j, by linear_combination' h ⟩ ⟩;
        intro j
        obtain ⟨R_j, hR_j⟩ := h_coprime j
        use Q j * R_j * T j;
        exact ⟨ by convert Ideal.mul_mem_right ( T j ) _ hR_j using 1; ring, fun k hk => Ideal.mem_span_singleton.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
      choose H hH₁ hH₂ using h_crt;
      use ∑ j, H j;
      intro j; simp_all +decide [ sub_eq_iff_eq_add ] ;
      rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ) ];
      rw [ add_sub_right_comm ];
      exact Ideal.add_mem _ ( hH₁ j ) ( Ideal.sum_mem _ fun k hk => hH₂ k j ( by aesop ) );
    -- Therefore, $H^{(\ell)}(b_j) = T_j^{(\ell)}(b_j) = \gamma_{j,\ell}$ for all $j$ and $\ell$.
    have h_deriv : ∀ j : Fin m, ∀ l : Fin (L + 1), (Polynomial.derivative^[l.val] H).eval (b j) = (Polynomial.derivative^[l.val] (T j)).eval (b j) := by
      intro j l
      have h_div : (Polynomial.X - Polynomial.C (b j)) ^ (L + 1) ∣ H - T j := by
        exact Ideal.mem_span_singleton.mp ( hH j );
      obtain ⟨ q, hq ⟩ := h_div; replace hq := congr_arg ( Polynomial.derivative^[l.val] ) hq; simp_all +decide [ Polynomial.derivative_pow ] ;
      replace hq := congr_arg ( Polynomial.eval ( b j ) ) hq ; simp_all +decide [ Polynomial.iterate_derivative_mul, Polynomial.iterate_derivative_X_sub_pow ] ;
      simp_all +decide [ Polynomial.eval_finset_sum, sub_eq_iff_eq_add ];
      exact Finset.sum_eq_zero fun x hx => by rw [ zero_pow ( Nat.sub_ne_zero_of_lt ( by linarith [ Finset.mem_range.mp hx, Nat.sub_le ( l : ℕ ) x, Fin.is_lt l ] ) ) ] ; ring;
    refine' ⟨ H, fun j l => h_deriv j l ▸ _ ⟩;
    rw [ Polynomial.iterate_derivative_sum ];
    rw [ Polynomial.eval_finset_sum, Finset.sum_eq_single l ] <;> norm_num;
    · erw [ Polynomial.iterate_derivative_X_sub_pow ] ; norm_num;
      simp +decide [ Nat.descFactorial_self, Nat.factorial_ne_zero ];
    · intro k hk; erw [ Polynomial.iterate_derivative_X_sub_pow ] ;
      cases lt_or_gt_of_ne ( by simpa [ Fin.ext_iff ] using hk ) <;> simp_all +decide [ Nat.descFactorial_eq_zero_iff_lt ];
      exact Or.inr <| Or.inr <| Nat.sub_ne_zero_of_lt <| by simpa [ Fin.ext_iff ] using ‹l < k›;
  exact absurd ( h_not_ex H ) ( by push_neg; exact hH )

/-
If a function is analytic on a neighborhood of a closed disk, it is analytic on a slightly larger open disk.
-/
open Complex Polynomial Set Filter Topology Metric

lemma analytic_on_larger_disk (r : ℝ) (hr : r > 0) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 r)) :
    ∃ ρ > r, AnalyticOn ℂ f (Metric.ball 0 ρ) := by
  -- Since $f$ is analytic on the closed disk $\overline{D(0,r)}$, there exists an open set $U$ containing $\overline{D(0,r)}$ on which $f$ is analytic.
  obtain ⟨U, hU_open, hU_contain, hU_analytic⟩ : ∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ AnalyticOn ℂ f U := by
    exact ⟨ { z | AnalyticAt ℂ f z }, isOpen_iff_mem_nhds.mpr fun z hz => hz.eventually_analyticAt, fun z hz => hf z hz, fun z hz => hz.analyticWithinAt ⟩;
  -- Since $\overline{D(0,r)}$ is compact and contained in $U$, there exists $\delta > 0$ such that the $\delta$-neighborhood of $\overline{D(0,r)}$ is contained in $U$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, Metric.thickening δ (Metric.closedBall 0 r) ⊆ U := by
    apply_rules [ IsCompact.exists_thickening_subset_open ];
    exact ProperSpace.isCompact_closedBall _ _;
  refine' ⟨ r + δ / 2, by linarith, hU_analytic.mono _ ⟩;
  refine' Set.Subset.trans _ hδ;
  intro x hx; simp_all +decide [ Metric.mem_thickening_iff ];
  by_cases hx' : ‖x‖ ≤ r;
  · exact ⟨ x, hx', by simpa using hδ_pos ⟩;
  · refine' ⟨ r • ( ‖x‖⁻¹ • x ), _, _ ⟩ <;> simp_all +decide [ norm_smul, abs_of_nonneg ];
    · rw [ abs_of_pos hr, inv_mul_cancel₀ ( by linarith ), mul_one ];
    · rw [ dist_eq_norm ] ; ring_nf;
      rw [ show x - x * ( r : ℂ ) * ( ‖x‖ : ℂ ) ⁻¹ = x * ( 1 - ( r : ℂ ) * ( ‖x‖ : ℂ ) ⁻¹ ) by ring, norm_mul ];
      norm_cast ; norm_num [ show ‖x‖ ≠ 0 by linarith ];
      cases abs_cases ( 1 - r * ‖x‖⁻¹ ) <;> nlinarith [ mul_inv_cancel₀ ( by linarith : ‖x‖ ≠ 0 ) ]

/-
If a function $f$ is analytic on a neighborhood of the closed disk of radius $r$, then for any $\epsilon > 0$, it can be uniformly approximated by a polynomial on that disk.
-/
open Complex Polynomial Set Filter Topology Metric

lemma polynomial_approx_on_disk (r : ℝ) (hr : r > 0) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 r)) (ε : ℝ) (hε : ε > 0) :
    ∃ P : Polynomial ℂ, ∀ z, norm z ≤ r → norm (f z - P.eval z) < ε := by
  by_contra h;
  -- Let's choose $\rho > r$ such that $f$ is analytic on $B(0, \rho)$.
  obtain ⟨ρ, hρ_pos, hρ⟩ : ∃ ρ > r, AnalyticOn ℂ f (Metric.ball 0 ρ) := by
    exact analytic_on_larger_disk r hr f hf;
  -- Choose $\rho'$ such that $r < \rho' < \rho$. Then $f$ is differentiable on $\overline{B}(0, \rho')$.
  obtain ⟨ρ', hρ'_pos, hρ'_lt⟩ : ∃ ρ' > r, ρ' < ρ ∧ DifferentiableOn ℂ f (Metric.closedBall 0 ρ') := by
    exact ⟨ ( r + ρ ) / 2, by linarith, by linarith, hρ.differentiableOn.mono ( Metric.closedBall_subset_ball <| by linarith ) ⟩;
  -- By the properties of power series, the partial sums of the power series converge uniformly to $f$ on $\overline{B}(0, r)$.
  have h_uniform : ∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ, ‖z‖ ≤ r → ‖f z - (cauchyPowerSeries f 0 ρ').partialSum n z‖ < ε := by
    have h_uniform : TendstoUniformlyOn (fun n z => (cauchyPowerSeries f 0 ρ').partialSum n z) (fun z => f z) Filter.atTop (Metric.closedBall 0 r) := by
      have h_uniform : TendstoUniformlyOn (fun n z => (cauchyPowerSeries f 0 ρ').partialSum n z) (fun z => f z) Filter.atTop (Metric.ball 0 (r + (ρ' - r) / 2)) := by
        have := @DifferentiableOn.hasFPowerSeriesOnBall;
        have := @this ℂ _ _ _ ⟨ ρ', by linarith ⟩ 0 f;
        specialize this hρ'_lt.2 ( show 0 < ρ' by linarith );
        convert this.tendstoUniformlyOn _;
        all_goals norm_num;
        rotate_left;
        exacts [ ⟨ r + ( ρ' - r ) / 2, by linarith ⟩, by exact Subtype.mk_lt_mk.mpr ( by linarith ), by norm_num ];
      exact h_uniform.mono <| Metric.closedBall_subset_ball <| by linarith;
    rw [ Metric.tendstoUniformlyOn_iff ] at h_uniform;
    exact Filter.eventually_atTop.mp ( h_uniform ε hε ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn z hz => hN n hn z <| mem_closedBall_zero_iff.mpr hz ⟩;
  obtain ⟨ N, hN ⟩ := h_uniform;
  -- The partial sums of the power series are polynomials.
  have h_partial_sum_poly : ∀ n : ℕ, ∃ P : Polynomial ℂ, ∀ z : ℂ, (cauchyPowerSeries f 0 ρ').partialSum n z = P.eval z := by
    intro n; use ∑ i ∈ Finset.range n, Polynomial.C ((cauchyPowerSeries f 0 ρ').coeff i) * Polynomial.X ^ i; simp +decide [ Polynomial.eval_finset_sum ] ;
    simp +decide [ FormalMultilinearSeries.partialSum ];
    exact fun z => Finset.sum_congr rfl fun _ _ => mul_comm _ _;
  exact h <| by obtain ⟨ P, hP ⟩ := h_partial_sum_poly N; exact ⟨ P, fun z hz => by simpa only [ hP ] using hN N le_rfl z hz ⟩ ;

/-
If a polynomial $P$ has vanishing derivatives up to order $L$ at a point $a$, then $(X-a)^{L+1}$ divides $P$.
-/
open Complex Polynomial Set Filter Topology Metric

lemma polynomial_divisible_by_pow_sub_C (P : Polynomial ℂ) (a : ℂ) (L : ℕ)
    (h : ∀ l : Fin (L + 1), (derivative^[l] P).eval a = 0) :
    (X - C a)^(L+1) ∣ P := by
  -- By definition of polynomial derivative, if $(X - a)^{L+1}$ divides $P$, then $P^{(l)}(a) = 0$ for all $l \leq L$.
  have h_deriv_zero : ∀ l : ℕ, l ≤ L → Polynomial.eval a (Polynomial.derivative^[l] P) = 0 := by
    exact fun l hl => h ⟨ l, Nat.lt_succ_of_le hl ⟩;
  refine' Polynomial.X_sub_C_pow_dvd_iff.mpr _;
  -- By definition of polynomial composition, if $(X - a)^{L+1}$ divides $P$, then $P^{(l)}(a) = 0$ for all $l \leq L$.
  have h_comp_deriv_zero : ∀ l : ℕ, l ≤ L → Polynomial.eval 0 (Polynomial.derivative^[l] (P.comp (Polynomial.X + Polynomial.C a))) = 0 := by
    -- By definition of polynomial composition, we know that $(P.comp (Polynomial.X + Polynomial.C a))^{(l)}(0) = P^{(l)}(a)$.
    have h_comp_deriv : ∀ l : ℕ, Polynomial.derivative^[l] (P.comp (Polynomial.X + Polynomial.C a)) = (Polynomial.derivative^[l] P).comp (Polynomial.X + Polynomial.C a) := by
      intro l; induction l <;> simp_all +decide [ Function.iterate_succ_apply', Polynomial.derivative_comp ] ;
    aesop;
  rw [ Polynomial.X_pow_dvd_iff ];
  intro d hd; specialize h_comp_deriv_zero d ( Nat.le_of_lt_succ hd ) ; rw [ Polynomial.eval ] at h_comp_deriv_zero; simp_all +decide [ Polynomial.coeff_iterate_derivative ] ;

/-
If a polynomial $P$ vanishes to order $L$ at each point of a finite set $A$, then it is divisible by $\prod_{a \in A} (X-a)^{L+1}$.
-/
open Complex Polynomial Set Filter Topology Metric

lemma polynomial_divisible_by_prod_pow_sub_C (P : Polynomial ℂ) (A : Finset ℂ) (L : ℕ)
    (h : ∀ a ∈ A, ∀ l : Fin (L + 1), (derivative^[l] P).eval a = 0) :
    (∏ a ∈ A, (X - C a)^(L+1)) ∣ P := by
  refine' Finset.prod_dvd_of_coprime _ _;
  · intro a ha b hb hab; exact IsCoprime.pow ( Polynomial.irreducible_X_sub_C _ |> fun h => h.coprime_iff_not_dvd.mpr fun h' => hab <| by simpa [ sub_eq_iff_eq_add ] using Polynomial.dvd_iff_isRoot.mp h' ) ;
  · exact fun i a => polynomial_divisible_by_pow_sub_C P i L (h i a)

/-
Given a finite set $S \subset \mathbb{C}$ and values $\gamma_{s,l}$, there exists a polynomial $H$ such that $H^{(l)}(s) = \gamma_{s,l}$ for all $s \in S$ and $0 \le l \le L$.
-/
open Complex Polynomial Set Filter Topology Metric

lemma hermite_interpolation_finset (S : Finset ℂ) (L : ℕ) (γ : S → Fin (L + 1) → ℂ) :
    ∃ H : Polynomial ℂ, ∀ (s : S) (l : Fin (L + 1)), (derivative^[l] H).eval (s : ℂ) = γ s l := by
  -- Let $m = |S|$. Since $S$ is a finite set, there exists a bijection $e : \{0, \dots, m-1\} \to S$.
  obtain ⟨e, he⟩ : ∃ e : Fin S.card ≃ S, True := by
    exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
  -- Define $\gamma' : \{0, \dots, m-1\} \to \{0, \dots, L\} \to \mathbb{C}$ by $\gamma'(j, l) = \gamma(e(j), l)$.
  set γ' : Fin S.card → Fin (L + 1) → ℂ := fun j l => γ (e j) l;
  -- Apply `hermite_interpolation` to $b$ and $\gamma'$ to obtain a polynomial $H$.
  obtain ⟨H, hH⟩ : ∃ H : Polynomial ℂ, ∀ (j : Fin S.card) (l : Fin (L + 1)), (Polynomial.derivative^[l] H).eval (e j).val = γ' j l := by
    apply hermite_interpolation;
    exact Subtype.coe_injective.comp e.injective;
  use H; intro s l; specialize hH ( e.symm s ) l; aesop;

/-
Given disjoint finite sets $A, B$ and values $\beta$ on $B$, there exists a polynomial $P_0$ that vanishes to order $L$ on $A$, matches $\beta$ on $B$, and is divisible by $\prod_{a \in A} (X-a)^{L+1}$.
-/
open Complex Polynomial Set Filter Topology Metric

lemma exists_poly_interpolating_and_divisible (A B : Finset ℂ) (hAB : Disjoint A B) (L : ℕ)
    (β : {x // x ∈ B} → Fin (L + 1) → ℂ) :
    ∃ P₀ H : Polynomial ℂ,
      (∀ a ∈ A, ∀ l : Fin (L + 1), (derivative^[l] P₀).eval a = 0) ∧
      (∀ b, (hb : b ∈ B) → ∀ l : Fin (L + 1), (derivative^[l] P₀).eval b = β ⟨b, hb⟩ l) ∧
      P₀ = (∏ a ∈ A, (X - C a)^(L+1)) * H := by
  -- Let $S = A \cup B$. Define $\gamma : S \to \{0, \dots, L\} \to \mathbb{C}$ by $\gamma(s, l) = 0$ if $s \in A$, and $\gamma(s, l) = \beta(s, l)$ if $s \in B$.
  let S := (A ∪ B).toSet
  let γ : S → Fin (L + 1) → ℂ := fun s l => if hs : s.val ∈ A then 0 else β ⟨s.val, by aesop⟩ l;
  -- Use `hermite_interpolation_finset` on $S$ to find a polynomial $P_0$ such that $P_0^{(\ell)}(s) = \gamma(s, l)$ for all $s \in S$.
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Polynomial ℂ, ∀ (s : S) (l : Fin (L + 1)), (Polynomial.derivative^[l] P₀).eval (s : ℂ) = γ s l := by
    apply hermite_interpolation_finset;
  refine' ⟨ P₀, _ ⟩;
  simp +zetaDelta at *;
  refine' ⟨ fun a ha l => _, fun b hb l => _, _ ⟩;
  · simpa [ ha ] using hP₀ a ( Or.inl ha ) l;
  · simpa [ show b ∉ A from fun h => Finset.disjoint_left.mp hAB h hb ] using hP₀ b ( Or.inr hb ) l;
  · apply_rules [ polynomial_divisible_by_prod_pow_sub_C ];
    intro a ha l; specialize hP₀ a ( Or.inl ha ) l; aesop;

/-
Definitions of polynomial function and transcendental entire function.
-/
def IsPolynomial (f : ℂ → ℂ) : Prop := ∃ P : Polynomial ℂ, ∀ z, f z = P.eval z

def TranscendentalEntire (f : ℂ → ℂ) : Prop := Differentiable ℂ f ∧ ¬ IsPolynomial f

/-
A set with no finite limit point in $\mathbb{C}$ is countable.
-/
lemma countable_of_hasNoFiniteLimitPoint (S : Set ℂ) (h : HasNoFiniteLimitPoint S) : S.Countable := by
  -- Since $S$ has no finite limit point, its intersection with any compact set is finite.
  have h_compact_finite : ∀ n : ℕ, (S ∩ Metric.closedBall 0 (n : ℝ)).Finite := by
    exact fun n => h _ <| ProperSpace.isCompact_closedBall _ _;
  -- Since $S$ has no finite limit point, its intersection with any compact set is finite. Hence, $S$ is countable.
  have h_countable : S = ⋃ n : ℕ, S ∩ Metric.closedBall 0 (n : ℝ) := by
    ext z
    simp [h_compact_finite];
    exact fun hz => ⟨ ⌈‖z‖⌉₊, Nat.le_ceil _ ⟩;
  exact h_countable ▸ Set.countable_iUnion fun n => Set.Finite.countable ( h_compact_finite n )

/-
Existence of a sequence of radii avoiding the sets $S_n$.
-/
lemma exists_radii (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n)) :
    ∃ r : ℕ → ℝ, StrictMono r ∧ (∀ n, r n > n + 1) ∧
    ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅ := by
      -- Fix an $n$ and define the set of bad radii as $BadR = \{ |z| : z \in \bigcup_{j \le n+1} S_j \}$.
      have h_bad_rad (n : ℕ) : Set.Countable {‖z‖ | z ∈ ⋃ j ∈ Finset.range (n + 2), S j} := by
        have h_countable_union : ∀ n, Set.Countable (⋃ j ∈ Finset.range (n + 2), S j) := by
          exact fun n => Set.Countable.biUnion ( Finset.countable_toSet _ ) fun j hj => countable_of_hasNoFiniteLimitPoint _ ( hS j );
        exact Set.Countable.image ( h_countable_union n ) _;
      -- Since $BadR$ is countable, we can choose $r_n$ in the interval $(n+1, n+2)$ for each $n$.
      have hr_exists : ∀ n : ℕ, ∃ r_n : ℝ, (n + 1 : ℝ) < r_n ∧ r_n < (n + 2 : ℝ) ∧ r_n ∉ {‖z‖ | z ∈ ⋃ j ∈ Finset.range (n + 2), S j} := by
        intro n;
        contrapose! h_bad_rad;
        exact ⟨ n, fun h => absurd ( h.mono <| show { x | ∃ z ∈ ⋃ j ∈ Finset.range ( n + 2 ), S j, ‖z‖ = x } ⊇ Set.Ioo ( n + 1 : ℝ ) ( n + 2 ) from fun x hx => h_bad_rad x hx.1 hx.2 ) ( by exact fun h' => absurd ( h'.measure_zero <| MeasureTheory.MeasureSpace.volume ) ( by simp +decide [ Set.Ioo_def ] ) ) ⟩;
      choose r hr using hr_exists;
      use r;
      exact ⟨ strictMono_nat_of_lt_succ fun n => by have := hr n; have := hr ( n + 1 ) ; norm_num at * ; linarith, fun n => hr n |>.1, fun n => Set.eq_empty_of_forall_notMem fun z hz => hr n |>.2.2 ⟨ z, hz.2, hz.1 ⟩ ⟩

/-
The annulus $\{z \in \mathbb{C} : r_1 < |z| < r_2\}$ is uncountable.
-/
lemma annulus_uncountable (r₁ r₂ : ℝ) (h₀ : 0 ≤ r₁) (h : r₁ < r₂) :
    ¬ Set.Countable {z : ℂ | r₁ < ‖z‖ ∧ ‖z‖ < r₂} := by
      by_contra h;
      have := h.image Complex.re;
      refine' absurd ( this.mono _ ) _;
      exact Set.Ioo ( r₁ : ℝ ) r₂;
      · exact fun x hx => ⟨ x, ⟨ by simpa [ abs_of_nonneg ( show 0 ≤ x by linarith [ hx.1 ] ) ] using hx.1, by simpa [ abs_of_nonneg ( show 0 ≤ x by linarith [ hx.1 ] ) ] using hx.2 ⟩, rfl ⟩;
      · exact fun H => absurd ( H.measure_zero <| MeasureTheory.MeasureSpace.volume ) ( by simp +decide [ *, le_of_lt ] )

/-
Existence of auxiliary points $c_n$ in the annuli defined by $r_n$, avoiding $\Sigma$.
-/
lemma exists_auxiliary_points (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) :
    ∃ c : ℕ → ℂ, (∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) ∧
    (∀ n, c n ∉ ⋃ j, S j) ∧ Function.Injective c := by
      -- For each $n$, the annulus $A_n = \{z : r_n < |z| < r_{n+1}\}$ is uncountable by `annulus_uncountable`.
      have h_annulus_uncountable : ∀ n, ¬ Set.Countable {z : ℂ | r n < ‖z‖ ∧ ‖z‖ < r (n + 1)} := by
        intro n hn; have := @annulus_uncountable ( r n ) ( r ( n + 1 ) ) ( hr_pos n ) ( by linarith [ hr n.lt_succ_self ] ) ; aesop;
      -- The set $\Sigma = \bigcup_j S_j$ is countable because each $S_j$ is countable (as it has no finite limit point).
      have h_sigma_countable : Set.Countable (⋃ j, S j) := by
        exact Set.countable_iUnion fun n => countable_of_hasNoFiniteLimitPoint _ <| hS n;
      -- Thus $A_n \setminus \Sigma$ is non-empty. Choose $c_n \in A_n \setminus \Sigma$.
      have h_annulus_minus_sigma_nonempty : ∀ n, ∃ c_n : ℂ, r n < ‖c_n‖ ∧ ‖c_n‖ < r (n + 1) ∧ c_n ∉ ⋃ j, S j := by
        intro n;
        contrapose! h_annulus_uncountable;
        exact ⟨ n, Set.Countable.mono ( fun x hx => h_annulus_uncountable x hx.1 hx.2 ) h_sigma_countable ⟩;
      choose c hc₁ hc₂ hc₃ using h_annulus_minus_sigma_nonempty;
      use c;
      exact ⟨ fun n => ⟨ hc₁ n, hc₂ n ⟩, hc₃, fun m n hmn => le_antisymm ( le_of_not_gt fun hmn' => by have := hc₁ m; have := hc₂ m; have := hc₁ n; have := hc₂ n; norm_num [ hmn.symm ] at *; linarith [ hr.monotone ( Nat.succ_le_of_lt hmn' ) ] ) ( le_of_not_gt fun hmn' => by have := hc₁ m; have := hc₂ m; have := hc₁ n; have := hc₂ n; norm_num [ hmn.symm ] at *; linarith [ hr.monotone ( Nat.succ_le_of_lt hmn' ) ] ) ⟩

/-
Lemma 3: Small polynomial with prescribed jets.
-/
lemma small_polynomial_with_prescribed_jets (r : ℝ) (hr : 0 < r)
    (A B : Finset ℂ) (hA : ∀ a ∈ A, ‖a‖ < r) (hB : ∀ b ∈ B, r < ‖b‖)
    (L : ℕ) (β : B → Fin (L + 1) → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Polynomial ℂ,
      (∀ a ∈ A, ∀ l : Fin (L + 1), (derivative^[l] P).eval a = 0) ∧
      (∀ b, (hb : b ∈ B) → ∀ l : Fin (L + 1), (derivative^[l] P).eval b = β ⟨b, hb⟩ l) ∧
      (∀ z, ‖z‖ ≤ r → ‖P.eval z‖ < ε) := by
        -- Let $U(z) = \prod_{a \in A} (z-a)^{L+1}$ and $V(z) = \prod_{b \in B} (z-b)^{L+1}$.
        set U : Polynomial ℂ := Finset.prod A (fun a => (Polynomial.X - Polynomial.C a) ^ (L + 1))
        set V : Polynomial ℂ := Finset.prod B (fun b => (Polynomial.X - Polynomial.C b) ^ (L + 1));
        -- By Lemma `exists_poly_interpolating_and_divisible`, there exists a polynomial $P_0$ such that $P_0^{(\ell)}(a)=0$ for $a \in A$ and $P_0^{(\ell)}(b)=\beta_{b,\ell}$ for $b \in B$.
        obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Polynomial ℂ, (∀ a ∈ A, ∀ l : Fin (L + 1), (Polynomial.derivative^[l] P₀).eval a = 0) ∧ (∀ b, (hb : b ∈ B) → ∀ l : Fin (L + 1), (Polynomial.derivative^[l] P₀).eval b = β ⟨b, hb⟩ l) ∧ P₀ = U * (P₀ / U) := by
          -- Apply the lemma `exists_poly_interpolating_and_divisible` to obtain the polynomial $P_0$.
          obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Polynomial ℂ, (∀ a ∈ A, ∀ l : Fin (L + 1), (Polynomial.derivative^[l] P₀).eval a = 0) ∧ (∀ b, (hb : b ∈ B) → ∀ l : Fin (L + 1), (Polynomial.derivative^[l] P₀).eval b = β ⟨b, hb⟩ l) ∧ U ∣ P₀ := by
            have := exists_poly_interpolating_and_divisible A B;
            exact Exists.elim ( this ( Finset.disjoint_left.mpr fun x hx₁ hx₂ => by have := hA x hx₁; have := hB x hx₂; linarith ) L β ) fun P₀ hP₀ => Exists.elim hP₀ fun H hH => ⟨ P₀, hH.1, hH.2.1, hH.2.2.symm ▸ dvd_mul_right _ _ ⟩;
          refine' ⟨ P₀, hP₀.1, hP₀.2.1, _ ⟩;
          rw [ EuclideanDomain.mul_div_cancel' _ hP₀.2.2 ];
          exact Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ <| Polynomial.X_sub_C_ne_zero x;
        -- Let $H(z) = P_0(z) / U(z)$.
        set H : Polynomial ℂ := P₀ / U;
        -- By Runge's theorem, there exists a polynomial $W$ such that $|W(z) - (-H(z)/V(z))| < \varepsilon / M$ on $\overline{D(0,r)}$, where $M = \sup_{|z| \le r} |U(z)V(z)|$.
        obtain ⟨W, hW⟩ : ∃ W : Polynomial ℂ, ∀ z, ‖z‖ ≤ r → ‖Polynomial.eval z W - (-Polynomial.eval z H / Polynomial.eval z V)‖ < ε / (sSup {‖Polynomial.eval z (U * V)‖ | z ∈ Metric.closedBall 0 r} + 1) := by
          -- The function $G(z) = -H(z)/V(z)$ is holomorphic on a neighborhood of $\overline{D(0,r)}$.
          have hG_holomorphic : AnalyticOnNhd ℂ (fun z => -Polynomial.eval z H / Polynomial.eval z V) (Metric.closedBall 0 r) := by
            intro z hz;
            refine' AnalyticAt.div _ _ _;
            · apply_rules [ AnalyticAt.neg, AnalyticAt.mul, analyticAt_id, analyticAt_const ];
              apply_rules [ Differentiable.analyticAt, Polynomial.differentiable ];
            · exact Polynomial.differentiable _ |> Differentiable.analyticAt <| _;
            · simp +zetaDelta at *;
              norm_num [ Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero ];
              exact fun h => by linarith [ hB z h ] ;
          have := polynomial_approx_on_disk r hr ( fun z => -Polynomial.eval z H / Polynomial.eval z V ) hG_holomorphic ( ε / ( sSup { ‖Polynomial.eval z ( U * V )‖ | z ∈ Metric.closedBall 0 r } + 1 ) ) ( div_pos hε ( add_pos_of_nonneg_of_pos ( by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ z, hz, rfl ⟩ ; positivity ) zero_lt_one ) );
          exact ⟨ this.choose, fun z hz => by rw [ norm_sub_rev ] ; exact this.choose_spec z hz ⟩;
        refine' ⟨ P₀ + U * V * W, _, _, _ ⟩ <;> norm_num at *;
        · intro a ha l;
          -- Since $U(a) = 0$, we have that $U * V * W$ is divisible by $(X - a)^{L+1}$.
          have h_div : (Polynomial.X - Polynomial.C a)^(L+1) ∣ U * V * W := by
            exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( Finset.dvd_prod_of_mem _ ha ) _ ) _;
          -- Since $U * V * W$ is divisible by $(X - a)^{L+1}$, its $l$-th derivative at $a$ is zero.
          have h_deriv_zero : ∀ l : ℕ, l ≤ L → Polynomial.eval a (Polynomial.derivative^[l] (U * V * W)) = 0 := by
            intro l hl; obtain ⟨ Q, hQ ⟩ := h_div; norm_num [ hQ, Polynomial.iterate_derivative_mul ] ;
            rw [ Polynomial.eval_finset_sum, Finset.sum_eq_zero ] ; norm_num;
            intro x hx; right; left; erw [ Polynomial.iterate_derivative_X_sub_pow ] ; norm_num [ Nat.choose_eq_zero_of_lt ( show x < L + 1 from by linarith ) ] ;
            exact Or.inr ( Nat.sub_ne_zero_of_lt ( by omega ) );
          rw [ hP₀.1 a ha l, h_deriv_zero l ( Fin.is_le l ), add_zero ];
        · intro b hb l; rw [ ← hP₀.2.1 b hb l ] ; simp +decide [ ← hP₀.2.2, mul_assoc, Polynomial.derivative_mul ] ;
          rw [ Polynomial.iterate_derivative_mul ];
          rw [ Polynomial.eval_finset_sum, Finset.sum_eq_zero ] ; intros ; norm_num [ Polynomial.eval_prod, Finset.prod_eq_zero hb ];
          refine' Or.inr <| Or.inr <| _;
          rw [ Polynomial.iterate_derivative_mul ];
          rw [ Polynomial.eval_finset_sum, Finset.sum_eq_zero ] ; intros ; norm_num [ Polynomial.eval_prod, Finset.prod_eq_zero hb ];
          refine' Or.inr <| Or.inl <| _;
          -- Since $V(z) = \prod_{b \in B} (z-b)^{L+1}$, we have $V^{(k)}(b) = 0$ for any $k \leq L$.
          have hV_deriv_zero : ∀ k ≤ L, Polynomial.eval b (Polynomial.derivative^[k] V) = 0 := by
            intro k hk; rw [ show V = ( ∏ b ∈ B, ( Polynomial.X - Polynomial.C b ) ^ ( L + 1 ) ) from rfl ] ; rw [ Finset.prod_eq_prod_diff_singleton_mul hb ] ;
            rw [ Polynomial.iterate_derivative_mul ];
            rw [ Polynomial.eval_finset_sum, Finset.sum_eq_zero ] ; intros ; norm_num [ Polynomial.derivative_pow ];
            erw [ Polynomial.iterate_derivative_X_sub_pow ] ; norm_num;
            exact Or.inr <| Or.inr <| Or.inr <| Nat.sub_ne_zero_of_lt <| by linarith [ Finset.mem_range.mp ‹_› ] ;
          exact hV_deriv_zero _ ( Nat.le_trans ( Nat.sub_le _ _ ) ( Nat.le_trans ( Finset.mem_range_succ_iff.mp ‹_› ) ( Nat.le_of_lt_succ ( Fin.is_lt l ) ) ) );
        · intro z hz
          have h_eval : Polynomial.eval z P₀ + Polynomial.eval z U * Polynomial.eval z V * Polynomial.eval z W = Polynomial.eval z U * Polynomial.eval z V * (Polynomial.eval z W + Polynomial.eval z H / Polynomial.eval z V) := by
            rw [ hP₀.2.2 ] ; ring_nf;
            by_cases hV : Polynomial.eval z V = 0 <;> simp +decide [ hV, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf
            · rw [ Polynomial.eval_prod ] at hV; simp +decide [ Finset.prod_eq_zero_iff, sub_eq_zero ] at hV;
              exact absurd ( hB z hV ) ( by linarith );
            · ring;
          -- Since $|W(z) - (-H(z)/V(z))| < \varepsilon / M$, we have $|U(z)V(z)(W(z) + H(z)/V(z))| < \varepsilon$.
          have h_bound : ‖Polynomial.eval z U * Polynomial.eval z V * (Polynomial.eval z W + Polynomial.eval z H / Polynomial.eval z V)‖ ≤ ‖Polynomial.eval z U * Polynomial.eval z V‖ * (ε / (sSup {‖Polynomial.eval z (U * V)‖ | z ∈ Metric.closedBall 0 r} + 1)) := by
            norm_num [ div_eq_mul_inv ] at *;
            exact mul_le_mul_of_nonneg_left ( le_of_lt ( hW z hz ) ) ( by positivity );
          refine' lt_of_le_of_lt ( h_eval ▸ h_bound ) _;
          rw [ mul_div, div_lt_iff₀ ] <;> norm_num at *;
          · rw [ mul_comm ] ; gcongr;
            refine' lt_of_le_of_lt ( le_csSup _ _ ) ( lt_add_one _ );
            · -- The set {‖eval z U‖ * ‖eval z V‖ | z ∈ Metric.closedBall 0 r} is bounded above because U and V are polynomials and the closed ball is compact.
              have h_bdd_above : BddAbove (Set.image (fun z => ‖Polynomial.eval z U‖ * ‖Polynomial.eval z V‖) (Metric.closedBall 0 r)) := by
                exact IsCompact.bddAbove ( isCompact_closedBall 0 r |> IsCompact.image <| Continuous.mul ( Polynomial.continuous _ |> Continuous.norm ) ( Polynomial.continuous _ |> Continuous.norm ) );
              simpa only [ Metric.closedBall, dist_zero_right ] using h_bdd_above;
            · exact ⟨ z, hz, rfl ⟩;
          · exact add_pos_of_nonneg_of_pos ( by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ z, hz, rfl ⟩ ; positivity ) zero_lt_one

/-
Intersection of a set with no finite limit point with a ball is finite.
-/
lemma finite_intersection_ball (S : Set ℂ) (h : HasNoFiniteLimitPoint S) (r : ℝ) :
    (S ∩ Metric.ball 0 r).Finite := by
      have := h ( Metric.closedBall 0 r );
      exact Set.Finite.subset ( this ( ProperSpace.isCompact_closedBall _ _ ) ) fun x hx => ⟨ hx.1, hx.2.out.le ⟩

/-
Existence of a correction polynomial $T_{next}$ with prescribed properties.
-/
lemma exists_correction_polynomial (m : ℕ) (hm : m > 0)
    (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1))
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (k_prev : ℕ)
    (F_prev : Polynomial ℂ)
    (k_next : ℕ) (hk_next : k_next > k_prev) :
    ∃ T_next : Polynomial ℂ,
      (∀ z, ‖z‖ ≤ r (m-1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
      (∀ i ≤ m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m-1)), ∀ l ≤ k_next, (derivative^[l] T_next).eval z = 0) ∧
      (∀ i < m-1, ∀ l ≤ k_next, (derivative^[l] T_next).eval (c i) = 0) ∧
      (∀ i ≤ m, ∀ z ∈ S i ∩ {z | r (m-1) < ‖z‖ ∧ ‖z‖ < r m}, ∀ l ≤ k_next, (derivative^[l] T_next).eval z = -(derivative^[l] F_prev).eval z) ∧
      (∀ l ≤ k_next, (derivative^[l] T_next).eval (c (m-1)) = if l = k_prev then 1 - (derivative^[l] F_prev).eval (c (m-1)) else -(derivative^[l] F_prev).eval (c (m-1))) := by
        have h_finite : Set.Finite (⋃ i ≤ m, S i ∩ Metric.ball 0 (r (m - 1))) ∧ Set.Finite (⋃ i ≤ m, S i ∩ {z | r (m - 1) < ‖z‖ ∧ ‖z‖ < r m}) := by
          constructor <;> refine' Set.Finite.biUnion ( Set.finite_Iic _ ) fun i hi => _;
          · have := hS i;
            exact this ( Metric.closedBall 0 ( r ( m - 1 ) ) ) ( ProperSpace.isCompact_closedBall _ _ ) |> Set.Finite.subset <| Set.inter_subset_inter_right _ <| Metric.ball_subset_closedBall;
          · refine' Set.Finite.subset ( hS i ( Metric.closedBall 0 ( r m ) ) ( ProperSpace.isCompact_closedBall _ _ ) ) _;
            exact fun x hx => ⟨ hx.1, mem_closedBall_zero_iff.mpr hx.2.2.le ⟩;
        have h_finite_union : Set.Finite (⋃ i ≤ m, S i ∩ Metric.ball 0 (r (m - 1))) ∧ Set.Finite (⋃ i ≤ m, S i ∩ {z | r (m - 1) < ‖z‖ ∧ ‖z‖ < r m}) ∧ Set.Finite (Set.image c (Finset.range (m - 1))) ∧ Set.Finite {c (m - 1)} := by
          exact ⟨ h_finite.1, h_finite.2, Set.toFinite _, Set.finite_singleton _ ⟩;
        obtain ⟨A, B, hA, hB, h_disjoint, h_union⟩ : ∃ A B : Finset ℂ, (∀ a ∈ A, ‖a‖ < r (m - 1)) ∧ (∀ b ∈ B, r (m - 1) < ‖b‖) ∧ (⋃ i ≤ m, S i ∩ Metric.ball 0 (r (m - 1))) ∪ (Set.image c (Finset.range (m - 1))) = A ∧ (⋃ i ≤ m, S i ∩ {z | r (m - 1) < ‖z‖ ∧ ‖z‖ < r m}) ∪ {c (m - 1)} = B := by
          refine' ⟨ h_finite_union.1.toFinset ∪ Finset.image c ( Finset.range ( m - 1 ) ), h_finite_union.2.1.toFinset ∪ { c ( m - 1 ) }, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
          rintro a ( ⟨ i, hi₁, hi₂, hi₃ ⟩ | ⟨ i, hi₁, rfl ⟩ ) <;> [ exact hi₃; exact lt_of_lt_of_le ( hc_norm i |>.2.le ) ( hr.monotone ( by omega ) ) ];
          exact lt_of_lt_of_le ( hc_norm i |>.2 ) ( hr.monotone ( by omega ) );
        -- Define the values $\beta_{b,\ell}$ for $b \in B$ and $\ell \leq k_{next}$.
        set β : B → Fin (k_next + 1) → ℂ := fun b l => if b.val = c (m - 1) ∧ l.val = k_prev then 1 - (derivative^[l.val] F_prev).eval (c (m - 1)) else - (derivative^[l.val] F_prev).eval b.val;
        obtain ⟨T_next, hT_next⟩ : ∃ T_next : Polynomial ℂ, (∀ a ∈ A, ∀ l : Fin (k_next + 1), (derivative^[l.val] T_next).eval a = 0) ∧ (∀ b : { x // x ∈ B }, ∀ l : Fin (k_next + 1), (derivative^[l.val] T_next).eval b.val = β b l) ∧ (∀ z, ‖z‖ ≤ r (m - 1) → ‖T_next.eval z‖ < 2 ^ (-m + 1 : ℝ)) := by
          have := small_polynomial_with_prescribed_jets ( r ( m - 1 ) ) ( by linarith [ hr_gt ( m - 1 ), show ( m : ℝ ) ≥ 1 by norm_cast ] ) A B hA hB k_next β ( 2 ^ ( -m + 1 : ℝ ) ) ( by positivity ) ; aesop;
        refine' ⟨ T_next, hT_next.2.2, _, _, _, _ ⟩;
        · intro i hi z hz l hl;
          exact hT_next.1 z ( h_disjoint.subset <| Or.inl <| Set.mem_iUnion₂.mpr ⟨ i, hi, hz ⟩ ) ⟨ l, by linarith ⟩;
        · intro i hi l hl;
          convert hT_next.1 ( c i ) _ ⟨ l, by linarith ⟩ using 1;
          exact h_disjoint.subset <| Set.mem_union_right _ <| Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_range.mpr hi;
        · intro i hi z hz l hl;
          have hz_in_B : z ∈ B := by
            exact h_union.subset <| Or.inl <| Set.mem_iUnion₂.mpr ⟨ i, hi, hz ⟩;
          convert hT_next.2.1 ⟨ z, hz_in_B ⟩ ⟨ l, by linarith ⟩ using 1;
          simp +zetaDelta at *;
          intro hz_eq_c hz_eq_k_prev; specialize hc_mem ( m - 1 ) i; aesop;
        · intro l hl; specialize hT_next; have := hT_next.2.1 ⟨ c ( m - 1 ), by rw [ Set.ext_iff ] at h_union; specialize h_union ( c ( m - 1 ) ) ; aesop ⟩ ⟨ l, by linarith ⟩ ; aesop;

/-
Linearity of iterated derivative.
-/
lemma iterate_derivative_add {R : Type*} [CommSemiring R] (f g : Polynomial R) (n : ℕ) :
    (derivative^[n] (f + g)) = (derivative^[n] f) + (derivative^[n] g) := by
      induction' n with n ih generalizing f g <;> simp_all +decide [ Function.iterate_succ_apply' ]

/-
Inductive step for the construction of the sequence of polynomials.
-/
lemma exists_next_step (m : ℕ) (hm : m > 0)
    (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (k : ℕ → ℕ) (hk_mono : StrictMonoOn k (Set.Iic (m-1)))
    (F_prev : Polynomial ℂ)
    (hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m-1)), (derivative^[k i] F_prev).eval z = 0)
    (hF_vals : ∀ i < m-1, (derivative^[k i] F_prev).eval (c i) = 1) :
    ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
      k_next > k (m-1) ∧ k_next > F_prev.natDegree ∧
      (∀ z, ‖z‖ ≤ r (m-1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
      let F_next := F_prev + T_next
      (∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r m), (derivative^[k i] F_next).eval z = 0) ∧
      (∀ z ∈ S m ∩ Metric.ball 0 (r m), (derivative^[k_next] F_next).eval z = 0) ∧
      (∀ i < m, (derivative^[k i] F_next).eval (c i) = 1) := by
        obtain ⟨T_next, hT_next⟩ : ∃ T_next : Polynomial ℂ, (∀ z, ‖z‖ ≤ r (m - 1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧ (∀ i ≤ m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m - 1)), ∀ l ≤ (k (m - 1) + F_prev.natDegree + 1), (derivative^[l] T_next).eval z = 0) ∧ (∀ i < m - 1, ∀ l ≤ (k (m - 1) + F_prev.natDegree + 1), (derivative^[l] T_next).eval (c i) = 0) ∧ (∀ i ≤ m, ∀ z ∈ S i ∩ {z | r (m - 1) < ‖z‖ ∧ ‖z‖ < r m}, ∀ l ≤ (k (m - 1) + F_prev.natDegree + 1), (derivative^[l] T_next).eval z = -(derivative^[l] F_prev).eval z) ∧ (∀ l ≤ (k (m - 1) + F_prev.natDegree + 1), (derivative^[l] T_next).eval (c (m - 1)) = if l = k (m - 1) then 1 - (derivative^[l] F_prev).eval (c (m - 1)) else -(derivative^[l] F_prev).eval (c (m - 1))) := by
          apply exists_correction_polynomial m hm S hS r hr hr_pos hr_gt c hc_norm hc_mem (k (m - 1)) F_prev (k (m - 1) + F_prev.natDegree + 1) (by
          linarith);
        use k ( m - 1 ) + F_prev.natDegree + 1, T_next;
        refine' ⟨ _, _, hT_next.1, _, _, _ ⟩;
        · linarith;
        · linarith;
        · intro i hi z hz
          by_cases hz_case : ‖z‖ ≤ r (m - 1);
          · simp +zetaDelta at *;
            rw [ hF_zeros i hi z hz.1 ( lt_of_le_of_ne hz_case fun h => by have := hr_avoid ( m - 1 ) ; exact this.subset ⟨ h, Set.mem_iUnion₂.mpr ⟨ i, by omega, hz.1 ⟩ ⟩ ), hT_next.2.1 i ( by omega ) z hz.1 ( lt_of_le_of_ne hz_case fun h => by have := hr_avoid ( m - 1 ) ; exact this.subset ⟨ h, Set.mem_iUnion₂.mpr ⟨ i, by omega, hz.1 ⟩ ⟩ ) ( k i ) ( by linarith [ hk_mono.le_iff_le ( show i ∈ Iic ( m - 1 ) from Nat.le_sub_one_of_lt hi ) ( show m - 1 ∈ Iic ( m - 1 ) from Nat.le_refl _ ) |>.2 ( Nat.le_sub_one_of_lt hi ) ] ) ] ; norm_num;
          · have := hT_next.2.2.2.1 i ( by linarith ) z ⟨ hz.1, ⟨ by linarith, by simpa using hz.2.out ⟩ ⟩ ( k i ) ( by linarith [ hk_mono.le_iff_le ( show i ≤ m - 1 from Nat.le_sub_one_of_lt hi ) ( show m - 1 ≤ m - 1 from le_rfl ) |>.2 ( Nat.le_sub_one_of_lt hi ) ] ) ; simp_all +decide [ Polynomial.eval_add, Function.iterate_add_apply ] ;
        · intro z hz
          have hF_prev_zero : (derivative^[k (m - 1) + F_prev.natDegree + 1] F_prev).eval z = 0 := by
            rw [ Polynomial.iterate_derivative_eq_zero ] ; aesop;
            linarith;
          by_cases hz' : ‖z‖ < r ( m - 1 ) <;> simp_all +decide [ Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C ];
          · convert hT_next.2.1 m ( by linarith ) z hz.1 hz' _ le_rfl using 1;
          · cases eq_or_lt_of_le hz' <;> simp_all +decide [ Set.ext_iff ];
            · exact False.elim <| hr_avoid ( m - 1 ) z ( by linarith ) m ( by omega ) hz.1;
            · have := hT_next.2.2.2.1 m ( by linarith ) z hz.1 ‹_› hz.2 ( k ( m - 1 ) + F_prev.natDegree + 1 ) ( by linarith ) ; aesop;
        · intro i hi; specialize hT_next; rcases lt_or_eq_of_le ( Nat.le_sub_one_of_lt hi ) <;> simp_all +decide [ Function.iterate_add_apply ] ;
          · exact hT_next.2.2.1 i ‹_› _ ( by linarith [ hk_mono.le_iff_le ( show i ≤ m - 1 from by linarith ) ( show m - 1 ≤ m - 1 from by linarith ) |>.2 ( by linarith ) ] );
          · rw [ hT_next.2.2.2.2 _ ( by linarith ) ] ; aesop

/-
Inductive step for the construction of the sequence of polynomials.
-/
lemma exists_next_step_v2 (m : ℕ) (hm : m > 0)
    (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (k : ℕ → ℕ) (hk_mono : StrictMonoOn k (Set.Iic (m-1)))
    (F_prev : Polynomial ℂ)
    (hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m-1)), (derivative^[k i] F_prev).eval z = 0)
    (hF_vals : ∀ i < m-1, (derivative^[k i] F_prev).eval (c i) = 1) :
    ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
      k_next > k (m-1) ∧ k_next > F_prev.natDegree ∧
      (∀ z, ‖z‖ ≤ r (m-1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
      let F_next := F_prev + T_next
      (∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r m), (derivative^[k i] F_next).eval z = 0) ∧
      (∀ z ∈ S m ∩ Metric.ball 0 (r m), (derivative^[k_next] F_next).eval z = 0) ∧
      (∀ i < m, (derivative^[k i] F_next).eval (c i) = 1) := by
  let k_prev := k (m - 1)
  let k_next := max k_prev F_prev.natDegree + 1
  have hk_next_gt : k_next > k_prev := by simp [k_next, k_prev]; omega
  have hk_next_deg : k_next > F_prev.natDegree := by simp [k_next]; omega
  obtain ⟨T_next, hT_bound, hT_zeros, hT_c_prev, hT_match, hT_c_curr⟩ :=
    exists_correction_polynomial m hm S hS r hr hr_pos hr_gt c hc_norm hc_mem k_prev F_prev k_next hk_next_gt
  refine ⟨k_next, T_next, hk_next_gt, hk_next_deg, hT_bound, ?_, ?_, ?_⟩
  · -- Zeros for i < m
    intro i hi z hz
    by_cases hz_case : ‖z‖ < r (m - 1);
    · specialize hT_zeros i ( Nat.le_of_lt hi ) z ⟨ hz.1, by simpa using hz_case ⟩ ( k i ) ( by linarith [ Nat.le_max_left k_prev F_prev.natDegree, Nat.le_max_right k_prev F_prev.natDegree, show k i ≤ k_prev from hk_mono.le_iff_le ( by norm_num; linarith [ Nat.sub_add_cancel hm ] ) ( by norm_num ) |>.2 ( Nat.le_sub_one_of_lt hi ) ] ) ; aesop;
    · by_cases hz_case : ‖z‖ = r (m - 1);
      · specialize hr_avoid ( m - 1 ) ; simp_all +decide [ Set.ext_iff ];
        exact False.elim <| hr_avoid z hz_case i ( by omega ) hz.1;
      · -- Since $‖z‖ > r (m - 1)$, we have $‖z‖ < r m$.
        have hz_lt_rm : ‖z‖ < r m := by
          simpa using hz.2;
        -- Since $i < m$, we have $k i \leq k_next$.
        have hki_le_knext : k i ≤ k_next := by
          exact le_trans ( hk_mono.le_iff_le ( by norm_num; omega ) ( by norm_num ) |>.2 ( Nat.le_pred_of_lt hi ) ) ( Nat.le_succ_of_le ( Nat.le_max_left _ _ ) );
        specialize hT_match i ( by linarith ) z ⟨ hz.1, by exact ⟨ lt_of_le_of_ne ( le_of_not_gt ‹¬‖z‖ < r ( m - 1 ) › ) ( Ne.symm hz_case ), hz_lt_rm ⟩ ⟩ ( k i ) hki_le_knext ; aesop
  · -- Zeros for i = m
    intro z hz
    -- Since $k_{next} > \deg(F_{prev})$, we have $F_{prev}^{(k_{next})}(z) = 0$.
    have hF_prev_k_next : (derivative^[k_next] F_prev).eval z = 0 := by
      rw [ Polynomial.iterate_derivative_eq_zero ] <;> aesop;
    by_cases hz_ball : z ∈ Metric.ball 0 (r (m - 1));
    · have := hT_zeros m ( by linarith ) z ⟨ hz.1, hz_ball ⟩ k_next ( by linarith ) ; aesop;
    · specialize hT_match m le_rfl z ⟨ hz.1, by
        simp_all +decide [ Set.ext_iff ];
        exact lt_of_le_of_ne hz_ball fun h => hr_avoid ( m - 1 ) z h.symm m ( by omega ) hz.1 ⟩ k_next le_rfl;
      simp_all +decide [ Function.iterate_add_apply ]
  · -- Values for i < m
    intro i hi
    by_cases hi' : i < m - 1 <;> simp_all +decide [ Function.iterate_add_apply ];
    · exact hT_c_prev i hi' _ ( by linarith [ hk_mono.le_iff_le ( show i ≤ m - 1 from Nat.le_of_lt hi' ) ( show m - 1 ≤ m - 1 from le_rfl ) |>.2 ( Nat.le_of_lt hi' ) ] );
    · rw [ show i = m - 1 by omega ] ; specialize hT_c_curr ( k ( m - 1 ) ) ( by linarith ) ; aesop;

lemma exists_next_step_v3 (m : ℕ) (hm : m > 0)
    (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (k : ℕ → ℕ) (hk_mono : StrictMonoOn k (Set.Iic (m-1)))
    (F_prev : Polynomial ℂ)
    (hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m-1)), (derivative^[k i] F_prev).eval z = 0)
    (hF_vals : ∀ i < m-1, (derivative^[k i] F_prev).eval (c i) = 1) :
    ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
      k_next > k (m-1) ∧ k_next > F_prev.natDegree ∧
      (∀ z, ‖z‖ ≤ r (m-1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
      let F_next := F_prev + T_next
      (∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r m), (derivative^[k i] F_next).eval z = 0) ∧
      (∀ z ∈ S m ∩ Metric.ball 0 (r m), (derivative^[k_next] F_next).eval z = 0) ∧
      (∀ i < m, (derivative^[k i] F_next).eval (c i) = 1) := by
        convert exists_next_step_v2 m hm S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k hk_mono F_prev hF_zeros hF_vals using 1

/-
Inductive step for the construction of the sequence of polynomials.
-/
lemma exists_next_step_final (m : ℕ) (hm : m > 0)
    (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (k : ℕ → ℕ) (hk_mono : StrictMonoOn k (Set.Iic (m-1)))
    (F_prev : Polynomial ℂ)
    (hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m-1)), (derivative^[k i] F_prev).eval z = 0)
    (hF_vals : ∀ i < m-1, (derivative^[k i] F_prev).eval (c i) = 1) :
    ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
      k_next > k (m-1) ∧ k_next > F_prev.natDegree ∧
      (∀ z, ‖z‖ ≤ r (m-1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
      let F_next := F_prev + T_next
      (∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r m), (derivative^[k i] F_next).eval z = 0) ∧
      (∀ z ∈ S m ∩ Metric.ball 0 (r m), (derivative^[k_next] F_next).eval z = 0) ∧
      (∀ i < m, (derivative^[k i] F_next).eval (c i) = 1) := by
        obtain ⟨k_next, T_next, hk_next⟩ := exists_next_step_v2 m hm S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k hk_mono F_prev hF_zeros hF_vals;
        use k_next, T_next

/-
Definitions of History and IsValid for the construction.
-/
def History := List (ℕ × Polynomial ℂ)

def k_of (L : History) (i : ℕ) : ℕ := (L.get? i).map Prod.fst |>.getD 0

noncomputable def T_of (L : History) (i : ℕ) : Polynomial ℂ := (L.get? i).map Prod.snd |>.getD 0

noncomputable def F_of (L : History) : Polynomial ℂ := (L.map Prod.snd).sum

def IsValid (S : ℕ → Set ℂ) (r : ℕ → ℝ) (c : ℕ → ℂ) (L : History) : Prop :=
  let m := L.length
  m > 0 →
  k_of L 0 = 1 ∧
  StrictMonoOn (k_of L) (Set.Iio m) ∧
  (∀ j < m,
    (∀ i ≤ j, ∀ z ∈ S i ∩ Metric.ball 0 (r j), (derivative^[k_of L i] (F_of (L.take (j+1)))).eval z = 0) ∧
    (∀ i < j, (derivative^[k_of L i] (F_of (L.take (j+1)))).eval (c i) = 1) ∧
    (j > 0 → ∀ z, ‖z‖ ≤ r (j - 1) → ‖(T_of L j).eval z‖ < 2 ^ (-(j : ℝ) + 1)))

/-
Base case for the validity of the history.
-/
lemma valid_zero (S : ℕ → Set ℂ) (r : ℕ → ℝ) (c : ℕ → ℂ) : IsValid S r c [(1, 0)] := by
  unfold IsValid;
  simp +decide [ StrictMonoOn ];
  unfold k_of F_of; aesop;

/-
Definition of the next step in the construction.
-/
noncomputable def next_step (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (L : History) : ℕ × Polynomial ℂ :=
  if h : IsValid S r c L then
    let m := L.length
    if hm : m = 0 then (1, 0)
    else
      let k := k_of L
      let F_prev := F_of L
      have hk_mono : StrictMonoOn k (Set.Iic (m - 1)) := by
        -- By definition of `IsValid`, we know that `k` is strictly monotone on `Iio m`.
        have hk_mono : StrictMonoOn k (Iio m) := by
          -- By definition of IsValid, we know that k is strictly monotone on Iio m.
          apply h (Nat.pos_of_ne_zero hm) |>.2.1;
        exact hk_mono.mono ( fun x hx => Nat.lt_of_le_of_lt hx ( Nat.pred_lt hm ) )
      have hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m - 1)), (derivative^[k i] F_prev).eval z = 0 := by
        have := h;
        have := this ( Nat.pos_of_ne_zero hm );
        intro i hi z hz;
        convert this.2.2 ( m - 1 ) ( Nat.sub_lt ( Nat.pos_of_ne_zero hm ) zero_lt_one ) |>.1 i ( Nat.le_sub_one_of_lt hi ) z ⟨ hz.1, hz.2.out.trans_le ( by simp ) ⟩;
        rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hm ) ];
        simp +zetaDelta at *
      have hF_vals : ∀ i < m - 1, (derivative^[k i] F_prev).eval (c i) = 1 := by
        have := h ( Nat.pos_of_ne_zero hm );
        intro i hi;
        convert this.2.2 ( m - 1 ) ( Nat.sub_lt ( Nat.pos_of_ne_zero hm ) zero_lt_one ) |>.2.1 i hi;
        rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hm ), List.take_length ]
      let res := exists_next_step_final m (Nat.pos_of_ne_zero hm) S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k hk_mono F_prev hF_zeros hF_vals
      (Classical.choose res, Classical.choose (Classical.choose_spec res))
  else (0, 0)

/-
Definition of the history sequence.
-/
noncomputable def history_seq (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) : ℕ → List (ℕ × Polynomial ℂ)
| 0 => [(1, 0)]
| n + 1 =>
  let L := history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n
  L ++ [next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem L]

/-
Helper lemma for `k_of` on appended lists.
-/
lemma k_of_append (L : List (ℕ × Polynomial ℂ)) (x : ℕ × Polynomial ℂ) (i : ℕ) :
    k_of (L ++ [x]) i = if i < L.length then k_of L i else if i = L.length then x.1 else 0 := by
      unfold k_of;
      by_cases hi : i < L.length <;> by_cases hi' : i = L.length <;> simp +decide [ Nat.lt_succ_iff, hi, hi' ];
      · rw [ List.getElem?_append ] ; aesop;
      · grind

/-
Helper lemma for `F_of` on appended lists.
-/
lemma F_of_append (L : List (ℕ × Polynomial ℂ)) (x : ℕ × Polynomial ℂ) :
    F_of (L ++ [x]) = F_of L + x.2 := by
  unfold F_of
  simp

/-
Helper lemma for `T_of` on appended lists.
-/
lemma T_of_append (L : List (ℕ × Polynomial ℂ)) (x : ℕ × Polynomial ℂ) (i : ℕ) :
    T_of (L ++ [x]) i = if i < L.length then T_of L i else if i = L.length then x.2 else 0 := by
  unfold T_of
  by_cases hi : i < L.length <;> by_cases hi' : i = L.length <;> simp +decide [ Nat.lt_succ_iff, hi, hi' ]
  · rw [ List.getElem?_append ]; aesop
  · grind

/-
Definitions of T_seq, k_seq, and f.
-/
noncomputable def T_seq (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) : Polynomial ℂ :=
  ((history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).get? n).map Prod.snd |>.getD 0

noncomputable def k_seq (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) : ℕ :=
  ((history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).get? n).map Prod.fst |>.getD 0

noncomputable def f_term (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) (z : ℂ) : ℂ :=
  (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z

noncomputable def f (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (z : ℂ) : ℂ :=
  ∑' n, f_term S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n z

/-
Specification of the next step in the construction.
-/
lemma next_step_spec (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (L : List (ℕ × Polynomial ℂ)) (hL : IsValid S r c L) (hL_nonempty : L ≠ []) :
    let res := next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem L
    let k_next := res.1
    let T_next := res.2
    let m := L.length
    let F_prev := F_of L
    let k_prev := k_of L (m - 1)
    k_next > k_prev ∧
    (∀ z, ‖z‖ ≤ r (m - 1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
    let F_next := F_prev + T_next
    (∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r m), (derivative^[k_of L i] F_next).eval z = 0) ∧
    (∀ z ∈ S m ∩ Metric.ball 0 (r m), (derivative^[k_next] F_next).eval z = 0) ∧
    (∀ i < m, (derivative^[k_of L i] F_next).eval (c i) = 1) := by
      -- Let's unfold the definition of `next_step` to access the properties of `k_next` and `T_next`.
      obtain ⟨k_next, T_next, hk_next, hT_next⟩ : ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
        k_next > k_of L (L.length - 1) ∧
        k_next > (F_of L).natDegree ∧
        (∀ z, ‖z‖ ≤ r (L.length - 1) → ‖T_next.eval z‖ < 2 ^ (-(L.length : ℝ) + 1)) ∧
        let F_next := F_of L + T_next
        (∀ i < L.length, ∀ z ∈ S i ∩ Metric.ball 0 (r L.length), (derivative^[k_of L i] F_next).eval z = 0) ∧
        (∀ z ∈ S (L.length) ∩ Metric.ball 0 (r L.length), (derivative^[k_next] F_next).eval z = 0) ∧
        (∀ i < L.length, (derivative^[k_of L i] F_next).eval (c i) = 1) := by
          apply exists_next_step_v3 (L.length) (List.length_pos_iff.mpr hL_nonempty) S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem
          generalize_proofs at *;
          · exact hL ( List.length_pos_iff.mpr hL_nonempty ) |>.2.1.mono ( Set.Iic_subset_Iio.mpr ( Nat.sub_lt ( List.length_pos_iff.mpr hL_nonempty ) zero_lt_one ) );
          · intro i hi z hz;
            have := hL ( Nat.pos_of_ne_zero ( by aesop ) );
            convert this.2.2 ( L.length - 1 ) ( Nat.sub_lt ( List.length_pos_iff.mpr hL_nonempty ) zero_lt_one ) |>.1 i ( Nat.le_sub_one_of_lt hi ) z ⟨ hz.1, hz.2 ⟩ using 1;
            cases L <;> aesop;
          · intro i hi;
            have := hL ( by linarith [ Nat.sub_add_cancel ( List.length_pos_iff.mpr hL_nonempty ) ] );
            convert this.2.2 ( L.length - 1 ) ( Nat.sub_lt ( List.length_pos_iff.mpr hL_nonempty ) zero_lt_one ) |>.2.1 i ( by omega ) using 1;
            cases L <;> aesop;
      unfold next_step; simp +decide [ * ] ;
      have := Classical.choose_spec ( show ∃ k : ℕ, ∃ T : Polynomial ℂ, k > k_of L ( L.length - 1 ) ∧ k > ( F_of L ).natDegree ∧ ( ∀ z : ℂ, ‖z‖ ≤ r ( L.length - 1 ) → ‖T.eval z‖ < 2 ^ ( - ( L.length : ℝ ) + 1 ) ) ∧ let F_next := F_of L + T; ( ∀ i < L.length, ∀ z ∈ S i ∩ Metric.ball 0 ( r L.length ), ( derivative^[k_of L i] F_next ).eval z = 0 ) ∧ ( ∀ z ∈ S L.length ∩ Metric.ball 0 ( r L.length ), ( derivative^[k] F_next ).eval z = 0 ) ∧ ( ∀ i < L.length, ( derivative^[k_of L i] F_next ).eval ( c i ) = 1 ) from ⟨ k_next, T_next, hk_next, hT_next ⟩ );
      have := Classical.choose_spec this;
      simp +zetaDelta at *;
      tauto

/-
Appending the next step to a valid history preserves validity.
-/
lemma valid_next_step (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (L : List (ℕ × Polynomial ℂ)) (hL : IsValid S r c L) :
    IsValid S r c (L ++ [next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem L]) := by
      intros h;
      refine' ⟨ _, _, _ ⟩;
      · rcases L with ( _ | ⟨ ⟨ k, T ⟩, L ⟩ ) <;> simp_all +decide [ k_of ];
        · unfold next_step; aesop;
        · have := hL; unfold IsValid at this; aesop;
      · intro i hi j hj hij;
        by_cases hi' : i < L.length <;> by_cases hj' : j < L.length <;> simp_all +decide [ k_of_append ];
        · exact hL ( Nat.pos_of_ne_zero ( by aesop ) ) |>.2.1 hi' hj' hij;
        · split_ifs <;> try linarith;
          · have := next_step_spec S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem L hL (by
            aesop);
            refine' lt_of_le_of_lt _ this.1;
            have := hL;
            have := this ( List.length_pos_iff.mpr ( by aesop_cat : L ≠ [] ) );
            exact this.2.1.le_iff_le ( by simpa using hi' ) ( by simpa using Nat.sub_lt ( List.length_pos_iff.mpr ( by aesop_cat ) ) zero_lt_one ) |>.2 ( Nat.le_sub_one_of_lt hi' );
          · omega;
        · linarith;
        · grind;
      · intro j hj;
        by_cases hj' : j < L.length;
        · have := hL ( by linarith );
          simp_all +decide [ List.take_append_of_le_length, Nat.succ_le_iff ];
          have := this.2.2 j hj'; simp_all +decide [ k_of_append, T_of_append ] ;
          exact ⟨ fun i hi z hz hz' => by rw [ if_pos ( by linarith ) ] ; exact this.2.2 j hj' |>.1 i hi z hz hz', fun i hi => by rw [ if_pos ( by linarith ) ] ; exact this.2.2 j hj' |>.2.1 i hi ⟩;
        · rcases eq_or_lt_of_le ( Nat.le_of_not_lt hj' ) <;> simp_all +decide [ List.take_append_of_le_length ];
          · have := next_step_spec S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem L hL;
            by_cases hL_empty : L = [] <;> simp_all +decide [ List.take_append ];
            · unfold k_of F_of next_step; aesop;
            · refine' ⟨ _, _, _ ⟩;
              · intro i hi z hz hz'; cases lt_or_eq_of_le hi <;> simp_all +decide [ List.take_succ ] ;
                · rw [ k_of_append, F_of_append ] ; aesop;
                · rw [ F_of_append ];
                  rw [ k_of_append ] ; aesop;
              · intro i hi;
                rw [ List.take_of_length_le ( by linarith ) ];
                rw [ F_of_append, k_of_append ] ; aesop;
              · unfold T_of; aesop;
          · linarith

/-
The history sequence is valid for all n.
-/
lemma history_seq_valid (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) :
    IsValid S r c (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) := by
      induction' n with n ih;
      · -- The base case is when the list is [(1, 0)], which is valid by definition.
        apply valid_zero;
      · convert valid_next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem _ ih using 1

/-
The polynomials T_n satisfy the required decay bound.
-/
lemma T_seq_bound (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) (hn : n > 0) :
    ∀ z, ‖z‖ ≤ r (n - 1) → ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖ < 2 ^ (-(n : ℝ) + 1) := by
      have := history_seq_valid S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n;
      have := this;
      unfold IsValid at this;
      specialize this (by
      induction hn <;> simp +decide [ *, history_seq ]);
      have h_len : (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).length = n + 1 := by
        exact Nat.recOn n ( by rfl ) fun n ihn => by rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +arith +decide [ ihn ] ;
      convert this.2.2 n ( by linarith ) |>.2.2 hn using 1

/-
The series 2^(-n+1) is summable.
-/
lemma summable_two_pow_neg_add_one : Summable (fun n : ℕ => (2 : ℝ) ^ (-(n : ℝ) + 1)) := by
  norm_num [ Real.rpow_add, Real.rpow_neg ];
  exact Summable.mul_right _ ( by simpa using summable_geometric_two )

/-
f is differentiable on B(0, r_N).
-/
lemma f_diff_on_ball (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (N : ℕ) :
    DifferentiableOn ℂ (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem) (Metric.ball 0 (r N)) := by
      apply differentiableOn_tsum_of_summable_norm;
      rotate_right;
      use fun n => if n > N then 2 ^ (-(n : ℝ) + 1) else ( SupSet.sSup ( Set.image ( fun z => ‖( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ).eval z‖ ) ( closedBall 0 ( r N ) ) ) );
      · have h_summable : Summable (fun n : ℕ => if n > N then (2 : ℝ) ^ (-(n : ℝ) + 1) else 0) := by
          have h_summable : Summable (fun n : ℕ => (2 : ℝ) ^ (-(n : ℝ) + 1)) := by
            norm_num [ Real.rpow_add ];
            simpa using summable_geometric_two.mul_right 2;
          exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> positivity ) ( fun n => by split_ifs <;> first | positivity | aesop ) h_summable;
        rw [ ← summable_nat_add_iff ( N + 1 ) ] at *;
        grind +ring;
      · intro n; apply_rules [ Differentiable.differentiableOn, Polynomial.differentiable ] ;
      · exact Metric.isOpen_ball;
      · intro i w hw; split_ifs <;> simp_all +decide [ f_term ] ;
        · exact le_of_lt ( T_seq_bound S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem i ( Nat.pos_of_ne_zero ( by linarith ) ) w ( by linarith [ hr.monotone ( Nat.le_sub_one_of_lt ‹_› ) ] ) );
        · exact le_csSup ( IsCompact.bddAbove ( isCompact_closedBall 0 ( r N ) |> IsCompact.image <| continuous_norm.comp <| Polynomial.continuous _ ) ) <| Set.mem_image_of_mem _ <| mem_closedBall_zero_iff.mpr <| le_of_lt hw

/-
f is an entire function.
-/
theorem f_entire (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) :
    AnalyticOn ℂ (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem) Set.univ := by
      have h_diff : ∀ z : ℂ, DifferentiableAt ℂ (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem) z := by
        -- Since $r_n \to \infty$ (implied by $r_n > n + 1$), there exists $N$ such that $‖z‖ < r_N$.
        intro z
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖z‖ < r N := by
          exact ⟨ ⌊‖z‖⌋₊ + 1, by have := hr_gt ( ⌊‖z‖⌋₊ + 1 ) ; push_cast at *; linarith [ Nat.lt_floor_add_one ‖z‖ ] ⟩;
        have h_diff : DifferentiableOn ℂ (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem) (Metric.ball 0 (r N)) := by
          exact f_diff_on_ball S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N;
        exact h_diff.differentiableAt ( Metric.isOpen_ball.mem_nhds <| by simpa using hN );
      exact analyticOn_univ_iff_differentiable.mpr h_diff

/-
The partial sums of f converge locally uniformly to f on the whole plane.
-/
lemma f_tendsto_locally_uniformly (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) :
    TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z)
      (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem) atTop Set.univ := by
        have h_series : ∀ K : Set ℂ, IsCompact K → ∃ M : ℕ, ∀ z ∈ K, ∀ n > M, ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖ < 2 ^ (-(n : ℝ) + 1) := by
          intro K hK
          obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ z ∈ K, ‖z‖ ≤ r M := by
            obtain ⟨ M, hM ⟩ := hK.isBounded.exists_pos_norm_le;
            exact ⟨ ⌈M⌉₊, fun z hz => le_trans ( hM.2 z hz ) ( le_trans ( Nat.le_ceil _ ) ( by linarith [ hr_gt ⌈M⌉₊ ] ) ) ⟩;
          use M + 1;
          intros z hz n hn;
          apply T_seq_bound;
          · linarith;
          · exact le_trans ( hM z hz ) ( hr.monotone ( Nat.le_sub_one_of_lt ( by linarith ) ) );
        have h_series : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z) (fun z => ∑' n, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z) atTop K := by
          intros K hK
          obtain ⟨M, hM⟩ := h_series K hK
          have h_uniform : ∀ z ∈ K, ∀ n > M, ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖ ≤ 2 ^ (-(n : ℝ) + 1) := by
            exact fun z hz n hn => le_of_lt ( hM z hz n hn );
          have h_uniform : Summable (fun n : ℕ => SupSet.sSup (Set.image (fun z => ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖) K)) := by
            have h_uniform : ∀ n > M, sSup (Set.image (fun z => ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖) K) ≤ 2 ^ (-(n : ℝ) + 1) := by
              intros n hn;
              by_cases hK_empty : K = ∅;
              · simp [hK_empty];
                positivity;
              · exact csSup_le ( Set.Nonempty.image _ <| Set.nonempty_iff_ne_empty.mpr hK_empty ) <| Set.forall_mem_image.mpr fun z hz => h_uniform z hz n hn;
            rw [ ← summable_nat_add_iff ( M + 1 ) ];
            refine' Summable.of_nonneg_of_le ( fun n => _ ) ( fun n => h_uniform _ <| by linarith ) _;
            · apply_rules [ Real.sSup_nonneg ] ; aesop;
            · norm_num [ Real.rpow_add, Real.rpow_neg ];
              exact Summable.mul_right _ ( Summable.mul_left _ ( by simpa using summable_geometric_two ) );
          have h_uniform : TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z) (fun z => ∑' n, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z) atTop K := by
            have h_uniform : ∀ n, ∀ z ∈ K, ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖ ≤ sSup (Set.image (fun z => ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖) K) := by
              exact fun n z hz => le_csSup ( IsCompact.bddAbove ( hK.image ( show Continuous fun z => ‖eval z ( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n )‖ from by exact Continuous.norm <| by exact Polynomial.continuous _ ) ) ) <| Set.mem_image_of_mem _ hz
            have h_uniform : TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z) (fun z => ∑' n, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z) atTop K := by
              have h_uniform : ∀ N, ∀ z ∈ K, ‖∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z - ∑' n, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖ ≤ ∑' n, sSup (Set.image (fun z => ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem (n + N)).eval z‖) K) := by
                intros N z hz
                have h_uniform : ‖∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z - ∑' n, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖ = ‖∑' n, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem (n + N)).eval z‖ := by
                  rw [ ← Summable.sum_add_tsum_nat_add N ];
                  · norm_num [ sub_add_eq_sub_sub ];
                  · have h_uniform : Summable (fun n => ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖) := by
                      exact Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => h_uniform n z hz ) ‹_›;
                    exact h_uniform.of_norm;
                rw [h_uniform];
                refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
                · exact Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => by solve_by_elim ) ( ‹Summable fun n => sSup ( ( fun z => ‖eval z ( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n )‖ ) '' K ) ›.comp_injective ( add_left_injective N ) );
                · exact Summable.tsum_le_tsum ( fun n => by solve_by_elim ) ( by exact Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => by solve_by_elim ) ( ‹Summable fun n => sSup ( ( fun z => ‖eval z ( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n )‖ ) '' K ) ›.comp_injective ( add_left_injective N ) ) ) ( by exact ‹Summable fun n => sSup ( ( fun z => ‖eval z ( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n )‖ ) '' K ) ›.comp_injective ( add_left_injective N ) )
              have h_uniform : Filter.Tendsto (fun N => ∑' n, sSup (Set.image (fun z => ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem (n + N)).eval z‖) K)) Filter.atTop (nhds 0) := by
                convert tendsto_sum_nat_add fun n => sSup ( Set.image ( fun z => ‖eval z ( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n )‖ ) K ) using 1;
              rw [ Metric.tendstoUniformlyOn_iff ];
              intro ε hε; filter_upwards [ h_uniform.eventually ( gt_mem_nhds hε ), Filter.eventually_ge_atTop 0 ] with N hN hN'; intro z hz; rw [ dist_comm ] ; exact lt_of_le_of_lt ( by simpa [ dist_eq_norm ] using ‹∀ N : ℕ, ∀ z ∈ K, ‖∑ n ∈ Finset.range N, eval z ( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) - ∑' n, eval z ( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n)‖ ≤ ∑' n, sSup ( ( fun z => ‖eval z ( T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + N ) )‖ ) '' K ) › N z hz ) hN;
            convert h_uniform using 1;
          convert h_uniform using 1;
        rw [ Metric.tendstoLocallyUniformlyOn_iff ];
        intro ε hε x hx;
        specialize h_series ( Metric.closedBall x 1 ) ( ProperSpace.isCompact_closedBall x 1 );
        rw [ Metric.tendstoUniformlyOn_iff ] at h_series;
        exact ⟨ Metric.closedBall x 1, mem_nhdsWithin_of_mem_nhds ( Metric.closedBall_mem_nhds _ zero_lt_one ), h_series ε hε ⟩

/-
The k-th derivative of f is the limit of the k-th derivatives of the partial sums.
-/
lemma f_iterated_deriv_eq_limit (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (k : ℕ) (z : ℂ) :
    (iteratedDeriv k (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem)) z =
    lim (Filter.atTop.map (fun N => (iteratedDeriv k (fun w => ∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval w)) z)) := by
      have := @f_tendsto_locally_uniformly S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem;
      -- By the properties of the derivatives of the partial sums, we can apply the fact that the derivatives of the partial sums converge locally uniformly to the derivative of $f$.
      have h_deriv_conv : TendstoLocallyUniformlyOn (fun N z => iteratedDeriv k (fun w => ∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval w) z) (iteratedDeriv k (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem)) atTop Set.univ := by
        induction' k with k ih;
        · simpa using this;
        · simp_all +decide [ iteratedDeriv_succ ];
          apply_rules [ TendstoLocallyUniformlyOn.deriv ];
          · refine' Filter.Eventually.of_forall fun N => _;
            -- The sum of polynomials is a polynomial, and the k-th derivative of a polynomial is also a polynomial.
            have h_poly : ∀ N, ∃ P : Polynomial ℂ, ∀ z, ∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z = P.eval z := by
              exact fun N => ⟨ ∑ n ∈ Finset.range N, T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n, fun z => by simp +decide [ Polynomial.eval_finset_sum ] ⟩;
            obtain ⟨ P, hP ⟩ := h_poly N; simp +decide [ funext hP ] ;
            -- The k-th derivative of a polynomial is also a polynomial.
            have h_poly_deriv : ∀ k, ∃ Q : Polynomial ℂ, iteratedDeriv k (fun x => P.eval x) = fun x => Q.eval x := by
              intro k; induction' k with k ih <;> simp_all +decide [ iteratedDeriv_succ ] ;
              · exact ⟨ P, rfl ⟩;
              · obtain ⟨ Q, hQ ⟩ := ih; use Polynomial.derivative Q; ext; simp +decide [ hQ ] ;
            obtain ⟨ Q, hQ ⟩ := h_poly_deriv k; rw [ hQ ] ; exact Differentiable.differentiableOn ( by exact Q.differentiable ) ;
          · exact isOpen_univ;
      rw [ eq_comm ];
      refine' Filter.Tendsto.limUnder_eq _;
      exact h_deriv_conv.tendsto_at ( Set.mem_univ z )

/-
The sequence k_n is strictly increasing.
-/
lemma k_seq_strict_mono (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) :
    StrictMono (k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem) := by
      refine' strictMono_nat_of_lt_succ _;
      intro n;
      -- By definition of `k_seq`, we know that `k_seq (n + 1)` is the first component of the new entry in the history sequence.
      have h_k_seq_succ : k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem (n + 1) = (next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n)).fst := by
        unfold k_seq;
        rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +decide [ List.getElem?_append ];
        rw [ show ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ).length = n + 1 from ?_ ] ; simp +decide [ List.getElem?_eq_none ];
        induction n <;> simp +arith +decide [ *, history_seq ];
      have h_k_seq_succ : (next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n)).fst > k_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) (n) := by
        have := next_step_spec S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ( history_seq_valid S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ?_;
        · convert this.1 using 1;
          rw [ show ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n |> List.length ) = n + 1 from ?_ ];
          · rfl;
          · exact Nat.recOn n ( by rfl ) fun n ih => by rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +arith +decide [ ih ] ;
        · induction n <;> simp_all +decide [ history_seq ];
      convert h_k_seq_succ.lt using 1

/-
The derivative of the partial sum vanishes on S_n inside the ball.
-/
lemma partial_sum_deriv_vanishes (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (N : ℕ) (n : ℕ) (hn : n ≤ N) (z : ℂ) (hz : z ∈ S n) (hz_norm : ‖z‖ < r N) :
    (iteratedDeriv (k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) (fun w => ∑ j ∈ Finset.range (N + 1), (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j).eval w)) z = 0 := by
      -- By definition of $k_seq$, we know that $k_seq n = k_of L n$ where $L = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N$.
      set L : List (ℕ × Polynomial ℂ) := history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
      have hk_eq : k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n = k_of L n := by
        simp +zetaDelta at *;
        -- By definition of $k_seq$, we know that $k_seq n = k_of L n$ where $L = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N$. This follows directly from the definition of $k_seq$.
        simp [k_seq, k_of];
        have h_len : ∀ m n, m ≤ n → List.length (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem m) = m + 1 ∧ List.length (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) = n + 1 ∧ ∀ i ≤ m, (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem m).get? i = (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).get? i := by
          intros m n hmn
          induction' hmn with n hn ih;
          · field_simp;
            exact ⟨ by exact Nat.recOn m ( by rfl ) fun n ihn => by rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +arith +decide [ ihn ], by exact Nat.recOn m ( by rfl ) fun n ihn => by rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +arith +decide [ ihn ], fun _ _ => trivial ⟩;
          · simp_all +decide [ history_seq ];
            grind;
        specialize h_len n N hn;
        specialize h_len ; have := h_len.2.2 n le_rfl ; aesop;
      -- By definition of $F_of$, we know that $F_of L = \sum_{j=0}^N T_seq j$.
      have hF_of : F_of L = ∑ j ∈ Finset.range (N + 1), T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j := by
        have hF_of : ∀ n, F_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) = ∑ j ∈ Finset.range (n + 1), T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j := by
          intro n
          induction' n with n ih;
          · exact rfl;
          · rw [ Finset.sum_range_succ ];
            rw [ ← ih, show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl, F_of_append ];
            simp +decide [ T_seq ];
            rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +decide [ List.getElem?_append ];
            rw [ show ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ).length = n + 1 from ?_ ] ; simp +decide [ Nat.succ_eq_add_one ];
            exact Nat.recOn n ( by rfl ) fun n ih => by rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +decide [ ih ] ;
        exact hF_of N;
      -- By the properties of the history sequence, we know that $F_of L$ evaluated at $z$ is zero.
      have hF_of_zero : (derivative^[k_of L n] (F_of L)).eval z = 0 := by
        have := history_seq_valid S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N;
        specialize this ( show L.length > 0 from ?_ );
        · -- By definition of `history_seq`, we know that `L.length = N + 1`.
          have hL_length : L.length = N + 1 := by
            have hL_length : ∀ n, (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).length = n + 1 := by
              intro n; induction n <;> simp +arith +decide [ *, history_seq ] ;
            exact hL_length N;
          linarith;
        · convert this.2.2 N ( by
            have hL_length : ∀ n, (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).length = n + 1 := by
              intro n; induction n <;> simp +arith +decide [ *, history_seq ] ;
            linarith [ hL_length N ] ) |>.1 n hn z ⟨ hz, by
            simpa using hz_norm ⟩ using 1;
          rw [ show List.take ( N + 1 ) ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N from ?_ ];
          -- By definition of `history_seq`, the length of `history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N` is `N + 1`.
          have h_len : ∀ n, (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).length = n + 1 := by
            intro n; induction n <;> simp +arith +decide [ *, history_seq ] ;
          rw [ ← h_len, List.take_length ];
      simp_all +decide [ Polynomial.eval_finset_sum, iteratedDeriv_eq_iterate ];
      -- Since the polynomial derivative is the same as the function derivative when applied to the polynomial evaluated at z, we can conclude that the k-th derivative of the function is zero at z.
      have h_poly_deriv : ∀ p : Polynomial ℂ, deriv^[k_of L n] (fun w => p.eval w) = fun w => (derivative^[k_of L n] p).eval w := by
        intro p; induction' k_of L n with k ih generalizing p <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
        ext; simp +decide [ Polynomial.derivative_eval ] ;
      convert congr_fun ( h_poly_deriv ( ∑ j ∈ Finset.range ( N + 1 ), T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j ) ) z using 1;
      · simp +decide [ Polynomial.eval_finset_sum ];
      · exact hF_of_zero.symm

/-
f satisfies the vanishing derivative condition on each S_n.
-/
lemma f_deriv_vanishes_on_Sn (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) (z : ℂ) (hz : z ∈ S n) :
    (iteratedDeriv (k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem)) z = 0 := by
      rw [ f_iterated_deriv_eq_limit ];
      -- By `partial_sum_deriv_vanishes`, `(iteratedDeriv k S_N) z = 0` for all `N ≥ M`.
      obtain ⟨M, hM⟩ : ∃ M, ∀ N ≥ M, ‖z‖ < r N := by
        exact ⟨ ⌈‖z‖⌉₊, fun N hN => by linarith [ Nat.le_ceil ( ‖z‖ ), hr_gt N, show ( N : ℝ ) ≥ ⌈‖z‖⌉₊ by exact_mod_cast hN ] ⟩;
      refine' Filter.Tendsto.limUnder_eq _;
      refine' tendsto_const_nhds.congr' _;
      filter_upwards [ Filter.eventually_ge_atTop ( M + n + 1 ) ] with N hN;
      have := partial_sum_deriv_vanishes S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( N - 1 ) n ( Nat.le_sub_one_of_lt ( by linarith ) ) z hz ( by simpa using hM ( N - 1 ) ( Nat.le_sub_one_of_lt ( by linarith ) ) ) ; rcases N <;> aesop;

/-
The derivative of the partial sum is 1 at c_n.
-/
lemma partial_sum_deriv_eq_one (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (N : ℕ) (n : ℕ) (hn : n < N) :
    (iteratedDeriv (k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) (fun w => ∑ j ∈ Finset.range (N + 1), (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j).eval w)) (c n) = 1 := by
      -- By definition of `F_of`, we know that `F_of (history_seq ... N)` is the sum of the first `N+1` polynomials in the sequence.
      have hF_of : F_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N) = ∑ j ∈ Finset.range (N + 1), (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j) := by
        have hF_of : ∀ k, F_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k) = ∑ j ∈ Finset.range (k + 1), (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j) := by
          intro k; induction' k with k ih <;> simp_all +decide [ Finset.sum_range_succ ] ;
          · unfold F_of T_seq; simp +decide [ history_seq ] ;
          · unfold F_of at *;
            rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( k + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k ) ] from rfl ] ; simp +decide [ *, Finset.sum_range_succ ] ; ring_nf;
            unfold T_seq; simp +decide [ add_comm 1 k ] ;
            rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( k + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k ) ] from rfl ] ; simp +decide [ List.getElem?_append ] ;
            rw [ show ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k ).length = k + 1 from ?_ ] ; aesop;
            exact Nat.recOn k ( by rfl ) fun n ihn => by rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +decide [ ihn ] ;
        apply hF_of;
      have := history_seq_valid S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N;
      -- By definition of `k_of`, we know that `k_of (history_seq ... N) n` is the k-th derivative of the sum of the first `N+1` polynomials in the sequence.
      have hk_of : k_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N) n = k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n := by
        unfold k_of k_seq;
        have h_len : ∀ m n, m ≤ n → (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).take (m + 1) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem m := by
          intros m n hmn
          induction' n with n ih generalizing m;
          · aesop;
          · cases hmn <;> simp_all +decide [ List.take_append ];
            · exact Nat.recOn n ( by trivial ) fun n ihn => by rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 2 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) ) ] from rfl ] ; simp +arith +decide [ ihn ] ;
            · rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ];
              rw [ List.take_append_of_le_length ] <;> norm_num [ ih m ‹_› ];
              -- By definition of `history_seq`, we know that its length is `n + 1`.
              have h_len : ∀ n, (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).length = n + 1 := by
                intro n; induction n <;> simp +arith +decide [ * ] ;
                · exact hc_inj rfl;
                · rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( _ + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem _ ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem _ ) ] from rfl ] ; simp +arith +decide [ * ];
              linarith [ h_len n ];
        rw [ ← h_len n N hn.le ];
        simp +decide [ List.get?_eq_get ];
      -- By definition of `IsValid`, we know that the k-th derivative of the sum of the first `N+1` polynomials in the sequence is 1 at `c_n`.
      have h_deriv : ∀ j < N + 1, (∀ i < j, (derivative^[k_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N) i] (F_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N))).eval (c i) = 1) := by
        unfold IsValid at this;
        specialize this (by
        exact Nat.recOn N ( by norm_num [ history_seq ] ) fun n ihn => by rw [ history_seq ] ; norm_num [ ihn ] ;);
        -- By definition of `history_seq`, we know that its length is `N + 1`.
        have h_length : (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N).length = N + 1 := by
          exact Nat.recOn N ( by rfl ) fun n ih => by rw [ show history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( n + 1 ) = history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ++ [ next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem ( history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ] from rfl ] ; simp +arith +decide [ ih ] ;
        grind;
      convert h_deriv ( n + 1 ) ( by linarith ) n ( by linarith ) using 1;
      rw [ hk_of, hF_of ];
      norm_num [ iteratedDeriv_eq_iterate ];
      -- The derivative of a sum is the sum of the derivatives.
      have h_deriv_sum : ∀ k : ℕ, deriv^[k] (fun w => ∑ j ∈ Finset.range (N + 1), Polynomial.eval w (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j)) = fun w => ∑ j ∈ Finset.range (N + 1), Polynomial.eval w (Polynomial.derivative^[k] (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j)) := by
        intro k; induction k <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
        ext; norm_num [ Polynomial.differentiableAt ] ;
      convert congr_fun ( h_deriv_sum ( k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ) ( c n ) using 1;
      induction' ( Finset.range ( N + 1 ) ) using Finset.induction <;> aesop

/-
f satisfies the derivative condition at c_n.
-/
lemma f_deriv_eq_one_on_cn (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) :
    (iteratedDeriv (k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem)) (c n) = 1 := by
      rw [ f_iterated_deriv_eq_limit ];
      refine' Filter.Tendsto.limUnder_eq _;
      refine' tendsto_const_nhds.congr' _;
      filter_upwards [ Filter.eventually_gt_atTop ( n + 1 ) ] with N hN;
      rw [ eq_comm, ← partial_sum_deriv_eq_one ];
      congr! 1;
      rotate_left;
      exacts [ N - 1, Nat.lt_pred_iff.mpr hN, by cases N <;> trivial ]

/-
f is a transcendental entire function.
-/
lemma f_transcendental (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) :
    TranscendentalEntire (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem) := by
      refine' ⟨ _, _ ⟩;
      · exact fun x => ( f_entire S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem |> AnalyticOn.differentiableOn ) |> DifferentiableOn.differentiableAt <| by simpa;
      · intro h;
        -- Since `f` is a polynomial, there exists `N` such that for all `k > N`, `f^{(k)} = 0`.
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k > N, ∀ z : ℂ, (iteratedDeriv k (f S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem)) z = 0 := by
          obtain ⟨ P, hP ⟩ := h;
          -- Since `P` is a polynomial, its derivatives of order higher than its degree are zero.
          obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k > N, ∀ z : ℂ, (iteratedDeriv k P.eval z) = 0 := by
            use P.natDegree;
            intro k hk z; rw [ iteratedDeriv_eq_iterate ] ;
            -- Since $P$ is a polynomial of degree $n$, its $k$-th derivative is zero for $k > n$.
            have h_poly_deriv : deriv^[k] (fun x => P.eval x) = fun x => Polynomial.eval x (Polynomial.derivative^[k] P) := by
              exact Nat.recOn k ( by norm_num ) fun n ih => by ext; simp +decide [ *, Function.iterate_succ_apply' ] ;
            rw [ h_poly_deriv, Polynomial.iterate_derivative_eq_zero ] ; aesop;
            linarith;
          exact ⟨ N, fun k hk z => by simpa only [ ← hP ] using hN k hk z ⟩;
        -- Choose `n` such that `k_seq n > N`.
        obtain ⟨n, hn⟩ : ∃ n : ℕ, k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n > N := by
          have := k_seq_strict_mono S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem;
          exact ⟨ _, this.id_le _ ⟩;
        exact absurd ( f_deriv_eq_one_on_cn S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n ) ( by rw [ hN _ hn ] ; norm_num )

/-
Main theorem: Existence of a transcendental entire function with prescribed zeros of derivatives.
-/
theorem thm_main (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n)) :
    ∃ k : ℕ → ℕ, ∃ f : ℂ → ℂ, TranscendentalEntire f ∧ ∀ n, ∀ z ∈ S n, (iteratedDeriv (k n) f) z = 0 := by
      have := @exists_radii;
      obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := this S hS;
      obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := exists_auxiliary_points S hS r hr₁ ( fun n => by linarith [ hr₂ n ] );
      exact ⟨ _, _, f_transcendental S hS r hr₁ ( fun n => by linarith [ hr₂ n ] ) hr₂ hr₃ c hc₁ hc₃ hc₂, f_deriv_vanishes_on_Sn S hS r hr₁ ( fun n => by linarith [ hr₂ n ] ) hr₂ hr₃ c hc₁ hc₃ hc₂ ⟩

/-
Main theorem: Existence of a transcendental entire function with prescribed zeros of derivatives.
-/
theorem main_result (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n)) :
    ∃ k : ℕ → ℕ, ∃ f : ℂ → ℂ, TranscendentalEntire f ∧ ∀ n, ∀ z ∈ S n, (iteratedDeriv (k n) f) z = 0 := by
  obtain ⟨r, hr_mono, hr_gt, hr_avoid⟩ := exists_radii S hS
  have hr_pos : ∀ n, 0 ≤ r n := by
    exact fun n => by linarith [ hr_gt n ] ;
  obtain ⟨c, hc_norm, hc_mem, hc_inj⟩ := exists_auxiliary_points S hS r hr_mono hr_pos
  let k := k_seq S hS r hr_mono hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem
  let f_val := f S hS r hr_mono hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem
  refine ⟨k, f_val, ?_, ?_⟩
  ·
    apply_rules [ f_transcendental ]
  ·
    -- Apply the lemma f_deriv_vanishes_on_Sn to conclude the proof.
    intros n z hz
    apply f_deriv_vanishes_on_Sn S hS r hr_mono hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n z hz

/-
If the derived set of a set S is empty, then S has no finite limit point (i.e., its intersection with any compact set is finite).
-/
lemma derivedSet_empty_imp_hasNoFiniteLimitPoint (S : Set ℂ) (h : derivedSet S = ∅) : HasNoFiniteLimitPoint S := by
  intro K hK;
  -- Since $S$ has no limit points, $S \cap K$ is closed in the compact set $K$, hence it is compact.
  have h_compact : IsCompact (S ∩ K) := by
    have h_closed : IsClosed S := by
      rw [ isClosed_iff_nhds ];
      intro x hx; contrapose! hx; simp_all +decide [ Set.ext_iff, mem_derivedSet ] ;
      specialize h x; rw [ accPt_iff_frequently ] at h; aesop;
    exact hK.inter_left h_closed;
  have h_discrete : DiscreteTopology (↥(S ∩ K)) := by
    have h_discrete : ∀ x ∈ S, ∀ᶠ y in nhds x, y ∈ S → y = x := by
      intro x hx; rw [ Set.eq_empty_iff_forall_notMem ] at h; specialize h x; simp_all +decide [ accPt_iff_frequently ] ;
      filter_upwards [ h ] with y hy hyS using Classical.not_not.1 fun hyx => hy hyx hyS;
    rw [ discreteTopology_iff_singleton_mem_nhds ];
    intro x; specialize h_discrete x x.2.1; rw [ nhds_induced ] ; aesop;
  exact IsCompact.finite h_compact h_discrete

/-
If an entire function f is bounded by a polynomial in |z|, then f is a polynomial.
-/
lemma isPolynomial_of_bound (f : ℂ → ℂ) (h_diff : Differentiable ℂ f) (n : ℕ) (C : ℝ)
    (h_bound : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ n) : IsPolynomial f := by
      -- We use induction on n.
      induction' n with n ih generalizing f;
      · -- Since $f$ is entire and bounded, it must be constant by Liouville's theorem.
        have h_const : ∀ z₁ z₂ : ℂ, f z₁ = f z₂ := by
          apply_rules [ @Complex.liouville_theorem_aux ];
          exact isBounded_iff_forall_norm_le.mpr ⟨ C, Set.forall_mem_range.mpr fun z => by simpa using h_bound z ⟩;
        exact ⟨ Polynomial.C ( f 0 ), fun z => by simpa using h_const z 0 ⟩;
      · -- By the induction hypothesis, we know that $f'$ is a polynomial.
        obtain ⟨P, hP⟩ : ∃ P : Polynomial ℂ, ∀ z, deriv f z = P.eval z := by
          have h_deriv_bound : ∀ z, ‖deriv f z‖ ≤ C * (1 + ‖z‖) ^ n * (n + 1) * 2 ^ (n + 1) := by
            -- By the Cauchy estimates, we have that for any $z \in \mathbb{C}$ and $r > 0$, $\|f'(z)\| \leq \frac{1}{r} \sup_{|w - z| = r} \|f(w)\|$.
            have h_cauchy : ∀ z : ℂ, ∀ r > 0, ‖deriv f z‖ ≤ (1 / r) * (C * (1 + ‖z‖ + r) ^ (n + 1)) := by
              intro z r hr_pos
              have h_cauchy : ‖deriv f z‖ ≤ (1 / r) * (C * (1 + ‖z‖ + r) ^ (n + 1)) := by
                have h_cauchy_integral : deriv f z = (1 / (2 * Real.pi * Complex.I)) * ∮ (w : ℂ) in C(z, r), f w / (w - z)^2 := by
                  have := @Complex.deriv_eq_smul_circleIntegral;
                  convert this hr_pos ( h_diff.differentiableOn.diffContOnCl ) using 1 ; norm_cast ; norm_num ; ring_nf;
                  ac_rfl
                -- Applying the bound on $f$ to the integral, we get:
                have h_integral_bound : ‖∮ (w : ℂ) in C(z, r), f w / (w - z)^2‖ ≤ (2 * Real.pi * r) * (C * (1 + ‖z‖ + r) ^ (n + 1)) / r^2 := by
                  refine' le_trans ( circleIntegral.norm_integral_le_of_norm_le_const _ _ ) _;
                  exact C * ( 1 + ‖z‖ + r ) ^ ( n + 1 ) / r ^ 2;
                  · positivity;
                  · intro w hw; specialize h_bound w; simp_all +decide [ abs_of_pos hr_pos ];
                    gcongr;
                    exact h_bound.trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( by linarith [ norm_sub_norm_le w z ] ) _ ) ( show 0 ≤ C by exact le_of_not_gt fun h => by have := h_bound; nlinarith [ show 0 ≤ ‖f w‖ by positivity, show 0 < ( 1 + ‖w‖ ) ^ ( n + 1 ) by positivity ] ) );
                  · rw [ mul_div ];
                simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.pi_pos.ne.symm ];
                rw [ abs_of_nonneg Real.pi_pos.le ] ; convert mul_le_mul_of_nonneg_left h_integral_bound ( by positivity : 0 ≤ ( Real.pi : ℝ ) ⁻¹ * ( 2⁻¹ : ℝ ) ) using 1 ; ring ; norm_num [ Real.pi_pos.ne', hr_pos.ne' ] ; ring_nf;
                -- Simplifying the right-hand side:
                field_simp
                ring;
              exact h_cauchy;
            -- By choosing $r = \|z\| + 1$, we can simplify the expression.
            intros z
            specialize h_cauchy z (‖z‖ + 1) (by positivity);
            refine le_trans h_cauchy ?_ ; rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> ring_nf <;> norm_cast <;> norm_num;
            · rw [ show ( 2 + ‖z‖ * 2 ) = 2 * ( 1 + ‖z‖ ) by ring, mul_pow ] ; ring_nf ; norm_num;
              nlinarith [ show 0 ≤ C * ‖z‖ * ( 1 + ‖z‖ ) ^ n * 2 ^ n by exact mul_nonneg ( mul_nonneg ( mul_nonneg ( show 0 ≤ C by have := h_bound 0; norm_num at this; nlinarith [ norm_nonneg ( f 0 ) ] ) ( norm_nonneg z ) ) ( pow_nonneg ( by positivity ) _ ) ) ( pow_nonneg ( by positivity ) _ ), show 0 ≤ C * ( n : ℝ ) * ( 1 + ‖z‖ ) ^ n * 2 ^ n by exact mul_nonneg ( mul_nonneg ( mul_nonneg ( show 0 ≤ C by have := h_bound 0; norm_num at this; nlinarith [ norm_nonneg ( f 0 ) ] ) ( Nat.cast_nonneg _ ) ) ( pow_nonneg ( by positivity ) _ ) ) ( pow_nonneg ( by positivity ) _ ) ];
            · positivity;
          have h_deriv_poly : IsPolynomial (fun z => deriv f z / ((n + 1) * 2 ^ (n + 1))) := by
            apply ih;
            · have h_deriv_poly : AnalyticOn ℂ (deriv f) Set.univ := by
                have h_diff_deriv : AnalyticOn ℂ f Set.univ := by
                  exact DifferentiableOn.analyticOn h_diff.differentiableOn ( by simpa );
                simp +zetaDelta at *;
                exact h_diff_deriv.deriv;
              exact fun z => DifferentiableAt.div_const ( h_deriv_poly.differentiableOn.differentiableAt ( by simpa ) ) _;
            · simp_all +decide [ mul_assoc, mul_div_mul_comm ];
              intro z; rw [ div_le_iff₀ ( by norm_cast; positivity ) ] ; convert h_deriv_bound z using 1 ; norm_cast ; ring;
          obtain ⟨ P, hP ⟩ := h_deriv_poly;
          use P * Polynomial.C ((n + 1 : ℂ) * 2 ^ (n + 1));
          intro z; specialize hP z; rw [ div_eq_iff ( by norm_cast; positivity ) ] at hP; aesop;
        -- By the fundamental theorem of calculus, we can integrate $P$ to find $f$.
        have h_ftc : ∀ z, f z = f 0 + ∫ t in (0 : ℝ)..1, deriv f (t * z) * z := by
          intro z;
          rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
          rotate_right;
          use fun t => f ( t * z );
          · norm_num;
          · intro t ht; convert HasDerivAt.comp t ( h_diff.differentiableAt.hasDerivAt ) ( HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) using 1 ; aesop;
          · exact Continuous.intervalIntegrable ( by rw [ show deriv f = _ from funext hP ] ; exact Continuous.mul ( by exact P.continuous.comp ( by continuity ) ) continuous_const ) _ _;
        norm_num [ hP ] at h_ftc;
        -- The integral of a polynomial is also a polynomial.
        have h_poly_integral : ∀ z, ∫ x in (0 : ℝ)..1, Polynomial.eval ((x : ℂ) * z) P = (∑ i ∈ P.support, P.coeff i * z^i * (∫ x in (0 : ℝ)..1, x^i)) := by
          norm_num [ Polynomial.eval_eq_sum, Polynomial.sum_def ];
          intro z; rw [ intervalIntegral.integral_finset_sum ] <;> norm_num [ mul_pow, mul_assoc, mul_comm, mul_left_comm ] ;
          · norm_cast;
            erw [ Finset.sum_congr rfl ] ; intros ; erw [ intervalIntegral.integral_ofReal ] ; norm_num ; ring_nf;
            norm_num;
          · exact fun i hi => Continuous.intervalIntegrable ( by exact Continuous.mul ( continuous_const ) ( by exact Continuous.mul ( by exact Continuous.pow ( Complex.continuous_ofReal ) _ ) continuous_const ) ) _ _;
        -- Therefore, $f$ is a polynomial.
        use Polynomial.C (f 0) + ∑ i ∈ P.support, Polynomial.C (P.coeff i * (∫ x in (0 : ℝ)..1, x^i)) * Polynomial.X^(i + 1);
        intro z; rw [ h_ftc z, h_poly_integral z ] ; simp +decide [ Polynomial.eval_finset_sum, mul_assoc, mul_comm, mul_left_comm, pow_succ, Finset.mul_sum _ _ _ ] ;

/-
If an entire function f is integral over the ring of polynomials, then f is a polynomial.
-/
lemma isPolynomial_of_isIntegral (f : ℂ → ℂ) (h_entire : AnalyticOn ℂ f Set.univ) :
    letI := Polynomial.algebraPi ℂ ℂ ℂ
    IsIntegral (Polynomial ℂ) f → IsPolynomial f := by
      intro h_integral;
      obtain ⟨ P, hP_monic, hP_root ⟩ := h_integral;
      -- Since each $a_i$ is a polynomial, there exist $C_i, k_i$ such that $|a_i(z)| \le C_i (1+|z|)^{k_i}$.
      have h_poly_bound : ∀ i : ℕ, ∃ C : ℝ, ∃ k : ℕ, ∀ z : ℂ, ‖(P.coeff i).eval z‖ ≤ C * (1 + ‖z‖) ^ k := by
        intro i
        obtain ⟨C, k, hC⟩ : ∃ C : ℝ, ∃ k : ℕ, ∀ z : ℂ, ‖(P.coeff i).eval z‖ ≤ C * (1 + ‖z‖) ^ k := by
          have h_poly_bound : ∀ p : ℂ[X], ∃ C : ℝ, ∃ k : ℕ, ∀ z : ℂ, ‖p.eval z‖ ≤ C * (1 + ‖z‖) ^ k := by
            intro p
            use ∑ i ∈ p.support, ‖p.coeff i‖, p.natDegree;
            intro z
            have h_poly_bound : ‖p.eval z‖ ≤ ∑ i ∈ p.support, ‖p.coeff i‖ * ‖z‖ ^ i := by
              rw [ Polynomial.eval_eq_sum, Polynomial.sum_def ];
              exact le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun _ _ => by rw [ norm_mul, norm_pow ] );
            refine le_trans h_poly_bound ?_;
            rw [ Finset.sum_mul _ _ _ ];
            exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( by linarith [ norm_nonneg z ] ) _ ) ( pow_le_pow_right₀ ( by linarith [ norm_nonneg z ] ) ( Polynomial.le_natDegree_of_mem_supp _ hi ) ) ) ( by positivity )
          exact h_poly_bound _;
        use C, k;
      -- So $|f(z)|$ is bounded by a polynomial in $|z|$.
      have h_f_poly_bound : ∃ C : ℝ, ∃ k : ℕ, ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ k := by
        -- By the properties of the roots of polynomials, we have $|f(z)| \leq \max(1, \sum_{i=0}^{n-1} |a_i(z)|)$.
        have h_f_le_max : ∀ z : ℂ, ‖f z‖ ≤ max 1 (∑ i ∈ Finset.range (P.natDegree), ‖(P.coeff i).eval z‖) := by
          intro z
          have h_f_le_max_step : ‖f z‖ ^ P.natDegree ≤ ∑ i ∈ Finset.range (P.natDegree), ‖(P.coeff i).eval z‖ * ‖f z‖ ^ i := by
            replace hP_root := congr_fun hP_root z;
            rw [ Polynomial.eval₂_eq_sum_range ] at hP_root;
            simp_all +decide [ Finset.sum_range_succ, Polynomial.eval_finset_sum ];
            simpa [ add_eq_zero_iff_eq_neg ] using norm_sum_le ( Finset.range P.natDegree ) ( fun i => Polynomial.eval z ( P.coeff i ) * f z ^ i ) |> le_trans ( by norm_num [ eq_neg_of_add_eq_zero_left hP_root ] );
          contrapose! h_f_le_max_step;
          refine' lt_of_le_of_lt ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by linarith [ le_max_left 1 ( ∑ i ∈ Finset.range P.natDegree, ‖Polynomial.eval z ( P.coeff i )‖ ), le_max_right 1 ( ∑ i ∈ Finset.range P.natDegree, ‖Polynomial.eval z ( P.coeff i )‖ ) ] ) ( show i ≤ P.natDegree - 1 from Nat.le_pred_of_lt ( Finset.mem_range.mp hi ) ) ) ( norm_nonneg _ ) ) _;
          rw [ ← Finset.sum_mul _ _ _ ];
          rcases n : P.natDegree with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
          exact mul_lt_mul_of_pos_right h_f_le_max_step.2 ( mul_pos ( by linarith ) ( pow_pos ( by linarith ) _ ) );
        choose! C k hCk using h_poly_bound;
        -- Let $C' = \sum_{i=0}^{n-1} C_i$ and $k' = \max(k_i)$.
        use (∑ i ∈ Finset.range (P.natDegree), C i) + 1, (∑ i ∈ Finset.range (P.natDegree), k i) + 1;
        intro z; specialize h_f_le_max z; refine le_trans h_f_le_max ?_; refine max_le ?_ ?_ <;> norm_num [ add_mul, Finset.sum_mul _ _ _ ];
        · exact le_add_of_nonneg_of_le ( Finset.sum_nonneg fun _ _ => mul_nonneg ( show 0 ≤ C _ from by have := hCk ‹_› 0; norm_num at this; linarith [ norm_nonneg ( Polynomial.eval 0 ( P.coeff ‹_› ) ) ] ) ( pow_nonneg ( by positivity ) _ ) ) ( one_le_pow₀ ( by linarith [ norm_nonneg z ] ) );
        · refine le_add_of_le_of_nonneg ( Finset.sum_le_sum fun i hi => le_trans ( hCk i z ) ?_ ) ( by positivity );
          exact mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by linarith [ norm_nonneg z ] ) ( by linarith [ Finset.single_le_sum ( fun i _ => Nat.zero_le ( k i ) ) hi ] ) ) ( show 0 ≤ C i from by have := hCk i 0; norm_num at this; linarith [ norm_nonneg ( Polynomial.eval 0 ( P.coeff i ) ) ] );
      exact isPolynomial_of_bound f ( show Differentiable ℂ f from fun z => ( h_entire.differentiableOn.differentiableAt <| by simpa ) ) _ _ h_f_poly_bound.choose_spec.choose_spec

/-
If (z-a)*f(z) is a polynomial, then f is a polynomial (assuming f is entire).
-/
lemma isPolynomial_of_mul_sub_c (f : ℂ → ℂ) (h_entire : AnalyticOn ℂ f Set.univ) (a : ℂ)
    (h_mul : IsPolynomial (fun z => (z - a) * f z)) : IsPolynomial f := by
      cases' h_mul with P hP;
      -- If $P(a) \neq 0$, then $f(a)$ would be undefined, contradicting the fact that $f$ is entire. Hence, $P(a) = 0$.
      have hP_a_zero : P.eval a = 0 := by
        simpa using Eq.symm ( hP a );
      obtain ⟨ Q, hQ ⟩ := Polynomial.dvd_iff_isRoot.mpr hP_a_zero;
      have h_eq : ∀ z, z ≠ a → f z = Q.eval z := by
        intro z hz; specialize hP z; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have h_eq_all : f a = Q.eval a := by
        have h_eq_all : Filter.Tendsto (fun z => f z) (nhdsWithin a {a}ᶜ) (nhds (Q.eval a)) := by
          exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_eq x hx ] ) ( Q.continuous.continuousWithinAt );
        exact tendsto_nhds_unique ( h_entire.continuousOn.continuousAt ( by simpa ) |> fun h => h.mono_left nhdsWithin_le_nhds ) h_eq_all;
      exact ⟨ Q, fun z => by by_cases h : z = a <;> simp +decide [ * ] ⟩

/-
If f is an entire function and p is a non-zero polynomial such that p*f is a polynomial, then f is a polynomial.
-/
lemma isPolynomial_of_mul_poly (f : ℂ → ℂ) (h_entire : AnalyticOn ℂ f Set.univ) (p : Polynomial ℂ) (hp : p ≠ 0)
    (h_mul : IsPolynomial (fun z => p.eval z * f z)) : IsPolynomial f := by
      -- We proceed by induction on the degree of `p`.
      induction' n : p.natDegree using Nat.strong_induction_on with n ih generalizing p f;
      by_cases h_deg : p.natDegree ≤ 0;
      · simp +zetaDelta at *;
        rw [ Polynomial.eq_C_of_natDegree_eq_zero h_deg ] at hp h_mul; obtain ⟨ q, hq ⟩ := h_mul; use Polynomial.C ( ( p.coeff 0 : ℂ ) ⁻¹ ) * q; intro z; simp +decide [ hq, hp ] ;
        simp +decide [ ← hq z, mul_comm ];
        rw [ mul_assoc, mul_inv_cancel₀ ( by aesop ), mul_one ];
      · -- Since `p` has degree `n > 0`, it has a root `a`.
        obtain ⟨a, ha⟩ : ∃ a : ℂ, p.eval a = 0 := by
          exact ( Complex.exists_root <| Polynomial.natDegree_pos_iff_degree_pos.mp <| lt_of_not_ge h_deg );
        -- We can write `p(z) = (z - a) * q(z)` where `degree q < n`.
        obtain ⟨q, hq⟩ : ∃ q : Polynomial ℂ, p = (Polynomial.X - Polynomial.C a) * q ∧ q.natDegree < p.natDegree := by
          obtain ⟨ q, hq ⟩ := Polynomial.dvd_iff_isRoot.mpr ha;
          by_cases hq_zero : q = 0 <;> simp_all ( config := { decide := Bool.true } ) [ Polynomial.natDegree_mul' ];
          linarith;
        -- By `isPolynomial_of_mul_sub_c`, `g` is a polynomial.
        have h_g_poly : IsPolynomial (fun z => q.eval z * f z) := by
          have h_g_poly : IsPolynomial (fun z => (z - a) * (q.eval z * f z)) := by
            obtain ⟨ P, hP ⟩ := h_mul; use P; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
          apply isPolynomial_of_mul_sub_c;
          exacts [ by exact DifferentiableOn.analyticOn ( by exact DifferentiableOn.mul ( q.differentiable.differentiableOn ) h_entire.differentiableOn ) ( by simpa ), h_g_poly ];
        exact ih _ ( by linarith ) _ h_entire _ ( by aesop ) h_g_poly rfl

/-
If an entire function f is algebraic over the ring of polynomials, then f is a polynomial.
-/
lemma isPolynomial_of_isAlgebraic (f : ℂ → ℂ) (h_entire : AnalyticOn ℂ f Set.univ) :
    letI := Polynomial.algebraPi ℂ ℂ ℂ
    IsAlgebraic (Polynomial ℂ) f → IsPolynomial f := by
      intro h;
      obtain ⟨ P, hP, hP' ⟩ := h;
      -- Let $a_n$ be the leading coefficient of $P$. $a_n$ is a non-zero polynomial.
      set a_n := Polynomial.leadingCoeff P with ha_n_def;
      -- Since $f$ is entire and $a_n$ is a polynomial, $a_n • f$ is entire.
      have h_a_n_f_entire : AnalyticOn ℂ (fun z => a_n.eval z * f z) Set.univ := by
        apply_rules [ AnalyticOn.mul, h_entire ];
        exact DifferentiableOn.analyticOn ( by exact Differentiable.differentiableOn ( by exact Polynomial.differentiable _ ) ) ( by simpa );
      -- By `isPolynomial_of_isIntegral`, `a_n • f` is a polynomial.
      have h_a_n_f_poly : IsPolynomial (fun z => a_n.eval z * f z) := by
        apply isPolynomial_of_isIntegral;
        · exact h_a_n_f_entire;
        · convert isIntegral_leadingCoeff_smul _;
          rotate_left;
          exact ℂ[X];
          exact ℂ → ℂ;
          exact inferInstance;
          exact Pi.commRing;
          exact P;
          field_simp;
          constructor <;> intro h;
          · exact fun x [Algebra ℂ[X] (ℂ → ℂ)] h => isIntegral_leadingCoeff_smul P x h;
          · convert h f hP' using 1;
      -- Since $a_n \neq 0$, by `isPolynomial_of_mul_poly`, $f$ is a polynomial.
      apply isPolynomial_of_mul_poly f h_entire a_n (by
      aesop) h_a_n_f_poly

/-
If f is a transcendental entire function (entire and not a polynomial), then it is transcendental over the ring of polynomials.
-/
lemma transcendental_of_transcendentalEntire (f : ℂ → ℂ) (hf : TranscendentalEntire f) :
  letI := Polynomial.algebraPi ℂ ℂ ℂ
  Transcendental (Polynomial ℂ) f := by
    intro H;
    convert isPolynomial_of_isAlgebraic f ?_ H;
    · unfold TranscendentalEntire at hf; aesop;
    · exact DifferentiableOn.analyticOn ( hf.1.differentiableOn ) ( by simpa )

/-
Let $\{S_k\}$ be any sequence of sets in the complex plane, each of which has no finite
limit point. Then there exists a sequence $\{n_k\}$ of positive integers and a
transcendental entire function $f(z)$ such that $f^{(n_k)}(z) = 0$ if $z \in S_k$.
-/
theorem theorem_1
    {S : ℕ → Set ℂ}
    (h : ∀ (k), derivedSet (S k) = ∅) :
  letI := Polynomial.algebraPi ℂ ℂ ℂ
  ∃ (f : ℂ → ℂ) (n : ℕ → ℕ),
    Differentiable ℂ f ∧ Transcendental (Polynomial ℂ) f ∧ ∀ k, 0 < n k ∧ ∀ {z} (_: z ∈ S k),
      iteratedDeriv (n k) f z = 0 := by
  have := exists_radii S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) );
  obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := this;
  obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := exists_auxiliary_points S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) ) r hr₁ ( fun n => by linarith [ hr₂ n ] );
  refine' ⟨ f S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) ) r hr₁ ( fun n => by linarith [ hr₂ n ] ) ( fun n => by linarith [ hr₂ n ] ) hr₃ c hc₁ hc₃ hc₂, fun n => k_seq S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) ) r hr₁ ( fun n => by linarith [ hr₂ n ] ) ( fun n => by linarith [ hr₂ n ] ) hr₃ c hc₁ hc₃ hc₂ n, _, _, _ ⟩;
  · exact fun z => ( f_entire S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) ) r hr₁ ( fun n => by linarith [ hr₂ n ] ) ( fun n => by linarith [ hr₂ n ] ) hr₃ c hc₁ hc₃ hc₂ |> fun h => h.differentiableOn.differentiableAt <| by simpa );
  · apply_rules [ transcendental_of_transcendentalEntire ];
    apply_rules [ f_transcendental ];
  · intro k;
    refine' ⟨ _, fun { z } hz => _ ⟩;
    · induction' k with k ih;
      · exact Nat.cast_pos.mpr ( by norm_num : 0 < 1 );
      · exact lt_of_le_of_lt ( Nat.zero_le _ ) ( k_seq_strict_mono S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) ) r hr₁ ( fun n => by linarith [ hr₂ n ] ) ( fun n => by linarith [ hr₂ n ] ) hr₃ c hc₁ hc₃ hc₂ k.lt_succ_self );
    · exact f_deriv_vanishes_on_Sn S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) ) r hr₁ ( fun n => by linarith [ hr₂ n ] ) ( fun n => by linarith [ hr₂ n ] ) hr₃ c hc₁ hc₃ hc₂ k z hz

theorem erdos_229.not_polynomial :
    letI := Polynomial.algebraPi ℂ ℂ ℂ
    (∀ (S : ℕ → Set ℂ), (∀ n, derivedSet (S n) = ∅) →
    ∃ (f : ℂ → ℂ), (¬ ∃ p : Polynomial ℂ, f = fun z => p.eval z) ∧ Differentiable ℂ f ∧ ∀ n ≥ 1,
      ∃ k, ∀ z ∈ S n, iteratedDeriv k f z = 0) := by
  intro S hS;
  -- Apply the theorem with the given sequence S and n ≥ 1.
  obtain ⟨f, n, hf_diff, hf_transcendental, hf_zeros⟩ := theorem_1 hS;
  refine' ⟨ f, _, hf_diff, fun n hn => _ ⟩;
  · contrapose! hf_transcendental;
    obtain ⟨ p, rfl ⟩ := hf_transcendental;
    refine' Classical.not_not.2 ⟨ Polynomial.X - Polynomial.C p, _, _ ⟩ <;> norm_num;
    exact ne_of_apply_ne Polynomial.derivative <| by norm_num;
  · exact ⟨ _, fun z hz => hf_zeros n |>.2 hz ⟩

/-!
# Erdős Problem 229

*Reference:* [erdosproblems.com/229](https://www.erdosproblems.com/229)
-/

/--
Let $(S_n)_{n \ge 1}$ be a sequence of sets of complex numbers, none of which have a finite
limit point. Does there exist an entire transcendental function $f(z)$ such that, for all $n \ge 1$, there
exists some $k_n \ge 0$ such that
$$
  f^{(k_n)}(z) = 0 \quad \text{for all } z \in S_n?
$$

Solved in the affirmative by Barth and Schneider [BaSc72].

[BaSc72] Barth, K. F. and Schneider, W. J., _On a problem of Erdős concerning the zeros of_
_the derivatives of an entire function_. Proc. Amer. Math. Soc. (1972), 229--232.-/
theorem erdos_229 :
    letI := Polynomial.algebraPi ℂ ℂ ℂ
    (∀ (S : ℕ → Set ℂ), (∀ n, derivedSet (S n) = ∅) →
    ∃ (f : ℂ → ℂ), Transcendental (Polynomial ℂ) f ∧ Differentiable ℂ f ∧ ∀ n ≥ 1,
      ∃ k, ∀ z ∈ S n, iteratedDeriv k f z = 0) := by
  intro S hS
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, ¬ (∃ p : Polynomial ℂ, f = fun z => p.eval z) ∧ Differentiable ℂ f ∧ ∀ n ≥ 1, ∃ k : ℕ, ∀ z ∈ S n, iteratedDeriv k f z = 0 := by
    convert erdos_229.not_polynomial S hS using 1;
  refine' ⟨ f, _, hf.2.1, hf.2.2 ⟩;
  -- Apply the lemma that states if f is transcendental entire, then it's transcendental over the ring of polynomials.
  apply transcendental_of_transcendentalEntire f ⟨hf.2.1, by
    exact fun ⟨ p, hp ⟩ => hf.1 ⟨ p, funext fun z => by simpa using hp z ⟩⟩

#print axioms erdos_229
-- 'erdos_229' depends on axioms: [propext, Classical.choice, Quot.sound]
