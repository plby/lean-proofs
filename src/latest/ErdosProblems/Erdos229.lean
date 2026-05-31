/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 229.
https://www.erdosproblems.com/forum/thread/229

Informal authors:
- K. F. Barth
- W. J. Schneider
- ChatGPT

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos229.md
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

namespace Erdos229

-- Remaining suppressions cover generated proof structure that is risky to
-- rewrite mechanically in this cleanup pass.
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.style.multiGoal false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

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
  classical
  let N : ℕ := m * (L + 1)
  let D : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ := Polynomial.derivative
  let jet : Polynomial.degreeLT ℂ N →ₗ[ℂ] (Fin m × Fin (L + 1) → ℂ) :=
    LinearMap.pi fun x : Fin m × Fin (L + 1) =>
      ((Polynomial.aeval (b x.1) : Polynomial ℂ →ₐ[ℂ] ℂ).toLinearMap).comp
        ((D ^ x.2.val).comp (Polynomial.degreeLT ℂ N).subtype)
  have hDpow : ∀ (n : ℕ) (p : Polynomial ℂ), (D ^ n) p = derivative^[n] p := by
    intro n p
    induction n generalizing p with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ']
        rw [Module.End.mul_apply]
        rw [ih]
        rw [Function.iterate_succ_apply']
  have hjet_inj : Function.Injective jet := by
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    by_cases hp0 : P.1 = 0
    · exact hp0
    exfalso
    have hzero : ∀ (j : Fin m) (l : Fin (L + 1)),
        (derivative^[l.val] P.1).eval (b j) = 0 := by
      intro j l
      have hcoord := congr_fun hP (j, l)
      change ((Polynomial.aeval (b j) : Polynomial ℂ →ₐ[ℂ] ℂ).toLinearMap)
          ((D ^ l.val) P.1) = 0 at hcoord
      simpa [hDpow l.val P.1] using hcoord
    have hdiv : ∀ j : Fin m, (X - C (b j)) ^ (L + 1) ∣ P.1 := by
      intro j
      have hlt : L < P.1.rootMultiplicity (b j) := by
        apply Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hp0
        intro n hn
        exact hzero j ⟨n, Nat.lt_succ_of_le hn⟩
      exact (Polynomial.le_rootMultiplicity_iff hp0).mp (Nat.succ_le_of_lt hlt)
    have hpair :
        Pairwise (Function.onFun IsCoprime fun j : Fin m => (X - C (b j)) ^ (L + 1)) := by
      intro i j hij
      exact ((Polynomial.pairwise_coprime_X_sub_C hb) hij).pow
    have hprod : (∏ j : Fin m, (X - C (b j)) ^ (L + 1)) ∣ P.1 := by
      exact Fintype.prod_dvd_of_coprime hpair hdiv
    have hfac_ne : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        (X - C (b j)) ^ (L + 1) ≠ (0 : Polynomial ℂ) := by
      intro j hj
      exact pow_ne_zero _ (Polynomial.monic_X_sub_C (b j)).ne_zero
    have hprod_nat :
        (∏ j : Fin m, (X - C (b j)) ^ (L + 1)).natDegree = m * (L + 1) := by
      rw [Polynomial.natDegree_prod Finset.univ
        (fun j : Fin m => (X - C (b j)) ^ (L + 1)) hfac_ne]
      simp [Polynomial.natDegree_pow]
    have hpNatLt : P.1.natDegree < m * (L + 1) := by
      have hpdeg : P.1.degree < (m * (L + 1) : ℕ) := by
        simpa [N] using Polynomial.mem_degreeLT.mp P.2
      rw [Polynomial.degree_eq_natDegree hp0] at hpdeg
      exact_mod_cast hpdeg
    have hprod_le : m * (L + 1) ≤ P.1.natDegree := by
      simpa [hprod_nat] using Polynomial.natDegree_le_of_dvd hprod hp0
    exact Nat.not_le_of_gt hpNatLt hprod_le
  have hdim : Module.finrank ℂ (Polynomial.degreeLT ℂ N) =
      Module.finrank ℂ (Fin m × Fin (L + 1) → ℂ) := by
    rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℂ N)]
    simp [N]
  have hjet_surj : Function.Surjective jet :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hjet_inj
  obtain ⟨P, hP⟩ := hjet_surj (fun x : Fin m × Fin (L + 1) => γ x.1 x.2)
  refine ⟨P.1, ?_⟩
  intro j l
  have hcoord := congr_fun hP (j, l)
  change ((Polynomial.aeval (b j) : Polynomial ℂ →ₐ[ℂ] ℂ).toLinearMap)
      ((D ^ l.val) P.1) = γ j l at hcoord
  simpa [hDpow l.val P.1] using hcoord

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
  · refine' ⟨ r • ( ‖x‖⁻¹ • x ), _, _ ⟩ <;> simp_all +decide;
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
  classical
  obtain ⟨ρ, hρr, hρan⟩ := analytic_on_larger_disk r hr f hf
  obtain ⟨R1, hR1r, hR1ρ⟩ := exists_between hρr
  obtain ⟨R2, hR2r, hR2R1⟩ := exists_between hR1r
  have hR1pos : 0 < R1 := by linarith
  have hR2pos : 0 < R2 := by linarith
  let Rbig : NNReal := ⟨R1, le_of_lt hR1pos⟩
  let Rsmall : NNReal := ⟨R2, le_of_lt hR2pos⟩
  let ps : FormalMultilinearSeries ℂ ℂ ℂ := cauchyPowerSeries f 0 Rbig
  let P : ℕ → Polynomial ℂ := fun N =>
    ∑ i ∈ Finset.range N, Polynomial.C (ps.coeff i) * Polynomial.X ^ i
  have hpoly_eval : ∀ (N : ℕ) (z : ℂ), (P N).eval z = ps.partialSum N z := by
    intro N z
    rw [FormalMultilinearSeries.partialSum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp [smul_eq_mul, mul_comm]
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 Rbig) := by
    exact hρan.differentiableOn.mono (Metric.closedBall_subset_ball hR1ρ)
  have hps : HasFPowerSeriesOnBall f ps 0 Rbig := by
    simpa [ps] using
      DifferentiableOn.hasFPowerSeriesOnBall (R := Rbig) (c := 0) hd
        (by simpa [Rbig] using hR1pos)
  have hlt : (Rsmall : ENNReal) < (Rbig : ENNReal) := by
    exact_mod_cast hR2R1
  have hunif := hps.tendstoUniformlyOn hlt
  have hev := (Metric.tendstoUniformlyOn_iff.mp hunif) ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨P N, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.ball (0 : ℂ) Rsmall := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hR2r
  have hdist := hN N le_rfl z hzball
  rw [hpoly_eval N z]
  simpa [dist_eq_norm] using hdist

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
  -- Let $m = |S|$. Since $S$ is a finite set, there exists a bijection $e : \{0, \dots, m - 1\} \to S$.
  obtain ⟨e, he⟩ : ∃ e : Fin S.card ≃ S, True := by
    exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
  -- Define $\gamma' : \{0, \dots, m - 1\} \to \{0, \dots, L\} \to \mathbb{C}$ by $\gamma'(j, l) = \gamma(e(j), l)$.
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
  let S : Set ℂ := ↑(A ∪ B)
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
    simp;
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
        exact ⟨ n, fun h => absurd ( h.mono <| show { x | ∃ z ∈ ⋃ j ∈ Finset.range ( n + 2 ), S j, ‖z‖ = x } ⊇ Set.Ioo ( n + 1 : ℝ ) ( n + 2 ) from fun x hx => h_bad_rad x hx.1 hx.2 ) ( by exact fun h' => absurd ( h'.measure_zero <| MeasureTheory.MeasureSpace.volume ) ( by simp +decide ) ) ⟩;
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
      · exact fun H => absurd ( H.measure_zero <| MeasureTheory.MeasureSpace.volume ) ( by simp +decide [ * ] )

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
        · intro b hb l; rw [ ← hP₀.2.1 b hb l ] ; simp +decide [ mul_assoc ] ;
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
      (∀ z, ‖z‖ ≤ r (m - 1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
      (∀ i ≤ m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m - 1)), ∀ l ≤ k_next, (derivative^[l] T_next).eval z = 0) ∧
      (∀ i < m - 1, ∀ l ≤ k_next, (derivative^[l] T_next).eval (c i) = 0) ∧
      (∀ i ≤ m, ∀ z ∈ S i ∩ {z | r (m - 1) < ‖z‖ ∧ ‖z‖ < r m}, ∀ l ≤ k_next, (derivative^[l] T_next).eval z = -(derivative^[l] F_prev).eval z) ∧
      (∀ l ≤ k_next, (derivative^[l] T_next).eval (c (m - 1)) = if l = k_prev then 1 - (derivative^[l] F_prev).eval (c (m - 1)) else -(derivative^[l] F_prev).eval (c (m - 1))) := by
        have _hm := hm
        have _hr_pos := hr_pos
        have h_finite : Set.Finite (⋃ i ≤ m, S i ∩ Metric.ball 0 (r (m - 1))) ∧ Set.Finite (⋃ i ≤ m, S i ∩ {z | r (m - 1) < ‖z‖ ∧ ‖z‖ < r m}) := by
          constructor <;> refine' Set.Finite.biUnion ( Set.finite_Iic _ ) fun i hi => _;
          · have := hS i;
            exact this ( Metric.closedBall 0 ( r ( m - 1 ) ) ) ( ProperSpace.isCompact_closedBall _ _ ) |> Set.Finite.subset <| Set.inter_subset_inter_right _ <| Metric.ball_subset_closedBall;
          · refine' Set.Finite.subset ( hS i ( Metric.closedBall 0 ( r m ) ) ( ProperSpace.isCompact_closedBall _ _ ) ) _;
            exact fun x hx => ⟨ hx.1, mem_closedBall_zero_iff.mpr hx.2.2.le ⟩;
        have h_finite_union : Set.Finite (⋃ i ≤ m, S i ∩ Metric.ball 0 (r (m - 1))) ∧ Set.Finite (⋃ i ≤ m, S i ∩ {z | r (m - 1) < ‖z‖ ∧ ‖z‖ < r m}) ∧ Set.Finite (Set.image c (Finset.range (m - 1))) ∧ Set.Finite {c (m - 1)} := by
          exact ⟨ h_finite.1, h_finite.2, Set.toFinite _, Set.finite_singleton _ ⟩;
        obtain ⟨A, B, hA, hB, h_disjoint, h_union⟩ : ∃ A B : Finset ℂ, (∀ a ∈ A, ‖a‖ < r (m - 1)) ∧ (∀ b ∈ B, r (m - 1) < ‖b‖) ∧ (⋃ i ≤ m, S i ∩ Metric.ball 0 (r (m - 1))) ∪ (Set.image c (Finset.range (m - 1))) = A ∧ (⋃ i ≤ m, S i ∩ {z | r (m - 1) < ‖z‖ ∧ ‖z‖ < r m}) ∪ {c (m - 1)} = B := by
          refine' ⟨ h_finite_union.1.toFinset ∪ Finset.image c ( Finset.range ( m - 1 ) ), h_finite_union.2.1.toFinset ∪ { c ( m - 1 ) }, _, _, _, _ ⟩ <;> simp_all +decide;
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
      induction n generalizing f g with
      | zero =>
        simp_all +decide
      | succ n ih =>
        simp_all +decide [ Function.iterate_succ_apply' ]

/-
Inductive step for the construction of the sequence of polynomials.
-/
set_option maxHeartbeats 8000000 in
-- This step construction needs a larger concrete heartbeat budget.
lemma exists_next_step (m : ℕ) (hm : m > 0)
    (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (k : ℕ → ℕ) (hk_mono : StrictMonoOn k (Set.Iic (m - 1)))
    (F_prev : Polynomial ℂ)
    (hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m - 1)), (derivative^[k i] F_prev).eval z = 0)
    (hF_vals : ∀ i < m - 1, (derivative^[k i] F_prev).eval (c i) = 1) :
    ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
      k_next > k (m - 1) ∧ k_next > F_prev.natDegree ∧
      (∀ z, ‖z‖ ≤ r (m - 1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
      let F_next := F_prev + T_next
      (∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r m), (derivative^[k i] F_next).eval z = 0) ∧
      (∀ z ∈ S m ∩ Metric.ball 0 (r m), (derivative^[k_next] F_next).eval z = 0) ∧
      (∀ i < m, (derivative^[k i] F_next).eval (c i) = 1) := by
        have _hc_inj := hc_inj
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
          · have := hT_next.2.2.2.1 i ( by linarith ) z ⟨ hz.1, ⟨ by linarith, by simpa using hz.2.out ⟩ ⟩ ( k i ) ( by linarith [ hk_mono.le_iff_le ( show i ≤ m - 1 from Nat.le_sub_one_of_lt hi ) ( show m - 1 ≤ m - 1 from le_rfl ) |>.2 ( Nat.le_sub_one_of_lt hi ) ] ) ; simp_all +decide [ Polynomial.eval_add ] ;
        · intro z hz
          have hF_prev_zero : (derivative^[k (m - 1) + F_prev.natDegree + 1] F_prev).eval z = 0 := by
            rw [ Polynomial.iterate_derivative_eq_zero ] ; aesop;
            linarith;
          by_cases hz' : ‖z‖ < r ( m - 1 ) <;> simp_all +decide [ Polynomial.eval_add ];
          · convert hT_next.2.1 m ( by linarith ) z hz.1 hz' _ le_rfl using 1;
          · cases eq_or_lt_of_le hz' <;> simp_all +decide [ Set.ext_iff ];
            · exact False.elim <| hr_avoid ( m - 1 ) z ( by linarith ) m ( by omega ) hz.1;
            · have := hT_next.2.2.2.1 m ( by linarith ) z hz.1 ‹_› hz.2 ( k ( m - 1 ) + F_prev.natDegree + 1 ) ( by linarith ) ; aesop;
        · intro i hi; specialize hT_next; rcases lt_or_eq_of_le ( Nat.le_sub_one_of_lt hi ) <;> simp_all +decide;
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
    (k : ℕ → ℕ) (hk_mono : StrictMonoOn k (Set.Iic (m - 1)))
    (F_prev : Polynomial ℂ)
    (hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m - 1)), (derivative^[k i] F_prev).eval z = 0)
    (hF_vals : ∀ i < m - 1, (derivative^[k i] F_prev).eval (c i) = 1) :
    ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
      k_next > k (m - 1) ∧ k_next > F_prev.natDegree ∧
      (∀ z, ‖z‖ ≤ r (m - 1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
      let F_next := F_prev + T_next
      (∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r m), (derivative^[k i] F_next).eval z = 0) ∧
      (∀ z ∈ S m ∩ Metric.ball 0 (r m), (derivative^[k_next] F_next).eval z = 0) ∧
      (∀ i < m, (derivative^[k i] F_next).eval (c i) = 1) := by
  exact exists_next_step m hm S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem
    k hk_mono F_prev hF_zeros hF_vals

lemma exists_next_step_v3 (m : ℕ) (hm : m > 0)
    (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j)
    (k : ℕ → ℕ) (hk_mono : StrictMonoOn k (Set.Iic (m - 1)))
    (F_prev : Polynomial ℂ)
    (hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m - 1)), (derivative^[k i] F_prev).eval z = 0)
    (hF_vals : ∀ i < m - 1, (derivative^[k i] F_prev).eval (c i) = 1) :
    ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
      k_next > k (m - 1) ∧ k_next > F_prev.natDegree ∧
      (∀ z, ‖z‖ ≤ r (m - 1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
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
    (k : ℕ → ℕ) (hk_mono : StrictMonoOn k (Set.Iic (m - 1)))
    (F_prev : Polynomial ℂ)
    (hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m - 1)), (derivative^[k i] F_prev).eval z = 0)
    (hF_vals : ∀ i < m - 1, (derivative^[k i] F_prev).eval (c i) = 1) :
    ∃ k_next : ℕ, ∃ T_next : Polynomial ℂ,
      k_next > k (m - 1) ∧ k_next > F_prev.natDegree ∧
      (∀ z, ‖z‖ ≤ r (m - 1) → ‖T_next.eval z‖ < 2 ^ (-(m : ℝ) + 1)) ∧
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

def k_of (L : History) (i : ℕ) : ℕ :=
  match L.drop i with
  | [] => 0
  | x :: _ => x.1

noncomputable def T_of (L : History) (i : ℕ) : Polynomial ℂ :=
  match L.drop i with
  | [] => 0
  | x :: _ => x.2

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
  intro hm
  simp [k_of, F_of, T_of] at *
  intro a ha b hb hab
  simp at ha hb
  omega

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
  unfold k_of
  by_cases hi : i < L.length
  · simp only [hi, if_true]
    rw [List.drop_append_of_le_length (Nat.le_of_lt hi)]
    cases hdrop : L.drop i with
    | nil =>
        have hlen := congrArg List.length hdrop
        simp at hlen
        omega
    | cons y ys => simp
  · by_cases heq : i = L.length
    · subst i
      simp
    · have hlen : (L ++ [x]).length ≤ i := by
        simp
        omega
      simp [hi, heq, List.drop_eq_nil_of_le hlen]

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
  by_cases hi : i < L.length
  · simp only [hi, if_true]
    rw [List.drop_append_of_le_length (Nat.le_of_lt hi)]
    cases hdrop : L.drop i with
    | nil =>
        have hlen := congrArg List.length hdrop
        simp at hlen
        omega
    | cons y ys => simp
  · by_cases heq : i = L.length
    · subst i
      simp
    · have hlen : (L ++ [x]).length ≤ i := by
        simp
        omega
      simp [hi, heq, List.drop_eq_nil_of_le hlen]

/-
Definitions of T_seq, k_seq, and f.
-/
noncomputable def T_seq (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) : Polynomial ℂ :=
  match (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).drop n with
  | [] => 0
  | x :: _ => x.2

noncomputable def k_seq (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) : ℕ :=
  match (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).drop n with
  | [] => 0
  | x :: _ => x.1

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
  classical
  unfold next_step
  simp only [hL, ↓reduceDIte]
  by_cases hm : L.length = 0
  · exact False.elim (hL_nonempty (List.eq_nil_of_length_eq_zero hm))
  · simp only [hm, ↓reduceDIte]
    let m := L.length
    let k := k_of L
    let F_prev := F_of L
    have hm_pos : m > 0 := Nat.pos_of_ne_zero hm
    let hk_mono : StrictMonoOn k (Iic (m - 1)) := by
      have hk_mono : StrictMonoOn k (Iio m) := by
        apply hL hm_pos |>.2.1
      exact hk_mono.mono (fun x hx => Nat.lt_of_le_of_lt hx (Nat.pred_lt hm))
    let hF_zeros : ∀ i < m, ∀ z ∈ S i ∩ Metric.ball 0 (r (m - 1)), (derivative^[k i] F_prev).eval z = 0 := by
      have := hL hm_pos
      intro i hi z hz
      convert this.2.2 (m - 1) (Nat.sub_lt hm_pos zero_lt_one) |>.1 i (Nat.le_sub_one_of_lt hi) z ⟨hz.1, hz.2.out.trans_le (by simp)⟩
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
      simp +zetaDelta at *
    let hF_vals : ∀ i < m - 1, (derivative^[k i] F_prev).eval (c i) = 1 := by
      have := hL hm_pos
      intro i hi
      convert this.2.2 (m - 1) (Nat.sub_lt hm_pos zero_lt_one) |>.2.1 i hi
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm), List.take_length]
    let res := exists_next_step_final m hm_pos S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem k hk_mono F_prev hF_zeros hF_vals
    have hspec := Classical.choose_spec (Classical.choose_spec res)
    exact ⟨hspec.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩

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
  classical
  by_cases hnil : L = []
  · subst L
    simpa [next_step, IsValid] using valid_zero S r c
  · let x := next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem L
    let m := L.length
    have hm : m > 0 := List.length_pos_iff.mpr hnil
    have hspec := next_step_spec S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem L hL hnil
    change IsValid S r c (L ++ [x])
    intro hnew
    constructor
    · have h0 := (hL hm).1
      simpa [x, m, k_of_append, hm] using h0
    constructor
    · intro a ha b hb hab
      have ha_lt_succ : a < m + 1 := by simpa [m] using ha
      have hb_lt_succ : b < m + 1 := by simpa [m] using hb
      have ha_le_m : a ≤ m := Nat.le_of_lt_succ ha_lt_succ
      have hb_le_m : b ≤ m := Nat.le_of_lt_succ hb_lt_succ
      have ha_lt_m : a < m := lt_of_lt_of_le hab hb_le_m
      by_cases hb_lt_m : b < m
      · have hmono := (hL hm).2.1
        have := hmono ha_lt_m hb_lt_m hab
        simpa [x, m, k_of_append, ha_lt_m, hb_lt_m] using this
      · have hb_eq_m : b = m := by omega
        subst b
        have hk_le : k_of L a ≤ k_of L (m - 1) := by
          by_cases ha_eq : a = m - 1
          · subst a
            exact le_rfl
          · have ha_lt_pred : a < m - 1 := by omega
            have hmono := (hL hm).2.1
            exact le_of_lt (hmono ha_lt_m (Nat.sub_lt hm zero_lt_one) ha_lt_pred)
        exact lt_of_le_of_lt (by simpa [x, m, k_of_append, ha_lt_m] using hk_le)
          (by simp [x, m, k_of_append, hspec])
    · intro j hj
      by_cases hj_lt : j < m
      · have hj_old := (hL hm).2.2 j hj_lt
        have htake : (L ++ [x]).take (j + 1) = L.take (j + 1) := by
          rw [List.take_append_of_le_length]
          omega
        constructor
        · intro i hi z hz
          have hi_lt_m : i < m := lt_of_le_of_lt hi hj_lt
          have h_old := hj_old.1 i hi z hz
          simpa [htake, k_of_append, m, hi_lt_m] using h_old
        constructor
        · intro i hi
          have hi_lt_m : i < m := lt_trans hi hj_lt
          have h_old := hj_old.2.1 i hi
          simpa [htake, k_of_append, m, hi_lt_m] using h_old
        · intro hj_pos z hz
          have h_old := hj_old.2.2 hj_pos z hz
          simpa [T_of_append, m, hj_lt] using h_old
      · have hj_lt_succ : j < m + 1 := by simpa [m] using hj
        have hj_eq : j = m := by omega
        subst j
        have htake : (L ++ [x]).take (m + 1) = L ++ [x] := by
          simp [m]
        constructor
        · intro i hi z hz
          rcases lt_or_eq_of_le hi with hi_lt | rfl
          · have h_old := hspec.2.2.1 i hi_lt z hz
            simpa [htake, F_of_append, k_of_append, m, hi_lt, x] using h_old
          · have h_new := hspec.2.2.2.1 z hz
            simpa [htake, F_of_append, k_of_append, m, x] using h_new
        constructor
        · intro i hi
          have h_val := hspec.2.2.2.2 i hi
          simpa [htake, F_of_append, k_of_append, m, hi, x] using h_val
        · intro hm_pos z hz
          have h_bound := hspec.2.1 z hz
          simpa [T_of_append, m, x] using h_bound

/-
The history sequence is valid for all n.
-/
lemma history_seq_valid (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) :
    IsValid S r c (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) := by
      induction n with
      | zero =>
        -- The base case is when the list is [(1, 0)], which is valid by definition.
        apply valid_zero;
      | succ n ih =>
        convert valid_next_step S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem _ ih using 1

lemma history_seq_length (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) :
    (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).length = n + 1 := by
  induction n with
  | zero => simp [history_seq]
  | succ n ih => simp [history_seq, ih]

/-
The polynomials T_n satisfy the required decay bound.
-/
lemma T_seq_bound (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (n : ℕ) (hn : n > 0) :
    ∀ z, ‖z‖ ≤ r (n - 1) → ‖(T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z‖ < 2 ^ (-(n : ℝ) + 1) := by
  classical
  let L := history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n
  have hvalid := history_seq_valid S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n
  have hlen : L.length = n + 1 := by
    simpa [L] using history_seq_length S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n
  have hLpos : L.length > 0 := by omega
  have hj : n < L.length := by omega
  have hbound := (hvalid hLpos).2.2 n hj |>.2.2 hn
  intro z hz
  change ‖(T_of L n).eval z‖ < 2 ^ (-(n : ℝ) + 1)
  exact hbound z hz

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
        induction k with
        | zero =>
          simpa using this;
        | succ k ih =>
          simp_all +decide [ iteratedDeriv_succ ];
          apply_rules [ TendstoLocallyUniformlyOn.deriv ];
          · refine' Filter.Eventually.of_forall fun N => _;
            -- The sum of polynomials is a polynomial, and the k-th derivative of a polynomial is also a polynomial.
            have h_poly : ∀ N, ∃ P : Polynomial ℂ, ∀ z, ∑ n ∈ Finset.range N, (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n).eval z = P.eval z := by
              exact fun N => ⟨ ∑ n ∈ Finset.range N, T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n, fun z => by simp +decide [ Polynomial.eval_finset_sum ] ⟩;
            obtain ⟨ P, hP ⟩ := h_poly N; simp +decide [ funext hP ] ;
            -- The k-th derivative of a polynomial is also a polynomial.
            have h_poly_deriv : ∀ k, ∃ Q : Polynomial ℂ, iteratedDeriv k (fun x => P.eval x) = fun x => Q.eval x := by
              intro k
              induction k with
              | zero =>
                simp_all +decide
                exact ⟨ P, rfl ⟩;
              | succ k ih =>
                simp_all +decide [ iteratedDeriv_succ ]
                obtain ⟨ Q, hQ ⟩ := ih; use Polynomial.derivative Q; ext; simp +decide [ hQ ] ;
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
  classical
  refine strictMono_nat_of_lt_succ ?_
  intro n
  let L := history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n
  have hvalid := history_seq_valid S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n
  have hlen : L.length = n + 1 := by
    simpa [L] using history_seq_length S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n
  have hnil : L ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [hlen] at this
  have hspec := next_step_spec S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem L hvalid hnil
  simpa [k_seq, history_seq, L, hlen] using hspec.1

lemma iteratedDeriv_eval_polynomial (P : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun z => P.eval z) = fun z => (Polynomial.derivative^[k] P).eval z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      ext z
      rw [Function.iterate_succ_apply']
      simp

lemma F_of_history_seq_eq_sum_T_seq (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (N : ℕ) :
    F_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N) =
      ∑ j ∈ Finset.range (N + 1), T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j := by
  induction N with
  | zero =>
      simp [history_seq, F_of, T_seq]
  | succ N ih =>
      rw [history_seq, F_of_append, ih]
      conv_rhs => rw [show N + 1 + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ]
      congr 1
      simp [T_seq, history_seq, history_seq_length S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N]

lemma k_seq_eq_k_of_history_seq (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) {n N : ℕ} (h : n ≤ N) :
    k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n =
      k_of (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N) n := by
  induction N generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ N ih =>
      by_cases hn : n ≤ N
      · have ih' := ih hn
        rw [history_seq, k_of_append]
        have hlen := history_seq_length S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
        have hnlt : n < (history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N).length := by omega
        simp [hnlt, ih']
      · have hn_eq : n = N + 1 := by omega
        subst n
        rw [history_seq, k_of_append]
        simp [k_seq, history_seq, history_seq_length S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N]

/-
The derivative of the partial sum vanishes on S_n inside the ball.
-/
lemma partial_sum_deriv_vanishes (S : ℕ → Set ℂ) (hS : ∀ n, HasNoFiniteLimitPoint (S n))
    (r : ℕ → ℝ) (hr : StrictMono r) (hr_pos : ∀ n, 0 ≤ r n) (hr_gt : ∀ n, n + 1 < r n)
    (hr_avoid : ∀ n, {z | ‖z‖ = r n} ∩ (⋃ j ∈ Finset.range (n + 2), S j) = ∅)
    (c : ℕ → ℂ) (hc_norm : ∀ n, r n < ‖c n‖ ∧ ‖c n‖ < r (n + 1)) (hc_inj : Function.Injective c)
    (hc_mem : ∀ n, c n ∉ ⋃ j, S j) (N : ℕ) (n : ℕ) (hn : n ≤ N) (z : ℂ) (hz : z ∈ S n) (hz_norm : ‖z‖ < r N) :
    (iteratedDeriv (k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n) (fun w => ∑ j ∈ Finset.range (N + 1), (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j).eval w)) z = 0 := by
  classical
  let L := history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
  have hvalid := history_seq_valid S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
  have hlen : L.length = N + 1 := by
    simpa [L] using history_seq_length S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
  have hLpos : L.length > 0 := by omega
  have hNlt : N < L.length := by omega
  have hball : z ∈ S n ∩ Metric.ball 0 (r N) := by
    exact ⟨hz, by simpa [Metric.mem_ball, dist_zero_right] using hz_norm⟩
  have hzero := (hvalid hLpos).2.2 N hNlt |>.1 n hn z hball
  have htake : L.take (N + 1) = L := by
    simp [L, hlen]
  have hks : k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n = k_of L n :=
    k_seq_eq_k_of_history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem hn
  have hFsum : F_of L = ∑ j ∈ Finset.range (N + 1), T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j := by
    simpa [L] using F_of_history_seq_eq_sum_T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
  have hfun :
      (fun w => ∑ j ∈ Finset.range (N + 1), (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j).eval w) =
        fun w => (∑ j ∈ Finset.range (N + 1), T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j).eval w := by
    funext w
    simp [Polynomial.eval_finset_sum]
  rw [hfun, iteratedDeriv_eval_polynomial]
  rw [← hFsum, hks]
  simpa [L, htake] using hzero

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
  classical
  let L := history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
  have hvalid := history_seq_valid S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
  have hlen : L.length = N + 1 := by
    simpa [L] using history_seq_length S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
  have hLpos : L.length > 0 := by omega
  have hNlt : N < L.length := by omega
  have hval := (hvalid hLpos).2.2 N hNlt |>.2.1 n hn
  have htake : L.take (N + 1) = L := by
    simp [L, hlen]
  have hks : k_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n = k_of L n :=
    k_seq_eq_k_of_history_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem (le_of_lt hn)
  have hFsum : F_of L = ∑ j ∈ Finset.range (N + 1), T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j := by
    simpa [L] using F_of_history_seq_eq_sum_T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem N
  have hfun :
      (fun w => ∑ j ∈ Finset.range (N + 1), (T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j).eval w) =
        fun w => (∑ j ∈ Finset.range (N + 1), T_seq S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem j).eval w := by
    funext w
    simp [Polynomial.eval_finset_sum]
  rw [hfun, iteratedDeriv_eval_polynomial]
  rw [← hFsum, hks]
  simpa [L, htake] using hval

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
      · exact fun x => ( f_entire S hS r hr hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem |> AnalyticOn.differentiableOn ) |> DifferentiableOn.differentiableAt <| by simp;
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
  · apply_rules [ f_transcendental ]
  · -- Apply the lemma f_deriv_vanishes_on_Sn to conclude the proof.
    intros n z hz
    apply f_deriv_vanishes_on_Sn S hS r hr_mono hr_pos hr_gt hr_avoid c hc_norm hc_inj hc_mem n z hz

/-
If the derived set of a set S is empty, then S has no finite limit point (i.e., its intersection with any compact set is finite).
-/
lemma derivedSet_empty_imp_hasNoFiniteLimitPoint (S : Set ℂ) (h : derivedSet S = ∅) : HasNoFiniteLimitPoint S := by
  intro K hK
  by_contra hfin
  have hinf : (S ∩ K).Infinite := hfin
  obtain ⟨x, hxK, hxacc⟩ := hinf.exists_accPt_of_subset_isCompact hK inter_subset_right
  have hxS : x ∈ derivedSet S := derivedSet_mono (S ∩ K) S inter_subset_left hxacc
  rw [h] at hxS
  exact hxS

/-
If an entire function f is bounded by a polynomial in |z|, then f is a polynomial.
-/
lemma isPolynomial_of_bound (f : ℂ → ℂ) (h_diff : Differentiable ℂ f) (n : ℕ) (C : ℝ)
    (h_bound : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ n) : IsPolynomial f := by
  classical
  have h_deriv_zero : ∀ k, n < k → iteratedDeriv k f 0 = 0 := by
    intro k hk
    have hC_nonneg : 0 ≤ C := by
      have hb0 : ‖f 0‖ ≤ C := by
        simpa using h_bound 0
      exact (norm_nonneg (f 0)).trans hb0
    have hle_nat : ∀ M : ℕ,
        ‖iteratedDeriv k f (0 : ℂ)‖ ≤
          (k.factorial : ℝ) * C * (2 : ℝ) ^ n *
            (((M : ℝ) + 1) ^ n / (((M : ℝ) + 1) ^ k)) := by
      intro M
      let R : ℝ := (M : ℝ) + 1
      have hR : 0 < R := by positivity
      have hR_ge_one : (1 : ℝ) ≤ R := by
        dsimp [R]
        exact le_add_of_nonneg_left (Nat.cast_nonneg M)
      have hC_sphere : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ C * (2 * R) ^ n := by
        intro z hz
        have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        have hb := h_bound z
        have hbase : 1 + ‖z‖ ≤ 2 * R := by
          rw [hzR]
          nlinarith
        have hpow : (1 + ‖z‖) ^ n ≤ (2 * R) ^ n :=
          pow_le_pow_left₀ (by positivity) hbase n
        exact hb.trans (mul_le_mul_of_nonneg_left hpow hC_nonneg)
      have hcauchy :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          (F := ℂ) k hR h_diff.diffContOnCl hC_sphere
      have hmain :
          k.factorial * (C * (2 * R) ^ n) / R ^ k =
            (k.factorial : ℝ) * C * (2 : ℝ) ^ n * (R ^ n / R ^ k) := by
        rw [mul_pow]
        ring
      exact hcauchy.trans (le_of_eq hmain)
    have ht :
        Tendsto (fun M : ℕ => (k.factorial : ℝ) * C * (2 : ℝ) ^ n *
            (((M : ℝ) + 1) ^ n / (((M : ℝ) + 1) ^ k))) atTop (𝓝 0) := by
      have ht0 : Tendsto (fun x : ℝ => x ^ n / x ^ k) atTop (𝓝 0) :=
        tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) hk
      have hnat : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop := by
        exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
      simpa [mul_assoc] using
        (ht0.comp hnat).const_mul ((k.factorial : ℝ) * C * (2 : ℝ) ^ n)
    have hle0 : ‖iteratedDeriv k f (0 : ℂ)‖ ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds ht hle_nat
    exact norm_le_zero_iff.mp hle0
  let ps : FormalMultilinearSeries ℂ ℂ ℂ := cauchyPowerSeries f 0 (1 : NNReal)
  have hps : HasFPowerSeriesOnBall f ps 0 (⊤ : ENNReal) := by
    change HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 (1 : NNReal)) 0 (⊤ : ENNReal)
    exact h_diff.hasFPowerSeriesOnBall (0 : ℂ) (R := (1 : NNReal)) (by norm_num)
  have hps_zero : ∀ m, n + 1 ≤ m → ps m = 0 := by
    intro m hm
    have hmgt : n < m := Nat.lt_of_succ_le hm
    have hderiv := h_deriv_zero m hmgt
    have hfsmul := hps.factorial_smul (1 : ℂ) m
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul,
      hderiv] at hfsmul
    have hterm : ps m (fun _ : Fin m => (1 : ℂ)) = 0 := by
      have hfsmul0 : (m.factorial : ℂ) * ps m (fun _ : Fin m => (1 : ℂ)) = 0 := by
        simpa [nsmul_eq_mul] using hfsmul
      exact (mul_eq_zero.mp hfsmul0).resolve_left (by exact_mod_cast Nat.factorial_ne_zero m)
    rw [← FormalMultilinearSeries.coeff_eq_zero]
    exact hterm
  have hfinite : HasFiniteFPowerSeriesOnBall f ps 0 (n + 1) (⊤ : ENNReal) :=
    { hps with finite := hps_zero }
  let P : Polynomial ℂ :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (ps.coeff i) * Polynomial.X ^ i
  refine ⟨P, ?_⟩
  intro z
  have hz : z ∈ Metric.eball (0 : ℂ) (⊤ : ENNReal) := by simp
  have heq := hfinite.eq_partialSum' z hz (n + 1) le_rfl
  have hpoly_eval : P.eval z = ps.partialSum (n + 1) z := by
    rw [FormalMultilinearSeries.partialSum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp [smul_eq_mul, mul_comm]
  simpa [P, sub_zero, hpoly_eval] using heq

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
            simp_all +decide [ Finset.sum_range_succ ];
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
      exact isPolynomial_of_bound f ( show Differentiable ℂ f from fun z => ( h_entire.differentiableOn.differentiableAt <| by simp ) ) _ _ h_f_poly_bound.choose_spec.choose_spec

/-
If (z-a)*f(z) is a polynomial, then f is a polynomial (assuming f is entire).
-/
lemma isPolynomial_of_mul_sub_c (f : ℂ → ℂ) (h_entire : AnalyticOn ℂ f Set.univ) (a : ℂ)
    (h_mul : IsPolynomial (fun z => (z - a) * f z)) : IsPolynomial f := by
      obtain ⟨P, hP⟩ := h_mul;
      -- If $P(a) \neq 0$, then $f(a)$ would be undefined, contradicting the fact that $f$ is entire. Hence, $P(a) = 0$.
      have hP_a_zero : P.eval a = 0 := by
        simpa using Eq.symm ( hP a );
      obtain ⟨ Q, hQ ⟩ := Polynomial.dvd_iff_isRoot.mpr hP_a_zero;
      have h_eq : ∀ z, z ≠ a → f z = Q.eval z := by
        intro z hz; specialize hP z; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have h_eq_all : f a = Q.eval a := by
        have h_eq_all : Filter.Tendsto (fun z => f z) (nhdsWithin a {a}ᶜ) (nhds (Q.eval a)) := by
          exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_eq x hx ] ) ( Q.continuous.continuousWithinAt );
        exact tendsto_nhds_unique ( h_entire.continuousOn.continuousAt ( by simp ) |> fun h => h.mono_left nhdsWithin_le_nhds ) h_eq_all;
      exact ⟨ Q, fun z => by by_cases h : z = a <;> simp +decide [ * ] ⟩

/-
If f is an entire function and p is a non-zero polynomial such that p*f is a polynomial, then f is a polynomial.
-/
lemma isPolynomial_of_mul_poly (f : ℂ → ℂ) (h_entire : AnalyticOn ℂ f Set.univ) (p : Polynomial ℂ) (hp : p ≠ 0)
    (h_mul : IsPolynomial (fun z => p.eval z * f z)) : IsPolynomial f := by
      -- We proceed by induction on the degree of `p`.
      induction n : p.natDegree using Nat.strong_induction_on generalizing p f with
      | h n ih =>
        by_cases h_deg : p.natDegree ≤ 0;
        · simp +zetaDelta at *;
          rw [ Polynomial.eq_C_of_natDegree_eq_zero h_deg ] at hp h_mul; obtain ⟨ q, hq ⟩ := h_mul; use Polynomial.C ( ( p.coeff 0 : ℂ ) ⁻¹ ) * q; intro z; simp +decide;
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
              obtain ⟨ P, hP ⟩ := h_mul; use P; simp_all +decide [ mul_comm, mul_left_comm ] ;
            apply isPolynomial_of_mul_sub_c;
            exacts [ by exact DifferentiableOn.analyticOn ( by exact DifferentiableOn.mul ( q.differentiable.differentiableOn ) h_entire.differentiableOn ) ( by simp ), h_g_poly ];
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
        exact DifferentiableOn.analyticOn ( by exact Differentiable.differentiableOn ( by exact Polynomial.differentiable _ ) ) ( by simp );
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
    · exact DifferentiableOn.analyticOn ( hf.1.differentiableOn ) ( by simp )

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
  · exact fun z => ( f_entire S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) ) r hr₁ ( fun n => by linarith [ hr₂ n ] ) ( fun n => by linarith [ hr₂ n ] ) hr₃ c hc₁ hc₃ hc₂ |> fun h => h.differentiableOn.differentiableAt <| by simp );
  · apply_rules [ transcendental_of_transcendentalEntire ];
    apply_rules [ f_transcendental ];
  · intro k;
    refine' ⟨ _, fun { z } hz => _ ⟩;
    · induction k with
      | zero =>
        exact Nat.cast_pos.mpr ( by norm_num : 0 < 1 );
      | succ k ih =>
        exact lt_of_le_of_lt ( Nat.zero_le _ ) ( k_seq_strict_mono S ( fun n => derivedSet_empty_imp_hasNoFiniteLimitPoint _ ( h n ) ) r hr₁ ( fun n => by linarith [ hr₂ n ] ) ( fun n => by linarith [ hr₂ n ] ) hr₃ c hc₁ hc₃ hc₂ k.lt_succ_self );
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
_the derivatives of an entire function_. Proc. Amer. Math. Soc. (1972), 229--232.
-/
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

end Erdos229

#print axioms Erdos229.erdos_229
-- 'Erdos229.erdos_229' depends on axioms: [propext, Classical.choice, Quot.sound]
