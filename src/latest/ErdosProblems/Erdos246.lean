/-

This is a Lean formalization of a solution to Erdős Problem 246.
https://www.erdosproblems.com/forum/thread/246

The original proof was found by: B. J. Birch

[Bi59] Birch, B. J., Note on a problem of Erdős. Proc. Cambridge
Philos. Soc. (1959), 370-373.


A proof of ChatGPT's choice was auto-formalized by Aristotle (from
Harmonic).  The final theorem statement is from Aristotle itself.


The proof is verified by Lean.

-/


/-
We prove that for coprime a, b >= 2, the set Gamma(a,b) = {a^k b^l} is complete, meaning its set of finite subset sums has finite complement in N. We follow the provided proof outline: establishing irrationality of log a / log b, density of fractional parts, bounded gaps in the subset sums, constructing an arithmetic progression in the subset sums, and finally using the arithmetic progression to prove completeness.
-/

import Mathlib

namespace Erdos246

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped Classical

set_option maxHeartbeats 0

/-
Definitions of FS (finite subset sums), IsCompleteSeq (completeness of a set), and Gamma (the set of numbers of the form a^k * b^l).
-/
open BigOperators

def FS (A : Set ℕ) : Set ℕ :=
  {s | ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ s = ∑ x ∈ F, x}

def IsCompleteSeq (A : Set ℕ) : Prop :=
  Set.Finite {n | n ∉ FS A}

def Gamma (a b : ℕ) : Set ℕ :=
  {x | ∃ k l : ℕ, x = a^k * b^l}

/-
If p, q >= 2 are coprime, then log p / log q is irrational.
-/
theorem log_ratio_irrational {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) :
  Irrational (Real.log p / Real.log q) := by
    refine' fun ⟨ a, ha ⟩ => _;
    -- Then $p^b = q^a$.
    have h_exp : (p : ℝ) ^ (a.den) = (q : ℝ) ^ (a.num.natAbs) := by
      have h_exp : (Real.log p) * (a.den : ℝ) = (Real.log q) * (a.num.natAbs : ℝ) := by
        rw [ eq_div_iff ] at ha;
        · simp +decide [ ← ha, mul_comm, Rat.cast_def ];
          rw [ ← mul_assoc, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr a.pos.ne' ), abs_of_nonneg ( mod_cast Rat.num_nonneg.mpr ( show 0 ≤ a by exact_mod_cast ( by nlinarith [ Real.log_pos ( show ( p :ℝ ) > 1 by norm_cast ), Real.log_pos ( show ( q :ℝ ) > 1 by norm_cast ) ] : ( 0 :ℝ ) ≤ a ) ) ) ];
        · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hq;
      rw [ ← Real.exp_log ( by positivity : 0 < ( p : ℝ ) ), ← Real.exp_log ( by positivity : 0 < ( q : ℝ ) ), ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_comm, h_exp, mul_comm ];
    norm_cast at *;
    apply_fun fun x => x.gcd p at h_exp ; simp_all +decide [ Nat.Coprime, Nat.Coprime.symm ];
    simp_all +decide [ Nat.gcd_comm, Nat.Coprime, Nat.Coprime.pow_left ];
    cases a_den : a.den <;> cases a_num : a.num.natAbs <;> simp_all +decide [ Nat.Coprime, Nat.Coprime.pow_left ];
    simp_all +decide [ Nat.Coprime, Nat.Coprime.pow_right ]

theorem exists_small_fract_mul (α : ℝ) (h_irr : Irrational α) (ε : ℝ) (hε : 0 < ε) :
  ∃ m : ℕ, m > 0 ∧ Int.fract (m * α) < ε := by
    -- Let $N$ be a positive integer such that $N > 1/\epsilon$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧ 1 / (N + 1) < ε := by
      exact ⟨ ⌊ε⁻¹⌋₊ + 1, Nat.succ_pos _, by simpa using inv_lt_of_inv_lt₀ hε <| by linarith [ Nat.lt_floor_add_one <| ε⁻¹ ] ⟩;
    -- Applying Dirichlet's approximation theorem to $N$ and $\alpha$, there exist integers $j$ and $k$ such that $0 < k \leq N$ and $|k\alpha - j| < \frac{1}{N+1}$.
    obtain ⟨j, k, hk_pos, hk_le_N, h_approx⟩ : ∃ j k : ℤ, 0 < k ∧ k ≤ N ∧ |k * α - j| < 1 / (N + 1) := by
      have := Real.exists_int_int_abs_mul_sub_le ( α : ℝ ) hN.1;
      obtain ⟨ j, k, hk₁, hk₂, hk₃ ⟩ := this;
      refine' ⟨ j, k, hk₁, hk₂, lt_of_le_of_ne hk₃ _ ⟩;
      intro h;
      -- If $|k\alpha - j| = \frac{1}{N+1}$, then $k\alpha = j \pm \frac{1}{N+1}$, which implies $\alpha = \frac{j \pm \frac{1}{N+1}}{k}$.
      have h_alpha_eq : α = (j + 1 / (N + 1)) / k ∨ α = (j - 1 / (N + 1)) / k := by
        cases abs_cases ( ( k : ℝ ) * α - j ) <;> [ left; right ] <;> rw [ eq_div_iff ( by positivity ) ] <;> linarith;
      rcases h_alpha_eq with ( rfl | rfl ) <;> [ exact h_irr ⟨ ( j + ( N + 1 : ℚ ) ⁻¹ ) / k, by push_cast; ring ⟩ ; exact h_irr ⟨ ( j - ( N + 1 : ℚ ) ⁻¹ ) / k, by push_cast; ring ⟩ ];
    -- Let $\delta = k\alpha - j$. Since $\alpha$ is irrational, $\delta \ne 0$.
    set δ := k * α - j
    have hδ_ne_zero : δ ≠ 0 := by
      exact sub_ne_zero_of_ne <| mod_cast h_irr.ratCast_mul ( by aesop ) |> fun h => h.ne_int _;
    -- If $\delta > 0$, then $\{k\alpha\} = \delta < \epsilon$, so we are done with $m=k$.
    by_cases hδ_pos : 0 < δ;
    · use k.natAbs;
      norm_num +zetaDelta at *;
      exact ⟨ hk_pos.ne', by rw [ abs_of_nonneg ( by positivity ) ] ; exact lt_of_le_of_lt ( by rw [ Int.fract ] ; exact sub_le_iff_le_add'.mpr <| by linarith [ abs_lt.mp h_approx, Int.fract_add_floor ( ( k : ℝ ) * α ), show ( ⌊ ( k : ℝ ) * α⌋ : ℝ ) ≥ j by exact_mod_cast Int.le_floor.mpr hδ_pos.le ] ) hN.2 ⟩;
    · -- If $\delta < 0$, then $\{k\alpha\} = 1 + \delta$. This corresponds to a step of size $|\delta|$ to the left on the circle.
      obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 < m ∧ m * |δ| ∈ Set.Ioo (1 - ε) 1 := by
        have h_seq : ∃ m : ℕ, 0 < m ∧ m * |δ| < 1 ∧ (m + 1) * |δ| ≥ 1 := by
          have h_seq : ∃ m : ℕ, m * |δ| < 1 ∧ (m + 1) * |δ| ≥ 1 := by
            have h_seq : ∃ m : ℕ, m * |δ| ≥ 1 := by
              exact ⟨ ⌊1 / |δ|⌋₊ + 1, by push_cast; nlinarith [ Nat.lt_floor_add_one ( 1 / |δ| ), abs_pos.mpr hδ_ne_zero, mul_div_cancel₀ 1 ( ne_of_gt ( abs_pos.mpr hδ_ne_zero ) ) ] ⟩;
            contrapose! h_seq;
            exact fun x => Nat.recOn x ( by norm_num ) fun n ihn => mod_cast h_seq n ihn;
          obtain ⟨ m, hm₁, hm₂ ⟩ := h_seq;
          by_cases hm_zero : m = 0;
          · norm_num [ hm_zero ] at *;
            linarith [ inv_lt_one_of_one_lt₀ ( by norm_cast; linarith : ( N : ℝ ) + 1 > 1 ) ];
          · exact ⟨ m, Nat.pos_of_ne_zero hm_zero, hm₁, hm₂ ⟩;
        grind;
      -- Let $m' = m * k$. Then $\{m' \alpha\} = \{m * (k \alpha)\} = \{m * (j + \delta)\} = \{m * j + m * \delta\} = \{m * \delta\}$.
      use m * k.natAbs;
      cases abs_cases ( k * α - j ) <;> simp_all +decide [ abs_of_pos ];
      · cases lt_or_eq_of_le ‹_› <;> first | linarith | aesop;
      · exact ⟨ hk_pos.ne', by rw [ Int.fract ] ; exact sub_lt_iff_lt_add'.mpr <| by nlinarith [ show ( m : ℝ ) * k > 0 by exact mul_pos ( Nat.cast_pos.mpr hm.1 ) ( Int.cast_pos.mpr hk_pos ), Int.fract_add_floor ( ( m : ℝ ) * k * α ), show ( Int.floor ( ( m : ℝ ) * k * α ) : ℝ ) ≥ m * j - 1 by exact mod_cast Int.le_floor.mpr <| by push_cast; nlinarith [ show ( m : ℝ ) * k > 0 by exact mul_pos ( Nat.cast_pos.mpr hm.1 ) ( Int.cast_pos.mpr hk_pos ) ] ] ⟩

/-
If alpha is irrational, then the set of fractional parts {n * alpha} is dense in [0, 1].
-/
theorem lem_dense (α : ℝ) (h_irr : Irrational α) :
  closure (Set.range (fun n : ℕ => Int.fract (n * α))) = Set.Icc 0 1 := by
    -- By definition of irrationality, the sequence $\{n \alpha\}$ is dense in $[0, 1]$.
    have h_dense : ∀ ε > 0, ∀ y : ℝ, 0 ≤ y ∧ y < 1 → ∃ n : ℕ, |Int.fract (n * α) - y| < ε := by
      -- Fix $\varepsilon \in (0,1)$. By `exists_small_fract_mul`, there exists $m > 0$ such that $\delta := \{m\alpha\} < \varepsilon$.
      intro ε hε y hy
      obtain ⟨m, hm_pos, hmδ⟩ : ∃ m : ℕ, m > 0 ∧ Int.fract (m * α) < ε ∧ Int.fract (m * α) > 0 := by
        obtain ⟨ m, hm₁, hm₂ ⟩ := exists_small_fract_mul α h_irr ε hε;
        exact ⟨ m, hm₁, hm₂, Int.fract_pos.mpr <| mod_cast h_irr.ratCast_mul ( Nat.cast_ne_zero.mpr hm₁.ne' ) |> fun h => h.ne_int _ ⟩;
      -- Since $\delta \in (0, \varepsilon)$, the sequence $0, \delta, 2\delta, \dots$ (modulo 1) forms a $\delta$-net of $[0,1]$.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, k * Int.fract (m * α) ≤ y ∧ y < (k + 1) * Int.fract (m * α) := by
        exact ⟨ ⌊y / Int.fract ( m * α ) ⌋₊, by nlinarith [ Nat.floor_le ( show 0 ≤ y / Int.fract ( m * α ) by exact div_nonneg hy.1 hmδ.2.le ), mul_div_cancel₀ y hmδ.2.ne' ], by nlinarith [ Nat.lt_floor_add_one ( y / Int.fract ( m * α ) ), mul_div_cancel₀ y hmδ.2.ne' ] ⟩;
      -- Therefore, $|y - \{k m \alpha\}| < \delta < \varepsilon$.
      use k * m;
      -- Since $\{k m \alpha\} = \{k \{m \alpha\}\}$, we have $\{k m \alpha\} = k \{m \alpha\}$.
      have h_fract : Int.fract ((k * m : ℝ) * α) = k * Int.fract (m * α) := by
        rw [ mul_assoc, Int.fract_eq_iff ];
        exact ⟨ by nlinarith, by nlinarith, ⟨ k * ⌊ ( m : ℝ ) * α⌋, by push_cast; rw [ Int.fract ] ; ring ⟩ ⟩;
      exact abs_sub_lt_iff.mpr ⟨ by push_cast; linarith, by push_cast; linarith ⟩;
    refine' Set.Subset.antisymm _ _;
    · exact closure_minimal ( Set.range_subset_iff.mpr fun n => ⟨ Int.fract_nonneg _, Int.fract_lt_one _ |> le_of_lt ⟩ ) isClosed_Icc;
    · intro x hx; rcases eq_or_lt_of_le hx.2 <;> simp_all +decide [ Metric.mem_closure_iff ] ;
      · intro ε hε; obtain ⟨ n, hn ⟩ := h_dense ( Min.min ε 1 / 2 ) ( by positivity ) ( 1 - Min.min ε 1 / 2 ) ( by linarith [ show 0 < Min.min ε 1 / 2 by positivity, min_le_left ε 1, min_le_right ε 1 ] ) ( by linarith [ show 0 < Min.min ε 1 / 2 by positivity, min_le_left ε 1, min_le_right ε 1 ] ) ; use n; rw [ dist_comm ] ; exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp hn, min_le_left ε 1, min_le_right ε 1 ], by linarith [ abs_lt.mp hn, min_le_left ε 1, min_le_right ε 1 ] ⟩ ;
      · exact fun ε hε => by obtain ⟨ n, hn ⟩ := h_dense ε hε x hx.1 ( by linarith ) ; exact ⟨ n, by rw [ dist_comm ] ; exact hn ⟩ ;

/-
For any irrational beta and delta > 0, there exists a bound B such that for any real T, there is an n <= B with fractional part of (T - n * beta) less than delta.
-/
theorem exists_bounded_n_fract_lt (β : ℝ) (h_irr : Irrational β) (δ : ℝ) (hδ : 0 < δ) :
  ∃ B : ℕ, ∀ T : ℝ, ∃ n ≤ B, Int.fract (T - n * β) < δ := by
    -- Let's choose any $\delta > 0$.
    set δ' := min δ (1 / 2)
    have hδ'_pos : 0 < δ' := by
      positivity;
    -- By the density of $\{n\beta\}$ in $[0, 1]$, for any $\delta > 0$, there exists $m > 0$ such that $\{m\beta\} < \delta'$.
    have h_dense : ∀ δ' > 0, ∃ m : ℕ, m > 0 ∧ Int.fract (m * β) < δ' := by
      exact fun δ' a => exists_small_fract_mul β h_irr δ' a;
    -- Let $m$ be such that $\{m\beta\} < \delta'$.
    obtain ⟨m, hm_pos, hm⟩ : ∃ m : ℕ, m > 0 ∧ Int.fract (m * β) < δ' := h_dense δ' hδ'_pos;
    -- Let $B = \lceil 1 / \{m\beta\} \rceil$.
    use Nat.ceil (1 / Int.fract (m * β)) * m;
    intro T
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k ≤ Nat.ceil (1 / Int.fract (m * β)) ∧ Int.fract (T - k * m * β) < δ' := by
      -- Let $y = \{T\}$.
      set y := Int.fract T;
      -- Since $\{m\beta\} < \delta'$, we have $\{T - k m \beta\} = \{y - k \{m\beta\}\}$.
      have h_fract : ∀ k : ℕ, Int.fract (T - k * m * β) = Int.fract (y - k * Int.fract (m * β)) := by
        norm_num [ Int.fract_eq_fract ];
        exact fun k => ⟨ ⌊T⌋ - k * ⌊ ( m : ℝ ) * β⌋, by push_cast; nlinarith [ Int.fract_add_floor T, Int.fract_add_floor ( ( m : ℝ ) * β ) ] ⟩;
      -- Since $\{m\beta\} < \delta'$, we have $\{y - k \{m\beta\}\} < \delta'$ for some $k \leq \lceil 1 / \{m\beta\} \rceil$.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, k ≤ Nat.ceil (1 / Int.fract (m * β)) ∧ y - k * Int.fract (m * β) < δ' ∧ y - k * Int.fract (m * β) ≥ 0 := by
        refine' ⟨ ⌊y / Int.fract ( m * β ) ⌋₊, _, _, _ ⟩;
        · exact Nat.floor_le_of_le ( by rw [ div_le_iff₀ ( Int.fract_pos.mpr <| by exact mod_cast h_irr.ratCast_mul ( Nat.cast_ne_zero.mpr hm_pos.ne' ) |> fun h => h.ne_rat _ ) ] ; nlinarith [ Nat.le_ceil ( 1 / Int.fract ( m * β ) ), Int.fract_nonneg T, Int.fract_lt_one T, Int.fract_nonneg ( m * β ), Int.fract_lt_one ( m * β ), mul_div_cancel₀ 1 ( show ( Int.fract ( m * β ) ) ≠ 0 from ne_of_gt <| Int.fract_pos.mpr <| by exact mod_cast h_irr.ratCast_mul ( Nat.cast_ne_zero.mpr hm_pos.ne' ) |> fun h => h.ne_rat _ ) ] );
        · nlinarith [ Nat.lt_floor_add_one ( y / Int.fract ( m * β ) ), Int.fract_nonneg ( m * β ), Int.fract_lt_one ( m * β ), mul_div_cancel₀ y ( show Int.fract ( m * β ) ≠ 0 from ne_of_gt <| Int.fract_pos.mpr <| mod_cast h_irr.ratCast_mul ( Nat.cast_ne_zero.mpr hm_pos.ne' ) |> fun h => h.ne_int _ ) ];
        · nlinarith [ Nat.floor_le ( show 0 ≤ y / Int.fract ( m * β ) by exact div_nonneg ( Int.fract_nonneg _ ) ( Int.fract_nonneg _ ) ), Int.fract_nonneg ( m * β ), Int.fract_lt_one ( m * β ), mul_div_cancel₀ y ( show Int.fract ( m * β ) ≠ 0 from ne_of_gt ( Int.fract_pos.mpr ( mod_cast h_irr.ratCast_mul ( Nat.cast_ne_zero.mpr hm_pos.ne' ) |> fun h => h.ne_rat _ ) ) ) ];
      use k;
      field_simp;
      exact ⟨ hk.1, by rw [ show ( T - m * β * k : ℝ ) = T - k * m * β by ring ] ; rw [ h_fract ] ; rw [ Int.fract ] ; exact by rw [ show ⌊y - k * Int.fract ( m * β ) ⌋ = 0 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith [ min_le_left δ ( 1 / 2 ), min_le_right δ ( 1 / 2 ) ] ⟩ ] ; norm_num; linarith ⟩;
    exact ⟨ k * m, by nlinarith, by simpa [ mul_assoc ] using hk.2.trans_le ( min_le_left _ _ ) ⟩

/-
There exists X0 >= 1 such that for every X >= X0 there exist u, v in N with X/2 < p^u q^v <= X.
-/
theorem lem_halfinterval {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) :
  ∃ X₀ : ℝ, X₀ ≥ 1 ∧ ∀ X : ℝ, X ≥ X₀ → ∃ u v : ℕ, X / 2 < (p : ℝ)^u * (q : ℝ)^v ∧ (p : ℝ)^u * (q : ℝ)^v ≤ X := by
    -- By Lemma 25, there exists a bound B such that for any T, there is an n ≤ B with fractional part of (T - n * β) less than δ.
    obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ T : ℝ, ∃ n ≤ B, Int.fract (T - n * (Real.log q / Real.log p)) < Real.log 2 / Real.log p := by
      have h_irr : Irrational (Real.log q / Real.log p) := by
        apply_mod_cast log_ratio_irrational hq hp h_coprime.symm;
      convert exists_bounded_n_fract_lt _ h_irr _ _;
      exact div_pos ( Real.log_pos ( by norm_num ) ) ( Real.log_pos ( by norm_cast ) );
    refine' ⟨ Real.rpow p ( B * ( Real.log q / Real.log p ) + 1 ), Real.one_le_rpow ( by norm_cast; linarith ) ( by positivity ), fun X hX => _ ⟩;
    obtain ⟨ n, hn₁, hn₂ ⟩ := hB ( Real.log X / Real.log p );
    -- Let $u = \lfloor T - n\beta \rfloor$.
    obtain ⟨ u, hu ⟩ : ∃ u : ℕ, u = ⌊Real.log X / Real.log p - n * (Real.log q / Real.log p)⌋ := by
      refine' ⟨ Int.toNat <| ⌊Real.log X / Real.log p - n * ( Real.log q / Real.log p ) ⌋, _ ⟩;
      rw [ Int.toNat_of_nonneg ( Int.floor_nonneg.mpr <| sub_nonneg.mpr <| ?_ ) ];
      refine' le_trans _ ( div_le_div_of_nonneg_right ( Real.log_le_log ( _ ) hX ) ( Real.log_nonneg ( by norm_cast; linarith ) ) );
      · norm_num [ Real.log_rpow ( by positivity : 0 < ( p : ℝ ) ) ];
        rw [ mul_div_cancel_right₀ _ ( ne_of_gt ( Real.log_pos ( by norm_cast ) ) ) ] ; nlinarith [ show ( n : ℝ ) ≤ B by norm_cast, show 0 ≤ Real.log q / Real.log p by positivity ];
      · exact Real.rpow_pos_of_pos ( by positivity ) _;
    refine' ⟨ u, n, _, _ ⟩;
    · -- Using the properties of exponents, we can rewrite the inequality as $X < 2 \cdot p^u \cdot q^n$.
      have h_exp : Real.log X < Real.log 2 + u * Real.log p + n * Real.log q := by
        rw [ eq_comm, Int.floor_eq_iff ] at hu;
        rw [ lt_div_iff₀ ( Real.log_pos ( by norm_cast ) ) ] at *;
        nlinarith [ Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ), Real.log_pos ( show ( q : ℝ ) > 1 by norm_cast ), mul_div_cancel₀ ( Real.log X ) ( ne_of_gt ( Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ) ) ), mul_div_cancel₀ ( Real.log q ) ( ne_of_gt ( Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ) ) ), Int.fract_add_floor ( Real.log X / Real.log p - n * ( Real.log q / Real.log p ) ), show ( ⌊Real.log X / Real.log p - n * ( Real.log q / Real.log p ) ⌋ : ℝ ) = u by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by norm_num at *; linarith, by norm_num at *; linarith ⟩ ];
      rw [ div_lt_iff₀ ( by positivity ) ];
      contrapose! h_exp;
      convert Real.log_le_log ( by positivity ) h_exp using 1 ; rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] ; ring;
    · -- Exponentiating both sides of the inequality $u + n\beta \leq T$, we get $p^{u + n\beta} \leq p^T$.
      have h_exp : (p : ℝ) ^ (u + n * (Real.log q / Real.log p)) ≤ X := by
        have h_exp : (p : ℝ) ^ (u + n * (Real.log q / Real.log p)) ≤ (p : ℝ) ^ (Real.log X / Real.log p) := by
          exact_mod_cast Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show ( u : ℝ ) + n * ( Real.log q / Real.log p ) ≤ Real.log X / Real.log p from by rw [ eq_comm, Int.floor_eq_iff ] at hu; norm_num at *; linarith );
        convert h_exp using 1;
        erw [ Real.rpow_logb ] <;> norm_cast ; linarith;
        · linarith;
        · exact lt_of_lt_of_le ( by exact Real.rpow_pos_of_pos ( by positivity ) _ ) hX;
      convert h_exp using 1 ; norm_num [ Real.rpow_add ( by positivity : 0 < ( p : ℝ ) ), Real.rpow_mul ( by positivity : 0 ≤ ( p : ℝ ) ), mul_div_cancel₀, ne_of_gt ( Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ) ) ];
      rw [ ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_comm ];
      rw [ Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf ; norm_num [ Real.exp_log, show p ≠ 0 by positivity, show q ≠ 0 by positivity ];
      rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast ) ) ), mul_one ]

/-
There exists a constant L > 0 such that for every M, there is an element s of FS(Gamma(p,q)) with s <= M < s + L.
-/
theorem prop_boundedgaps {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) :
  ∃ L : ℕ, L > 0 ∧ ∀ M : ℕ, ∃ s ∈ FS (Gamma p q), s ≤ M ∧ M < s + L := by
    -- Let $X₀$ be as given in Lemma lem_halfinterval.
    obtain ⟨X₀, hX₀⟩ := lem_halfinterval hp hq h_coprime;
    -- Let $G$ be the maximum gap size between consecutive elements of $S \cap [0, \lfloor X_0 \rfloor + 1]$.
    obtain ⟨G, hG⟩ : ∃ G : ℕ, ∀ M ∈ Finset.range (Nat.floor X₀ + 2), ∃ s ∈ FS (Gamma p q), s ≤ M ∧ M < s + G := by
      use Nat.succ (Nat.floor X₀ + 2);
      exact fun M hM => ⟨ 0, ⟨ ∅, by norm_num, by norm_num ⟩, by norm_num, by linarith [ Finset.mem_range.mp hM ] ⟩;
    refine ⟨ G + 2, Nat.succ_pos _, fun M => ?_ ⟩ ; induction' M using Nat.strong_induction_on with M ih ; rcases le_or_gt M ( Nat.floor X₀ + 1 ) with h | h;
    · exact Exists.elim ( hG M ( Finset.mem_range.mpr ( by linarith ) ) ) fun s hs => ⟨ s, hs.1, hs.2.1, by linarith ⟩;
    · -- By `lem_halfinterval`, there exists $t \in \Gamma(p,q)$ such that $M/2 < t \le M$.
      obtain ⟨t, ht⟩ : ∃ t ∈ Gamma p q, M / 2 < t ∧ t ≤ M := by
        obtain ⟨ u, v, hu, hv ⟩ := hX₀.2 M ( Nat.lt_of_floor_lt ( by linarith ) |> le_of_lt );
        exact ⟨ p ^ u * q ^ v, ⟨ u, v, rfl ⟩, Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith, by exact_mod_cast hv ⟩;
      -- Consider the interval $(M-t-L, M-t]$.
      obtain ⟨s', hs'⟩ : ∃ s' ∈ FS (Gamma p q), s' ≤ M - t ∧ M - t < s' + (G + 2) := by
        exact ih _ ( Nat.sub_lt ( by linarith ) ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ht.2.1 ( by norm_num ) ) ) );
      -- Since $s' < t$, we have $s' + t \in FS (Gamma p q)$.
      have hs'_t_in_FS : s' + t ∈ FS (Gamma p q) := by
        obtain ⟨ F, hF₁, rfl ⟩ := hs'.1;
        -- Since $t \in \Gamma(p,q)$ and $F \subseteq \Gamma(p,q)$, we have $t \notin F$.
        have ht_not_in_F : t ∉ F := by
          intro H; have := Finset.single_le_sum ( fun x _ => Nat.zero_le x ) H; omega;
        exact ⟨ F ∪ { t }, by aesop_cat, by rw [ Finset.sum_union ] <;> aesop_cat ⟩;
      exact ⟨ s' + t, hs'_t_in_FS, by omega, by omega ⟩

/-
For any M > 1, there exists N such that 2^((N+1)(N+2)/2) > ((N+1)(N+2)/2) * M^N + 1.
-/
theorem exists_large_N_inequality (M : ℝ) (hM : M > 1) :
  ∃ N : ℕ, (2 : ℝ) ^ ((N + 1) * (N + 2) / 2) > ((N + 1) * (N + 2) / 2) * M ^ N + 1 := by
    by_contra h_contra;
    -- Taking logarithms base 2:
    have h_log : Filter.Tendsto (fun N : ℕ => (Real.log ((N + 1) * (N + 2) / 2) + N * Real.log M + Real.log 2) / ((N + 1) * (N + 2) / 2)) Filter.atTop (nhds 0) := by
      -- We can divide the numerator and the denominator by $N^2$ and then take the limit as $N$ approaches infinity.
      have h_div : Filter.Tendsto (fun N : ℕ => (Real.log ((N + 1) * (N + 2) / 2) / N^2 + Real.log M / N + Real.log 2 / N^2) / ((1 + 1/N) * (1 + 2/N) / 2)) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $\frac{\log((N+1)(N+2)/2)}{N^2}$ tends to $0$ as $N$ tends to infinity.
        have h_log : Filter.Tendsto (fun N : ℕ => Real.log ((N + 1) * (N + 2) / 2) / (N^2 : ℝ)) Filter.atTop (nhds 0) := by
          -- We can use the fact that $\log((N+1)(N+2)/2) \leq \log(N^2) = 2\log(N)$ for all $N \geq 2$.
          have h_log_bound : ∀ N : ℕ, 2 ≤ N → Real.log ((N + 1) * (N + 2) / 2) ≤ 2 * Real.log N + Real.log 2 := by
            intro N hN; rw [ ← Real.log_rpow, ← Real.log_mul, Real.log_le_log_iff ] <;> norm_num <;> nlinarith [ ( by norm_cast : ( 2 :ℝ ) ≤ N ) ] ;
          -- We can use the fact that $\frac{\log(N)}{N^2}$ tends to $0$ as $N$ tends to infinity.
          have h_log_div_N2 : Filter.Tendsto (fun N : ℕ => Real.log N / (N^2 : ℝ)) Filter.atTop (nhds 0) := by
            refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ) ] ;
          refine' squeeze_zero_norm' _ _;
          exacts [ fun N => ( 2 * Real.log N + Real.log 2 ) / N ^ 2, Filter.eventually_atTop.mpr ⟨ 2, fun N hN => by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| by rw [ le_div_iff₀ <| by positivity ] ; nlinarith ) <| sq_nonneg _ ) ] ; exact div_le_div_of_nonneg_right ( h_log_bound N hN ) <| sq_nonneg _ ⟩, by simpa [ add_div, mul_div_assoc ] using Filter.Tendsto.add ( h_log_div_N2.const_mul 2 ) <| tendsto_const_nhds.mul <| tendsto_inv_atTop_nhds_zero_nat.pow 2 ];
        simpa using Filter.Tendsto.div ( Filter.Tendsto.add ( Filter.Tendsto.add h_log ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_nhds_zero_nat.pow 2 ) ) ) ( Filter.Tendsto.div_const ( Filter.Tendsto.mul ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) ) ) _ ) ( by norm_num );
      refine h_div.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN;
      field_simp;
    -- Exponentiating both sides gives us:
    have h_exp : Filter.Tendsto (fun N : ℕ => (((N + 1) * (N + 2) / 2) * M ^ N * 2) ^ (1 / ((N + 1) * (N + 2) / 2 : ℝ))) Filter.atTop (nhds 1) := by
      have h_exp : Filter.Tendsto (fun N : ℕ => Real.exp ((Real.log ((N + 1) * (N + 2) / 2) + N * Real.log M + Real.log 2) / ((N + 1) * (N + 2) / 2 : ℝ))) Filter.atTop (nhds 1) := by
        simpa only [ Real.exp_zero ] using Filter.Tendsto.comp ( Real.continuous_exp.tendsto _ ) h_log;
      convert h_exp using 2 ; rw [ Real.rpow_def_of_pos ( by positivity ) ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ) ] ; rw [ Real.log_pow ] ; ring_nf;
    -- This contradicts `h_contra`, so our assumption must be false.
    have h_contradiction : ∃ N : ℕ, (((N + 1) * (N + 2) / 2) * M ^ N * 2) ^ (1 / ((N + 1) * (N + 2) / 2 : ℝ)) < 2 := by
      exact ( h_exp.eventually ( gt_mem_nhds <| by norm_num ) ) |> fun h => h.exists;
    obtain ⟨ N, hN ⟩ := h_contradiction;
    -- Raising both sides to the power of $((N + 1) * (N + 2) / 2)$ gives us:
    have h_exp : (((N + 1) * (N + 2) / 2) * M ^ N * 2) < 2 ^ ((N + 1) * (N + 2) / 2) := by
      convert pow_lt_pow_left₀ hN ( by positivity ) ( show ( ( N + 1 ) * ( N + 2 ) / 2 : ℕ ) ≠ 0 from Nat.ne_of_gt <| Nat.div_pos ( by nlinarith ) zero_lt_two ) using 1;
      rw [ ← Real.rpow_natCast _ ( ( N + 1 ) * ( N + 2 ) / 2 ), ← Real.rpow_mul ( by positivity ) ] ; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ];
      rw [ div_self <| by positivity, Real.rpow_one ];
    refine h_contra ⟨ N, ?_ ⟩;
    nlinarith [ show ( ( N + 1 ) * ( N + 2 ) / 2 : ℝ ) * M ^ N ≥ 1 by exact one_le_mul_of_one_le_of_one_le ( by rw [ le_div_iff₀ ] <;> norm_cast ; nlinarith ) ( one_le_pow₀ hM.le ) ]

/-
Definitions of Phi, Q_set, and translate_set.
-/
def Phi (p q : ℕ) (S : Finset (ℤ × ℤ)) : ℚ :=
  S.sum (fun x => (p : ℚ) ^ x.1 * (q : ℚ) ^ x.2)

def Q_set : Set (ℤ × ℤ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

def translate_set (S : Finset (ℤ × ℤ)) (t : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  S.map ⟨fun x => (x.1 - t.1, x.2 - t.2), fun x y h => by
    grind⟩

/-
If the number of subsets of S is greater than the sum of elements of S plus 1, then there exist two distinct subsets with the same sum.
-/
lemma pigeonhole_subset_sums (S : Finset ℕ) (h : ∑ x ∈ S, x + 1 < 2 ^ S.card) :
  ∃ U V : Finset ℕ, U ⊆ S ∧ V ⊆ S ∧ U ≠ V ∧ ∑ x ∈ U, x = ∑ x ∈ V, x := by
    by_contra h_contra;
    have h_pigeonhole : Finset.card (Finset.image (fun U => ∑ x ∈ U, x) (Finset.powerset S)) ≤ (∑ x ∈ S, x) + 1 := by
      exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun U hU => Finset.mem_Icc.mpr ⟨ Nat.zero_le _, Finset.sum_le_sum_of_subset <| Finset.mem_powerset.mp hU ⟩ ) ( by simp +arith +decide );
    exact not_lt_of_ge h_pigeonhole <| by rw [ Finset.card_image_of_injOn fun U hU V hV hUV ↦ Classical.not_not.1 fun hUV' ↦ h_contra ⟨ U, V, Finset.mem_powerset.1 hU, Finset.mem_powerset.1 hV, hUV', hUV ⟩ ] ; simpa;

/-
If S is a subset of Q_set, then Phi(S) is a natural number.
-/
lemma Phi_is_nat (p q : ℕ) (S : Finset (ℤ × ℤ)) (hS : (S : Set (ℤ × ℤ)) ⊆ Q_set) :
  ∃ n : ℕ, Phi p q S = n := by
    use S.sum (fun x => p ^ x.1.toNat * q ^ x.2.toNat);
    norm_num +zetaDelta at *;
    exact Finset.sum_congr rfl fun x hx => by cases' hS hx with hx₁ hx₂; erw [ ← Int.toNat_of_nonneg hx₁, ← Int.toNat_of_nonneg hx₂ ] ; norm_cast;

/-
There exists a finite subset S of Q_set such that the sum of p^u q^v for (u,v) in S is strictly less than 2^|S| - 1.
-/
lemma exists_subset_sum_lt_pow_card (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
  ∃ S : Finset (ℤ × ℤ), (S : Set (ℤ × ℤ)) ⊆ Q_set ∧ (∑ x ∈ S, p ^ x.1.toNat * q ^ x.2.toNat) + 1 < 2 ^ S.card := by
    -- Choose k large enough such that k^2 * p^k * q^k + 1 < 2^(k^2).
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k ≥ 2 ∧ k^2 * p^k * q^k + 1 < 2^(k^2) := by
      -- We'll use that exponential functions grow faster than polynomial functions.
      have h_exp_growth : Filter.Tendsto (fun k : ℕ => (k^2 * p^k * q^k + 1 : ℝ) / 2^(k^2)) Filter.atTop (nhds 0) := by
        -- We can factor out $2^{k^2}$ from the denominator and use the fact that $p^k q^k$ grows much slower than $2^{k^2}$.
        have h_factor : Filter.Tendsto (fun k : ℕ => (k^2 * (p * q : ℝ)^k + 1) / (2^(k^2))) Filter.atTop (nhds 0) := by
          -- We can divide the numerator and the denominator by $2^{k^2}$ and use the fact that $p^k q^k$ grows much slower than $2^{k^2}$.
          have h_div : Filter.Tendsto (fun k : ℕ => (k^2 * (p * q : ℝ)^k) / (2^(k^2))) Filter.atTop (nhds 0) := by
            -- We can rewrite the expression as $k^2 \cdot \left(\frac{pq}{2^k}\right)^k$.
            suffices h_rewrite : Filter.Tendsto (fun k : ℕ => (k^2 : ℝ) * ((p * q : ℝ) / 2^k)^k) Filter.atTop (nhds 0) by
              convert h_rewrite using 2 ; ring;
            -- Since $p$ and $q$ are fixed, there exists some $N$ such that for all $k \geq N$, $\frac{pq}{2^k} < \frac{1}{2}$.
            obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ≥ N, (p * q : ℝ) / 2^k < 1 / 2 := by
              have h_lim : Filter.Tendsto (fun k : ℕ => (p * q : ℝ) / 2^k) Filter.atTop (nhds 0) := by
                exact tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two );
              simpa using h_lim.eventually ( gt_mem_nhds <| by norm_num );
            -- For $k \geq N$, we have $(k^2 : ℝ) * ((p * q : ℝ) / 2^k)^k \leq (k^2 : ℝ) * (1 / 2)^k$.
            have h_bound : ∀ k ≥ N, (k^2 : ℝ) * ((p * q : ℝ) / 2^k)^k ≤ (k^2 : ℝ) * (1 / 2)^k := by
              exact fun k hk => mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( le_of_lt ( hN k hk ) ) _ ) ( sq_nonneg _ );
            -- We'll use the fact that $k^2 * (1 / 2)^k$ tends to $0$ as $k$ tends to infinity.
            have h_lim : Filter.Tendsto (fun k : ℕ => (k^2 : ℝ) * (1 / 2)^k) Filter.atTop (nhds 0) := by
              refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat ; norm_num;
              refine' ⟨ 20, fun n hn => _ ⟩ ; rw [ inv_eq_one_div, div_eq_mul_inv ] ; induction hn <;> norm_num [ pow_succ' ] at *;
              rw [ inv_eq_one_div, le_div_iff₀ ] at * <;> nlinarith [ ( by norm_cast : ( 20 : ℝ ) ≤ ↑‹ℕ› ), pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) ‹ℕ› ];
            exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ N, fun k hk => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_bound k hk ⟩ ) h_lim;
          simpa [ add_div ] using h_div.add ( tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| by norm_num ) );
        simpa only [ mul_pow, mul_assoc ] using h_factor;
      have := h_exp_growth.eventually ( gt_mem_nhds zero_lt_one );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ k, hk ⟩ ; exact ⟨ k + 2, by linarith, by have := hk ( k + 2 ) ( by linarith ) ; rw [ div_lt_one ( by positivity ) ] at this; exact_mod_cast this ⟩ ;
    refine' ⟨ Finset.image ( fun x : ℕ × ℕ => ( x.1, x.2 ) ) ( Finset.product ( Finset.range k ) ( Finset.range k ) ), _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
    · exact fun x hx => ⟨ Nat.cast_nonneg _, Nat.cast_nonneg _ ⟩;
    · -- The sum of elements in $S_k$ is bounded by $k^2 \cdot p^k \cdot q^k$.
      have h_sum_bound : ∑ x ∈ Finset.range k ×ˢ Finset.range k, p ^ x.1 * q ^ x.2 ≤ k^2 * p^k * q^k := by
        refine' le_trans ( Finset.sum_le_sum fun x hx => Nat.mul_le_mul ( pow_le_pow_right₀ ( by linarith ) ( show x.1 ≤ k from by linarith [ Finset.mem_range.mp ( Finset.mem_product.mp hx |>.1 ) ] ) ) ( pow_le_pow_right₀ ( by linarith ) ( show x.2 ≤ k from by linarith [ Finset.mem_range.mp ( Finset.mem_product.mp hx |>.2 ) ] ) ) ) _ ; norm_num ; ring_nf ; norm_num;
      simpa only [ sq ] using lt_of_le_of_lt ( Nat.succ_le_succ h_sum_bound ) hk.2

/-
Generalized pigeonhole principle for subset sums.
-/
lemma pigeonhole_subset_sums_general {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) (h : ∑ x ∈ S, f x + 1 < 2 ^ S.card) :
  ∃ U V : Finset α, U ⊆ S ∧ V ⊆ S ∧ U ≠ V ∧ ∑ x ∈ U, f x = ∑ x ∈ V, f x := by
    by_contra! h';
    exact absurd ( Finset.card_le_card ( show Finset.image ( fun s => ∑ x ∈ s, f x ) ( Finset.powerset S ) ⊆ Finset.Icc ( 0 : ℕ ) ( ∑ x ∈ S, f x ) from Finset.image_subset_iff.2 fun s hs => Finset.mem_Icc.2 ⟨ Nat.zero_le _, Finset.sum_le_sum_of_subset ( Finset.mem_powerset.1 hs ) ⟩ ) ) ( by simp +decide [ Finset.card_image_of_injOn ( fun s hs t ht hst => not_imp_not.1 ( h' s t ( Finset.mem_powerset.1 hs ) ( Finset.mem_powerset.1 ht ) ) hst ) ] ; linarith )

/-
There exist disjoint nonempty finite sets U, V subset Q such that Phi(U) = Phi(V).
-/
lemma lem_equal (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
  ∃ U V : Finset (ℤ × ℤ),
    (U : Set (ℤ × ℤ)) ⊆ Q_set ∧
    (V : Set (ℤ × ℤ)) ⊆ Q_set ∧
    Disjoint U V ∧
    U.Nonempty ∧
    V.Nonempty ∧
    Phi p q U = Phi p q V := by
      -- By Lemma~\ref{lem:exists_subset_sum_lt_pow_card}, there exists a finite subset $S \subset Q$ such that $(\sum_{x \in S} p^{x_1} q^{x_2}) + 1 < 2^{|S|}$.
      obtain ⟨S, hS⟩ : ∃ S : Finset (ℤ × ℤ), (S : Set (ℤ × ℤ)) ⊆ Q_set ∧ (∑ x ∈ S, p ^ x.1.toNat * q ^ x.2.toNat) + 1 < 2 ^ S.card := by
        exact exists_subset_sum_lt_pow_card p q hp hq;
      -- Let $f(x) = p^{x_1} q^{x_2}$ (as natural numbers).
      set f : ℤ × ℤ → ℕ := fun x => p ^ x.1.toNat * q ^ x.2.toNat;
      -- By `pigeonhole_subset_sums_general`, there exist distinct subsets $U', V' \subseteq S$ such that $\sum_{x \in U'} f(x) = \sum_{x \in V'} f(x)$.
      obtain ⟨U', V', hU'V'⟩ : ∃ U' V' : Finset (ℤ × ℤ), U' ⊆ S ∧ V' ⊆ S ∧ U' ≠ V' ∧ ∑ x ∈ U', f x = ∑ x ∈ V', f x := by
        apply pigeonhole_subset_sums_general S f hS.right;
      -- Let $U = U' \setminus V'$ and $V = V' \setminus U'$.
      set U := U' \ V'
      set V := V' \ U';
      -- Then $U, V$ are disjoint, subsets of $S$ (hence of $Q$), and have the same sum.
      have h_disjoint : Disjoint U V := by
        exact Finset.disjoint_left.mpr fun x hxU hxV => by aesop;
      have h_nonempty_U : U.Nonempty := by
        by_contra h_empty_U;
        simp_all +decide [ Finset.subset_iff ];
        rw [ Finset.sdiff_eq_empty_iff_subset ] at h_empty_U;
        have h_eq : ∑ x ∈ V' \ U', f x = 0 := by
          simp_all +decide [ ← Finset.sum_sdiff h_empty_U ];
        simp +zetaDelta at *;
        grind
      have h_nonempty_V : V.Nonempty := by
        by_contra h_empty_V;
        simp_all +decide [ Finset.sdiff_eq_empty_iff_subset ];
        rw [ Finset.sdiff_eq_empty_iff_subset ] at h_empty_V;
        have h_sum_lt : ∑ x ∈ U', f x > ∑ x ∈ V', f x := by
          rw [ ← Finset.sum_sdiff h_empty_V ];
          exact lt_add_of_pos_left _ ( Finset.sum_pos ( fun x hx => mul_pos ( pow_pos ( by linarith ) _ ) ( pow_pos ( by linarith ) _ ) ) h_nonempty_U );
        linarith
      have h_sum_eq : ∑ x ∈ U, f x = ∑ x ∈ V, f x := by
        have h_sum_eq : ∑ x ∈ U', f x = ∑ x ∈ U' \ V', f x + ∑ x ∈ U' ∩ V', f x ∧ ∑ x ∈ V', f x = ∑ x ∈ V' \ U', f x + ∑ x ∈ U' ∩ V', f x := by
          exact ⟨ by rw [ ← Finset.sum_union ( Finset.disjoint_right.mpr fun x => by aesop ) ] ; congr; ext x; by_cases hx : x ∈ V' <;> aesop, by rw [ ← Finset.sum_union ( Finset.disjoint_right.mpr fun x => by aesop ) ] ; congr; ext x; by_cases hx : x ∈ U' <;> aesop ⟩;
        linarith;
      refine' ⟨ U, V, _, _, h_disjoint, h_nonempty_U, h_nonempty_V, _ ⟩ <;> simp_all +decide [ Phi ];
      · exact fun x hx => hS.1 <| hU'V'.1 <| Finset.mem_sdiff.mp hx |>.1;
      · exact fun x hx => hS.1 <| hU'V'.2.1 <| Finset.mem_sdiff.mp hx |>.1;
      · convert congr_arg ( ( ↑ ) : ℕ → ℚ ) h_sum_eq using 1;
        · simp +zetaDelta at *;
          exact Finset.sum_congr rfl fun x hx => by rw [ ← Int.toNat_of_nonneg ( show 0 ≤ x.1 from hS.1 ( hU'V'.1 ( Finset.mem_sdiff.mp hx |>.1 ) ) |>.1 ), ← Int.toNat_of_nonneg ( show 0 ≤ x.2 from hS.1 ( hU'V'.1 ( Finset.mem_sdiff.mp hx |>.1 ) ) |>.2 ) ] ; norm_cast;
        · simp +zetaDelta at *;
          exact Finset.sum_congr rfl fun x hx => by rw [ ← Int.toNat_of_nonneg ( show 0 ≤ x.1 by exact hS.1 ( hU'V'.2.1 ( Finset.mem_sdiff.mp hx |>.1 ) ) |>.1 ), ← Int.toNat_of_nonneg ( show 0 ≤ x.2 by exact hS.1 ( hU'V'.2.1 ( Finset.mem_sdiff.mp hx |>.1 ) ) |>.2 ) ] ; norm_cast;

/-
Phi of a translated set is the shifted value, assuming p, q >= 2.
-/
lemma Phi_translate (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (S : Finset (ℤ × ℤ)) (t : ℤ × ℤ) :
  Phi p q (translate_set S t) = (p : ℚ) ^ (-t.1) * (q : ℚ) ^ (-t.2) * Phi p q S := by
    simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Phi, translate_set ];
    exact Finset.sum_congr rfl fun x hx => by rw [ zpow_sub₀ ( by positivity ), zpow_sub₀ ( by positivity ) ] ; ring;

/-
Algebraic identity: P^-A Q^-B P^A Q^B = 1.
-/
lemma inv_mul_cancel_pow (P Q : ℕ) (A B : ℤ) (hP : 2 ≤ P) (hQ : 2 ≤ Q) :
  (P : ℚ) ^ (-A) * (Q : ℚ) ^ (-B) * ((P : ℚ) ^ A * (Q : ℚ) ^ B) = 1 := by
    norm_cast ; norm_num [ mul_mul_mul_comm, mul_assoc, mul_left_comm, zpow_add₀, show P ≠ 0 by linarith, show Q ≠ 0 by linarith ];
    field_simp

/-
If we shift a set S by (A,B) which maximizes u+v, the result (excluding the origin) is disjoint from Q_set.
-/
lemma shift_disjoint_Q (S : Finset (ℤ × ℤ)) (A B : ℤ) (h_max : ∀ x ∈ S, x.1 + x.2 ≤ A + B) :
  Disjoint (translate_set (S.erase (A, B)) (A, B) : Set (ℤ × ℤ)) Q_set := by
    unfold Q_set translate_set;
    norm_num [ Set.disjoint_left ];
    grind

/-
There exist finite disjoint sets E, F in Z^2 such that 1 = Phi(E) - Phi(F) and E, F are disjoint from Q_set.
-/
lemma lem_unit (P Q : ℕ) (hP : 2 ≤ P) (hQ : 2 ≤ Q) :
  ∃ E F : Finset (ℤ × ℤ),
    Disjoint E F ∧
    1 = Phi P Q E - Phi P Q F ∧
    Disjoint (E ∪ F : Set (ℤ × ℤ)) Q_set := by
      -- Apply `lem_equal` to get disjoint nonempty $U, V \subseteq Q_{set}$ with $\Phi(U) = \Phi(V)$.
      obtain ⟨U, V, hUV_disjoint, hUV_nonempty, hUV_eq⟩ : ∃ U V : Finset (ℤ × ℤ), (U : Set (ℤ × ℤ)) ⊆ Q_set ∧ (V : Set (ℤ × ℤ)) ⊆ Q_set ∧ Disjoint U V ∧ U.Nonempty ∧ V.Nonempty ∧ Phi P Q U = Phi P Q V := by
        exact lem_equal P Q hP hQ;
      -- Let $S = U \cup V$. Since $S$ is finite and nonempty, there exists $(A,B) \in S$ maximizing $u+v$.
      obtain ⟨A, B, h_max⟩ : ∃ A B : ℤ, (A, B) ∈ U ∪ V ∧ ∀ x ∈ U ∪ V, x.1 + x.2 ≤ A + B := by
        have := Finset.exists_max_image ( U ∪ V ) ( fun x => x.1 + x.2 ) ⟨ _, Finset.mem_union_left _ hUV_eq.2.1.choose_spec ⟩ ; aesop;
      -- WLOG assume $(A,B) \in V$ (if in $U$, swap $U$ and $V$).
      by_cases hAB_in_V : (A, B) ∈ V;
      · -- Let $V' = V \setminus \{(A,B)\}$. Then $\Phi(V) = P^A Q^B + \Phi(V')$.
        set V' : Finset (ℤ × ℤ) := V.erase (A, B)
        have hV'_eq : Phi P Q V = (P : ℚ) ^ A * (Q : ℚ) ^ B + Phi P Q V' := by
          unfold Phi; aesop;
        -- Define $E = \text{translate\_set}(U, (A,B))$ and $F = \text{translate\_set}(V', (A,B))$.
        set E : Finset (ℤ × ℤ) := translate_set U (A, B)
        set F : Finset (ℤ × ℤ) := translate_set V' (A, B);
        refine' ⟨ E, F, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
        · simp +zetaDelta at *;
          unfold translate_set; aesop;
        · -- By `Phi_translate`, $\Phi(E) = P^{-A} Q^{-B} \Phi(U)$ and $\Phi(F) = P^{-A} Q^{-B} \Phi(V')$.
          have hE_F_eq : Phi P Q E = (P : ℚ) ^ (-A) * (Q : ℚ) ^ (-B) * Phi P Q U ∧ Phi P Q F = (P : ℚ) ^ (-A) * (Q : ℚ) ^ (-B) * Phi P Q V' := by
            exact ⟨ Phi_translate P Q hP hQ U ( A, B ), Phi_translate P Q hP hQ V' ( A, B ) ⟩;
          rw [ hE_F_eq.1, hE_F_eq.2, hUV_eq.2.2.2 ] ; ring_nf;
          norm_num [ mul_assoc, mul_left_comm, ← zpow_add₀ ( by positivity : ( P : ℚ ) ≠ 0 ), ← zpow_add₀ ( by positivity : ( Q : ℚ ) ≠ 0 ) ];
          rw [ ← mul_assoc, mul_inv_cancel₀ ( by positivity ), one_mul, inv_mul_cancel₀ ( by positivity ) ];
        · apply And.intro;
          · convert shift_disjoint_Q U A B _;
            · exact Eq.symm ( Finset.erase_eq_of_notMem fun h => hUV_eq.1 _ _ h hAB_in_V );
            · exact fun x hx => h_max _ _ <| Or.inl hx;
          · apply shift_disjoint_Q;
            exact fun x hx => h_max _ _ <| Or.inr hx;
      · -- Since $(A,B) \notin V$, we have $(A,B) \in U$.
        have hAB_in_U : (A, B) ∈ U := by
          aesop;
        -- Let $U' = U \setminus \{(A,B)\}$. Then $\Phi(U) = P^A Q^B + \Phi(U')$.
        set U' := U.erase (A, B) with hU'_def
        have hU'_eq : Phi P Q U = (P : ℚ) ^ A * (Q : ℚ) ^ B + Phi P Q U' := by
          unfold Phi; aesop;
        -- Define $E = \text{translate\_set}(V, (A,B))$ and $F = \text{translate\_set}(U', (A,B))$.
        use translate_set V (A, B), translate_set U' (A, B);
        refine' ⟨ _, _, _ ⟩;
        · simp_all +decide [ Finset.disjoint_left, Set.disjoint_left ];
          unfold translate_set; aesop;
        · -- By `Phi_translate`, $\Phi(E) = P^{-A} Q^{-B} \Phi(V)$ and $\Phi(F) = P^{-A} Q^{-B} \Phi(U')$.
          have hE_eq : Phi P Q (translate_set V (A, B)) = (P : ℚ) ^ (-A) * (Q : ℚ) ^ (-B) * Phi P Q V := by
            apply Phi_translate P Q hP hQ V (A, B)
          have hF_eq : Phi P Q (translate_set U' (A, B)) = (P : ℚ) ^ (-A) * (Q : ℚ) ^ (-B) * Phi P Q U' := by
            convert Phi_translate P Q hP hQ U' ( A, B ) using 1;
          simp_all +decide [ mul_sub ];
          rw [ ← mul_sub, ← hUV_eq.2.2.2, add_sub_cancel_right, inv_mul_eq_div, div_eq_mul_inv ];
          field_simp;
        · simp_all +decide [ Set.disjoint_left, translate_set ];
          rintro a b ( ⟨ a', b', h₁, rfl, rfl ⟩ | ⟨ ⟨ a', b', h₁, rfl, rfl ⟩, h₂ ⟩ ) <;> simp_all +decide [ Q_set ];
          · exact fun h₂ => lt_of_not_ge fun h₃ => hAB_in_V <| by convert h₁ using 1; exact Prod.ext ( by linarith [ h_max _ _ <| Or.inr h₁ ] ) ( by linarith [ h_max _ _ <| Or.inr h₁ ] ) ;
          · grind

/-
Scaling the set by M corresponds to raising bases to power M in Phi, provided M != 0.
-/
def max_norm (S : Finset (ℤ × ℤ)) : ℕ :=
  S.sup (fun x => max x.1.natAbs x.2.natAbs)

def scale_set (M : ℕ) (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S.image (fun x => (M * x.1, M * x.2))

lemma Phi_scale (p q : ℕ) (M : ℕ) (hM : M ≠ 0) (S : Finset (ℤ × ℤ)) :
  Phi p q (scale_set M S) = Phi (p ^ M) (q ^ M) S := by
    unfold Phi scale_set
    simp [Finset.sum_map, Finset.sum_add_distrib];
    rw [ Finset.sum_image ];
    · norm_num [ zpow_mul ];
    · intro x hx y hy; aesop;

/-
There exist sequences of sets E_i, F_i of length k satisfying the unit equation, disjointness from Q, and pairwise disjointness.
-/
lemma exists_sequence_EF (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (k : ℕ) :
  ∃ E F : Fin k → Finset (ℤ × ℤ),
    (∀ i, Disjoint (E i) (F i)) ∧
    (∀ i, 1 = Phi p q (E i) - Phi p q (F i)) ∧
    (∀ i, Disjoint (E i ∪ F i : Set (ℤ × ℤ)) Q_set) ∧
    (∀ i j, i ≠ j → Disjoint (E i ∪ F i) (E j ∪ F j)) := by
      norm_num +zetaDelta at *;
      have h_ind : ∀ n : ℕ, ∃ E F : Fin n → Finset (ℤ × ℤ),
        (∀ i, Disjoint (E i) (F i)) ∧
        (∀ i, 1 = Phi p q (E i) - Phi p q (F i)) ∧
        (∀ i, Disjoint (E i ∪ F i : Set (ℤ × ℤ)) Q_set) ∧
        (∀ i j, i ≠ j → Disjoint ((E i ∪ F i) : Finset (ℤ × ℤ)) (E j ∪ F j)) := by
          intro n;
          induction' n with n ih;
          · exact ⟨ fun _ => ∅, fun _ => ∅, by simp +decide ⟩;
          · obtain ⟨ E, F, hE, hF, hQ, h ⟩ := ih;
            -- Let $S$ be the union of all $E_i$ and $F_i$ for $i < n$.
            set S : Finset (ℤ × ℤ) := Finset.biUnion Finset.univ (fun i => E i ∪ F i) with hS_def;
            -- Let $M = 1 + \max_{x \in S} \|x\|$.
            obtain ⟨M, hM⟩ : ∃ M : ℕ, M > 0 ∧ ∀ x ∈ S, max x.1.natAbs x.2.natAbs < M := by
              exact ⟨ Finset.sup S ( fun x => Max.max x.1.natAbs x.2.natAbs ) + 1, Nat.succ_pos _, fun x hx => Nat.lt_succ_of_le ( Finset.le_sup ( f := fun x => Max.max x.1.natAbs x.2.natAbs ) hx ) ⟩;
            -- Let $E'$ and $F'$ be the sets obtained from Lemma lem_unit with $P = p^M$ and $Q = q^M$.
            obtain ⟨E', F', hE', hF', hQ'⟩ : ∃ E' F' : Finset (ℤ × ℤ),
              Disjoint E' F' ∧
              1 = Phi (p ^ M) (q ^ M) E' - Phi (p ^ M) (q ^ M) F' ∧
              Disjoint (E' ∪ F' : Set (ℤ × ℤ)) Q_set := by
                have := lem_unit ( p ^ M ) ( q ^ M ) ( by linarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ p ) hM.1 ] ) ( by linarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ q ) hM.1 ] ) ; aesop;
            -- Let $E_{n} = \text{scale\_set } M E'$ and $F_{n} = \text{scale\_set } M F'$.
            use Fin.cons (scale_set M E') E, Fin.cons (scale_set M F') F;
            simp_all +decide [ Fin.forall_fin_succ, Finset.disjoint_left, Set.disjoint_left ];
            refine' ⟨ _, _, _, _, _ ⟩;
            · unfold scale_set; simp +contextual [ hE' ] ;
              intro a b x y hx hy hxy z w hz hz' hw'; specialize hE' x y hx; specialize hF' ; aesop;
            · refine' ⟨ _, hF ⟩;
              rw [ ← Phi_scale, ← Phi_scale ];
              · linarith;
              · linarith;
            · simp_all +decide [ scale_set ];
              constructor;
              · rintro a b ( ⟨ a', b', ha', rfl, rfl ⟩ | ⟨ a', b', ha', rfl, rfl ⟩ ) <;> simp_all +decide [ Q_set ];
                · exact hQ' _ _ ( Or.inl ha' );
                · exact hQ' _ _ ( Or.inr ha' );
              · exact fun i a b a_1 => hQ i a b a_1;
            · intro i hi a b hab; specialize hM; specialize hQ i; specialize h i; simp_all +decide [ Fin.ext_iff, scale_set ] ;
              rcases hab with ( ⟨ a', b', ha', rfl, rfl ⟩ | ⟨ a', b', ha', rfl, rfl ⟩ ) <;> simp_all +decide [ Q_set ];
              · constructor <;> intro H <;> specialize hM <;> specialize hQ' a' b' ( Or.inl ha' ) <;> specialize hM <;> specialize hQ <;> specialize hQ ( M * a' ) ( M * b' ) <;> simp_all +decide [ mul_nonneg ];
                · have := hM.2 _ _ i ( Or.inl H ) ; simp_all +decide [ Int.natAbs_mul ] ;
                · have := hM.2 _ _ i ( Or.inr H ) ; simp_all +decide [ Int.natAbs_mul ] ;
              · constructor <;> intro H <;> specialize hM <;> have := hM.2 _ _ i ( by tauto ) <;> simp_all +decide [ Int.natAbs_mul ];
                · linarith [ hQ _ _ ( Or.inl H ) ( by norm_num ) ];
                · linarith [ hQ _ _ ( Or.inr H ) ( by norm_num ) ];
            · intro i; refine' ⟨ _, _ ⟩;
              · simp_all +decide [ scale_set ];
                intro a b hab; refine' ⟨ _, _ ⟩ <;> intro x y hx hy <;> specialize hM <;> specialize hQ' x y <;> simp_all +decide [ Q_set ] ;
                · contrapose! hQ';
                  constructor <;> nlinarith [ hM.2 _ _ i hab, abs_lt.mp ( show |a| < M by linarith [ hM.2 _ _ i hab ] ), abs_lt.mp ( show |b| < M by linarith [ hM.2 _ _ i hab ] ) ];
                · contrapose! hQ';
                  constructor <;> nlinarith [ hM.2 _ _ i hab, abs_lt.mp ( show |a| < M from by linarith [ hM.2 _ _ i hab ] ), abs_lt.mp ( show |b| < M from by linarith [ hM.2 _ _ i hab ] ) ];
              · exact fun j hij a b hab => h i j hij a b hab;
      obtain ⟨ E, F, hE, hF, hE', hF' ⟩ := h_ind k; use E, F; aesop;

/-
Phi of a shifted set scales by p^t1 q^t2.
-/
def shift_set (S : Finset (ℤ × ℤ)) (t : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  translate_set S (-t.1, -t.2)

lemma Phi_shift (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (S : Finset (ℤ × ℤ)) (t : ℤ × ℤ) :
  Phi p q (shift_set S t) = (p : ℚ) ^ t.1 * (q : ℚ) ^ t.2 * Phi p q S := by
    convert Phi_translate p q hp hq S ( -t.1, -t.2 ) using 1 ; ring_nf

/-
Uniqueness of representation p^u q^v.
-/
lemma unique_representation (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) (u v u' v' : ℤ) :
  (p : ℚ) ^ u * (q : ℚ) ^ v = (p : ℚ) ^ u' * (q : ℚ) ^ v' ↔ u = u' ∧ v = v' := by
    -- If $p^u q^v = p^{u'} q^{v'}$, then $p^{u-u'} = q^{v'-v}$. Taking logs, $(u-u') \log p = (v'-v) \log q$.
    have h_log : (p : ℚ) ^ u * (q : ℚ) ^ v = (p : ℚ) ^ u' * (q : ℚ) ^ v' → (u - u') * Real.log p = (v' - v) * Real.log q := by
      intro h; apply_fun Real.log at h; simp_all +decide [ Real.log_mul, ne_of_gt ( zero_lt_two.trans_le hp ), ne_of_gt ( zero_lt_two.trans_le hq ) ] ;
      rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_zpow, Real.log_zpow, Real.log_zpow, Real.log_zpow ] at h ; linarith;
    -- If $v' \neq v$, then $\frac{\log p}{\log q} = \frac{v'-v}{u-u'}$ is rational.
    have h_rat : (u - u') * Real.log p = (v' - v) * Real.log q → (v' = v ∧ u = u') := by
      intro h_eq
      by_contra h_neq
      have h_rat : ∃ r : ℚ, Real.log p / Real.log q = r := by
        by_cases hu : u = u' <;> by_cases hv : v = v' <;> simp_all +decide [ sub_eq_iff_eq_add ];
        · norm_cast at h_eq; aesop;
        · norm_cast at h_eq ; aesop;
        · exact ⟨ ( v' - v ) / ( u - u' ), by push_cast; rw [ div_eq_div_iff ] <;> cases lt_or_gt_of_ne ( show ( u : ℝ ) ≠ u' from mod_cast hu ) <;> cases lt_or_gt_of_ne ( show ( v : ℝ ) ≠ v' from mod_cast hv ) <;> nlinarith [ Real.log_pos ( show ( p : ℝ ) > 1 by norm_cast ), Real.log_pos ( show ( q : ℝ ) > 1 by norm_cast ) ] ⟩;
      exact absurd h_rat ( by exact fun ⟨ r, hr ⟩ => log_ratio_irrational hp hq h_coprime <| by use r; aesop );
    grind

/-
Characterization of FS(Gamma) in terms of Phi.
-/
lemma mem_FS_Gamma_iff_exists_Phi (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) (s : ℕ) :
  s ∈ FS (Gamma p q) ↔ ∃ S : Finset (ℤ × ℤ), (S : Set (ℤ × ℤ)) ⊆ Q_set ∧ Phi p q S = s := by
    constructor <;> intro hs <;> simp_all +decide [ Nat.Coprime ];
    · obtain ⟨ F, hF₁, hF₂ ⟩ := hs;
      -- Since $F$ is a finite subset of $\Gamma(p, q)$, we can write each element $x \in F$ as $p^u q^v$ for some $u, v \geq 0$.
      have hF_rewrite : ∀ x ∈ F, ∃ u v : ℕ, x = p^u * q^v := by
        intro x hx; specialize hF₁ hx; unfold Gamma at hF₁; aesop;
      choose! u v huv using hF_rewrite;
      -- Let $S$ be the set of pairs $(u(x), v(x))$ for $x \in F$.
      use Finset.image (fun x => (u x, v x)) F;
      norm_num [ Q_set, Phi ];
      rw [ Finset.sum_image ] <;> norm_num [ hF₂ ];
      · exact Finset.sum_congr rfl fun x hx => mod_cast huv x hx ▸ rfl;
      · intro x hx y hy; have := huv x hx; have := huv y hy; simp +decide [ ← this, ← huv x hx ] at *;
        intro hx' hy'; rw [ huv x hx, huv y hy, hx', hy' ] ;
    · obtain ⟨ S, hS₁, hS₂ ⟩ := hs;
      -- Consider the subset $F$ of $\Gamma(p,q)$ consisting of the elements $p^{u} q^{v}$ for $(u,v) \in S$.
      set F := S.image (fun x => p ^ x.1.toNat * q ^ x.2.toNat) with hF_def;
      -- By definition of $F$, we know that $F \subseteq \Gamma(p,q)$.
      have hF_subset_Gamma : (F : Set ℕ) ⊆ Gamma p q := by
        exact fun x hx => by obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact ⟨ Int.toNat y.1, Int.toNat y.2, rfl ⟩ ;
      -- By definition of $F$, we know that $\sum_{x \in F} x = \Phi(S)$.
      have hF_sum : ∑ x ∈ F, x = Phi p q S := by
        rw [ Finset.sum_image ];
        · unfold Phi; norm_num;
          exact Finset.sum_congr rfl fun x hx => by rw [ ← Int.toNat_of_nonneg ( hS₁ hx |>.1 ), ← Int.toNat_of_nonneg ( hS₁ hx |>.2 ) ] ; norm_cast;
        · intros x hx y hy; have := hS₁ hx; have := hS₁ hy; simp_all +decide [ Q_set ] ;
          intro h; have := unique_representation p q hp hq h_coprime x.1.toNat x.2.toNat y.1.toNat y.2.toNat; simp_all +decide [ Int.toNat_of_nonneg ] ;
          exact Prod.ext ( this.mp ( by rw [ ← Int.toNat_of_nonneg ( by linarith : 0 ≤ x.1 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ x.2 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ y.1 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ y.2 ) ] at *; exact mod_cast h ) |>.1 ) ( this.mp ( by rw [ ← Int.toNat_of_nonneg ( by linarith : 0 ≤ x.1 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ x.2 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ y.1 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ y.2 ) ] at *; exact mod_cast h ) |>.2 );
      use F;
      exact ⟨ hF_subset_Gamma, by rw [ ← @Nat.cast_inj ℚ ] ; aesop ⟩

/-
There exist A, B, R such that m p^A q^B + R is representable by a subset of Q for all m.
-/
theorem prop_AP (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) :
  ∃ A B : ℕ, ∃ R : ℤ, ∀ m : ℕ, ∃ S_m : Finset (ℤ × ℤ),
    (S_m : Set (ℤ × ℤ)) ⊆ Q_set ∧
    Phi p q S_m = m * (p : ℚ) ^ A * (q : ℚ) ^ B + R := by
      have := prop_boundedgaps hp hq h_coprime;
      choose L hL₁ hL₂ using this;
      -- Let $r = \sum_{i=0}^{L-1} \Phi(F_i)$.
      obtain ⟨E, F, hEF₁, hEF₂, hEF₃, hEF₄⟩ : ∃ E F : Fin L → Finset (ℤ × ℤ), (∀ i, Disjoint (E i) (F i)) ∧ (∀ i, 1 = Phi p q (E i) - Phi p q (F i)) ∧ (∀ i, Disjoint (E i ∪ F i : Set (ℤ × ℤ)) Q_set) ∧ (∀ i j, i ≠ j → Disjoint (E i ∪ F i) (E j ∪ F j)) := by
        exact exists_sequence_EF p q hp hq L;
      -- Let $S_{all} = \bigcup_{i=0}^{L-1} (E_i \cup F_i)$.
      set S_all : Finset (ℤ × ℤ) := Finset.biUnion Finset.univ (fun i => E i ∪ F i);
      -- Since $S_{all}$ is finite, there exist $A, B \ge 0$ such that for all $(u,v) \in S_{all}$, $u+A \ge 0$ and $v+B \ge 0$.
      obtain ⟨A, B, hAB⟩ : ∃ A B : ℤ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ x ∈ S_all, x.1 + A ≥ 0 ∧ x.2 + B ≥ 0 := by
        obtain ⟨A, hA⟩ : ∃ A : ℤ, 0 ≤ A ∧ ∀ x ∈ S_all, x.1 + A ≥ 0 := by
          exact ⟨ ∑ x ∈ S_all, |x.1|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x hx => by cases abs_cases x.1 <;> linarith [ Finset.single_le_sum ( fun x _ => abs_nonneg x.1 ) hx ] ⟩;
        obtain ⟨B, hB⟩ : ∃ B : ℤ, 0 ≤ B ∧ ∀ x ∈ S_all, x.2 + B ≥ 0 := by
          exact ⟨ ∑ x ∈ S_all, |x.2|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x hx => by cases abs_cases x.2 <;> linarith [ Finset.single_le_sum ( fun x _ => abs_nonneg x.2 ) hx ] ⟩;
        exact ⟨ A, B, hA.1, hB.1, fun x hx => ⟨ hA.2 x hx, hB.2 x hx ⟩ ⟩;
      -- Let $R = p^A q^B r$.
      obtain ⟨R, hR⟩ : ∃ R : ℕ, (p : ℚ) ^ A * (q : ℚ) ^ B * (∑ i : Fin L, Phi p q (F i)) = R := by
        -- Since $p^A q^B \Phi(F_i)$ is an integer for each $i$, their sum is also an integer.
        have h_int : ∀ i : Fin L, ∃ R : ℕ, (p : ℚ) ^ A * (q : ℚ) ^ B * Phi p q (F i) = R := by
          intro i
          have h_int : ∀ x ∈ F i, (p : ℚ) ^ A * (q : ℚ) ^ B * (p : ℚ) ^ x.1 * (q : ℚ) ^ x.2 = (p : ℚ) ^ (x.1 + A) * (q : ℚ) ^ (x.2 + B) := by
            intro x hx;
            rw [ zpow_add₀ ( by positivity ), zpow_add₀ ( by positivity ) ] ; ring;
          -- Since $p^{x.1 + A} q^{x.2 + B}$ is an integer for each $x \in F_i$, their sum is also an integer.
          have h_int_sum : ∃ R : ℕ, ∑ x ∈ F i, (p : ℚ) ^ (x.1 + A) * (q : ℚ) ^ (x.2 + B) = R := by
            use ∑ x ∈ F i, p ^ (x.1 + A).toNat * q ^ (x.2 + B).toNat;
            simp +zetaDelta at *;
            exact Finset.sum_congr rfl fun x hx => by rw [ ← Int.toNat_of_nonneg ( hAB.2.2 _ _ i ( Or.inr hx ) |>.1 ), ← Int.toNat_of_nonneg ( hAB.2.2 _ _ i ( Or.inr hx ) |>.2 ) ] ; norm_cast;
          convert h_int_sum using 1;
          unfold Phi; simp +decide [ mul_assoc, Finset.mul_sum _ _ _, h_int ] ;
          exact funext fun R => by rw [ Finset.sum_congr rfl ] ; intros x hx; linear_combination' h_int x hx;
        choose! R hR using h_int; exact ⟨ ∑ i, R i, by push_cast; rw [ Finset.mul_sum _ _ _, Finset.sum_congr rfl fun _ _ => hR _ ] ⟩ ;
      use A.natAbs, B.natAbs, R;
      intro m
      obtain ⟨s, hs₁, hs₂, hs₃⟩ := hL₂ m
      obtain ⟨y, hy⟩ : ∃ y : ℕ, y < L ∧ m = s + y := by
        exact ⟨ m - s, by rw [ tsub_lt_iff_left hs₂ ] ; linarith, by rw [ add_tsub_cancel_of_le hs₂ ] ⟩;
      -- Let $U_m = T \cup \bigcup_{i=0}^{y-1} E_i \cup \bigcup_{i=y}^{L-1} F_i$.
      obtain ⟨T, hT₁, hT₂⟩ : ∃ T : Finset (ℤ × ℤ), (T : Set (ℤ × ℤ)) ⊆ Q_set ∧ Phi p q T = s := by
        exact (mem_FS_Gamma_iff_exists_Phi p q hp hq h_coprime s).mp hs₁
      set U_m : Finset (ℤ × ℤ) := T ∪ Finset.biUnion (Finset.univ.filter (fun i => i.val < y)) (fun i => E i) ∪ Finset.biUnion (Finset.univ.filter (fun i => y ≤ i.val)) (fun i => F i);
      -- Then $\Phi(U_m) = m + r$.
      have hU_m : Phi p q U_m = m + ∑ i : Fin L, Phi p q (F i) := by
        have hU_m : Phi p q U_m = Phi p q T + ∑ i ∈ Finset.univ.filter (fun i => i.val < y), Phi p q (E i) + ∑ i ∈ Finset.univ.filter (fun i => y ≤ i.val), Phi p q (F i) := by
          have hU_m : Phi p q U_m = Phi p q T + Phi p q (Finset.biUnion (Finset.univ.filter (fun i => i.val < y)) (fun i => E i)) + Phi p q (Finset.biUnion (Finset.univ.filter (fun i => y ≤ i.val)) (fun i => F i)) := by
            unfold Phi;
            rw [ Finset.sum_union, Finset.sum_union ];
            · simp_all +decide [ Finset.disjoint_left, Set.subset_def ];
              intro a b ha x hx; specialize hEF₃ x; simp_all +decide [ Set.disjoint_left ] ;
              exact fun h => hEF₃.1 a b h ( hT₁ a b ha );
            · simp_all +decide [ Finset.disjoint_left, Set.subset_def ];
              rintro a b ( h | ⟨ i, hi, hi' ⟩ ) x hx <;> simp_all +decide [ Finset.disjoint_left, Set.disjoint_left ];
              · exact fun hx' => hEF₃ x |>.2 _ _ hx' ( hT₁ _ _ h );
              · exact fun hx' => hEF₄ i x ( by rintro rfl; linarith ) a b ( Or.inl hi' ) |>.2 hx';
          rw [ hU_m, Phi, Phi, Phi ];
          rw [ Finset.sum_biUnion, Finset.sum_biUnion ];
          · rfl;
          · intros i hi j hj hij;
            exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( hEF₄ i j hij ) ( Finset.mem_union_right _ hx₁ ) ( Finset.mem_union_right _ hx₂ );
          · intros i hi j hj hij;
            exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( hEF₄ i j hij ) ( Finset.mem_union_left _ hx₁ ) ( Finset.mem_union_left _ hx₂ );
        have h_sum_E : ∑ i ∈ Finset.univ.filter (fun i => i.val < y), Phi p q (E i) = ∑ i ∈ Finset.univ.filter (fun i => i.val < y), (1 + Phi p q (F i)) := by
          exact Finset.sum_congr rfl fun i hi => by linarith [ hEF₂ i ] ;
        simp_all +decide [ Finset.sum_add_distrib ];
        rw [ show ( Finset.univ.filter fun i : Fin L => ( i : ℕ ) < y ) = Finset.Iio ⟨ y, by linarith ⟩ by ext; aesop ] ; norm_num ; ring_nf;
        rw [ add_assoc, ← Finset.sum_union ];
        · rcongr i ; by_cases hi : ( i : ℕ ) < y <;> aesop;
        · simp +decide [ Finset.disjoint_left ];
          exact fun i hi => hi;
      -- Let $S_m = \text{translate\_set } U_m (-A, -B)$.
      set S_m : Finset (ℤ × ℤ) := translate_set U_m (-A, -B);
      refine' ⟨ S_m, _, _ ⟩;
      · intro x hx
        obtain ⟨u, hu⟩ : ∃ u ∈ U_m, x = (u.1 - (-A), u.2 - (-B)) := by
          norm_num +zetaDelta at *;
          unfold translate_set at hx; aesop;
        simp_all +decide [ Q_set ];
        simp +zetaDelta at *;
        rcases hu.1 with ( hu | ⟨ i, hi, hu ⟩ | ⟨ i, hi, hu ⟩ ) <;> [ exact ⟨ by linarith [ Set.mem_setOf.mp ( hT₁ hu ) ], by linarith [ Set.mem_setOf.mp ( hT₁ hu ) ] ⟩ ; exact hAB.2.2 _ _ _ ( Or.inl hu ) ; exact hAB.2.2 _ _ _ ( Or.inr hu ) ];
      · -- By definition of $S_m$, we have $\Phi(S_m) = p^A q^B \Phi(U_m)$.
        have hS_m : Phi p q S_m = (p : ℚ) ^ A * (q : ℚ) ^ B * Phi p q U_m := by
          convert Phi_shift p q hp hq U_m ( A, B ) using 1;
        cases A <;> cases B <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        linarith

/-
Phi of the constructed set U is the sum of Phis of its components, due to disjointness.
-/
lemma Phi_construction (p q : ℕ) (L : ℕ) (E F : Fin L → Finset (ℤ × ℤ)) (T : Finset (ℤ × ℤ)) (y : ℕ) (hy : y ≤ L)
  (hT : (T : Set (ℤ × ℤ)) ⊆ Q_set)
  (hEF_Q : ∀ i, Disjoint (E i ∪ F i : Set (ℤ × ℤ)) Q_set)
  (hEF_disj : ∀ i j, i ≠ j → Disjoint (E i ∪ F i) (E j ∪ F j))
  (hEF_self : ∀ i, Disjoint (E i) (F i)) :
  let U := T ∪ Finset.biUnion (Finset.univ.filter (fun i => i.val < y)) E ∪ Finset.biUnion (Finset.univ.filter (fun i => y ≤ i.val)) F
  Phi p q U = Phi p q T + ∑ i ∈ Finset.univ.filter (fun i => i.val < y), Phi p q (E i) + ∑ i ∈ Finset.univ.filter (fun i => y ≤ i.val), Phi p q (F i) := by
    simp +zetaDelta at *;
    rw [ Phi ];
    rw [ Finset.sum_union, Finset.sum_union ];
    · rw [ Finset.sum_biUnion, Finset.sum_biUnion ];
      · unfold Phi; ring;
      · exact fun i hi j hj hij => hEF_disj i j hij |>.2.2;
      · exact fun i hi j hj hij => hEF_disj i j hij |>.1.1;
    · simp_all +decide [ Finset.disjoint_left, Set.disjoint_left ];
      grind;
    · simp_all +decide [ Finset.disjoint_left, Set.subset_def ];
      exact fun a b hab => ⟨ fun i hi => fun hi' => by have := hEF_Q i; exact this.1.le_bot ⟨ hi', hT _ _ hab ⟩, fun i hi => fun hi' => by have := hEF_Q i; exact this.2.le_bot ⟨ hi', hT _ _ hab ⟩ ⟩

/-
Multiplication by a coprime number covers all residues modulo n.
-/
lemma residues_cover_v2 (n : ℕ) (hn : n > 0) (u : ℕ) (h_coprime : Nat.Coprime u n) :
  ∀ r : ℕ, ∃ s : ℕ, s < n ∧ (s * u) % n = r % n := by
    -- Since u and n are coprime, multiplication by u is a bijection on the residues modulo n. Hence, for any r, there exists a unique s such that s * u ≡ r (mod n).
    have h_bij : ∀ r : ℕ, ∃ s : ℕ, s * u % n = r % n := by
      intro r
      obtain ⟨s, hs⟩ : ∃ s : ℤ, s * u ≡ r [ZMOD n] := by
        have := Nat.gcd_eq_gcd_ab u n;
        exact ⟨ r * Nat.gcdA u n, by rw [ Int.modEq_iff_dvd ] ; use Nat.gcdB u n * r; nlinarith ⟩;
      exact ⟨ Int.toNat ( s % n ), by simpa [ ← Int.natCast_inj, Int.ModEq, Int.mul_emod, Int.emod_nonneg _ ( by positivity : ( n : ℤ ) ≠ 0 ) ] using hs ⟩;
    exact fun r => by obtain ⟨ s, hs ⟩ := h_bij r; exact ⟨ s % n, Nat.mod_lt _ hn, by simpa [ Nat.mul_mod ] using hs ⟩ ;

/-
Subset sums of a set of elements all congruent to u cover all residues modulo m, if u is coprime to m.
-/
lemma subset_sums_cover_residues (m : ℕ) (hm : m > 0) (u : ℕ) (h_coprime : Nat.Coprime u m)
  (S : Finset ℕ) (hS_card : S.card = m) (hS_mod : ∀ x ∈ S, x % m = u % m) :
  ∀ r : ℕ, ∃ U : Finset ℕ, U ⊆ S ∧ (∑ x ∈ U, x) % m = r % m := by
    intro r
    obtain ⟨s, hs_lt_m, hs_mod⟩ : ∃ s : ℕ, s < m ∧ (s * u) % m = r % m := by
      exact residues_cover_v2 m hm u h_coprime r;
    -- Since |S| = m and s < m, there exists a subset U of S with size s.
    obtain ⟨U, hU_sub, hU_card⟩ : ∃ U ⊆ S, U.card = s := by
      exact Finset.exists_subset_card_eq ( by linarith );
    exact ⟨ U, hU_sub, by simpa [ Finset.sum_nat_mod, Nat.mul_mod, Finset.sum_congr rfl fun x hx => hS_mod x ( hU_sub hx ), hU_card ] using hs_mod ⟩

/-
There exists a set of powers of p that covers all residues modulo m (via subset sums).
-/
lemma exists_powers_covering_residues (p m : ℕ) (hp : 2 ≤ p) (hm : m > 0) (h_coprime : Nat.Coprime p m) :
  ∃ S : Finset ℕ, S.card = m ∧ (∀ x ∈ S, ∃ k, x = p ^ k) ∧ (∀ r : ℕ, ∃ U : Finset ℕ, U ⊆ S ∧ (∑ x ∈ U, x) % m = r % m) := by
    -- Let $D = \phi(m)$.
    set D := Nat.totient m
    generalize_proofs at *;
    -- Let $S = \{ p^{1 + D k} : 0 \le k < m \}$.
    set S : Finset ℕ := Finset.image (fun k => p ^ (1 + D * k)) (Finset.range m);
    -- The elements are $p \cdot (p^D)^k$.
    have hS_mod : ∀ x ∈ S, x % m = p % m := by
      norm_num +zetaDelta at *;
      intro a ha; rw [ pow_add, pow_mul ] ; have := Nat.ModEq.pow_totient h_coprime; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
      simp +decide [ ← ZMod.natCast_eq_natCast_iff', this ];
    -- Since $p \ge 2$, the powers $p^{1+Dk}$ are distinct for distinct $k$.
    have hS_distinct : S.card = m := by
      rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hp ];
      exact fun a₁ a₂ h => by have := Nat.pow_right_injective ( by linarith : 1 < p ) h; aesop;
    -- Since $p$ is coprime to $m$, by `subset_sums_cover_residues`, the subset sums cover all residues mod $m$.
    have hS_cover : ∀ r : ℕ, ∃ U : Finset ℕ, U ⊆ S ∧ (∑ x ∈ U, x) % m = r % m := by
      exact fun r => subset_sums_cover_residues m hm p h_coprime S hS_distinct hS_mod r;
    exact ⟨ S, hS_distinct, fun x hx => by obtain ⟨ k, hk, rfl ⟩ := Finset.mem_image.mp hx; exact ⟨ _, rfl ⟩, hS_cover ⟩

/-
If S_m covers residues mod m and is 0 mod n, and S_n covers residues mod n and is 0 mod m, then their sums cover residues mod mn.
-/
lemma sums_cover_product (m n : ℕ) (hm : m > 0) (hn : n > 0) (h_coprime : Nat.Coprime m n)
  (S_m : Finset ℕ) (hS_m_mod : ∀ x ∈ S_m, x % n = 0) (hS_m_cover : ∀ r, ∃ U, U ⊆ S_m ∧ (∑ x ∈ U, x) % m = r % m)
  (S_n : Finset ℕ) (hS_n_mod : ∀ x ∈ S_n, x % m = 0) (hS_n_cover : ∀ r, ∃ V, V ⊆ S_n ∧ (∑ x ∈ V, x) % n = r % n) :
  ∀ T : ℕ, ∃ U V, U ⊆ S_m ∧ V ⊆ S_n ∧ (∑ x ∈ U, x + ∑ x ∈ V, x) % (m * n) = T % (m * n) := by
    simp +zetaDelta at *;
    intro T;
    obtain ⟨ U, hU₁, hU₂ ⟩ := hS_m_cover T; obtain ⟨ V, hV₁, hV₂ ⟩ := hS_n_cover T; use U, hU₁, V, hV₁; simp +decide [ Nat.add_mod, Nat.mul_mod, * ] ;
    -- By the Chinese Remainder Theorem, since $m$ and $n$ are coprime, we have:
    have h_crt : (∑ x ∈ U, x) + (∑ x ∈ V, x) ≡ T [MOD m] ∧ (∑ x ∈ U, x) + (∑ x ∈ V, x) ≡ T [MOD n] := by
      simp_all +decide [ Nat.ModEq ];
      exact ⟨ by simp +decide [ Nat.add_mod, hU₂, Nat.mod_eq_zero_of_dvd ( Finset.dvd_sum fun x hx => Nat.dvd_of_mod_eq_zero ( hS_n_mod x ( hV₁ hx ) ) ) ], by simp +decide [ Nat.add_mod, hV₂, Nat.mod_eq_zero_of_dvd ( Finset.dvd_sum fun x hx => Nat.dvd_of_mod_eq_zero ( hS_m_mod x ( hU₁ hx ) ) ) ] ⟩;
    simp_all +decide [ Nat.ModEq ];
    rw [ Nat.ModEq.symm ];
    rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ] ; tauto;
    assumption

/-
There exist A, B, R such that m p^A q^B + R is representable by a subset of Q for all m.
-/
theorem prop_AP_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) :
  ∃ A B : ℕ, ∃ R : ℤ, ∀ m : ℕ, ∃ S_m : Finset (ℤ × ℤ),
    (S_m : Set (ℤ × ℤ)) ⊆ Q_set ∧
    Phi p q S_m = m * (p : ℚ) ^ A * (q : ℚ) ^ B + R := by
      exact prop_AP p q hp hq h_coprime

/-
There exist sets P and Q of powers of p and q respectively, such that P consists of multiples of p^(A+1) covering residues mod q^(B+1), and Q consists of multiples of q^(B+1) covering residues mod p^(A+1).
-/
lemma exists_good_sets (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) (A B : ℕ) :
  ∃ P Q : Finset ℕ,
    (∀ x ∈ P, ∃ k, x = p ^ k) ∧
    (∀ y ∈ Q, ∃ k, y = q ^ k) ∧
    (∀ x ∈ P, p ^ (A + 1) ∣ x) ∧
    (∀ y ∈ Q, q ^ (B + 1) ∣ y) ∧
    (∀ r : ℕ, ∃ U ⊆ P, (∑ x ∈ U, x) % q ^ (B + 1) = r % q ^ (B + 1)) ∧
    (∀ r : ℕ, ∃ V ⊆ Q, (∑ y ∈ V, y) % p ^ (A + 1) = r % p ^ (A + 1)) := by
      -- Let $D = \varphi(q^{B+1})$. Define $P = \{ p^{A+1 + (A+1)D k} \mid k \in \{0, \dots, q^{B+1}-1\} \}$.
      set D := Nat.totient (q ^ (B + 1))
      set P := Finset.image (fun k => p ^ (A + 1 + (A + 1) * D * k)) (Finset.range (q ^ (B + 1)));
      have hP_cover : ∀ r : ℕ, ∃ U : Finset ℕ, U ⊆ P ∧ (∑ x ∈ U, x) % q ^ (B + 1) = r % q ^ (B + 1) := by
        have hP_cover : ∀ x ∈ P, x % q ^ (B + 1) = p ^ (A + 1) % q ^ (B + 1) := by
          have hP_mod : ∀ k : ℕ, p ^ (A + 1 + (A + 1) * D * k) ≡ p ^ (A + 1) [MOD q ^ (B + 1)] := by
            -- By Euler's theorem, since $p$ and $q$ are coprime, we have $p^{\varphi(q^{B+1})} \equiv 1 \pmod{q^{B+1}}$.
            have h_euler : p ^ Nat.totient (q ^ (B + 1)) ≡ 1 [MOD q ^ (B + 1)] := by
              exact Nat.ModEq.pow_totient <| Nat.Coprime.pow_right _ h_coprime;
            intro k; convert h_euler.pow ( ( A + 1 ) * k ) |> Nat.ModEq.mul_left ( p ^ ( A + 1 ) ) using 1 <;> ring;
          aesop;
        have hP_cover : ∀ r : ℕ, ∃ U : Finset ℕ, U ⊆ P ∧ (∑ x ∈ U, x) % q ^ (B + 1) = r % q ^ (B + 1) := by
          intro r
          have hP_card : P.card = q ^ (B + 1) := by
            rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hp, hq ];
            intro a₁ a₂ h; rw [ pow_right_inj₀ ] at h <;> first |linarith|aesop;
          have hP_cover : ∀ r : ℕ, ∃ U : Finset ℕ, U ⊆ P ∧ (∑ x ∈ U, x) % q ^ (B + 1) = r % q ^ (B + 1) := by
            intro r
            have h_coprime : Nat.Coprime (p ^ (A + 1)) (q ^ (B + 1)) := by
              exact h_coprime.pow _ _
            have := subset_sums_cover_residues ( q ^ ( B + 1 ) ) ( by positivity ) ( p ^ ( A + 1 ) ) h_coprime P hP_card ( by aesop ) r; aesop;
          exact hP_cover r;
        assumption;
      -- Let $E = \varphi(p^{A+1})$. Define $Q = \{ q^{B+1 + (B+1)E k} \mid k \in \{0, \dots, p^{A+1}-1\} \}$.
      set E := Nat.totient (p ^ (A + 1))
      set Q := Finset.image (fun k => q ^ (B + 1 + (B + 1) * E * k)) (Finset.range (p ^ (A + 1)));
      refine' ⟨ P, Q, _, _, _, _, hP_cover, _ ⟩;
      · aesop;
      · aesop;
      · exact fun x hx => by obtain ⟨ k, hk, rfl ⟩ := Finset.mem_image.mp hx; exact pow_dvd_pow _ ( by nlinarith [ show 0 ≤ D * k by positivity ] ) ;
      · exact fun x hx => by obtain ⟨ k, _, rfl ⟩ := Finset.mem_image.mp hx; exact pow_dvd_pow _ ( by nlinarith [ show 0 ≤ ( B + 1 ) * E * k by positivity ] ) ;
      · -- Apply `subset_sums_cover_residues` with $m = p^{A+1}$ and $u = q^{B+1}$.
        have hQ_cover : ∀ r : ℕ, ∃ V : Finset ℕ, V ⊆ Q ∧ (∑ y ∈ V, y) % p ^ (A + 1) = r % p ^ (A + 1) := by
          have h_card_Q : Q.card = p ^ (A + 1) := by
            rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
            intro a₁ a₂ h; rw [ pow_right_inj₀ ( by linarith ) ] at h <;> aesop;
          have h_mod_Q : ∀ y ∈ Q, y % p ^ (A + 1) = q ^ (B + 1) % p ^ (A + 1) := by
            simp +zetaDelta at *;
            -- By Euler's theorem, since $p$ and $q$ are coprime, we have $q^{\varphi(p^{A+1})} \equiv 1 \pmod{p^{A+1}}$.
            have h_euler : q ^ Nat.totient (p ^ (A + 1)) ≡ 1 [MOD p ^ (A + 1)] := by
              exact Nat.ModEq.pow_totient <| Nat.Coprime.pow_right _ <| h_coprime.symm;
            intro k hk; rw [ Nat.pow_add, Nat.pow_mul ] ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, pow_mul' ]
          apply subset_sums_cover_residues;
          any_goals assumption;
          · positivity;
          · exact h_coprime.symm.pow _ _;
        assumption

/-
Given sets P and Q with specific divisibility and covering properties, we can find subsets P0 and Q0 such that their sum is congruent to T modulo p^(A+1)q^(B+1).
-/
lemma exists_subsets_sum_mod (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) (A B : ℕ)
  (P Q : Finset ℕ)
  (hP_mod : ∀ x ∈ P, p ^ (A + 1) ∣ x)
  (hQ_mod : ∀ y ∈ Q, q ^ (B + 1) ∣ y)
  (hP_cover : ∀ r : ℕ, ∃ U ⊆ P, (∑ x ∈ U, x) % q ^ (B + 1) = r % q ^ (B + 1))
  (hQ_cover : ∀ r : ℕ, ∃ V ⊆ Q, (∑ y ∈ V, y) % p ^ (A + 1) = r % p ^ (A + 1))
  (T : ℕ) :
  ∃ P₀ Q₀ : Finset ℕ, P₀ ⊆ P ∧ Q₀ ⊆ Q ∧ (∑ x ∈ P₀, x + ∑ y ∈ Q₀, y) % (p ^ (A + 1) * q ^ (B + 1)) = T % (p ^ (A + 1) * q ^ (B + 1)) := by
    have h_sum_cong : ∃ P₀ Q₀ : Finset ℕ, P₀ ⊆ P ∧ Q₀ ⊆ Q ∧ (∑ x ∈ P₀, x) % q ^ (B + 1) = T % q ^ (B + 1) ∧ (∑ y ∈ Q₀, y) % p ^ (A + 1) = T % p ^ (A + 1) := by
      exact Exists.elim ( hP_cover T ) fun P₀ hP₀ => Exists.elim ( hQ_cover T ) fun Q₀ hQ₀ => ⟨ P₀, Q₀, hP₀.1, hQ₀.1, hP₀.2, hQ₀.2 ⟩;
    simp +zetaDelta at *;
    obtain ⟨ P₀, hP₀, x, hx, hx₁, hx₂ ⟩ := h_sum_cong; use P₀, hP₀, x, hx; rw [ Nat.modEq_of_dvd ] ; simp_all +decide [ ← Int.natCast_dvd_natCast ] ;
    have h_div : (p ^ (A + 1) : ℤ) ∣ (T - (∑ x ∈ P₀, x + ∑ y ∈ x, y)) ∧ (q ^ (B + 1) : ℤ) ∣ (T - (∑ x ∈ P₀, x + ∑ y ∈ x, y)) := by
      constructor;
      · have h_div : (p ^ (A + 1) : ℤ) ∣ (∑ x ∈ P₀, x) := by
          exact Finset.dvd_sum fun x hx => hP_mod x ( hP₀ hx );
        obtain ⟨ k, hk ⟩ := h_div; obtain ⟨ l, hl ⟩ := Nat.modEq_iff_dvd.mp hx₂.symm; use -k - l; push_cast at *; linarith;
      · have h_div_q : (q ^ (B + 1) : ℤ) ∣ (∑ y ∈ x, y) := by
          exact Finset.dvd_sum fun y hy => hQ_mod y <| hx hy;
        obtain ⟨ k, hk ⟩ := h_div_q; use -k + ( T / q ^ ( B + 1 ) - ( ∑ x ∈ P₀, x ) / q ^ ( B + 1 ) ) ; push_cast at *; linarith [ Nat.mod_add_div T ( q ^ ( B + 1 ) ), Nat.mod_add_div ( ∑ x ∈ P₀, x ) ( q ^ ( B + 1 ) ) ] ;
    convert Int.coe_lcm_dvd h_div.1 h_div.2 using 1;
    · exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| by exact_mod_cast h_coprime.pow _ _ );
    · norm_num

/-
For any N larger than a certain bound C, N can be decomposed into a sum of subset sums from P and Q, a constant term involving R, and a multiple of p^(A+1)q^(B+1).
-/
lemma decompose_N (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q) (A B : ℕ) (R : ℤ)
  (P Q : Finset ℕ)
  (hP_mod : ∀ x ∈ P, p ^ (A + 1) ∣ x)
  (hQ_mod : ∀ y ∈ Q, q ^ (B + 1) ∣ y)
  (hP_cover : ∀ r : ℕ, ∃ U ⊆ P, (∑ x ∈ U, x) % q ^ (B + 1) = r % q ^ (B + 1))
  (hQ_cover : ∀ r : ℕ, ∃ V ⊆ Q, (∑ y ∈ V, y) % p ^ (A + 1) = r % p ^ (A + 1))
  (C : ℕ) (hC : C = ∑ x ∈ P, x + ∑ y ∈ Q, y + p * q * R.natAbs) :
  ∀ N > C, ∃ P₀ Q₀ : Finset ℕ, ∃ m : ℕ,
    P₀ ⊆ P ∧ Q₀ ⊆ Q ∧
    (N : ℤ) = ∑ x ∈ P₀, (x : ℤ) + ∑ y ∈ Q₀, (y : ℤ) + p * q * R + m * (p ^ (A + 1) * q ^ (B + 1)) := by
      -- Apply `exists_subsets_sum_mod` with target $T$ such that $T \equiv N - pqR \pmod M$.
      intro N hN
      obtain ⟨P₀, Q₀, hP₀, hQ₀, h_sum⟩ := exists_subsets_sum_mod p q hp hq h_coprime A B P Q hP_mod hQ_mod hP_cover hQ_cover (Int.toNat (N - p * q * R));
      -- Since $N > C$, we have $N - pqR - S > 0$.
      have h_pos : N - p * q * R - (∑ x ∈ P₀, x + ∑ y ∈ Q₀, y) > 0 := by
        cases abs_cases R <;> push_cast [ * ] at * <;> nlinarith [ show 0 < p * q by positivity, show ∑ x ∈ P₀, x ≤ ∑ x ∈ P, x from Finset.sum_le_sum_of_subset hP₀, show ∑ y ∈ Q₀, y ≤ ∑ y ∈ Q, y from Finset.sum_le_sum_of_subset hQ₀ ];
      obtain ⟨m, hm⟩ : ∃ m : ℤ, N - p * q * R - (∑ x ∈ P₀, x + ∑ y ∈ Q₀, y) = m * (p ^ (A + 1) * q ^ (B + 1)) := by
        refine' exists_eq_mul_left_of_dvd _;
        convert Nat.modEq_iff_dvd.mp h_sum using 1;
        · rw [ Int.toNat_of_nonneg ]
          · norm_cast
          · linarith
      use P₀, Q₀, m.natAbs;
      simp_all +decide [ abs_of_nonneg ( by nlinarith [ show 0 < ( p : ℤ ) ^ ( A + 1 ) * q ^ ( B + 1 ) by positivity ] : ( 0 : ℤ ) ≤ m ) ];
      linarith

/-
The set S_m' (constructed from S_m by shifting exponents) is disjoint from sets of powers of p (P0) and powers of q (Q0), and P0 is disjoint from Q0.
-/
lemma disjoint_parts (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q)
  (S_m : Finset (ℤ × ℤ)) (hS_m : (S_m : Set (ℤ × ℤ)) ⊆ Q_set)
  (P₀ Q₀ : Finset ℕ)
  (hP₀ : ∀ x ∈ P₀, ∃ k, x = p ^ k)
  (hQ₀ : ∀ y ∈ Q₀, ∃ k, y = q ^ k)
  (hP_div : ∀ x ∈ P₀, p ∣ x)
  (hQ_div : ∀ y ∈ Q₀, q ∣ y) :
  let S_m' := S_m.image (fun x => p ^ (x.1.toNat + 1) * q ^ (x.2.toNat + 1))
  Disjoint S_m' P₀ ∧ Disjoint S_m' Q₀ ∧ Disjoint P₀ Q₀ := by
    constructor;
    · rw [ Finset.disjoint_left ];
      intro x hx₁ hx₂; obtain ⟨ k₁, hk₁ ⟩ := hP₀ x hx₂; obtain ⟨ k₂, hk₂ ⟩ := Finset.mem_image.mp hx₁; simp_all +decide [ pow_add, mul_assoc, Nat.Prime.dvd_mul ] ;
      -- Since $p$ and $q$ are coprime, $q \mid p^k₁$ implies $q \mid 1$, which is impossible.
      have hq_div_one : q ∣ p ^ k₁ := by
        exact hk₂.2 ▸ dvd_mul_of_dvd_right ( dvd_mul_of_dvd_right ( dvd_mul_left _ _ ) _ ) _;
      exact absurd ( h_coprime.symm.pow_right k₁ ) ( by intro t; have := Nat.dvd_gcd ( dvd_refl q ) hq_div_one; aesop );
    · constructor;
      · rw [ Finset.disjoint_left ];
        norm_num +zetaDelta at *;
        intros a x y hx hy hQ; obtain ⟨ k, hk ⟩ := hQ₀ a hQ; simp_all +decide [ pow_add, mul_assoc, Nat.Prime.dvd_mul ] ;
        -- Since $p$ and $q$ are coprime, $p$ must divide $q^k$, which implies $p$ divides $q$, contradicting $p \geq 2$ and $q \geq 2$.
        have h_contra : p ∣ q ^ k := by
          exact hy ▸ dvd_mul_of_dvd_right ( dvd_mul_right _ _ ) _;
        exact absurd ( h_coprime.pow_right k ) ( by intro H; have := Nat.dvd_gcd ( dvd_refl p ) h_contra; aesop );
      · rw [ Finset.disjoint_left ] ; intro x hx hy ; obtain ⟨ k₁, hk₁ ⟩ := hP₀ x hx ; obtain ⟨ k₂, hk₂ ⟩ := hQ₀ x hy ; simp_all +decide [ Nat.Prime.dvd_iff_one_le_factorization ];
        specialize hP_div _ hx ; specialize hQ_div _ hy ; simp_all +decide [ Nat.Prime.dvd_iff_one_le_factorization ];
        exact absurd ( Nat.Prime.dvd_of_dvd_pow ( Nat.minFac_prime ( by linarith ) ) ( dvd_trans ( Nat.minFac_dvd q ) hQ_div ) ) ( by intro t; have := Nat.dvd_gcd t ( Nat.minFac_dvd q ) ; aesop )

/-
If there is an arithmetic progression of sums of elements of Gamma(p,q) representable by subsets of Q, then Gamma(p,q) is complete.
-/
theorem prop_APtoComplete (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h_coprime : Nat.Coprime p q)
  (h_AP : ∃ A B : ℕ, ∃ R : ℤ, ∀ m : ℕ, ∃ S_m : Finset (ℤ × ℤ),
    (S_m : Set (ℤ × ℤ)) ⊆ Q_set ∧
    Phi p q S_m = m * (p : ℚ) ^ A * (q : ℚ) ^ B + R) :
  IsCompleteSeq (Gamma p q) := by
    -- By `exists_good_sets`, there exist sets $P$ and $Q$ with properties.
    obtain ⟨A, B, R, h_AP⟩ := h_AP
    obtain ⟨P, Q, hP_prop, hQ_prop⟩ : ∃ P Q : Finset ℕ,
      (∀ x ∈ P, ∃ k, x = p ^ k) ∧
      (∀ y ∈ Q, ∃ k, y = q ^ k) ∧
      (∀ x ∈ P, p ^ (A + 1) ∣ x) ∧
      (∀ y ∈ Q, q ^ (B + 1) ∣ y) ∧
      (∀ r : ℕ, ∃ U ⊆ P, (∑ x ∈ U, x) % q ^ (B + 1) = r % q ^ (B + 1)) ∧
      (∀ r : ℕ, ∃ V ⊆ Q, (∑ y ∈ V, y) % p ^ (A + 1) = r % p ^ (A + 1)) := by
        convert exists_good_sets p q hp hq h_coprime A B using 1;
    -- Let $C = \sum P + \sum Q + pq|R|$.
    set C := ∑ x ∈ P, x + ∑ y ∈ Q, y + p * q * R.natAbs with hC_def;
    -- We show that for all $N > C$, $N \in \operatorname{FS}(\Gamma(p,q))$.
    have h_all_gt_C : ∀ N > C, N ∈ FS (Gamma p q) := by
      intro N hN_gt_C
      obtain ⟨P₀, Q₀, m, hP₀, hQ₀, hN_eq⟩ : ∃ P₀ Q₀ : Finset ℕ, ∃ m : ℕ,
        P₀ ⊆ P ∧ Q₀ ⊆ Q ∧
        (N : ℤ) = ∑ x ∈ P₀, (x : ℤ) + ∑ y ∈ Q₀, (y : ℤ) + p * q * R + m * (p ^ (A + 1) * q ^ (B + 1)) := by
          apply decompose_N p q hp hq h_coprime A B R P Q hQ_prop.2.1 hQ_prop.2.2.1 hQ_prop.2.2.2.1 hQ_prop.2.2.2.2 C hC_def N hN_gt_C;
      -- From `h_AP`, get $S_m$ such that $\Phi(S_m) = m p^A q^B + R$.
      obtain ⟨S_m, hS_m⟩ : ∃ S_m : Finset (ℤ × ℤ), (S_m : Set (ℤ × ℤ)) ⊆ Q_set ∧ Phi p q S_m = m * (p : ℚ) ^ A * (q : ℚ) ^ B + R := h_AP m;
      -- Let $S_m'$ be the image of $S_m$ under $(u,v) \mapsto p^{u+1}q^{v+1}$.
      set S_m' := S_m.image (fun x => p ^ (x.1.toNat + 1) * q ^ (x.2.toNat + 1)) with hS_m'_def;
      -- Then $\Phi(S_m') = pq \Phi(S_m) = m p^{A+1}q^{B+1} + pqR$.
      have hPhi_S_m' : ∑ x ∈ S_m', x = m * (p : ℤ) ^ (A + 1) * (q : ℤ) ^ (B + 1) + p * q * R := by
        have hPhi_S_m' : ∑ x ∈ S_m', x = p * q * ∑ x ∈ S_m, (p : ℚ) ^ x.1.toNat * (q : ℚ) ^ x.2.toNat := by
          rw [ Finset.sum_image ];
          · norm_num [ pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
          · intro x hx y hy; have := hS_m.1 hx; have := hS_m.1 hy; simp_all +decide [ Q_set ] ;
            intro h; have := unique_representation p q hp hq h_coprime ( x.1.toNat + 1 ) ( x.2.toNat + 1 ) ( y.1.toNat + 1 ) ( y.2.toNat + 1 ) ; simp_all +decide [ ne_of_gt ( zero_lt_two.trans_le hp ), ne_of_gt ( zero_lt_two.trans_le hq ) ] ;
            simp_all +decide [ Int.toNat_of_nonneg, Prod.ext_iff ];
            exact this.mp ( by rw [ ← Int.toNat_of_nonneg ( by linarith : 0 ≤ x.1 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ x.2 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ y.1 ), ← Int.toNat_of_nonneg ( by linarith : 0 ≤ y.2 ) ] ; exact mod_cast h );
        convert hPhi_S_m' using 1;
        rw [ show ( ∑ x ∈ S_m, ( p : ℚ ) ^ x.1.toNat * ( q : ℚ ) ^ x.2.toNat ) = ( m : ℚ ) * p ^ A * q ^ B + R from ?_ ] ; push_cast ; ring_nf;
        · norm_cast ; ring_nf;
          norm_num [ ← @Int.cast_inj ℚ ];
        · convert hS_m.2 using 1;
          unfold Phi; norm_cast;
          rw [ Nat.cast_sum ] ; exact Finset.sum_congr rfl fun x hx => by rw [ ← Int.toNat_of_nonneg ( show 0 ≤ x.1 from hS_m.1 hx |>.1 ), ← Int.toNat_of_nonneg ( show 0 ≤ x.2 from hS_m.1 hx |>.2 ) ] ; norm_cast;
      -- By `disjoint_parts`, $S_m', P_0, Q_0$ are pairwise disjoint.
      have h_disjoint : Disjoint S_m' P₀ ∧ Disjoint S_m' Q₀ ∧ Disjoint P₀ Q₀ := by
        apply disjoint_parts p q hp hq h_coprime S_m hS_m.left P₀ Q₀;
        · exact fun x hx => hP_prop x ( hP₀ hx );
        · exact fun x hx => hQ_prop.1 x ( hQ₀ hx );
        · exact fun x hx => dvd_trans ( dvd_pow_self _ ( Nat.succ_ne_zero _ ) ) ( hQ_prop.2.1 x ( hP₀ hx ) );
        · exact fun x hx => dvd_trans ( dvd_pow_self _ ( Nat.succ_ne_zero _ ) ) ( hQ_prop.2.2.1 x ( hQ₀ hx ) );
      -- So $N$ is a sum of distinct elements of $\Gamma(p,q)$.
      have hN_sum : N = ∑ x ∈ S_m' ∪ P₀ ∪ Q₀, x := by
        rw [ Finset.sum_union, Finset.sum_union ] <;> norm_num [ h_disjoint ];
        push_cast [ ← @Nat.cast_inj ℤ ] at * ; linarith;
      refine' hN_sum ▸ ⟨ _, _, rfl ⟩;
      simp_all +decide [ Set.subset_def, Gamma ];
      rintro x ( ⟨ a, b, hx, rfl ⟩ | hx | hx ) <;> [ exact ⟨ _, _, rfl ⟩ ; exact hP_prop x ( hP₀ hx ) |> fun ⟨ k, hk ⟩ => ⟨ k, 0, by simpa using hk ⟩ ; exact hQ_prop.1 x ( hQ₀ hx ) |> fun ⟨ k, hk ⟩ => ⟨ 0, k, by simpa using hk ⟩ ];
    exact Set.finite_iff_bddAbove.mpr ⟨ C, fun N hN => not_lt.1 fun contra => hN <| h_all_gt_C N contra ⟩

/--
Erdős Problem 246: If `(a,b)=1` (i.e. `a` and `b` are coprime) and `a,
b ≥ 2`, then the set `{a^k * b^l : k,l ≥ 0}` is complete: every
sufficiently large `n` is a sum of distinct such numbers.
-/
theorem erdos_246 (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (h_coprime : Nat.Coprime a b) :
  IsCompleteSeq (Gamma a b) := by
    apply_rules [ prop_APtoComplete ];
    exact prop_AP a b ha hb h_coprime

#print axioms erdos_246
-- 'erdos_246' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos246
