import Mathlib

namespace Erdos188

variable {α : Type*} [AddCommMonoid α]

def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/--
The set of numbers $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red
points unit distance apart, and no $k$-term arithmetic progression of blue points with distance 1.
-/
def s := { k : ℕ | ∃ blue : Set ℂ,
    (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) ∧
    ¬ (∃ bs ⊆ blue, (∃ s, IsAPOfLengthWith bs k s 1)) }

/-
P_val is 100 * sqrt(2).
-/
noncomputable def P_val : ℝ := 100 * Real.sqrt 2

/-
w_val is 0.5.
-/
noncomputable def w_val : ℝ := 0.5

/-
f_map(y) is 2 * floor(2y). This is a step function used to define the vertical shifts of the red strips.
-/
noncomputable def f_map (y : ℝ) : ℝ := 2 * Int.floor (2 * y)

/-
A point z is red if its real part falls into one of the intervals [f(y) + nP, f(y) + nP + w].
-/
def is_red_point (z : ℂ) : Prop :=
  ∃ n : ℤ, 0 ≤ z.re - (f_map z.im + P_val * n) ∧ z.re - (f_map z.im + P_val * n) ≤ w_val

set_option maxHeartbeats 0 in
lemma red_dist_ne_one : {z : ℂ | is_red_point z}.Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) := by
  -- To prove the pairwise condition, we need to show that for any two distinct red points $z_1$ and $z_2$, the distance between them is not 1.
  intro z1 hz1 z2 hz2 hne
  by_contra h_dist;
  obtain ⟨ n1, hn1 ⟩ := hz1
  obtain ⟨ n2, hn2 ⟩ := hz2
  have h_dist_sq : (z1.re - z2.re)^2 + (z1.im - z2.im)^2 = 1 := by
    rw [ dist_eq_norm, Complex.norm_def ] at h_dist;
    rw [ Real.sqrt_eq_one ] at h_dist ; norm_num [ Complex.normSq ] at h_dist ; linarith;
  -- Since $|y_1 - y_2| < 1$, we have $|n_1 - n_2| \leq 3$.
  have h_n_diff : |(Int.floor (2 * z1.im)) - (Int.floor (2 * z2.im))| ≤ 3 := by
    rw [ abs_le ];
    exact ⟨ by rw [ ← @Int.cast_le ℝ ] ; push_cast; linarith [ abs_le.mp ( show |z1.im - z2.im| ≤ 1 by exact abs_le.mpr ⟨ by nlinarith, by nlinarith ⟩ ), Int.floor_le ( 2 * z1.im ), Int.lt_floor_add_one ( 2 * z1.im ), Int.floor_le ( 2 * z2.im ), Int.lt_floor_add_one ( 2 * z2.im ) ], by rw [ ← @Int.cast_le ℝ ] ; push_cast; linarith [ abs_le.mp ( show |z1.im - z2.im| ≤ 1 by exact abs_le.mpr ⟨ by nlinarith, by nlinarith ⟩ ), Int.floor_le ( 2 * z1.im ), Int.lt_floor_add_one ( 2 * z1.im ), Int.floor_le ( 2 * z2.im ), Int.lt_floor_add_one ( 2 * z2.im ) ] ⟩;
  -- Since $|n_1 - n_2| \leq 3$, we have $|x_1 - x_2| \geq P - 6 - w$.
  have h_x_diff : |z1.re - z2.re| ≥ P_val - 6 - w_val := by
    have h_x_diff : |z1.re - z2.re| ≥ |P_val * (n1 - n2)| - |2 * (Int.floor (2 * z1.im) - Int.floor (2 * z2.im))| - w_val := by
      norm_num [ f_map ] at *;
      cases abs_cases ( z1.re - z2.re ) <;> cases abs_cases ( P_val : ℝ ) <;> cases abs_cases ( ( n1 : ℝ ) - n2 ) <;> cases abs_cases ( ( ⌊2 * z1.im⌋ : ℝ ) - ⌊2 * z2.im⌋ ) <;> push_cast [ * ] at * <;> nlinarith;
    by_cases h : n1 = n2 <;> simp_all +decide [ abs_mul ];
    · unfold f_map at *;
      norm_num [ P_val, w_val ] at *;
      by_cases h_floor : ⌊2 * z1.im⌋ = ⌊2 * z2.im⌋;
      · subst h
        simp_all only [sub_self, abs_zero, Nat.ofNat_nonneg, mul_zero, neg_zero, one_div]
        obtain ⟨left, right⟩ := hn1
        obtain ⟨left_1, right_1⟩ := hn2
        rw [ Int.floor_eq_iff ] at h_floor
        nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, Int.floor_le ( 2 * z2.im ), Int.lt_floor_add_one ( 2 * z2.im ) ];
      · cases lt_or_gt_of_ne h_floor <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( ⌊2 * z1.im⌋ : ℝ ) ≥ ⌊2 * z2.im⌋ + 1 by exact_mod_cast lt_of_le_of_ne ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] } ) ( Ne.symm h_floor ) ];
    · have h_abs_diff : |(n1 : ℝ) - n2| ≥ 1 := by
        exact mod_cast abs_pos.mpr ( sub_ne_zero.mpr h );
      nlinarith [ show ( |⌊2 * z1.im⌋ - ⌊2 * z2.im⌋| : ℝ ) ≤ 3 by exact_mod_cast h_n_diff, abs_nonneg ( ⌊2 * z1.im⌋ - ⌊2 * z2.im⌋ : ℝ ), abs_nonneg ( z1.re - z2.re ), abs_of_nonneg ( show ( 0 : ℝ ) ≤ P_val by exact mul_nonneg ( by norm_num ) ( Real.sqrt_nonneg _ ) ) ];
  -- Calculate the numerical value of P_val - 6 - w_val.
  have h_num : P_val - 6 - w_val > 1 := by
    exact show ( 100 * Real.sqrt 2 - 6 - 0.5 : ℝ ) > 1 by norm_num; nlinarith only [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
  cases abs_cases ( z1.re - z2.re ) <;> nlinarith

/-
BlueSet is the complement of the set of red points.
-/
def BlueSet : Set ℂ := { z | ¬ is_red_point z }

/-- The explicit value of `k` produced by the parameter choices in this file. -/
def k_val : ℕ := 254701

/-- `1 / P_val` simplifies to `sqrt 2 / 200`. -/
lemma one_div_P_val :
    (1 / P_val : ℝ) = Real.sqrt 2 / 200 := by
  unfold P_val
  have hs : (Real.sqrt 2) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact ne_of_gt this
  field_simp [hs]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]

/-
If $p/q$ is a rational approximation to $\alpha$ with error less than $\delta/q$, then the multiples $n\alpha$ for $n < q$ are $(1/q + \delta)$-dense modulo 1.
-/
lemma dense_of_approx (q : ℕ) (p : ℤ) (α : ℝ) (δ : ℝ)
    (h_approx : |q * α - p| < δ) (h_q_pos : 0 < q) (h_coprime : Int.gcd p q = 1) :
    ∀ y : ℝ, ∃ n < q, ∃ m : ℤ, |n * α - m - y| ≤ 1 / q + δ := by
      -- Let $\beta = p/q$. Since $|q\alpha - p| < \delta$, we have $|\alpha - \beta| < \delta/q$.
      set β : ℝ := p / q
      have h_beta : |α - β| < δ / q := by
        rw [ abs_lt ] at * ; constructor <;> nlinarith [ show ( q : ℝ ) > 0 by positivity, mul_div_cancel₀ ( p : ℝ ) ( by positivity : ( q : ℝ ) ≠ 0 ), mul_div_cancel₀ ( δ : ℝ ) ( by positivity : ( q : ℝ ) ≠ 0 ) ] ;
      -- The set $\{ (n p) \pmod q \mid n < q \}$ is $\{0, \dots, q-1\}$ because $\gcd(p, q) = 1$.
      have h_set : ∀ k : ℤ, ∃ n < q, ∃ m : ℤ, n * p = k + m * q := by
        -- By Bezout's identity, since $\gcd(p, q) = 1$, there exist integers $x$ and $y$ such that $px + qy = 1$.
        obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, p * x + q * y = 1 := by
          have := Int.gcd_eq_gcd_ab p q; aesop;
        intro k
        obtain ⟨n, m, hnm⟩ : ∃ n m : ℤ, n * p = k + m * q := by
          exact ⟨ k * x, -k * y, by linear_combination' k * hxy ⟩;
        refine' ⟨ Int.toNat ( n % q ), _, _ ⟩;
        · linarith [ Int.emod_lt_of_pos n ( by positivity : 0 < ( q : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg n ( by positivity : ( q : ℤ ) ≠ 0 ) ) ];
        · use m - (n / q) * p;
          rw [ Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by positivity ) ) ] ; rw [ Int.emod_def ] ; linarith [ Int.emod_add_mul_ediv n q ] ;
      -- For any $y \in \mathbb{R}$, let $y' = \{y\}$. There exists $k \in \{0, \dots, q-1\}$ such that $|y' - k/q| \le 1/(2q)$.
      intros y
      obtain ⟨k, hk⟩ : ∃ k : ℤ, |y - k / q| ≤ 1 / (2 * q) := by
        use ⌊y * q + 1 / 2⌋;
        rw [ abs_le ] ; constructor <;> nlinarith [ Int.floor_le ( y * q + 1 / 2 ), Int.lt_floor_add_one ( y * q + 1 / 2 ), show ( q : ℝ ) > 0 by positivity, mul_div_cancel₀ ( ⌊y * q + 1 / 2⌋ : ℝ ) ( by positivity : ( q : ℝ ) ≠ 0 ), mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 2 * q : ℝ ) ≠ 0 ) ] ;
      obtain ⟨ n, hn₁, m, hm ⟩ := h_set k;
      refine' ⟨ n, hn₁, m, _ ⟩;
      -- Then $|n \alpha - \lfloor n \beta \rfloor - \lfloor y \rfloor - y| \le |n \alpha - n \beta| + |\{n \beta\} - \{y\}| < n (\delta/q) + 1/(2q) < \delta + 1/q$.
      have h_bound : |(n : ℝ) * α - (n : ℝ) * β| < δ := by
        rw [ ← mul_sub, abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ n ) ];
        exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hn₁.le ) ( abs_nonneg _ ) ) ( by rw [ lt_div_iff₀ ( by positivity ) ] at h_beta; nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast ] );
      -- Since $n * p = k + m * q$, we have $n * β = k / q + m$.
      have h_n_beta : (n : ℝ) * β = k / q + m := by
        rw [ mul_div, div_add', div_eq_div_iff ] <;> norm_cast at * <;> aesop;
      exact abs_le.mpr ⟨ by ring_nf at *; linarith [ abs_le.mp hk, abs_lt.mp h_bound ], by ring_nf at *; linarith [ abs_le.mp hk, abs_lt.mp h_bound ] ⟩

lemma specific_bound : 1 / 990 + |990 * (1 / P_val) - 7| < w_val / (2 * P_val) := by
  rw [ abs_of_nonneg, one_div_P_val ] ; ring_nf ; norm_num;
  · unfold P_val w_val; norm_num; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_inv_cancel₀ ( ne_of_gt <| Real.sqrt_pos.mpr zero_lt_two ) ] ;
  · unfold P_val; ring_nf; norm_num [ Real.sqrt_nonneg ] ;
    rw [ ← div_eq_inv_mul, le_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

/-
An explicit version of `exists_k_dense` specialized to `P_val,w_val`:
it produces density with the **fixed** `k = 254701`.
-/
lemma exists_k_dense_P_val_explicit :
    ∀ y : ℝ, ∃ n < k_val, ∃ m : ℤ,
      |n * (1 / P_val) - m - y| < w_val / (2 * P_val) := by
  -- By `specific_bound`, we have $1/990 + E < w_{val} / (2 * P_{val})$.
  have h_specific_bound : 1 / 990 + |(990 : ℝ) * (1 / P_val) - 7| < w_val / (2 * P_val) := by
    exact specific_bound;
  -- Choose $\delta$ strictly between $E$ and $w_{val} / (2 * P_{val}) - 1/990$.
  obtain ⟨δ, hδ₁, hδ₂⟩ : ∃ δ : ℝ, |(990 : ℝ) * (1 / P_val) - 7| < δ ∧ δ < w_val / (2 * P_val) - 1 / 990 := by
    exact exists_between ( by linarith );
  -- Apply `dense_of_approx` with $q=990$ and $p=7$.
  have h_dense : ∀ y : ℝ, ∃ n : ℕ, n < 990 ∧ ∃ m : ℤ, |(n : ℝ) / P_val - m - y| ≤ 1 / 990 + δ := by
    convert dense_of_approx 990 7 ( 1 / P_val ) δ _ _ _ using 1 <;> norm_num at * ; aesop;
    exact hδ₁;
  intro y; obtain ⟨ n, hn₁, m, hm ⟩ := h_dense y; use n; refine' ⟨ _, m, _ ⟩ <;> norm_num [ abs_le ] at *;
  · exact hn₁.trans_le ( by decide );
  · cases abs_cases ( ( n : ℝ ) / P_val - m - y ) <;> ring_nf at * <;> linarith

/--
Explicit `hk` used in the final combinatorial step:
for every `x` we find `n < 254701` landing in a red strip.
-/
lemma exists_k_of_irrational_P_val_w_val_explicit :
  (∀ x : ℝ, ∃ n < k_val, ∃ m : ℤ,
      0 ≤ x + n - m * P_val ∧ x + n - m * P_val ≤ w_val) := by
  intro x
  obtain ⟨n, hn_lt, m, hm⟩ := exists_k_dense_P_val_explicit (-x / (100 * Real.sqrt 2) + (1 / 4) / (100 * Real.sqrt 2));
  norm_num [ abs_lt, P_val, w_val ] at hm ⊢;
  -- Let's simplify the inequality obtained from `hm`.
  field_simp at hm ⊢;
  exact ⟨ n, hn_lt, m, by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ], by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ⟩

/-- Explicit final statement: the specific `k` produced is `254701`. -/
theorem erdos_188.k254701_mem : (254701 : ℕ) ∈ s := by
  use BlueSet;
  constructor;
  · convert red_dist_ne_one using 1;
    exact Set.ext fun x => by unfold BlueSet; aesop;
  · rintro ⟨ bs, hbs₁, s, hbs₂ ⟩;
    -- By definition of $IsAPOfLengthWith$, there exists some $x$ such that $s + x \cdot 1 \in bs$ for all $x \in \{0, 1, ..., 254700\}$.
    obtain ⟨x, hx⟩ : ∃ x : ℕ, x < 254701 ∧ is_red_point (s + x * 1) := by
      convert exists_k_of_irrational_P_val_w_val_explicit ( s.re - f_map s.im ) using 1;
      ext; simp [is_red_point];
      constructor <;> rintro ⟨ h₁, m, hm₁, hm₂ ⟩ <;> exact ⟨ h₁, m, by linarith, by linarith ⟩;
    cases hbs₂ ; aesop

/--
Old and new problems and results in combinatorial number theory by Erdős & Graham (Page 14, 15):

It has been shown that there is a large $M$ so that it is possible to partition $\mathbb{E}^2$ into
two sets $A$ and $B$ so that $A$ contains no pair of points with distance 1 and $B$ contains no A.P.
of length $M$.
-/
theorem erdos_188.nonempty : s.Nonempty :=
  ⟨254701, erdos_188.k254701_mem⟩

#print axioms erdos_188.nonempty
-- 'Erdos188.erdos_188.nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos188
