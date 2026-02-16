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

noncomputable def P_val : ℝ := ((593 : ℝ) / 100) * Real.sqrt 2

noncomputable def w_val : ℝ := (21 : ℝ) / 25

/-
f_map(y) is 2 * floor(2y). This is a step function used to define the vertical shifts of the red strips.
-/
noncomputable def f_map (y : ℝ) : ℝ := 2 * Int.floor (2 * y)

/-
A point z is red if its real part falls into one of the intervals [f(y) + nP, f(y) + nP + w].
-/
def is_red_point (z : ℂ) : Prop :=
  ∃ n : ℤ, 0 ≤ z.re - (f_map z.im + P_val * n) ∧ z.re - (f_map z.im + P_val * n) ≤ w_val

lemma red_dist_ne_one : {z : ℂ | is_red_point z}.Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) := by
  intro z hz w hw hne hdist
  obtain ⟨n₁, hn₁⟩ := hz
  obtain ⟨n₂, hn₂⟩ := hw
  have h_diff : |(f_map z.im + P_val * n₁) - (f_map w.im + P_val * n₂)| ≤ 1 + 2 * w_val := by
    -- Since $|z - w| = 1$, we have $|z.re - w.re| \leq 1$.
    have h_diff_re : |z.re - w.re| ≤ 1 := by
      exact hdist ▸ Complex.abs_re_le_norm ( z - w );
    exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_diff_re ], by linarith [ abs_le.mp h_diff_re ] ⟩;
  -- Since $P_val$ is irrational, the term $P_val * (n₁ - n₂)$ can't be an integer unless $n₁ = n₂$. But if $n₁ = n₂$, then the difference between the y-coordinates would have to be even, which contradicts the assumption that the distance is 1.
  by_cases h_eq : n₁ = n₂;
  · simp_all +decide [ dist_eq_norm, Complex.normSq, Complex.norm_def ];
    unfold Erdos188.f_map at *;
    -- Since $⌊2 * z.im⌋$ and $⌊2 * w.im⌋$ are integers, their difference must be an integer. The only integer between $-1$ and $1$ is $0$, so $⌊2 * z.im⌋ = ⌊2 * w.im⌋$.
    have h_floor_eq : ⌊2 * z.im⌋ = ⌊2 * w.im⌋ := by
      exact Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ abs_le.mp h_diff, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( Erdos188.w_val : ℝ ) = 21 / 25 by exact rfl ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ abs_le.mp h_diff, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( Erdos188.w_val : ℝ ) = 21 / 25 by exact rfl ] );
    -- Since $z.im$ and $w.im$ are in the same interval between two consecutive integers, their difference must be less than 1.
    have h_diff_lt_1 : |z.im - w.im| < 1 / 2 := by
      rw [ Int.floor_eq_iff ] at h_floor_eq;
      exact abs_sub_lt_iff.mpr ⟨ by linarith [ Int.floor_le ( 2 * w.im ), Int.lt_floor_add_one ( 2 * w.im ) ], by linarith [ Int.floor_le ( 2 * w.im ), Int.lt_floor_add_one ( 2 * w.im ) ] ⟩;
    -- Since $z.re$ and $w.re$ are in the same interval between two consecutive integers, their difference must be less than 1.
    have h_diff_re_lt_1 : |z.re - w.re| < 1 / 2 := by
      norm_num [ Erdos188.w_val ] at *;
      exact abs_lt.mpr ⟨ by nlinarith only [ abs_lt.mp h_diff_lt_1, hdist, hn₁, hn₂, show ( ⌊2 * z.im⌋ : ℝ ) = ⌊2 * w.im⌋ by exact_mod_cast h_floor_eq ], by nlinarith only [ abs_lt.mp h_diff_lt_1, hdist, hn₁, hn₂, show ( ⌊2 * z.im⌋ : ℝ ) = ⌊2 * w.im⌋ by exact_mod_cast h_floor_eq ] ⟩;
    nlinarith only [ abs_lt.mp h_diff_lt_1, abs_lt.mp h_diff_re_lt_1, hdist ];
  · -- Since $P_val$ is irrational, the term $P_val * (n₁ - n₂)$ can't be an integer unless $n₁ = n₂$. But if $n₁ \neq n₂$, then the difference between the y-coordinates would have to be even, which contradicts the assumption that the distance is 1. Hence, $n₁$ must equal $n₂$.
    have h_diff_even : |P_val * (n₁ - n₂)| ≤ 1 + 2 * w_val + 4 := by
      have h_diff_even : |f_map z.im - f_map w.im| ≤ 4 := by
        have h_diff_even : |z.im - w.im| ≤ 1 := by
          exact le_trans ( Complex.abs_im_le_norm ( z - w ) ) ( by simpa [ dist_eq_norm ] using hdist.le );
        norm_num [ Erdos188.f_map ] at *;
        exact abs_le.mpr ⟨ by linarith [ show ( ⌊2 * z.im⌋ : ℝ ) ≥ ⌊2 * w.im⌋ - 2 by exact_mod_cast Int.le_floor.mpr ( by norm_num; linarith [ abs_le.mp h_diff_even, Int.floor_le ( 2 * w.im ), Int.lt_floor_add_one ( 2 * w.im ) ] ) ], by linarith [ show ( ⌊2 * z.im⌋ : ℝ ) ≤ ⌊2 * w.im⌋ + 2 by exact_mod_cast Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; linarith [ abs_le.mp h_diff_even, Int.floor_le ( 2 * w.im ), Int.lt_floor_add_one ( 2 * w.im ) ] ) ) ] ⟩;
      exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_diff, abs_le.mp h_diff_even ], by linarith [ abs_le.mp h_diff, abs_le.mp h_diff_even ] ⟩;
    norm_num [ abs_le, P_val, w_val ] at *;
    rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ) ] at h_diff_even;
    exact h_eq ( Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; cases abs_cases ( ( n₁ : ℝ ) - n₂ ) <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; cases abs_cases ( ( n₁ : ℝ ) - n₂ ) <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) )

/-- The explicit value of `k` produced by the parameter choices in this file. -/
def k_val : ℕ := 177

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

theorem sqrt2_bounds_17579_17621: (17579 : ℝ) / 12453 < Real.sqrt 2 ∧ Real.sqrt 2 < (17621 : ℝ) / 12453 := by
  constructor
  · have h0 : (0 : ℝ) ≤ (17579 : ℝ) / 12453 := by
      positivity
    have hsq : ((17579 : ℝ) / 12453) ^ 2 < (2 : ℝ) := by
      norm_num
    exact (Real.lt_sqrt h0).2 hsq
  · have h0 : (0 : ℝ) ≤ (17621 : ℝ) / 12453 := by
      positivity
    have hsq : (2 : ℝ) < ((17621 : ℝ) / 12453) ^ 2 := by
      norm_num
    exact (Real.sqrt_lt (by positivity : (0 : ℝ) ≤ (2 : ℝ)) h0).2 hsq

theorem abs_12453_sqrt2_sub_17600_lt_21: |(12453 : ℝ) * Real.sqrt 2 - 17600| < 21 := by
  classical
  rcases sqrt2_bounds_17579_17621 with ⟨hL, hU⟩
  have hpos : (0 : ℝ) < (12453 : ℝ) := by
    norm_num
  have h17579 : (17579 : ℝ) < (12453 : ℝ) * Real.sqrt 2 := by
    have h := mul_lt_mul_of_pos_left hL hpos
    -- h : (12453:ℝ) * ((17579:ℝ)/12453) < (12453:ℝ) * Real.sqrt 2
    -- simplify left side
    have h' : (12453 : ℝ) * ((17579 : ℝ) / 12453) = (17579 : ℝ) := by
      field_simp
    -- rewrite using h'
    simpa [h'] using h
  have h17621 : (12453 : ℝ) * Real.sqrt 2 < (17621 : ℝ) := by
    have h := mul_lt_mul_of_pos_left hU hpos
    -- h : (12453:ℝ) * Real.sqrt 2 < (12453:ℝ) * ((17621:ℝ)/12453)
    have h' : (12453 : ℝ) * ((17621 : ℝ) / 12453) = (17621 : ℝ) := by
      field_simp
    simpa [h'] using h
  have hlow : (-21 : ℝ) < (12453 : ℝ) * Real.sqrt 2 - 17600 := by
    linarith
  have hupp : (12453 : ℝ) * Real.sqrt 2 - 17600 < (21 : ℝ) := by
    linarith
  exact (abs_lt).2 ⟨hlow, hupp⟩

theorem approx_q176_p21: |(176 : ℝ) * (1 / P_val) - 21| < w_val / (4 * P_val) := by
  have hP : 0 < P_val := by
    simp [P_val]
  have hPne : (P_val : ℝ) ≠ 0 := ne_of_gt hP
  have h_main : |(176 : ℝ) - 21 * P_val| < w_val / 4 := by
    simp [P_val, w_val]
    ring_nf
    have h := abs_12453_sqrt2_sub_17600_lt_21
    have h1 : |(12453 : ℝ) * Real.sqrt 2 - 17600| / (100 : ℝ) < (21 : ℝ) / 100 := by
      exact div_lt_div_of_pos_right h (by norm_num)
    have h2 : |((12453 : ℝ) * Real.sqrt 2 - 17600) / (100 : ℝ)| < (21 : ℝ) / 100 := by
      simpa [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < (100 : ℝ))] using h1
    have hx : (176 + Real.sqrt 2 * (-12453 / 100) : ℝ) = -(((12453 : ℝ) * Real.sqrt 2 - 17600) / (100 : ℝ)) := by
      ring_nf
    have : |(176 + Real.sqrt 2 * (-12453 / 100) : ℝ)| < (21 : ℝ) / 100 := by
      have : |-( ((12453 : ℝ) * Real.sqrt 2 - 17600) / (100 : ℝ))| < (21 : ℝ) / 100 := by
        simpa using h2
      simpa [hx] using (by simpa using this)
    simpa using this
  have hrewrite : (176 : ℝ) * (1 / P_val) - 21 = (176 - 21 * P_val) / P_val := by
    field_simp [hPne]
  have habs : |(176 : ℝ) * (1 / P_val) - 21| = |(176 - 21 * P_val) / P_val| := by
    simpa using congrArg (fun x : ℝ => |x|) hrewrite
  have habs2 : |((176 : ℝ) - 21 * P_val) / P_val| = |(176 : ℝ) - 21 * P_val| / P_val := by
    simpa [abs_of_pos hP] using (abs_div ((176 : ℝ) - 21 * P_val) P_val)
  have hdiv : |(176 : ℝ) - 21 * P_val| / P_val < (w_val / 4) / P_val := by
    exact div_lt_div_of_pos_right h_main hP
  have hgoal' : |(176 : ℝ) * (1 / P_val) - 21| < (w_val / 4) / P_val := by
    -- rewrite left using habs and habs2, then use hdiv
    --
    -- from habs: |176*(1/P_val)-21| = |(176-21*P_val)/P_val|
    -- then habs2 rewrites |(176-21*P_val)/P_val|
    --
    calc
      |(176 : ℝ) * (1 / P_val) - 21|
          = |(176 - 21 * P_val) / P_val| := habs
      _ = |(176 : ℝ) - 21 * P_val| / P_val := by
            -- apply habs2
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using habs2
      _ < (w_val / 4) / P_val := hdiv
  -- rewrite rhs
  simpa [div_mul_eq_div_div] using hgoal'


theorem w_div_2P_simp: w_val / (2 * P_val) = (42 : ℝ) / ((593 : ℝ) * Real.sqrt 2) := by
  simp [w_val, P_val]
  field_simp
  ring_nf

theorem w_div_4P_simp: w_val / (4 * P_val) = (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) := by
  -- expand the definitions of `w_val` and `P_val`
  have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h593 : (593 : ℝ) ≠ 0 := by norm_num
  simp [w_val, P_val]
  field_simp [hsqrt, h593]
  ring_nf

theorem dense_bound_q176: (1 / (176 : ℝ)) + w_val / (4 * P_val) < w_val / (2 * P_val) := by
  -- Rewrite the goal using the given simp lemmas
  have hgoal : (1 / (176 : ℝ)) + (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) <
      (42 : ℝ) / ((593 : ℝ) * Real.sqrt 2) := by
    -- It suffices to show `1/176 < 21 / (593*sqrt 2)`
    have h176 : (1 / (176 : ℝ)) < (21 : ℝ) / (1186 : ℝ) := by
      norm_num
    have hsqrt2 : Real.sqrt (2 : ℝ) < (2 : ℝ) := by
      exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    have hden : (593 : ℝ) * Real.sqrt 2 < (1186 : ℝ) := by
      have htmp : (593 : ℝ) * Real.sqrt 2 < (593 : ℝ) * (2 : ℝ) :=
        mul_lt_mul_of_pos_left hsqrt2 (by norm_num)
      have hmul : (593 : ℝ) * (2 : ℝ) = (1186 : ℝ) := by
        norm_num
      simpa [hmul] using htmp
    have hpos : (0 : ℝ) < (593 : ℝ) * Real.sqrt 2 := by
      have h593pos : (0 : ℝ) < (593 : ℝ) := by
        norm_num
      have hsqrtpos : (0 : ℝ) < Real.sqrt (2 : ℝ) := by
        exact Real.sqrt_pos.2 (by norm_num)
      exact mul_pos h593pos hsqrtpos
    have hrecip : (1 : ℝ) / (1186 : ℝ) < (1 : ℝ) / ((593 : ℝ) * Real.sqrt 2) := by
      simpa using (one_div_lt_one_div_of_lt hpos hden)
    have h21recip : (21 : ℝ) / (1186 : ℝ) < (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) := by
      have hmul21 := mul_lt_mul_of_pos_left hrecip (by norm_num : (0 : ℝ) < (21 : ℝ))
      simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using hmul21
    have h1 : (1 / (176 : ℝ)) < (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) :=
      lt_trans h176 h21recip
    have hadd : (1 / (176 : ℝ)) + (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) <
        (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) + (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) :=
      add_lt_add_right h1 ((21 : ℝ) / ((593 : ℝ) * Real.sqrt 2))
    have hsum : (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) + (21 : ℝ) / ((593 : ℝ) * Real.sqrt 2) =
        (42 : ℝ) / ((593 : ℝ) * Real.sqrt 2) := by
      have hnum : (21 : ℝ) + (21 : ℝ) = (42 : ℝ) := by
        norm_num
      -- `add_div` gives `(a+b)/c = a/c + b/c`.
      have := (add_div (21 : ℝ) (21 : ℝ) ((593 : ℝ) * Real.sqrt 2)).symm
      -- this : 21/d + 21/d = (21+21)/d
      simpa [hnum] using this
    exact lt_of_lt_of_eq hadd hsum
  simpa [w_div_4P_simp, w_div_2P_simp] using hgoal

/-
An explicit version of `exists_k_dense` specialized to `P_val,w_val`.
-/
theorem exists_k_dense_P_val_explicit: ∀ y : ℝ, ∃ n < k_val, ∃ m : ℤ,
      |n * (1 / P_val) - m - y| < w_val / (2 * P_val) := by
  intro y
  classical
  have hqpos : (0 : ℕ) < 176 := by decide
  have hcop : Int.gcd (21 : ℤ) 176 = 1 := by decide
  have hden :=
    dense_of_approx 176 (21 : ℤ) (1 / P_val) (w_val / (4 * P_val))
      approx_q176_p21 hqpos hcop y
  rcases hden with ⟨n, hnlt, m, hnm⟩
  refine ⟨n, ?_, m, ?_⟩
  · have hn' : n < 177 := lt_trans hnlt (Nat.lt_succ_self 176)
    simpa [k_val] using hn'
  · exact lt_of_le_of_lt hnm dense_bound_q176

/--
Explicit `hk` used in the final combinatorial step.
-/
lemma exists_k_of_irrational_P_val_w_val_explicit :
  (∀ x : ℝ, ∃ n < k_val, ∃ m : ℤ,
      0 ≤ x + n - m * P_val ∧ x + n - m * P_val ≤ w_val) := by
  -- Apply the lemma with α = 1/P_val and w = w_val/(2P_val).
  have h_apply_lemma : ∀ x : ℝ, ∃ n < k_val, ∃ m : ℤ, |n * (1 / P_val) - m - x / P_val| < w_val / (2 * P_val) := by
    exact fun x => exists_k_dense_P_val_explicit ( x / Erdos188.P_val );
  intro x
  obtain ⟨ n, hn₁, m, hm ⟩ := h_apply_lemma ( -x + Erdos188.w_val / 2 );
  refine' ⟨ n, hn₁, m, _, _ ⟩ <;> ring_nf at hm ⊢;
  · norm_num [ Erdos188.P_val, Erdos188.w_val ] at *;
    nlinarith [ abs_lt.mp hm, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, inv_mul_cancel_left₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ) ( n : ℝ ), inv_mul_cancel_left₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ) ( m : ℝ ), inv_mul_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ) ];
  · norm_num [ Erdos188.P_val, Erdos188.w_val ] at *;
    nlinarith [ abs_lt.mp hm, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, inv_mul_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ), inv_pos.mpr ( Real.sqrt_pos.mpr zero_lt_two ), mul_inv_cancel_left₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ) x, mul_inv_cancel_left₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ) ( n : ℝ ), mul_inv_cancel_left₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ) ( m : ℝ ) ]

/-- Explicit final statement. -/
theorem erdos_188.k177_mem : (177 : ℕ) ∈ s := by
  -- Define the blue set as the complement of the red set.
  use {z : ℂ | ¬ is_red_point z};
  constructor;
  · convert red_dist_ne_one using 1;
    aesop;
  · rintro ⟨ bs, hbs₁, s, hbs₂ ⟩;
    obtain ⟨ hbs₂, hbs₃ ⟩ := hbs₂;
    simp_all +decide [ Set.subset_def ];
    contrapose! hbs₁;
    unfold Erdos188.is_red_point; norm_num [ Complex.ext_iff ] ; ring_nf;
    obtain ⟨ n, hn ⟩ := exists_k_of_irrational_P_val_w_val_explicit ( s.re - Erdos188.f_map s.im );
    exact ⟨ n, hn.1, hn.2.choose, by linarith [ hn.2.choose_spec ], by linarith [ hn.2.choose_spec ] ⟩

/--
Old and new problems and results in combinatorial number theory by Erdős & Graham (Page 14, 15):

It has been shown that there is a large $M$ so that it is possible to partition $\mathbb{E}^2$ into
two sets $A$ and $B$ so that $A$ contains no pair of points with distance 1 and $B$ contains no A.P.
of length $M$.
-/
theorem erdos_188.nonempty : s.Nonempty :=
  ⟨177, erdos_188.k177_mem⟩

#print axioms erdos_188.nonempty
-- 'Erdos188.erdos_188.nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos188
