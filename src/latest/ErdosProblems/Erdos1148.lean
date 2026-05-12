import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Lemma 2.1: Dictionary between ternary representations and discriminant points.
If b^2 - 4ac = 4n, b is even, and a, c have the same parity, then x=(a-c)/2,
y=b/2, z=(a+c)/2 are integers satisfying x^2+y^2-z^2=n.
-/
lemma lemma_dictionary (n : ℤ) (a b c : ℤ) (h_eq : b^2 - 4 * a * c = 4 * n)
    (hb : b % 2 = 0) (hac : a % 2 = c % 2) :
    ((a - c) / 2) ^ 2 + (b / 2) ^ 2 - ((a + c) / 2) ^ 2 = n := by
  have h4 : 4 * (((a - c) / 2) ^ 2 + (b / 2) ^ 2 - ((a + c) / 2) ^ 2) = 4 * n := by
    have hx : a - c = 2 * ((a - c) / 2) := by
      have : (a - c) % 2 = 0 := by omega
      omega
    have hy : b = 2 * (b / 2) := by omega
    have hz : a + c = 2 * ((a + c) / 2) := by
      have : (a + c) % 2 = 0 := by omega
      omega
    calc
      4 * (((a - c) / 2) ^ 2 + (b / 2) ^ 2 - ((a + c) / 2) ^ 2)
        = (2 * ((a - c) / 2)) ^ 2 + (2 * (b / 2)) ^ 2 - (2 * ((a + c) / 2)) ^ 2 := by ring
      _ = (a - c) ^ 2 + b ^ 2 - (a + c) ^ 2 := by rw [← hx, ← hy, ← hz]
      _ = b ^ 2 - 4 * a * c := by ring
      _ = 4 * n := h_eq
  exact mul_left_cancel₀ (by decide) h4

/-
Definition of R*_disc(d) from the paper.
-/
def R_star_disc (d : ℤ) : Set (ℤ × ℤ × ℤ) :=
  { t | t.2.1 ^ 2 - 4 * t.1 * t.2.2 = d ∧ Int.gcd t.1 (Int.gcd t.2.1 t.2.2) = 1 }

/-
Definition of V_disc,+1(R) from the paper.
-/
def V_disc_plus_1 : Set (ℝ × ℝ × ℝ) :=
  { t | t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 1 }

/-
Definition of Omega_strict and proof that it is non-empty.
-/
def Omega_strict : Set (ℝ × ℝ × ℝ) :=
  { t | t ∈ V_disc_plus_1 ∧ |t.1 - t.2.2| < 1 ∧ |t.2.1| < 1 ∧ |t.1 + t.2.2| < 1 }

theorem Omega_strict_nonempty : Omega_strict.Nonempty := by
  use (-3/8, 1/2, 1/2)
  dsimp [Omega_strict, V_disc_plus_1]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-
Projection to hyperboloid.
-/
noncomputable def project_to_hyperboloid (n : ℤ) (t : ℤ × ℤ × ℤ) : ℝ × ℝ × ℝ :=
  let s := Real.sqrt (4 * (n : ℝ))
  ((t.1 : ℝ) / s, (t.2.1 : ℝ) / s, (t.2.2 : ℝ) / s)

/-
Statement of Duke's Theorem adapted for Problem 1148.
-/
def DukeTheoremStatement : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n ≥ N →
  ∃ t ∈ R_star_disc (4 * n),
    project_to_hyperboloid n t ∈ Omega_strict ∧
    t.1 % 2 = t.2.2 % 2

/-
Main Theorem: Assuming Duke's Theorem, every sufficiently large integer n
can be written as x^2 + y^2 - z^2 with max(x^2, y^2, z^2) <= n.
-/
theorem erdos_problem_1148 (h_duke : DukeTheoremStatement) :
  ∃ N : ℤ, ∀ n : ℤ, n ≥ N → ∃ x y z : ℤ, n = x^2 + y^2 - z^2 ∧ max (x^2) (max (y^2) (z^2)) ≤ n := by
  rcases h_duke with ⟨N, hN⟩
  use max N 1
  intro n hn
  have hnN : n ≥ N := le_trans (le_max_left N 1) hn
  have hn1 : n ≥ 1 := le_trans (le_max_right N 1) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos

  rcases hN n hnN with ⟨⟨a, b, c⟩, ht_disc, ht_omega, ht_parity⟩
  -- Reduce (a, b, c).1 → a, (a, b, c).2.2 → c, etc. so omega doesn't see extra division terms
  dsimp at ht_disc ht_parity

  let x := (a - c) / 2
  let y := b / 2
  let z := (a + c) / 2

  use x, y, z

  have h_eq : b ^ 2 - 4 * a * c = 4 * n := ht_disc.1

  have hb_even : b % 2 = 0 := by
    have h_parity : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases h_parity with h0 | h1
    · exact h0
    · exfalso
      have hk : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
      rcases hk with ⟨k, hk⟩
      have h_eq2 : 4 * (k ^ 2 + k - a * c - n) = -1 := by
        calc 4 * (k ^ 2 + k - a * c - n)
            = (2 * k + 1) ^ 2 - 4 * a * c - 4 * n - 1 := by ring
          _ = b ^ 2 - 4 * a * c - 4 * n - 1 := by rw [hk]
          _ = 4 * n - 4 * n - 1 := by rw [h_eq]
          _ = -1 := by ring
      generalize k ^ 2 + k - a * c - n = X at h_eq2
      omega

  -- KEY: Prove the 2*w relationships BEFORE h_n, so omega never sees x^2, y^2, z^2
  have hx_rel : a - c = 2 * x := by
    have : (a - c) % 2 = 0 := by omega
    change a - c = 2 * ((a - c) / 2)
    omega
  have hy_rel : b = 2 * y := by
    change b = 2 * (b / 2)
    omega
  have hz_rel : a + c = 2 * z := by
    have : (a + c) % 2 = 0 := by omega
    change a + c = 2 * ((a + c) / 2)
    omega

  have h_n : x ^ 2 + y ^ 2 - z ^ 2 = n := by
    exact lemma_dictionary n a b c h_eq hb_even ht_parity

  refine ⟨h_n.symm, ?_⟩

  have hs : Real.sqrt (4 * (n : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
    calc Real.sqrt (4 * (n : ℝ))
        = Real.sqrt 4 * Real.sqrt (n : ℝ) := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (n : ℝ)
      _ = 2 * Real.sqrt (n : ℝ) := by norm_num

  dsimp [Omega_strict, project_to_hyperboloid] at ht_omega

  have h_omega1 : |(a : ℝ) / (2 * Real.sqrt (n : ℝ)) - (c : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by
    have h := ht_omega.2.1
    rwa [hs] at h

  have h_omega2 : |(b : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by
    have h := ht_omega.2.2.1
    rwa [hs] at h

  have h_omega3 : |(a : ℝ) / (2 * Real.sqrt (n : ℝ)) + (c : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by
    have h := ht_omega.2.2.2
    rwa [hs] at h

  have sqrt_pos : 0 < 2 * Real.sqrt (n : ℝ) := by positivity

  have h_bound1 : |((a - c : ℤ) : ℝ)| < 2 * Real.sqrt (n : ℝ) := by
    have h_sub : (a : ℝ) / (2 * Real.sqrt (n : ℝ)) - (c : ℝ) / (2 * Real.sqrt (n : ℝ))
        = ((a - c : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ)) := by push_cast; ring
    have h_omega1' : |((a - c : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by rwa [← h_sub]
    rw [abs_div, abs_of_pos sqrt_pos, div_lt_iff₀ sqrt_pos] at h_omega1'
    linarith

  have h_bound2 : |((b : ℤ) : ℝ)| < 2 * Real.sqrt (n : ℝ) := by
    have h_b : (b : ℝ) / (2 * Real.sqrt (n : ℝ))
        = ((b : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ)) := by rfl
    have h_omega2' : |((b : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by rwa [← h_b]
    rw [abs_div, abs_of_pos sqrt_pos, div_lt_iff₀ sqrt_pos] at h_omega2'
    linarith

  have h_bound3 : |((a + c : ℤ) : ℝ)| < 2 * Real.sqrt (n : ℝ) := by
    have h_add : (a : ℝ) / (2 * Real.sqrt (n : ℝ)) + (c : ℝ) / (2 * Real.sqrt (n : ℝ))
        = ((a + c : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ)) := by push_cast; ring
    have h_omega3' : |((a + c : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by rwa [← h_add]
    rw [abs_div, abs_of_pos sqrt_pos, div_lt_iff₀ sqrt_pos] at h_omega3'
    linarith

  have bound_helper : ∀ (w : ℤ), |(2 * w : ℝ)| < 2 * Real.sqrt (n : ℝ) → (w ^ 2 : ℤ) ≤ n := by
    intro w hw
    have hw2 : 2 * |(w : ℝ)| < 2 * Real.sqrt (n : ℝ) := by
      calc 2 * |(w : ℝ)| = |(2 : ℝ)| * |(w : ℝ)| := by norm_num
           _ = |(2 * w : ℝ)| := by rw [← abs_mul]
           _ < 2 * Real.sqrt (n : ℝ) := hw
    have hw3 : |(w : ℝ)| < Real.sqrt (n : ℝ) := by linarith
    have hdiff : 0 < Real.sqrt (n : ℝ) - |(w : ℝ)| := sub_pos.mpr hw3
    have hsum_pos : 0 < Real.sqrt (n : ℝ) + |(w : ℝ)| := by
      have : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn_pos)
      positivity
    have hprod : 0 < (Real.sqrt (n : ℝ)) ^ 2 - |(w : ℝ)| ^ 2 := by
      calc 0
          < (Real.sqrt (n : ℝ) - |(w : ℝ)|) * (Real.sqrt (n : ℝ) + |(w : ℝ)|) := mul_pos hdiff hsum_pos
        _ = (Real.sqrt (n : ℝ)) ^ 2 - |(w : ℝ)| ^ 2 := by ring
    have h2 : |(w : ℝ)| ^ 2 < (Real.sqrt (n : ℝ)) ^ 2 := by linarith
    rw [sq_abs, Real.sq_sqrt hn_nonneg] at h2
    exact_mod_cast le_of_lt h2

  have hx_bound : (x ^ 2 : ℤ) ≤ n := by
    apply bound_helper
    have : ((a - c : ℤ) : ℝ) = 2 * (x : ℝ) := by rw [hx_rel]; push_cast; ring
    rwa [this] at h_bound1

  have hy_bound : (y ^ 2 : ℤ) ≤ n := by
    apply bound_helper
    have : ((b : ℤ) : ℝ) = 2 * (y : ℝ) := by rw [hy_rel]; push_cast; ring
    rwa [this] at h_bound2

  have hz_bound : (z ^ 2 : ℤ) ≤ n := by
    apply bound_helper
    have : ((a + c : ℤ) : ℝ) = 2 * (z : ℝ) := by rw [hz_rel]; push_cast; ring
    rwa [this] at h_bound3

  exact max_le hx_bound (max_le hy_bound hz_bound)

end
