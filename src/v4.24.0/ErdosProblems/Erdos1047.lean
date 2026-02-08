/-

This is a Lean formalization of a solution to Erdős Problem 1047.
https://www.erdosproblems.com/forum/thread/1047

The original proof was found by: Pommerenke; also Goodman; also a
referee

[Po61] Pommerenke, Ch., On metric properties of complex
polynomials. Michigan Math. J. (1961), 97-115.

[Go66] Goodman, A. W., On the convexity of the level curves of a
polynomial. Proc. Amer. Math. Soc. (1966), 358--361.


Aristotle gave this proof given only the *statement* of the result
(informally).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We construct a polynomial $f(z) = z^6 - z$ and choose $c = 0.582$. We show that $f$ is monic, has 6 distinct roots, and the sublevel set $\{z : |f(z)| \le c\}$ has 6 distinct connected components, one for each root. We further show that the component containing 0 is not convex. This confirms the existence of such a polynomial and constant.
-/

import Mathlib

namespace Erdos1047

/-
Let $f(z) = z^6 - z$.
-/
noncomputable def f : Polynomial ℂ := Polynomial.X ^ 6 - Polynomial.X

/-
Let $c = 0.57$.
-/
def c : ℝ := 0.57

/-
The roots of $f$ are distinct.
-/
theorem f_roots_distinct : (f.roots).Nodup := by
  -- The roots of $f$ are $0$ and the 5th roots of unity, which are all distinct.
  have h_roots : f.roots = {0} + Multiset.map (fun ζ => ζ) (Polynomial.roots (Polynomial.X ^ 5 - 1 : Polynomial ℂ)) := by
    rw [ show f = Polynomial.X * ( Polynomial.X ^ 5 - 1 ) by unfold f; ring, Polynomial.roots_mul ] <;> norm_num;
    exact ne_of_apply_ne ( Polynomial.eval 2 ) ( by norm_num );
  -- The polynomial $X^5 - 1$ has roots that are the 5th roots of unity, which are all distinct.
  have h_roots_X5_minus_1 : Multiset.Nodup (Polynomial.roots (Polynomial.X ^ 5 - 1 : Polynomial ℂ)) := by
    convert Polynomial.nodup_roots ?_ using 1;
    refine' Polynomial.separable_X_pow_sub_C _ _ _ <;> norm_num;
  aesop

/-
The sublevel set $\{z : |f(z)| \le c\}$.
-/
def sublevelSet : Set ℂ := {z | ‖f.eval z‖ ≤ c}

/-
Let `roots` be the set of roots of $f$.
-/
noncomputable def roots : Finset ℂ := f.roots.toFinset

/-
The set of roots has cardinality 6.
-/
lemma roots_card : roots.card = 6 := by
  -- Since $f$ is a polynomial of degree 6 with distinct roots, the set of roots of $f$ has cardinality 6.
  have h_distinct_roots : Multiset.Nodup (Polynomial.roots (Polynomial.X ^ 6 - Polynomial.X) : Multiset ℂ) := by
    convert f_roots_distinct;
  -- Since $f$ is a polynomial of degree 6 with distinct roots, the set of roots of $f$ has cardinality 6. Use this fact.
  have h_card : Multiset.card (Polynomial.roots (Polynomial.X ^ 6 - Polynomial.X : Polynomial ℂ)) = 6 := by
    -- Since $f$ is a polynomial of degree 6 with distinct roots, the set of roots of $f$ has cardinality 6. Use this fact to conclude the proof.
    have h_card : Multiset.card (Polynomial.roots (Polynomial.X ^ 6 - Polynomial.X : Polynomial ℂ)) = Polynomial.natDegree (Polynomial.X ^ 6 - Polynomial.X : Polynomial ℂ) := by
      -- Since $f$ is a polynomial of degree 6 with distinct roots, it splits into linear factors over the complex numbers.
      have h_splits : Polynomial.Splits (algebraMap ℂ ℂ) (Polynomial.X ^ 6 - Polynomial.X : Polynomial ℂ) := by
        exact IsAlgClosed.splits_domain (Polynomial.X ^ 6 - Polynomial.X);
      erw [ Polynomial.splits_iff_card_roots ] at h_splits ; aesop;
    erw [ h_card, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
  rw [ ← h_card, ← Multiset.toFinset_card_of_nodup h_distinct_roots ] ; aesop

/-
Let `components` be the set of connected components of the sublevel set containing the roots.
-/
open Classical

noncomputable def components : Finset (Set ℂ) := roots.image (fun z => connectedComponentIn sublevelSet z)

/-
The critical values of $f$ are strictly greater than $c'$.
-/
def c' : ℝ := 0.582

def sublevelSet' : Set ℂ := {z | ‖f.eval z‖ ≤ c'}

/-
The point $0.685$ is in the sublevel set defined by $c' = 0.582$.
-/
def r_test : ℝ := 0.685

/-
The midpoint `m_test` is not in the sublevel set `sublevelSet'`.
-/
noncomputable def m_test : ℂ := (r_test * (1 + Complex.exp (Complex.I * (2 * Real.pi / 5))) / 2)

set_option maxHeartbeats 0 in
lemma m_test_not_in_sublevelSet' : m_test ∉ sublevelSet' := by
  unfold m_test sublevelSet';
  unfold f c' r_test; norm_num [ Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im ] ; ring_nf; norm_num;
  norm_num [ ← Complex.exp_nat_mul, Complex.exp_re, Complex.exp_im ] ; ring_nf ; norm_num [ mul_div ] at *;
  norm_num [ ( by ring : Real.pi * 2 = 2 * Real.pi ), ( by ring : Real.pi * 4 / 5 = Real.pi - Real.pi / 5 ), ( by ring : Real.pi * 6 / 5 = Real.pi + Real.pi / 5 ), ( by ring : Real.pi * 8 / 5 = 2 * Real.pi - 2 * Real.pi / 5 ), ( by ring : Real.pi * 12 / 5 = 2 * Real.pi + 2 * Real.pi / 5 ), Real.cos_add, Real.sin_add ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
  rw [ Real.lt_sqrt ] <;> ring_nf <;> norm_num [ mul_div ] at *;
  rw [ show Real.pi * 2 / 5 = 2 * ( Real.pi / 5 ) by ring, Real.sin_two_mul, Real.cos_two_mul ] ; ring_nf ; norm_num [ mul_div ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at * ;
  rw [ Real.sin_sq, Real.cos_sq ] ; ring_nf ; norm_num [ mul_div ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at * ;
  rw [ show Real.pi * ( 2 / 5 ) = 2 * ( Real.pi / 5 ) by ring, Real.cos_two_mul ] ; norm_num ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
  nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), pow_pos ( Real.sqrt_pos.mpr ( show 0 < 5 by norm_num ) ) 3 ]

/-
The segment $[0, r_{test}]$ is contained in the sublevel set.
-/
lemma segment_in_sublevelSet' : segment ℝ 0 (r_test : ℂ) ⊆ sublevelSet' := by
  -- For any $t \in [0, 1]$, we have $|f(t r_{test})| \leq c'$.
  have h_le_c' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f.eval (t * (r_test : ℂ))‖ ≤ c' := by
    unfold f;
    norm_num [ Complex.norm_def, Complex.normSq ];
    norm_cast ; norm_num [ pow_succ ];
    intro t ht₁ ht₂; rw [ Real.sqrt_le_left ] <;> norm_num [ r_test, c' ] ; ring_nf ; norm_num [ ht₁, ht₂ ] ;
    nlinarith [ pow_nonneg ht₁ 2, pow_nonneg ht₁ 3, pow_nonneg ht₁ 4, pow_nonneg ht₁ 5, pow_nonneg ht₁ 6, pow_nonneg ht₁ 7, pow_nonneg ht₁ 8, pow_nonneg ht₁ 9, pow_nonneg ht₁ 10, pow_nonneg ht₁ 11, pow_nonneg ht₁ 12, mul_le_mul_of_nonneg_left ht₂ <| sq_nonneg <| t - 1 ];
  simp_all +decide [ segment_eq_image ];
  exact fun x hx => h_le_c' x hx.1 hx.2

/-
The modulus of $f$ is invariant under rotation by $2\pi/5$.
-/
lemma f_symmetry (z : ℂ) : ‖f.eval (z * Complex.exp (Complex.I * (2 * Real.pi / 5)))‖ = ‖f.eval z‖ := by
  rw [ show f = Polynomial.X ^ 6 - Polynomial.X from rfl ] ; norm_num [ mul_pow, ← Complex.exp_nat_mul ] ; ring_nf;
  rw [ show Complex.exp ( Complex.I * Real.pi * ( 12 / 5 ) ) = Complex.exp ( Complex.I * Real.pi * ( 2 / 5 ) ) by rw [ Complex.exp_eq_exp_iff_exists_int ] ; exact ⟨ 1, by ring ⟩ ] ; norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ] ; ring_nf;
  rw [ Real.sin_sq, Real.cos_sq ] ; ring_nf

/-
The segment connecting 0 to the rotated point is in the sublevel set.
-/
lemma segment_rotated_in_sublevelSet' : segment ℝ 0 (r_test * Complex.exp (Complex.I * (2 * Real.pi / 5))) ⊆ sublevelSet' := by
  have h_segment : segment ℝ 0 (r_test : ℂ) ⊆ sublevelSet' := by
    exact segment_in_sublevelSet';
  field_simp;
  intro x hx;
  -- By definition of $f_symmetry$, we know that $|f(z)| = |f(t r_{test})|$ for some $t \in [0, 1]$.
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = t * (r_test : ℂ) * Complex.exp (Complex.I * (2 * Real.pi / 5)) := by
    rw [ segment_eq_image ] at hx;
    field_simp;
    rcases hx with ⟨ t, ⟨ ht₀, ht₁ ⟩, rfl ⟩ ; exact ⟨ t, ht₀, ht₁, by simp +decide [ mul_assoc ] ⟩;
  have h_f_symmetry : ‖f.eval (t * (r_test : ℂ) * Complex.exp (Complex.I * (2 * Real.pi / 5)))‖ = ‖f.eval (t * (r_test : ℂ))‖ := by
    field_simp;
    convert f_symmetry ( t * r_test ) using 1 ; ring_nf;
  have h_f_le_c' : ‖f.eval (t * (r_test : ℂ))‖ ≤ c' := by
    convert h_segment ( show ( t : ℂ ) * r_test ∈ segment ℝ 0 ( r_test : ℂ ) from ?_ ) using 1;
    rw [ segment_eq_image ];
    exact ⟨ t, ⟨ ht.1, ht.2.1 ⟩, by norm_num ⟩;
  unfold sublevelSet'; aesop

/-
The roots of $f$ are contained in the sublevel set `sublevelSet'`.
-/
lemma roots_in_sublevelSet' (z : ℂ) (hz : z ∈ roots) : z ∈ sublevelSet' := by
  -- Since $z$ is a root of $f$, we have $f(z) = 0$, thus $|f(z)| = 0$.
  have h_fz_zero : f.eval z = 0 := by
    unfold roots at hz; aesop;
  exact Set.mem_setOf.mpr ( by rw [ h_fz_zero ] ; norm_num [ show c' = 0.582 by rfl ] )

/-
The set of roots has cardinality 6.
-/
noncomputable def roots' : Finset ℂ := {0} ∪ (Finset.univ.image (fun k : Fin 5 => Complex.exp (Complex.I * 2 * k * Real.pi / 5)))

/-
Let $C0$ be the connected component of 0 in the sublevel set.
-/
def C0 : Set ℂ := connectedComponentIn sublevelSet' 0

/-
$r_{test}$ is in the connected component C0.
-/
lemma r_test_in_C0 : (r_test : ℂ) ∈ C0 := by
  have h_segment : segment ℝ 0 (r_test : ℂ) ⊆ sublevelSet' := by
    exact segment_in_sublevelSet';
  -- The segment $[0, r_{test}]$ is connected and contained in `sublevelSet'`.
  have h_segment_connected : IsConnected (segment ℝ 0 (r_test : ℂ)) := by
    rw [ segment_eq_image ];
    exact ⟨ Set.Nonempty.image _ ⟨ 0, by norm_num ⟩, isPreconnected_Icc.image _ <| Continuous.continuousOn <| by continuity ⟩;
  -- Since $0 \in C0$ and $0 \in [0, r_{test}]$, the whole segment is in $C0$.
  have h_segment_in_C0 : segment ℝ 0 (r_test : ℂ) ⊆ C0 := by
    apply_rules [ IsPreconnected.subset_connectedComponentIn ];
    · exact h_segment_connected.isPreconnected;
    · exact left_mem_segment _ _ _;
  exact h_segment_in_C0 <| right_mem_segment _ _ _

/-
The rotated point is in the connected component C0.
-/
lemma rotated_in_C0 : (r_test * Complex.exp (Complex.I * (2 * Real.pi / 5))) ∈ C0 := by
  -- The segment connecting 0 to the rotated point is in the sublevel set.
  have segment_rotated_in_sublevelSet : (segment ℝ 0 (r_test * Complex.exp (Complex.I * (2 * Real.pi / 5)))) ⊆ sublevelSet' := by
    convert segment_rotated_in_sublevelSet' using 1;
  -- The segment connecting 0 to the rotated point is in the connected component C0.
  have segment_rotated_in_C0 : (segment ℝ 0 (r_test * Complex.exp (Complex.I * (2 * Real.pi / 5)))) ⊆ C0 := by
    apply_rules [ IsPreconnected.subset_connectedComponentIn ];
    · convert convex_segment _ _ |> Convex.isPreconnected using 1;
      · infer_instance;
      · infer_instance;
    · exact left_mem_segment _ _ _;
  exact segment_rotated_in_C0 <| right_mem_segment _ _ _

/-
The connected component of 0 is not convex.
-/
lemma C0_not_convex : ¬ Convex ℝ C0 := by
  -- By definition of convexity, if $C0$ is convex, then the segment $[r_{test}, z_{rot}]$ is in $C0$.
  by_contra h_convex
  have h_segment : segment ℝ (r_test : ℂ) (r_test * Complex.exp (Complex.I * (2 * Real.pi / 5))) ⊆ C0 := by
    exact h_convex.segment_subset ( by simpa using r_test_in_C0 ) ( by simpa using rotated_in_C0 );
  -- The midpoint $m_{test}$ is in this segment.
  have h_midpoint : m_test ∈ segment ℝ (r_test : ℂ) (r_test * Complex.exp (Complex.I * (2 * Real.pi / 5))) := by
    unfold m_test;
    norm_num [ segment_eq_image ];
    exact ⟨ 1 / 2, by norm_num, by push_cast; ring ⟩;
  -- So $m_{test} \in C0 \subseteq sublevelSet'$.
  have h_m_test_in_sublevelSet' : m_test ∈ sublevelSet' := by
    exact h_segment h_midpoint |> fun h => connectedComponentIn_subset _ _ h;
  exact m_test_not_in_sublevelSet' h_m_test_in_sublevelSet'

/-
On the circle $|z| = (1/6)^{1/5}$, $|f(z)| > c'$.
-/
lemma circle_separation' : ∀ z : ℂ, ‖z‖ = (1/6)^(1/5 : ℝ) → ‖f.eval z‖ > c' := by
  -- By definition of $f$, we know that $|f(z)| \geq (1/6)^{1/5} (5/6)$ for all $z$ with $|z| = (1/6)^{1/5}$.
  have h_min : ∀ z : ℂ, ‖z‖ = (1 / 6 : ℝ) ^ (1 / 5 : ℝ) → ‖Polynomial.eval z f‖ ≥ (1 / 6 : ℝ) ^ (1 / 5 : ℝ) * (5 / 6) := by
    -- Let's choose any $z$ such that $|z| = (1/6)^{1/5}$.
    intro z hz
    have h_fz : ‖z^6 - z‖ ≥ ‖z‖ * (1 - ‖z‖^5) := by
      have := norm_sub_le ( z ^ 6 - z ) ( z ^ 6 ) ; norm_num at *;
      linarith;
    convert h_fz using 1;
    · unfold f; norm_num;
    · rw [ hz, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
  refine fun z hz => lt_of_lt_of_le ?_ ( h_min z hz ) ; norm_num [ c' ];
  rw [ ← div_lt_iff₀ ] <;> norm_num [ Real.lt_rpow_iff_log_lt ];
  rw [ div_mul_eq_mul_div, lt_div_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ]

/-
On the rays where $z^5$ is negative real and $|z| \ge (1/6)^{1/5}$, $|f(z)| > c'$.
-/
lemma ray_separation' (r : ℝ) (θ : ℝ) (hr : r ≥ (1/6)^(1/5 : ℝ)) (hθ : 5 * θ = Real.pi) : ‖f.eval (r * Complex.exp (θ * Complex.I))‖ > c' := by
  -- Substitute $z = r * e^{iθ}$ into $f(z)$ and simplify.
  have h_sub : ‖f.eval (r * Complex.exp (θ * Complex.I))‖ = r * ‖r^5 * Complex.exp (5 * θ * Complex.I) - 1‖ := by
    unfold f; norm_num [ mul_pow, ← Complex.exp_nat_mul ] ; ring_nf; norm_num [ Complex.norm_def, Complex.normSq ] ;
    norm_cast; norm_num [ show θ * 6 = θ * 5 + θ by ring, show θ * 5 = Real.pi by linarith, Real.sin_add, Real.cos_add ] ; ring_nf;
    rw [ show ( θ : ℂ ) * Complex.I * 6 = ( θ : ℂ ) * Complex.I * 5 + ( θ : ℂ ) * Complex.I by ring, show ( θ : ℂ ) * Complex.I * 5 = ( θ : ℂ ) * Complex.I * 4 + ( θ : ℂ ) * Complex.I by ring, show ( θ : ℂ ) * Complex.I * 4 = ( θ : ℂ ) * Complex.I * 3 + ( θ : ℂ ) * Complex.I by ring, show ( θ : ℂ ) * Complex.I * 3 = ( θ : ℂ ) * Complex.I * 2 + ( θ : ℂ ) * Complex.I by ring, show ( θ : ℂ ) * Complex.I * 2 = ( θ : ℂ ) * Complex.I + ( θ : ℂ ) * Complex.I by ring ] ; norm_num [ Complex.exp_re, Complex.exp_im, Real.sin_add, Real.cos_add ] ; ring_nf;
    rw [ show Real.sin θ ^ 12 = ( Real.sin θ ^ 2 ) ^ 6 by ring, show Real.sin θ ^ 10 = ( Real.sin θ ^ 2 ) ^ 5 by ring, show Real.sin θ ^ 8 = ( Real.sin θ ^ 2 ) ^ 4 by ring, show Real.sin θ ^ 6 = ( Real.sin θ ^ 2 ) ^ 3 by ring, show Real.sin θ ^ 4 = ( Real.sin θ ^ 2 ) ^ 2 by ring, show Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 by rw [ Real.sin_sq ] ] ; ring_nf;
    rw [ show r ^ 2 - r ^ 7 * Real.cos θ * 10 + ( r ^ 7 * Real.cos θ ^ 3 * 40 - r ^ 7 * Real.cos θ ^ 5 * 32 ) + r ^ 12 = r ^ 2 * ( 1 - r ^ 5 * Real.cos θ * 10 + ( r ^ 5 * Real.cos θ ^ 3 * 40 - r ^ 5 * Real.cos θ ^ 5 * 32 ) + r ^ 10 ) by ring, Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by linarith [ Real.rpow_nonneg ( by norm_num : ( 0 : ℝ ) ≤ 1 / 6 ) ( 1 / 5 : ℝ ) ] ) ];
  -- Since $5\theta = \pi$, we have $\exp(5\theta i) = \exp(\pi i) = -1$.
  have h_exp : Complex.exp (5 * θ * Complex.I) = -1 := by
    exact Complex.exp_pi_mul_I ▸ mod_cast hθ ▸ rfl;
  rw [ h_sub, h_exp ] ; norm_cast ; norm_num [ c' ];
  rw [ abs_of_nonpos ] <;> norm_num at *;
  · -- Substitute $r \geq (1/6)^{1/5}$ into the inequality.
    have h_subst : 291 / 500 < (1 / 6 : ℝ) ^ (1 / 5 : ℝ) * (1 + ((1 / 6 : ℝ) ^ (1 / 5 : ℝ)) ^ 5) := by
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
      rw [ ← div_lt_iff₀ ] <;> norm_num [ Real.lt_rpow_iff_log_lt ];
      rw [ div_mul_eq_mul_div, lt_div_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ];
    exact h_subst.trans_le ( mul_le_mul hr ( add_le_add_left ( pow_le_pow_left₀ ( by positivity ) hr 5 ) _ ) ( by positivity ) ( by linarith [ Real.rpow_nonneg ( by norm_num : ( 0 : ℝ ) ≤ 1 / 6 ) ( 1 / 5 : ℝ ) ] ) );
  · linarith [ pow_nonneg ( show 0 ≤ r by exact le_trans ( by positivity ) hr ) 5 ]

/-
Define `r_c` and `index_map` to classify the components.
-/
noncomputable def r_c : ℝ := (1/6)^(1/5 : ℝ)

noncomputable def index_map (z : ℂ) : Fin 6 :=
  if ‖z‖ < r_c then 0
  else
    let θ := z.arg
    if θ > -Real.pi ∧ θ < -3 * Real.pi / 5 then 1
    else if θ > -3 * Real.pi / 5 ∧ θ < -Real.pi / 5 then 2
    else if θ > -Real.pi / 5 ∧ θ < Real.pi / 5 then 3
    else if θ > Real.pi / 5 ∧ θ < 3 * Real.pi / 5 then 4
    else 5

/-
Let `components'` be the set of connected components of `sublevelSet'` containing the roots.
-/
noncomputable def components' : Finset (Set ℂ) := roots'.image (fun z => connectedComponentIn sublevelSet' z)

/-
Define open sets $U_i$ that partition the complement of the separating set.
-/
noncomputable def U : Fin 6 → Set ℂ
| 0 => {z | ‖z‖ < r_c}
| 1 => {z | ‖z‖ > r_c ∧ -Real.pi < z.arg ∧ z.arg < -3 * Real.pi / 5}
| 2 => {z | ‖z‖ > r_c ∧ -3 * Real.pi / 5 < z.arg ∧ z.arg < -Real.pi / 5}
| 3 => {z | ‖z‖ > r_c ∧ -Real.pi / 5 < z.arg ∧ z.arg < Real.pi / 5}
| 4 => {z | ‖z‖ > r_c ∧ Real.pi / 5 < z.arg ∧ z.arg < 3 * Real.pi / 5}
| 5 => {z | ‖z‖ > r_c ∧ 3 * Real.pi / 5 < z.arg ∧ z.arg < Real.pi}

/-
The set of roots of f is equal to the set roots'.
-/
lemma roots_eq : roots = roots' := by
  unfold roots roots';
  -- The polynomial $f(z) = z^6 - z$ can be factored as $z(z^5 - 1)$.
  have h_factor : f = Polynomial.X * (Polynomial.X ^ 5 - 1) := by
    exact Polynomial.funext fun x => by norm_num [ f ] ; ring;
  rw [ h_factor, Polynomial.roots_mul ] <;> norm_num;
  · -- The roots of $X^5 - 1$ are exactly the 5th roots of unity.
    have h_roots_X5_minus_1 : (Polynomial.X ^ 5 - 1 : Polynomial ℂ).roots.toFinset = Finset.image (fun k : Fin 5 => Complex.exp (Complex.I * 2 * k * Real.pi / 5)) Finset.univ := by
      -- The polynomial $X^5 - 1$ splits into linear factors over the complex numbers, with roots exactly the 5th roots of unity.
      have h_splits : (Polynomial.X ^ 5 - 1 : Polynomial ℂ) = Finset.prod (Finset.univ : Finset (Fin 5)) (fun k => Polynomial.X - Polynomial.C (Complex.exp (Complex.I * 2 * k * Real.pi / 5))) := by
        refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
        exact Finset.image ( fun k : Fin 5 => Complex.exp ( Complex.I * 2 * k * Real.pi / 5 ) ) Finset.univ;
        · refine' lt_of_lt_of_le ( Polynomial.degree_sub_lt _ _ _ ) _ <;> norm_num [ Polynomial.degree_prod ];
          · erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num;
          · exact ne_of_apply_ne ( Polynomial.eval 2 ) ( by norm_num );
          · norm_num [ Polynomial.leadingCoeff_prod ];
          · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, Complex.exp_eq_exp_iff_exists_int ];
            · erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num;
            · norm_num [ Fin.ext_iff, Complex.ext_iff ];
              intro a₁ a₂ x hx; exact_mod_cast ( by nlinarith [ Real.pi_pos, show ( x : ℝ ) = 0 by rcases x with ⟨ _ | _ | x ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos, show ( a₁ : ℝ ) < 5 by exact Nat.cast_lt.mpr a₁.2, show ( a₂ : ℝ ) < 5 by exact Nat.cast_lt.mpr a₂.2 ] ] : ( a₁ : ℝ ) = a₂ ) ;
        · simp +zetaDelta at *;
          intro a; rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff.mpr ⟨ a, by push_cast; ring ⟩ ] ; simp +decide [ Finset.prod_eq_prod_diff_singleton_mul ( Finset.mem_univ a ) ] ;
      rw [ h_splits, Polynomial.roots_prod ];
      · norm_num [ Finset.ext_iff ];
        exact fun x => ⟨ fun hx => by rcases hx with ( rfl | rfl | rfl | rfl | rfl ) <;> [ exact ⟨ 0, by norm_num ⟩ ; exact ⟨ 1, by norm_num ⟩ ; exact ⟨ 2, by norm_num ⟩ ; exact ⟨ 3, by norm_num ⟩ ; exact ⟨ 4, by norm_num ⟩ ], by rintro ⟨ k, rfl ⟩ ; fin_cases k <;> norm_num ⟩;
      · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _;
    rw [h_roots_X5_minus_1];
  · exact ne_of_apply_ne ( Polynomial.eval 2 ) ( by norm_num )

/-
The modulus of f is invariant under rotation by multiples of 2pi/5.
-/
lemma f_symmetry_pow (z : ℂ) (k : ℕ) : ‖f.eval (z * (Complex.exp (Complex.I * (2 * Real.pi / 5))) ^ k)‖ = ‖f.eval z‖ := by
  -- By definition of $f$, we know that $f(z * \exp(i * (2 * \pi / 5))) = f(z)$ for any $z$.
  have h_f_symm : ∀ z : ℂ, ‖f.eval (z * Complex.exp (Complex.I * (2 * Real.pi / 5)))‖ = ‖f.eval z‖ := by
    exact fun z => f_symmetry z;
  induction' k with k ih <;> simp_all +decide [ pow_succ, ← mul_assoc ]

/-
The sets U_i are pairwise disjoint.
-/
lemma U_disjoint : Pairwise (fun i j => Disjoint (U i) (U j)) := by
  intro a b hne; cases a ; cases b ; norm_num [ Fin.ext_iff ] at hne ⊢;
  rename_i i hi j hj;
  interval_cases i <;> interval_cases j <;> simp +decide [ * ] at hne ⊢;
  all_goals rw [ Set.disjoint_left ] ; simp +decide [ U ];
  all_goals intros; linarith

/-
For each i, the root assigned to index i is in the set U_i.
-/
noncomputable def root_of_index : Fin 6 → ℂ
| 0 => 0
| 1 => Complex.exp (Complex.I * (2 * 3 * Real.pi / 5))
| 2 => Complex.exp (Complex.I * (2 * 4 * Real.pi / 5))
| 3 => Complex.exp (Complex.I * (2 * 0 * Real.pi / 5))
| 4 => Complex.exp (Complex.I * (2 * 1 * Real.pi / 5))
| 5 => Complex.exp (Complex.I * (2 * 2 * Real.pi / 5))

lemma root_of_index_mem_U (i : Fin 6) : root_of_index i ∈ U i := by
  fin_cases i <;> simp +decide [ U ];
  all_goals unfold root_of_index; norm_num [ Complex.norm_exp, Complex.arg ];
  all_goals unfold r_c; norm_num [ Complex.exp_re, Complex.exp_im ];
  bound;
  · norm_num [ show 6 * Real.pi / 5 = Real.pi + Real.pi / 5 by ring, Real.sin_add, Real.cos_add ];
    rw [ if_neg ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ), if_neg ( by exact not_le_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] ) ) ) ] ; norm_num;
    exact ⟨ Real.rpow_lt_one ( by norm_num ) ( by norm_num ) ( by norm_num ), Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] ), by rw [ Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] ⟩;
  · rw [ show 8 * Real.pi / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring ] ; norm_num [ Real.sin_two_mul, Real.cos_two_mul ] ; ring_nf ; norm_num [ Real.pi_pos ];
    rw [ if_pos ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ), Real.arcsin_sin ] <;> try linarith [ Real.pi_pos ];
    exact ⟨ Real.rpow_lt_one ( by norm_num ) ( by norm_num ) ( by norm_num ), by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩;
  · exact ⟨ Real.rpow_lt_one ( by norm_num ) ( by norm_num ) ( by norm_num ), by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩;
  · rw [ if_pos ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ), Real.arcsin_sin ] <;> try linarith [ Real.pi_pos ];
    exact ⟨ Real.rpow_lt_one ( by norm_num ) ( by norm_num ) ( by norm_num ), by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩;
  · rw [ show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring ] ; norm_num [ Real.sin_pi_sub, Real.cos_pi_sub ];
    rw [ if_neg ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ), if_pos ( Real.sin_nonneg_of_nonneg_of_le_pi ( by positivity ) ( by linarith [ Real.pi_pos ] ) ) ] ; rw [ Real.arcsin_sin ] <;> try linarith [ Real.pi_pos ];
    exact ⟨ Real.rpow_lt_one ( by norm_num ) ( by norm_num ) ( by norm_num ), by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩

/-
For each i, the root assigned to index i is in the set of roots.
-/
lemma root_of_index_mem_roots' (i : Fin 6) : root_of_index i ∈ roots' := by
  fin_cases i <;> norm_num [ roots' ];
  all_goals unfold root_of_index; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
  · refine Or.inr ⟨ 3, ?_, ?_ ⟩ <;> norm_num;
  · refine Or.inr ⟨ 4, ?_, ?_ ⟩ <;> norm_num;
  · exact ⟨ 0, by norm_num ⟩;
  · exact Or.inr ⟨ 1, by norm_num, by norm_num ⟩;
  · exact Or.inr ⟨ 2, by norm_num, by norm_num ⟩

/-
A real number in (-pi, pi] is either one of the specific values or in one of the specified intervals.
-/
lemma real_cover_5 (x : ℝ) (hx : -Real.pi < x ∧ x ≤ Real.pi) :
  x = -3*Real.pi/5 ∨ x = -Real.pi/5 ∨ x = Real.pi/5 ∨ x = 3*Real.pi/5 ∨ x = Real.pi ∨
  (-Real.pi < x ∧ x < -3*Real.pi/5) ∨
  (-3*Real.pi/5 < x ∧ x < -Real.pi/5) ∨
  (-Real.pi/5 < x ∧ x < Real.pi/5) ∨
  (Real.pi/5 < x ∧ x < 3*Real.pi/5) ∨
  (3*Real.pi/5 < x ∧ x < Real.pi) := by
    grind

/-
If z is on one of the boundary rays and has modulus at least r_c, then |f(z)| > c'.
-/
lemma on_ray_implies_large_val (z : ℂ) (h_norm : ‖z‖ ≥ r_c)
  (h_arg : z.arg = -3*Real.pi/5 ∨ z.arg = -Real.pi/5 ∨ z.arg = Real.pi/5 ∨ z.arg = 3*Real.pi/5 ∨ z.arg = Real.pi) :
  ‖f.eval z‖ > c' := by
    -- By `ray_separation'`, $|f(w)| > c'$ for $w = \|z\| e^{i \pi/5}$.
    have h_ray : ‖f.eval (‖z‖ * Complex.exp (Complex.I * (Real.pi / 5)))‖ > c' := by
      convert ray_separation' ‖z‖ ( Real.pi / 5 ) h_norm _ using 1;
      · norm_num [ mul_comm ];
      · ring;
    -- Since $z = \|z\| e^{i \theta}$ and $|f(z)| = |f(\|z\| e^{i \theta})|$, we have $|f(z)| > c'$.
    have h_eq : z = ‖z‖ * Complex.exp (Complex.I * (z.arg)) := by
      nth_rw 1 [ ← Complex.norm_mul_exp_arg_mul_I z ] ; ring_nf;
    rcases h_arg with h_arg | h_arg | h_arg | h_arg | h_arg;
    · rw [ h_eq, h_arg ];
      convert h_ray using 1;
      convert f_symmetry_pow _ 3 using 2 ; ring_nf;
      norm_num [ mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add ] ; ring_nf;
      exact congr_arg ( Polynomial.eval · f ) ( by rw [ ← Complex.exp_periodic ] ; ring_nf );
    · rw [ h_eq, h_arg ];
      convert h_ray using 1;
      convert f_symmetry_pow _ 4 using 2 ; ring_nf;
      norm_num [ mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add ] ; ring_nf;
      exact congr_arg ( fun x => Polynomial.eval x f ) ( by rw [ ← Complex.exp_periodic ] ; ring_nf );
    · rw [ h_eq, h_arg ] ; simpa using h_ray;
    · rw [ h_eq, h_arg ];
      convert h_ray using 1;
      convert f_symmetry_pow ( ‖z‖ * Complex.exp ( Complex.I * ( Real.pi / 5 ) ) ) 1 using 2 ; ring_nf;
      norm_num [ mul_assoc, ← Complex.exp_add ] ; ring_nf;
    · rw [ h_eq, h_arg ];
      convert h_ray using 1;
      convert f_symmetry_pow ( ‖z‖ * Complex.exp ( Complex.I * ( Real.pi / 5 ) ) ) 2 using 1 ; ring_nf;
      norm_num [ mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add ] ; ring_nf

/-
The sets U_i are open.
-/
lemma isOpen_U (i : Fin 6) : IsOpen (U i) := by
  fin_cases i <;> unfold U <;> norm_num [ isOpen_lt, isOpen_const ];
  exact isOpen_lt continuous_norm continuous_const;
  · refine' isOpen_iff_mem_nhds.mpr _;
    intro z hz;
    have h_arg_cont : ContinuousAt (fun z : ℂ => z.arg) z := by
      refine' Complex.continuousAt_arg _;
      norm_num [ Complex.slitPlane ];
      contrapose! hz;
      norm_num [ Complex.arg ];
      split_ifs <;> norm_num [ hz ];
      · exact fun _ _ => by linarith [ Real.pi_pos ];
      · intros; linarith [ Real.pi_pos ];
    exact Filter.inter_mem ( IsOpen.mem_nhds ( isOpen_lt continuous_const continuous_norm ) hz.1 ) ( Filter.inter_mem ( h_arg_cont.eventually ( Ioi_mem_nhds hz.2.1 ) ) ( h_arg_cont.eventually ( Iio_mem_nhds hz.2.2 ) ) );
  · refine' IsOpen.inter _ _;
    · exact isOpen_lt continuous_const continuous_norm;
    · refine' isOpen_iff_mem_nhds.mpr _;
      intro z hz;
      -- The argument function is continuous, so the preimage of an open interval under the argument function is open.
      have h_arg_cont : ContinuousAt Complex.arg z := by
        refine' Complex.continuousAt_arg _;
        contrapose! hz;
        simp_all +decide [ Complex.slitPlane ];
        rw [ show z = z.re by simpa [ Complex.ext_iff ] using hz.2 ] ; norm_num [ Complex.arg ];
        intro h; have := h.1; have := h.2; split_ifs at * <;> norm_num at * <;> linarith [ Real.pi_pos ] ;
      exact h_arg_cont.eventually ( Ioo_mem_nhds hz.1 hz.2 );
  · refine' isOpen_iff_mem_nhds.mpr _;
    intro z hz
    obtain ⟨hz_norm, hz_arg⟩ := hz
    have h_arg_cont : ContinuousAt (fun z : ℂ => z.arg) z := by
      refine' Complex.continuousAt_arg _ |> fun h => h.mono_left _;
      · norm_num [ Complex.slitPlane ];
        contrapose! hz_norm;
        cases eq_or_lt_of_le hz_norm.1 <;> simp_all +decide [ Complex.arg ];
        · simp_all +decide [ show z = 0 by refine' Complex.ext _ _ <;> aesop ];
          exact Real.rpow_nonneg ( by norm_num ) _;
        · split_ifs at hz_arg <;> linarith [ Real.pi_pos ];
      · exact le_rfl
    have h_norm_cont : ContinuousAt (fun z : ℂ => ‖z‖) z := by
      exact continuous_norm.continuousAt
    exact (by
    exact Filter.inter_mem ( h_norm_cont.eventually ( lt_mem_nhds hz_norm ) ) ( Filter.inter_mem ( h_arg_cont.eventually ( Ioi_mem_nhds hz_arg.1 ) ) ( h_arg_cont.eventually ( Iio_mem_nhds hz_arg.2 ) ) ));
  · -- The set {z | π / 5 < z.arg ∧ z.arg < 3 * π / 5} is open because the argument function is continuous, and the interval (π/5, 3π/5) is open.
    have h_arg_open : IsOpen {z : ℂ | Real.pi / 5 < z.arg ∧ z.arg < 3 * Real.pi / 5} := by
      refine' isOpen_iff_mem_nhds.mpr _;
      intro z hz;
      -- The argument function is continuous, so the preimage of an open interval under the argument function is open.
      have h_arg_cont : ContinuousAt (fun z : ℂ => z.arg) z := by
        refine' Complex.continuousAt_arg _;
        norm_num [ Complex.slitPlane ];
        contrapose! hz;
        cases eq_or_lt_of_le hz.1 <;> simp_all +decide [ Complex.arg ];
        · exact fun h => False.elim <| h.not_ge <| by positivity;
        · split_ifs <;> intros <;> linarith [ Real.pi_pos ];
      exact h_arg_cont.eventually ( Ioo_mem_nhds hz.1 hz.2 );
    exact IsOpen.inter ( isOpen_lt continuous_const continuous_norm ) h_arg_open;
  · refine' IsOpen.inter _ _;
    · exact isOpen_lt continuous_const continuous_norm;
    · refine' isOpen_iff_mem_nhds.mpr _;
      intro z hz
      obtain ⟨hz₁, hz₂⟩ := hz
      have h_arg_cont : ContinuousAt (fun z : ℂ => z.arg) z := by
        refine' Complex.continuousAt_arg _;
        simp [Complex.slitPlane];
        contrapose! hz₁; simp_all +decide [ Complex.arg ];
        split_ifs at * <;> linarith [ Real.pi_pos ];
      exact Filter.inter_mem ( h_arg_cont.eventually ( lt_mem_nhds hz₁ ) ) ( h_arg_cont.eventually ( gt_mem_nhds hz₂ ) )

/-
The sublevel set is contained in the union of the open sets U_i.
-/
lemma sublevelSet_subset_union_U : sublevelSet' ⊆ ⋃ i, U i := by
  intro z hz;
  -- Consider the case where ‖z‖ > r_c.
  by_cases h_norm : ‖z‖ > r_c;
  · -- Since $z$ is not on any of the boundary rays and its modulus is greater than $r_c$, its argument must lie in one of the open intervals.
    have h_arg : z.arg = -3 * Real.pi / 5 ∨ z.arg = -Real.pi / 5 ∨ z.arg = Real.pi / 5 ∨ z.arg = 3 * Real.pi / 5 ∨ z.arg = Real.pi ∨
      (-Real.pi < z.arg ∧ z.arg < -3 * Real.pi / 5) ∨
      (-3 * Real.pi / 5 < z.arg ∧ z.arg < -Real.pi / 5) ∨
      (-Real.pi / 5 < z.arg ∧ z.arg < Real.pi / 5) ∨
      (Real.pi / 5 < z.arg ∧ z.arg < 3 * Real.pi / 5) ∨
      (3 * Real.pi / 5 < z.arg ∧ z.arg < Real.pi) := by
        have := real_cover_5 z.arg ⟨ by linarith [ Complex.neg_pi_lt_arg z ], by linarith [ Complex.arg_le_pi z ] ⟩ ; aesop;
    -- Since $z$ is not on any of the boundary rays, its argument must lie in one of the open intervals.
    have h_arg_open : (-Real.pi < z.arg ∧ z.arg < -3 * Real.pi / 5) ∨ (-3 * Real.pi / 5 < z.arg ∧ z.arg < -Real.pi / 5) ∨ (-Real.pi / 5 < z.arg ∧ z.arg < Real.pi / 5) ∨ (Real.pi / 5 < z.arg ∧ z.arg < 3 * Real.pi / 5) ∨ (3 * Real.pi / 5 < z.arg ∧ z.arg < Real.pi) := by
      have h_arg_not_boundary : ¬(z.arg = -3 * Real.pi / 5 ∨ z.arg = -Real.pi / 5 ∨ z.arg = Real.pi / 5 ∨ z.arg = 3 * Real.pi / 5 ∨ z.arg = Real.pi) := by
        intro h_arg_boundary
        have h_contradiction : ‖f.eval z‖ > c' := by
          apply on_ray_implies_large_val z h_norm.le h_arg_boundary
        exact h_contradiction.not_ge hz;
      grind;
    rcases h_arg_open with ( h | h | h | h | h ) <;> [ exact Set.mem_iUnion.mpr ⟨ 1, by exact ⟨ h_norm, h ⟩ ⟩ ; exact Set.mem_iUnion.mpr ⟨ 2, by exact ⟨ h_norm, h ⟩ ⟩ ; exact Set.mem_iUnion.mpr ⟨ 3, by exact ⟨ h_norm, h ⟩ ⟩ ; exact Set.mem_iUnion.mpr ⟨ 4, by exact ⟨ h_norm, h ⟩ ⟩ ; exact Set.mem_iUnion.mpr ⟨ 5, by exact ⟨ h_norm, h ⟩ ⟩ ];
  · by_cases h_eq : ‖z‖ = r_c;
    · exact absurd ( circle_separation' z h_eq ) ( by simpa [ h_eq ] using hz );
    · exact Set.mem_iUnion.mpr ⟨ 0, lt_of_le_of_ne ( le_of_not_gt h_norm ) h_eq ⟩

/-
If a connected set is contained in a finite union of pairwise disjoint open sets, it is contained in one of them.
-/
lemma connected_subset_disjoint_union_open {ι : Type*} [Finite ι] {U : ι → Set ℂ} (h_open : ∀ i, IsOpen (U i)) (h_disjoint : Pairwise (fun i j => Disjoint (U i) (U j))) {S : Set ℂ} (h_conn : IsConnected S) (h_subset : S ⊆ ⋃ i, U i) : ∃ i, S ⊆ U i := by
  obtain ⟨i, hi⟩ : ∃ i, (S ∩ U i).Nonempty := by
    exact Exists.elim ( Set.nonempty_iff_ne_empty.2 <| show S ≠ ∅ from h_conn.nonempty.ne_empty ) fun x hx => ⟨ Classical.choose <| Set.mem_iUnion.1 <| h_subset hx, ⟨ x, hx, Classical.choose_spec <| Set.mem_iUnion.1 <| h_subset hx ⟩ ⟩;
  use i;
  have h_subset_U_i : IsPreconnected S := by
    exact h_conn.isPreconnected;
  contrapose! h_subset_U_i;
  rw [ IsPreconnected ];
  simp_all +decide [ Set.subset_def ];
  refine' ⟨ U i, h_open i, ( ⋃ j ≠ i, U j ), isOpen_iUnion fun j => isOpen_iUnion fun hj => h_open j, _, _, _, _ ⟩ <;> simp_all +decide [ Set.Nonempty ];
  · exact fun x hx => Classical.or_iff_not_imp_left.2 fun hx' => by obtain ⟨ j, hj ⟩ := h_subset x hx; exact ⟨ j, by rintro rfl; exact hx' hj, hj ⟩ ;
  · exact ⟨ h_subset_U_i.choose, h_subset_U_i.choose_spec.1, by obtain ⟨ j, hj ⟩ := h_subset _ h_subset_U_i.choose_spec.1; exact ⟨ j, by rintro rfl; exact h_subset_U_i.choose_spec.2 hj, hj ⟩ ⟩;
  · exact fun x hx hx' j hj hx'' => Set.disjoint_left.mp ( h_disjoint hj ) hx'' hx'

/-
The set of roots is the image of the index map.
-/
lemma roots'_eq_image : roots' = Finset.univ.image root_of_index := by
  unfold roots' root_of_index;
  ext ; simp +decide [ Fin.exists_fin_succ, Finset.mem_image ];
  ring_nf at * ; aesop

/-
The connected component of the i-th root is contained in the i-th open set U_i.
-/
lemma component_subset_U (i : Fin 6) : connectedComponentIn sublevelSet' (root_of_index i) ⊆ U i := by
  -- By `connected_subset_disjoint_union_open`, there exists $k$ such that $C_i \subseteq U_k$.
  obtain ⟨k, hk⟩ : ∃ k : Fin 6, connectedComponentIn sublevelSet' (root_of_index i) ⊆ U k := by
    apply connected_subset_disjoint_union_open (fun j => isOpen_U j) (fun j k => by
      exact fun h => U_disjoint h) (by
    refine' ⟨ _, _ ⟩;
    · refine' ⟨ root_of_index i, _ ⟩;
      apply_rules [ mem_connectedComponentIn ];
      exact roots_in_sublevelSet' _ ( roots_eq.symm ▸ root_of_index_mem_roots' _ );
    · exact isPreconnected_connectedComponentIn) (by
    apply Set.Subset.trans (connectedComponentIn_subset _ _) (sublevelSet_subset_union_U));
  -- Since $z_i \in C_i$, $z_i \in U_k$.
  have hzik : root_of_index i ∈ U k := by
    exact hk <| mem_connectedComponentIn <| by
      exact roots_in_sublevelSet' _ <| roots_eq ▸ roots'_eq_image ▸ Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
  have hzik_eq_i : k = i := by
    -- Since $z_i \in U_i$ and $z_i \in U_k$, and $U_i$ and $U_k$ are disjoint, we must have $k = i$.
    have hzik_eq_i : root_of_index i ∈ U i := by
      exact root_of_index_mem_U i;
    exact Classical.not_not.1 fun h => Set.disjoint_left.1 ( U_disjoint h ) hzik hzik_eq_i;
  aesop

/-
The set of connected components containing the roots has cardinality 6.
-/
lemma components'_card : components'.card = 6 := by
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => connectedComponentIn sublevelSet' ( root_of_index ⟨ i, hi ⟩ );
  · unfold components';
    simp +decide [ roots'_eq_image ];
    exact fun a => ⟨ a, a.2, rfl ⟩;
  · unfold components';
    norm_num +zetaDelta at *;
    exact fun i hi => ⟨ root_of_index ⟨ i, hi ⟩, root_of_index_mem_roots' _, rfl ⟩;
  · intro i j hi hj h_eq
    have h_subset : connectedComponentIn sublevelSet' (root_of_index ⟨i, hi⟩) ⊆ U ⟨i, hi⟩ ∧ connectedComponentIn sublevelSet' (root_of_index ⟨j, hj⟩) ⊆ U ⟨j, hj⟩ := by
      exact ⟨ component_subset_U _, component_subset_U _ ⟩;
    have h_subset_eq : U ⟨i, hi⟩ ∩ U ⟨j, hj⟩ ≠ ∅ := by
      have h_subset_eq : root_of_index ⟨i, hi⟩ ∈ connectedComponentIn sublevelSet' (root_of_index ⟨i, hi⟩) := by
        apply_rules [ mem_connectedComponentIn ];
        apply roots_in_sublevelSet';
        exact roots_eq ▸ root_of_index_mem_roots' _;
      exact Set.Nonempty.ne_empty ⟨ root_of_index ⟨ i, hi ⟩, h_subset.1 h_subset_eq, h_eq ▸ h_subset_eq |> fun h => h_subset.2 h ⟩;
    contrapose! h_subset_eq;
    exact Set.disjoint_iff_inter_eq_empty.mp ( U_disjoint <| by simpa [ Fin.ext_iff ] using h_subset_eq )

/-
There exists a monic polynomial f, a constant c > 0, and a natural number m such that f has m distinct roots, the sublevel set {|f(z)| <= c} has m distinct connected components, and at least one component is not convex.
-/
theorem main_result : ∃ (f : Polynomial ℂ) (c : ℝ) (m : ℕ),
  f.Monic ∧
  f.roots.Nodup ∧
  f.roots.toFinset.card = m ∧
  c > 0 ∧
  (f.roots.toFinset.image (fun z => connectedComponentIn {w | ‖f.eval w‖ ≤ c} z)).card = m ∧
  ∃ K ∈ (f.roots.toFinset.image (fun z => connectedComponentIn {w | ‖f.eval w‖ ≤ c} z)), ¬ Convex ℝ K := by
    refine' ⟨ Polynomial.X ^ 6 - Polynomial.X, _, _, _, _, rfl, _, _, _ ⟩;
    exact 0.582;
    · rw [ Polynomial.Monic, Polynomial.leadingCoeff_sub_of_degree_lt ] <;> norm_num;
    · convert f_roots_distinct;
    · norm_num;
    · convert components'_card using 1;
      · unfold components';
        congr! 2;
        convert roots_eq using 1;
      · convert roots_card using 1;
    · refine' ⟨ _, Finset.mem_image.mpr ⟨ 0, _, rfl ⟩, _ ⟩ <;> norm_num;
      · exact ne_of_apply_ne ( Polynomial.eval 2 ) ( by norm_num );
      · convert C0_not_convex using 1;
        unfold C0;
        unfold sublevelSet';
        unfold f c'; norm_num;

theorem erdos_1047 :
  ¬ (∀ (f : Polynomial ℂ) (c : ℝ) (m : ℕ),
      f.Monic →
      f.roots.Nodup →
      f.roots.toFinset.card = m →
      c > 0 →
      (f.roots.toFinset.image
            (fun z => connectedComponentIn {w | ‖f.eval w‖ ≤ c} z)).card = m →
      ∀ K ∈ (f.roots.toFinset.image
            (fun z => connectedComponentIn {w | ‖f.eval w‖ ≤ c} z)),
        Convex ℝ K) := by
  classical
  intro h
  rcases main_result with
    ⟨f, c, m, hfMonic, hfNodup, hcard, hcpos, himgcard, ⟨K, hKmem, hKnotConvex⟩⟩
  have hKconv : Convex ℝ K :=
    (h f c m hfMonic hfNodup hcard hcpos himgcard) K hKmem
  exact hKnotConvex hKconv

#print axioms erdos_1047
-- 'erdos_1047' depends on axioms: [propext, Classical.choice, Quot.sound]
