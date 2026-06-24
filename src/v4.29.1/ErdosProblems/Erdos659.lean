/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 659.
https://www.erdosproblems.com/forum/thread/659

Formalization status:
- Conditional on: bernays

Informal authors:
- Benjamin Grayzel
- Adam Sheffer
- Pieter Moree
- Robert Osburn
- Desmond Weisenberg
- Gemini

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://adamsheffer.wordpress.com/2014/07/16/point-sets-with-few-distinct-distances/
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos659.md
-/
/-
We formalized the solution to the Erdős problem concerning distances and points.
We defined the lattice `L` and the point sets `P_m`.
We proved that `P_m` satisfies the local constraint (every 4 points determine at least 3 distances)
by reducing it to the absence of squares, equilateral triangles, and golden ratio distances in `L`,
which we verified.
We proved that the number of distinct distances in `P_m` is bounded by `B_Q(3m^2)`, where `Q` is the
quadratic form `x^2 + 2y^2`.
Using Bernays' theorem (assumed as a hypothesis), we established the asymptotic bound `O(n /
sqrt(log n))` for the number of distinct distances in a subset of size `n`.
--
I have proved Perucca's classification theorem (`PeruccaClassificationStatement_proof`) using some
helper lemmas I established.
-/

import Mathlib
import ErdosProblems.Axioms

namespace Erdos659

set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 50000000

open scoped Real

open Filter

open Asymptotics

/-
Define the set of points P_m as the image of the m x m grid under the lattice map (x, y) -> (x,
sqrt(2)y).
-/
noncomputable def latticePoint (p : ℤ × ℤ) : ℝ × ℝ :=
  (p.1, Real.sqrt 2 * p.2)

noncomputable def P (m : ℕ) : Finset (ℝ × ℝ) :=
  (Finset.product (Finset.range m) (Finset.range m)).map ⟨fun (i, j) => latticePoint (i, j), by
    unfold latticePoint;
    norm_num [ Function.Injective ]⟩

/-
Define D(P) as the set of nonzero distances between pairs of points in P.
-/
noncomputable def distinctDistances' (S : Finset (ℝ × ℝ)) : Finset ℝ :=
  (S.product S).image (fun (p, q) => dist p q) \ {0}

/-
Define the quadratic form Q(u,v) = u^2 + 2v^2 and prove it is primitive and positive definite with
discriminant -8.
-/
def Q_form : BinQuadForm := ⟨1, 0, 2⟩

lemma Q_form_primitive : Q_form.Primitive := by
  unfold BinQuadForm.Primitive Q_form
  decide

lemma Q_form_posDef : Q_form.PosDef := by
  unfold BinQuadForm.PosDef BinQuadForm.discr Q_form
  decide

lemma Q_form_discr : Q_form.discr = -8 := by
  unfold BinQuadForm.discr Q_form
  rfl

/-
The number of distinct distances in P_m is at most the number of integers <= 3m^2 represented by the
quadratic form Q(u,v) = u^2 + 2v^2.
-/
theorem distinctDistances'_bound (m : ℕ) (hm : m ≥ 1) :
    (distinctDistances' (P m)).card ≤ BinQuadForm.B Q_form (3 * m ^ 2) := by
      -- The squared distances are exactly the values of Q(u,v) = u^2 + 2v^2 with |u|, |v| ≤
      -- m-1.
      have h_squared_dist : ∀ p ∈ (P m), ∀ q ∈ (P m), p ≠ q → ∃ u v : ℤ,
        u^2 + 2 * v^2 = (dist p q)^2 ∧ 0 < u^2 + 2 * v^2 ∧
          u^2 + 2 * v^2 ≤ 3 * m^2 := by
        intros p hp q hq hne
        obtain ⟨u, v, huv⟩ : ∃ u v : ℤ,
          u^2 + 2 * v^2 = (dist p q)^2 ∧ |u| ≤ m - 1 ∧ |v| ≤ m - 1 := by
          unfold P at hp hq;
          unfold latticePoint at hp hq;
          norm_num [ dist_eq_norm, Prod.norm_def ] at *;
          rcases hp with ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩ ;
          rcases hq with ⟨ c, d, ⟨ hc, hd ⟩, rfl ⟩;
          cases max_cases ( |(a : ℝ) - c| ) ( |Real.sqrt 2 * b - Real.sqrt 2 * d| ) <;>
            simp_all +decide [ ← mul_sub, abs_mul ];
          · refine ⟨ (a : ℤ) - (c : ℤ), 0, ?_, ?_, ?_ ⟩ <;> norm_num;
            · have ha_le : a ≤ m - 1 := Nat.le_sub_one_of_lt ha
              have hc_le : c ≤ m - 1 := Nat.le_sub_one_of_lt hc
              have h_abs : ((a : ℤ) - (c : ℤ)).natAbs ≤ m - 1 :=
                Int.natAbs_coe_sub_coe_le_of_le ha_le hc_le
              have h_abs_lt : ((a : ℤ) - (c : ℤ)).natAbs < m :=
                lt_of_le_of_lt h_abs (by omega)
              rw [← Int.natCast_natAbs]
              exact_mod_cast h_abs_lt;
            · linarith;
          · norm_num [ mul_pow, abs_of_nonneg ] at *;
            refine ⟨ 0, (b : ℤ) - (d : ℤ), by push_cast; ring, by norm_num; linarith, ?_ ⟩;
            have hb_le : b ≤ m - 1 := Nat.le_sub_one_of_lt hb
            have hd_le : d ≤ m - 1 := Nat.le_sub_one_of_lt hd
            have h_abs : ((b : ℤ) - (d : ℤ)).natAbs ≤ m - 1 :=
              Int.natAbs_coe_sub_coe_le_of_le hb_le hd_le
            have h_abs_lt : ((b : ℤ) - (d : ℤ)).natAbs < m :=
              lt_of_le_of_lt h_abs (by omega)
            rw [← Int.natCast_natAbs]
            exact_mod_cast h_abs_lt;
        exact ⟨ u, v, huv.1,
          by
            exact_mod_cast
              ( by nlinarith [ show 0 < dist p q from dist_pos.mpr hne ] :
                ( 0 : ℝ ) < u ^ 2 + 2 * v ^ 2 ),
          by nlinarith [ abs_le.mp huv.2.1, abs_le.mp huv.2.2 ] ⟩;
      have h_squared_dist : ∀ d ∈ distinctDistances' (P m), ∃ n : ℕ,
        n ≤ 3 * m^2 ∧ ∃ u v : ℤ,
        u^2 + 2 * v^2 = n ∧ d^2 = n := by
        intro d hd;
        -- By definition of $distinctDistances'$, there exist $p, q \in P_m$ such that $p \neq q$
        -- and $d = dist p q$.
        obtain ⟨p, hp, q, hq, hpq, rfl⟩ : ∃ p ∈ P m, ∃ q ∈ P m,
          p ≠ q ∧ d = dist p q := by
          unfold distinctDistances' at hd; aesop;
        obtain ⟨ u, v, h₁, h₂,
          h₃ ⟩ := h_squared_dist p hp q hq hpq; exact ⟨ u.natAbs ^ 2 + 2 * v.natAbs ^ 2,
          by linarith [ abs_mul_abs_self u, abs_mul_abs_self v ], u, v,
          by simp +decide,
          by
            simp +decide at *
            linarith ⟩ ;
      -- Therefore, the number of distinct distances in $P_m$ is at most the number of integers $n
      -- \leq 3m^2$ represented by $Q(u,v) = u^2 + 2v^2$.
      have h_card_le_B : (distinctDistances' (P m)).card ≤
          (Nat.card {n : ℕ | (n : ℝ) ≤ 3 * m^2 ∧
            ∃ u v : ℤ, u^2 + 2 * v^2 = (n : ℤ)}) := by
        have h_card_le_B : (distinctDistances' (P m)).card ≤
            (Nat.card (Finset.image (fun d => Nat.floor (d^2)) (distinctDistances' (P m)))) := by
          rw [ Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_image_of_injOn ];
          intro d hd d' hd' h_eq; obtain ⟨ n, hn₁, u, v, huv,
            hd₂ ⟩ := h_squared_dist d hd; obtain ⟨ n', hn₁', u', v', huv',
            hd₂' ⟩ := h_squared_dist d' hd'; simp_all +decide [ sq ] ;
          -- Since $d$ and $d'$ are both non-negative (as they are distances), we can conclude that
          -- $d = d'$.
          have h_nonneg : 0 ≤ d ∧ 0 ≤ d' := by
            unfold distinctDistances' at hd hd'; aesop;
          nlinarith;
        refine le_trans h_card_le_B ?_;
        apply_rules [ Nat.card_mono ];
        · exact Set.finite_iff_bddAbove.mpr ⟨ 3 * m ^ 2, fun n hn => mod_cast hn.1 ⟩;
        · intro n hn;
          obtain ⟨ d, hd, rfl ⟩ := Finset.mem_image.mp hn;
          obtain ⟨ n, hn₁, u, v, hn₂,
            hn₃ ⟩ := h_squared_dist d hd
          use mod_cast Nat.floor_le_of_le ( mod_cast hn₃.symm ▸ mod_cast hn₁ )
          aesop;
      convert h_card_le_B using 1;
      unfold Q_form; norm_num [ BinQuadForm.eval ] ;
      unfold BinQuadForm.B; norm_num [ BinQuadForm.eval ] ;
      norm_num [ sq, mul_assoc ]

/-
The set L is closed under subtraction.
-/
def L_set : Set (ℝ × ℝ) := Set.range latticePoint

lemma L_set_sub_closed : ∀ p q, p ∈ L_set → q ∈ L_set → p - q ∈ L_set := by
  unfold L_set;
  unfold latticePoint;
  norm_num +zetaDelta at *;
  exact fun a b a_1 b_1 x y hx hy z w hz hw =>
    ⟨ ⟨ x - z, by push_cast; linarith ⟩, ⟨ y - w, by push_cast; linarith ⟩ ⟩

/-
If n = m * sqrt(2) for integers n, m, then n = m = 0.
-/
lemma sqrt2_irrational_implication (n m : ℤ) (h : (n : ℝ) = Real.sqrt 2 * m) :
    n = 0 ∧ m = 0 := by
  by_contra hmn;
  exact irrational_sqrt_two <| ⟨ n / m,
    by push_cast [ h ] ; rw [ mul_div_cancel_right₀ _ ( by aesop ) ] ⟩

/-
The lattice L contains no non-zero vector v such that its 90-degree rotation is also in L.
-/
lemma L_set_no_square_vector : ∀ v, v ∈ L_set → (-v.2, v.1) ∈ L_set → v = 0 := by
  norm_num +zetaDelta at *;
  rintro a b ⟨ x, hx ⟩ ⟨ y, hy ⟩;
  -- From the equations $a = x.1$ and $b = \sqrt{2} x.2$, and $b = -y.1$ and $a = \sqrt{2} y.2$, we
  -- can deduce that $y.1 = -\sqrt{2} x.2$ and $y.2 = x.1 / \sqrt{2}$.
  have hy1 : y.1 = -Real.sqrt 2 * x.2 := by
    unfold latticePoint at *; aesop;
  have hy2 : y.2 = x.1 / Real.sqrt 2 := by
    unfold latticePoint at *; aesop;
  -- Since $y.1$ and $y.2$ are integers, and $\sqrt{2}$ is irrational, this implies that $x.2 = 0$
  -- and $x.1 = 0$.
  have hx2 : x.2 = 0 := by
    by_contra hx2_nonzero;
    exact irrational_sqrt_two <| ⟨ -y.1 / x.2,
      by push_cast [ hy1 ] ; rw [ div_eq_iff <| Int.cast_ne_zero.mpr hx2_nonzero ] ; ring ⟩
  have hx1 : x.1 = 0 := by
    by_contra hx1_nonzero;
    exact irrational_sqrt_two <| ⟨ x.1 / y.2,
      by push_cast [ hy2 ] ; rw [ div_div_cancel₀ ] ; positivity ⟩;
  unfold latticePoint at hx; aesop;

/-
If a vector v is in L and its 60-degree rotation is also in L, then v must be 0.
-/
lemma L_set_rotation_60 (v : ℝ × ℝ) (hv : v ∈ L_set) :
    let v_rot := (v.1 / 2 - v.2 * Real.sqrt 3 / 2, v.1 * Real.sqrt 3 / 2 + v.2 / 2)
    v_rot ∈ L_set → v = 0 := by
      field_simp;
      obtain ⟨ u, v, hv ⟩ := hv;
      rintro ⟨ m, hm ⟩;
      norm_num [ Prod.ext_iff, latticePoint ] at hm ⊢;
      -- If $u.2 \neq 0$, then $\sqrt{6}$ must be rational, which is a contradiction.
      by_cases hu2 : u.2 = 0;
      · by_cases hu1 : u.1 = 0 <;> simp_all +decide;
        -- Squaring both sides of the equation $\sqrt{2} * m.2 = u.1 * \sqrt{3} / 2$, we get $2 *
        -- m.2^2 = 3 * u.1^2 / 4$, which simplifies to $8 * m.2^2 = 3 * u.1^2$.
        have h_sq : 8 * m.2 ^ 2 = 3 * u.1 ^ 2 := by
          have := congr_arg ( · ^ 2 ) hm.2
          ring_nf at this
          norm_num at this
          norm_cast at this
          push_cast [ ← @Int.cast_inj ℝ ] at *; linarith;
        -- Since $u.1 \neq 0$, we can divide both sides of the equation $8 * m.2^2 = 3 * u.1^2$ by
        -- $u.1^2$ to get $8 * (m.2 / u.1)^2 = 3$.
        obtain ⟨k, hk⟩ : ∃ k : ℚ, k^2 = 3 / 8 := by
          use m.2 / u.1;
          rw [ div_pow, div_eq_div_iff ] <;> norm_cast <;> first |linarith|aesop;
        apply_fun ( fun x => x.num ) at hk ; norm_num [ sq,
          Rat.mul_self_num ] at hk ; nlinarith [ show k.num ≤ 1 by nlinarith,
          show k.num ≥ -1 by nlinarith ];
      · have h_sqrt6_rat : ∃ q : ℚ, Real.sqrt 6 = q := by
          have h_eq : u.1 - 2 * m.1 = Real.sqrt 6 * u.2 := by
            rw [ show ( 6 : ℝ ) = 2 * 3 by norm_num,
              Real.sqrt_mul ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 3,
              Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ]
          exact ⟨ ( u.1 - 2 * m.1 ) / u.2,
            by
              push_cast [ h_eq ]
              rw [ mul_div_cancel_right₀ _ ( Int.cast_ne_zero.mpr hu2 ) ] ⟩;
        exact False.elim <| by
          obtain ⟨ q, hq ⟩ := h_sqrt6_rat
          have := congr_arg ( · ^ 2 ) hq
          norm_num at this
          norm_cast at this
          exact absurd ( congr_arg ( ·.num ) this ) ( by
            norm_num [ sq, Rat.mul_self_num ]
            intros h
            nlinarith [ show q.num ≤ 2 by nlinarith, show q.num ≥ -2 by nlinarith ] ) ;

/-
If z1 and z2 form an equilateral triangle with the origin in the complex plane, then z2 is a
rotation of z1 by +/ - 60 degrees.
-/
lemma complex_equilateral (z1 z2 : ℂ)
  (h : Complex.normSq z1 = Complex.normSq z2)
  (h2 : Complex.normSq (z1 - z2) = Complex.normSq z1) :
  z2 = z1 * Complex.exp (Complex.I * Real.pi / 3) ∨
  z2 = z1 * Complex.exp (-Complex.I * Real.pi / 3) := by
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at *;
    norm_num [ Complex.normSq, neg_div ] at *;
    by_cases h_case : z2.re = z1.re * (1 / 2) - z1.im * (Real.sqrt 3 / 2) ∨
      z2.re = z1.re * (1 / 2) + z1.im * (Real.sqrt 3 / 2);
    · grind;
    · exact False.elim <| h_case <| Classical.or_iff_not_imp_left.2 fun h =>
        mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by
          ring_nf
          norm_num
          nlinarith;

/-
Multiplication by exp(i pi/3) corresponds to the rotation formula.
-/
lemma rotation_equivalence (v : ℝ × ℝ) :
  let z : ℂ := v.1 + v.2 * Complex.I
  let w : ℂ := z * Complex.exp (Complex.I * Real.pi / 3)
  w.re = v.1 / 2 - v.2 * Real.sqrt 3 / 2 ∧ w.im = v.1 * Real.sqrt 3 / 2 + v.2 / 2 := by
    norm_num [ Complex.exp_re, Complex.exp_im ] ; ring_nf;
    grind

/-
If a vector v is in L and its -60 degree rotation is also in L, then v must be 0.
-/
lemma L_set_rotation_neg_60 (v : ℝ × ℝ) (hv : v ∈ L_set) :
    let v_rot := (v.1 / 2 + v.2 * Real.sqrt 3 / 2, -v.1 * Real.sqrt 3 / 2 + v.2 / 2)
    v_rot ∈ L_set → v = 0 := by
      intro h;
      -- Let w = v_rot. Then v is the rotation of w by 60 degrees.
      set w := h
      have hw : v = (w.1 / 2 - w.2 * Real.sqrt 3 / 2, w.1 * Real.sqrt 3 / 2 + w.2 / 2) := by
        grind;
      intro hw';
      -- Apply the lemma L_set_rotation_60 to w (with v as the rotated vector).
      have := L_set_rotation_60 w hw'
      simp at this;
      rw [ hw, this ];
      · norm_num;
      · exact hw ▸ hv

/-
If two vectors in L form an equilateral triangle with the origin, they must be zero.
-/
lemma L_set_equilateral_zero (v w : ℝ × ℝ) (hv : v ∈ L_set) (hw : w ∈ L_set)
  (h_eq : dist v 0 = dist w 0) (h_eq' : dist v w = dist v 0) : v = 0 := by
    revert v w hv hw h_eq h_eq';
    -- Let's unfold the definition of `L_set` to understand the elements of `v` and `w`.
    intro v w hv hw h_dist_eq h_dist_eq'
    obtain ⟨i, j, hi, hj⟩ := hv
    obtain ⟨k, l, hk, hl⟩ := hw;
    norm_num [ Prod.dist_eq, latticePoint ] at *;
    rcases eq_or_ne i.2 0 <;> rcases eq_or_ne k.2 0 <;> simp_all +decide [ abs_of_pos,
      Real.sqrt_pos.mpr ];
    · simp_all +decide [ abs_eq_abs, dist_eq_norm ];
      cases h_dist_eq <;> simp_all +decide [ Norm.norm ];
      · simpa using h_dist_eq'.symm;
      · cases abs_cases ( - ( k.1 : ℝ ) - k.1 ) <;>
        cases abs_cases ( k.1 : ℝ ) <;>
        norm_cast at * <;>
        linarith;
    · rw [ max_eq_right ] at h_dist_eq';
      · rw [ max_def_lt ] at h_dist_eq';
        split_ifs at h_dist_eq' <;> simp_all +decide [ abs_eq_abs ];
        · rw [ max_eq_right ( by linarith ) ] at h_dist_eq;
          exact False.elim <| irrational_sqrt_two <| ⟨ |↑i.1| / |↑k.2|,
            by push_cast [ h_dist_eq ] ; rw [ mul_div_cancel_right₀ _ <| by positivity ] ⟩;
        · exact False.elim <| irrational_sqrt_two <| ⟨ |↑k.1| / |↑k.2|,
          by push_cast [ ← h_dist_eq' ] ; rw [ mul_div_cancel_right₀ _ <| by positivity ] ⟩;
      · contrapose! h_dist_eq';
        cases max_cases ( |↑i.1| ) ( Real.sqrt 2 * |↑k.2| ) <;>
          cases max_cases ( |↑k.1| ) ( Real.sqrt 2 * |↑k.2| ) <;>
          cases max_cases ( dist i.1 k.1 ) ( Real.sqrt 2 * |↑k.2| ) <;>
          first | linarith | simp_all +decide;
        cases abs_cases ( i.1 : ℝ ) <;>
          cases abs_cases ( k.1 : ℝ ) <;>
          cases abs_cases ( k.2 : ℝ ) <;>
          simp_all +decide [ dist_eq_norm ];
        any_goals nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
          ( by norm_cast : ( 0 : ℝ ) ≤ k.2 ) ];
        · norm_num [ Norm.norm ] at *;
          rw [ abs_of_nonneg, abs_of_nonpos ] <;> nlinarith [ Real.sqrt_nonneg 2,
            Real.sq_sqrt zero_le_two, ( by norm_cast : ( k.1 : ℝ ) < 0 ),
            ( by norm_cast : ( 0 : ℝ ) ≤ k.2 ) ];
        · norm_num [ Norm.norm ] at *;
          cases abs_cases ( - ( k.1 : ℝ ) - k.1 ) <;>
            cases abs_cases ( k.1 : ℝ ) <;>
            push_cast [ * ] at * <;>
            nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
              ( by
                norm_cast
                linarith : ( k.2 : ℝ ) < 0 ) ];
        · norm_num [ show i.1 = -k.1 by exact_mod_cast neg_eq_iff_eq_neg.mp h_dist_eq ] at *;
          norm_num [ Norm.norm ] at *;
          rw [ abs_of_nonpos, abs_of_nonneg ] <;> nlinarith [ Real.sqrt_nonneg 2,
            Real.sq_sqrt zero_le_two, show ( k.1 : ℝ ) ≥ 1 by exact_mod_cast by linarith ];
        · norm_num [ show i.1 = -k.1 by exact_mod_cast neg_eq_iff_eq_neg.mp h_dist_eq ] at *;
          norm_num [ Norm.norm ] at *;
          cases abs_cases ( - ( k.1 : ℝ ) - k.1 ) <;>
            cases abs_cases ( k.1 : ℝ ) <;>
            linarith [ ( by norm_cast; linarith : ( 0 : ℝ ) < k.1 ) ];
    · rw [ max_eq_iff ] at h_dist_eq;
      norm_num [ abs_eq_abs ] at h_dist_eq;
      rcases h_dist_eq with ( ⟨ h | h, h' ⟩ | ⟨ h,
        h' ⟩ ) <;> norm_cast at * <;> simp_all +decide;
      · exact irrational_sqrt_two <| ⟨ |↑k.1| / |↑i.2|,
        by push_cast [ ← h_dist_eq' ] ; rw [ mul_div_cancel_right₀ _ <| by positivity ] ⟩;
      · rw [ max_eq_iff ] at h_dist_eq';
        rcases h_dist_eq' with ( ⟨ h₁, h₂ ⟩ | ⟨ h₁, h₂ ⟩ ) <;>
          norm_num [ dist_eq_norm ] at *;
        · norm_num [ Norm.norm ] at *;
          cases abs_cases ( -k.1 - k.1 : ℝ ) <;>
            cases abs_cases ( k.1 : ℝ ) <;>
            cases lt_or_gt_of_ne ‹¬i.2 = 0› <;>
            nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
              show ( |i.2| : ℝ ) ≥ 1 by
                exact mod_cast abs_pos.mpr ‹¬i.2 = 0› ];
        · exact irrational_sqrt_two <| ⟨ |↑k.1| / |↑i.2|,
          by push_cast [ ← h₁ ] ; rw [ mul_div_cancel_right₀ _ <| by positivity ] ⟩;
      · exact irrational_sqrt_two <| ⟨ |↑k.1| / |↑i.2|,
        by push_cast [ ← h ] ; rw [ mul_div_cancel_right₀ _ <| by positivity ] ⟩;
    · cases max_choice ( |↑i.1| ) ( Real.sqrt 2 * |↑i.2| ) <;>
      cases max_choice ( |↑k.1| ) ( Real.sqrt 2 * |↑k.2| ) <;>
      simp_all +decide;
      · rw [ abs_eq_abs ] at h_dist_eq;
        rcases h_dist_eq with h | h <;> simp_all +decide [ Real.dist_eq ];
        · -- Since $|√2 * i.2 - √2 * k.2| = |k.1|$, we can divide both sides by
          -- $√2$ to get $|i.2 -
          -- k.2| = |k.1| / √2$.
          have h_div : |(i.2 - k.2 : ℝ)| = |(k.1 : ℝ)| / Real.sqrt 2 := by
            rw [ ← h_dist_eq', ← mul_sub, abs_mul, abs_of_nonneg ( Real.sqrt_nonneg _ ),
              mul_div_cancel_left₀ _ ( by positivity ) ];
          -- Since $|k.1| / \sqrt{2}$ is rational, $|k.1|$ must be a multiple of $\sqrt{2}$.
          obtain ⟨q, hq⟩ : ∃ q : ℚ, |(k.1 : ℝ)| = q * Real.sqrt 2 := by
            exact ⟨ |↑i.2 - ↑k.2|,
              by push_cast [ h_div ] ; rw [ div_mul_cancel₀ _ ( by positivity ) ] ⟩;
          -- Since $|k.1|$ is an integer and $q$ is rational, the only way $|k.1| = q * \sqrt{2}$
          -- can hold is if $q = 0$.
          have hq_zero : q = 0 := by
            by_contra hq_nonzero;
            exact irrational_sqrt_two <| ⟨ |↑k.1| / q,
              by push_cast [ hq ] ; rw [ mul_div_cancel_left₀ _ <| by positivity ] ⟩;
          simp_all +decide [ abs_eq_zero ];
          exact not_le_of_gt
            ( mul_pos ( Real.sqrt_pos.mpr zero_lt_two ) ( abs_pos.mpr ( by positivity ) ) )
            ‹Real.sqrt 2 * |↑i.2| ≤ 0›;
        · rw [ max_eq_iff ] at h_dist_eq';
          norm_cast at * ; simp_all +decide [ Int.dist_eq ];
          norm_num [ abs_sub_comm, ← mul_sub ] at *;
          cases h_dist_eq' <;> simp_all +decide [ ← two_mul, abs_mul ];
          · by_cases h : k.1 = 0 <;> simp_all +decide;
            exact not_le_of_gt
              ( mul_pos ( Real.sqrt_pos.mpr zero_lt_two ) ( abs_pos.mpr ( by norm_cast ) ) )
              ‹Real.sqrt 2 * |↑i.2| ≤ 0›;
          · nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
            abs_pos.mpr ( show ( i.2 : ℝ ) ≠ 0 by positivity ),
            abs_pos.mpr ( show ( k.2 : ℝ ) ≠ 0 by positivity ) ];
      · exact irrational_sqrt_two <| ⟨ |↑i.1| / |↑k.2|,
        by push_cast [ h_dist_eq ] ; rw [ mul_div_cancel_right₀ _ <| by positivity ] ⟩;
      · exact irrational_sqrt_two <| ⟨ |↑k.1| / |↑i.2|,
        by push_cast [ ← h_dist_eq ] ; rw [ mul_div_cancel_right₀ _ <| by positivity ] ⟩;
      · cases max_choice ( dist i.1 k.1 ) ( dist ( Real.sqrt 2 * i.2 ) ( Real.sqrt 2 * k.2 ) ) <;>
        simp_all +decide [ dist_eq_norm ];
        · -- Since $|i.2| = |k.2|$ and $i.2 \neq 0$, we have $|i.1 - k.1| = \sqrt{2} |k.2|$.
          have h_abs : |(i.1 : ℝ) - k.1| = Real.sqrt 2 * |(k.2 : ℝ)| := by
            norm_num [ Norm.norm ] at * ; aesop;
          exact irrational_sqrt_two <| ⟨ |i.1 - k.1| / |k.2|,
            by push_cast [ h_abs ] ; rw [ mul_div_cancel_right₀ _ <| by positivity ] ⟩;
        · simp_all +decide [ ← mul_sub, abs_mul ];
          norm_num [ abs_of_pos, Real.sqrt_pos ] at *;
          norm_cast at * ; simp_all +decide [ abs_eq_abs ];
          omega

/-
The lattice L contains no non-degenerate equilateral triangle.
-/
lemma L_set_no_equilateral_triangle :
    ∀ p q r, p ∈ L_set → q ∈ L_set → r ∈ L_set →
    dist p q = dist q r → dist q r = dist r p → p = q := by
      intros p q r hp hq hr h_eq h_eq';
      -- Let v = q - p and w = r - p. Since L is closed under subtraction, v and w are in L.
      set v : ℝ × ℝ := q - p
      set w : ℝ × ℝ := r - p
      have hv : v ∈ L_set := by
        exact L_set_sub_closed _ _ hq hp
      have hw : w ∈ L_set := by
        exact L_set_sub_closed _ _ hr hp;
      -- The distances satisfy dist(p, q) = dist(q, r) = dist(r, p).
      -- Translating to v and w:
      -- dist(v, 0) = dist(q - p, 0) = dist(q, p) = dist(p, q).
      -- dist(w, 0) = dist(r - p, 0) = dist(r, p).
      -- dist(v, w) = dist(q - p, r - p) = dist(q, r).
      have h_dist_v : dist v 0 = dist p q := by
        norm_num [ dist_eq_norm', Prod.norm_def ];
        rfl
      have h_dist_w : dist w 0 = dist r p := by
        simp +decide [ dist_eq_norm ];
        rfl
      have h_dist_vw : dist v w = dist q r := by
        simp +zetaDelta at *;
      have := L_set_equilateral_zero v w hv hw ?_ ?_ <;> aesop

/-
The squared distance between any two points in L is an integer.
-/
lemma L_set_squared_dist_is_int (p q : ℝ × ℝ) (hp : p ∈ L_set) (hq : q ∈ L_set) :
    ∃ n : ℤ, dist p q ^ 2 = n := by
      rcases hp with ⟨ u, rfl ⟩ ; rcases hq with ⟨ v, rfl ⟩ ; norm_num [ Prod.dist_eq,
        Real.dist_eq ] ;
      unfold latticePoint; norm_num;
      norm_num [ ← mul_sub, max_def' ];
      norm_num [ mul_pow, abs_of_nonneg, Real.sqrt_nonneg ];
      split_ifs <;> norm_cast <;> aesop

/-
The number (3+sqrt(5))/2 is irrational.
-/
lemma phi_sq_irrational_explicit : Irrational ((3 + Real.sqrt 5) / 2) := by
  exact_mod_cast
    Nat.Prime.irrational_sqrt ( by norm_num )
      |> Irrational.ratCast_add 3
      |> Irrational.div_ratCast <| by norm_num;

/-
The lattice L contains no four-point set forming a regular-pentagon trapezoid.
-/
lemma L_set_no_pentagon_trapezoid :
    ∀ p q r s, p ∈ L_set → q ∈ L_set → r ∈ L_set → s ∈ L_set →
    p ≠ q → q ≠ r → r ≠ s → s ≠ p →
    dist p r = dist p s → dist p s = dist q r → dist q r = dist q s →
      dist q s = dist r s * ((1 + Real.sqrt 5) / 2) → False := by
      intro p q r s hp hq hr hs hpq hqr hrs hsp hpr hpr' hqr' hsq;
      -- Since p, q, r, s are in L, by `L_set_squared_dist_is_int`, d1^2 and d2^2 are integers.
      obtain ⟨n1, hn1⟩ : ∃ n1 : ℤ, dist r s ^ 2 = n1 := by
        exact L_set_squared_dist_is_int r s hr hs
      obtain ⟨n2, hn2⟩ : ∃ n2 : ℤ, dist q s ^ 2 = n2 := by
        exact L_set_squared_dist_is_int q s hq hs;
      -- Squaring both sides of the equation $dist q s = dist r s * ((1 + Real.sqrt 5) / 2)$, we get
      -- $n2 = n1 * ((3 + Real.sqrt 5) / 2)$.
      have h_eq : n2 = n1 * ((3 + Real.sqrt 5) / 2) := by
        rw [ ← hn2, ← hn1, hsq ] ; ring_nf ; norm_num ; ring;
      -- Since $n1$ and $n2$ are integers, $(3 + \sqrt{5}) / 2$ must be rational.
      have h_rat : ∃ q : ℚ, (3 + Real.sqrt 5) / 2 = q := by
        exact ⟨ n2 / n1,
          by
            push_cast [ h_eq ]
            rw [ mul_div_cancel_left₀ _ ( by
              intro h
              norm_num [ h ] at *
              exact absurd hn1 ( by aesop ) ) ] ⟩;
      exact Nat.Prime.irrational_sqrt ( show Nat.Prime 5 by norm_num ) ⟨ h_rat.choose * 2 - 3,
        by push_cast; linarith [ h_rat.choose_spec ] ⟩

/-
A set of 4 points forms a square if the sides are equal and the diagonals are equal (and related to
the side by sqrt(2)).
-/
def is_square (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ p q r s, S = {p, q, r, s} ∧ p ≠ q ∧ q ≠ r ∧ r ≠ s ∧ s ≠ p ∧
  dist p q = dist q r ∧ dist q r = dist r s ∧ dist r s = dist s p ∧
  dist p r = dist q s ∧ dist p r = dist p q * Real.sqrt 2

/-
A set of points has an equilateral triangle if it contains 3 distinct points with equal pairwise
distances.
-/
def has_equilateral_triangle (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ p q r, {p, q, r} ⊆ S ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p ∧
  dist p q = dist q r ∧ dist q r = dist r p

/-
A set of 4 points forms a pentagon trapezoid if it consists of 3 equal sides and the diagonals are
in golden ratio to the side.
-/
def is_pentagon_trapezoid (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ p q r s, S = {p, q, r, s} ∧ p ≠ q ∧ q ≠ r ∧ r ≠ s ∧ s ≠ p ∧
  dist p r = dist p s ∧ dist p s = dist q r ∧ dist q r = dist q s ∧
  dist q s = dist r s * ((1 + Real.sqrt 5) / 2)

/-
A set has golden ratio distances if the ratio of two distinct distances is the golden ratio.
-/
def has_golden_ratio_distances (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ d1 d2, d1 ∈ distinctDistances' S ∧ d2 ∈ distinctDistances' S ∧
    d1 = d2 * ((1 + Real.sqrt 5) / 2)

/-
The set of points P_m is a subset of the lattice L.
-/
lemma P_subset_L (m : ℕ) : (P m : Set (ℝ × ℝ)) ⊆ L_set := by
  unfold L_set P;
  intro x hx; aesop

/-
The lattice L contains no set of points determining distances in the golden ratio.
-/
lemma L_no_golden_ratio (S : Finset (ℝ × ℝ)) (hS : (S : Set (ℝ × ℝ)) ⊆ L_set) :
    ¬ has_golden_ratio_distances S := by
      -- Suppose S has golden ratio distances. Then there exist d1, d2 in distinctDistances'(S) such
      -- that d1 = d2 * phi.
      rintro ⟨d1, d2, hd1, hd2, hd_ratio⟩
      have h_d1_sq : ∃ n : ℤ, d1 ^ 2 = n := by
        obtain ⟨ p, q, hp, hq, hd1_eq ⟩ : ∃ p q : ℝ × ℝ,
          p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ dist p q = d1 := by
          unfold distinctDistances' at hd1; aesop;
        have := L_set_squared_dist_is_int p q ( hS hp ) ( hS hq ) ; aesop;
      have h_d2_sq : ∃ n : ℤ, d2 ^ 2 = n := by
        unfold distinctDistances' at *;
        simp +zetaDelta at *;
        obtain ⟨ ⟨ a, b, a', b', ⟨ ha, hb ⟩, rfl ⟩,
          hd2 ⟩ := hd2; exact L_set_squared_dist_is_int _ _ ( hS ha ) ( hS hb ) ;
      -- Since $d2$ is a distinct distance, $d2 \neq 0$, so $d2^2 > 0$.
      have h_d2_sq_pos : 0 < d2 ^ 2 := by
        cases eq_or_ne d2 0 <;> simp_all +decide;
        · unfold distinctDistances' at hd1; aesop;
        · positivity;
      -- Thus phi^2 = d1^2 / d2^2 is rational.
      have h_phi_sq_rational : ∃ q : ℚ, ((1 + Real.sqrt 5) / 2) ^ 2 = q := by
        -- Substitute $d1 = d2 * ((1 + Real.sqrt 5) / 2)$ into $d1^2 = n$ and $d2^2 = m$ to get $n =
        -- m * ((1 + Real.sqrt 5) / 2)^2$.
        obtain ⟨n, hn⟩ := h_d1_sq
        obtain ⟨m, hm⟩ := h_d2_sq
        have h_eq : n = m * ((1 + Real.sqrt 5) / 2) ^ 2 := by
          rw [ ← hn, hd_ratio, mul_pow, hm ];
        exact ⟨ n / m, by push_cast [ h_eq ] ; rw [ mul_div_cancel_left₀ _ ( by aesop ) ] ⟩;
      exact Nat.Prime.irrational_sqrt ( show Nat.Prime 5 by norm_num )
        ⟨ h_phi_sq_rational.choose * 2 - 3, by
          push_cast
          linarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ),
            h_phi_sq_rational.choose_spec ] ⟩

/-
If two vectors u and v are orthogonal and have the same norm, then v is a 90 degree or -90 degree
rotation of u.
-/
lemma orthogonal_equal_norm_implies_rotation (u v : ℝ × ℝ)
    (h_ortho : u.1 * v.1 + u.2 * v.2 = 0)
    (h_norm : u.1 ^ 2 + u.2 ^ 2 = v.1 ^ 2 + v.2 ^ 2) :
    (v.1 = -u.2 ∧ v.2 = u.1) ∨ (v.1 = u.2 ∧ v.2 = -u.1) := by
      -- From the first equation, $u_x v_x = -u_y v_y$.
      have h_prod : u.1 * v.1 = -u.2 * v.2 := by
        linarith;
      -- Squaring both sides of the equation $u_x v_x = -u_y v_y$, we get $u_x^2 v_x^2 = u_y^2
      -- v_y^2$.
      have h_sq : u.1^2 * v.1^2 = u.2^2 * v.2^2 := by
        linear_combination' h_prod * h_prod;
      by_cases h_case1 : u.1^2 + u.2^2 = 0;
      · norm_num [ show u.1 = 0 by nlinarith only [ h_case1 ],
        show u.2 = 0 by nlinarith only [ h_case1 ] ] at *;
        constructor <;> nlinarith;
      · grind

/-
The distance on R x R is the L-infinity distance.
-/
lemma dist_L_infty (p q : ℝ × ℝ) : dist p q = max (|p.1 - q.1|) (|p.2 - q.2|) := by
  exact rfl

/-
Define Euclidean distance on R^2 and prove the expansion of its square.
-/
noncomputable def dist_euc (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

lemma dist_euc_comm (p q : ℝ × ℝ) : dist_euc p q = dist_euc q p := by
  unfold dist_euc
  congr 1
  ring

lemma dist_euc_eq_zero {p q : ℝ × ℝ} : dist_euc p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold dist_euc at h
    have hs_le : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h
    have hs_nonneg : 0 ≤ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hs : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 0 := le_antisymm hs_le hs_nonneg
    apply Prod.ext
    · nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    · nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  · intro h
    subst h
    simp [dist_euc]

lemma dist_euc_sq_expansion (u v : ℝ × ℝ) :
  (dist_euc u v) ^ 2 = (u.1^2 + u.2^2) + (v.1^2 + v.2^2) - 2 * (u.1 * v.1 + u.2 * v.2) := by
    unfold dist_euc;
    rw [ Real.sq_sqrt ] <;> nlinarith

/-
The set of distinct Euclidean distances in a set of points.
-/
noncomputable def distinctDistances'_euc (S : Finset (ℝ × ℝ)) : Finset ℝ :=
  (S.product S).image (fun (p, q) => dist_euc p q) \ {0}

/-
Definition of a square using Euclidean distance.
-/
def is_square_euc (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ p q r s, S = {p, q, r, s} ∧ p ≠ q ∧ q ≠ r ∧ r ≠ s ∧ s ≠ p ∧
  dist_euc p q = dist_euc q r ∧ dist_euc q r = dist_euc r s ∧ dist_euc r s = dist_euc s p ∧
  dist_euc p r = dist_euc q s ∧ dist_euc p r = dist_euc p q * Real.sqrt 2

/-
Definition of a set containing an equilateral triangle using Euclidean distance.
-/
def has_equilateral_triangle_euc (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ p q r, {p, q, r} ⊆ S ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p ∧
  dist_euc p q = dist_euc q r ∧ dist_euc q r = dist_euc r p

/-
Definition of a set containing golden ratio distances using Euclidean distance.
-/
def has_golden_ratio_distances_euc (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ d1 d2, d1 ∈ distinctDistances'_euc S ∧ d2 ∈ distinctDistances'_euc S ∧
    d1 = d2 * ((1 + Real.sqrt 5) / 2)

/-
If a vector u is in L and its 90 degree rotation is in L, then u is 0.
-/
def rotate90 (u : ℝ × ℝ) : ℝ × ℝ := (-u.2, u.1)

lemma L_no_rotate90 (u : ℝ × ℝ) (hu : u ∈ L_set) (hrot : rotate90 u ∈ L_set) : u = 0 := by
  -- Apply `L_set_no_square_vector` to obtain that $u = 0$.
  apply L_set_no_square_vector u hu hrot

/-
If p, q, r form a right isosceles triangle at q, then r-q is a rotation of p-q.
-/
lemma right_isosceles_euc_implies_rotation (p q r : ℝ × ℝ)
  (h_eq : dist_euc p q = dist_euc q r)
  (h_diag : dist_euc p r = dist_euc p q * Real.sqrt 2) :
  let u := (p.1 - q.1, p.2 - q.2)
  let v := (r.1 - q.1, r.2 - q.2)
  v = rotate90 u ∨ v = - rotate90 u := by
    -- By squaring both sides of the equation dist_euc p r = dist_euc p q * sqrt(2), we get (p.1 -
    -- r.1)^2 + (p.2 - r.2)^2 = 2 * ((p.1 - q.1)^2 + (p.2 - q.2)^2).
    have h_sq : (p.1 - r.1)^2 + (p.2 - r.2)^2 = 2 * ((p.1 - q.1)^2 + (p.2 - q.2)^2) := by
      unfold dist_euc at *;
      rw [ ← Real.sq_sqrt ( by positivity : 0 ≤ ( p.1 - r.1 ) ^ 2 + ( p.2 - r.2 ) ^ 2 ), h_diag,
        mul_pow, Real.sq_sqrt ( by positivity : 0 ≤ ( p.1 - q.1 ) ^ 2 + ( p.2 - q.2 ) ^ 2 ),
        Real.sq_sqrt ( by positivity : 0 ≤ ( 2 : ℝ ) ) ] ; ring;
    have h_ortho : (p.1 - q.1) * (r.1 - q.1) + (p.2 - q.2) * (r.2 - q.2) = 0 := by
      unfold dist_euc at h_eq;
      rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] at h_eq ; linarith;
    simp_all +decide [ rotate90 ];
    have h_rotate : (r.1 - q.1) = -(p.2 - q.2) ∨ (r.1 - q.1) = (p.2 - q.2) := by
      have h_rotate : (p.1 - q.1)^2 + (p.2 - q.2)^2 = (r.1 - q.1)^2 + (r.2 - q.2)^2 := by
        grind;
      exact Classical.or_iff_not_imp_left.2 fun h =>
        mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by nlinarith;
    cases h_rotate <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · exact Classical.or_iff_not_imp_left.2 fun h =>
        ⟨ mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by nlinarith,
          mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by nlinarith ⟩;
    · exact Classical.or_iff_not_imp_right.2 fun h =>
        ⟨ mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linarith,
          mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linarith ⟩

/-
The lattice L contains no square (Euclidean version).
-/
lemma L_no_square_euc (S : Finset (ℝ × ℝ)) (hS : (S : Set (ℝ × ℝ)) ⊆ L_set) :
    ¬ is_square_euc S := by
      rintro ⟨ p, q, r, s, rfl, hpq, hqr, hrs, hsp, h_dist ⟩;
      -- Let u = p - q and v = r - q.
      set u : ℝ × ℝ := (p.1 - q.1, p.2 - q.2)
      set v : ℝ × ℝ := (r.1 - q.1, r.2 - q.2);
      -- By right_isosceles_euc_implies_rotation, v = rotate90(u) or v = -rotate90(u).
      have hv : v = rotate90 u ∨ v = -rotate90 u := by
        apply right_isosceles_euc_implies_rotation;
        · exact h_dist.1;
        · exact h_dist.2.2.2.2;
      -- Since p, q, r are in L, u and v are in L (by closure under subtraction).
      have hu : u ∈ L_set := by
        have hu : p ∈ L_set ∧ q ∈ L_set := by
          exact ⟨ hS <| by norm_num, hS <| by norm_num ⟩;
        exact L_set_sub_closed _ _ hu.1 hu.2
      have hv : v ∈ L_set := by
        have hv : r ∈ L_set ∧ q ∈ L_set := by
          exact ⟨ hS <| by norm_num, hS <| by norm_num ⟩;
        apply L_set_sub_closed
        · exact hv.left
        · exact hv.right
      -- By L_no_rotate90, u = 0.
      have hu_zero : u = 0 := by
        rcases ‹v = rotate90 u ∨ v = -rotate90 u› with hv | hv <;>
          simp_all +decide [ Set.subset_def ];
        · exact L_no_rotate90 u hu ‹_›;
        · exact L_no_rotate90 u hu ( by
            simpa using L_set_sub_closed _ _
              ( show 0 ∈ L_set from ⟨ ( 0, 0 ), by norm_num [ latticePoint ] ⟩ )
              ‹-rotate90 u ∈ L_set› );
      exact hpq ( Prod.mk_inj.mpr ⟨ sub_eq_zero.mp ( congr_arg Prod.fst hu_zero ),
        sub_eq_zero.mp ( congr_arg Prod.snd hu_zero ) ⟩ )

/-
If a vector u is in L and its 60 degree rotation is in L, then u is 0.
-/
noncomputable def rotate60 (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 / 2 - u.2 * Real.sqrt 3 / 2, u.1 * Real.sqrt 3 / 2 + u.2 / 2)

lemma L_no_rotate60 (u : ℝ × ℝ) (hu : u ∈ L_set) (hrot : rotate60 u ∈ L_set) : u = 0 := by
  by_contra hu_nonzero;
  exact hu_nonzero <| L_set_rotation_60 u hu hrot

/-
If a vector u is in L and its -60 degree rotation is in L, then u is 0.
-/
noncomputable def rotate_neg60 (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 / 2 + u.2 * Real.sqrt 3 / 2, -u.1 * Real.sqrt 3 / 2 + u.2 / 2)

lemma L_no_rotate_neg60 (u : ℝ × ℝ) (hu : u ∈ L_set)
    (hrot : rotate_neg60 u ∈ L_set) : u = 0 := by
  apply L_set_rotation_neg_60 u hu hrot

/-
If p, q, r form an equilateral triangle, then r-p is a rotation of q-p by 60 or -60 degrees.
-/
lemma equilateral_euc_implies_rotation (p q r : ℝ × ℝ)
  (h_eq1 : dist_euc p q = dist_euc q r)
  (h_eq2 : dist_euc q r = dist_euc r p)
  (_h_neq : p ≠ q) :
  let u := (q.1 - p.1, q.2 - p.2)
  let v := (r.1 - p.1, r.2 - p.2)
  v = rotate60 u ∨ v = rotate_neg60 u := by
    unfold dist_euc at *;
    rw [ Real.sqrt_inj ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) )
      ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ] at *;
    norm_num [ Prod.ext_iff, rotate60, rotate_neg60 ];
    by_cases h_case : r.1 - p.1 = (q.1 - p.1) / 2 - (q.2 - p.2) * Real.sqrt 3 / 2 ∨
      r.1 - p.1 = (q.1 - p.1) / 2 + (q.2 - p.2) * Real.sqrt 3 / 2;
    · grind;
    · exact False.elim <| h_case <| Classical.or_iff_not_imp_left.2 fun h =>
        mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by
          ring_nf
          norm_num
          nlinarith;

/-
The lattice L contains no equilateral triangle (Euclidean version).
-/
lemma L_no_equilateral_euc (S : Finset (ℝ × ℝ)) (hS : (S : Set (ℝ × ℝ)) ⊆ L_set) :
    ¬ has_equilateral_triangle_euc S := by
      intro h;
      obtain ⟨ p, q, r, hp, hq, hr, hneq, hdist ⟩ := h;
      have h_rotate : let u := (q.1 - p.1, q.2 - p.2); let v := (r.1 - p.1,
        r.2 - p.2); v = rotate60 u ∨ v = rotate_neg60 u := by
        apply equilateral_euc_implies_rotation;
        · exact hdist.1;
        · exact hdist.2;
        · assumption;
      -- Since p, q, r ∈ L, u and v are in L.
      have h_u_v_in_L : (q.1 - p.1, q.2 - p.2) ∈ L_set ∧ (r.1 - p.1, r.2 - p.2) ∈ L_set := by
        have h_u_v_in_L : ∀ x ∈ S, ∀ y ∈ S, (x.1 - y.1, x.2 - y.2) ∈ L_set := by
          intros x hx y hy; exact L_set_sub_closed x y (hS hx) (hS hy);
        exact ⟨ h_u_v_in_L q ( hp ( by simp +decide ) ) p ( hp ( by simp +decide ) ),
          h_u_v_in_L r ( hp ( by simp +decide ) ) p ( hp ( by simp +decide ) ) ⟩;
      cases h_rotate <;> simp_all +decide;
      · have := L_no_rotate60 _ h_u_v_in_L.1 h_u_v_in_L.2;
        simp_all +decide [ Prod.ext_iff, sub_eq_zero ];
      · have := L_no_rotate_neg60 _ h_u_v_in_L.1 h_u_v_in_L.2
        simp_all +decide [ sub_eq_iff_eq_add ] ;
        exact hq ( Prod.ext this.1 this.2 ▸ rfl )

/-
Squared Euclidean distances in L are integers.
-/
lemma L_set_squared_dist_euc_is_int (p q : ℝ × ℝ) (hp : p ∈ L_set) (hq : q ∈ L_set) :
    ∃ n : ℤ, (dist_euc p q) ^ 2 = n := by
      unfold dist_euc;
      obtain ⟨ x, y, rfl, rfl ⟩ := hp
      obtain ⟨ u, v, rfl, rfl ⟩ := hq
      norm_num [ Real.sq_sqrt, add_nonneg, sq_nonneg ] ;
      norm_num [ latticePoint ];
      ring_nf; norm_num; norm_cast; aesop;

/-
The lattice L contains no set of points determining Euclidean distances in the golden ratio.
-/
lemma L_no_golden_ratio_euc (S : Finset (ℝ × ℝ)) (hS : (S : Set (ℝ × ℝ)) ⊆ L_set) :
    ¬ has_golden_ratio_distances_euc S := by
      rintro ⟨ d1, d2, hd1, hd2, h ⟩;
      -- Since S is in L, d1^2 and d2^2 are integers.
      obtain ⟨n1, hn1⟩ : ∃ n1 : ℤ, d1^2 = n1 := by
        unfold distinctDistances'_euc at hd1;
        norm_num +zetaDelta at *;
        rcases hd1.1 with ⟨ a, b, c, d, ⟨ ha, hb ⟩,
          rfl ⟩ ; exact L_set_squared_dist_euc_is_int _ _ ( hS ha ) ( hS hb ) ;
      obtain ⟨n2, hn2⟩ : ∃ n2 : ℤ, d2^2 = n2 := by
        unfold distinctDistances'_euc at hd2;
        norm_num +zetaDelta at *;
        rcases hd2.1 with ⟨ a, b, a', b', ⟨ ha, hb ⟩,
          rfl ⟩ ;
        exact L_set_squared_dist_euc_is_int ( a, b ) ( a', b' ) ( hS ha ) ( hS hb ) ;
      have h_phi_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = n1 / n2 := by
        rw [ ← hn1, ← hn2, h ];
        rw [ mul_pow, mul_div_cancel_left₀ _ ( pow_ne_zero 2 <| by
          rintro rfl
          exact absurd hd2 <| by
            unfold distinctDistances'_euc
            aesop ) ];
      exact False.elim <| Nat.Prime.irrational_sqrt ( show Nat.Prime 5 by norm_num )
        ⟨ ↑n1 / ↑n2 * 2 - 3, by
          push_cast [ ← h_phi_sq ]
          linarith [ Real.sq_sqrt <| show 0 ≤ 5 by norm_num ] ⟩

/-
The statement of Perucca's classification theorem.
-/
def PeruccaClassificationStatement : Prop :=
  ∀ (S : Finset (ℝ × ℝ)), S.card = 4 → (distinctDistances'_euc S).card = 2 →
    is_square_euc S ∨ has_equilateral_triangle_euc S ∨ has_golden_ratio_distances_euc S

/-
Every 4-point subset of P_m determines at least 3 distinct Euclidean distances (assuming Perucca's
classification).
-/
theorem P_local_constraint (m : ℕ) (h_perucca : PeruccaClassificationStatement) :
    ∀ S, S ⊆ (P m) → S.card = 4 → (distinctDistances'_euc S).card ≥ 3 := by
      intro S hS_sub hS_card
      by_contra h_contra;
      interval_cases _ : Finset.card ( distinctDistances'_euc S ) <;> simp_all +decide;
      · simp_all +decide [ Finset.ext_iff, distinctDistances'_euc ];
        have := Finset.one_lt_card.1 ( by linarith ) ; obtain ⟨ p, hp, q, hq,
          hpq ⟩ := this; specialize ‹∀ a x x_1 x_2 x_3 : ℝ, ( x, x_1 ) ∈ S → ( x_2,
          x_3 ) ∈ S → dist_euc ( x, x_1 ) ( x_2,
          x_3 ) = a → a = 0› _ _ _ _ _ hp hq rfl; simp_all +decide [ dist_euc ] ;
        exact hpq ( Prod.mk_inj.mpr ⟨ by rw [ Real.sqrt_eq_zero' ] at *; nlinarith,
          by rw [ Real.sqrt_eq_zero' ] at *; nlinarith ⟩ );
      · have := Finset.card_eq_one.mp ‹_›;
        -- If all pairs of points in S have the same distance, then any three points in S form an
        -- equilateral triangle.
        obtain ⟨a, ha⟩ := this
        have h_equilateral : ∀ p q r : ℝ × ℝ,
          p ∈ S → q ∈ S → r ∈ S → p ≠ q → q ≠ r → r ≠ p →
            dist_euc p q = dist_euc q r ∧
            dist_euc q r = dist_euc r p := by
          intros p q r hp hq hr hpq hqr hrp
          have h_dist_eq : dist_euc p q ∈ distinctDistances'_euc S ∧
            dist_euc q r ∈ distinctDistances'_euc S ∧
              dist_euc r p ∈ distinctDistances'_euc S := by
            simp [distinctDistances'_euc];
            exact ⟨
              ⟨ ⟨ p.1, p.2, q.1, q.2, ⟨ hp, hq ⟩, rfl ⟩,
                by
                  exact ne_of_gt ( Real.sqrt_pos.mpr ( by
                    exact not_le.mp fun h =>
                      hpq <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩ ) ) ⟩,
              ⟨ ⟨ q.1, q.2, r.1, r.2, ⟨ hq, hr ⟩, rfl ⟩,
                by
                  exact ne_of_gt ( Real.sqrt_pos.mpr ( by
                    exact not_le.mp fun h =>
                      hqr <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩ ) ) ⟩,
              ⟨ ⟨ r.1, r.2, p.1, p.2, ⟨ hr, hp ⟩, rfl ⟩,
                by
                  exact ne_of_gt ( Real.sqrt_pos.mpr ( by
                    exact not_le.mp fun h =>
                      hrp <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩ ) ) ⟩ ⟩;
          aesop;
        -- Let's choose any three points from S and show that they form an equilateral triangle.
        obtain ⟨p, q, r, hpS, hqS, hrS, hpq, hqr, hrp⟩ : ∃ p q r : ℝ × ℝ,
          p ∈ S ∧ q ∈ S ∧ r ∈ S ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p := by
          rcases Finset.two_lt_card.1 ( by linarith : 2 < Finset.card S ) with ⟨ p, hp, q, hq,
            hpq ⟩ ; use p, q ; aesop;
        have h_equilateral_triangle : has_equilateral_triangle_euc S := by
          use p, q, r;
          grind;
        exact absurd
          ( L_no_equilateral_euc S ( fun x hx => P_subset_L m <| hS_sub hx )
            h_equilateral_triangle )
          ( by tauto );
      · -- By Perucca's classification, S must be a square, contain an equilateral triangle, or
        -- have
        -- golden ratio distances.
        have h_perucca_applied : is_square_euc S ∨ has_equilateral_triangle_euc S ∨
          has_golden_ratio_distances_euc S := by
          exact h_perucca S hS_card ‹_›;
        contrapose! h_perucca_applied;
        exact ⟨
          fun h => L_no_square_euc S ( fun x hx => by
            have := hS_sub ( Finset.mem_coe.mp hx )
            exact P_subset_L m this ) h,
          fun h => L_no_equilateral_euc S ( fun x hx => by
            have := hS_sub ( Finset.mem_coe.mp hx )
            exact P_subset_L m this ) h,
          fun h => L_no_golden_ratio_euc S ( fun x hx => by
            have := hS_sub ( Finset.mem_coe.mp hx )
            exact P_subset_L m this ) h ⟩

/-
Characterization of points in P_m.
-/
lemma P_coords (m : ℕ) (p : ℝ × ℝ) (hp : p ∈ P m) :
    ∃ i j : ℕ, i < m ∧ j < m ∧ p = ((i : ℝ), Real.sqrt 2 * (j : ℝ)) := by
      unfold P at hp;
      unfold latticePoint at hp; erw [ Finset.mem_map ] at hp; obtain ⟨ x, hx,
        rfl ⟩ := hp; exact ⟨ x.1, x.2, Finset.mem_range.mp ( Finset.mem_product.mp hx |>.1 ),
        Finset.mem_range.mp ( Finset.mem_product.mp hx |>.2 ), rfl ⟩ ;

/-
Squared Euclidean distance between points in P_m is of the form u^2 + 2v^2 with |u|, |v| < m.
-/
lemma P_dist_sq_form (m : ℕ) (p q : ℝ × ℝ) (hp : p ∈ P m) (hq : q ∈ P m) :
    ∃ u v : ℤ, |u| < m ∧ |v| < m ∧ (dist_euc p q)^2 = u^2 + 2 * v^2 := by
      -- Let's unfold the definitions of P_coords and use the provided solution's approach.
      obtain ⟨i1, j1, hi1, hj1, hp_def⟩ : ∃ i1 j1 : ℕ,
        i1 < m ∧ j1 < m ∧ p = ((i1 : ℝ),
        Real.sqrt 2 * (j1 : ℝ)) := by
        exact P_coords m p hp
      obtain ⟨i2, j2, hi2, hj2, hq_def⟩ : ∃ i2 j2 : ℕ,
        i2 < m ∧ j2 < m ∧ q = ((i2 : ℝ),
        Real.sqrt 2 * (j2 : ℝ)) := by
        exact P_coords m q hq;
      -- Let's calculate the squared Euclidean distance between p and q.
      have h_dist_sq : (dist_euc p q) ^ 2 = (i1 - i2 : ℝ) ^ 2 + 2 * (j1 - j2 : ℝ) ^ 2 := by
        rw [ hp_def, hq_def, dist_euc ];
        rw [ Real.sq_sqrt <| by positivity ] ; ring_nf ; norm_num;
        ring;
      exact ⟨ i1 - i2, j1 - j2, abs_lt.mpr ⟨ by linarith, by linarith ⟩,
        abs_lt.mpr ⟨ by linarith, by linarith ⟩, by simpa using h_dist_sq ⟩

/-
The number of distinct Euclidean distances in P_m is bounded by B_Q(3m^2).
-/
theorem distinctDistances'_euc_bound (m : ℕ) (_hm : m ≥ 1) :
    (distinctDistances'_euc (P m)).card ≤ BinQuadForm.B Q_form (3 * m ^ 2) := by
      -- The number of distinct squared distances in P_m is at most the number of integers ≤ 3m^2
      -- represented by the quadratic form Q(u,v) = u^2 + 2v^2.
      have h_card_dist_sq : (distinctDistances'_euc (P m)).card ≤
          (Nat.card {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n}) := by
        -- By definition of $distinctDistances'_euc$, every element in $distinctDistances'_euc (P
        -- m)$ is a square root of an integer in the set $\{n \mid (n : ℝ) \leq 3 *
        -- m ^ 2 ∧ \exists
        -- u v : ℤ, (Q_form.eval u v : ℤ) = n\}$.
        have h_subset : ∀ d ∈ distinctDistances'_euc (P m),
          ∃ n ∈ {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n},
          d = Real.sqrt n := by
          intro d hd
          obtain ⟨p, q, hp, hq, hd_eq⟩ : ∃ p q : ℝ × ℝ,
            p ∈ P m ∧ q ∈ P m ∧ dist_euc p q = d := by
            unfold distinctDistances'_euc at hd;
            simp +zetaDelta at *;
            tauto;
          obtain ⟨ u, v, hu, hv, h ⟩ := P_dist_sq_form m p q hp hq;
          use Int.natAbs (u^2 + 2 * v^2);
          field_simp;
          constructor;
          · constructor;
            · norm_cast;
              nlinarith only [ abs_lt.mp hu, abs_lt.mp hv,
                abs_of_nonneg ( by positivity : 0 ≤ u ^ 2 + 2 * v ^ 2 ) ];
            · use u, v;
              unfold Q_form
              norm_num [ abs_of_nonneg ( by positivity : 0 ≤ u ^ 2 + 2 * v ^ 2 ) ] ;
              unfold BinQuadForm.eval; norm_num; ring;
          · norm_num [ ← hd_eq, ← h ];
            rw [ Real.sqrt_sq ( by exact Real.sqrt_nonneg _ ) ];
        have h_finite : Set.Finite {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n} := by
          exact Set.finite_iff_bddAbove.mpr
            ⟨ ⌊ ( 3 * m ^ 2 : ℝ ) ⌋₊, fun n hn => Nat.le_floor hn.1 ⟩
        have h_card : (distinctDistances'_euc (P m)).card ≤
            (Finset.image (fun n : ℕ => Real.sqrt n) (Set.Finite.toFinset h_finite)).card := by
          exact Finset.card_le_card fun x hx => by
            obtain ⟨ n, hn, rfl ⟩ := h_subset x hx
            exact Finset.mem_image.mpr ⟨ n, by aesop ⟩ ;
        generalize_proofs at *;
        exact h_card.trans ( Finset.card_image_le.trans ( by
          rw [ ← Nat.card_eq_finsetCard ]
          aesop ) );
      convert h_card_dist_sq using 1

/-
The quadratic form Q satisfies the conditions of Bernays' theorem.
-/
lemma Q_satisfies_bernays :
    let Δ := Q_form.discr
    (¬ ∃ z : ℤ, z * z = Δ) ∧ Q_form.Primitive ∧ Q_form.PosDef := by
      unfold Q_form;
      constructor;
      · unfold BinQuadForm.discr;
        exact fun ⟨ z, hz ⟩ => by
          norm_num [ BinQuadForm.b, BinQuadForm.a, BinQuadForm.c ] at hz
          nlinarith
      · exact ⟨ by trivial, by trivial ⟩

/-
m_of_n(n) squared is at least n.
-/
noncomputable def m_of_n (n : ℕ) : ℕ := Nat.sqrt n + 1

lemma m_of_n_sq_ge_n (n : ℕ) : (m_of_n n) ^ 2 ≥ n := by
  exact Nat.le_of_lt ( Nat.lt_succ_sqrt' _ )

/-
Sequence of sets P_n with |P_n| = n.
-/
noncomputable def P_seq (n : ℕ) : Finset (ℝ × ℝ) :=
  if h : n = 0 then ∅ else
  let m := m_of_n n
  let S := P m
  have h_card : n ≤ S.card := by
    rw [ show S.card = m ^ 2 by
          erw [ Finset.card_map, Finset.card_product ] ; norm_num ; ring ];
    exact m_of_n_sq_ge_n n
  (Finset.exists_subset_card_eq h_card).choose

/-
Properties of P_seq.
-/
lemma P_seq_spec (n : ℕ) : (P_seq n).card = n ∧ P_seq n ⊆ P (m_of_n n) := by
  unfold P_seq;
  split_ifs <;> simp_all +decide;
  have := Finset.exists_subset_card_eq ( show n ≤ ( P ( m_of_n n ) |> Finset.card ) from ?_ );
  · exact ⟨ this.choose_spec.2, this.choose_spec.1 ⟩;
  · unfold P m_of_n;
    norm_num +zetaDelta at *;
    linarith [ Nat.lt_succ_sqrt n ]

/-
Main theorem: Existence of sets P_n satisfying the local constraint and the distinct distance bound.
-/
theorem main_theorem (h_perucca : PeruccaClassificationStatement)
    (h_bernays : ∀ (Δ : ℤ) (_hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ),
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x))) :
    ∃ (P : ℕ → Finset (ℝ × ℝ)),
      (∀ n, (P n).card = n) ∧
      (∀ n, n ≥ 4 → ∀ S, S ⊆ P n → S.card = 4 →
        (distinctDistances'_euc S).card ≥ 3) ∧
      (Asymptotics.IsBigO Filter.atTop (fun n => ((distinctDistances'_euc (P n)).card : ℝ))
        (fun n => (n : ℝ) / Real.sqrt (Real.log n))) := by
          -- Apply Bernays' theorem to the quadratic form Q.
          obtain ⟨CΔ, hCΔ_pos, hCΔ⟩ : ∃ CΔ : ℝ,
            0 < CΔ ∧ (fun x => (Q_form.B x : ℝ)) ~[Filter.atTop]
              (fun x => CΔ * x / Real.sqrt (Real.log x)) := by
            exact h_bernays _
              (by
                rintro ⟨ z, hz ⟩
                nlinarith [ show z ≤ 2 by nlinarith, show z ≥ -2 by nlinarith ])
              |> fun ⟨ CΔ, hCΔ₁, hCΔ₂ ⟩ =>
                ⟨ CΔ, hCΔ₁, hCΔ₂ _ Q_form_primitive Q_form_posDef Q_form_discr ⟩;
          refine ⟨ fun n => P_seq n, ?_, ?_, ?_ ⟩;
          · exact fun n => P_seq_spec n |>.1;
          · intro n hn S hS hS_card
            have h_subset : S ⊆ P (m_of_n n) := by
              exact hS.trans ( P_seq_spec n |>.2 );
            exact P_local_constraint (m_of_n n) h_perucca S h_subset hS_card;
          · -- Since $B_Q(3 * (m_of_n n)^2) \leq B_Q(3n + 6\sqrt{n} + 3)$, we can
            -- use the bound from
            -- Bernays' theorem.
            have h_bound : ∀ n : ℕ,
              n ≥ 1 →
                (distinctDistances'_euc (P_seq n)).card ≤
                  (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) := by
              intros n hn
              have h_bound : (distinctDistances'_euc (P_seq n)).card ≤
                  (Q_form.B (3 * (m_of_n n) ^ 2) : ℝ) := by
                have h_bound : (distinctDistances'_euc (P_seq n)).card ≤
                    (distinctDistances'_euc (P (m_of_n n))).card := by
                  have h_subset : P_seq n ⊆ P (m_of_n n) := by
                    exact P_seq_spec n |>.2;
                  apply_rules [ Finset.card_le_card ];
                  simp_all +decide [ Finset.subset_iff ];
                  unfold distinctDistances'_euc; aesop;
                exact_mod_cast h_bound.trans ( distinctDistances'_euc_bound _ <| Nat.succ_pos _ );
              refine le_trans h_bound ?_;
              refine Nat.cast_le.mpr ?_;
              refine Nat.card_mono ?_ ?_;
              · refine Set.finite_iff_bddAbove.mpr ⟨ ⌊3 * n + 6 * Real.sqrt n + 3⌋₊,
                fun x hx => Nat.le_floor <| hx.1 ⟩;
              · refine fun x hx => ⟨ ?_, hx.2 ⟩;
                refine le_trans hx.1 ?_;
                norm_num [ m_of_n ];
                nlinarith only [ show ( n.sqrt : ℝ ) ^ 2 ≤ n by exact_mod_cast Nat.sqrt_le' n,
                  Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n,
                  show ( n.sqrt : ℝ ) ≥ 0 by positivity ];
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log(3n + 6\sqrt{n} + 3)}$.
            have h_bernays_bound : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                CΔ * (3 * n + 6 * Real.sqrt n + 3) /
                  Real.sqrt (Real.log (3 * n + 6 * Real.sqrt n + 3)) * 2 := by
              have h_bernays_bound : ∀ᶠ x in Filter.atTop,
                (Q_form.B x : ℝ) ≤ CΔ * x / Real.sqrt (Real.log x) * 2 := by
                have := hCΔ.def ( show 0 < 1 by norm_num );
                filter_upwards [ this, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
                norm_num [ abs_of_nonneg, div_nonneg, Real.sqrt_nonneg, hCΔ_pos.le,
                  hx₂.le ] at hx₁ ⊢;
                rw [ abs_of_nonneg ( by positivity : 0 ≤ x ) ] at hx₁
                linarith [ abs_le.mp hx₁ ];
              rw [ Filter.eventually_atTop ] at *;
              obtain ⟨ a, ha ⟩ := h_bernays_bound
              use Max.max a 1
              intro b hb
              specialize ha ( 3 * b + 6 * Real.sqrt b + 3 )
                ( by linarith [ le_max_left a 1, le_max_right a 1, Real.sqrt_nonneg b ] )
              aesop;
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log(3n + 6\sqrt{n} + 3)}$ for sufficiently large $n$.
            have h_bernays_bound_simplified : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                CΔ * (3 * n + 6 * Real.sqrt n + 3) / Real.sqrt (Real.log n) * 2 := by
              filter_upwards [ h_bernays_bound,
                Filter.eventually_gt_atTop 1 ] with n hn hn' using
                le_trans hn ( mul_le_mul_of_nonneg_right
                  ( div_le_div_of_nonneg_left ( by positivity )
                    ( Real.sqrt_pos.mpr <| Real.log_pos <| by linarith ) <|
                      Real.sqrt_le_sqrt <| Real.log_le_log ( by positivity ) <|
                        by linarith [ Real.sqrt_nonneg n ] )
                  zero_le_two );
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log n}$ for sufficiently large $n$.
            have h_bernays_bound_final : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                12 * CΔ * n / Real.sqrt (Real.log n) := by
              filter_upwards [ h_bernays_bound_simplified,
                Filter.eventually_gt_atTop 16 ] with n hn hn';
              refine le_trans hn ?_;
              rw [ div_mul_eq_mul_div,
                div_le_div_iff_of_pos_right ( Real.sqrt_pos.mpr <| Real.log_pos <| by linarith ) ];
              nlinarith [ sq_nonneg ( Real.sqrt n - 4 ),
                Real.mul_self_sqrt ( show 0 ≤ n by linarith ), Real.sqrt_nonneg n,
                mul_le_mul_of_nonneg_left
                  ( show Real.sqrt n ≤ n / 2 by
                    nlinarith [ sq_nonneg ( Real.sqrt n - 4 ),
                      Real.mul_self_sqrt ( show 0 ≤ n by linarith ), Real.sqrt_nonneg n ] )
                  hCΔ_pos.le ];
            rw [ Asymptotics.isBigO_iff ];
            exact ⟨ 12 * CΔ, by
              filter_upwards [ Filter.eventually_ge_atTop 1,
                h_bernays_bound_final.natCast_atTop ] with n hn hn'
              rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ),
                Real.norm_of_nonneg ( by positivity ) ]
              exact le_trans ( h_bound n hn ) ( by simpa [ mul_div_assoc ] using hn' ) ⟩

/-
Helper lemma 2: A rhombus with equal diagonals is a square. Specifically, if 4 points have sides a,
a, a, a and diagonals b, b, then b = a * sqrt(2).
-/
lemma configuration_4_2_implies_square (p1 p2 p3 p4 : ℝ × ℝ) (a b : ℝ)
    (h_distinct : p1 ≠ p2 ∧ p2 ≠ p3 ∧ p3 ≠ p4 ∧ p4 ≠ p1 ∧ p1 ≠ p3 ∧ p2 ≠ p4)
    (ha : a > 0) (hb : b > 0) (hab : a ≠ b)
    (h12 : dist_euc p1 p2 = a) (h23 : dist_euc p2 p3 = a)
    (h34 : dist_euc p3 p4 = a) (h41 : dist_euc p4 p1 = a)
    (h13 : dist_euc p1 p3 = b) (h24 : dist_euc p2 p4 = b) :
    b = a * Real.sqrt 2 := by
      unfold dist_euc at *;
      rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> try linarith;
      -- By contradiction, assume $b \neq a \sqrt{2}$.
      by_contra h_contra;
      -- By expanding and simplifying, we can derive that $b^2 = 2a^2$.
      have h_b_sq : b^2 = 2 * a^2 := by
        by_cases h_eq : p1.1 = p3.1;
        · by_cases h_eq2 : p2.2 = p4.2;
          · grind;
          · grind;
        · grind;
      exact h_contra ( by
        nlinarith only [ ha, hb, h_b_sq, show 0 < a * Real.sqrt 2 by positivity,
          Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] )

/-
Roots of the polynomial t ^ 3 - 2 * t ^ 2 - 2 * t + 1 are -1, (3+sqrt(5))/2,
and (3-sqrt(5))/2.
-/
lemma golden_polynomial_roots (t : ℝ) (h : t ^ 3 - 2 * t ^ 2 - 2 * t + 1 = 0) :
    t = -1 ∨ t = (3 + Real.sqrt 5) / 2 ∨ t = (3 - Real.sqrt 5) / 2 := by
      exact Classical.or_iff_not_imp_left.2 fun h' =>
        Classical.or_iff_not_imp_left.2 fun h'' =>
          mul_left_cancel₀ ( sub_ne_zero_of_ne h' ) <|
            mul_left_cancel₀ ( sub_ne_zero_of_ne h'' ) <| by
              ring_nf
              norm_num
              nlinarith;

/-
Algebraic helper: roots of 2(1-x) = (2x-1)^2 are (1 ± sqrt(5))/4.
-/
lemma solve_golden_equation (x : ℝ) (h : 2 * (1 - x) = (2 * x - 1) ^ 2) :
    x = (1 + Real.sqrt 5) / 4 ∨ x = (1 - Real.sqrt 5) / 4 := by
      grind

/-
Algebraic helper: 2(1-x) = 5-4x has no solution with x <= 1.
-/
lemma solve_impossible_equation (x : ℝ) (h1 : 2 * (1 - x) = 5 - 4 * x)
    (h2 : x ≤ 1) : False := by
  linarith

/-
Helper lemma 1: A specific 3-3 distance configuration implies the golden ratio.
-/
lemma configuration_3_3_implies_golden (p1 p2 p3 p4 : ℝ × ℝ) (a b : ℝ)
    (_h_distinct : p1 ≠ p2 ∧ p2 ≠ p3 ∧ p3 ≠ p4 ∧ p1 ≠ p3 ∧ p2 ≠ p4 ∧ p1 ≠ p4)
    (ha : a > 0) (hb : b > 0) (hab : a ≠ b)
    (h12 : dist_euc p1 p2 = a) (h23 : dist_euc p2 p3 = a) (h34 : dist_euc p3 p4 = a)
    (h13 : dist_euc p1 p3 = b) (h24 : dist_euc p2 p4 = b) (h14 : dist_euc p1 p4 = b) :
    b = a * ((1 + Real.sqrt 5) / 2) ∨ a = b * ((1 + Real.sqrt 5) / 2) := by
      -- Squaring both sides of each distance equation, we get $a^2 = (p1.1 - p2.1)^2 + (p1.2 -
      -- p2.2)^2$, $a^2 = (p2.1 - p3.1)^2 + (p2.2 - p3.2)^2$, $a^2 = (p3.1 - p4.1)^2 + (p3.2 -
      -- p4.2)^2$, $b^2 = (p1.1 - p3.1)^2 + (p1.2 - p3.2)^2$, $b^2 = (p2.1 - p4.1)^2 + (p2.2 -
      -- p4.2)^2$, and $b^2 = (p1.1 - p4.1)^2 + (p1.2 - p4.2)^2$.
      have h_sq_eqs : a^2 = (p1.1 - p2.1)^2 + (p1.2 - p2.2)^2 ∧
        a^2 = (p2.1 - p3.1)^2 + (p2.2 - p3.2)^2 ∧ a^2 = (p3.1 - p4.1)^2 + (p3.2 - p4.2)^2 ∧
        b^2 = (p1.1 - p3.1)^2 + (p1.2 - p3.2)^2 ∧ b^2 = (p2.1 - p4.1)^2 + (p2.2 - p4.2)^2 ∧
        b^2 = (p1.1 - p4.1)^2 + (p1.2 - p4.2)^2 := by
        unfold dist_euc at *;
        exact ⟨ by rw [ ← h12, Real.sq_sqrt <| by positivity ], by rw [ ← h23,
          Real.sq_sqrt <| by positivity ], by rw [ ← h34, Real.sq_sqrt <| by positivity ],
          by rw [ ← h13, Real.sq_sqrt <| by positivity ], by rw [ ← h24,
          Real.sq_sqrt <| by positivity ], by rw [ ← h14, Real.sq_sqrt <| by positivity ] ⟩;
      -- Let's assume without loss of generality that $p_2 = (0, 0)$ and $p_3 = (a, 0)$.
      suffices h_wlog : ∀ (p1 p2 p3 p4 : ℝ × ℝ), p2 = (0, 0) → p3 = (a,
        0) → a > 0 → b > 0 → a ≠ b → (dist_euc p1 p2 = a ∧ dist_euc p2 p3 = a ∧
          dist_euc p3 p4 = a ∧ dist_euc p1 p3 = b ∧ dist_euc p2 p4 = b ∧
            dist_euc p1 p4 = b) →
          b = a * ((1 + Real.sqrt 5) / 2) ∨ a = b * ((1 + Real.sqrt 5) / 2) by
        -- By translating and rotating the points, we can assume without loss of generality that
        -- $p_2 = (0, 0)$ and $p_3 = (a, 0)$.
        obtain ⟨θ, hθ⟩ : ∃ θ : ℝ,
          p3.1 - p2.1 = a * Real.cos θ ∧ p3.2 - p2.2 = a * Real.sin θ := by
          use ( Complex.arg ( p3.1 - p2.1 + ( p3.2 - p2.2 ) * Complex.I ) );
          rw [ Complex.cos_arg, Complex.sin_arg ] <;> norm_num [ Complex.ext_iff ];
          · norm_num [ Complex.normSq, Complex.norm_def ];
            norm_num [ ← sq, h_sq_eqs.2.1.symm, ha.le, hb.le ];
            norm_num [ show ( p3.1 - p2.1 ) ^ 2 + ( p3.2 - p2.2 ) ^ 2 = a ^ 2 by linarith ];
            norm_num [ ha.le, ha.ne', mul_div_cancel₀ ];
          · intro h1 h2; simp_all +decide [ sub_eq_iff_eq_add ] ;
        contrapose! h_wlog;
        use ( ( p1.1 - p2.1 ) * Real.cos θ + ( p1.2 - p2.2 ) * Real.sin θ,
          - ( p1.1 - p2.1 ) * Real.sin θ + ( p1.2 - p2.2 ) * Real.cos θ ), ( 0, 0 ), ( a, 0 ),
          ( ( p4.1 - p2.1 ) * Real.cos θ + ( p4.2 - p2.2 ) * Real.sin θ,
          - ( p4.1 - p2.1 ) * Real.sin θ + ( p4.2 - p2.2 ) * Real.cos θ )
        simp_all +decide ;
        unfold dist_euc at *; simp_all +decide ;
        refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩ <;>
          rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] <;>
          try linarith;
        · nlinarith only [ h_sq_eqs.1, Real.sin_sq_add_cos_sq θ ];
        · grind +ring;
        · grind;
        · ring_nf at *;
          rw [ Real.sin_sq, Real.cos_sq ] ; ring_nf at * ; linarith;
        · rw [ ← sq, h_sq_eqs.2.2.2.2.2 ] ; ring_nf;
          rw [ Real.sin_sq, Real.cos_sq ] ; ring;
      intros p1 p2 p3 p4 hp2 hp3 ha hb hab h_eqs
      have h_coords : ∃ x1 y1 x4 y4 : ℝ, p1 = (x1, y1) ∧ p4 = (x4,
        y4) ∧ x1^2 + y1^2 = a^2 ∧ (x1 - a)^2 + y1^2 = b^2 ∧ (x4 - a)^2 + y4^2 = a^2 ∧
          x4^2 + y4^2 = b^2 ∧ (x1 - x4)^2 + (y1 - y4)^2 = b^2 := by
        have h_coords : ∀ (p q : ℝ × ℝ),
          dist_euc p q = Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2) := by
          exact fun p q => rfl;
        simp_all +decide [ Real.sqrt_eq_iff_mul_self_eq_of_pos ];
        exact ⟨ p1.1, p1.2, rfl, p4.1, p4.2, rfl, by linarith, by linarith, by linarith,
          by linarith, by linarith ⟩;
      -- Let's consider the two cases: $y1 = y4$ and $y1 = -y4$.
      obtain ⟨x1, y1, x4, y4, hp1, hp4, h1, h2, h3, h4, h5⟩ := h_coords
      by_cases hy : y1 = y4;
      · -- By solving the system of equations given by h1, h2, h3, and h4, we can find the
        -- relationship between a and b.
        have h_rel : b^2 = a^2 - a * b ∨ b^2 = a^2 + a * b := by
          grind;
        rcases h_rel with h_rel | h_rel;
        · exact Or.inr <| by
            nlinarith only [ ha, hb, h_rel, show 0 < a * Real.sqrt 5 by positivity,
              show 0 < b * Real.sqrt 5 by positivity, Real.sqrt_nonneg 5,
              Real.sq_sqrt <| show 0 ≤ 5 by norm_num ]
        · exact Or.inl <| by
            nlinarith only [ ha, hb, h_rel, show 0 < a * Real.sqrt 5 by positivity,
              show 0 < b * Real.sqrt 5 by positivity, Real.sqrt_nonneg 5,
              Real.sq_sqrt <| show 0 ≤ 5 by norm_num ]
      · -- If $y1 \neq y4$, then $y1 = -y4$.
        have hy_neg : y1 = -y4 := by
          grind;
        subst hy_neg;
        nlinarith [ mul_pos ha hb ]

/-
Definition of C4+2K2 configuration: 4 points forming a rhombus with sides a and diagonals b.
-/
def is_C4_2K2 (S : Finset (ℝ × ℝ)) (a b : ℝ) : Prop :=
  ∃ p1 p2 p3 p4, S = {p1, p2, p3, p4} ∧ p1 ≠ p2 ∧ p2 ≠ p3 ∧
  p3 ≠ p4 ∧ p4 ≠ p1 ∧ p1 ≠ p3 ∧ p2 ≠ p4 ∧ dist_euc p1 p2 = a ∧
  dist_euc p2 p3 = a ∧ dist_euc p3 p4 = a ∧ dist_euc p4 p1 = a ∧
  dist_euc p1 p3 = b ∧ dist_euc p2 p4 = b

/-
Definition of P4+P4 configuration: 4 points where one distance forms a path of length 3, and the
other distance forms the complement (also a path of length 3).
-/
def is_P4_P4 (S : Finset (ℝ × ℝ)) (a b : ℝ) : Prop :=
  ∃ p1 p2 p3 p4, S = {p1, p2, p3, p4} ∧ p1 ≠ p2 ∧ p2 ≠ p3 ∧
  p3 ≠ p4 ∧ p1 ≠ p3 ∧ p2 ≠ p4 ∧ p1 ≠ p4 ∧ dist_euc p1 p2 = a ∧
  dist_euc p2 p3 = a ∧ dist_euc p3 p4 = a ∧ dist_euc p1 p3 = b ∧
  dist_euc p2 p4 = b ∧ dist_euc p1 p4 = b

/-
Lemma: A C4+2K2 configuration implies a square.
-/
lemma C4_2K2_implies_square (S : Finset (ℝ × ℝ)) (a b : ℝ) (ha : a > 0)
    (hb : b > 0) (hab : a ≠ b) (h : is_C4_2K2 S a b) : is_square_euc S := by
  rcases h with ⟨ p1, p2, p3, p4, rfl, h1, h2, h3, h4, h5, h6 ⟩;
  have h_square : b = a * Real.sqrt 2 := by
    apply configuration_4_2_implies_square p1 p2 p3 p4 a b
    · aesop
    all_goals tauto
  refine ⟨ p1, p2, p3, p4, ?_, ?_, ?_, ?_, ?_ ⟩ <;> aesop

/-
Lemma: A P4+P4 configuration implies golden ratio distances.
-/
lemma P4_P4_implies_golden (S : Finset (ℝ × ℝ)) (a b : ℝ) (ha : a > 0)
    (hb : b > 0) (hab : a ≠ b) (h : is_P4_P4 S a b) :
    has_golden_ratio_distances_euc S := by
  -- Apply configuration_3_3_implies_golden to conclude the existence of distances in the golden
  -- ratio.
  obtain ⟨p1, p2, p3, p4, hS, h_distinct, h12, h23, h34, h13, h24, h14⟩ := h;
  have h_gold : b = a * ((1 + Real.sqrt 5) / 2) ∨ a = b * ((1 + Real.sqrt 5) / 2) := by
    have := configuration_3_3_implies_golden p1 p2 p3 p4 a b ⟨ h_distinct, h12, h23, h34, h13,
      h24 ⟩ ha hb hab; aesop;
  use if b = a * ((1 + Real.sqrt 5) / 2) then b else a,
    if b = a * ((1 + Real.sqrt 5) / 2) then a else b;
  split_ifs <;> simp_all +decide [ distinctDistances'_euc ];
  · exact ⟨
      ⟨ ⟨ p1.1, p1.2, p3.1, p3.2, by aesop ⟩, by positivity, by positivity ⟩,
      ⟨ ⟨ p1.1, p1.2, p2.1, p2.2, by aesop ⟩, by positivity ⟩ ⟩;
  · exact ⟨
      ⟨ ⟨ p1.1, p1.2, p2.1, p2.2, by aesop ⟩, by positivity, by positivity ⟩,
      ⟨ ⟨ p1.1, p1.2, p3.1, p3.2, by aesop ⟩, by positivity ⟩ ⟩

/-
Helper lemma: A graph on 4 vertices with no monochromatic triangle of color 'a' has at most 4 edges
of color 'a'.
-/
lemma four_vertex_oriented_edge_bound
    (e01 e02 e03 e12 e13 e23 : Prop)
    [Decidable e01] [Decidable e02] [Decidable e03]
    [Decidable e12] [Decidable e13] [Decidable e23]
    (h012 : ¬ (e01 ∧ e02 ∧ e12))
    (h013 : ¬ (e01 ∧ e03 ∧ e13))
    (h023 : ¬ (e02 ∧ e03 ∧ e23))
    (h123 : ¬ (e12 ∧ e13 ∧ e23)) :
    (if e01 then 2 else 0) + (if e02 then 2 else 0) + (if e03 then 2 else 0) +
      (if e12 then 2 else 0) + (if e13 then 2 else 0) + (if e23 then 2 else 0) ≤ 8 := by
  by_cases e01 <;> by_cases e02 <;> by_cases e03 <;>
    by_cases e12 <;> by_cases e13 <;> by_cases e23 <;>
    simp_all

lemma num_edges_le_4_of_no_triangle (S : Finset (ℝ × ℝ)) (d : ℝ)
    (h4 : S.card = 4)
    (h_no_triangle : ¬ ∃ p q r, {p, q, r} ⊆ S ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p ∧
      dist_euc p q = d ∧ dist_euc q r = d ∧ dist_euc r p = d) :
    (S.offDiag.filter (fun (x, y) => dist_euc x y = d)).card ≤ 8 := by
  classical
  let G : SimpleGraph S := {
    Adj := fun (x y : S) => x ≠ y ∧ dist_euc x.1 y.1 = d
    symm := by
      intro x y h
      exact ⟨h.1.symm, by rw [dist_euc_comm]; exact h.2⟩
    loopless := ⟨fun _ h => h.1 rfl⟩
  }
  have h_directed :
      (S.offDiag.filter (fun (x, y) => dist_euc x y = d)).card =
        ((Finset.univ : Finset (S × S)).filter fun xy => G.Adj xy.1 xy.2).card := by
    have hS_nonempty : S.Nonempty := by
      apply Finset.card_pos.mp
      omega
    let defaultS : S := ⟨hS_nonempty.choose, hS_nonempty.choose_spec⟩
    let toS (p : ℝ × ℝ) : S := if hp : p ∈ S then ⟨p, hp⟩ else defaultS
    let i (xy : (ℝ × ℝ) × (ℝ × ℝ)) : S × S := (toS xy.1, toS xy.2)
    refine Finset.card_nbij i ?_ ?_ ?_
    · intro xy hxy
      rcases Finset.mem_filter.mp hxy with ⟨hxy_off, hxy_dist⟩
      rcases Finset.mem_offDiag.mp hxy_off with ⟨hxS, hyS, _⟩
      rcases Finset.mem_offDiag.mp hxy_off with ⟨_, _, hne⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp [i, toS, G, hxS, hyS, hne, hxy_dist]
    · intro xy₁ hxy₁ xy₂ hxy₂ heq
      rcases Finset.mem_filter.mp hxy₁ with ⟨hxy₁_off, _⟩
      rcases Finset.mem_offDiag.mp hxy₁_off with ⟨hx₁S, hy₁S, _⟩
      rcases Finset.mem_filter.mp hxy₂ with ⟨hxy₂_off, _⟩
      rcases Finset.mem_offDiag.mp hxy₂_off with ⟨hx₂S, hy₂S, _⟩
      have hx_eq := congrArg (fun z : S × S => (z.1 : ℝ × ℝ)) heq
      have hy_eq := congrArg (fun z : S × S => (z.2 : ℝ × ℝ)) heq
      simp [i, toS, hx₁S, hx₂S] at hx_eq
      simp [i, toS, hy₁S, hy₂S] at hy_eq
      exact Prod.ext hx_eq hy_eq
    · intro xy hxy
      rcases xy with ⟨x, y⟩
      have hAdj : G.Adj x y := (Finset.mem_filter.mp hxy).2
      refine ⟨(x.1, y.1), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨x.2, y.2, fun h => hAdj.1 (Subtype.ext h)⟩, hAdj.2⟩
      · ext <;> simp [i, toS]
  have h_clique_free : G.CliqueFree 3 := by
    intro t ht
    rw [SimpleGraph.is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := ht
    apply h_no_triangle
    refine ⟨a.1, b.1, c.1, ?_, ?_, ?_, ?_, hab.2, hbc.2, ?_⟩
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl <;> simp
    · exact fun h => hab.1 (Subtype.ext h)
    · exact fun h => hbc.1 (Subtype.ext h)
    · exact fun h => hac.1 ((Subtype.ext h).symm)
    · rw [dist_euc_comm]
      exact hac.2
  have h_edge_le : G.edgeFinset.card ≤ 4 := by
    have hT := SimpleGraph.CliqueFree.card_edgeFinset_le (G := G) (r := 2) h_clique_free
    simpa [Fintype.card_coe, h4] using hT
  calc
    (S.offDiag.filter (fun (x, y) => dist_euc x y = d)).card =
        2 * G.edgeFinset.card := by
          rw [h_directed]
          exact (SimpleGraph.two_mul_card_edgeFinset (G := G)).symm
    _ ≤ 8 := by omega

/-
Lemma: If a vertex is connected to 3 others by distance 'a', then there is a monochromatic triangle.
-/
lemma star_graph_implies_triangle (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (p : ℝ × ℝ) (hp : p ∈ S)
    (h_star : ∀ q ∈ S, q ≠ p → dist_euc p q = a) :
    has_equilateral_triangle_euc S := by
      -- Let $N = S \setminus \{p\}$. Since $|S|=4$, $|N|=3$.
      set N := S \ {p} with hN_def
      have hN_card : N.card = 3 := by
        rw [ Finset.card_sdiff ] ; aesop;
      -- Let $q, r, s$ be the elements of $N$.
      obtain ⟨q, r, s, hq, hr, hs, hN⟩ : ∃ q r s,
        q ∈ N ∧ r ∈ N ∧ s ∈ N ∧ q ≠ r ∧ r ≠ s ∧ s ≠ q := by
        rcases Finset.card_eq_three.mp hN_card with ⟨ q, r, s, hq, hr, hs ⟩
        use q, r, s
        aesop;
      -- If for all pairs in $N$, the distance is not $a$, then for all pairs the distance is $b$.
      by_cases h_all_b : dist_euc q r = b ∧ dist_euc r s = b ∧ dist_euc s q = b;
      · use q, r, s;
        aesop_cat;
      · -- If for any pair in $N$, the distance is $a$, then $\{p, x, y\}$ forms an equilateral
        -- triangle of side $a$.
        obtain ⟨x, y, hxN, hyN, hxy⟩ : ∃ x y,
          x ∈ N ∧ y ∈ N ∧ x ≠ y ∧ dist_euc x y = a := by
          grind;
        use p, x, y;
        simp_all +decide [ Finset.subset_iff, dist_euc ];
        exact ⟨ Ne.symm hxN.2, by rw [ ← h_star _ _ hyN.1 hyN.2 ] ; ring_nf ⟩

/-
Definition of edge count for a given distance, and lemma stating that the sum of edge counts for
distances a and b in a 4-point set is 12 (since there are 12 directed edges in total).
-/
noncomputable def edge_count (S : Finset (ℝ × ℝ)) (r : ℝ) : ℕ :=
  (S.offDiag.filter (fun (x, y) => dist_euc x y = r)).card

lemma edge_count_sum (S : Finset (ℝ × ℝ)) (a b : ℝ) (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b) :
    edge_count S a + edge_count S b = 12 := by
      -- Since there are 4 points, the total number of edges is 4 * 3 = 12.
      have h_total_edges : (Finset.offDiag S).card = 12 := by
        norm_num [ h4 ];
      rw [ ← h_total_edges,
        show edge_count S a =
          Finset.card
            ( Finset.filter ( fun x => dist_euc x.1 x.2 = a ) ( Finset.offDiag S ) ) from rfl,
        show edge_count S b =
          Finset.card
            ( Finset.filter ( fun x => dist_euc x.1 x.2 = b ) ( Finset.offDiag S ) ) from rfl,
        ← Finset.card_union_of_disjoint ];
      · congr with x ; aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => hab <| by linarith

/-
Lemma: If a graph on 4 vertices has 4 edges of color 'a' and no monochromatic triangle, it is a C4
(cycle of length 4) in color 'a'.
-/
lemma C4_of_edge_count_8 (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (h_count : edge_count S a = 8)
    (h_no_tri : ¬ has_equilateral_triangle_euc S) :
    is_C4_2K2 S a b := by
      -- Since $G_a$ has no triangle and its edge count is 4, it has a star graph by
      -- Lemma~\ref{lem:star_graph_implies_triangle}. Therefore, every vertex in $G_a$ has degree 2.
      have h_deg2 : ∀ p ∈ S,
          (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card = 2 := by
        have h_deg2 : ∀ p ∈ S,
          (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card ≤ 2 := by
          intro p hp
          by_contra h_contra;
          obtain ⟨q1, q2, q3, hq1, hq2, hq3, h_distinct⟩ : ∃ q1 q2 q3,
            q1 ∈ S ∧ q2 ∈ S ∧ q3 ∈ S ∧ q1 ≠ q2 ∧ q2 ≠ q3 ∧ q3 ≠ q1 ∧
              q1 ≠ p ∧ q2 ≠ p ∧ q3 ≠ p ∧
              dist_euc p q1 = a ∧ dist_euc p q2 = a ∧ dist_euc p q3 = a := by
            obtain ⟨ s, hs ⟩ := Finset.two_lt_card.mp ( lt_of_not_ge h_contra );
            obtain ⟨ hs₁, t, ht₁, u, hu₁, hst, hsu, htu ⟩ := hs; use s, t, u; aesop;
          have h_triangle : has_equilateral_triangle_euc S := by
            apply star_graph_implies_triangle S a b h4 h_dist hab p hp;
            have h_triangle : (S.erase p).card = 3 := by
              rw [ Finset.card_erase_of_mem hp, h4 ];
            rw [ Finset.card_eq_three ] at h_triangle;
            obtain ⟨ x, y, z, hxy, hxz, hyz,
              h ⟩ := h_triangle; simp_all +decide [ Finset.Subset.antisymm_iff,
              Finset.subset_iff ] ;
            grind +ring;
          contradiction;
        have h_deg2 : ∑ p ∈ S,
          (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card = 8 := by
          have h_degree_sum :
              ∑ p ∈ S, (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card =
                edge_count S a := by
            let T : Finset (Σ p : ℝ × ℝ, ℝ × ℝ) :=
              S.sigma (fun p => (S.erase p).filter (fun q => dist_euc p q = a))
            have hT_card :
                T.card =
                  ∑ p ∈ S, (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card := by
              simp [T, Finset.sigma, Finset.card]
            rw [← hT_card]
            unfold edge_count
            refine Finset.card_bij (fun x hx => (x.1, x.2)) ?_ ?_ ?_
            · intro x hx
              rcases Finset.mem_sigma.mp hx with ⟨hpS, hq⟩
              rcases Finset.mem_filter.mp hq with ⟨hqerase, hpq⟩
              rcases Finset.mem_erase.mp hqerase with ⟨hqp, hqS⟩
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_offDiag.mpr ⟨hpS, hqS, hqp.symm⟩, hpq⟩
            · intro x hx y hy hxy
              cases x
              cases y
              simp at hxy
              simp [hxy]
            · intro y hy
              rcases y with ⟨p, q⟩
              rcases Finset.mem_filter.mp hy with ⟨hoff, hpq⟩
              rcases Finset.mem_offDiag.mp hoff with ⟨hpS, hqS, hpne⟩
              refine ⟨⟨p, q⟩, ?_, rfl⟩
              exact Finset.mem_sigma.mpr
                ⟨hpS,
                  Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpne.symm, hqS⟩, hpq⟩⟩
          rw [h_degree_sum, h_count]
        contrapose! h_deg2;
        exact ne_of_lt ( lt_of_lt_of_le
          ( Finset.sum_lt_sum ( fun x hx => by aesop ) ( show ∃ x, x ∈ S ∧
              Finset.card
                ( Finset.filter ( fun y => dist_euc x y = a ) ( Finset.erase S x ) ) < 2 from by
              obtain ⟨ p, hp₁, hp₂ ⟩ := h_deg2
              exact ⟨ p, hp₁, lt_of_le_of_ne ( by aesop ) hp₂ ⟩ ) )
          ( by norm_num [ * ] ) );
      have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p1, hp1S⟩ := hS_nonempty
      let N1 := (S.erase p1).filter (fun q => dist_euc p1 q = a)
      have hN1_card : N1.card = 2 := h_deg2 p1 hp1S
      obtain ⟨p2, p4, hp24, hN1_eq⟩ := Finset.card_eq_two.mp hN1_card
      have hp2N1 : p2 ∈ N1 := by simp [hN1_eq]
      have hp4N1 : p4 ∈ N1 := by simp [hN1_eq]
      have hp2_erase : p2 ∈ S.erase p1 := (Finset.mem_filter.mp hp2N1).1
      have hp4_erase : p4 ∈ S.erase p1 := (Finset.mem_filter.mp hp4N1).1
      have hp2S : p2 ∈ S := (Finset.mem_erase.mp hp2_erase).2
      have hp4S : p4 ∈ S := (Finset.mem_erase.mp hp4_erase).2
      have hp1_ne_p2 : p1 ≠ p2 := (Finset.mem_erase.mp hp2_erase).1.symm
      have hp1_ne_p4 : p1 ≠ p4 := (Finset.mem_erase.mp hp4_erase).1.symm
      have hp1p2 : dist_euc p1 p2 = a := (Finset.mem_filter.mp hp2N1).2
      have hp1p4 : dist_euc p1 p4 = a := (Finset.mem_filter.mp hp4N1).2
      have hthree_subset : ({p1, p2, p4} : Finset (ℝ × ℝ)) ⊆ S := by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl | rfl
        · exact hp1S
        · exact hp2S
        · exact hp4S
      have hthree_card : ({p1, p2, p4} : Finset (ℝ × ℝ)).card = 3 := by
        simp [hp1_ne_p2, hp1_ne_p4, hp24]
      have hR_card : (S \ ({p1, p2, p4} : Finset (ℝ × ℝ))).card = 1 := by
        rw [Finset.card_sdiff, h4]
        have hinter : (({p1, p2, p4} : Finset (ℝ × ℝ)) ∩ S).card = 3 := by
          rw [Finset.inter_eq_left.mpr hthree_subset, hthree_card]
        rw [hinter]
      obtain ⟨p3, hR_eq⟩ := Finset.card_eq_one.mp hR_card
      have hp3R : p3 ∈ S \ ({p1, p2, p4} : Finset (ℝ × ℝ)) := by simp [hR_eq]
      have hp3S : p3 ∈ S := (Finset.mem_sdiff.mp hp3R).1
      have hp3_not : p3 ∉ ({p1, p2, p4} : Finset (ℝ × ℝ)) := (Finset.mem_sdiff.mp hp3R).2
      have hp3_ne_p1 : p3 ≠ p1 := by intro h; exact hp3_not (by simp [h])
      have hp3_ne_p2 : p3 ≠ p2 := by intro h; exact hp3_not (by simp [h])
      have hp3_ne_p4 : p3 ≠ p4 := by intro h; exact hp3_not (by simp [h])
      have hS_eq : S = {p1, p2, p3, p4} := by
        ext x
        constructor
        · intro hx
          by_cases hx1 : x = p1
          · simp [hx1]
          by_cases hx2 : x = p2
          · simp [hx2]
          by_cases hx4 : x = p4
          · simp [hx4]
          have hxR : x ∈ S \ ({p1, p2, p4} : Finset (ℝ × ℝ)) := by
            simp [hx, hx1, hx2, hx4]
          have hx3 : x = p3 := by simpa [hR_eq] using hxR
          simp [hx3]
        · intro hx
          simp at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hp1S
          · exact hp2S
          · exact hp3S
          · exact hp4S
      have hp2p4_not_a : dist_euc p2 p4 ≠ a := by
        intro hp2p4
        apply h_no_tri
        refine ⟨p1, p2, p4, ?_, hp1_ne_p2, hp24, hp1_ne_p4.symm, ?_, ?_⟩
        · intro x hx
          simp at hx
          rcases hx with rfl | rfl | rfl
          · exact hp1S
          · exact hp2S
          · exact hp4S
        · rw [hp1p2, hp2p4]
        · rw [hp2p4]
          rw [dist_euc_comm]
          exact hp1p4.symm
      have hp1p3_not_a : dist_euc p1 p3 ≠ a := by
        intro hp1p3
        have hp3N1 : p3 ∈ N1 := by
          simp [N1, hp3S, hp3_ne_p1, hp1p3]
        have : p3 = p2 ∨ p3 = p4 := by simpa [hN1_eq] using hp3N1
        rcases this with h | h
        · exact hp3_ne_p2 h
        · exact hp3_ne_p4 h
      have neighbor_forced
          (p q r s : ℝ × ℝ)
          (hpS : p ∈ S) (hqS : q ∈ S) (hrS : r ∈ S) (hsS : s ∈ S)
          (hS : S = {p, q, r, s})
          (hpq : dist_euc p q = a)
          (hps_not : dist_euc p s ≠ a)
          (hqp_ne : q ≠ p) (hpr_ne : p ≠ r) (hqr_ne : q ≠ r) (hrs_ne : r ≠ s) :
          dist_euc p r = a := by
        by_contra hpr_not
        let N := (S.erase p).filter (fun x => dist_euc p x = a)
        have hN_card : N.card = 2 := h_deg2 p hpS
        have hqN : q ∈ N := by
          simp [N, hqS, hqp_ne, hpq]
        have hN_subset : N ⊆ {q} := by
          intro x hx
          have hx_erase := (Finset.mem_filter.mp hx).1
          have hxS := (Finset.mem_erase.mp hx_erase).2
          have hxp : x ≠ p := (Finset.mem_erase.mp hx_erase).1
          have hxa := (Finset.mem_filter.mp hx).2
          have hx_cases : x = p ∨ x = q ∨ x = r ∨ x = s := by simpa [hS] using hxS
          rcases hx_cases with rfl | rfl | rfl | rfl
          · exact False.elim (hxp rfl)
          · simp
          · exact False.elim (hpr_not hxa)
          · exact False.elim (hps_not hxa)
        have : N.card ≤ 1 := by
          exact le_trans (Finset.card_le_card hN_subset) (by simp)
        omega
      have hp2p3 : dist_euc p2 p3 = a := by
        refine neighbor_forced p2 p1 p3 p4 hp2S hp1S hp3S hp4S ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · ext x
          simp [hS_eq]
          tauto
        · rw [dist_euc_comm]; exact hp1p2
        · exact hp2p4_not_a
        · exact hp1_ne_p2
        · exact hp3_ne_p2.symm
        · exact hp3_ne_p1.symm
        · exact hp3_ne_p4
      have hp4p3 : dist_euc p4 p3 = a := by
        refine neighbor_forced p4 p1 p3 p2 hp4S hp1S hp3S hp2S ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · ext x
          simp [hS_eq]
          tauto
        · rw [dist_euc_comm]; exact hp1p4
        · rw [dist_euc_comm]; exact hp2p4_not_a
        · exact hp1_ne_p4
        · exact hp3_ne_p4.symm
        · exact hp3_ne_p1.symm
        · exact hp3_ne_p2
      have hp1p3_b : dist_euc p1 p3 = b := by
        rcases h_dist p1 p3 hp1S hp3S hp3_ne_p1.symm with h | h
        · exact False.elim (hp1p3_not_a h)
        · exact h
      have hp2p4_b : dist_euc p2 p4 = b := by
        rcases h_dist p2 p4 hp2S hp4S hp24 with h | h
        · exact False.elim (hp2p4_not_a h)
        · exact h
      refine ⟨p1, p2, p3, p4, hS_eq, hp1_ne_p2, hp3_ne_p2.symm, hp3_ne_p4,
        hp1_ne_p4.symm, hp3_ne_p1.symm, hp24, hp1p2, hp2p3, ?_, ?_, hp1p3_b,
        hp2p4_b⟩
      · rw [dist_euc_comm]
        exact hp4p3
      · rw [dist_euc_comm]
        exact hp1p4

/-
In a 4-point set with 2 distances and no equilateral triangle, every vertex has at most 2 neighbors
at distance a.
-/
lemma max_degree_le_2 (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (h_no_tri : ¬ has_equilateral_triangle_euc S) :
    ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2 := by
      intros p hp
      by_contra h_contra;
      -- If p has degree ≥ 3 in the graph of a-edges, then there are at least 3 other points in S
      -- that are at distance a from p.
      obtain ⟨q1, q2, q3, hq1, hq2, hq3, h_distinct⟩ :
          ∃ q1 q2 q3 : ℝ × ℝ,
        q1 ∈ S ∧ q2 ∈ S ∧ q3 ∈ S ∧ q1 ≠ p ∧ q2 ≠ p ∧ q3 ≠ p ∧
          q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧
          dist_euc p q1 = a ∧ dist_euc p q2 = a ∧ dist_euc p q3 = a := by
        obtain ⟨ s, hs ⟩ := Finset.exists_subset_card_eq
          ( show 3 ≤ Finset.card ( Finset.filter ( fun q => dist_euc p q = a ) S ) from by
            linarith );
        rcases Finset.card_eq_three.mp hs.2 with ⟨ q1, q2, q3, hq1, hq2, hq3 ⟩ ; use q1, q2,
          q3 ; simp_all +decide [ Finset.subset_iff ];
        refine ⟨ ?_, ?_, ?_ ⟩ <;> intro h <;> simp_all +decide;
        · unfold dist_euc at hs; norm_num at hs;
          have hpos : 0 < ( p.1 - q2.1 ) ^ 2 + ( p.2 - q2.2 ) ^ 2 := by
            exact not_le.mp fun h =>
              hq1 <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩
          exact hq1 ( Prod.mk_inj.mpr ⟨
            by nlinarith [ Real.sqrt_pos.mpr hpos ],
            by nlinarith [ Real.sqrt_pos.mpr hpos ] ⟩ );
        · unfold dist_euc at hs; simp_all +decide ;
          have hsqrt : 0 ≤ Real.sqrt ( ( p.1 - q1.1 ) ^ 2 + ( p.2 - q1.2 ) ^ 2 ) :=
            Real.sqrt_nonneg _
          have hmul := Real.mul_self_sqrt
            ( by positivity : 0 ≤ ( p.1 - q1.1 ) ^ 2 + ( p.2 - q1.2 ) ^ 2 )
          exact hq1 ( Prod.mk_inj.mpr ⟨
            by nlinarith [ hsqrt, hmul ],
            by nlinarith [ hsqrt, hmul ] ⟩ );
        · unfold dist_euc at hs; simp_all +decide ;
          have hsqrt : 0 ≤ Real.sqrt ( ( p.1 - q1.1 ) ^ 2 + ( p.2 - q1.2 ) ^ 2 ) :=
            Real.sqrt_nonneg _
          have hmul := Real.mul_self_sqrt
            ( add_nonneg ( sq_nonneg ( p.1 - q1.1 ) ) ( sq_nonneg ( p.2 - q1.2 ) ) )
          exact hq2 ( Prod.mk_inj.mpr ⟨
            by nlinarith [ hsqrt, hmul ],
            by nlinarith [ hsqrt, hmul ] ⟩ );
      have h_star : ∀ q ∈ S, q ≠ p → dist_euc p q = a := by
        intro q hq hqp; have := Finset.eq_of_subset_of_card_le ( show { q1, q2, q3,
          p } ⊆ S from by aesop_cat ) ; aesop;
      exact h_no_tri <| star_graph_implies_triangle S a b h4 h_dist hab p hp h_star

lemma edge_count_zero (S : Finset (ℝ × ℝ)) : edge_count S 0 = 0 := by
  unfold edge_count
  rw [Finset.card_eq_zero]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hoff, hdist⟩
    rcases Finset.mem_offDiag.mp hoff with ⟨_, _, hne⟩
    exact False.elim (hne (dist_euc_eq_zero.mp hdist))
  · intro hx
    simp at hx

lemma sum_degrees_filter_eq_edge_count (S : Finset (ℝ × ℝ)) (a : ℝ) (ha : a ≠ 0) :
    ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = edge_count S a := by
  let T : Finset (Σ p : ℝ × ℝ, ℝ × ℝ) :=
    S.sigma (fun p => S.filter (fun q => dist_euc p q = a))
  have hT_card :
      T.card = ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card := by
    simp [T, Finset.sigma, Finset.card]
  rw [← hT_card]
  unfold edge_count
  refine Finset.card_bij (fun x hx => (x.1, x.2)) ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hpS, hq⟩
    rcases Finset.mem_filter.mp hq with ⟨hqS, hpq⟩
    have hne : x.1 ≠ x.2 := by
      intro h
      apply ha
      rw [← hpq, h]
      exact dist_euc_eq_zero.mpr rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hpS, hqS, hne⟩, hpq⟩
  · intro x hx y hy hxy
    cases x
    cases y
    simp at hxy
    simp [hxy]
  · intro y hy
    rcases y with ⟨p, q⟩
    rcases Finset.mem_filter.mp hy with ⟨hoff, hpq⟩
    rcases Finset.mem_offDiag.mp hoff with ⟨hpS, hqS, _⟩
    refine ⟨⟨p, q⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨hpS, Finset.mem_filter.mpr ⟨hqS, hpq⟩⟩

/-
If a 4-point set has edge count 6 and degrees are only 2 or 0, then it contains an equilateral
triangle.
-/
lemma case_2_2_2_0_implies_triangle (S : Finset (ℝ × ℝ)) (a : ℝ)
    (_h4 : S.card = 4)
    (h_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 2 ∨
      (S.filter (fun q => dist_euc p q = a)).card = 0)
    (h_count : edge_count S a = 6) :
    has_equilateral_triangle_euc S := by
      have ha : a ≠ 0 := by
        intro h
        rw [h, edge_count_zero] at h_count
        norm_num at h_count
      have h_sum_degrees : ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 6 := by
        rw [sum_degrees_filter_eq_edge_count S a ha, h_count]
      have h_card_two :
          (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 3 := by
        have h_degrees : ∑ p ∈ S, (Finset.filter (fun q => dist_euc p q = a) S).card =
            ∑ p ∈ S,
          if (Finset.filter (fun q => dist_euc p q = a) S).card = 2 then 2 else 0 := by
          exact Finset.sum_congr rfl fun x hx => by cases h_deg x hx <;> simp +decide [ * ] ;
        simp_all +decide [ Finset.sum_ite ];
        linarith;
      have := Finset.card_eq_three.mp h_card_two;
      obtain ⟨ x, y, z, hxy, hxz, hyz, h ⟩ := this
      simp_all +decide [ Finset.Subset.antisymm_iff,
        Finset.subset_iff ] ;
      have h_triangle : (S.filter (fun q => dist_euc x q = a)) = {y,
        z} ∧ (S.filter (fun q => dist_euc y q = a)) = {x,
        z} ∧ (S.filter (fun q => dist_euc z q = a)) = {x, y} := by
        have h_triangle : ∀ p ∈ ({x, y, z} : Finset (ℝ × ℝ)),
          (S.filter (fun q => dist_euc p q = a)).card = 2 →
            (S.filter (fun q => dist_euc p q = a)) = {x, y, z} \ {p} := by
          intros p hp hp_card
          have h_subset : {q ∈ S | dist_euc p q = a} ⊆ {x, y, z} \ {p} := by
            simp_all +decide [ Finset.subset_iff ];
            exact fun a b ha hb => ⟨ h.1 a b ha ( by
              have h_symm : ∀ p q : ℝ × ℝ,
                  p ∈ S → q ∈ S → dist_euc p q = dist_euc q p := by
                exact fun p q hp hq =>
                  Real.sqrt_inj ( by positivity ) ( by positivity ) |>.2 ( by ring );
              grind ), by
              rintro rfl; simp_all +decide [ dist_euc ] ⟩;
          refine Finset.eq_of_subset_of_card_le h_subset ?_;
          rw [ Finset.card_sdiff ] ; aesop;
        grind +ring;
      use x, y, z; simp_all +decide [ Finset.ext_iff ] ;
      have := h_triangle.1 y.1 y.2
      have := h_triangle.2.1 z.1 z.2
      have := h_triangle.2.2 x.1 x.2
      simp_all +decide ;
      exact ⟨ by aesop_cat, Ne.symm hxz ⟩

/-
Arithmetic lemma: if 4 numbers <= 2 sum to 6, they are either {2,2,2,0} or {2,2,1,1}.
-/
lemma degree_sum_6_max_2_arithmetic (d : Fin 4 → ℕ) (h_le : ∀ i, d i ≤ 2)
    (h_sum : ∑ i, d i = 6) :
    (∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ d i = 2 ∧ d j = 2 ∧ d k = 2 ∧
      d (if i ≠ 0 ∧ j ≠ 0 ∧
      k ≠ 0 then 0 else if i ≠ 1 ∧ j ≠ 1 ∧ k ≠ 1 then 1 else if i ≠ 2 ∧ j ≠ 2 ∧
      k ≠ 2 then 2 else 3) = 0) ∨
    (∃ i j, i ≠ j ∧ d i = 1 ∧ d j = 1 ∧ (∀ k, k ≠ i → k ≠ j → d k = 2)) := by
      by_contra h_contra;
      simp_all +decide [ Fin.forall_fin_succ, Fin.exists_fin_succ ];
      simp_all +decide [ Fin.sum_univ_four ];
      grind

/-
If a function on a 4-element set sums to 6 and is bounded by 2, then the values are either {2,2,2,0}
or {2,2,1,1}.
-/
lemma degree_sum_6_max_2_finset {α : Type*} (S : Finset α) (f : α → ℕ)
    (h4 : S.card = 4)
    (h_le : ∀ x ∈ S, f x ≤ 2)
    (h_sum : ∑ x ∈ S, f x = 6) :
    ((S.filter (fun x => f x = 2)).card = 3 ∧ (S.filter (fun x => f x = 0)).card = 1) ∨
    ((S.filter (fun x => f x = 2)).card = 2 ∧ (S.filter (fun x => f x = 1)).card = 2) := by
      classical
      -- Let's count the total number of elements in S with values 2, 1, and 0.
      have h_total :
          (Finset.filter (fun x => f x = 2) S).card +
            (Finset.filter (fun x => f x = 1) S).card +
              (Finset.filter (fun x => f x = 0) S).card = 4 := by
        rw [ ← h4, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones S ▸ by
          rw [ Finset.sum_congr rfl ]
          intro x hx
          have := h_le x hx
          interval_cases f x <;> simp +decide
      have h_sum :
          (Finset.filter (fun x => f x = 2) S).card * 2 +
            (Finset.filter (fun x => f x = 1) S).card * 1 +
              (Finset.filter (fun x => f x = 0) S).card * 0 = 6 := by
        rw [ ← h_sum, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        simpa only [ Finset.sum_mul _ _ _ ] using by
          rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ]
          exact Finset.sum_congr rfl fun x hx => by
            have := h_le x hx
            interval_cases f x <;> trivial
      omega

/-
The case where 3 vertices have degree 2 and 1 has degree 0 is impossible because it implies an
equilateral triangle.
-/
lemma eliminate_case_2_2_2_0 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (_h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_no_tri : ¬ has_equilateral_triangle_euc S)
    (h_case : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 3 ∧
              (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 0)).card = 1) :
    False := by
      have h_deg : ∀ p ∈ S,
        (S.filter (fun q => dist_euc p q = a)).card = 2 ∨
          (S.filter (fun q => dist_euc p q = a)).card = 0 := by
        have h_deg :
            Finset.card
              (Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2) S) +
              Finset.card (Finset.filter (fun p =>
                (S.filter (fun q => dist_euc p q = a)).card = 0) S) = S.card := by
          grind;
        have h_deg :
            Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2) S ∪
              Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 0) S = S := by
          exact Finset.eq_of_subset_of_card_le
            ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) )
            ( by
              rw [ Finset.card_union_of_disjoint
                ( Finset.disjoint_filter.mpr fun _ _ _ => by linarith ), h_deg ] );
        intro p hp; replace h_deg := Finset.ext_iff.mp h_deg p; aesop;
      exact h_no_tri <| case_2_2_2_0_implies_triangle S a h4 h_deg h_count

/-
If a graph on 4 vertices has 6 directed edges, max degree 2, and no triangle, then it has 2 vertices
of degree 2 and 2 vertices of degree 1.
-/
lemma degrees_2_2_1_1 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_no_tri : ¬ has_equilateral_triangle_euc S) :
    (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
    (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2 := by
      have ha : a ≠ 0 := by
        intro h
        rw [h, edge_count_zero] at h_count
        norm_num at h_count
      have h_deg_sum : ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 6 := by
        rw [sum_degrees_filter_eq_edge_count S a ha, h_count]
      exact Or.resolve_left ( degree_sum_6_max_2_finset S _ h4 h_max_deg h_deg_sum ) fun h =>
        eliminate_case_2_2_2_0 S a h4 h_count h_max_deg h_no_tri h

/-
The sum of degrees equals the edge count (assuming a != 0).
-/
lemma sum_degrees_eq_edge_count (S : Finset (ℝ × ℝ)) (a : ℝ) (ha : a ≠ 0) :
    ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = edge_count S a := by
  exact sum_degrees_filter_eq_edge_count S a ha

/-
If two vertices have degree 1 in a graph with 6 directed edges on 4 vertices, they cannot be
connected to each other.
-/
lemma degree_1_vertices_not_connected (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (u v : ℝ × ℝ) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1)
    (h_deg_v : (S.filter (fun q => dist_euc v q = a)).card = 1) :
    dist_euc u v ≠ a := by
      -- Assume for contradiction that dist_euc u v = a.
      by_contra h_contra
      have h_neighborhoods : {q ∈ S | dist_euc u q = a} = {v} ∧
        {q ∈ S | dist_euc v q = a} = {u} := by
        have h_neighborhoods : v ∈ {q ∈ S | dist_euc u q = a} ∧
            u ∈ {q ∈ S | dist_euc v q = a} := by
          simp [h_contra];
          exact ⟨ hv, hu, by
            rw [ ← h_contra, dist_euc ]
            exact Real.sqrt_inj ( by positivity ) ( by positivity ) |>.2
              ( by simpa [ dist_comm ] using by ring ) ⟩;
        exact ⟨ Finset.card_eq_one.mp h_deg_u |> fun ⟨ x, hx ⟩ => by aesop,
          Finset.card_eq_one.mp h_deg_v |> fun ⟨ x, hx ⟩ => by aesop ⟩;
      -- Let S' = S \ {u, v}. S' has size 2. Let S' = {x, y}.
      obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ℝ × ℝ,
        x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v ∧
          S = {u, v, x, y} := by
        have h_card_S' : (S \ {u, v}).card = 2 := by
          rw [ Finset.card_sdiff ] ; aesop_cat;
        obtain ⟨ x, y, hx, hy ⟩ := Finset.card_eq_two.mp h_card_S';
        use x, y; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
        grind;
      -- The sum of degrees in S is 6. deg(u) + deg(v) = 1 + 1 = 2. So ∑ p ∈ S',
      -- deg(p) = 6 - 2 = 4.
      have h_sum_degrees_S' :
          (S.filter (fun q => dist_euc x q = a)).card +
            (S.filter (fun q => dist_euc y q = a)).card = 4 := by
        have h_sum_degrees_S' : ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 6 := by
          rw [ ← h_count, sum_degrees_eq_edge_count ];
          rintro rfl; simp_all +decide [ Finset.card_eq_one ];
          exact huv ( by
            rw [ dist_euc ] at h_contra
            have hsqrt : 0 ≤ Real.sqrt ( ( u.1 - v.1 ) ^ 2 + ( u.2 - v.2 ) ^ 2 ) :=
              Real.sqrt_nonneg _
            have hsq := Real.sq_sqrt
              ( add_nonneg ( sq_nonneg ( u.1 - v.1 ) ) ( sq_nonneg ( u.2 - v.2 ) ) )
            exact Prod.mk_inj.mpr ⟨
              by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, hsqrt, hsq ],
              by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, hsqrt, hsq ] ⟩ );
        grind;
      -- Since $u$ and $v$ have no neighbors in $S'$, neighbors of $p$ must be in $S'$.
      have h_neighborhoods_S' : (S.filter (fun q => dist_euc x q = a)) ⊆ {x,
        y} ∧ (S.filter (fun q => dist_euc y q = a)) ⊆ {x, y} := by
        simp_all +decide [ Finset.subset_iff ];
        simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
        simp_all +decide [ dist_euc ];
        exact ⟨
          ⟨
            fun h => False.elim <| h_neighborhoods.1.2.1 <| by
              rw [ ← h, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
              ring,
            fun h => False.elim <| h_neighborhoods.2.2.2.1 <| by
              rw [ ← h, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
              ring ⟩,
          fun h => False.elim <| h_neighborhoods.1.2.2 <| by
            rw [ ← h, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
            ring,
          fun h => False.elim <| h_neighborhoods.2.2.2.2 <| by
            rw [ ← h, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
            ring ⟩;
      have := Finset.card_le_card h_neighborhoods_S'.1
      have := Finset.card_le_card h_neighborhoods_S'.2
      simp_all +decide ;
      simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
      simp_all +decide [ Finset.filter_insert, Finset.filter_singleton, dist_euc ];
      grind

/-
If two degree 1 vertices share a neighbor x (degree 2), it leads to a contradiction (sum of degrees
too low).
-/
lemma degree_1_neighbors_distinct (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (u v x : ℝ × ℝ) (hu : u ∈ S) (hv : v ∈ S) (hx : x ∈ S)
    (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x)
    (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1)
    (h_deg_v : (S.filter (fun q => dist_euc v q = a)).card = 1)
    (h_deg_x : (S.filter (fun q => dist_euc x q = a)).card = 2)
    (h_ux : dist_euc u x = a)
    (h_vx : dist_euc v x = a) :
    False := by
      have h_y_deg : ∀ y ∈ S,
        y ≠ u ∧ y ≠ v ∧ y ≠ x →
          dist_euc y u ≠ a ∧ dist_euc y v ≠ a ∧ dist_euc y x ≠ a := by
        intros y hy hy_ne
        have h_y_u : dist_euc y u ≠ a := by
          intro H; have := Finset.card_eq_one.mp h_deg_u; obtain ⟨ q,
            hq ⟩ := this; simp_all +decide ;
          rw [ Finset.eq_singleton_iff_unique_mem ] at hq ; simp_all +decide [ dist_euc ];
          grind
        have h_y_v : dist_euc y v ≠ a := by
          intro H;
          have := Finset.card_eq_one.mp h_deg_v; obtain ⟨ z,
            hz ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
          have := hz _ _ |>.1 ⟨ hy, ?_ ⟩ <;> simp_all +decide;
          · specialize hz x.1 x.2 ; aesop;
          · convert H using 1;
            unfold dist_euc; ring_nf;
        have h_y_x : dist_euc y x ≠ a := by
          intro H;
          have h_y_x : Finset.card (Finset.filter (fun q => dist_euc x q = a) S) ≥ 3 := by
            refine Finset.two_lt_card.mpr ?_;
            use u, by
              simp_all +decide [ dist_euc ];
              rw [ ← h_ux, Real.sqrt_inj ( by positivity ) ( by positivity ) ] ; ring, v, by
              unfold dist_euc at *; simp_all +decide ;
              rw [ ← h_vx, Real.sqrt_inj ( by positivity ) ( by positivity ) ] ; ring, y, by
              simp_all +decide [ dist_euc ];
              exact Eq.trans ( by ring_nf ) H;
            grind;
          linarith [ h_max_deg x hx ]
        exact ⟨h_y_u, h_y_v, h_y_x⟩;
      have h_sum_degrees : ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 6 := by
        rw [ ← h_count, ← sum_degrees_eq_edge_count ];
        rintro rfl; simp_all +decide [ dist_euc ];
        exact hux <| Prod.mk_inj.mpr ⟨
          by
            rw [ Real.sqrt_eq_zero' ] at h_ux
            nlinarith only [ h_ux ],
          by
            rw [ Real.sqrt_eq_zero' ] at h_ux
            nlinarith only [ h_ux ] ⟩;
      rw [ ← Finset.sum_sdiff
        ( Finset.insert_subset hu
          ( Finset.insert_subset hv ( Finset.singleton_subset_iff.mpr hx ) ) )
        ] at *
      simp_all +decide [ Finset.sum_insert ] ;
      have h_card_S_minus : (S \ {u, v, x}).card = 1 := by
        rw [ Finset.card_sdiff ] ; simp +decide [ * ];
      rw [ Finset.card_eq_one ] at h_card_S_minus ; obtain ⟨ y,
        hy ⟩ := h_card_S_minus ; simp_all +decide [ Finset.sum_singleton ];
      rw [ Finset.card_eq_two ] at h_sum_degrees ; obtain ⟨ z, w,
        hzw ⟩ := h_sum_degrees ; simp_all +decide [ Finset.ext_iff ];
      grind

/-
In a graph with 4 vertices and degrees {2, 2, 1, 1}, any vertex with degree 1 is connected to a
vertex with degree 2.
-/
lemma degree_1_connects_to_degree_2 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
             (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2)
    (u : ℝ × ℝ) (hu : u ∈ S) (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1) :
    ∃ x ∈ S, (S.filter (fun q => dist_euc x q = a)).card = 2 ∧ dist_euc u x = a := by
      obtain ⟨v, hv, h_deg_v⟩ : ∃ v ∈ S, v ≠ u ∧ dist_euc u v = a := by
        obtain ⟨ v, hv ⟩ := Finset.card_eq_one.mp h_deg_u;
        rw [ Finset.eq_singleton_iff_unique_mem ] at hv;
        by_cases hvu : v = u;
        · simp_all +decide [ dist_euc ];
          contrapose! h_count;
          unfold edge_count; simp +decide [ hv.1.symm ] ;
          unfold dist_euc; simp +decide [ Real.sqrt_eq_zero' ] ;
          rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
          exact fun a b c d ha hb hab => not_le.mp fun h =>
            hab ( by nlinarith only [ h ] ) ( by nlinarith only [ h ] );
        · exact ⟨ v, Finset.mem_filter.mp hv.1 |>.1, hvu, Finset.mem_filter.mp hv.1 |>.2 ⟩;
      refine ⟨ v, hv, ?_, h_deg_v.2 ⟩;
      -- Since $v$ is not in the set of vertices with degree 1, its degree must be 2.
      have h_not_in_deg1 :
          v ∉ Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1) S := by
        have := degree_1_vertices_not_connected S a h4 h_count h_max_deg u v hu hv; aesop;
      have := h_max_deg v hv
      interval_cases _ : Finset.card ( Finset.filter ( fun q => dist_euc v q = a ) S ) <;>
        simp_all +decide ;
      specialize ‹∀ a_1 b : ℝ, ( a_1, b ) ∈ S → ¬dist_euc v ( a_1,
        b ) = a› u.1 u.2 ; simp_all +decide;
      exact ‹¬dist_euc v u = a› ( by
        rw [ ← h_deg_v.2, dist_euc ]
        exact Real.sqrt_inj ( by positivity ) ( by positivity ) |>.2 <| by ring )

/-
In a graph with 4 vertices and degrees {2, 2, 1, 1}, the two degree 1 vertices are connected to
distinct degree 2 vertices.
-/
lemma degree_1_connects_to_distinct_degree_2 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
      (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2)
    (u v : ℝ × ℝ) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1)
    (h_deg_v : (S.filter (fun q => dist_euc v q = a)).card = 1) :
    ∃ x y : ℝ × ℝ, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧
      (S.filter (fun q => dist_euc x q = a)).card = 2 ∧
      (S.filter (fun q => dist_euc y q = a)).card = 2 ∧
      dist_euc u x = a ∧ dist_euc v y = a := by
        obtain ⟨x, hx⟩ : ∃ x ∈ S,
          (S.filter (fun q => dist_euc x q = a)).card = 2 ∧ dist_euc u x = a := by
          exact degree_1_connects_to_degree_2 S a h4 h_count h_max_deg h_deg u hu h_deg_u
        obtain ⟨y, hy⟩ : ∃ y ∈ S,
          (S.filter (fun q => dist_euc y q = a)).card = 2 ∧ dist_euc v y = a := by
          exact degree_1_connects_to_degree_2 S a h4 h_count h_max_deg h_deg v hv h_deg_v;
        by_cases hxy : x = y;
        · have := degree_1_neighbors_distinct S a h4 h_count h_max_deg u v x hu hv hx.1
            huv ( by aesop ) ( by aesop ) h_deg_u h_deg_v hx.2.1 ( by aesop ) ( by aesop )
          aesop;
        · exact ⟨ x, y, hx.1, hy.1, hxy, hx.2.1, hy.2.1, hx.2.2, hy.2.2 ⟩

/-
If a graph on 4 vertices has 6 directed edges of color 'a', no monochromatic triangle, and degrees
{2, 2, 1, 1}, then it is a P4 path graph in color 'a'.
-/
lemma path_graph_structure (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (h_count : edge_count S a = 6)
    (h_no_tri : ¬ has_equilateral_triangle_euc S)
    (h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
      (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2) :
    is_P4_P4 S a b := by
      -- By definition of `is_P4_P4`, we need to find points `p1`, `p2`, `p3`, `p4` such that the
      -- conditions hold.
      obtain ⟨u, v, x, y, h_set, h_deg_u, h_deg_v, h_deg_x, h_deg_y,
        h.neighbors⟩ : ∃ u v x y : ℝ × ℝ, {u, v, x,
        y} = S ∧ (S.filter (fun q => dist_euc u q = a)).card = 1 ∧
          (S.filter (fun q => dist_euc v q = a)).card = 1 ∧
          (S.filter (fun q => dist_euc x q = a)).card = 2 ∧
          (S.filter (fun q => dist_euc y q = a)).card = 2 ∧ dist_euc u x = a ∧
          dist_euc v y = a := by
        -- By definition of `is_P4_P4`, we need to find points `u`, `v`, `x`, `y` such that the
        -- conditions hold.
        obtain ⟨u, v, hu, hv, h_deg_u, h_deg_v⟩ : ∃ u v : ℝ × ℝ,
          u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ (S.filter (fun q => dist_euc u q = a)).card = 1 ∧
            (S.filter (fun q => dist_euc v q = a)).card = 1 := by
          obtain ⟨ u, hu, v, hv,
            huv ⟩ := Finset.one_lt_card.1
              ( by
                linarith :
                  1 < Finset.card
                    ( Finset.filter
                      ( fun p => Finset.card ( Finset.filter ( fun q => dist_euc p q = a ) S ) = 1 )
                      S ) )
          use u, v
          aesop;
        obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ℝ × ℝ,
          x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ (S.filter (fun q => dist_euc x q = a)).card = 2 ∧
            (S.filter (fun q => dist_euc y q = a)).card = 2 ∧ dist_euc u x = a ∧
            dist_euc v y = a := by
          have := degree_1_connects_to_distinct_degree_2 S a h4 h_count
            ( fun p hp => max_degree_le_2 S a b h4 h_dist hab h_no_tri p hp ) h_deg u v
            hu hv h_deg_u h_deg_v.1 h_deg_v.2
          aesop;
        use u, v, x, y;
        rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hu,
          Finset.insert_subset_iff.mpr ⟨ hv, Finset.insert_subset_iff.mpr ⟨ hx,
          Finset.singleton_subset_iff.mpr hy ⟩ ⟩ ⟩ ) ]
        · aesop
        · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem ] <;> aesop
      -- Since $x$ and $y$ have degree 2, they must be connected to each other.
      have h_xy : dist_euc x y = a := by
        contrapose! h_deg_x; simp_all +decide;
        have h_xy : {q ∈ S | dist_euc x q = a} ⊆ {y, u} := by
          simp_all +decide [ Finset.subset_iff ];
          intro a b ha hb; subst h_set; simp_all +decide ;
          rcases ha with ( ha | ha | ha | ha ) <;> simp_all +decide;
          · contrapose! h_deg_v; simp_all +decide ;
            refine ne_of_gt ( Finset.one_lt_card.mpr ?_ );
            use x, by
              simp +decide [ ← hb ];
              exact Real.sqrt_inj ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) )
                ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) |>.2 ( by ring ), y, by
              aesop;
            grind;
          · unfold dist_euc at *; simp_all +decide ;
            norm_num [ ← hb ] at *;
            rw [ Real.sqrt_eq_zero' ] at *;
            exact Or.inr ( Prod.mk_inj.mpr ⟨ by nlinarith only [ h.neighbors.1 ],
              by nlinarith only [ h.neighbors.1 ] ⟩ );
        exact ne_of_lt ( lt_of_le_of_lt
          ( Finset.card_le_card ( show { q ∈ S | dist_euc x q = a } ⊆ { u } from
            fun q hq => by
              have := h_xy hq
              aesop ) )
          ( by norm_num ) );
      -- Since $u$ and $v$ have degree 1, they must be connected to $x$ and $y$ respectively.
      have h_uv : dist_euc u y = b ∧ dist_euc v x = b ∧ dist_euc u v = b := by
        have h_uv : dist_euc u y ≠ a ∧ dist_euc v x ≠ a ∧ dist_euc u v ≠ a := by
          refine ⟨ ?_, ?_, ?_ ⟩ <;> intro h <;> simp_all +decide [ Finset.card_eq_one ];
          · obtain ⟨ a, b, h ⟩ := h_deg_u
            simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
            grind +ring;
          · simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
            grind;
          · simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
            grind;
        grind;
      use u, x, y, v;
      simp_all +decide [ Finset.ext_iff ];
      refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩;
      any_goals intro h; simp_all +decide;
      · intro a b; specialize h_set a b; aesop;
      · simp_all +decide [ dist_euc ];
        exact ⟨ by
          rw [ ← h.neighbors.2, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
          ring,
          by
            rw [ ← h_uv.2.1, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
            ring ⟩

/-
The number of directed edges of a given length in a graph is even (because edges come in pairs (u,v)
and (v,u)).
-/
lemma edge_count_even (S : Finset (ℝ × ℝ)) (r : ℝ) : Even (edge_count S r) := by
  unfold edge_count;
  -- The set of edges is symmetric because `dist_euc` is symmetric.
  have h_symm : ∀ (x y : ℝ × ℝ),
      x ∈ S ∧ y ∈ S ∧ x ≠ y → dist_euc x y = r → dist_euc y x = r := by
    unfold dist_euc; intro x y h h'; ring_nf at *; aesop;
  -- Let's consider the set of edges in the graph where the distance is r.
  set E := (S.offDiag.filter (fun (x, y) => dist_euc x y = r)) with hE_def;
  -- Since $E$ is symmetric, we can pair each element $(x, y)$ with $(y, x)$.
  have h_pair : ∃ T : Finset ((ℝ × ℝ) × ℝ × ℝ),
      E = T ∪ Finset.image (fun p => (p.2, p.1)) T ∧
        Disjoint T (Finset.image (fun p => (p.2, p.1)) T) := by
    refine ⟨ E.filter fun p => p.1.1 < p.2.1 ∨ p.1.1 = p.2.1 ∧ p.1.2 < p.2.2, ?_, ?_ ⟩;
    · ext ⟨x, y⟩; simp [E];
      cases lt_trichotomy x.1 y.1 <;> cases lt_trichotomy x.2 y.2 <;> aesop;
    · norm_num [ Finset.disjoint_right ];
      grind;
  obtain ⟨ T, hT₁, hT₂ ⟩ := h_pair; rw [ hT₁,
    Finset.card_union_of_disjoint hT₂ ] ; simp_all +decide [ parity_simps ] ;
  rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ]

/-
If x (degree 2) is connected to u (degree 1), then x is connected to y (the other degree 2 vertex).
-/
lemma degree_2_connected_to_degree_2_if_connected_to_degree_1 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
      (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2)
    (x y u v : ℝ × ℝ) (hx : x ∈ S) (hy : y ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hxy : x ≠ y) (huv : u ≠ v)
    (h_deg_x : (S.filter (fun q => dist_euc x q = a)).card = 2)
    (h_deg_y : (S.filter (fun q => dist_euc y q = a)).card = 2)
    (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1)
    (h_deg_v : (S.filter (fun q => dist_euc v q = a)).card = 1)
    (h_conn : dist_euc x u = a) :
    dist_euc x y = a := by
      by_contra h_contra;
      -- If x and y are not connected, then the neighbors of x are exactly u and another vertex, say
      -- z. Similarly, the neighbors of y are exactly v and another vertex, say w.
      obtain ⟨z, hz⟩ : ∃ z, z ∈ S ∧ z ≠ u ∧ z ≠ x ∧ dist_euc x z = a := by
        obtain ⟨ z, hz ⟩ := Finset.exists_mem_ne
          ( by
            linarith :
              1 < Finset.card ( Finset.filter ( fun q => dist_euc x q = a ) S ) ) u;
        by_cases hz_eq_x : z = x;
        · simp_all +decide [ dist_euc ];
          norm_num [ ← hz.1 ] at *;
          exact False.elim <| hz <| Prod.mk_inj.mpr ⟨
            by
              rw [ Real.sqrt_eq_zero' ] at h_conn
              nlinarith only [ h_conn ],
            by
              rw [ Real.sqrt_eq_zero' ] at h_conn
              nlinarith only [ h_conn ] ⟩;
        · aesop
      obtain ⟨w, hw⟩ : ∃ w, w ∈ S ∧ w ≠ v ∧ w ≠ y ∧ dist_euc y w = a := by
        contrapose! h_deg_y; simp_all +decide ;
        rw [ Finset.card_filter ] at *;
        rw [ Finset.sum_eq_single v ] <;> simp_all +decide ;
        · split_ifs <;> norm_num;
        · intro a_1 b h₁ h₂; specialize h_deg_y a_1 b h₁ h₂; by_cases h₃ : ( a_1,
          b ) = y <;> simp_all +decide ;
          rintro rfl; simp_all +decide [ dist_euc ];
          simp_all +decide [ add_nonneg, sq_nonneg ];
          norm_num [ show x = u by ext <;> nlinarith only [ h_conn ] ] at *;
          linarith;
      have h_eq : S = {x, y, u, v} := by
        have := Finset.eq_of_subset_of_card_le ( show { x, y, u,
          v } ⊆ S from by aesop_cat ) ; simp_all +decide ;
        rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem ] at this <;> aesop;
      simp_all +decide [ Finset.filter ];
      rcases hz with ⟨ rfl | rfl | rfl | rfl, hz₁, hz₂,
        hz₃ ⟩ <;>
        rcases hw with ⟨ rfl | rfl | rfl | rfl, hw₁, hw₂, hw₃ ⟩ <;>
        simp_all +decide;
      · -- This contradicts our assumption that dist_euc w y ≠ a.
        apply h_contra;
        convert hw₃ using 1;
        exact Real.sqrt_inj ( by positivity ) ( by positivity ) |>.2 ( by ring );
      · contrapose! h_deg_u;
        rw [ Multiset.ndinsert_of_notMem,
          Multiset.ndinsert_of_notMem ] <;> simp_all +decide;
        · rw [ Multiset.filter_cons, Multiset.filter_cons, Multiset.filter_cons,
          Multiset.filter_singleton ] ; simp_all +decide;
          simp_all +decide [ dist_euc ];
          split_ifs <;> simp_all +decide;
          · exact ‹¬Real.sqrt ( ( w.1 - y.1 ) ^ 2 + ( w.2 - y.2 ) ^ 2 ) = a› ( by
              rw [ ← hw₃ ]
              rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ]
              ring );
          · exact ‹¬Real.sqrt ( ( w.1 - x.1 ) ^ 2 + ( w.2 - x.2 ) ^ 2 ) = a› ( by
              rw [ ← h_conn ]
              rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ]
              ring );
          · norm_num [ ← ‹0 = a› ] at *;
            exact ‹¬Real.sqrt ( ( w.1 - x.1 ) ^ 2 + ( w.2 - x.2 ) ^ 2 ) = 0› ( by
              rw [ Real.sqrt_eq_zero' ] at *
              nlinarith );
          · exact ‹¬Real.sqrt ( ( w.1 - x.1 ) ^ 2 + ( w.2 - x.2 ) ^ 2 ) = a› ( by
              rw [ show ( w.1 - x.1 ) ^ 2 + ( w.2 - x.2 ) ^ 2 =
                ( x.1 - w.1 ) ^ 2 + ( x.2 - w.2 ) ^ 2 by ring, h_conn ] );
        · aesop;
        · grind

/-
In a graph with 4 vertices and degrees {2, 2, 1, 1}, the two degree 2 vertices are connected to each
other.
-/
lemma degree_2_vertices_connected (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
      (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2)
    (x y : ℝ × ℝ) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h_deg_x : (S.filter (fun q => dist_euc x q = a)).card = 2)
    (h_deg_y : (S.filter (fun q => dist_euc y q = a)).card = 2) :
    dist_euc x y = a := by
      -- Let u be a vertex of degree 1. Such a vertex exists because there are 2 of them.
      obtain ⟨u, hu⟩ : ∃ u ∈ S, (S.filter (fun q => dist_euc u q = a)).card = 1 := by
        exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun p hp => ⟨ p,
          Finset.mem_filter.mp hp |>.1, Finset.mem_filter.mp hp |>.2 ⟩;
      obtain ⟨v, hv⟩ : ∃ v ∈ S,
          (S.filter (fun q => dist_euc v q = a)).card = 1 ∧ v ≠ u := by
        exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne
          ( show 1 < Finset.card
              ( Finset.filter
                ( fun p => Finset.card ( Finset.filter ( fun q => dist_euc p q = a ) S ) = 1 )
                S ) from by linarith ) u );
      -- By `degree_1_connects_to_degree_2`, u connects to some vertex z of degree 2.
      obtain ⟨z, hz⟩ : ∃ z ∈ S,
        (S.filter (fun q => dist_euc z q = a)).card = 2 ∧ dist_euc u z = a := by
        have := degree_1_connects_to_degree_2 S a h4 h_count h_max_deg h_deg u hu.1 hu.2; aesop;
      -- The set of degree 2 vertices is exactly {x, y}. So z = x or z = y.
      have hz_cases : z = x ∨ z = y := by
        have hz_cases :
            Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2) S =
              {x, y} := by
          rw [ Finset.eq_of_subset_of_card_le ( show { x,
            y } ⊆ Finset.filter
              ( fun p => Finset.card ( Finset.filter ( fun q => dist_euc p q = a ) S ) = 2 ) S
              from by aesop_cat ) ] ; aesop;
        rw [ Finset.ext_iff ] at hz_cases; specialize hz_cases z; aesop;
      rcases hz_cases with ( rfl | rfl ) <;> simp_all +decide only [Finset.card_eq_two];
      · apply degree_2_connected_to_degree_2_if_connected_to_degree_1
        · convert h4 using 1
        · exact h_count
        · exact fun p a => h_max_deg p a
        · grind
        · grind
        · exact hy
        · exact hu.1
        · exact hv.1
        all_goals try tauto
        · grind;
        · obtain ⟨ x, y, hxy, h ⟩ := h_deg_y; rw [ h ] ; simp +decide [ hxy ] ;
        · convert hz.2.2 using 1;
          unfold dist_euc; ring_nf;
      · have := @degree_2_connected_to_degree_2_if_connected_to_degree_1 S a;
        contrapose! this;
        exact ⟨ h4, h_count, h_max_deg, ⟨ by
          grind, by
          aesop ⟩, z, x, u, v, hy, hx, hu.1, hv.1, by tauto, by tauto, by
          aesop, by
          grind, by
          exact hu.2, by
          exact hv.2.1, by
          convert hz.2.2 using 1;
          unfold dist_euc ; ring_nf;, by
          convert this using 1;
          unfold dist_euc; ring_nf; ⟩

/-
If a 4-point graph has 6 edges of color 'a' and no equilateral triangle, it has golden ratio
distances.
-/
lemma count_6_implies_golden (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (h_count : edge_count S a = 6)
    (h_no_tri : ¬ has_equilateral_triangle_euc S) :
    has_golden_ratio_distances_euc S := by
      -- Apply `path_graph_structure` to show that the graph is a P4 path graph (`is_P4_P4`).
      have h_path : is_P4_P4 S a b := by
        apply path_graph_structure S a b h4 h_dist hab h_count h_no_tri;
        have := degrees_2_2_1_1 S a h4 h_count
          ( max_degree_le_2 S a b h4 h_dist hab h_no_tri ) h_no_tri
        aesop;
      apply_rules [ P4_P4_implies_golden ];
      · contrapose! hab;
        obtain ⟨ p1, p2, p3, p4, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
          h11, h12 ⟩ := h_path
        exact absurd h7 ( by
          linarith [ show 0 < dist_euc p1 p2 from Real.sqrt_pos.mpr ( by
            exact not_le.mp fun h => h1 <| by
              exact Prod.mk_inj.mpr <| ⟨
                by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ],
                by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ⟩ ) ] );
      · contrapose! h_no_tri;
        obtain ⟨ p1, p2, p3, p4, hS, h12, h23, h34, h13, h24, h14 ⟩ := h_path;
        exact False.elim <| h_no_tri.not_gt <| h14.2.2.2.2.1 ▸
          Real.sqrt_pos.2 ( by
            exact not_le.mp fun h =>
              h13 <| Prod.mk_inj.mpr ⟨ by nlinarith only [ h ], by nlinarith only [ h ] ⟩ )

/-
Proof of Perucca's classification theorem: any 4-point set with 2 distances is a square, has an
equilateral triangle, or has golden ratio distances.
-/
theorem PeruccaClassificationStatement_proof : PeruccaClassificationStatement := by
  intro S h4 h_distinct
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b, a > 0 ∧ b > 0 ∧ a ≠ b ∧
      (∀ p ∈ S, ∀ q ∈ S, q ≠ p → dist_euc p q = a ∨ dist_euc p q = b) ∧
        (distinctDistances'_euc S).card = 2 := by
    have := Finset.card_eq_two.mp h_distinct;
    obtain ⟨ a, b, hab, h ⟩ := this; use a, b; simp_all +decide [ Finset.ext_iff ] ;
    refine ⟨ ?_, ?_, ?_, ?_ ⟩;
    · contrapose! h;
      use a; simp;
      intro H;
      obtain ⟨ p, hp, q, hq, hpq, rfl ⟩ := Finset.mem_image.mp ( Finset.mem_sdiff.mp H |>.1 );
      unfold dist_euc at *; simp_all +decide [ Real.sqrt_le_iff ] ;
      norm_num [ show p.1.1 = p.2.1 by nlinarith, show p.1.2 = p.2.2 by nlinarith ] at *;
      unfold distinctDistances'_euc at H; aesop;
    · contrapose! h;
      refine ⟨ b, Or.inr ⟨ ?_, Or.inr rfl ⟩ ⟩;
      simp [distinctDistances'_euc];
      exact fun x y z t hx hy hxy => le_antisymm h ( hxy ▸ Real.sqrt_nonneg _ );
    · intro x y hx z w hz hne; specialize h ( dist_euc ( x, y ) ( z,
      w ) ) ; simp_all +decide [ distinctDistances'_euc ] ;
      exact h.mp ⟨ ⟨ x, y, z, w, ⟨ hx, hz ⟩, rfl ⟩,
        by
          exact ne_of_gt ( Real.sqrt_pos.mpr ( by
            exact not_le.mp fun h => hne ( by nlinarith ) ( by nlinarith ) ) ) ⟩;
    · rw [ show distinctDistances'_euc S = { a, b } by ext; aesop ] ; aesop;
  have h_edge_count : edge_count S a + edge_count S b = 12 := by
    exact edge_count_sum S a b h4 ( by aesop ) hab.1
  have h_edge_count_even : Even (edge_count S a) ∧ Even (edge_count S b) := by
    exact ⟨ edge_count_even S a, edge_count_even S b ⟩
  have h_edge_count_nonzero : edge_count S a ≠ 0 ∧ edge_count S b ≠ 0 := by
    constructor <;> intro h <;> simp_all +decide;
    · -- If the edge count for a is zero, then all edges in S must be of distance b.
      have h_all_b : ∀ p ∈ S, ∀ q ∈ S, q ≠ p → dist_euc p q = b := by
        intros p hp q hq hneq
        have h_dist : dist_euc p q = a ∨ dist_euc p q = b := by
          grind;
        rw [ edge_count ] at h; simp_all +decide ;
        exact h_dist.resolve_left fun h' => h _ _ _ _ hp hq ( by aesop ) h';
      have h_contradiction : (distinctDistances'_euc S).card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_;
        simp_all +decide [ distinctDistances'_euc ];
        intros a x x_1 x_2 x_3 hx hx' hx'' hx''' b x x_4 x_5 x_6 hx'''' hx''''' hx'''''' hx''''''';
        by_cases h : x = x_5 ∧ x_4 = x_6 <;> simp_all +decide [ dist_euc ];
        grind +ring;
      linarith;
    · -- If edge_count S b = 0, then all distances in S must be a.
      have h_all_a : ∀ p ∈ S, ∀ q ∈ S, q ≠ p → dist_euc p q = a := by
        intros p hp q hq hqp
        have h_dist : dist_euc p q = a ∨ dist_euc p q = b := by
          exact hab.2.1 _ _ hp _ _ hq ( by aesop ) |> Or.imp id id;
        generalize_proofs at *; (
        contrapose! h; simp_all +decide [ edge_count ] ;
        exact ⟨ p.1, p.2, hp, q.1, q.2, hq, by aesop ⟩);
      have h_eq_dist : ∀ p ∈ S, ∀ q ∈ S, dist_euc p q = if p = q then 0 else a := by
        intros p hp q hq; split_ifs <;> simp_all +decide ;
        · unfold dist_euc; norm_num;
        · grind;
      have h_eq_dist : distinctDistances'_euc S = {a} := by
        ext; simp;
        constructor <;> intro h <;> simp_all +decide [ distinctDistances'_euc ];
        · grind +ring;
        · obtain ⟨ p, hp, q, hq,
          hpq ⟩ := Finset.one_lt_card.1 ( by linarith : 1 < Finset.card S )
          use ⟨ p.1, p.2, q.1, q.2, ⟨ hp, hq ⟩,
            h_eq_dist _ _ hp _ _ hq ▸ if_neg ( by aesop ) ⟩
          linarith;
      aesop
  have h_edge_count_cases : edge_count S a = 2 ∨ edge_count S a = 4 ∨ edge_count S a = 6 ∨
    edge_count S a = 8 ∨ edge_count S a = 10 := by
    have : edge_count S a ≤ 12 := Nat.le_of_lt_succ ( by linarith )
    interval_cases edge_count S a <;>
      simp_all +decide ;
  rcases h_edge_count_cases with h_case | h_case <;> simp_all +decide only;
  · -- If `edge_count S a = 2`, then `edge_count S b = 10`, which implies a monochromatic triangle
    -- of color `b`, contradiction.
    have h_contra : has_equilateral_triangle_euc S := by
      have h_monochromatic_triangle : edge_count S b > 8 := by
        linarith;
      contrapose! h_monochromatic_triangle;
      apply_rules [ num_edges_le_4_of_no_triangle ];
      exact fun ⟨ p, q, r, h₁, h₂, h₃, h₄, h₅, h₆, h₇ ⟩ =>
        h_monochromatic_triangle ⟨ p, q, r, by aesop ⟩
    exact Or.inr (Or.inl h_contra);
  · rcases h_case with ( h_case | h_case | h_case | h_case );
    · by_cases h_no_triangle : ¬ has_equilateral_triangle_euc S;
      · have h_C4_2K2 : is_C4_2K2 S b a := by
          apply C4_of_edge_count_8 S b a h4 (by
          exact fun x y hx hy hxy => Or.symm ( hab.2.1 x hx y hy hxy.symm )) (by
          tauto) (by
          grind) (by
          assumption);
        exact Or.inl <| C4_2K2_implies_square S b a hb ha ( Ne.symm hab.1 ) h_C4_2K2;
      · exact Or.inr <| Or.inl <| Classical.not_not.mp h_no_triangle;
    · by_cases h_no_tri : has_equilateral_triangle_euc S <;> simp_all +decide;
      exact Or.inr ( count_6_implies_golden S a b h4 ( by aesop ) hab.1 h_case h_no_tri );
    · by_cases h_no_triangle : ¬ has_equilateral_triangle_euc S;
      · exact Or.inl <|
          C4_2K2_implies_square S a b ha hb hab.1 <|
            C4_of_edge_count_8 S a b h4
              ( fun x y hx hy hxy => hab.2.1 x hx y hy <| by tauto )
              hab.1 h_case h_no_triangle;
      · exact Or.inr <| Or.inl <| Classical.not_not.mp h_no_triangle;
    · -- If `edge_count S a = 10`, then `edge_count S a > 8`, which implies a
      -- monochromatic triangle
      -- of color `a` (by `num_edges_le_4_of_no_triangle`), contradiction.
      have h_monochromatic_triangle : ∃ p q r, {p, q,
        r} ⊆ S ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p ∧ dist_euc p q = a ∧ dist_euc q r = a ∧
          dist_euc r p = a := by
        contrapose! h_case;
        exact ne_of_lt ( lt_of_le_of_lt
          ( num_edges_le_4_of_no_triangle S a h4
            ( by simpa [ Finset.subset_iff ] using h_case ) )
          ( by decide ) );
      obtain ⟨ p, q, r, hpqr, hpq, hqr, hrp, hpq', hqr',
        hrp' ⟩ := h_monochromatic_triangle; exact Or.inr <| Or.inl ⟨ p, q, r, by aesop ⟩ ;

/-
Any 4-point subset of P_m determines at least 3 distinct Euclidean distances.
-/
theorem P_local_constraint_proven (m : ℕ) (h_perucca : PeruccaClassificationStatement) :
    ∀ S, S ⊆ (P m) → S.card = 4 → (distinctDistances'_euc S).card ≥ 3 := by
      have := @P_local_constraint; aesop;

open EuclideanGeometry Finset Real

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

notation g " ≪ " f => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

/--
Given a finite set of points in the plane, we define the number of distinct distances between pairs
of points.
-/
noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  (points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2).card

noncomputable def toEuclideanPoint (p : ℝ × ℝ) : ℝ² :=
  !₂[p.1, p.2]

lemma toEuclideanPoint_injective : Function.Injective toEuclideanPoint := by
  rintro ⟨x, y⟩ ⟨z, t⟩ h
  apply Prod.ext
  · simpa [toEuclideanPoint] using
      congrArg (fun v : ℝ² => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2) v) 0) h
  · simpa [toEuclideanPoint] using
      congrArg (fun v : ℝ² => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2) v) 1) h

lemma dist_toEuclideanPoint (p q : ℝ × ℝ) :
    dist (toEuclideanPoint p) (toEuclideanPoint q) = dist_euc p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨z, t⟩
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  norm_num [toEuclideanPoint, dist_euc, Fin.sum_univ_two]

lemma distinctDistances'_euc_eq_offDiag_image (S : Finset (ℝ × ℝ)) :
    distinctDistances'_euc S =
      S.offDiag.image (fun pair : (ℝ × ℝ) × (ℝ × ℝ) => dist_euc pair.1 pair.2) := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_sdiff.mp hd with ⟨hd_image, hd_zero⟩
    rcases Finset.mem_image.mp hd_image with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_product.mp hpair with ⟨hp, hq⟩
    have hpq : pair.1 ≠ pair.2 := by
      intro hpq
      apply hd_zero
      simp [dist_euc_eq_zero.mpr hpq]
    exact Finset.mem_image.mpr
      ⟨pair, Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_offDiag.mp hpair with ⟨hp, hq, hpq⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨pair, Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
    · simp [dist_euc_eq_zero, hpq]

lemma distinctDistances_image_toEuclideanPoint (S : Finset (ℝ × ℝ)) :
    distinctDistances (S.image toEuclideanPoint) = (distinctDistances'_euc S).card := by
  unfold distinctDistances
  rw [distinctDistances'_euc_eq_offDiag_image]
  apply congrArg Finset.card
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_offDiag.mp hpair with ⟨hp, hq, hpq⟩
    rcases Finset.mem_image.mp hp with ⟨p, hpS, hp_eq⟩
    rcases Finset.mem_image.mp hq with ⟨q, hqS, hq_eq⟩
    refine Finset.mem_image.mpr ⟨(p, q), ?_, ?_⟩
    · exact Finset.mem_offDiag.mpr
        ⟨hpS, hqS, fun hpq' => hpq (by
          rw [← hp_eq, ← hq_eq]
          exact congrArg toEuclideanPoint hpq')⟩
    · calc
        dist_euc (p, q).1 (p, q).2 = dist (toEuclideanPoint p) (toEuclideanPoint q) :=
          (dist_toEuclideanPoint p q).symm
        _ = dist pair.1 pair.2 := by rw [hp_eq, hq_eq]
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_offDiag.mp hpair with ⟨hp, hq, hpq⟩
    refine Finset.mem_image.mpr
      ⟨(toEuclideanPoint pair.1, toEuclideanPoint pair.2), ?_, ?_⟩
    · exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_image.mpr ⟨pair.1, hp, rfl⟩,
          Finset.mem_image.mpr ⟨pair.2, hq, rfl⟩,
          fun h => hpq (toEuclideanPoint_injective h)⟩
    · exact dist_toEuclideanPoint pair.1 pair.2

/--
Is there a set of $n$ points in $\mathbb{R}^2$ such that every subset of $4$ points determines at
least $3$ distances, yet the total number of distinct distances is $\ll \frac{n}{\sqrt{\log n}}$?
-/
theorem erdos_659 : ∃ A : ℕ → Finset ℝ²,
   (∀ n, #(A n) = n ∧ ∀ S ⊆ A n, #S = 4 → 3 ≤ distinctDistances S) ∧
    (fun n ↦ distinctDistances (A n)) ≪ fun n ↦ n / sqrt (log n) := by
  obtain ⟨P, hP_card, hP_local, hP_bigO⟩ :=
    main_theorem PeruccaClassificationStatement_proof
      (by intro Δ hΔ; exact _root_.bernays Δ hΔ)
  refine ⟨fun n => (P n).image toEuclideanPoint, ?_, ?_⟩
  · intro n
    constructor
    · rw [Finset.card_image_of_injective _ toEuclideanPoint_injective, hP_card n]
    · intro S hS hS_card
      have hA_card : ((P n).image toEuclideanPoint).card = n := by
        rw [Finset.card_image_of_injective _ toEuclideanPoint_injective, hP_card n]
      have hn : n ≥ 4 := by
        have hle := Finset.card_le_card hS
        rw [hA_card, hS_card] at hle
        omega
      let S' : Finset (ℝ × ℝ) := (P n).filter (fun p => toEuclideanPoint p ∈ S)
      have hS'_subset : S' ⊆ P n := by
        intro p hp
        exact (Finset.mem_filter.mp hp).1
      have hS_image : S'.image toEuclideanPoint = S := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
          exact (Finset.mem_filter.mp hp).2
        · intro hx
          have hxA : x ∈ (P n).image toEuclideanPoint := hS hx
          rcases Finset.mem_image.mp hxA with ⟨p, hp, rfl⟩
          exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hx⟩, rfl⟩
      have hS'_card : S'.card = 4 := by
        rw [← hS_card, ← hS_image,
          Finset.card_image_of_injective _ toEuclideanPoint_injective]
      have hdist := hP_local n hn S' hS'_subset hS'_card
      rw [← hS_image, distinctDistances_image_toEuclideanPoint]
      exact hdist
  · simpa [distinctDistances_image_toEuclideanPoint] using hP_bigO

#print axioms erdos_659
-- 'Erdos659.erdos_659' depends on axioms: [bernays, propext, Classical.choice, Quot.sound]

end Erdos659
