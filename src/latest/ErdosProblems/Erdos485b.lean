/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 485.
https://www.erdosproblems.com/forum/thread/485

Formalization status:
- Partial

Informal authors:
- W. Verdenius

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/485#post-4030
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem485.lean
-/
import Mathlib

namespace Erdos485b

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.deprecated false

/-!
Below you can find a formalization, obtained by Aristotle from Harmonic
(aristotle@harmonic.fun), of the following two theorems by Verdenius:

**Theorem**. For every positive integer `n`, there exists a polynomial `f(x)` of
degree `n` with all nonzero integer coefficients such that `f(x)²` has fewer
than `(1/5)(102 · n^{log₉ 6} - 12)` nonzero coefficients.

**Theorem**. For every positive integer `n`, there exists a polynomial `f(x)` of
degree `n` with all nonzero real coefficients such that `f(x)²` has fewer than
`(1/7)(170 · n^{log_{13} 8} - 14)` nonzero coefficients.

W. Verdenius, On the number of terms of the square and the cube of polynomials,
Indag. Math. 11 (1949), 546–565.

-/

open Polynomial Finset
open Polynomial Finset Pointwise

set_option maxHeartbeats 1600000

noncomputable section

/-- The base polynomial `P(x) = 1 + 2x - 2x² + 4x³ - 10x⁴ + 28x⁵ - 98x⁶ + 686x⁷ + 2401x⁸`. -/
def baseP : ℤ[X] :=
  C 1 + C 2 * X + C (-2) * X ^ 2 + C 4 * X ^ 3 + C (-10) * X ^ 4 +
  C 28 * X ^ 5 + C (-98) * X ^ 6 + C 686 * X ^ 7 + C 2401 * X ^ 8

private lemma baseP_coeff_val (i : ℕ) :
    baseP.coeff i = if i = 0 then 1 else if i = 1 then 2 else if i = 2 then -2
      else if i = 3 then 4 else if i = 4 then -10 else if i = 5 then 28
      else if i = 6 then -98 else if i = 7 then 686 else if i = 8 then 2401 else 0 := by
  rcases Nat.lt_or_ge i 9 with h | h
  · interval_cases i <;>
      simp only [baseP, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] <;>
      norm_num
  · simp only [baseP, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]; omega

lemma baseP_natDegree : baseP.natDegree = 8 := by
  unfold baseP; compute_degree!

lemma baseP_coeff_ne_zero (i : ℕ) (hi : i ≤ 8) : baseP.coeff i ≠ 0 := by
  interval_cases i <;>
    simp only [baseP, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] <;>
    norm_num

set_option maxHeartbeats 6400000 in
lemma baseP_sq_gap (i : ℕ) (hi : i ∈ ({2, 3, 4, 5, 11, 12, 13, 14} : Finset ℕ)) :
    (baseP ^ 2).coeff i = 0 := by
  rw [pow_two, coeff_mul]
  simp only [baseP_coeff_val]
  fin_cases hi <;> decide

-- Proved helpers
lemma pow9_construction_base :
    ∃ (f : ℤ[X]) (R : Finset ℕ),
      f.natDegree = 9 ^ 0 ∧
      (∀ i, i ≤ 9 ^ 0 → f.coeff i ≠ 0) ∧
      (∀ r ∈ R, r < 9 ^ 0) ∧
      (0 : ℕ) ∈ R ∧
      R.card = (6 ^ (0 + 1) - 1) / 5 ∧
      (f ^ 2).support ⊆ R ∪ R.image (· + 9 ^ 0) ∪ {2 * 9 ^ 0} := by
  refine ⟨X + 1, {0}, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  · exact Polynomial.natDegree_X_add_C (1 : ℤ)
  · intro i hi; interval_cases i <;> simp [Polynomial.coeff_one, Polynomial.coeff_X]
  · intro i
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X, add_sq]; aesop

lemma exists_nonzero_not_in_finite (S : Finset ℤ) : ∃ x : ℤ, x ≠ 0 ∧ x ∉ S :=
  Exists.imp (by aesop) (Set.Infinite.exists_notMem_finset (Set.Ioi_infinite 0) S)

lemma R'_card_arithmetic (N : ℕ) :
    6 * ((6 ^ (N + 1) - 1) / 5) + 1 = (6 ^ (N + 2) - 1) / 5 := by
  ring_nf at *
  exact Eq.symm (Nat.div_eq_of_eq_mul_left (by norm_num) (Nat.sub_eq_of_eq_add (by
    linarith [Nat.sub_add_cancel (show 1 ≤ 6 ^ N * 6 from
      Nat.one_le_iff_ne_zero.mpr (by norm_num)),
      Nat.div_mul_cancel (show 5 ∣ 6 ^ N * 6 - 1 from
        Nat.dvd_of_mod_eq_zero (by
          rw [← Nat.mod_add_div (6 ^ N * 6) 5]; norm_num [Nat.pow_mod, Nat.mul_mod]))])))

def R'_set (R : Finset ℕ) (d : ℕ) : Finset ℕ :=
  R ∪ R.image (· + d) ∪ R.image (· + 2 * d) ∪ {3 * d} ∪
  R.image (· + 6 * d) ∪ R.image (· + 7 * d) ∪ R.image (· + 8 * d)

lemma R'_set_range (R : Finset ℕ) (d : ℕ) (hd : 0 < d) (hR : ∀ r ∈ R, r < d) :
    ∀ r ∈ R'_set R d, r < 9 * d := by
  simp [R'_set]; grind

lemma R'_set_zero (R : Finset ℕ) (d : ℕ) (h0 : (0 : ℕ) ∈ R) :
    (0 : ℕ) ∈ R'_set R d := by
  unfold R'_set; aesop

lemma R'_set_card (R : Finset ℕ) (d : ℕ) (hd : 0 < d) (hR : ∀ r ∈ R, r < d) :
    (R'_set R d).card = 6 * R.card + 1 := by
  unfold R'_set
  rw [Finset.card_union_of_disjoint] <;> norm_num [Finset.disjoint_left]
  · rw [Finset.card_insert_of_notMem] <;>
      norm_num [Finset.card_image_of_injective, Function.Injective]
    · rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
          Finset.card_union_of_disjoint, Finset.card_union_of_disjoint] <;>
        norm_num [Finset.disjoint_left]; ring_nf
      · rw [Finset.card_image_of_injective, Finset.card_image_of_injective,
            Finset.card_image_of_injective, Finset.card_image_of_injective] <;>
          simp +arith +decide [Function.Injective]; ring
      · grind
      · grind
      · grind +ring
      · grind
    · grind
  · grind

lemma comp_coeff_zero_of_not_dvd (p : ℤ[X]) (a : ℤ) (d k : ℕ)
    (_hd : 0 < d) (hk : ¬ d ∣ k) :
    (p.comp (C a * X ^ d)).coeff k = 0 := by
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range]
  norm_num [mul_pow, mul_assoc, mul_left_comm, Polynomial.coeff_C_mul_X_pow]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← pow_mul, mul_comm, Polynomial.coeff_mul]
  rw [Finset.sum_eq_zero]; intros; simp_all +decide
  exact fun h => Or.inr <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by
    erw [Polynomial.natDegree_pow, Polynomial.natDegree_C]; norm_num; contrapose! hk; aesop

lemma natDegree_baseP_comp (a : ℤ) (d : ℕ) (ha : a ≠ 0) (_hd : 0 < d) :
    (baseP.comp (C a * X ^ d)).natDegree = 8 * d := by
  rw [ Polynomial.natDegree_comp, Polynomial.natDegree_mul' ] <;> simp +decide [ * ];
  exact Or.inl baseP_natDegree

/-
Completeness: f * Q has all nonzero coefficients.
-/
lemma product_complete (f : ℤ[X]) (d : ℕ) (lam : ℤ)
    (hd : 0 < d) (hlam : lam ≠ 0)
    (hf_deg : f.natDegree = d)
    (hf_comp : ∀ i, i ≤ d → f.coeff i ≠ 0)
    (hlam_good : ∀ j ∈ Finset.range 8,
      baseP.coeff (j + 1) * f.coeff 0 * lam + baseP.coeff j * f.coeff d ≠ 0) :
    ∀ i, i ≤ 9 * d → (f * baseP.comp (C lam * X ^ d)).coeff i ≠ 0 := by
  intro i hi; by_cases hi' : i % d = 0 <;> by_cases hi'' : i / d = 0 <;> simp_all +decide [ mul_assoc, mul_left_comm ] ;
  · cases hi'' <;> simp_all +decide [ Nat.mod_eq_of_lt ];
    simp_all +decide [ Polynomial.coeff_zero_eq_eval_zero ];
    norm_num [ hd.ne', baseP ];
  · -- Since $i$ is a multiple of $d$, we can write $i = j * d$ for some $j$.
    obtain ⟨j, rfl⟩ : ∃ j, i = j * d := by
      exact exists_eq_mul_left_of_dvd <| Nat.dvd_of_mod_eq_zero hi'
    have hj : j ≤ 9 := by
      nlinarith
    have hj' : j ≥ 1 := by
      nlinarith [ Nat.pos_of_ne_zero hi''.1 ] ;
    have hj'' : j ≤ 8 ∨ j = 9 := by
      interval_cases j <;> trivial;
    cases' hj'' with hj'' hj'' <;> simp_all +decide ;
    · -- By definition of polynomial multiplication, we have:
      have h_coeff : (f * (baseP.comp (C lam * X ^ d))).coeff (j * d) = ∑ k ∈ Finset.range (j + 1), f.coeff (j * d - k * d) * (baseP.comp (C lam * X ^ d)).coeff (k * d) := by
        rw [ Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ];
        rw [ ← Finset.sum_flip ];
        rw [ ← Finset.sum_subset ( show Finset.image ( fun k => k * d ) ( Finset.range ( j + 1 ) ) ⊆ Finset.range ( j * d + 1 ) from Finset.image_subset_iff.mpr fun k hk => Finset.mem_range.mpr <| by nlinarith [ Finset.mem_range.mp hk ] ) ] <;> norm_num [ Finset.sum_image, hd.ne' ] ; ring_nf;
        · exact Finset.sum_congr rfl fun x hx => by rw [ Nat.sub_sub_self ( by nlinarith [ Finset.mem_range.mp hx ] ) ] ;
        · intro x hx hx'; rw [ Nat.sub_sub_self ( by nlinarith ) ] ;
          exact Or.inr ( comp_coeff_zero_of_not_dvd _ _ _ _ hd ( by contrapose! hx'; obtain ⟨ k, hk ⟩ := hx'; exact ⟨ k, by nlinarith, by nlinarith ⟩ ) );
      -- By definition of polynomial composition, we have:
      have h_coeff_comp : ∀ k ∈ Finset.range (j + 1), (baseP.comp (C lam * X ^ d)).coeff (k * d) = baseP.coeff k * lam ^ k := by
        intro k hk; rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ] ; simp +decide [ mul_pow, mul_assoc, mul_comm ] ;
        rw [ Finset.sum_eq_single k ] <;> simp_all +decide [ ← pow_mul ];
        · norm_num [ mul_comm k, Polynomial.coeff_mul ];
          rw [ Finset.sum_eq_single ( 0, d * k ) ] <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
          · rw [ Finset.sum_eq_single ( d * k, 0 ) ] <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
            · norm_num [ Polynomial.coeff_zero_eq_eval_zero ];
            · aesop;
          · intro a b hab ha; rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] <;> norm_num ; contrapose! ha ; aesop;
        · intro b hb hb'; rw [ Polynomial.coeff_mul, Finset.sum_eq_zero ] ; intros ; simp_all +decide [mul_comm,
          mul_left_comm, pow_mul'] ;
          by_cases h : ‹ℕ × ℕ›.1 = 0 <;> by_cases h' : ‹ℕ × ℕ›.2 = 0 <;> simp_all +decide [ ← pow_mul ];
          · exact Or.inr <| Or.inr <| by contrapose! hb'; nlinarith;
          · exact Or.inr <| Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_C ] ; nlinarith [ Nat.pos_of_ne_zero h ] ;
          · exact Or.inr <| Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_C ] ; norm_num ; contrapose! h ; aesop;
        · grind +suggestions
      simp_all +decide [ Finset.sum_range_succ ];
      rw [ Finset.sum_eq_single ( j - 1 ) ] <;> norm_num [ h_coeff_comp ];
      · convert hlam_good ( j - 1 ) ( by interval_cases j <;> trivial ) |> fun h => mul_ne_zero h ( pow_ne_zero ( j - 1 ) hlam ) using 1 ; ring_nf!; interval_cases j <;> simp +decide [ * ] ; ring_nf;
        grind +splitImp;
        grind;
        · rw [ show 4 * d - d * 3 = d by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring_nf;
        · rw [ show 5 * d - d * 4 = d by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring_nf;
        · rw [ show 6 * d - d * 5 = d by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring_nf;
        · rw [ show 7 * d - d * 6 = d by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring_nf;
        · rw [ show 8 * d - d * 7 = d by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring_nf;
      · intro k hk₁ hk₂; rw [ h_coeff_comp k ( by linarith ) ] ; simp_all +decide ;
        exact Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by rw [ hf_deg ] ; exact lt_tsub_iff_left.mpr <| by nlinarith [ Nat.sub_add_cancel hj', show k < j - 1 from lt_of_le_of_ne ( Nat.le_sub_one_of_lt hk₁ ) hk₂ ] ;
      · aesop;
    · rw [ Polynomial.coeff_mul, Finset.sum_eq_single ( d, 8 * d ) ] <;> simp_all +decide ;
      · rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
        norm_num [ mul_pow, ← pow_mul', baseP_natDegree ];
        norm_num [ Finset.sum_range_succ, Polynomial.coeff_X_pow, mul_assoc, mul_left_comm, hd.ne' ];
        norm_num [ Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_X_pow, mul_assoc, pow_succ, hd ];
        exact ⟨ by unfold baseP; norm_num [ Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_C ], hlam ⟩;
      · intro a b hab h; by_cases ha : a ≤ d <;> by_cases hb : b ≤ 8 * d <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ;
        · exact False.elim <| h ( by linarith ) ( by linarith );
        · rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
          rw [ Polynomial.natDegree_comp, Polynomial.natDegree_mul' ] <;> norm_num [ hd.ne', hlam ];
          exact lt_of_le_of_lt ( Nat.mul_le_mul_right _ ( show baseP.natDegree ≤ 8 by exact baseP_natDegree.le ) ) ( by linarith );
      · exact fun h => False.elim <| h <| by ring;
  · rw [ Polynomial.coeff_mul, Finset.sum_eq_single ( i, 0 ) ] <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
    · simp_all +decide [ Polynomial.coeff_zero_eq_eval_zero ];
      exact ⟨ hf_comp i ( by omega ), by unfold baseP; norm_num [ hd.ne' ] ⟩;
    · -- Since $b$ is not a multiple of $d$, the coefficient of $b$ in $baseP.comp (lam * X^d)$ is zero.
      have h_coeff_zero : ∀ b, ¬(d ∣ b) → (baseP.comp (C lam * X ^ d)).coeff b = 0 := by
        exact fun k hk => comp_coeff_zero_of_not_dvd _ _ _ _ hd hk;
      intro a b hab h; contrapose! hi'; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      exact Classical.not_not.1 fun hi'' => hi'.2 <| h_coeff_zero b <| by rw [ Nat.mod_eq_of_lt ] <;> omega;
  · -- Since $i$ is not a multiple of $d$, we can write $i = j * d + r$ where $0 < r < d$ and $j \leq 8$.
    obtain ⟨j, r, hr⟩ : ∃ j r, 0 < r ∧ r < d ∧ i = j * d + r ∧ j ≤ 8 := by
      exact ⟨ i / d, i % d, Nat.pos_of_ne_zero hi', Nat.mod_lt _ hd, by rw [ Nat.div_add_mod' ], by nlinarith [ Nat.div_mul_le_self i d, Nat.mod_add_div i d, Nat.pos_of_ne_zero hi' ] ⟩;
    -- The coefficient (f * Q).coeff i where Q = baseP.comp(C lam * X^d) involves the convolution sum over (a,b) with a+b=i. Since Q only has nonzero terms at positions that are multiples of d (positions 0, d, 2d, ..., 8d), the coefficient simplifies to:
    have h_coeff : (f * (baseP.comp (C lam * X ^ d))).coeff i = f.coeff r * (baseP.comp (C lam * X ^ d)).coeff (j * d) := by
      rw [ Polynomial.coeff_mul, Finset.sum_eq_single ( r, j * d ) ] <;> simp_all +decide ;
      · intro a b hab h; contrapose! h; simp_all +decide ;
        -- Since $b$ is a multiple of $d$, we can write $b = k * d$ for some integer $k$.
        obtain ⟨k, hk⟩ : ∃ k, b = k * d := by
          have h_b_mul_d : ∀ k, (baseP.comp (C lam * X ^ d)).coeff k ≠ 0 → d ∣ k := by
            intros k hk; exact (by
            exact Classical.not_not.1 fun h => hk <| comp_coeff_zero_of_not_dvd _ _ _ _ hd h);
          exact exists_eq_mul_left_of_dvd <| h_b_mul_d b h.2;
        rcases lt_trichotomy k j with hk' | rfl | hk' <;> simp_all +decide [Nat.mod_eq_of_lt];
        · exact False.elim <| h.1 <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by nlinarith;
        · grind;
        · exact False.elim <| h.1 <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by nlinarith;
      · exact fun h => False.elim <| h <| add_comm _ _;
    -- Since $baseP$ has nonzero coefficients at positions $0, 1, 2, ..., 8$, and $j \leq 8$, we have $(baseP.comp (C lam * X ^ d)).coeff (j * d) \neq 0$.
    have h_baseP_coeff : (baseP.comp (C lam * X ^ d)).coeff (j * d) = (baseP.coeff j) * lam ^ j := by
      rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ] ; simp +decide [*] ; ring_nf;
      rw [ Finset.sum_eq_single j ] <;> simp_all +decide [mul_comm, mul_left_comm];
      · norm_num [ mul_assoc, mul_comm, mul_left_comm, Polynomial.coeff_mul ];
        rw [ Finset.sum_eq_single ( 0, j * d ) ] <;> simp +decide [ mul_comm ];
        · norm_num [ mul_comm, Polynomial.coeff_zero_eq_eval_zero ];
        · aesop;
      · intro k hk₁ hk₂; rw [ Polynomial.coeff_mul ] ; simp +decide ;
        rw [ Finset.sum_eq_zero ] <;> simp_all +decide;
        intro a b hab hb; rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; simp_all +decide [ Polynomial.natDegree_pow ] ;
        exact Nat.pos_of_ne_zero ( by rintro rfl; exact hk₂ ( by nlinarith only [ hab, hd ] ) );
      · exact fun h => Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith [ show baseP.natDegree = 8 from baseP_natDegree ] ;
    simp_all +decide [mul_comm, mul_left_comm];
    exact ⟨ hf_comp r ( by linarith ), baseP_coeff_ne_zero j ( by linarith ) ⟩

/-
Support containment for the construction step.
-/
lemma support_mul_subset_add (f g : ℤ[X]) :
    (f * g).support ⊆ f.support + g.support :=
  AddMonoidAlgebra.support_mul f.toFinsupp g.toFinsupp

lemma step_support_containment (f : ℤ[X]) (R : Finset ℕ) (d : ℕ) (lam : ℤ)
    (hlam : lam ≠ 0)
    (hR_range : ∀ r ∈ R, r < d) (h0 : 0 ∈ R)
    (hf_supp : (f ^ 2).support ⊆ R ∪ R.image (· + d) ∪ {2 * d}) :
    ((f * baseP.comp (C lam * X ^ d)) ^ 2).support ⊆
      R'_set R d ∪ (R'_set R d).image (· + 9 * d) ∪ {18 * d} := by
  -- By poly_support_mul, supp((f * Q)^2) ⊆ supp(f^2) + supp(Q^2).
  have h_support_mul : (f * baseP.comp (C lam * X ^ d)) ^ 2 = f ^ 2 * (baseP ^ 2).comp (C lam * X ^ d) := by
    simp +decide [ mul_pow ]
  have h_support_mul_superset : ((f * baseP.comp (C lam * X ^ d)) ^ 2).support ⊆ (f ^ 2).support + ((baseP ^ 2).comp (C lam * X ^ d)).support := by
    exact h_support_mul.symm ▸ support_mul_subset_add _ _ |> Finset.Subset.trans <| by simp +decide ;
  simp_all [mul_pow];
  -- By poly_support_mul, supp(Q^2) ⊆ ({0,1,6,7,8,9,10,15,16} : Finset ℕ).image (· * d).
  have h_support_Q2 : ((baseP ^ 2).comp (C lam * X ^ d)).support ⊆ (Finset.range 17).image (fun s => s * d) \ (({2, 3, 4, 5, 11, 12, 13, 14} : Finset ℕ).image (fun s => s * d)) := by
    intro i hi
    have h_coeff_zero : ∀ j ∈ ({2, 3, 4, 5, 11, 12, 13, 14} : Finset ℕ), (baseP ^ 2).coeff j = 0 := by
      simp +decide [ baseP_sq_gap ]
    have h_coeff_zero_comp : ∀ k, ¬d ∣ k → ((baseP ^ 2).comp (C lam * X ^ d)).coeff k = 0 := by
      exact fun k hk => comp_coeff_zero_of_not_dvd _ _ _ _ (Nat.pos_of_ne_zero (by intro h; subst h; exact absurd (hR_range 0 h0) (by omega))) hk
    have h_coeff_zero_comp_image : ∀ s ∈ ({2, 3, 4, 5, 11, 12, 13, 14} : Finset ℕ), ((baseP ^ 2).comp (C lam * X ^ d)).coeff (s * d) = 0 := by
      intro s hs
      have h_coeff_zero_comp_image_step : ((baseP ^ 2).comp (C lam * X ^ d)).coeff (s * d) = ((baseP ^ 2).coeff s) * lam ^ s := by
        rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ] ; simp +decide [ * ] ; ring_nf;
        rw [ Finset.sum_eq_single s ] <;> simp +decide [*];
        intro b hb hb'; rw [ Polynomial.coeff_mul, Finset.sum_eq_zero ] <;> simp +decide [*] ; ring_nf; (
        intro a b_1 hab hb'; rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; simp_all +decide [ Polynomial.natDegree_pow ] ;
        exact Nat.pos_of_ne_zero ( by aesop ) ;)
      simp_all +decide;
      rcases hs with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +decide [ h_coeff_zero ]
    have h_coeff_zero_comp_image_range : ∀ j, j > 16 → ((baseP ^ 2).comp (C lam * X ^ d)).coeff (j * d) = 0 := by
      intro j hj
      have h_deg : Polynomial.natDegree ((baseP ^ 2).comp (C lam * X ^ d)) ≤ 16 * d := by
        rw [ Polynomial.natDegree_comp, Polynomial.natDegree_mul' ] <;> norm_num [ baseP_natDegree ] ; ring_nf ; aesop;
      have h_coeff_zero_comp_image_range : j * d > 16 * d := by
        exact Nat.mul_lt_mul_of_pos_right hj ( Nat.pos_of_ne_zero ( by specialize hR_range 0 h0; aesop ) )
      have h_coeff_zero_comp_image_range : ((baseP ^ 2).comp (C lam * X ^ d)).coeff (j * d) = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith;
      exact h_coeff_zero_comp_image_range
    simp_all +decide [ Finset.subset_iff ];
    by_cases hi_div : d ∣ i <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
    -- Since $i$ is divisible by $d$, we can write $i = k * d$ for some integer $k$.
    obtain ⟨k, rfl⟩ : ∃ k, i = k * d := by
      exact exists_eq_mul_left_of_dvd <| Nat.dvd_of_mod_eq_zero hi_div;
    exact ⟨ ⟨ k, Nat.lt_of_not_ge fun hk => hi <| h_coeff_zero_comp_image_range k <| by linarith, rfl ⟩, by aesop_cat, by aesop_cat, by aesop_cat, by aesop_cat, by aesop_cat, by aesop_cat, by aesop_cat, by aesop_cat ⟩;
  -- By minkowski_step, for any $x \in \text{supp}(f^2)$ and $y \in \text{supp}(Q^2)$, $x + y \in R'_set R d \cup (R'_set R d).image (· + 9 * d) ∪ {18 * d}$.
  have h_minkowski_step : ∀ x ∈ (f ^ 2).support, ∀ y ∈ ((baseP ^ 2).comp (C lam * X ^ d)).support, x + y ∈ R'_set R d ∪ (R'_set R d).image (· + 9 * d) ∪ {18 * d} := by
    intros x hx y hy
    obtain ⟨s, hs⟩ : ∃ s ∈ ({0,1,6,7,8,9,10,15,16} : Finset ℕ), y = s * d := by
      have := h_support_Q2 hy; simp_all +decide [ Finset.subset_iff ] ;
      rcases h_support_Q2 hy with ⟨ ⟨ a, ha, rfl ⟩, _, _, _, _, _, _, _, _ ⟩ ; interval_cases a <;> simp +decide at *;
    have := hf_supp hx; simp_all +decide [ Finset.subset_iff ] ;
    rcases hf_supp hx with ( rfl | hx | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ R'_set ];
    · rcases hs.1 with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +arith +decide [ * ] at hy ⊢;
    · rcases hs.1 with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +arith +decide [ * ];
    · rcases hs.1 with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +arith +decide [ * ] at hy ⊢;
  intro x hx; specialize h_support_mul_superset hx; rw [ Finset.mem_add ] at h_support_mul_superset; aesop;

/-
The inductive step of the Erdős construction.
-/
lemma pow9_construction_step (N : ℕ)
    (f : ℤ[X]) (R : Finset ℕ)
    (hf_deg : f.natDegree = 9 ^ N)
    (hf_comp : ∀ i, i ≤ 9 ^ N → f.coeff i ≠ 0)
    (hR_range : ∀ r ∈ R, r < 9 ^ N)
    (hR_zero : (0 : ℕ) ∈ R)
    (hR_card : R.card = (6 ^ (N + 1) - 1) / 5)
    (hf_supp : (f ^ 2).support ⊆ R ∪ R.image (· + 9 ^ N) ∪ {2 * 9 ^ N}) :
    ∃ (g : ℤ[X]) (R' : Finset ℕ),
      g.natDegree = 9 ^ (N + 1) ∧
      (∀ i, i ≤ 9 ^ (N + 1) → g.coeff i ≠ 0) ∧
      (∀ r ∈ R', r < 9 ^ (N + 1)) ∧
      (0 : ℕ) ∈ R' ∧
      R'.card = (6 ^ (N + 2) - 1) / 5 ∧
      (g ^ 2).support ⊆ R' ∪ R'.image (· + 9 ^ (N + 1)) ∪ {2 * 9 ^ (N + 1)} := by
  set d := 9 ^ N with hd_def
  have hd_pos : (0 : ℕ) < d := pow_pos (by norm_num) N
  have hf0 : f.coeff 0 ≠ 0 := hf_comp 0 (Nat.zero_le _)
  -- Build bad lambda set and choose good lambda
  obtain ⟨lam, hlam_ne, hlam_not_bad⟩ := exists_nonzero_not_in_finite
    ((Finset.range 8).biUnion fun j =>
      {-(baseP.coeff j * f.coeff d) / (baseP.coeff (j+1) * f.coeff 0)})
  have hlam_good : ∀ j ∈ Finset.range 8,
      baseP.coeff (j + 1) * f.coeff 0 * lam + baseP.coeff j * f.coeff d ≠ 0 := by
    intro j hj;
    contrapose! hlam_not_bad;
    simp +zetaDelta at *;
    refine' ⟨ j, hj, _ ⟩;
    rw [ Int.ediv_eq_of_eq_mul_left ];
    · exact mul_ne_zero ( baseP_coeff_ne_zero _ ( by linarith ) ) hf0;
    · linarith  -- Lambda avoidance: each linear equation has at most one root
  -- Define witnesses
  refine ⟨f * baseP.comp (C lam * X ^ d), R'_set R d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Degree
  · have hQ_deg := natDegree_baseP_comp lam d hlam_ne hd_pos
    have hf_ne : f ≠ 0 := by intro h; simp [h] at hf0
    have hQ_ne : baseP.comp (C lam * X ^ d) ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hQ_deg; omega
    rw [Polynomial.natDegree_mul hf_ne hQ_ne, hf_deg, hQ_deg, pow_succ]; ring
  -- Completeness
  · intro i hi; rw [pow_succ, mul_comm] at hi
    exact product_complete f d lam hd_pos hlam_ne hf_deg hf_comp hlam_good i hi
  -- R' range
  · intro r hr; show r < 9 ^ (N + 1); rw [pow_succ, mul_comm]
    exact R'_set_range R d hd_pos hR_range r hr
  -- 0 ∈ R'
  · exact R'_set_zero R d hR_zero
  -- R' card
  · rw [R'_set_card R d hd_pos hR_range, hR_card]; exact R'_card_arithmetic N
  -- Support
  · have h := step_support_containment f R d lam hlam_ne hR_range hR_zero hf_supp
    have h9 : 9 ^ (N + 1) = 9 * d := by rw [pow_succ, mul_comm]
    rw [h9]; convert h using 2 ; ring_nf

-- Full construction by induction
lemma pow9_construction (N : ℕ) :
    ∃ (f : ℤ[X]) (R : Finset ℕ),
      f.natDegree = 9 ^ N ∧
      (∀ i, i ≤ 9 ^ N → f.coeff i ≠ 0) ∧
      (∀ r ∈ R, r < 9 ^ N) ∧
      (0 : ℕ) ∈ R ∧
      R.card = (6 ^ (N + 1) - 1) / 5 ∧
      (f ^ 2).support ⊆ R ∪ R.image (· + 9 ^ N) ∪ {2 * 9 ^ N} := by
  induction N with
  | zero => exact pow9_construction_base
  | succ N ih =>
    obtain ⟨f, R, hf⟩ := ih
    exact pow9_construction_step N f R hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2

-- Structured Minkowski sum bound
def structuredSet (R : Finset ℕ) (d : ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion (fun j => R.image (· + j * d)) ∪ {m * d}

lemma structuredSet_card (R : Finset ℕ) (d m : ℕ)
    (hR : ∀ r ∈ R, r < d) :
    (structuredSet R d m).card = m * R.card + 1 := by
  unfold structuredSet;
  rw [ Finset.card_union_of_disjoint ] <;> norm_num;
  · rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun _ _ => Finset.card_image_of_injective _ fun x y hxy => by aesop ] ; norm_num;
    · intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
      intro a ha x hx; contrapose! hij; nlinarith [ hR a ha, hR x hx ] ;
  · exact fun x hx y hy => by nlinarith [ hR y hy ] ;

lemma structured_minkowski_containment (R : Finset ℕ) (d k : ℕ)
    (h0 : (0 : ℕ) ∈ R) :
    (R ∪ R.image (· + d) ∪ {2 * d}) + (Finset.range (k + 1)).image (· * d)
      ⊆ structuredSet R d (k + 2) := by
  intro x hx; simp_all +decide [ Finset.mem_add ] ;
  rcases hx with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, b, hb, rfl ⟩ );
  · unfold structuredSet;
    cases ha <;> simp_all +decide [ two_mul, add_mul ];
    · exact Or.inl ( by ring );
    · exact Or.inr ⟨ a + 2, by linarith, 0, h0, by ring ⟩;
  · rcases ha with ( ha | ⟨ c, hc, rfl ⟩ );
    · exact Finset.mem_union_left _ ( Finset.mem_biUnion.mpr ⟨ b, Finset.mem_range.mpr ( by linarith ), Finset.mem_image.mpr ⟨ a, ha, by ring ⟩ ⟩ );
    · exact Finset.mem_union_left _ ( Finset.mem_biUnion.mpr ⟨ b + 1, Finset.mem_range.mpr ( by linarith ), Finset.mem_image.mpr ⟨ c, hc, by ring ⟩ ⟩ )

lemma structured_minkowski_bound (R : Finset ℕ) (d k : ℕ)
    (hR : ∀ r ∈ R, r < d) (h0 : (0 : ℕ) ∈ R) :
    ((R ∪ R.image (· + d) ∪ {2 * d}) + (Finset.range (k + 1)).image (· * d)).card
      ≤ (k + 2) * R.card + 1 := by
  calc _ ≤ (structuredSet R d (k + 2)).card :=
        Finset.card_le_card (structured_minkowski_containment R d k h0)
    _ = (k + 2) * R.card + 1 := structuredSet_card R d (k + 2) hR

lemma finset_add_card_le (A B : Finset ℕ) : (A + B).card ≤ A.card * B.card :=
  Finset.card_image₂_le _ _ _

/-
Support bound for g²*P²
-/
lemma sq_prod_support_bound (g P : ℤ[X]) (R : Finset ℕ) (d a : ℕ)
    (hR_range : ∀ r ∈ R, r < d) (hR_zero : (0 : ℕ) ∈ R)
    (hg_supp : (g ^ 2).support ⊆ R ∪ R.image (· + d) ∪ {2 * d})
    (hP_supp : P.support ⊆ (Finset.range a).image (· * d)) :
    ((g * P) ^ 2).support.card ≤ 2 * a * R.card + 1 := by
  -- By support_mul_subset_add, we have supp(g²P²) ⊆ supp(g²) + supp(P²).
  have h_support : (g ^ 2 * P ^ 2).support ⊆ (g ^ 2).support + (P ^ 2).support := by
    exact support_mul_subset_add _ _
  -- By structured_minkowski_bound, we have card(supp(g²) + supp(P²)) ≤ (2*a-2+2)*#R+1 = 2*a*#R+1.
  have h_card : ((g ^ 2).support + (P ^ 2).support).card ≤ (2 * a * #R + 1) := by
    -- By structured_minkowski_bound, we have card(supp(g²) + supp(P²)) ≤ (2*a-2+2)*#R+1 = 2*a*#R+1. Use this fact.
    have h_card : ((g ^ 2).support + (P ^ 2).support).card ≤ ((R ∪ R.image (· + d) ∪ {2 * d}) + (Finset.range (2 * a - 1)).image (· * d)).card := by
      refine' Finset.card_le_card ( Finset.add_subset_add hg_supp _ );
      -- By support_mul_subset_add, we have supp(P²) ⊆ supp(P) + supp(P).
      have h_support_P : (P ^ 2).support ⊆ P.support + P.support := by
        convert support_mul_subset_add P P using 1 ; ring_nf;
      refine' h_support_P.trans _;
      intro x hx; obtain ⟨ y, hy, z, hz, rfl ⟩ := Finset.mem_add.mp hx; ( have := hP_supp hy; have := hP_supp hz; simp_all +decide [ Finset.mem_image ] ; );
      rcases ‹∃ a_1 < a, a_1 * d = y› with ⟨ i, hi, rfl ⟩ ; rcases ‹∃ a_1 < a, a_1 * d = z› with ⟨ j, hj, rfl ⟩ ; exact ⟨ i + j, by omega, by ring ⟩ ;
    refine le_trans h_card ?_;
    by_cases ha : a = 0;
    · aesop;
    · convert structured_minkowski_bound R d ( 2 * a - 2 ) hR_range hR_zero using 1;
      · rcases a with ( _ | _ | a ) <;> trivial;
      · rw [ Nat.sub_add_cancel ( by linarith [ Nat.pos_of_ne_zero ha ] ) ];
  simpa only [ mul_pow ] using le_trans ( Finset.card_le_card h_support ) h_card

/-
Existence of complete product g*P
-/
lemma exists_complete_prod (g : ℤ[X]) (d a : ℕ)
    (hd : 0 < d) (ha : 1 ≤ a)
    (hg_deg : g.natDegree = d)
    (hg_comp : ∀ i, i ≤ d → g.coeff i ≠ 0) :
    ∃ (P : ℤ[X]),
      P.support ⊆ (Finset.range a).image (· * d) ∧
      (g * P).natDegree = a * d ∧
      (∀ i, i ≤ a * d → (g * P).coeff i ≠ 0) := by
  -- Choose $\lambda \in \mathbb{Z}$ such that $\lambda \neq 0$ and $\lambda * g.coeff 0 + g.coeff d \neq 0$.
  obtain ⟨lambda, hlambda_ne_zero, hlambda_cond⟩ : ∃ lambda : ℤ, lambda ≠ 0 ∧ lambda * g.coeff 0 + g.coeff d ≠ 0 := by
    by_contra h_contra;
    exact h_contra ⟨ 2 * g.coeff d, mul_ne_zero two_ne_zero ( hg_comp d le_rfl ), by cases lt_or_gt_of_ne ( hg_comp d le_rfl ) <;> cases lt_or_gt_of_ne ( hg_comp 0 ( by linarith ) ) <;> nlinarith ⟩;
  refine' ⟨ ∑ j ∈ Finset.range a, Polynomial.monomial ( j * d ) ( lambda ^ j ), _, _, _ ⟩ <;> simp_all +decide ;
  · intro i hi; contrapose! hi; simp_all +decide [ Polynomial.coeff_monomial ] ;
    exact Finset.sum_eq_zero fun x hx => if_neg <| hi x <| Finset.mem_range.mp hx;
  · rw [ Polynomial.natDegree_mul' ] <;> simp_all +decide ;
    · rw [ Polynomial.natDegree_sum_eq_of_disjoint ] <;> norm_num [ Polynomial.natDegree_monomial, hlambda_ne_zero ];
      · induction ha <;> simp_all +decide [ Finset.range_add_one ];
        grind;
      · intro i hi j hj hij; contrapose hij; aesop;
    · refine' ⟨ by aesop_cat, _ ⟩;
      intro H; replace H := congr_arg ( fun p => p.coeff ( ( a - 1 ) * d ) ) H; rcases a with ( _ | _ | a ) <;> simp_all +decide [ Polynomial.coeff_monomial ] ;
      simp_all +decide [ ne_of_gt hd ];
  · -- Let's choose any $i$ such that $0 \leq i \leq a \cdot d$.
    intro i hi
    by_cases h_case : i % d = 0;
    · -- Since $i$ is a multiple of $d$, we can write $i = q * d$ for some $q$.
      obtain ⟨q, rfl⟩ : ∃ q, i = q * d := by
        exact exists_eq_mul_left_of_dvd <| Nat.dvd_of_mod_eq_zero h_case;
      rcases q with ( _ | q ) <;> simp_all +decide [ Polynomial.coeff_mul ];
      · simp_all +decide [ Polynomial.coeff_monomial ];
        cases a <;> simp_all +decide [ Finset.sum_range_succ' ];
        split_ifs <;> norm_num ; linarith;
      · rw [ Finset.sum_eq_add ( 0, ( q + 1 ) * d ) ( d, q * d ) ] <;> norm_num [ Polynomial.coeff_monomial ];
        · simp_all +decide [ hd.ne'];
          split_ifs <;> simp_all +decide [pow_succ, mul_assoc, mul_comm];
          exact fun h => hlambda_cond <| mul_left_cancel₀ ( pow_ne_zero q hlambda_ne_zero ) <| by linear_combination' h;
        · aesop;
        · intro a_1 b hab ha_1 hb_1; contrapose! hb_1; simp_all +decide [ add_mul ] ;
          -- Since $b$ is in the range $a$, we have $b = x * d$ for some $x$ in the range $a$.
          obtain ⟨x, hx⟩ : ∃ x ∈ Finset.range a, b = x * d := by
            exact Exists.elim ( Finset.exists_ne_zero_of_sum_ne_zero hb_1.2 ) fun x hx => ⟨ x, Finset.mem_range.mpr ( by nlinarith [ show x < a from Finset.mem_range.mp hx.1 ] ), by aesop ⟩;
          rcases lt_trichotomy x q with h | rfl | h <;> simp_all +decide [ add_comm, mul_comm ];
          · exact False.elim <| hb_1.1 <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by nlinarith;
          · nlinarith [ show x > q + 1 from lt_of_le_of_ne h ( Ne.symm <| by rintro rfl; exact ha_1 ( by nlinarith ) <| by nlinarith ) ];
        · exact fun h => False.elim <| h <| by ring;
    · -- Since $i$ is not a multiple of $d$, we can write $i = qd + r$ where $0 < r < d$ and $0 \leq q \leq a-1$.
      obtain ⟨q, r, hr⟩ : ∃ q r, 0 < r ∧ r < d ∧ i = q * d + r ∧ q < a := by
        use i / d, i % d;
        exact ⟨ Nat.pos_of_ne_zero h_case, Nat.mod_lt _ hd, by rw [ Nat.div_add_mod' ], by nlinarith [ Nat.mod_add_div i d, Nat.pos_of_ne_zero h_case ] ⟩;
      rw [ Polynomial.coeff_mul, Finset.sum_eq_single ( r, q * d ) ] <;> simp_all +decide [ Polynomial.coeff_monomial ];
      · exact ⟨ hg_comp r ( by linarith ), by rw [ Finset.sum_eq_single q ] <;> aesop ⟩;
      · intro a_1 b hab h; contrapose! h; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        -- Since $b$ is a multiple of $d$, we can write $b = k * d$ for some integer $k$.
        obtain ⟨k, hk⟩ : ∃ k, b = k * d := by
          exact exists_eq_mul_left_of_dvd ( by obtain ⟨ k, hk ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.2; aesop );
        -- Since $a_1 + k * d = q * d + r$ and $0 < r < d$, we must have $k = q$.
        have hk_eq_q : k = q := by
          nlinarith [ show a_1 ≤ d by exact le_of_not_gt fun h' => h.1 <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith ];
        grind;
      · exact fun h => False.elim <| h <| add_comm _ _

/-
Extension with (1 + μ*X^b)
-/
lemma exists_complete_extension_linear (f : ℤ[X]) (m b : ℕ)
    (hb : 0 < b) (hbm : b ≤ m)
    (hf_deg : f.natDegree = m)
    (hf_comp : ∀ i, i ≤ m → f.coeff i ≠ 0) :
    ∃ (mu : ℤ), mu ≠ 0 ∧
      (f * (1 + C mu * X ^ b)).natDegree = m + b ∧
      (∀ i, i ≤ m + b → (f * (1 + C mu * X ^ b)).coeff i ≠ 0) := by
  obtain ⟨mu, hmu⟩ : ∃ mu : ℤ, mu ≠ 0 ∧ ∀ i ∈ Finset.Icc b m, f.coeff i + mu * f.coeff (i - b) ≠ 0 := by
    -- Consider the set of bad values for mu, which are the values that make some coefficient of f*(1+mu*x^b) zero.
    set S : Finset ℤ := (Finset.Icc b m).image (fun i => -f.coeff i / f.coeff (i - b)) with hS_def;
    obtain ⟨ mu, hmu ⟩ := exists_nonzero_not_in_finite S;
    exact ⟨ mu, hmu.1, fun i hi => fun hi' => hmu.2 <| Finset.mem_image.mpr ⟨ i, hi, by rw [ Int.ediv_eq_of_eq_mul_left ] <;> first | linarith | specialize hf_comp ( i - b ) ( Nat.sub_le_of_le_add <| by linarith [ Finset.mem_Icc.mp hi ] ) ; aesop ⟩ ⟩;
  use mu; simp_all +decide ;
  constructor;
  · rw [ Polynomial.natDegree_mul' ] <;> simp_all +decide [ Polynomial.natDegree_add_eq_right_of_natDegree_lt ];
    exact ⟨ by specialize hf_comp 0; aesop_cat, by exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by norm_num [ hb.ne' ] ) ⟩;
  · intro i hi; by_cases hi' : i ≤ m <;> by_cases hi'' : i ≥ b <;> simp_all +decide [mul_add,
    Polynomial.coeff_eq_zero_of_natDegree_lt] ;
    · erw [ Polynomial.coeff_mul ];
      rw [ Finset.sum_eq_single ( i - b, b ) ] <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
      · simpa only [ mul_comm ] using hmu.2 i hi'' hi';
      · intros; omega;
    · rw [ Polynomial.coeff_mul ];
      rw [ Finset.sum_eq_zero ] <;> aesop;
    · rw [ Polynomial.coeff_mul, Finset.sum_eq_single ( i - b, b ) ] <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
      lia;
    · bv_omega

-- Support bound with (1+μx^b)
lemma sq_with_linear_support_bound (f : ℤ[X]) (mu : ℤ) (b : ℕ)
    (hmu : mu ≠ 0) (hb : 0 < b) (bound : ℕ)
    (hf_bound : (f ^ 2).support.card ≤ bound) :
    ((f * (1 + C mu * X ^ b)) ^ 2).support.card ≤ 3 * bound := by
  rw [ mul_pow ];
  refine le_trans ?_ ( mul_le_mul_right hf_bound 3 );
  have h_support : (f ^ 2 * (1 + C mu * X ^ b) ^ 2).support ⊆ (f ^ 2).support + ({0, b, 2 * b} : Finset ℕ) := by
    convert support_mul_subset_add _ _ using 2;
    ext ; simp +decide [sq, add_mul, mul_assoc, Polynomial.coeff_one, Polynomial.coeff_X_pow];
    ring_nf; split_ifs <;> simp_all +decide [pow_succ] ;
    aesop;
  refine le_trans ( Finset.card_le_card h_support ) ?_;
  convert finset_add_card_le _ _ using 1;
  grind

-- Support bound for f² via degree bound
lemma sq_support_card_le (f : ℤ[X]) :
    (f ^ 2).support.card ≤ 2 * f.natDegree + 1 := by
  calc (f ^ 2).support.card ≤ (f ^ 2).natDegree + 1 :=
        card_supp_le_succ_natDegree _
    _ ≤ 2 * f.natDegree + 1 := by
        have := Polynomial.natDegree_pow_le (n := 2) (p := f)
        omega

-- All-ones polynomial lemmas
lemma allOnes_natDegree (n : ℕ) (_hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), (X : ℤ[X]) ^ i).natDegree = n := by
  rw [Polynomial.natDegree_eq_of_degree_eq_some]
  erw [Polynomial.degree_eq_of_le_of_coeff_ne_zero] <;>
    norm_num [Polynomial.coeff_X_pow]
  rw [Polynomial.degree_le_iff_coeff_zero]; aesop

lemma allOnes_coeff (n i : ℕ) (hi : i ≤ n) :
    (∑ j ∈ Finset.range (n + 1), (X : ℤ[X]) ^ j).coeff i = 1 := by
  aesop

-- Small n case
lemma exists_complete_with_bound_small (n : ℕ) (hn : 0 < n) (hn80 : n ≤ 80) :
    ∃ (f : ℤ[X]) (N a : ℕ),
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      1 ≤ a ∧ a ≤ 8 ∧
      a * 9 ^ N ≤ n ∧
      (f ^ 2).support.card ≤ 6 * a * ((6 ^ (N + 1) - 1) / 5) + 3 := by
  set f := ∑ i ∈ Finset.range (n + 1), (X : ℤ[X]) ^ i with hf_def
  have hf_deg : f.natDegree = n := allOnes_natDegree n hn
  have hf_coeff : ∀ i : ℕ, i ≤ n → f.coeff i ≠ 0 := by
    intro i hi; rw [allOnes_coeff n i hi]; exact one_ne_zero
  have hf_sq : (f ^ 2).support.card ≤ 2 * n + 1 := by
    rw [← hf_deg]; exact sq_support_card_le f
  by_cases hn8 : n ≤ 8
  · refine ⟨f, 0, n, hf_deg, hf_coeff, ?_, hn8, ?_, ?_⟩
    · omega
    · simp
    · omega
  · push Not at hn8
    refine ⟨f, 1, n / 9, hf_deg, hf_coeff, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · simp; exact Nat.div_mul_le_self n 9
    · omega

/-- For a complete polynomial g of degree d, with structured support data R,
    and any n ≥ d, there exists a complete polynomial f of degree n
    with |supp(f²)| ≤ 6*(n/d)*|R| + 3. -/
lemma exists_complete_extension (g : ℤ[X]) (R : Finset ℕ) (d n : ℕ)
    (hd : 0 < d) (hdn : d ≤ n)
    (hg_deg : g.natDegree = d)
    (hg_comp : ∀ i, i ≤ d → g.coeff i ≠ 0)
    (hR_range : ∀ r ∈ R, r < d) (hR_zero : (0 : ℕ) ∈ R)
    (hg_supp : (g ^ 2).support ⊆ R ∪ R.image (· + d) ∪ {2 * d}) :
    ∃ f : ℤ[X],
      f.natDegree = n ∧
      (∀ i, i ≤ n → f.coeff i ≠ 0) ∧
      (f ^ 2).support.card ≤ 6 * (n / d) * R.card + 3 := by
  set a := n / d with ha_def
  set b := n % d with hb_def
  have hn_eq : n = a * d + b := by
    have h := Nat.div_add_mod n d; nlinarith [mul_comm d (n/d)]
  have hb_lt : b < d := Nat.mod_lt n hd
  have ha1 : 1 ≤ a := Nat.le_div_iff_mul_le hd |>.mpr (by linarith)
  -- Step 1: Get complete gP of degree ad
  obtain ⟨P, hP_supp, hgP_deg, hgP_comp⟩ := exists_complete_prod g d a hd ha1 hg_deg hg_comp
  -- Step 2: Support bound for (g*P)²
  have hgP_sq_bound : ((g * P) ^ 2).support.card ≤ 2 * a * R.card + 1 :=
    sq_prod_support_bound g P R d a hR_range hR_zero hg_supp hP_supp
  -- Step 3: Extend to degree n if b > 0
  by_cases hb0 : b = 0
  · -- b = 0: n = a*d, f = g*P
    have hn_ad : n = a * d := by omega
    refine ⟨g * P, by omega, fun i hi => hgP_comp i (by omega), ?_⟩
    calc ((g * P) ^ 2).support.card
        ≤ 2 * a * R.card + 1 := hgP_sq_bound
      _ ≤ 6 * a * R.card + 3 := by nlinarith
  · -- b > 0: extend with (1 + μx^b)
    have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
    have hbm : b ≤ a * d := by nlinarith
    obtain ⟨mu, hmu, hf_deg, hf_comp⟩ :=
      exists_complete_extension_linear (g * P) (a * d) b hb_pos hbm hgP_deg hgP_comp
    refine ⟨g * P * (1 + C mu * X ^ b), by omega, fun i hi => hf_comp i (by omega), ?_⟩
    have hf_sq_bound := sq_with_linear_support_bound (g * P) mu b hmu hb_pos
      (2 * a * R.card + 1) hgP_sq_bound
    calc ((g * P * (1 + C mu * X ^ b)) ^ 2).support.card
        ≤ 3 * (2 * a * R.card + 1) := hf_sq_bound
      _ = 6 * a * R.card + 3 := by ring

-- Large n case
lemma exists_complete_with_bound_large (n : ℕ) (hn : 81 ≤ n) :
    ∃ (f : ℤ[X]) (N a : ℕ),
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      1 ≤ a ∧ a ≤ 8 ∧
      a * 9 ^ N ≤ n ∧
      (f ^ 2).support.card ≤ 6 * a * ((6 ^ (N + 1) - 1) / 5) + 3 := by
  set N := Nat.log 9 n with hN_def
  have hN2 : 2 ≤ N := by
    have h81 : Nat.log 9 81 = 2 := by decide
    have hmono := @Nat.log_mono_right 9 81 n (by omega)
    omega
  have h9le : 9 ^ N ≤ n := Nat.pow_log_le_self 9 (by omega)
  have hlt9 : n < 9 ^ (N + 1) := Nat.lt_pow_succ_log_self (by omega) n
  set d := 9 ^ N with hd_def
  set a := n / d with ha_def
  have hd_pos : 0 < d := by positivity
  have ha1 : 1 ≤ a := Nat.le_div_iff_mul_le hd_pos |>.mpr (by linarith)
  have ha8 : a ≤ 8 := by
    have : a < 9 := by
      rw [ha_def, Nat.div_lt_iff_lt_mul hd_pos]
      linarith [show 9 ^ (N + 1) = 9 ^ N * 9 from pow_succ 9 N]
    omega
  have haN : a * d ≤ n := Nat.div_mul_le_self n d
  obtain ⟨g, R, hg_deg, hg_comp, hR_range, hR_zero, hR_card, hg_supp⟩ :=
    pow9_construction N
  obtain ⟨f, hf_deg, hf_comp, hf_bound⟩ :=
    exists_complete_extension g R d n hd_pos (by omega) hg_deg hg_comp
      hR_range hR_zero hg_supp
  exact ⟨f, N, a, hf_deg, hf_comp, ha1, ha8, by rwa [hd_def] at haN,
    by rw [hR_card] at hf_bound; exact hf_bound⟩

-- Combined proof
lemma exists_complete_with_bound_proof (n : ℕ) (hn : 0 < n) :
    ∃ (f : ℤ[X]) (N a : ℕ),
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      1 ≤ a ∧ a ≤ 8 ∧
      a * 9 ^ N ≤ n ∧
      (f ^ 2).support.card ≤ 6 * a * ((6 ^ (N + 1) - 1) / 5) + 3 := by
  by_cases hn80 : n ≤ 80
  · exact exists_complete_with_bound_small n hn hn80
  · push Not at hn80
    exact exists_complete_with_bound_large n (by omega)

lemma arithmetic_bound (n N a : ℕ) (_hn : 0 < n) (ha1 : 1 ≤ a) (ha8 : a ≤ 8)
    (haN : a * 9 ^ N ≤ n) :
    ((6 * a * ((6 ^ (N + 1) - 1) / 5) + 3 : ℕ) : ℝ) <
    (1 / 5 : ℝ) * (102 * (n : ℝ) ^ (Real.log 6 / Real.log 9) - 12) := by
  suffices h_suff : (6 * a * (6 ^ (N + 1) - 1) + 27 : ℝ) < 102 * (n : ℝ) ^ (Real.log 6 / Real.log 9) by
    convert div_lt_div_iff_of_pos_right ( by norm_num : ( 0 :ℝ ) < 5 ) |>.2 ( sub_lt_sub_right h_suff 12 ) using 1 ; norm_num ; ring_nf;
    · rw [ Nat.cast_div ] <;> norm_num ; ring;
      exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.mod_add_div ( 6 ^ N * 6 ) 5 ] ; norm_num [ Nat.pow_mod, Nat.mul_mod ] );
    · ring;
  have h_exp : (n : ℝ) ^ (Real.log 6 / Real.log 9) ≥ (a : ℝ) ^ (Real.log 6 / Real.log 9) * (6 : ℝ) ^ N := by
    refine' le_trans _ ( Real.rpow_le_rpow ( by positivity ) ( Nat.cast_le.mpr haN ) ( by positivity ) );
    norm_num [ Real.mul_rpow, Real.rpow_def_of_pos ];
    norm_num [ mul_assoc, mul_div_cancel₀, Real.exp_nat_mul, Real.exp_log ];
  have h_sqrt : (a : ℝ) ^ (Real.log 6 / Real.log 9) ≥ Real.sqrt a := by
    rw [ Real.sqrt_eq_rpow ] ; exact Real.rpow_le_rpow_of_exponent_le ( mod_cast ha1 ) ( by rw [ div_eq_mul_inv ] ; rw [ inv_eq_one_div, mul_one_div ] ; rw [ le_div_iff₀ ( by positivity ) ] ; norm_num [ ← Real.log_rpow, Real.log_le_log ] ) ;
  interval_cases a <;> norm_num at *;
  all_goals ring_nf at *; norm_num [ Real.sqrt_le_iff ] at *;
  all_goals nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 6 ) ( show N ≥ 0 by norm_num ) ]

/-- **Main Theorem.** For every positive integer `n`, there exists a polynomial `f(x)` of
degree `n` with all nonzero integer coefficients such that `f(x)²` has fewer than
`(1/5)(102 · n^{log₉ 6} - 12)` nonzero coefficients. -/
theorem exists_complete_poly_with_sparse_square (n : ℕ) (hn : 0 < n) :
    ∃ f : ℤ[X],
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      ((f ^ 2).support.card : ℝ) <
        (1 / 5 : ℝ) * (102 * (n : ℝ) ^ (Real.log 6 / Real.log 9) - 12) := by
  obtain ⟨f, N, a, hf_deg, hf_comp, ha1, ha8, haN, hf_supp⟩ :=
    exists_complete_with_bound_proof n hn
  exact ⟨f, hf_deg, hf_comp, calc
    ((f ^ 2).support.card : ℝ)
        ≤ ↑(6 * a * ((6 ^ (N + 1) - 1) / 5) + 3) := by exact_mod_cast hf_supp
      _ < (1 / 5 : ℝ) * (102 * (n : ℝ) ^ (Real.log 6 / Real.log 9) - 12) :=
          arithmetic_bound n N a hn ha1 ha8 haN⟩

/-!
# Base polynomial of degree 12 for the improved sparse square construction with real coefficients
-/

noncomputable section

lemma exists_cbrt5 : ∃ β : ℝ, 0 < β ∧ β ^ 3 = 5 := by
  exact ⟨5 ^ (1/3 : ℝ), by positivity,
    by rw [← Real.rpow_natCast, ← Real.rpow_mul] <;> norm_num⟩

lemma beta_pow4 {β : ℝ} (hβ3 : β ^ 3 = 5) : β ^ 4 = 5 * β := by
  have : β ^ 4 = β ^ 3 * β := by ring
  rw [this, hβ3]

-- Coefficient function
def c12 (β : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => (2/5 : ℝ) * β^2
  | 3 => -(2/5 : ℝ) * β^2
  | 4 => (2/5 : ℝ) * β^2 - (2/5 : ℝ) * β
  | 5 => -(2/5 : ℝ) * β^2 + (6/5 : ℝ) * β
  | 6 => (2/5 : ℝ) * β^2 - (12/5 : ℝ) * β + (4/5 : ℝ)
  | 7 => -(2/5 : ℝ) * β^2 + 4 * β - 4
  | 8 => -6 * β + 12
  | 9 => (9/4 : ℝ) * β^2 + (45/4 : ℝ) * β - (135/4 : ℝ)
  | 10 => -(225/8 : ℝ) * β^2 - (45/8 : ℝ) * β + (855/8 : ℝ)
  | 11 => (1755/32 : ℝ) * β^2 + (3375/32 : ℝ) * β - (10125/32 : ℝ)
  | 12 => (22275/64 : ℝ) * β^2 - (2025/64 : ℝ) * β - (58725/64 : ℝ)
  | _ => 0

-- Gap conditions proved individually using nlinarith
set_option maxHeartbeats 3200000 in
private lemma gap3 (β : ℝ) :
    c12 β 0 * c12 β 3 + c12 β 1 * c12 β 2 + c12 β 2 * c12 β 1 + c12 β 3 * c12 β 0 = 0 := by
  simp only [c12]; ring

set_option maxHeartbeats 3200000 in
private lemma gap4 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 0 * c12 β 4 + c12 β 1 * c12 β 3 + c12 β 2 * c12 β 2 +
    c12 β 3 * c12 β 1 + c12 β 4 * c12 β 0 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 3200000 in
private lemma gap5 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 0 * c12 β 5 + c12 β 1 * c12 β 4 + c12 β 2 * c12 β 3 +
    c12 β 3 * c12 β 2 + c12 β 4 * c12 β 1 + c12 β 5 * c12 β 0 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 3200000 in
private lemma gap6 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 0 * c12 β 6 + c12 β 1 * c12 β 5 + c12 β 2 * c12 β 4 +
    c12 β 3 * c12 β 3 + c12 β 4 * c12 β 2 + c12 β 5 * c12 β 1 +
    c12 β 6 * c12 β 0 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 3200000 in
private lemma gap7 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 0 * c12 β 7 + c12 β 1 * c12 β 6 + c12 β 2 * c12 β 5 +
    c12 β 3 * c12 β 4 + c12 β 4 * c12 β 3 + c12 β 5 * c12 β 2 +
    c12 β 6 * c12 β 1 + c12 β 7 * c12 β 0 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 3200000 in
private lemma gap8 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 0 * c12 β 8 + c12 β 1 * c12 β 7 + c12 β 2 * c12 β 6 +
    c12 β 3 * c12 β 5 + c12 β 4 * c12 β 4 + c12 β 5 * c12 β 3 +
    c12 β 6 * c12 β 2 + c12 β 7 * c12 β 1 + c12 β 8 * c12 β 0 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 6400000 in
private lemma gap16 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 4 * c12 β 12 + c12 β 5 * c12 β 11 + c12 β 6 * c12 β 10 +
    c12 β 7 * c12 β 9 + c12 β 8 * c12 β 8 + c12 β 9 * c12 β 7 +
    c12 β 10 * c12 β 6 + c12 β 11 * c12 β 5 + c12 β 12 * c12 β 4 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 6400000 in
private lemma gap17 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 5 * c12 β 12 + c12 β 6 * c12 β 11 + c12 β 7 * c12 β 10 +
    c12 β 8 * c12 β 9 + c12 β 9 * c12 β 8 + c12 β 10 * c12 β 7 +
    c12 β 11 * c12 β 6 + c12 β 12 * c12 β 5 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 6400000 in
private lemma gap18 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 6 * c12 β 12 + c12 β 7 * c12 β 11 + c12 β 8 * c12 β 10 +
    c12 β 9 * c12 β 9 + c12 β 10 * c12 β 8 + c12 β 11 * c12 β 7 +
    c12 β 12 * c12 β 6 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 6400000 in
private lemma gap19 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 7 * c12 β 12 + c12 β 8 * c12 β 11 + c12 β 9 * c12 β 10 +
    c12 β 10 * c12 β 9 + c12 β 11 * c12 β 8 + c12 β 12 * c12 β 7 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 6400000 in
private lemma gap20 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 8 * c12 β 12 + c12 β 9 * c12 β 11 + c12 β 10 * c12 β 10 +
    c12 β 11 * c12 β 9 + c12 β 12 * c12 β 8 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

set_option maxHeartbeats 6400000 in
private lemma gap21 (β : ℝ) (hβ3 : β ^ 3 = 5) :
    c12 β 9 * c12 β 12 + c12 β 10 * c12 β 11 +
    c12 β 11 * c12 β 10 + c12 β 12 * c12 β 9 = 0 := by
  simp only [c12]; have h4 := beta_pow4 hβ3; nlinarith [h4]

/-
Now the main construction
-/
set_option maxHeartbeats 12800000 in
theorem exists_base_poly_deg12 :
    ∃ P : ℝ[X],
      P.natDegree = 12 ∧
      (∀ i, i ≤ 12 → P.coeff i ≠ 0) ∧
      (∀ i ∈ ({3, 4, 5, 6, 7, 8, 16, 17, 18, 19, 20, 21} : Finset ℕ),
        (P ^ 2).coeff i = 0) := by
  -- Let's choose any β such that β^3 = 5 and 0 < β.
  obtain ⟨β, hβ_pos, hβ_cube⟩ : ∃ β : ℝ, 0 < β ∧ β^3 = 5 := by
    exact ⟨ 5 ^ ( 1/3 : ℝ ), by positivity, by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ⟩;
  use ∑ i ∈ Finset.range 13, Polynomial.monomial i ( c12 β i );
  refine' ⟨ _, _, _ ⟩;
  · refine' Polynomial.natDegree_eq_of_degree_eq_some _;
    rw [ Polynomial.degree_eq_of_le_of_coeff_ne_zero ] <;> norm_num [ Polynomial.coeff_monomial ];
    · rw [ Polynomial.degree_le_iff_coeff_zero ] ; norm_num [ Polynomial.coeff_monomial ];
      grind;
    · unfold c12; norm_num; nlinarith [ sq_nonneg β ] ;
  · intro i hi; interval_cases i <;> norm_num [ Polynomial.coeff_monomial ] <;> norm_num [ c12 ] <;> nlinarith [ pow_pos hβ_pos 2, pow_pos hβ_pos 3 ] ;
  · simp +decide [ sq, Polynomial.coeff_mul ];
    norm_num [ Finset.Nat.sum_antidiagonal_succ, Polynomial.coeff_monomial ];
    simp +decide only [← add_assoc];
    exact ⟨ gap3 β, gap4 β hβ_cube, gap5 β hβ_cube, gap6 β hβ_cube, gap7 β hβ_cube, gap8 β hβ_cube, gap16 β hβ_cube, gap17 β hβ_cube, gap18 β hβ_cube, gap19 β hβ_cube, gap20 β hβ_cube, gap21 β hβ_cube ⟩

end

-- ============================================================
-- R'_set13 infrastructure
-- ============================================================

def R'_set13 (R : Finset ℕ) (d : ℕ) : Finset ℕ :=
  R ∪ R.image (· + d) ∪ R.image (· + 2 * d) ∪ R.image (· + 3 * d) ∪ {4 * d} ∪
  R.image (· + 9 * d) ∪ R.image (· + 10 * d) ∪ R.image (· + 11 * d) ∪ R.image (· + 12 * d)

lemma R'_set13_range (R : Finset ℕ) (d : ℕ) (hd : 0 < d) (hR : ∀ r ∈ R, r < d) :
    ∀ r ∈ R'_set13 R d, r < 13 * d := by
  simp [R'_set13]; grind

lemma R'_set13_zero (R : Finset ℕ) (d : ℕ) (h0 : (0 : ℕ) ∈ R) :
    (0 : ℕ) ∈ R'_set13 R d := by
  unfold R'_set13; simp [h0]

lemma R'_set13_card (R : Finset ℕ) (d : ℕ) (hd : 0 < d) (hR : ∀ r ∈ R, r < d) :
    (R'_set13 R d).card = 8 * R.card + 1 := by
  simp +arith +decide [R'_set13]
  rw [Finset.card_insert_of_notMem] <;> norm_num [Finset.disjoint_left]
  · rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
        Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
        Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
        Finset.card_union_of_disjoint] <;>
      norm_num [Finset.disjoint_right]
    all_goals norm_num [Finset.card_image_of_injective, Function.Injective, hd.ne']
    grind; grind; grind
    · grind +splitImp
    · grind
    · grind
    · grind
    · grind
  · grind

lemma R'_card13_arithmetic (N : ℕ) :
    8 * ((8 ^ (N + 1) - 1) / 7) + 1 = (8 ^ (N + 2) - 1) / 7 := by
  rw [← Nat.mod_add_div (8 ^ (N + 1)) 7]
  norm_num [Nat.pow_succ', Nat.mul_mod, Nat.pow_mod, Nat.mul_mod]
  exact Eq.symm (Nat.div_eq_of_eq_mul_left (by norm_num) (Nat.sub_eq_of_eq_add (by
    linarith [Nat.div_add_mod (8 * 8 ^ N) 7,
              show (8 * 8 ^ N) % 7 = 1 by norm_num [Nat.mul_mod, Nat.pow_mod]])))

lemma pow13_construction_base :
    ∃ (f : ℝ[X]) (R : Finset ℕ),
      f.natDegree = 13 ^ 0 ∧
      (∀ i, i ≤ 13 ^ 0 → f.coeff i ≠ 0) ∧
      (∀ r ∈ R, r < 13 ^ 0) ∧
      (0 : ℕ) ∈ R ∧
      R.card = (8 ^ (0 + 1) - 1) / 7 ∧
      (f ^ 2).support ⊆ R ∪ R.image (· + 13 ^ 0) ∪ {2 * 13 ^ 0} := by
  refine' ⟨X + 1, {0}, _, _, _, _, _, _⟩ <;>
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X,
             Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · intro i hi; interval_cases i <;> norm_num
  · intro i hi; ring_nf at hi ⊢; aesop

-- ============================================================
-- Fix the base polynomial P₁₂
-- ============================================================

private noncomputable def baseP12 : ℝ[X] := exists_base_poly_deg12.choose

private lemma baseP12_deg : baseP12.natDegree = 12 :=
  exists_base_poly_deg12.choose_spec.1

private lemma baseP12_coeff_ne (i : ℕ) (hi : i ≤ 12) : baseP12.coeff i ≠ 0 :=
  exists_base_poly_deg12.choose_spec.2.1 i hi

private lemma baseP12_sq_gap (i : ℕ)
    (hi : i ∈ ({3, 4, 5, 6, 7, 8, 16, 17, 18, 19, 20, 21} : Finset ℕ)) :
    (baseP12 ^ 2).coeff i = 0 :=
  exists_base_poly_deg12.choose_spec.2.2 i hi

/-
============================================================
Generic polynomial lemmas for ℝ[X]
============================================================
-/
lemma comp_coeff_zero_of_not_dvd_real (p : ℝ[X]) (a : ℝ) (d k : ℕ)
    (_hd : 0 < d) (hk : ¬ d ∣ k) :
    (p.comp (C a * X ^ d)).coeff k = 0 := by
  rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
  norm_num [ mul_pow, ← pow_mul ];
  refine Finset.sum_eq_zero fun i hi => ?_;
  rw [ Polynomial.coeff_mul, Finset.sum_eq_zero ] ; aesop;
  intro x hx; by_cases hi : x.1 = 0 <;> simp_all +decide ;
  · aesop;
  · exact fun h => Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_C ] ; norm_num ; linarith [ Nat.pos_of_ne_zero hi ] ;

lemma support_mul_subset_add_real (f g : ℝ[X]) :
    (f * g).support ⊆ f.support + g.support :=
  AddMonoidAlgebra.support_mul f.toFinsupp g.toFinsupp

/-
============================================================
Composition and degree
============================================================
-/
lemma natDegree_baseP12_comp (a : ℝ) (d : ℕ) (ha : a ≠ 0) (_hd : 0 < d) :
    (baseP12.comp (C a * X ^ d)).natDegree = 12 * d := by
  norm_num [ baseP12_deg, Polynomial.natDegree_comp, Polynomial.natDegree_mul', ha ]

/-
============================================================
Existence of nonzero real not in finite set
============================================================
-/
lemma exists_nonzero_not_in_finite_real (S : Finset ℝ) : ∃ x : ℝ, x ≠ 0 ∧ x ∉ S := by
  exact Exists.imp ( by aesop ) ( Set.Infinite.nonempty ( Set.Infinite.diff ( Set.Ioi_infinite 0 ) ( S.finite_toSet ) ) )

/-
============================================================
Completeness: f * Q has all nonzero coefficients
============================================================
-/
lemma product_complete_13 (f : ℝ[X]) (d : ℕ) (lam : ℝ)
    (hd : 0 < d) (hlam : lam ≠ 0)
    (hf_deg : f.natDegree = d)
    (hf_comp : ∀ i, i ≤ d → f.coeff i ≠ 0)
    (hlam_good : ∀ j ∈ Finset.range 12,
      baseP12.coeff (j + 1) * f.coeff 0 * lam + baseP12.coeff j * f.coeff d ≠ 0) :
    ∀ i, i ≤ 13 * d → (f * baseP12.comp (C lam * X ^ d)).coeff i ≠ 0 := by
  intro i hi
  by_cases h : d ∣ i;
  · obtain ⟨ k, rfl ⟩ := h;
    have h_convolution : (f * baseP12.comp (C lam * X ^ d)).coeff (d * k) = ∑ j ∈ Finset.range (k + 1), f.coeff ((k - j) * d) * baseP12.coeff j * lam ^ j := by
      rw [ Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ];
      rw [ ← Finset.sum_subset ( show Finset.image ( fun j => d * ( k - j ) ) ( Finset.range ( k + 1 ) ) ⊆ Finset.range ( d * k + 1 ) from Finset.image_subset_iff.mpr fun j hj => Finset.mem_range.mpr <| by nlinarith [ Finset.mem_range.mp hj, Nat.sub_le k j ] ) ];
      · rw [ Finset.sum_image ];
        · refine' Finset.sum_congr rfl fun j hj => _;
          rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
          simp +decide [ mul_pow, ← mul_assoc, ← pow_mul, mul_comm d, baseP12_deg ];
          rw [ Finset.sum_eq_single j ] <;> simp +decide [mul_assoc];
          · rw [ show k * d - ( k - j ) * d = j * d by rw [ Nat.sub_eq_of_eq_add ] ; nlinarith only [ Nat.sub_add_cancel ( show j ≤ k from Finset.mem_range_succ_iff.mp hj ) ] ] ; norm_num [ Polynomial.coeff_C, Polynomial.coeff_X_pow, pow_mul', hlam ];
            norm_num [ ← pow_mul', Polynomial.coeff_C, Polynomial.coeff_X_pow, hlam ];
            norm_num [ Polynomial.coeff_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C, pow_mul' ];
            rw [ Finset.sum_eq_single ( 0, j * d ) ] <;> norm_num [ ← pow_mul', Polynomial.coeff_C, Polynomial.coeff_X_pow ];
            · norm_num [ Polynomial.coeff_zero_eq_eval_zero ];
            · aesop;
          · intro b hb hb'; rw [ Polynomial.coeff_mul, Finset.sum_eq_zero ] <;> simp +decide [ Polynomial.coeff_X_pow ] ;
            intro a b_1 hab hb_1; rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; simp +decide [ Polynomial.natDegree_pow ] ;
            contrapose! hb'; simp_all +decide [ Nat.sub_mul ];
            rw [ Nat.sub_sub_self ( by nlinarith ) ] at hab ; nlinarith;
          · exact fun h => Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith [ Finset.mem_range.mp hj, baseP12_deg ] ;
        · exact fun x hx y hy hxy => by nlinarith [ Nat.sub_add_cancel ( show x ≤ k from Finset.mem_range_succ_iff.mp hx ), Nat.sub_add_cancel ( show y ≤ k from Finset.mem_range_succ_iff.mp hy ) ] ;
      · intro x hx hx'; rw [ comp_coeff_zero_of_not_dvd_real ] ; aesop;
        · lia;
        · contrapose! hx';
          obtain ⟨ y, hy ⟩ := hx';
          exact Finset.mem_image.mpr ⟨ y, Finset.mem_range.mpr ( by nlinarith [ Nat.sub_add_cancel ( show x ≤ d * k from Finset.mem_range_succ_iff.mp hx ), Nat.sub_add_cancel ( show y ≤ k from by nlinarith [ Nat.sub_add_cancel ( show x ≤ d * k from Finset.mem_range_succ_iff.mp hx ) ] ) ] ), by nlinarith [ Nat.sub_add_cancel ( show x ≤ d * k from Finset.mem_range_succ_iff.mp hx ), Nat.sub_add_cancel ( show y ≤ k from by nlinarith [ Nat.sub_add_cancel ( show x ≤ d * k from Finset.mem_range_succ_iff.mp hx ) ] ) ] ⟩;
    by_cases hk : k ≤ 12;
    · by_cases hk : k = 0 ∨ k = 13;
      · interval_cases k <;> simp_all +decide [ Finset.sum_range_succ' ];
        exact baseP12_coeff_ne 0 bot_le;
      · have h_convolution_simplified : ∑ j ∈ Finset.range (k + 1), f.coeff ((k - j) * d) * baseP12.coeff j * lam ^ j = f.coeff d * baseP12.coeff (k - 1) * lam ^ (k - 1) + f.coeff 0 * baseP12.coeff k * lam ^ k := by
          rw [ Finset.sum_range_succ ];
          interval_cases k <;> norm_num [ Finset.sum_range_succ ];
          all_goals simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
        have h_convolution_simplified : f.coeff d * baseP12.coeff (k - 1) * lam ^ (k - 1) + f.coeff 0 * baseP12.coeff k * lam ^ k = lam ^ (k - 1) * (baseP12.coeff k * f.coeff 0 * lam + baseP12.coeff (k - 1) * f.coeff d) := by
          cases k <;> norm_num [ pow_succ' ] at * ; linarith;
        rcases k with ( _ | k ) <;> simp_all +decide;
    · norm_num [ show k = 13 by nlinarith ] at *;
      simp_all +decide [ Finset.sum_range_succ, Polynomial.coeff_eq_zero_of_natDegree_lt ];
      rw [ show baseP12.coeff 13 = 0 from _ ] ; simp_all +decide [ pow_succ, mul_assoc ];
      · exact baseP12_coeff_ne 12 ( by norm_num );
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ baseP12_deg ] ; norm_num;
  · -- Since $d \nmid i$, we can write $i = j * d + r$ where $0 < r < d$ and $0 \leq j \leq 12$.
    obtain ⟨j, r, hr⟩ : ∃ j r, 0 < r ∧ r < d ∧ i = j * d + r ∧ j ≤ 12 := by
      exact ⟨ i / d, i % d, Nat.pos_of_ne_zero fun con => h <| Nat.dvd_of_mod_eq_zero con, Nat.mod_lt _ hd, by rw [ Nat.div_add_mod' ], by nlinarith [ Nat.div_mul_le_self i d, Nat.mod_add_div i d, Nat.pos_of_ne_zero fun con => h <| Nat.dvd_of_mod_eq_zero con ] ⟩;
    rw [ Polynomial.coeff_mul, Finset.sum_eq_single ( r, j * d ) ] <;> simp_all +decide;
    · rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
      norm_num [ mul_pow, ← pow_mul ];
      rw [ Finset.sum_eq_single j ] <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
      · simp_all +decide [ mul_comm d, Polynomial.coeff_mul ];
        rw [ Finset.sum_eq_single ( 0, j * d ) ] <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
        · exact ⟨ hf_comp r ( by linarith ), baseP12_coeff_ne j ( by linarith ), by rw [ Polynomial.coeff_zero_eq_eval_zero ] ; norm_num [ hlam ] ⟩;
        · aesop;
      · intro k hk hk'; rw [ Polynomial.coeff_mul, Finset.sum_eq_zero ] <;> simp_all +decide ;
        intro a b hab hb; rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; simp_all +decide [ Polynomial.natDegree_pow ] ;
        exact Nat.pos_of_ne_zero fun ha => hk' <| by nlinarith only [ ha, hab, hr.1, hr.2.1 ] ;
    · intro a b hab hne; by_cases ha : a ≤ d <;> by_cases hb : d ∣ b <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ;
      · obtain ⟨ k, rfl ⟩ := hb; simp_all +decide [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ] ;
        exact False.elim <| hne ( by nlinarith [ show k = j by nlinarith ] ) ( by nlinarith [ show k = j by nlinarith ] );
      · rw [ comp_coeff_zero_of_not_dvd_real ] ; aesop;
        assumption;
    · exact fun h => False.elim <| h <| add_comm _ _

/-
============================================================
Support containment for the construction step
============================================================
-/
lemma step_support_containment_13 (f : ℝ[X]) (R : Finset ℕ) (d : ℕ) (lam : ℝ)
    (hR_range : ∀ r ∈ R, r < d) (h0 : 0 ∈ R)
    (hf_supp : (f ^ 2).support ⊆ R ∪ R.image (· + d) ∪ {2 * d}) :
    ((f * baseP12.comp (C lam * X ^ d)) ^ 2).support ⊆
      R'_set13 R d ∪ (R'_set13 R d).image (· + 13 * d) ∪ {26 * d} := by
  have h_support : (Polynomial.support (baseP12.comp (C lam * X ^ d) ^ 2)) ⊆ {0, 1, 2, 9, 10, 11, 12, 13, 14, 15, 22, 23, 24} * {d} := by
    intro i hi;
    -- If $i$ is in the support of $(baseP12.comp (C lam * X ^ d))^2$, then there exists $k$ such that $i = k * d$ and $k$ is in the support of $(baseP12)^2$.
    obtain ⟨k, hk⟩ : ∃ k, i = k * d ∧ k ∈ (baseP12 ^ 2).support := by
      have h_coeff : Polynomial.coeff ((baseP12.comp (C lam * X ^ d)) ^ 2) i = Polynomial.coeff ((baseP12 ^ 2).comp (C lam * X ^ d)) i := by
        norm_num [ Polynomial.comp_assoc ];
      simp_all +decide [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
      obtain ⟨ k, hk ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi; use k; simp_all +decide [ mul_pow, ← pow_mul' ] ;
      contrapose! hk; simp_all +decide ;
      rw [ Polynomial.coeff_mul, Finset.sum_eq_zero ] ; aesop;
      intro x hx; by_cases h : x.1 = 0 <;> simp_all +decide ;
      exact fun h' => Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_C ] ; norm_num ; linarith [ Nat.pos_of_ne_zero h ] ;
    have h_k_range : k ≤ 24 := by
      have h_k_range : k ≤ (baseP12 ^ 2).natDegree := by
        exact Polynomial.le_natDegree_of_mem_supp _ hk.2;
      exact h_k_range.trans ( by norm_num [ baseP12_deg ] );
    interval_cases k <;> simp_all +decide only [mem_mul];
    all_goals have := baseP12_sq_gap 3; have := baseP12_sq_gap 4; have := baseP12_sq_gap 5; have := baseP12_sq_gap 6; have := baseP12_sq_gap 7; have := baseP12_sq_gap 8; have := baseP12_sq_gap 16; have := baseP12_sq_gap 17; have := baseP12_sq_gap 18; have := baseP12_sq_gap 19; have := baseP12_sq_gap 20; have := baseP12_sq_gap 21; simp_all +decide ;
  have h_support_mul : (Polynomial.support (f ^ 2 * (baseP12.comp (C lam * X ^ d)) ^ 2)) ⊆ (R ∪ (R.image (· + d)) ∪ {2 * d}) + ({0, 1, 2, 9, 10, 11, 12, 13, 14, 15, 22, 23, 24} * {d}) := by
    exact Finset.Subset.trans ( support_mul_subset_add_real _ _ ) ( Finset.add_subset_add hf_supp h_support );
  refine' Finset.Subset.trans _ ( Finset.Subset.trans h_support_mul _ );
  · simp +decide [ mul_pow ];
  · simp +decide [ Finset.subset_iff, Finset.mem_add, Finset.mem_mul ];
    rintro x ( ⟨ z, hz, rfl ⟩ | ⟨ a, ha, z, hz, rfl ⟩ ) <;> simp_all +decide [ R'_set13 ];
    · grind;
    · rcases ha with ( ha | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [add_comm, add_left_comm];
      · grind;
      · rcases hz with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +arith +decide [ * ]

/-
============================================================
Construction step
============================================================
-/
set_option maxHeartbeats 6400000 in
lemma pow13_construction_step (N : ℕ)
    (f : ℝ[X]) (R : Finset ℕ)
    (hf_deg : f.natDegree = 13 ^ N)
    (hf_comp : ∀ i, i ≤ 13 ^ N → f.coeff i ≠ 0)
    (hR_range : ∀ r ∈ R, r < 13 ^ N)
    (hR_zero : (0 : ℕ) ∈ R)
    (hR_card : R.card = (8 ^ (N + 1) - 1) / 7)
    (hf_supp : (f ^ 2).support ⊆ R ∪ R.image (· + 13 ^ N) ∪ {2 * 13 ^ N}) :
    ∃ (g : ℝ[X]) (R' : Finset ℕ),
      g.natDegree = 13 ^ (N + 1) ∧
      (∀ i, i ≤ 13 ^ (N + 1) → g.coeff i ≠ 0) ∧
      (∀ r ∈ R', r < 13 ^ (N + 1)) ∧
      (0 : ℕ) ∈ R' ∧
      R'.card = (8 ^ (N + 2) - 1) / 7 ∧
      (g ^ 2).support ⊆ R' ∪ R'.image (· + 13 ^ (N + 1)) ∪ {2 * 13 ^ (N + 1)} := by
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam ≠ 0 ∧ ∀ j ∈ Finset.range 12, baseP12.coeff (j + 1) * f.coeff 0 * lam + baseP12.coeff j * f.coeff (13 ^ N) ≠ 0 := by
    have h_finite : Set.Finite {lam : ℝ | ∃ j ∈ Finset.range 12, baseP12.coeff (j + 1) * f.coeff 0 * lam + baseP12.coeff j * f.coeff (13 ^ N) = 0} := by
      have h_finite : ∀ j ∈ Finset.range 12, Set.Finite {lam : ℝ | baseP12.coeff (j + 1) * f.coeff 0 * lam + baseP12.coeff j * f.coeff (13 ^ N) = 0} := by
        intro j hj; by_cases h : baseP12.coeff ( j + 1 ) * f.coeff 0 = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
        · exact absurd h ( baseP12_coeff_ne _ ( by linarith ) );
        · exact Set.Finite.subset ( Set.finite_singleton ( - ( baseP12.coeff j * f.coeff ( 13 ^ N ) ) / ( baseP12.coeff ( j + 1 ) * f.coeff 0 ) ) ) fun x hx => eq_div_of_mul_eq ( mul_ne_zero h ( hf_comp 0 bot_le ) ) <| by linear_combination hx.out;
      exact Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet ( Finset.range 12 ) ) h_finite ) fun x hx => by aesop;
    exact Exists.imp ( by aesop ) ( exists_nonzero_not_in_finite_real h_finite.toFinset );
  refine' ⟨ f * baseP12.comp ( C lam * X ^ ( 13 ^ N ) ), R'_set13 R ( 13 ^ N ), _, _, _, _, _ ⟩;
  · rw [ Polynomial.natDegree_mul' ] <;> simp_all +decide [ pow_succ' ];
    · rw [ natDegree_baseP12_comp ] <;> norm_num [ hlam ] ; ring;
    · exact ⟨ by rintro rfl; simpa using hf_comp 0 bot_le, by exact ne_of_apply_ne Polynomial.natDegree <| by erw [ Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X_pow ] <;> norm_num [ hlam, baseP12_deg ] ⟩;
  · convert product_complete_13 f ( 13 ^ N ) lam _ _ _ _ _ using 1 <;> norm_num [ pow_succ', hf_deg, hlam ];
    · exact hf_comp;
    · exact fun j hj => hlam.2 j ( Finset.mem_range.mpr hj );
  · convert R'_set13_range R ( 13 ^ N ) ( by positivity ) hR_range using 1;
    rw [ pow_succ' ];
  · exact R'_set13_zero _ _ hR_zero;
  · refine' ⟨ _, _ ⟩;
    · grind +suggestions;
    · convert step_support_containment_13 f R ( 13 ^ N ) lam hR_range hR_zero hf_supp using 1 ; ring_nf

-- Full construction by induction
lemma pow13_construction (N : ℕ) :
    ∃ (f : ℝ[X]) (R : Finset ℕ),
      f.natDegree = 13 ^ N ∧
      (∀ i, i ≤ 13 ^ N → f.coeff i ≠ 0) ∧
      (∀ r ∈ R, r < 13 ^ N) ∧
      (0 : ℕ) ∈ R ∧
      R.card = (8 ^ (N + 1) - 1) / 7 ∧
      (f ^ 2).support ⊆ R ∪ R.image (· + 13 ^ N) ∪ {2 * 13 ^ N} := by
  induction N with
  | zero => exact pow13_construction_base
  | succ N ih =>
    obtain ⟨f, R, hf⟩ := ih
    exact pow13_construction_step N f R hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2

/-
============================================================
Support bounds (ℝ versions)
============================================================
-/
lemma sq_support_card_le_real (f : ℝ[X]) :
    (f ^ 2).support.card ≤ 2 * f.natDegree + 1 := by
  exact le_trans ( Finset.card_le_card ( show _ ⊆ Finset.range ( 2 * f.natDegree + 1 ) from fun i hi ↦ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Polynomial.le_natDegree_of_mem_supp _ hi |> le_trans <| by norm_num ) ) ( by norm_num )

lemma sq_prod_support_bound_real (g P : ℝ[X]) (R : Finset ℕ) (d a : ℕ)
    (hR_range : ∀ r ∈ R, r < d) (hR_zero : (0 : ℕ) ∈ R)
    (hg_supp : (g ^ 2).support ⊆ R ∪ R.image (· + d) ∪ {2 * d})
    (hP_supp : P.support ⊆ (Finset.range a).image (· * d)) :
    ((g * P) ^ 2).support.card ≤ 2 * a * R.card + 1 := by
  rw [ mul_pow ];
  have h_support_bound : (g ^ 2 * P ^ 2).support ⊆ (R ∪ R.image (· + d) ∪ {2 * d}) + (Finset.range (2 * a - 1)).image (· * d) := by
    refine' Finset.Subset.trans ( support_mul_subset_add_real _ _ ) ( Finset.add_subset_add hg_supp _ );
    intro x hx; simp_all +decide [ sq, Polynomial.coeff_mul ] ;
    obtain ⟨ i, j, hij ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx;
    simp_all +decide [ Finset.subset_iff ];
    rcases hP_supp hij.1 with ⟨ k, hk₁, hk₂ ⟩ ; rcases hP_supp hij.2 with ⟨ l, hl₁, hl₂ ⟩ ; exact ⟨ k + l, by omega, by linarith ⟩;
  refine le_trans ( Finset.card_le_card h_support_bound ) ?_;
  have := structured_minkowski_bound R d ( 2 * a - 1 - 1 ) hR_range hR_zero;
  rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.mul_succ ]

/-
============================================================
Complete product construction (ℝ version)
============================================================
-/
lemma exists_complete_prod_real (g : ℝ[X]) (d a : ℕ)
    (hd : 0 < d) (ha : 1 ≤ a)
    (hg_deg : g.natDegree = d)
    (hg_comp : ∀ i, i ≤ d → g.coeff i ≠ 0) :
    ∃ (P : ℝ[X]),
      P.support ⊆ (Finset.range a).image (· * d) ∧
      (g * P).natDegree = a * d ∧
      (∀ i, i ≤ a * d → (g * P).coeff i ≠ 0) := by
  by_cases h : g.coeff 0 ≠ 0;
  · by_cases h : g.coeff d ≠ 0;
    · obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam ≠ 0 ∧ lam * g.coeff 0 + g.coeff d ≠ 0 := by
        contrapose! h;
        linarith [ h 1 one_ne_zero, h 2 two_ne_zero ];
      refine' ⟨ ∑ j ∈ Finset.range a, Polynomial.monomial ( j * d ) ( lam ^ j ), _, _, _ ⟩;
      · intro i hi; simp_all +decide [ Polynomial.coeff_monomial ] ;
        contrapose! hi; simp_all +decide [ Finset.sum_ite ] ;
        exact Finset.sum_eq_zero fun x hx => False.elim <| hi x ( Finset.mem_range.mp <| Finset.mem_filter.mp hx |>.1 ) <| Finset.mem_filter.mp hx |>.2;
      · rw [ Polynomial.natDegree_mul' ] <;> simp_all +decide ;
        · rw [ Polynomial.natDegree_sum_eq_of_disjoint ];
          · rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.succ_mul ];
            simp +arith +decide [ Finset.range_add_one ];
            rw [ max_eq_left ] <;> norm_num;
            · ring;
            · exact ⟨ by linarith, fun b hb => by nlinarith ⟩;
          · intro i hi j hj hij; contrapose hij; aesop;
        · refine' ⟨ by aesop_cat, _ ⟩;
          intro H; replace H := congr_arg ( fun p => p.coeff 0 ) H; simp_all +decide [ Polynomial.coeff_monomial ] ;
          cases a <;> simp_all +decide [ Finset.sum_range_succ' ];
          have hd_ne : d ≠ 0 := Nat.ne_of_gt hd;
          norm_num [hd_ne] at H;
      · intro i hi
        by_cases hr : i % d = 0;
        · -- Since $i$ is a multiple of $d$, we can write $i = q * d$ for some $q$.
          obtain ⟨q, rfl⟩ : ∃ q, i = q * d := by
            exact exists_eq_mul_left_of_dvd <| Nat.dvd_of_mod_eq_zero hr;
          by_cases hq : q = 0 ∨ q = a;
          · rcases hq with ( rfl | rfl ) <;> simp_all +decide [ Polynomial.coeff_mul ];
            · simp_all +decide [ Polynomial.coeff_monomial ];
              cases a <;> simp_all +decide [ Finset.sum_range_succ' ];
              aesop;
            · rw [ Finset.sum_eq_single ( d, ( q - 1 ) * d ) ] <;> simp_all +decide [ Polynomial.coeff_monomial ];
              · rw [ Finset.sum_eq_single ( q - 1 ) ] <;> aesop;
              · intro a b hab h; rcases q with ( _ | q ) <;> simp_all +decide [ Nat.succ_mul ] ;
                by_cases ha : a ≤ d;
                · by_cases hb : b ≤ q * d;
                  · exact False.elim <| h ( by linarith ) ( by linarith );
                  · exact Or.inr <| Finset.sum_eq_zero fun x hx => if_neg <| by nlinarith [ Finset.mem_range.mp hx ] ;
                · exact Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith;
              · exact fun h => False.elim <| h <| by nlinarith [ Nat.sub_add_cancel ha ] ;
          · rw [ Polynomial.coeff_mul, Finset.sum_eq_add ( ( 0, q * d ) ) ( ( d, ( q - 1 ) * d ) ) ] <;> norm_num [ Polynomial.coeff_monomial ];
            · rcases q with ( _ | q ) <;> simp_all +decide [ Finset.sum_ite, Finset.filter_or, Finset.filter_eq' ];
              split_ifs <;> simp_all +decide [ ne_of_gt ];
              exact fun h => hlam.2 <| mul_left_cancel₀ ( pow_ne_zero q hlam.1 ) <| by linear_combination' h;
            · aesop;
            · intro a_1 b hab ha_1 hb_1; contrapose! hb_1; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
              -- Since $a_1 \neq 0$ and $b \neq q * d$, we must have $a_1 = d$ and $b = (q - 1) * d$.
              have ha1_eq_d : a_1 = d := by
                obtain ⟨ k, hk ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb_1.2;
                simp +zetaDelta at *;
                exact le_antisymm ( Nat.le_of_not_lt fun h => hb_1.1 <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith ) ( Nat.le_of_not_lt fun h => ha_1 ( by nlinarith [ show k = q by nlinarith ] ) <| by nlinarith [ show k = q by nlinarith ] );
              exact ⟨ ha1_eq_d, by nlinarith [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hq.1 ) ] ⟩;
            · exact fun h => False.elim <| h <| by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ q from Nat.pos_of_ne_zero fun h => hq <| Or.inl h ) ] ;
        · rw [ Polynomial.coeff_mul, Finset.sum_eq_single ( i % d, i / d * d ) ] <;> simp_all +decide [ Polynomial.coeff_monomial ];
          · simp_all +decide [ Finset.sum_ite, Finset.filter_or, Finset.filter_eq' ];
            split_ifs <;> simp_all +decide;
            · exact hg_comp _ ( Nat.le_of_lt ( Nat.mod_lt _ hd ) );
            · nlinarith [ Nat.mod_add_div i d, Nat.pos_of_ne_zero hr ];
          · intro a_1 b hab h; contrapose! h; simp_all +decide ;
            -- Since $g$ is a polynomial of degree $d$, we have $a_1 \leq d$. Also, since the sum is non-zero, there must be some $x \in \text{range } a$ such that $x * d = b$. This implies $b$ is a multiple of $d$, so $b = k * d$ for some integer $k$.
            have hb_mul_d : ∃ k : ℕ, b = k * d := by
              exact Exists.elim ( Finset.exists_ne_zero_of_sum_ne_zero h.2 ) fun x hx => ⟨ x, by aesop ⟩;
            cases' hb_mul_d with k hk; simp_all +decide ;
            norm_num [ show i = a_1 + k * d by linarith ] at *;
            norm_num [ Nat.add_mul_div_right _ _ hd ];
            exact ⟨ by rw [ Nat.mod_eq_of_lt ( lt_of_le_of_ne ( Nat.le_of_not_lt fun hi' => h.1 <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith ) <| by aesop ) ], Or.inl <| Or.inr <| lt_of_le_of_ne ( Nat.le_of_not_lt fun hi' => h.1 <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith ) <| by aesop ⟩;
          · exact fun h => False.elim <| h <| by linarith [ Nat.mod_add_div i d ] ;
    · aesop;
  · exact False.elim <| h <| hg_comp 0 bot_le

/-
============================================================
Linear extension (ℝ version)
============================================================
-/
lemma exists_complete_extension_linear_real (f : ℝ[X]) (m b : ℕ)
    (hb : 0 < b) (hbm : b ≤ m)
    (hf_deg : f.natDegree = m)
    (hf_comp : ∀ i, i ≤ m → f.coeff i ≠ 0) :
    ∃ (mu : ℝ), mu ≠ 0 ∧
      (f * (1 + C mu * X ^ b)).natDegree = m + b ∧
      (∀ i, i ≤ m + b → (f * (1 + C mu * X ^ b)).coeff i ≠ 0) := by
  obtain ⟨mu, hmu⟩ : ∃ mu : ℝ, mu ≠ 0 ∧ ∀ i ∈ Finset.Icc b m, f.coeff i + mu * f.coeff (i - b) ≠ 0 := by
    -- Choose mu such that it avoids all bad values.
    have h_bad_values : Set.Finite {mu : ℝ | ∃ i ∈ Finset.Icc b m, f.coeff i + mu * f.coeff (i - b) = 0} := by
      refine Set.Finite.subset ( Set.toFinite ( Finset.image ( fun i => -f.coeff i / f.coeff ( i - b ) ) ( Finset.Icc b m ) ) ) ?_;
      grind;
    exact Exists.imp ( by aesop ) ( Set.Infinite.nonempty ( h_bad_values.infinite_compl.diff ( Set.finite_singleton 0 ) ) );
  refine' ⟨ mu, hmu.1, _, _ ⟩;
  · rw [ Polynomial.natDegree_mul' ] <;> simp_all +decide [ Polynomial.natDegree_add_eq_right_of_natDegree_lt ];
    exact ⟨ by aesop_cat, by exact ne_of_apply_ne ( fun p => p.coeff b ) ( by aesop_cat ) ⟩;
  · intro i hi; by_cases hi' : i < b <;> simp_all +decide [mul_add] ;
    · rw [ Polynomial.coeff_mul ];
      rw [ Finset.sum_eq_zero ] <;> simp_all +decide;
      · exact hf_comp i ( by linarith );
      · grind;
    · rw [ Polynomial.coeff_mul ];
      rw [ Finset.sum_eq_single ( i - b, b ) ] <;> simp_all +decide ;
      · by_cases hi'' : i ≤ m;
        · simpa only [ mul_comm ] using hmu.2 i hi' hi'';
        · rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ( by linarith ) ] ; aesop;
      · intros; omega;

lemma sq_with_linear_support_bound_real (f : ℝ[X]) (mu : ℝ) (b : ℕ)
    (hmu : mu ≠ 0) (hb : 0 < b) (bound : ℕ)
    (hf_bound : (f ^ 2).support.card ≤ bound) :
    ((f * (1 + C mu * X ^ b)) ^ 2).support.card ≤ 3 * bound := by
  have h_support : ((f * (1 + C mu * X ^ b)) ^ 2).support ⊆ (f ^ 2).support + ({0, b, 2 * b} : Finset ℕ) := by
    rw [ mul_pow ];
    convert support_mul_subset_add_real _ _ using 2;
    ext; simp [pow_two];
    ring_nf;
    norm_num [ Polynomial.coeff_one, Polynomial.coeff_X_pow, mul_assoc, sq ];
    grind;
  refine le_trans ( Finset.card_mono h_support ) ?_;
  refine' le_trans ( Finset.card_image₂_le _ _ _ ) _;
  grind

/-
============================================================
Extension to arbitrary degree (ℝ version)
============================================================
-/
lemma exists_complete_extension_real (g : ℝ[X]) (R : Finset ℕ) (d n : ℕ)
    (hd : 0 < d) (hdn : d ≤ n)
    (hg_deg : g.natDegree = d)
    (hg_comp : ∀ i, i ≤ d → g.coeff i ≠ 0)
    (hR_range : ∀ r ∈ R, r < d) (hR_zero : (0 : ℕ) ∈ R)
    (hg_supp : (g ^ 2).support ⊆ R ∪ R.image (· + d) ∪ {2 * d}) :
    ∃ f : ℝ[X],
      f.natDegree = n ∧
      (∀ i, i ≤ n → f.coeff i ≠ 0) ∧
      (f ^ 2).support.card ≤ 6 * (n / d) * R.card + 3 := by
  -- Set a = n/d, b = n%d. Then n = a*d + b, b < d, a ≥ 1 (since d ≤ n).
  set a := n / d
  set b := n % d
  have h_n : n = a * d + b := by
    rw [ Nat.div_add_mod' ]
  have hb : b < d := by
    exact Nat.mod_lt _ hd
  have ha : 1 ≤ a := by
    exact Nat.div_pos hdn hd;
  -- Step 1: Get P from exists_complete_prod_real. Then g*P has degree a*d with all nonzero coefficients.
  obtain ⟨P, hP_supp, hP_deg, hP_comp⟩ : ∃ P : ℝ[X], P.support ⊆ (Finset.range a).image (· * d) ∧ (g * P).natDegree = a * d ∧ (∀ i, i ≤ a * d → (g * P).coeff i ≠ 0) := by
    convert exists_complete_prod_real g d a hd ha hg_deg hg_comp using 1;
  -- Step 2: Support bound for (g*P)² by sq_prod_support_bound_real: ≤ 2*a*|R|+1.
  have h_support_bound : ((g * P) ^ 2).support.card ≤ 2 * a * R.card + 1 := by
    apply sq_prod_support_bound_real g P R d a hR_range hR_zero hg_supp hP_supp;
  by_cases hb_zero : b = 0;
  · grind;
  · -- Step 3: Extend with exists_complete_extension_linear_real to get f = g*P*(1+mu*X^b) of degree a*d+b = n.
    obtain ⟨mu, hmu_ne_zero, hmu_deg, hmu_comp⟩ : ∃ mu : ℝ, mu ≠ 0 ∧ (g * P * (1 + C mu * X ^ b)).natDegree = a * d + b ∧ (∀ i, i ≤ a * d + b → (g * P * (1 + C mu * X ^ b)).coeff i ≠ 0) := by
      apply exists_complete_extension_linear_real;
      · positivity;
      · nlinarith [ Nat.pos_of_ne_zero hb_zero ];
      · exact hP_deg;
      · exact hP_comp;
    refine' ⟨ g * P * ( 1 + C mu * X ^ b ), hmu_deg.trans ( h_n ▸ rfl ), fun i hi => hmu_comp i ( h_n ▸ hi ), _ ⟩;
    have := sq_with_linear_support_bound_real ( g * P ) mu b hmu_ne_zero ( Nat.pos_of_ne_zero hb_zero ) ( 2 * a * R.card + 1 ) h_support_bound; norm_num at *; linarith;

/-
============================================================
Small n and large n cases
============================================================
-/
set_option maxRecDepth 10000 in
lemma exists_complete_with_bound_small_improved (n : ℕ) (hn : 0 < n) (hn_small : n ≤ 168) :
    ∃ (f : ℝ[X]) (N a : ℕ),
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      1 ≤ a ∧ a ≤ 12 ∧
      a * 13 ^ N ≤ n ∧
      (f ^ 2).support.card ≤ 6 * a * ((8 ^ (N + 1) - 1) / 7) + 3 := by
  -- Consider two cases: $n \leq 12$ and $13 \leq n \leq 168$.
  by_cases hn_case : n ≤ 12;
  · use ∑ i ∈ Finset.range (n + 1), Polynomial.X ^ i;
    refine' ⟨ 0, n, _, _, _, _, _ ⟩ <;> norm_num;
    · interval_cases n <;> erw [ Polynomial.natDegree_sum_eq_of_disjoint ] <;> norm_num;
      all_goals simp +decide [ Set.Pairwise ];
    · linarith;
    · linarith;
    · refine' le_trans ( sq_support_card_le_real _ ) _;
      erw [ Polynomial.natDegree_sum_eq_of_disjoint ] <;> norm_num;
      · interval_cases n <;> trivial;
      · aesop_cat;
  · refine' ⟨ ∑ i ∈ Finset.range ( n + 1 ), ( Polynomial.X : ℝ[X] ) ^ i, 1, n / 13, _, _, _, _, _, _ ⟩ <;> norm_num;
    · interval_cases n <;> erw [ Polynomial.natDegree_sum_eq_of_disjoint ] <;> norm_num;
      all_goals norm_num [ Set.Pairwise ];
      all_goals decide;
    · omega;
    · omega;
    · exact Nat.div_mul_le_self _ _;
    · refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.range ( 2 * n + 1 );
      · intro i hi; simp_all +decide [ sq, Finset.sum_mul _ _ _ ] ;
        contrapose! hi;
        refine Finset.sum_eq_zero fun j hj => ?_ ; simp_all +decide [ Polynomial.coeff_mul ];
        exact Finset.sum_eq_zero fun x hx => by rw [ Finset.mem_antidiagonal ] at hx; split_ifs <;> linarith;
      · interval_cases n <;> decide

lemma exists_complete_with_bound_large_improved (n : ℕ) (hn : 169 ≤ n) :
    ∃ (f : ℝ[X]) (N a : ℕ),
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      1 ≤ a ∧ a ≤ 12 ∧
      a * 13 ^ N ≤ n ∧
      (f ^ 2).support.card ≤ 6 * a * ((8 ^ (N + 1) - 1) / 7) + 3 := by
  -- By Lemma 2, there exists a polynomial g of degree d = 13^N such that g² has the required support property.
  obtain ⟨g, R, hg_deg, hg_comp, hR_range, hR_zero, hR_card, hg_supp⟩ : ∃ g : ℝ[X], ∃ R : Finset ℕ,
    g.natDegree = 13 ^ (Nat.log 13 n) ∧
    (∀ i, i ≤ 13 ^ (Nat.log 13 n) → g.coeff i ≠ 0) ∧
    (∀ r ∈ R, r < 13 ^ (Nat.log 13 n)) ∧
    (0 : ℕ) ∈ R ∧
    R.card = (8 ^ (Nat.log 13 n + 1) - 1) / 7 ∧
    (g ^ 2).support ⊆ R ∪ R.image (fun r => r + 13 ^ (Nat.log 13 n)) ∪ {2 * 13 ^ (Nat.log 13 n)} := by
      exact pow13_construction (Nat.log 13 n);
  obtain ⟨f, hf_deg, hf_comp, hf_supp⟩ := exists_complete_extension_real g R (13 ^ (Nat.log 13 n)) n (by
  positivity) (by
  exact Nat.pow_log_le_self 13 ( by linarith )) hg_deg hg_comp hR_range hR_zero hg_supp;
  refine' ⟨ f, Nat.log 13 n, n / 13 ^ Nat.log 13 n, hf_deg, hf_comp, _, _, _, _ ⟩;
  · exact Nat.div_pos ( Nat.pow_log_le_self 13 ( by linarith ) ) ( by positivity );
  · exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by rw [ mul_comm, ← Nat.pow_succ' ] ; exact Nat.lt_pow_succ_log_self ( by decide ) _ );
  · exact Nat.div_mul_le_self _ _;
  · aesop

lemma exists_complete_with_bound_proof_improved (n : ℕ) (hn : 0 < n) :
    ∃ (f : ℝ[X]) (N a : ℕ),
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      1 ≤ a ∧ a ≤ 12 ∧
      a * 13 ^ N ≤ n ∧
      (f ^ 2).support.card ≤ 6 * a * ((8 ^ (N + 1) - 1) / 7) + 3 := by
  by_cases hn168 : n ≤ 168
  · exact exists_complete_with_bound_small_improved n hn hn168
  · push Not at hn168
    exact exists_complete_with_bound_large_improved n (by omega)

/-
============================================================
Arithmetic bound
============================================================
-/
lemma arithmetic_bound_improved (n N a : ℕ) (ha1 : 1 ≤ a) (ha12 : a ≤ 12)
    (haN : a * 13 ^ N ≤ n) :
    ((6 * a * ((8 ^ (N + 1) - 1) / 7) + 3 : ℕ) : ℝ) <
    (1 / 7 : ℝ) * (170 * (n : ℝ) ^ (Real.log 8 / Real.log 13) - 14) := by
  rw [ Nat.cast_add, Nat.cast_mul, Nat.cast_mul ];
  -- Since $n \geq a \cdot 13^N$, we have $n^{\alpha} \geq a^{\alpha} \cdot 8^N$.
  have h_n_alpha : (n : ℝ) ^ (Real.log 8 / Real.log 13) ≥ (a : ℝ) ^ (Real.log 8 / Real.log 13) * 8 ^ N := by
    refine' le_trans _ ( Real.rpow_le_rpow ( by positivity ) ( Nat.cast_le.mpr haN ) ( by positivity ) );
    rw [ Nat.cast_mul, Real.mul_rpow ( by positivity ) ( by positivity ) ];
    norm_num [ Real.rpow_def_of_pos, mul_div ];
    norm_num [ mul_div_right_comm, Real.exp_nat_mul, Real.exp_log ];
  -- Since $a^{\alpha} \geq \sqrt{a}$, we have $170 \cdot a^{\alpha} \cdot 8^N \geq 170 \cdot \sqrt{a} \cdot 8^N$.
  have h_sqrt : (a : ℝ) ^ (Real.log 8 / Real.log 13) ≥ Real.sqrt a := by
    rw [ Real.sqrt_eq_rpow ];
    exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast ) ( by rw [ div_le_div_iff₀ ( by positivity ) ( by positivity ) ] ; norm_num [ mul_comm, ← Real.log_rpow, Real.log_le_log ] );
  rw [ Nat.cast_div ] <;> norm_num;
  · interval_cases a <;> norm_num at *;
    all_goals ring_nf at *; norm_num [ Real.sqrt_le_iff ] at *;
    all_goals nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 8 ) ( show N ≥ 0 by norm_num ) ];
  · exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.mod_add_div ( 8 ^ ( N + 1 ) ) 7 ] ; norm_num [ Nat.pow_mod ] )

-- ============================================================
-- Main improved theorem
-- ============================================================

theorem exists_complete_poly_with_sparse_square_improved (n : ℕ) (hn : 0 < n) :
    ∃ f : ℝ[X],
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      ((f ^ 2).support.card : ℝ) <
        (1 / 7 : ℝ) * (170 * (n : ℝ) ^ (Real.log 8 / Real.log 13) - 14) := by
  obtain ⟨f, N, a, hf_deg, hf_comp, ha1, ha12, haN, hf_supp⟩ :=
    exists_complete_with_bound_proof_improved n hn
  exact ⟨f, hf_deg, hf_comp, calc
    ((f ^ 2).support.card : ℝ)
        ≤ ↑(6 * a * ((8 ^ (N + 1) - 1) / 7) + 3) := by exact_mod_cast hf_supp
      _ < (1 / 7 : ℝ) * (170 * (n : ℝ) ^ (Real.log 8 / Real.log 13) - 14) :=
          arithmetic_bound_improved n N a ha1 ha12 haN⟩

#print axioms exists_complete_poly_with_sparse_square
-- 'Erdos485.exists_complete_poly_with_sparse_square' depends on axioms: [propext,
-- Classical.choice,
-- Quot.sound]

#print axioms exists_complete_poly_with_sparse_square_improved
-- 'Erdos485.exists_complete_poly_with_sparse_square_improved' depends on axioms: [propext,
-- Classical.choice,
-- Quot.sound]

end

end Erdos485b
