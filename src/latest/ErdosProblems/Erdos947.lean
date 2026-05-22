/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 947.
https://www.erdosproblems.com/forum/thread/947

Informal authors:
- ChatGPT
- Wouter van Doorn

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/947#post-4068
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem947.lean
-/
/-
I asked ChatGPT to write a TeX-file explaining the proof of a result by Mirsky-Newman and Davenport-Rado, which states that no exact covering system exists with distinct moduli (except for the trivial case of a single congruence class). They thereby solved Erdos Problem #947 (https://www.erdosproblems.com/947). This TeX-file was given to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), which managed to formalize it into Lean, the result of which can be found below.

-/

import Mathlib

namespace Erdos947

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.style.induction false
set_option linter.style.refine false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 50000000

/-
An exact covering system is a finite collection of congruence classes such that every integer satisfies exactly one of the congruences.
-/
def IsExactCoveringSystem (l : List (ℤ × ℕ)) : Prop :=
  (∀ p ∈ l, 0 ≤ p.1 ∧ p.1 < p.2) ∧
  (∀ m : ℤ, ∃! i : Fin l.length, let (a, n) := l.get i; m ≡ a [ZMOD n])

/-
The coefficient of $x^m$ in $(1-x^n)\sum_{k=0}^\infty x^{a+kn}$ is 1 if $m=a$ and 0 otherwise.
-/
open PowerSeries

def geometric_progression (a n : ℕ) : PowerSeries ℂ := PowerSeries.mk (fun m => if m % n = a then 1 else 0)

theorem coeff_geometric_progression_mul (a n m : ℕ) (h_a : a < n) :
  coeff m ((1 - (X : PowerSeries ℂ)^n) * geometric_progression a n) = if m = a then 1 else 0 := by
    simp +decide [ sub_mul, one_mul ];
    split_ifs with h <;> simp_all +decide [ PowerSeries.coeff_mul ];
    · simp +decide [ PowerSeries.coeff_X_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ];
      simp +decide [geometric_progression];
      rw [ if_pos ( Nat.mod_eq_of_lt h_a ), if_neg ( by linarith ) ] ; norm_num;
    · simp +decide [ PowerSeries.coeff_X_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ];
      split_ifs <;> simp_all +decide [ geometric_progression ];
      · rename_i hm
        rw [Nat.mod_eq_sub_mod hm]
        simp
      · rw [ Nat.mod_eq_of_lt ] <;> omega

/-
$(1-x^n)\sum_{k=0}^\infty x^{a+kn} = x^a$ as formal power series.
-/
open PowerSeries

theorem geometric_progression_mul (a n : ℕ) (h_a : a < n) :
  (1 - (X : PowerSeries ℂ)^n) * geometric_progression a n = (X : PowerSeries ℂ)^a := by
    convert PowerSeries.ext fun m => ?_ using 1;
    exact inferInstance;
    convert coeff_geometric_progression_mul a n m h_a using 1;
    simp +decide [ PowerSeries.coeff_X_pow ]

/-
Let $\{a_i\pmod{n_i}\}_{i=1}^k$ be an exact covering system. Then $\sum_{i=1}^k \sum_{k=0}^\infty x^{a_i+kn_i} = \sum_{m=0}^\infty x^m$.
-/
open PowerSeries

theorem power_series_identity_geometric (l : List (ℤ × ℕ)) (h : IsExactCoveringSystem l) :
  (∑ i : Fin l.length, geometric_progression (l.get i).1.toNat (l.get i).2) = geometric_progression 0 1 := by
    -- By definition of $IsExactCoveringSystem$, for any integer $x$, there exists a unique $i$ such that $x \equiv a_i \pmod{n_i}$.
    have h_unique : ∀ x : ℕ, ∃! i : Fin l.length, x ≡ (l.get i).1.toNat [MOD (l.get i).2] := by
      intro x
      obtain ⟨i, hi⟩ := h.2 (x : ℤ);
      use i;
      convert hi using 1;
      · simp +decide [ ← Int.natCast_modEq_iff ];
        rw [ max_eq_left ( by have := h.1 ( l.get i ) ( by simp +decide ) ; aesop ) ];
      · simp +decide [ ← Int.natCast_modEq_iff ];
        congr! 3;
        exact max_eq_left ( h.1 _ ( by simp ) |>.1 );
    -- By definition of $geometric_progression$, we know that the coefficient of $x^m$ in $\sum_{i=1}^k \sum_{k=0}^\infty x^{a_i+kn_i}$ is $\sum_{i=1}^k c_{i,m}$, where $c_{i,m}$ is the coefficient of $x^m$ in the $i$-th term.
    have h_coeff : ∀ m : ℕ, (∑ i : Fin l.length, (geometric_progression ((l.get i).1.toNat) ((l.get i).2) : PowerSeries ℂ).coeff m) = (geometric_progression 0 1 : PowerSeries ℂ).coeff m := by
      intro m
      obtain ⟨i, hi, hiu⟩ := h_unique m
      simp [geometric_progression]
      have hcard : (Finset.univ.filter fun x : Fin l.length => m % l[(x : ℕ)].2 = l[(x : ℕ)].1.toNat).card = 1 := by
        apply Finset.card_eq_one.mpr
        refine ⟨i, ?_⟩
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hj
          apply hiu j
          have hlt_j : l[(j : ℕ)].1.toNat < l[(j : ℕ)].2 := by
            have := h.1 (l.get j) (by simp)
            aesop
          rw [Nat.ModEq]
          exact hj.trans (Nat.mod_eq_of_lt hlt_j).symm
        · intro hji
          have hlt_i : l[(i : ℕ)].1.toNat < l[(i : ℕ)].2 := by
            have := h.1 (l.get i) (by simp)
            aesop
          have hi_eq : m % l[(i : ℕ)].2 = l[(i : ℕ)].1.toNat := by
            have hi_eq_mod : m % l[(i : ℕ)].2 = l[(i : ℕ)].1.toNat % l[(i : ℕ)].2 := by
              simpa [Nat.ModEq] using hi
            exact hi_eq_mod.trans (Nat.mod_eq_of_lt hlt_i)
          simpa [hji] using hi_eq
      simp [Nat.mod_one, hcard]
    ext m; specialize h_coeff m; aesop;

/-
The identity $\sum x^{a_i} \prod_{j \ne i} (1-x^{n_j}) \cdot (1-x) = \prod (1-x^{n_i})$ holds in formal power series.
-/
open PowerSeries

noncomputable def P_series (l : List (ℤ × ℕ)) : PowerSeries ℂ :=
  ∑ i : Fin l.length, (X : PowerSeries ℂ)^(l.get i).1.toNat * ∏ j ∈ (Finset.univ.erase i), (1 - (X : PowerSeries ℂ)^(l.get j).2)

noncomputable def Target_series (l : List (ℤ × ℕ)) : PowerSeries ℂ :=
  ∏ i : Fin l.length, (1 - (X : PowerSeries ℂ)^(l.get i).2)

theorem power_series_identity_mul (l : List (ℤ × ℕ)) (h : IsExactCoveringSystem l) :
  P_series l * (1 - X) = Target_series l := by
    -- By definition of $P_series$ and $Target_series$, we can rewrite the left-hand side.
    have h_lhs : P_series l * (1 - PowerSeries.X) = (∑ i : Fin l.length, (PowerSeries.X : PowerSeries ℂ)^(l.get i |>.1).toNat * (∏ j ∈ Finset.univ.erase i, (1 - (PowerSeries.X : PowerSeries ℂ)^(l.get j |>.2)))) * (1 - PowerSeries.X) := by
      rfl;
    -- Apply the identity $\sum_{i=1}^k \sum_{k=0}^\infty x^{a_i+kn_i} = \sum_{m=0}^\infty x^m$ to rewrite the left-hand side.
    have h_sum : (∑ i : Fin l.length, (PowerSeries.X : PowerSeries ℂ)^(l.get i |>.1).toNat * (∏ j ∈ Finset.univ.erase i, (1 - (PowerSeries.X : PowerSeries ℂ)^(l.get j |>.2)))) = (∏ i : Fin l.length, (1 - (PowerSeries.X : PowerSeries ℂ)^(l.get i |>.2))) * (∑ i : Fin l.length, geometric_progression (l.get i |>.1).toNat (l.get i |>.2)) := by
      -- By definition of $geometric_progression$, we know that $geometric_progression (l.get i |>.1).toNat (l.get i |>.2) = \sum_{k=0}^\infty x^{(l.get i |>.1).toNat + k(l.get i |>.2)}$.
      have h_geo : ∀ i : Fin l.length, (PowerSeries.X : PowerSeries ℂ)^(l.get i |>.1).toNat = (1 - (PowerSeries.X : PowerSeries ℂ)^(l.get i |>.2)) * geometric_progression (l.get i |>.1).toNat (l.get i |>.2) := by
        intro i
        have := h.1 (l.get i) (by
        grind);
        convert geometric_progression_mul ( Int.toNat ( l.get i |>.1 ) ) ( l.get i |>.2 ) ( by linarith [ Int.toNat_of_nonneg this.1 ] ) |> Eq.symm using 1;
      simp +decide only [h_geo, mul_assoc, Finset.mul_sum _ _ _];
      exact Finset.sum_congr rfl fun i hi => by rw [ ← Finset.mul_prod_erase _ _ hi ] ; ring;
    -- By `power_series_identity_geometric`, the sum is `geometric_progression 0 1`.
    have h_sum_geometric : (∑ i : Fin l.length, geometric_progression (l.get i |>.1).toNat (l.get i |>.2)) = geometric_progression 0 1 := by
      exact power_series_identity_geometric l h;
    -- By `geometric_progression_mul`, we know that `geometric_progression 0 1 * (1 - X) = X^0 = 1`.
    have h_geometric_mul : geometric_progression 0 1 * (1 - PowerSeries.X) = 1 := by
      convert geometric_progression_mul 0 1 ( by norm_num ) using 1;
      norm_num [ mul_comm ];
    simp_all +decide [mul_comm, mul_left_comm];
    rw [ ← mul_assoc, h_geometric_mul, one_mul ];
    exact rfl

/-
The polynomial identity $\sum x^{a_i} \prod_{j \ne i} (1-x^{n_j}) \cdot (1-x) = \prod (1-x^{n_i})$ holds in `Polynomial ℂ`.
-/
open Polynomial

noncomputable def P_poly (l : List (ℤ × ℕ)) : Polynomial ℂ :=
  ∑ i : Fin l.length, (Polynomial.X : Polynomial ℂ)^(l.get i).1.toNat * ∏ j ∈ (Finset.univ.erase i), (1 - (Polynomial.X : Polynomial ℂ)^(l.get j).2)

noncomputable def Target_poly (l : List (ℤ × ℕ)) : Polynomial ℂ :=
  ∏ i : Fin l.length, (1 - (Polynomial.X : Polynomial ℂ)^(l.get i).2)

theorem polynomial_identity_mul (l : List (ℤ × ℕ)) (h : IsExactCoveringSystem l) :
  P_poly l * (1 - Polynomial.X) = Target_poly l := by
    convert power_series_identity_mul l h using 1;
    unfold P_poly Target_poly P_series Target_series;
    constructor <;> intro h <;> simp_all +decide [ Polynomial.ext_iff, PowerSeries.ext_iff ];
    · convert power_series_identity_mul l ‹_› using 1;
      exact Iff.symm PowerSeries.ext_iff;
    · convert h using 1;
      norm_num [ Polynomial.coeff_mul, Polynomial.coeff_X_pow, Polynomial.coeff_one, PowerSeries.coeff_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one ];
      -- Since the coefficients of the polynomial and the power series are the same, the sums are equal.
      have h_coeff_eq : ∀ (p : Polynomial ℂ), ∀ (n : ℕ), (PowerSeries.coeff n (Polynomial.toPowerSeries p)) = (Polynomial.coeff p n) := by
        aesop;
      congr! 2;
      · congr! 2;
        · congr! 2;
          convert h_coeff_eq _ _ |> Eq.symm;
          induction' ( Finset.univ.erase ‹_› : Finset ( Fin l.length ) ) using Finset.induction <;> aesop;
        · rw [ PowerSeries.coeff_X, Polynomial.coeff_X ] ; aesop;
      · convert h_coeff_eq _ _ |> Eq.symm;
        induction' ( Finset.univ : Finset ( Fin l.length ) ) using Finset.induction <;> aesop

/-
There is no exact covering system with distinct moduli (and at least 2 classes).
-/
open Polynomial

set_option maxHeartbeats 1000000 in
-- The root-of-unity contradiction proof needs extra heartbeats for polynomial simplification.
theorem exact_covering_system_distinct_moduli_impossible (l : List (ℤ × ℕ)) (h_exact : IsExactCoveringSystem l) (h_distinct : l.Pairwise (fun p q => p.2 ≠ q.2)) (h_len : l.length ≥ 2) : False := by
  -- Let $N = \max_i n_i$. Since $l$ has length $\ge 2$ and moduli are distinct, $N > 1$.
  obtain ⟨N, hN⟩ : ∃ N ∈ List.map (fun p => p.2) l, ∀ n ∈ List.map (fun p => p.2) l, n ≤ N := by
    exact ⟨ Finset.max' ( List.toFinset ( List.map ( fun p => p.2 ) l ) ) ⟨ _, List.mem_toFinset.mpr ( List.mem_map.mpr ⟨ _, List.head!_mem_self ( by aesop_cat ), rfl ⟩ ) ⟩, List.mem_toFinset.mp ( Finset.max'_mem _ _ ), fun n hn => Finset.le_max' _ _ ( List.mem_toFinset.mpr hn ) ⟩
  have hN_gt1 : N > 1 := by
    rcases l with ( _ | ⟨ ⟨ a, b ⟩, _ | ⟨ ⟨ c, d ⟩, l ⟩ ⟩ ) <;> simp_all +decide [ List.pairwise_cons ];
    rcases hN with ⟨ rfl | rfl | ⟨ a, ha ⟩, hb, hd, hN ⟩ <;> simp_all +decide [ IsExactCoveringSystem ];
    · grind;
    · grind;
    · grind;
  -- Let $k$ be the index such that $n_k = N$. By distinctness, $k$ is unique.
  obtain ⟨k, hk⟩ : ∃ k : Fin l.length, (l.get k).2 = N ∧ ∀ j : Fin l.length, (l.get j).2 = N → j = k := by
    obtain ⟨ k, hk ⟩ := List.mem_map.mp hN.1;
    obtain ⟨k, hk⟩ : ∃ k : Fin l.length, (l.get k).2 = N := by
      obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hk.1; use ⟨ k, by aesop ⟩ ; aesop;
    refine' ⟨ k, hk, fun j hj => _ ⟩;
    have := List.pairwise_iff_get.mp h_distinct;
    exact le_antisymm ( le_of_not_gt fun h => this _ _ h <| by linarith ) ( le_of_not_gt fun h => this _ _ h <| by linarith );
  -- Let $\zeta$ be a primitive $N$-th root of unity.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := by
    exact ⟨ Complex.exp ( 2 * Real.pi * Complex.I / N ), Complex.isPrimitiveRoot_exp _ ( by linarith ) ⟩;
  -- Evaluate the polynomial identity $P(x)(1-x) = Q(x)$ at $x=\zeta$.
  have h_eval : P_poly l = ∑ i : Fin l.length, (Polynomial.X : Polynomial ℂ)^(l.get i).1.toNat * ∏ j ∈ (Finset.univ.erase i), (1 - (Polynomial.X : Polynomial ℂ)^(l.get j).2) := by
    rfl;
  -- Since $n_k = N$, one factor in the product is $1 - \zeta^N = 0$. So RHS is 0.
  have h_rhs_zero : Target_poly l = ∏ i : Fin l.length, (1 - (Polynomial.X : Polynomial ℂ)^(l.get i).2) := by
    exact rfl;
  have h_eval_zero : P_poly l * (1 - Polynomial.X) = Target_poly l := by
    convert polynomial_identity_mul l h_exact using 1;
  replace h_eval_zero := congr_arg ( Polynomial.eval ζ ) h_eval_zero ; simp_all +decide [ Polynomial.eval_prod, Polynomial.eval_finset_sum ];
  -- Since $n_k = N$, one factor in the product is $1 - \zeta^N = 0$. So RHS is 0. Thus $P(\zeta) = 0$.
  have h_P_zero : ∑ x : Fin l.length, ζ ^ l[(↑x : ℕ)].1.toNat * ∏ x ∈ Finset.univ.erase x, (1 - ζ ^ l[(↑x : ℕ)].2) = 0 := by
    have h_rhs_zero : ∏ x : Fin l.length, (1 - ζ ^ l[(↑x : ℕ)].2) = 0 := by
      exact Finset.prod_eq_zero ( Finset.mem_univ k ) ( by simp +decide [ hk.1, hζ.pow_eq_one ] );
    simp_all +decide [ sub_eq_iff_eq_add ];
    exact h_eval_zero.resolve_right ( by rintro rfl; exact absurd ( hζ.eq_orderOf ) ( by norm_num; linarith ) );
  -- Since $n_j < N$ for all $j \ne k$ (because $N$ is max and moduli are distinct), $\zeta^{n_j} \ne 1$.
  have h_zeta_ne_one : ∀ j : Fin l.length, j ≠ k → ζ ^ l[(↑j : ℕ)].2 ≠ 1 := by
    intro j hj_ne_k hj_eq_one; have := hζ.pow_eq_one; simp_all +decide [ IsPrimitiveRoot.iff_def ] ;
    have := hζ _ hj_eq_one; obtain ⟨ c, hc ⟩ := this; simp_all +decide [ pow_mul ] ;
    rcases c with ( _ | _ | c ) <;> simp_all +decide [ Nat.mul_succ ];
    · have := h_exact.1; simp_all +decide [ IsExactCoveringSystem ] ;
      exact absurd ( this _ _ ( show ( l[(↑j : ℕ)].1, l[(↑j : ℕ)].2 ) ∈ l from by simp ) ) ( by norm_num [ hc ] );
    · grind;
  -- Thus $P(\zeta) \ne 0$.
  have h_P_ne_zero : ζ ^ l[(↑k : ℕ)].1.toNat * ∏ x ∈ Finset.univ.erase k, (1 - ζ ^ l[(↑x : ℕ)].2) ≠ 0 := by
    exact mul_ne_zero ( pow_ne_zero _ ( hζ.ne_zero ( by linarith ) ) ) ( Finset.prod_ne_zero_iff.mpr fun x hx => sub_ne_zero_of_ne <| Ne.symm <| h_zeta_ne_one x <| Finset.ne_of_mem_erase hx );
  rw [ Finset.sum_eq_single k ] at h_P_zero <;> simp_all +decide;
  intro j hj; rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ j ) ] ; simp +decide ;
  exact Or.inr <| Finset.prod_eq_zero ( Finset.mem_erase_of_ne_of_mem ( Ne.symm hj ) <| Finset.mem_univ _ ) <| sub_eq_zero.mpr <| by simp +decide [ hk.1, hζ.pow_eq_one ] ;

#print axioms exact_covering_system_distinct_moduli_impossible
-- 'Erdos947.exact_covering_system_distinct_moduli_impossible' depends on axioms: [propext,
-- Classical.choice, Quot.sound]

end Erdos947
