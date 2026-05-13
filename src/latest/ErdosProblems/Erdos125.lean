/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 125.
https://www.erdosproblems.com/forum/thread/125

Informal authors:
- a DeepMind prover agent

Formal authors:
- a DeepMind prover agent
- George Tsoukalas

URLs:
- https://www.erdosproblems.com/forum/thread/125#post-4448
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/125.lean
- https://github.com/google-deepmind/formal-conjectures/blob/300bf771bdbef43d7b9aa2521e633a50fd54dd28/FormalConjectures/ErdosProblems/125.lean
-/
/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import ErdosProblems.Util

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.cdot false
set_option linter.style.show false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.flexible false

open Filter

open scoped Topology

/-!
# Erdős Problem 125

*Reference:* [erdosproblems.com/125](https://www.erdosproblems.com/125)
-/

open Nat Pointwise

namespace Erdos125

def A : Set ℕ := {x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1}}
def B : Set ℕ := {x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1}}

open Topology

def S3 : Set ℕ := {x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1}}
def S4 : Set ℕ := {x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1}}

lemma s3_bound (k : ℕ) (x : ℕ) (h : x ∈ S3) (hk : x < 3^k) : x ≤ (3^k - 1) / 2 := by
  rewrite[Nat.le_div_iff_mul_le (by decide),mul_two,Nat.le_sub_one_iff_lt hk.pos, S3]at *
  induction k generalizing x with|zero =>omega|succ =>_
  use not_le.1 fun and=>absurd (‹∀ A B C,_› (x/3) (by simp_all[ (by valid:x>0), Finset.insert_subset_iff])) (by cases show x%3=0 ∨x%3=1by simp_all[ (by valid:x>0), Finset.insert_subset_iff] with valid)

lemma s4_bound (m : ℕ) (y : ℕ) (h : y ∈ S4) (hm : y < 4^m) : y ≤ (4^m - 1) / 3 := by
  norm_num [←geom_sum_mul_of_one_le, S4] at h
  induction m generalizing y with|zero=>omega| succ=>_
  use not_lt.1 fun and=>absurd (‹∀ a s C,a≤_› (y/4) (by simp_all[ Finset.insert_subset_iff,and.pos])) (by cases show y%4=0 ∨y%4=1by simp_all[ Finset.insert_subset_iff,and.pos] with valid)

lemma gap_exists (k m : ℕ) (h : (3^k - 1) / 2 + (4^m - 1) / 3 < min (3^k) (4^m)) :
  ∀ x ∈ S3, ∀ y ∈ S4, ¬ ((3^k - 1) / 2 + (4^m - 1) / 3 < x + y ∧ x + y < min (3^k) (4^m)) := by
  have _h := h
  intro x hx y hy h_contra
  have hx_lt : x < 3 ^ k := by
    have hmin : min (3 ^ k) (4 ^ m) ≤ 3 ^ k := Nat.min_le_left _ _
    omega
  have hy_lt : y < 4 ^ m := by
    have hmin : min (3 ^ k) (4 ^ m) ≤ 4 ^ m := Nat.min_le_right _ _
    omega
  have hx_bound := s3_bound k x hx hx_lt
  have hy_bound := s4_bound m y hy hy_lt
  omega

lemma zero_in_S3 : 0 ∈ S3 := by
  norm_num[ S3]

lemma zero_in_S4 : 0 ∈ S4 := by
  norm_num [S4]

lemma zero_in_S3_add_S4 : 0 ∈ S3 + S4 := by
  have h3 := zero_in_S3
  have h4 := zero_in_S4
  simp_all[Set.mem_add,Exists.intro 0]

lemma one_in_S3 : 1 ∈ S3 := by
  norm_num[ S3]

lemma one_in_S4 : 1 ∈ S4 := by
  norm_num[S4]

lemma two_in_S3_add_S4 : 2 ∈ S3 + S4 := by
  have h3 := one_in_S3
  have h4 := one_in_S4
  constructor
  use h3,1

lemma gap_formula_eval : (3^4 - 1) / 2 + (4^3 - 1) / 3 < min (3^4) (4^3) := by
  try decide

lemma specific_gap_exists : ∀ x ∈ S3, ∀ y ∈ S4, ¬ (61 < x + y ∧ x + y < 64) := by
  have h_eval := gap_formula_eval
  have h_gap := gap_exists 4 3 h_eval
  valid

lemma gap_formula_eval_2 : (3^5 - 1) / 2 + (4^4 - 1) / 3 < min (3^5) (4^4) := by
  focus decide

lemma specific_gap_exists_2 : ∀ x ∈ S3, ∀ y ∈ S4, ¬ (206 < x + y ∧ x + y < 243) := by
  have h_eval := gap_formula_eval_2
  have h_gap := gap_exists 5 4 h_eval
  valid

lemma gap_formula_eval_3 : (3^6 - 1) / 2 + (4^5 - 1) / 3 < min (3^6) (4^5) := by
  focus decide

lemma specific_gap_exists_3 : ∀ x ∈ S3, ∀ y ∈ S4, ¬ (705 < x + y ∧ x + y < 729) := by
  have h_eval := gap_formula_eval_3
  have h_gap := gap_exists 6 5 h_eval
  classical assumption

def KM_seq : ℕ → ℕ × ℕ
| 0 => (5, 4)
| n + 1 =>
  let K := (KM_seq n).1
  let M := (KM_seq n).2
  if 3^K ≤ 4^M then (K + 24, M + 19) else (K + 5, M + 4)

def K_seq (n : ℕ) : ℕ := (KM_seq n).1
def M_seq (n : ℕ) : ℕ := (KM_seq n).2

lemma KM_seq_step_le (K M : ℕ) (h1 : 15 * 3^K ≤ 17 * 4^M) (h2 : 5 * 4^M ≤ 6 * 3^K) (h3 : 3^K ≤ 4^M) :
  15 * 3^(K + 24) ≤ 17 * 4^(M + 19) ∧ 5 * 4^(M + 19) ≤ 6 * 3^(K + 24) := by
  have e1 : 3^(K + 24) = 282429536481 * 3^K := by ring!
  have e2 : 4^(M + 19) = 274877906944 * 4^M := by ring
  omega

lemma KM_seq_step_gt (K M : ℕ) (h1 : 15 * 3^K ≤ 17 * 4^M) (h2 : 5 * 4^M ≤ 6 * 3^K) (h3 : ¬ (3^K ≤ 4^M)) :
  15 * 3^(K + 5) ≤ 17 * 4^(M + 4) ∧ 5 * 4^(M + 4) ≤ 6 * 3^(K + 5) := by
  have e1 : 3^(K + 5) = 243 * 3^K := by ring1
  have e2 : 4^(M + 4) = 256 * 4^M := by ring
  omega

lemma KM_seq_inv (n : ℕ) : 15 * 3^(K_seq n) ≤ 17 * 4^(M_seq n) ∧ 5 * 4^(M_seq n) ≤ 6 * 3^(K_seq n) := by
  induction n with
  | zero =>
      norm_num [K_seq, M_seq, KM_seq]
  | succ n ih =>
      dsimp [K_seq, M_seq, KM_seq]
      split
      · exact KM_seq_step_le (KM_seq n).1 (KM_seq n).2 ih.1 ih.2 (by assumption)
      · exact KM_seq_step_gt (KM_seq n).1 (KM_seq n).2 ih.1 ih.2 (by assumption)

lemma a_growth (n : ℕ) : n < (3^(K_seq n) - 1) / 2 + (4^(M_seq n) - 1) / 3 := by
  push_cast[ ←geom_sum_mul_of_one_le, K_seq, M_seq, true,n.lt_iff_add_one_le]
  delta Erdos125.KM_seq
  use le_add_right ((Nat.mul_div_cancel _) two_pos▸.trans (?_) ( Finset.sum_le_sum fun and p=>Nat.pow_pos (by decide)))
  use Finset.card_eq_sum_ones ( _)▸(Finset.card_range _)▸n.rec (by decide) fun and p=>show _≤Prod.fst (ite _ _ _)by bound

lemma gap_ineq (K M : ℕ) (h1 : 15 * 3^K ≤ 17 * 4^M) (h2 : 5 * 4^M ≤ 6 * 3^K) :
  10 * ((3^K - 1) / 2 + (4^M - 1) / 3) ≤ 9 * min (3^K) (4^M) := by
  omega

noncomputable def density_seq (A : Set ℕ) (n : ℕ) : ℝ :=
  ((A ∩ Set.univ).interIio n).ncard / (n : ℝ)

lemma has_density_iff (A : Set ℕ) (α : ℝ) :
  A.HasDensity α ↔ Filter.Tendsto (density_seq A) Filter.atTop (𝓝 α) := by
  rw [Set.HasDensity]
  have hfun : (fun n : ℕ => A.partialDensity Set.univ n) = density_seq A := by
    funext n
    simp [density_seq, Set.partialDensity, Set.interIio]
  rw [hfun]

lemma gap_density_eq (A : Set ℕ) (a b : ℕ) (h_gap : ∀ x ∈ A, ¬ (a < x ∧ x < b)) (h_lt : a < b) :
  ((A ∩ Set.univ).interIio b).ncard = ((A ∩ Set.univ).interIio (a + 1)).ncard := by
  exact (congr_arg _) ((Set.ext fun and=>and_congr_right fun and' =>Set.mem_Ioi.trans (.trans (by_contra (h_gap and and'.1 ∘by valid)) (Set.mem_Ioi).symm)))

lemma gap_density_le (A : Set ℕ) (a b : ℕ) (h_gap : ∀ x ∈ A, ¬ (a < x ∧ x < b)) (h_lt : a < b) (h_ratio : 10 * a ≤ 9 * b) :
  density_seq A b ≤ density_seq A (a + 1) * (0.9 + 1 / (b : ℝ)) := by
  have h_eq := gap_density_eq A a b h_gap h_lt
  unfold density_seq
  rw [h_eq]
  set N : ℝ := (((A ∩ Set.univ).interIio (a + 1)).ncard : ℝ)
  have hN : 0 ≤ N := by positivity
  have hb_nat : 0 < b := by omega
  have hb_pos : (0 : ℝ) < b := by exact_mod_cast hb_nat
  have ha_pos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
  have h_ratio_real : (10 : ℝ) * a ≤ 9 * b := by exact_mod_cast h_ratio
  have hcoef :
      1 / (b : ℝ) ≤
        (1 / ((a + 1 : ℕ) : ℝ)) * (0.9 + 1 / (b : ℝ)) := by
    field_simp [hb_pos.ne', ha_pos.ne']
    norm_num
    linarith
  calc
    N / (b : ℝ) = N * (1 / (b : ℝ)) := by ring
    _ ≤ N * ((1 / ((a + 1 : ℕ) : ℝ)) * (0.9 + 1 / (b : ℝ))) :=
      mul_le_mul_of_nonneg_left hcoef hN
    _ = N / ((a + 1 : ℕ) : ℝ) * (0.9 + 1 / (b : ℝ)) := by ring

lemma limit_bounds (f : ℕ → ℝ) (α : ℝ) (h_pos : 0 < α)
  (h_lim : Filter.Tendsto f Filter.atTop (𝓝 α)) :
  ∃ N0, ∀ n ≥ N0, 0.99 * α ≤ f n ∧ f n ≤ 1.01 * α := by
  apply (h_lim.eventually.comp (Icc_mem_nhds ↑(mul_lt_of_lt_one_left h_pos (by ·norm_num))) ↑(lt_mul_left h_pos (by ·norm_num))).exists_forall_of_atTop

lemma contradiction_from_bounds (f : ℕ → ℝ) (α : ℝ) (h_pos : 0 < α)
  (h_bounds : ∃ N0, ∀ n ≥ N0, 0.99 * α ≤ f n ∧ f n ≤ 1.01 * α)
  (h_gap : ∀ N0, ∃ a b, N0 < a ∧ a < b ∧ f b ≤ f (a + 1) * (0.9 + 1 / (b : ℝ))) :
  False := by
  rcases h_bounds with ⟨N0, h_bound⟩
  rcases h_gap (max N0 100) with ⟨a, b, ha, hab, h_ineq⟩
  have ha1 : N0 ≤ a + 1 := by omega
  have hb : N0 ≤ b := by omega
  have hb100 : 100 < b := by omega
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast Nat.lt_trans (by norm_num : 0 < 100) hb100
  have hb100r : (100 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb100
  have h_fb_lower : 0.99 * α ≤ f b := (h_bound b hb).1
  have h_fa_upper : f (a + 1) ≤ 1.01 * α := (h_bound (a + 1) ha1).2
  have h_b_large : 1 / (b : ℝ) ≤ 0.01 := by
    rw [div_le_iff₀ hbpos]
    nlinarith
  have h_fa_pos : 0 ≤ f (a + 1) := by
    have h := (h_bound (a + 1) ha1).1
    nlinarith [h_pos]
  have h_factor : 0.9 + 1 / (b : ℝ) ≤ 0.91 := by linear_combination h_b_large
  have h_factor_nonneg : 0 ≤ 0.9 + 1 / (b : ℝ) := by positivity
  have h_alpha_upper_nonneg : 0 ≤ 1.01 * α := by nlinarith [h_pos]
  have h_fb_upper : f b ≤ 1.01 * α * 0.91 := by
    exact h_ineq.trans
      (mul_le_mul h_fa_upper h_factor h_factor_nonneg h_alpha_upper_nonneg)
  have h_fb_upper' : f b ≤ 0.9191 * α := by
    nlinarith [h_fb_upper]
  nlinarith [h_pos, h_fb_lower, h_fb_upper']

lemma limit_contradiction (f : ℕ → ℝ) (α : ℝ) (h_pos : 0 < α)
  (h_lim : Filter.Tendsto f Filter.atTop (𝓝 α))
  (h_gap : ∀ N0, ∃ a b, N0 < a ∧ a < b ∧ f b ≤ f (a + 1) * (0.9 + 1 / (b : ℝ))) :
  False := by
  have h_bounds : ∃ N0, ∀ n ≥ N0, 0.99 * α ≤ f n ∧ f n ≤ 1.01 * α := limit_bounds f α h_pos h_lim
  exact contradiction_from_bounds f α h_pos h_bounds h_gap

lemma contradiction_from_limit (A : Set ℕ) (α : ℝ) (h_pos : 0 < α)
  (h_lim : A.HasDensity α)
  (h_gap : ∀ N0, ∃ a b, N0 < a ∧ a < b ∧ (∀ x ∈ A, ¬ (a < x ∧ x < b)) ∧ 10 * a ≤ 9 * b) :
  False := by
  have h_lim' : Filter.Tendsto (density_seq A) Filter.atTop (𝓝 α) := (has_density_iff A α).mp h_lim
  apply limit_contradiction (density_seq A) α h_pos h_lim'
  intro N0
  rcases h_gap N0 with ⟨a, b, h_N0, h_ab, h_empty, h_ratio⟩
  use a, b
  refine ⟨h_N0, h_ab, ?_⟩
  exact gap_density_le A a b h_empty h_ab h_ratio

lemma no_pos_density_of_gaps (A : Set ℕ)
  (h : ∀ N0, ∃ a b, N0 < a ∧ a < b ∧ (∀ x ∈ A, ¬ (a < x ∧ x < b)) ∧ 10 * a ≤ 9 * b) :
  ¬ A.HasPosDensity := by
  intro h_pos_den
  rcases h_pos_den with ⟨α, h_pos, h_den⟩
  exact contradiction_from_limit A α h_pos h_den h

lemma gap_exists_helper (K M : ℕ) (a b : ℕ) (ha : a = (3^K - 1) / 2 + (4^M - 1) / 3)
  (hb : b = min (3^K) (4^M)) (h_lt : a < b) :
  ∀ x ∈ S3 + S4, ¬ (a < x ∧ x < b) := by
  intro x hx
  have h_ex : ∃ s3 ∈ S3, ∃ s4 ∈ S4, s3 + s4 = x := hx
  rcases h_ex with ⟨s3, h_s3, s4, h_s4, rfl⟩
  subst ha hb
  exact gap_exists K M h_lt s3 h_s3 s4 h_s4

lemma no_pos_density_of_S3_S4_help (N0 : ℕ) :
  ∃ a b, N0 < a ∧ a < b ∧ (∀ x ∈ S3 + S4, ¬ (a < x ∧ x < b)) ∧ 10 * a ≤ 9 * b := by
  let K := K_seq N0
  let M := M_seq N0
  let a := (3^K - 1) / 2 + (4^M - 1) / 3
  let b := min (3^K) (4^M)
  use a, b
  have h_inv := KM_seq_inv N0
  have h1 : N0 < a := a_growth N0
  have h4 : 10 * a ≤ 9 * b := gap_ineq K M h_inv.1 h_inv.2
  have hb_pos : 0 < b := by positivity
  have h2 : a < b := by omega
  have h3 : ∀ x ∈ S3 + S4, ¬ (a < x ∧ x < b) := gap_exists_helper K M a b rfl rfl h2
  exact ⟨h1, h2, h3, h4⟩

lemma density_zero_of_S3_S4 : ¬ (S3 + S4).HasPosDensity := by
  apply no_pos_density_of_gaps (S3 + S4)
  intro N0
  exact no_pos_density_of_S3_S4_help N0

/-
Let $A = {∑ ε_{k} 3^{k} : ε_{k} ∈ {0,1}}$ be the set of integers which
have only the digits $0, 1$ when written base 3, and $B = {∑ ε_{k} 4^{k} : ε_{k} ∈ {0,1}}$
be the set of integers which have only the digits $0, 1$ when written base 4.
Does $A + B$ have positive density?
-/
theorem erdos_125 :
    False ↔ ({ x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1} } +
      { x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1} }).HasPosDensity := by
  have h : ¬ ({x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1}} + {x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1}}).HasPosDensity := by
    exact density_zero_of_S3_S4
  symm
  exact iff_false_intro h

lemma dirichlet_approximation (α : ℝ) (Q : ℕ) (hQ : Q > 0) :
  ∃ (p : ℤ) (q : ℕ), 0 < q ∧ q ≤ Q ∧ |(q : ℝ) * α - p| ≤ 1 / ((Q : ℝ) + 1) := by
  refine α.exists_int_int_abs_mul_sub_le hQ |>.imp fun and⟨A, B, _⟩=>?_
  match A with | (n : ℕ) =>exact ⟨ (n : ℕ),by valid,by assumption_mod_cast⟩

lemma log_ratio_approximation (Q : ℕ) (hQ : Q > 0) :
  ∃ (k m : ℕ), 0 < m ∧ m ≤ Q ∧ |(m : ℝ) * (Real.log 4) - (k : ℝ) * (Real.log 3)| ≤ (Real.log 3) / ((Q : ℝ) + 1) := by
  show∃ R M,_ ∧_ ∧abs ((Nat.cast M) *_ -Nat.cast R * _)≤_ /(id @_+1)
  by_cases h: ( Finset.Icc (1) Q).image (@ fun and : ℕ =>⌊↑ and*Real.log 04/.log (3)*( Q+1)⌋% ( Q+1))=.range ↑(Q + 1)
  · rcases(h▸ Finset.card_image_le).not_gt (by·norm_num [Q.succ_sub_one, Finset.card_image_of_injective, Nat.cast_injective])
  by_cases h: ( Finset.Icc (1) Q).image ↑(fun (n : ℕ)=>⌊↑ (n : ℕ) *Real.log @4/.log (3)*( Q+1)⌋%(Q+1))=.range @(Q+1)\{0}
  · refine(Finset.mem_image.1 (h.ge (by·norm_num[hQ.ne']: (Q: Int) ∈ _) ) ).elim fun and x =>⟨(⌊↑and*Real.log @4/.log (3)*(Q + 1)⌋/(Q+1)+1).toNat, and,?_⟩
    refine and_assoc.mp ⟨ Finset.mem_Icc.mp (x.1), (.trans (by rw [←Int.cast_natCast (Int.toNat _),Int.toNat_of_nonneg (by positivity),Int.cast_add]) ? _)⟩
    have:=⌊↑and*Real.log 4/.log (3)*(Q+1)⌋.ediv_add_emod (Q+1)
    push_cast[id,x,comm.trans Int.floor_eq_iff] at this⊢
    use abs_sub_le_iff.2 (by repeat use(le_div_iff₀ (by positivity)).2 (by nlinarith only[ (by positivity:Real.log (3) > 0), this, mul_div_cancel₀ (and*.log @4: ℝ) (by norm_num:Real.log (3)≠0)]))
  convert (by_contra fun and=>h (Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.2 fun and j=> _) (( Finset.card_image_of_injOn fun and _ _ _ _=>le_antisymm (not_lt.1 _) (not_lt.1 _)).ge.trans' _) ) )
  · simp_all-contextual
    use⟨ _,Int.toNat_le.2 (Int.le_of_lt_add_one.comp (Int.emod_lt_of_pos _) (by valid)),Int.toNat_of_nonneg ((Int.emod_nonneg _) (nofun))⟩,fun⟨A, B⟩=>(j.elim (and A.natAbs _)).asymm ?_
    simp_all[mul_assoc, sub_mul,mul_comm (A : ℝ),Q.cast_add_one_pos, A.cast_natAbs, sub_lt_iff_lt_add',abs_of_nonneg,nonneg_of_mul_nonneg_right (B.subst (by positivity)),div_mul_eq_mul_div,Int.floor_eq_iff,Real.log_pos,le_div_iff₀]
    exact (abs_of_nonneg (by nlinarith only[B.1])).trans_lt ((lt_div_iff₀ (by positivity)).2 (by linear_combination(div_lt_iff₀ (by positivity)).1 B.2))
  · use(Int.ModEq.symm (by assumption)).dvd.elim fun a s H=>‹¬∃ R M,_› ⟨a.toNat, and-by assumption,?_⟩
    norm_num[abs_le, H, sub_eq_iff_eq_add',Int.floor_eq_iff, H.le,(mod_cast a.toNat_of_nonneg (nonneg_of_mul_nonneg_right (s▸sub_nonneg.2 (by gcongr)) (by valid)):(a.toNat: ℝ) = a)] at ( s)‹and ∈_›⊢
    field_simp at(s)⊢
    refine ⟨by valid,s.imp (by linear_combination.+Int.sub_floor_div_mul_lt (↑‹ℕ›*.log 4*(Q+1): ℝ) (by positivity:Real.log (3)>0)) @?_⟩
    use (by linear_combination.+Int.sub_floor_div_mul_nonneg (‹ℕ›*.log 4*(Q+1): ℝ) (by positivity:Real.log (3)>0))
  · refine (Int.ModEq.dvd (by assumption)).elim fun a s H=>‹¬∃ R M,_› ⟨a.toNat,by assumption-and,?_⟩
    norm_num[abs_le, H, sub_eq_iff_eq_add',Int.floor_eq_iff, H.le,(mod_cast a.toNat_of_nonneg (nonneg_of_mul_nonneg_right (s▸sub_nonneg.2 (by gcongr)) (by valid)):(a.toNat: ℝ) = a),div_mul_eq_mul_div] at ( s)⊢
    use le_add_right (Finset.mem_Icc.1 (by valid)).2, sub_le_iff_le_add'.1 ((le_div_iff₀ (by positivity)).2 ? _),(sub_le_iff_le_add.mp.comp (le_div_iff₀ (by((positivity)))).2) ?_
    · linear_combination(le_div_iff₀ (by positivity)).1 (s.1)+Int.sub_floor_div_mul_lt (and*.log 4*(Q+1): ℝ) (by positivity:Real.log (3) > 0)
    · linear_combination(div_lt_iff₀ (by positivity)).1 (s.2)+Int.sub_floor_div_mul_nonneg (and*.log 4*(Q+1): ℝ) (by positivity:Real.log (3) > 0)
  · norm_num[Q.succ_sub_one,Q.succ_pos,Finset.card_sdiff, Finset.card_image_of_injective,Nat.cast_injective]

lemma gap_alignment (Q : ℕ) (hQ : Q > 0) :
  ∃ (k m : ℕ), 0 < m ∧ m ≤ Q ∧ |(4^m : ℝ) - 3^k| ≤ max (3^k : ℝ) (4^m : ℝ) * (Real.exp (Real.log 3 / ((Q : ℝ) + 1)) - 1) := by
  have h_log := log_ratio_approximation Q hQ
  rcases h_log with ⟨k, m, hm_pos, hm_le, h_bound⟩
  use k, m
  constructor
  · exact hm_pos
  · constructor
    · exact hm_le
    · apply (mul_le_mul_of_nonneg_left ↑(sub_le_sub_right (Real.add_one_le_exp _) _) (by (positivity) )).trans'
      rcases lt_trichotomy (4^m: ℝ) (3^k) with a | S | S
      · norm_num[a,abs_of_neg,a.le]
        have:=Real.log_le_sub_one_of_pos.comp (div_pos (pow_pos four_pos m)) (pow_pos three_pos k)
        linear_combination (3)^k*(le_sup_right).trans h_bound+3^k*this.trans' (by rw [Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow])+4^m*div_self_le_one (3^k: ℝ)
      · simp_all[h_bound.trans']
      · have := (.log (3 ^k) -Real.log (4 ^m)).add_one_le_exp
        simp_all[ Fin, max_eq_right S.le, sub_add, sub_le_comm.1, abs_of_pos (sub_pos.mpr S), Real.exp_log, Real.exp_sub]
        linear_combination(4)^m*le_sup_left.trans h_bound+(le_div_iff₀ (by bound)).1 (Real.exp_log three_pos▸Real.exp_log four_pos▸Real.exp_nat_mul _ _▸Real.exp_nat_mul _ _▸sub_le_iff_le_add.2 this)

lemma A_card_bound (k : ℕ) : ((A ∩ {x | x < 3^k}).ncard : ℝ) = (2^k : ℝ) := by
  delta and A
  refine((congr_arg _) ((congr_arg _) ((congr_arg Nat.card (by simp_all![Set.inter_def, and_comm])).trans (Nat.card_eq_finsetCard { a ∈.range (3^k) | (((3:).digits a)).toFinset ⊆{0,1}})))).trans (mod_cast ? _)
  refine show Nat.cast @_=(Nat.cast _) from(congr_arg _).comp ( Finset.card_filter _ _).trans ( k.rec ↑(.trans (add_zero _) ↑(by simp_all! ) ) fun and x =>(pow_succ' (3) _)▸pow_succ (2) and▸ x▸? _)
  refine (3 ^and).rec rfl fun and x =>.trans (by rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,x]) (.symm (.trans (by rw [ Finset.sum_range_succ, add_mul]) ?_))
  cases and.eq_zero_or_pos with norm_num[*, mul_two, add_assoc,(3).mul_add_div,Nat.succ_pos _, Finset.insert_subset_iff]

lemma B_card_bound (m : ℕ) : ((B ∩ {x | x < 4^m}).ncard : ℝ) = (2^m : ℝ) := by
  delta and B
  refine((congr_arg _).comp (congr_arg _) ((congr_arg ↑Nat.card (by simp_all![Set.inter_def, and_comm])).trans (Nat.card_eq_finsetCard { a ∈.range (4^m) | (Nat.digits (↑4) a).toFinset ⊆{0,1}}))).trans (mod_cast(?_))
  refine show((_: ℕ): ℝ)=(_: ℕ) from(congr_arg _).comp ( Finset.card_filter _ _).trans (m.rec ((add_zero _).trans (by simp_all)) fun and y=>pow_succ' 4 and▸pow_succ (2) and▸y▸? _)
  refine (4^and).rec rfl fun and k=>.trans (by rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,k]) (.symm (.trans (by rw [ Finset.sum_range_succ, add_mul]) ?_))
  cases and.eq_zero_or_pos with norm_num[*, mul_two, add_assoc,Finset.insert_subset_iff,(4).mul_add_div,Nat.succ_pos _]

lemma A_max_bound (k : ℕ) (a : ℕ) (ha : a ∈ A) (hak : a < 3^k) : a ≤ (3^k - 1) / 2 := by
  rw [←not_lt, Erdos125.A,Nat.div_lt_iff_lt_mul (by decide)]at*
  use not_lt.2 (Nat.le_sub_one_of_lt (k.rec (by aesop) ?_ a ha hak))
  use fun and A B R M=>match B with|0=>by valid | S+1=>by cases show(S+1)%3=0 ∨(S+1)%3=1by simp_all[ Finset.insert_subset_iff] with use (by valid ∘@A ((S+1)/3)) (by simp_all[ Finset.insert_subset_iff])

lemma B_max_bound (m : ℕ) (b : ℕ) (hb : b ∈ B) (hbm : b < 4^m) : b ≤ (4^m - 1) / 3 := by
  rewrite[B,Nat.le_div_iff_mul_le (by decide),Nat.le_sub_one_iff_lt (by valid)]at*
  induction m generalizing b with|zero=>omega| succ=>_
  use not_le.1 fun and=>absurd (‹∀ _ _ __, _› (b/4) (by simp_all[ (by valid:b>0), Finset.insert_subset_iff])) (by cases show b%4=0 ∨b%4=1by simp_all[ (by valid:b>0), Finset.insert_subset_iff] with valid)

lemma A_decomp_div (k a : ℕ) (ha : a ∈ A) : a / 3^k ∈ A := by
  norm_num [ Erdos125.A]at*
  use k.strongRec (fun A B R M=>match A with|0=> R.div_one.symm▸M | S+1=>? _) a ha
  exact (pow_succ' (3) _)▸ R.div_div_eq_div_mul _ _▸ (B S (by constructor) _) ↑(.trans (by cases R.eq_zero_or_pos with norm_num[*]) M)
lemma A_decomp_mod (k a : ℕ) (ha : a ∈ A) : a % 3^k ∈ A := by
norm_num[ Erdos125.A]at*
use k.strongRec ↑?_ a ha
use fun and A B R=>match and with|0=>B.mod_one.symm▸by bound | S+1=>pow_succ' (3) S▸Nat.mod_mul▸ if a: B%3=0 then(? _)else(? _)
· refine (by cases B/3%_ with(norm_num[a, Finset.insert_subset_iff]) ∘ A S (by constructor) (B/3)) (.trans (by cases B.eq_zero_or_pos with norm_num [ *]) R)
· simp_all-contextual[mul_add, S|>.lt_succ,B.mod_lt,B.pos_of_ne_zero (a.comp (by rw [.])), Finset.insert_subset_iff,Nat.add_mul_div_left,pos_iff_ne_zero.eq]
lemma B_decomp_div (m b : ℕ) (hb : b ∈ B) : b / 4^m ∈ B := by
  change b ∈{s |_}at@@hb⊢
  exact (Set.mem_setOf.mpr) (m.rec (b.div_one.symm▸hb) fun and=>.trans (b.div_div_eq_div_mul (4^ _) 4▸by cases b/_ with cases b with norm_num[ Finset.insert_subset_insert_iff]))
lemma B_decomp_mod (m b : ℕ) (hb : b ∈ B) : b % 4^m ∈ B := by
  change b ∈{s |_} at hb⊢
  use m.strongRec ?_ b hb.out
  use fun and A B R=>match and with|0=>by norm_num[B.mod_one] | S+1=>pow_succ' 4 S▸Nat.mod_mul▸ if a: B%4=0 then(? _)else(? _)
  · refine Set.mem_setOf.2 (.trans (by cases B/4%_ with norm_num[a, Finset.insert_subset_iff]) ( Finset.insert_subset (by decide: 0 ∈ _) (A S (by constructor) (B/4) ((.trans (by cases B with norm_num) R)))))
  · simp_all-contextual[B.mod_lt,B.pos_of_ne_zero (a.comp (by rw [.])), Finset.insert_subset_iff,Nat.add_mul_div_left _,pos_iff_ne_zero.eq]

def sum_c (k m a b : ℕ) : ℕ :=
  if 3^k ≤ 4^m then
    (4^m - 3^k) * (b / 4^m) + (a % 3^k) + (b % 4^m)
  else
    (3^k - 4^m) * (a / 3^k) + (a % 3^k) + (b % 4^m)

lemma sum_form_eq (k m a b : ℕ) :
  a + b = min (3^k) (4^m) * (a / 3^k + b / 4^m) + sum_c k m a b := by
  unfold sum_c
  have ha_eq : 3^k * (a / 3^k) + a % 3^k = a := Nat.div_add_mod a (3^k)
  have hb_eq : 4^m * (b / 4^m) + b % 4^m = b := Nat.div_add_mod b (4^m)
  split_ifs with h_le
  · have h_min : min (3^k) (4^m) = 3^k := min_eq_left h_le
    rw [h_min]
    have h_dist : 3^k * (a / 3^k + b / 4^m) = 3^k * (a / 3^k) + 3^k * (b / 4^m) := Nat.mul_add (3^k) _ _
    rw [h_dist]
    have h_diff : 3^k * (b / 4^m) + (4^m - 3^k) * (b / 4^m) = 4^m * (b / 4^m) := by
      rw [←Nat.add_mul]
      have h_add : 3^k + (4^m - 3^k) = 4^m := Nat.add_sub_of_le h_le
      rw [h_add]
    omega
  · have h_min : min (3^k) (4^m) = 4^m := min_eq_right (by omega)
    rw [h_min]
    have h_le2 : 4^m ≤ 3^k := by omega
    have h_dist : 4^m * (a / 3^k + b / 4^m) = 4^m * (a / 3^k) + 4^m * (b / 4^m) := Nat.mul_add (4^m) _ _
    rw [h_dist]
    have h_diff : 4^m * (a / 3^k) + (3^k - 4^m) * (a / 3^k) = 3^k * (a / 3^k) := by
      rw [←Nat.add_mul]
      have h_add : 4^m + (3^k - 4^m) = 3^k := Nat.add_sub_of_le h_le2
      rw [h_add]
    omega

lemma a_bot_bound (k a : ℕ) (ha : a ∈ A) : a % 3^k ≤ (3^k - 1) / 2 := by
  have h1 := A_decomp_mod k a ha
  have h2 : a % 3^k < 3^k := Nat.mod_lt _ (by positivity)
  exact A_max_bound k (a % 3^k) h1 h2

lemma b_bot_bound (m b : ℕ) (hb : b ∈ B) : b % 4^m ≤ (4^m - 1) / 3 := by
  have h1 := B_decomp_mod m b hb
  have h2 : b % 4^m < 4^m := Nat.mod_lt _ (by positivity)
  exact B_max_bound m (b % 4^m) h1 h2

lemma y_lt_N_0 (k m a b N_0 : ℕ) (h_bound : a + b < min (3^k) (4^m) * N_0) :
  a / 3^k + b / 4^m < N_0 := by
  have heq := sum_form_eq k m a b
  have h1 : min (3^k) (4^m) * (a / 3^k + b / 4^m) ≤ a + b := by omega
  have h2 : min (3^k) (4^m) * (a / 3^k + b / 4^m) < min (3^k) (4^m) * N_0 := by omega
  exact Nat.lt_of_mul_lt_mul_left h2

lemma c_bound (k m a b N_0 : ℕ) (ha : a ∈ A) (hb : b ∈ B)
  (h_bound : a + b < min (3^k) (4^m) * N_0) :
  sum_c k m a b ≤ (3^k - 1)/2 + (4^m - 1)/3 + |(3^k : ℤ) - 4^m|.toNat * N_0 := by
  have hy := y_lt_N_0 k m a b N_0 h_bound
  have ha_bot := a_bot_bound k a ha
  have hb_bot := b_bot_bound m b hb
  have h_a_top_pos : 0 ≤ a / 3^k := Nat.zero_le _
  have h_b_top_pos : 0 ≤ b / 4^m := Nat.zero_le _
  unfold sum_c
  split_ifs with h_le
  · have h_abs : |(3^k : ℤ) - 4^m|.toNat = 4^m - 3^k := by
      have h_le_int : (3^k : ℤ) ≤ (4^m : ℤ) := by exact_mod_cast h_le
      exact (.trans (by rw [←abs_sub_comm,abs_of_nonneg ↑(sub_nonneg_of_le (mod_cast h_le))]) (by norm_cast))
    rw [h_abs]
    have h1 : b / 4^m ≤ a / 3^k + b / 4^m := by omega
    have h2 : b / 4^m ≤ N_0 := by omega
    have h_mul : (4^m - 3^k) * (b / 4^m) ≤ (4^m - 3^k) * N_0 := Nat.mul_le_mul_left _ h2
    omega
  · have h_abs : |(3^k : ℤ) - 4^m|.toNat = 3^k - 4^m := by
      exact (congr_arg _).comp (congr_arg abs (sub_eq_of_eq_add ↑(mod_cast (by valid)))).trans ( abs_of_nonneg (by constructor)) |>.trans (Int.toNat_natCast _)
    rw [h_abs]
    have h1 : a / 3^k ≤ a / 3^k + b / 4^m := by omega
    have h2 : a / 3^k ≤ N_0 := by omega
    have h_mul : (3^k - 4^m) * (a / 3^k) ≤ (3^k - 4^m) * N_0 := Nat.mul_le_mul_left _ h2
    omega

lemma sum_form (k m a b N_0 : ℕ) (ha : a ∈ A) (hb : b ∈ B)
  (h_bound : a + b < min (3^k) (4^m) * N_0) :
  ∃ y c, y ∈ A + B ∧ y < N_0 ∧
  c ≤ (3^k - 1)/2 + (4^m - 1)/3 + |(3^k : ℤ) - 4^m|.toNat * N_0 ∧
  a + b = min (3^k) (4^m) * y + c := by
  use a / 3^k + b / 4^m, sum_c k m a b
  constructor
  · use a / 3^k
    constructor
    · exact A_decomp_div k a ha
    · use b / 4^m
      constructor
      · exact B_decomp_div m b hb
      · rfl
  · constructor
    · exact y_lt_N_0 k m a b N_0 h_bound
    · constructor
      · exact c_bound k m a b N_0 ha hb h_bound
      · exact sum_form_eq k m a b

def sum_map (k m : ℕ) (p : ℕ × ℕ) : ℕ := min (3^k) (4^m) * p.1 + p.2

lemma subset_image (k m N_0 : ℕ) :
  (A + B) ∩ {x | x < min (3^k) (4^m) * N_0} ⊆
  (sum_map k m) '' (((A + B) ∩ {x | x < N_0}) ×ˢ {c | c ≤ (3^k - 1)/2 + (4^m - 1)/3 + |(3^k : ℤ) - 4^m|.toNat * N_0}) := by
  intro x hx
  rcases hx with ⟨hx_AB, hx_lt⟩
  rcases hx_AB with ⟨a, ha, b, hb, hab⟩
  have hab_eq : a + b = x := hab
  rw [←hab_eq] at hx_lt
  have h_form := sum_form k m a b N_0 ha hb hx_lt
  rcases h_form with ⟨y, c, hy_AB, hy_lt, hc, hac⟩
  use (y, c)
  constructor
  · rw [Set.mem_prod]
    constructor
    · exact ⟨hy_AB, hy_lt⟩
    · exact hc
  · have h_sum : sum_map k m (y, c) = min (3^k) (4^m) * y + c := rfl
    rw [h_sum, ←hac]
    exact hab_eq

lemma ncard_bound_step (k m N_0 : ℕ) (C : ℕ)
  (hC : (3^k - 1)/2 + (4^m - 1)/3 + |(3^k : ℤ) - 4^m|.toNat * N_0 ≤ C) :
  (((A + B) ∩ {x | x < min (3^k) (4^m) * N_0}).ncard : ℝ) ≤ (((A + B) ∩ {x | x < N_0}).ncard : ℝ) * (C + 1 : ℝ) := by
  have h_sub := subset_image k m N_0
  have h_sub2 : (A + B) ∩ {x | x < min (3^k) (4^m) * N_0} ⊆
    (sum_map k m) '' (((A + B) ∩ {x | x < N_0}) ×ˢ {c : ℕ | c ≤ C}) := by
    intro x hx
    have h_im := h_sub hx
    rcases h_im with ⟨p, hp, hx_eq⟩
    use p
    constructor
    · rw [Set.mem_prod] at hp ⊢
      constructor
      · exact hp.1
      · exact le_trans hp.2 hC
    · exact hx_eq
  have h_fin1 : {c : ℕ | c ≤ C}.Finite := Set.finite_le_nat C
  have h_fin2 : ((A + B) ∩ {x | x < N_0}).Finite := Set.toFinite _
  have h_fin_prod := Set.Finite.prod h_fin2 h_fin1
  have h_fin_im := Set.Finite.image (sum_map k m) h_fin_prod
  have h_le := Set.ncard_le_ncard h_sub2 h_fin_im
  have h_im_le : (sum_map k m '' (((A + B) ∩ {x | x < N_0}) ×ˢ {c : ℕ | c ≤ C})).ncard ≤ (((A + B) ∩ {x | x < N_0}) ×ˢ {c : ℕ | c ≤ C}).ncard := by exact Set.ncard_image_le h_fin_prod
  have h_prod : (((A + B) ∩ {x | x < N_0}) ×ˢ {c : ℕ | c ≤ C}).ncard = (((A + B) ∩ {x | x < N_0}).ncard) * ({c : ℕ | c ≤ C}.ncard) := by apply @Set.ncard_prod
  have h_c_card : {c : ℕ | c ≤ C}.ncard = C + 1 := by norm_num[Set.Iic_def, false,Set.ncard_eq_toFinset_card']
  have h_trans := le_trans h_le h_im_le
  rw [h_prod, h_c_card] at h_trans
  exact_mod_cast h_trans

lemma density_multiplier_le (k m N_0 : ℕ) (C : ℕ)
  (hC : (3^k - 1)/2 + (4^m - 1)/3 + |(3^k : ℤ) - 4^m|.toNat * N_0 ≤ C)
  (h_frac : (C + 1 : ℝ) / (min (3^k) (4^m) : ℝ) ≤ 14 / 15)
  (hN0 : N_0 > 0) :
  (((A + B) ∩ {x | x < min (3^k) (4^m) * N_0}).ncard : ℝ) / ((min (3^k) (4^m) * N_0 : ℕ) : ℝ) ≤
  (((A + B) ∩ {x | x < N_0}).ncard : ℝ) / (N_0 : ℝ) * (14 / 15) := by
  have h_bound := ncard_bound_step k m N_0 C hC
  have h_min_pos : min (3^k) (4^m) > 0 := by
    have h1 : 3^k > 0 := by positivity
    have h2 : 4^m > 0 := by positivity
    exact lt_min h1 h2
  have h_pos : (0 : ℝ) < ((min (3^k) (4^m) * N_0 : ℕ) : ℝ) := by
    have h_mul : min (3^k) (4^m) * N_0 > 0 := Nat.mul_pos h_min_pos hN0
    exact Nat.cast_pos.mpr h_mul
  have h1 : (((A + B) ∩ {x | x < min (3^k) (4^m) * N_0}).ncard : ℝ) / ((min (3^k) (4^m) * N_0 : ℕ) : ℝ) ≤ (((A + B) ∩ {x | x < N_0}).ncard : ℝ) * (C + 1 : ℝ) / ((min (3^k) (4^m) * N_0 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right h_bound (le_of_lt h_pos)
  have h_cast : ((min (3^k) (4^m) * N_0 : ℕ) : ℝ) = (min (3^k) (4^m) : ℝ) * (N_0 : ℝ) := by push_cast; rfl
  have h2 : (((A + B) ∩ {x | x < N_0}).ncard : ℝ) * (C + 1 : ℝ) / ((min (3^k) (4^m) * N_0 : ℕ) : ℝ) = (((A + B) ∩ {x | x < N_0}).ncard : ℝ) / (N_0 : ℝ) * ((C + 1 : ℝ) / (min (3^k) (4^m) : ℝ)) := by
    rw [h_cast]
    ring
  have h3 : (((A + B) ∩ {x | x < N_0}).ncard : ℝ) / (N_0 : ℝ) * ((C + 1 : ℝ) / (min (3^k) (4^m) : ℝ)) ≤ (((A + B) ∩ {x | x < N_0}).ncard : ℝ) / (N_0 : ℝ) * (14 / 15) := by
    have h_nonneg : (0 : ℝ) ≤ (((A + B) ∩ {x | x < N_0}).ncard : ℝ) / (N_0 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left h_frac h_nonneg
  rw [h2] at h1
  exact le_trans h1 h3

lemma ratio_close_of_log_close (k m : ℕ) (ε : ℝ) (hε : ε > 0)
  (h_gap : |(m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3| < Real.log (1 + ε)) :
  |(4^m : ℝ) / (3^k : ℝ) - 1| < ε := by
  simp_all[abs_sub_lt_iff,←Real.rpow_natCast, sub_lt_iff_lt_add',Real.rpow_def_of_pos, add_pos _,← Real.exp_sub]
  use(Real.lt_log_iff_exp_lt (by bound)).1 (by bound),by_contra fun and=>absurd ((Real.log 4*m-.log (3)*k+.log (1+ε)).add_one_le_exp) ?_
  use Real.exp_add _ _▸((1+ε).exp_log<|by linarith).symm▸by nlinarith

lemma exists_k_m_ratio_close (ε : ℝ) (hε : ε > 0) :
  ∃ k m : ℕ, (3^k : ℝ) > 30 ∧ (4^m : ℝ) > 30 ∧ |(4^m : ℝ) / (3^k : ℝ) - 1| < ε := by
  have h_eps2 : Real.log (1 + ε) > 0 := by apply Real.log_pos (by(linarith ) )
  have h_Q : ∃ Q : ℕ, Q > 0 ∧ Real.log 3 / ((Q : ℝ) + 1) < Real.log (1 + ε) / 10 := by exact ⟨ _, (by·bound), (div_lt_comm₀ (by{positivity}) (by ((positivity)))).mpr.comp (Nat.lt_succ_floor _).trans (lt_add_one _),⟩
  rcases h_Q with ⟨Q, hQ_pos, hQ_bound⟩
  rcases log_ratio_approximation Q hQ_pos with ⟨k, m, hm_pos, hm_le, h_gap⟩
  use 10 * k, 10 * m
  constructor
  · obtain ⟨rfl⟩ :=eq_or_ne k 0
    · norm_num[*, not_le.2.comp (div_lt_self _ _).trans,Real.log_lt_log,Real.log_pos,lt_abs,(le_mul_of_one_le_left _ _).trans_lt',le_of_lt,Nat.succ_le] at h_gap
      cases(h_gap.trans_lt<|div_lt_self (by bound) (by simp_all)).asymm ((lt_of_lt_of_le (by bound) (abs_le.1<|le_mul_of_one_le_left (abs_nonneg _) (by bound)).2))
    · norm_num[pow_mul,(le_self_pow₀ _ _).trans_lt', *]
  · constructor
    · norm_num[pow_mul,(pow_right_mono₀ _ hm_pos).trans_lt']
    · have h_gap_10 : |((10 * m : ℕ) : ℝ) * Real.log 4 - ((10 * k : ℕ) : ℝ) * Real.log 3| < Real.log (1 + ε) := by norm_num[h_gap.trans_lt,abs_mul,mul_assoc,←mul_sub,←lt_div_iff₀', *]
      exact ratio_close_of_log_close (10 * k) (10 * m) ε hε h_gap_10

lemma good_k_m_of_close (N_0 k m : ℕ)
  (h_M : (3^k : ℝ) > 30) (h_M4 : (4^m : ℝ) > 30)
  (h_eps : |(4^m : ℝ) / (3^k : ℝ) - 1| < 1 / (30 * N_0 + 30 : ℝ)) :
  min (3^k) (4^m) > 1 ∧
  ((((3^k - 1)/2 + (4^m - 1)/3 + |(3^k : ℤ) - 4^m|.toNat * N_0 : ℕ) : ℝ) + 1) / (min (3^k) (4^m) : ℝ) ≤ 14 / 15 := by
  cases le_total (3^k : ℤ) (4 ^m)
  · field_simp at@h_eps⊢
    simp_all[abs_sub_comm (3^k : ℝ),abs_div,abs_of_nonneg,(k.rec _ (by valid):2 ∣3^k-1),(m.rec _ (by valid):3 ∣4^m-1),div_mul_eq_mul_div,div_lt_one]
    norm_cast at*
    simp_all[Int.subNatNat_of_lt,h_M.trans',h_M4.trans']
    trans((3^k-1)/2+ (4^m-1)/3+ (4^m-3^k) *N_0+1)*15
    · exact (.trans (by rw [←Int.cast_natCast (Int.toNat _),Int.toNat_of_nonneg (abs_nonneg _)]) ↑(by simp_all[ (by assumption_mod_cast: (4: ℝ)^m≥3^ _),abs_of_nonpos]))
    · nlinarith[show (4^m-3^k: ℝ)*30*(N_0+1)<3^k by simp_all only[←@Nat.cast_lt ℝ,push_cast], (by assumption_mod_cast: (31 : ℝ)≤3^k)]
  · field_simp at@h_eps⊢
    simp_all[abs_sub_comm,abs_div,show((3^k-1)/2+ (4^m-1)/3+ (3^k-4^m) *N_0+1: ℝ)*15≤4^m*14 from _,]
    simp_all[div_mul_eq_mul_div,←geom_sum_mul_of_one_le]
    norm_cast at*
    refine Int.subNatNat_of_le (by valid)▸mod_cast(min_eq_right (by valid)).symm▸⟨by valid,?_⟩
    linarith [geom_sum_mul (3 : ℤ) k,geom_sum_mul (4 : ℤ) m,Nat.cast_lt.1 ((div_lt_one (by bound)).1 h_eps),Nat.sub_add_cancel (by assumption)]

lemma exists_good_k_m (N_0 : ℕ) :
  ∃ k m : ℕ, min (3^k) (4^m) > 1 ∧
  ((((3^k - 1)/2 + (4^m - 1)/3 + |(3^k : ℤ) - 4^m|.toNat * N_0 : ℕ) : ℝ) + 1) / (min (3^k) (4^m) : ℝ) ≤ 14 / 15 := by
  have h_eps_pos : (1 / (30 * (N_0 : ℝ) + 30)) > 0 := by positivity
  rcases exists_k_m_ratio_close (1 / (30 * (N_0 : ℝ) + 30)) h_eps_pos with ⟨k, m, h3, h4, he⟩
  use k, m
  exact good_k_m_of_close N_0 k m h3 h4 he

lemma card_inter_bound (S : Set ℕ) (N : ℕ) : (S ∩ {x | x < N}).ncard ≤ N := by
  apply(Nat.card_mono (Set.finite_lt_nat _) fun and=>And.right).trans_eq (Nat.card_eq_fintype_card.trans ( Fintype.card_ofFinset _ _▸by simp_all))

lemma multiple_gaps_bound_step (r M : ℕ)
  (h_prev : ∃ N_0 > M, (((A + B) ∩ {x | x < N_0}).ncard : ℝ) / (N_0 : ℝ) ≤ (14 / 15 : ℝ)^r) :
  ∃ N > M, (((A + B) ∩ {x | x < N}).ncard : ℝ) / (N : ℝ) ≤ (14 / 15 : ℝ)^(r + 1) := by
  rcases h_prev with ⟨N_0, hN_0, h_dens⟩
  have h_good := exists_good_k_m N_0
  rcases h_good with ⟨k, m, h_min, h_frac⟩
  use min (3^k) (4^m) * N_0
  constructor
  · have h1 : min (3^k) (4^m) ≥ 2 := by omega
    have h2 : N_0 ≥ M + 1 := by omega
    have h3 : min (3^k) (4^m) * N_0 ≥ 2 * N_0 := Nat.mul_le_mul_right N_0 h1
    omega
  · have hN0_pos : N_0 > 0 := by omega
    have h_mult := density_multiplier_le k m N_0 ((3^k - 1)/2 + (4^m - 1)/3 + |(3^k : ℤ) - 4^m|.toNat * N_0) (le_refl _) h_frac hN0_pos
    have h_pow : (14 / 15 : ℝ) * (14 / 15)^r = (14 / 15)^(r + 1) := by exact pow_succ' (14 / 15) r |>.symm
    have h_final : (((A + B) ∩ {x | x < min (3^k) (4^m) * N_0}).ncard : ℝ) / ((min (3^k) (4^m) * N_0 : ℕ) : ℝ) ≤ (14 / 15 : ℝ)^(r + 1) := by
      have h1 := h_mult
      have h2 : (((A + B) ∩ {x | x < N_0}).ncard : ℝ) / (N_0 : ℝ) * (14 / 15) ≤ (14 / 15)^r * (14 / 15) := by
        have h_pos : (0 : ℝ) ≤ 14 / 15 := by norm_num
        exact mul_le_mul_of_nonneg_right h_dens h_pos
      have h3 : (14 / 15 : ℝ)^r * (14 / 15) = (14 / 15)^(r + 1) := by
        have h_comm : (14 / 15 : ℝ)^r * (14 / 15) = (14 / 15) * (14 / 15)^r := mul_comm _ _
        rw [h_comm, h_pow]
      rw [h3] at h2
      exact le_trans h1 h2
    exact h_final

lemma multiple_gaps_bound (r M : ℕ) :
  ∃ N > M, (((A + B) ∩ {x | x < N}).ncard : ℝ) / (N : ℝ) ≤ (14 / 15 : ℝ)^r := by
  induction r generalizing M with
  | zero =>
    use M + 1
    constructor
    · omega
    · have h_pow : (14 / 15 : ℝ)^0 = 1 := by norm_num
      rw [h_pow]
      have h_card := card_inter_bound (A + B) (M + 1)
      have h_pos : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by positivity
      have h_cast : (((A + B) ∩ {x | x < M + 1}).ncard : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact Nat.cast_le.mpr h_card
      exact div_le_one_of_le₀ h_cast h_pos
  | succ r ih =>
    have h_ih := ih M
    exact multiple_gaps_bound_step r M h_ih

lemma exists_sparse_scale (ε : ℝ) (hε : ε > 0) (M : ℕ) :
  ∃ N > M, (((A + B) ∩ {x | x < N}).ncard : ℝ) / (N : ℝ) < ε := by
  have h_r : ∃ r : ℕ, (14 / 15 : ℝ)^r < ε := by
    have h_lim : Filter.Tendsto (fun r : ℕ => (14 / 15 : ℝ)^r) Filter.atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rw [Metric.tendsto_atTop] at h_lim
    rcases h_lim ε hε with ⟨R, hR⟩
    use R
    have h_abs := hR R (le_refl R)
    rw [Real.dist_eq, sub_zero] at h_abs
    have h_pos : (14 / 15 : ℝ)^R ≥ 0 := by positivity
    rw [abs_of_nonneg h_pos] at h_abs
    exact h_abs
  rcases h_r with ⟨r, hr⟩
  have h_N := multiple_gaps_bound r M
  rcases h_N with ⟨N, hNM, hN_dens⟩
  use N
  constructor
  · exact hNM
  · exact lt_of_le_of_lt hN_dens hr

lemma pach_pintz_scales :
  ∃ (N_seq : ℕ → ℕ), Filter.Tendsto N_seq Filter.atTop Filter.atTop ∧
  ∀ ε > 0, ∀ᶠ k in Filter.atTop, (((A + B) ∩ {x | x < N_seq k}).ncard : ℝ) / (N_seq k : ℝ) < ε := by
  have h_sparse := exists_sparse_scale
  choose R L using fun and=>h_sparse ((1/2) ^and) (by ·positivity)
  exact ⟨ _,Filter.tendsto_atTop_mono ( fun and=>le_of_lt (L _ _).1) (le_rfl), fun and x =>(summable_geometric_two.tendsto_atTop_zero.eventually_lt_const ↑x).mono fun and=>(L _ _).right.trans⟩

lemma pach_pintz_diophantine_gaps :
  ∃ (N_seq : ℕ → ℕ), Filter.Tendsto N_seq Filter.atTop Filter.atTop ∧
  Filter.Tendsto (fun k => (((A + B) ∩ {x | x < N_seq k}).ncard : ℝ) / N_seq k) Filter.atTop (nhds 0) := by
  have h_scales := pach_pintz_scales
  rcases h_scales with ⟨N_seq, h_tendsto_N, h_density⟩
  use N_seq
  constructor
  · exact h_tendsto_N
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have h1 := h_density ε hε
    filter_upwards [h1] with k hk
    have h_nonneg : (0 : ℝ) ≤ (((A + B) ∩ {x | x < N_seq k}).ncard : ℝ) / (N_seq k : ℝ) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nonneg]
    exact hk

lemma lower_density_zero : (A + B).lowerDensity = 0 := by
  have h_gaps := pach_pintz_diophantine_gaps
  simp_all[div_eq_inv_mul, Real.zero_lt_one,Set.lowerDensity,Set.inter_comm]
  refine h_gaps.elim fun and⟨A, B⟩=>Filter.liminf_eq.trans (symm ? _)
  exact (IsGreatest.csSup_eq (by use .of_forall (by bound), fun and=>ge_of_tendsto B ∘ A.eventually)).symm

/--
Let $A = {∑ ε_{k} 3^{k} : ε_{k} ∈ {0,1}}$ be the set of integers which
have only the digits $0, 1$ when written base 3, and $B = {∑ ε_{k} 4^{k} : ε_{k} ∈ {0,1}}$
be the set of integers which have only the digits $0, 1$ when written base 4.
Does $A + B$ have positive lower density?
-/
theorem erdos_125.variants.positive_lower_density :
    False ↔ 0 < ({ x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1} } +
      { x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1} }).lowerDensity := by
  have hA : {x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1}} = A := rfl
  have hB : {x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1}} = B := rfl
  have h_zero : (A + B).lowerDensity = 0 := lower_density_zero
  constructor
  · intro h
    contradiction
  · intro h
    rw [hA, hB] at h
    rw [h_zero] at h
    revert h
    norm_num


#print axioms erdos_125.variants.positive_lower_density
-- 'Erdos125.erdos_125.variants.positive_lower_density' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms erdos_125
-- 'Erdos125.erdos_125' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos125
