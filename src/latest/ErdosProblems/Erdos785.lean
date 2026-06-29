/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 785.
https://www.erdosproblems.com/forum/thread/785

Informal authors:
- András Sárközy
- Endre Szemerédi
- Władysław Narkiewicz
- Imre Z. Ruzsa

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/785#post-4642
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem785.lean
-/
/-
For a set $S$ of positive integers define $S(x) = |S \cap [1, x]|$. We then say
that sets of positive integers $A$ and $B$ are exact additive complements if every
large enough integer can be written as $a+b$ with $a \in A$, $b \in B$ and such
that $\frac{A(x) B(x)}{x}$ converges to $1$ if $x$ goes to infinity. Erdős and
Danzer conjectured that $A(x) B(x) - x$ goes to infinity with $x$ for any two exact
additive complements $A$ and $B$ that are both infinite
(see https://www.erdosproblems.com/785), and this was proven by Sárközy and Szemerédi.

András Sárközy and Endre Szemerédi, On a problem in additive number theory.
Acta Math. Hungar. (1994), 237-245.

In fact, Sárközy and Szemerédi prove that the upper bound $A(x) B(x) - x = o(A(x))$
cannot hold, which was subsequently improved by Chen and Fang showing that even
$A(x) B(x) - x = O(A(x)^c)$ cannot hold for any fixed $c$.

Yong-Gao Chen and Jin-Hui Fang, On a conjecture of Sárközy and Szemerédi.
Acta Arith. 169 (2015), 47–58.

With $a^*(x)$ defined as $\max\{a \in A, a \le x \}$, Ruzsa further improved the
lower bound on $A(x) B(x) - x$ to

$A(x) B(x) - x > (1 - o(1)) \frac{a^*(x)}{A(x)}.$

In Ruzsa's proof he made use of a theorem by Narkiewicz which is referred to as
Narkiewicz's dichotomoy theorem.

Władysław Narkiewicz, Remarks on a conjecture of Hanani in additive number theory,
Colloq. Math. 7 (1959/60), 161–165.

Below you can find a formalization of Ruzsa's proof, obtained by Aristotle from
Harmonic (aristotle-harmonic@harmonic.fun). The formalization also includes
Narkiewicz's dichotomoy theorem.

-/

import Mathlib

namespace Erdos785

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.cases false
set_option maxHeartbeats 1000000
-- Several generated additive-complement estimates time out at the default heartbeat limit.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option autoImplicit false

section

/-
Definitions of additive complements, counting function, and exact complements.
-/
open Pointwise

def is_additive_complement (A B : Set ℕ) : Prop :=
  (Set.univ \ (A + B)).Finite

noncomputable def counting_function (A : Set ℕ) (x : ℝ) : ℕ :=
  Nat.card {n ∈ A | n ≤ x}

def exact_complements (A B : Set ℕ) : Prop :=
  is_additive_complement A B ∧
  Filter.Tendsto (fun x : ℝ => (counting_function A x * counting_function B x : ℝ) / x) Filter.atTop (nhds 1)

/-
Define f_x(l) to be the number of representations of the integer l as a_i + b_j with a_i, b_j <= x. Let F(x) = sum_{l > x} f_x(l). Note that the sum is finite because if a_i, b_j <= x, then a_i + b_j <= 2x.
-/
noncomputable def representation_count (A B : Set ℕ) (x : ℝ) (l : ℕ) : ℕ :=
  Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 + p.2 = l}

noncomputable def large_sum_count (A B : Set ℕ) (x : ℝ) : ℕ :=
  ∑ l ∈ Finset.Ioc ⌊x⌋.toNat ⌊2 * x⌋.toNat, representation_count A B x l

/-
Let A, B be infinite sequences of positive integers for which \eqref{hyp} holds and such that the number r(x) of integers up to x not contained in their sumset A+B satisfies r(x)=o(x). We then have 0 <= F(x) = o(x).
-/
noncomputable def missing_sum_count (A B : Set ℕ) (x : ℝ) : ℕ :=
  Nat.card {n : ℕ | (n : ℝ) ≤ x ∧ n ∉ A + B}

theorem lemma_smallbigf (A B : Set ℕ)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => (large_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0) := by
      sorry
/-
Lemma: Under the assumptions, lim_{x -> infinity} (A(x/2)B(x) + A(x)B(x/2))/x = 3/2.
-/
theorem lemma_limit_3_2 (A B : Set ℕ)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => (counting_function A (x / 2) * counting_function B x + counting_function A x * counting_function B (x / 2) : ℝ) / x) Filter.atTop (nhds (3 / 2)) := by
  set F := fun (x : ℝ) => large_sum_count A B x;
  have hF : Filter.Tendsto (fun x => F x / x : ℝ → ℝ) Filter.atTop (nhds 0) := by
    convert lemma_smallbigf A B h_hyp h_r using 1;
  have h_bound : ∀ x : ℝ, x ≥ 1 → ((counting_function A x - counting_function A (x / 2)) * (counting_function B x - counting_function B (x / 2)) : ℝ) ≤ F x := by
    intro x hx
    have h_bound : ∀ a ∈ A, a ≤ x → a > x / 2 → ∀ b ∈ B, b ≤ x → b > x / 2 → a + b ∈ Finset.Icc (⌊x⌋.toNat + 1) (⌊2 * x⌋.toNat) := by
      intro a ha₁ ha₂ ha₃ b hb₁ hb₂ hb₃; refine Finset.mem_Icc.mpr ⟨ ?_, ?_ ⟩;
      · exact Nat.succ_le_of_lt ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le x, show ( ⌊x⌋ : ℝ ) = ⌊x⌋.toNat by exact_mod_cast Eq.symm <| Int.toNat_of_nonneg <| Int.floor_nonneg.mpr <| by positivity ] );
      · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( 2 * x ), Int.lt_floor_add_one ( 2 * x ), show ( ⌊2 * x⌋.toNat : ℝ ) = ⌊2 * x⌋ from mod_cast Int.toNat_of_nonneg <| Int.floor_nonneg.2 <| by positivity ] ;
    have h_card_bound : Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 > x / 2 ∧ p.2 > x / 2} ≤ F x := by
      have h_card_bound : Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 > x / 2 ∧ p.2 > x / 2} ≤ ∑ l ∈ Finset.Icc (⌊x⌋.toNat + 1) (⌊2 * x⌋.toNat), Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 + p.2 = l} := by
        have h_card_bound : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 > x / 2 ∧ p.2 > x / 2} ⊆ ⋃ l ∈ Finset.Icc (⌊x⌋.toNat + 1) (⌊2 * x⌋.toNat), {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 + p.2 = l} := by
          intro p hp; specialize h_bound p.1 hp.1 hp.2.2.1 hp.2.2.2.2.1 p.2 hp.2.1 hp.2.2.2.1 hp.2.2.2.2.2; aesop;
        have h_card_bound : Nat.card (⋃ l ∈ Finset.Icc (⌊x⌋.toNat + 1) (⌊2 * x⌋.toNat), {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 + p.2 = l}) ≤ ∑ l ∈ Finset.Icc (⌊x⌋.toNat + 1) (⌊2 * x⌋.toNat), Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 + p.2 = l} := by
          have h_card_bound : ∀ (S : Finset ℕ) (f : ℕ → Set (ℕ × ℕ)), Nat.card (⋃ l ∈ S, f l) ≤ ∑ l ∈ S, Nat.card (f l) := by
            intros S f; induction S using Finset.induction with
            | empty => aesop
            | insert l S hlS ih =>
            simp_all +decide [ Finset.sum_insert hlS ];
            exact le_trans ( Set.ncard_union_le _ _ ) ( add_le_add_right ih _ );
          exact h_card_bound _ _;
        refine le_trans ?_ h_card_bound;
        apply_rules [ Nat.card_mono ];
        refine Set.Finite.biUnion ( Finset.finite_toSet _ ) fun l hl => ?_;
        exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ ⌊x⌋.toNat, ⌊x⌋.toNat ⟩, by rintro ⟨ a, b ⟩ ⟨ ha, hb, ha', hb', hab ⟩ ; exact ⟨ Nat.le_floor <| mod_cast ha', Nat.le_floor <| mod_cast hb' ⟩ ⟩;
      convert h_card_bound using 1;
      simp only [F, large_sum_count];
      rw [← Order.succ_eq_add_one, Finset.Icc_succ_left_eq_Ioc];
      unfold representation_count; aesop;
    have h_card_eq : Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 > x / 2 ∧ p.2 > x / 2} = (Nat.card {n ∈ A | n ≤ x} - Nat.card {n ∈ A | n ≤ x / 2}) * (Nat.card {n ∈ B | n ≤ x} - Nat.card {n ∈ B | n ≤ x / 2}) := by
      have h_card_eq : Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 > x / 2 ∧ p.2 > x / 2} = Nat.card {n ∈ A | n ≤ x ∧ n > x / 2} * Nat.card {n ∈ B | n ≤ x ∧ n > x / 2} := by
        rw [ ← Nat.card_prod ];
        fapply Nat.card_congr;
        exact ⟨ fun p => ⟨ ⟨ p.val.1, p.prop.1, p.prop.2.2.1, p.prop.2.2.2.2.1 ⟩, ⟨ p.val.2, p.prop.2.1, p.prop.2.2.2.1, p.prop.2.2.2.2.2 ⟩ ⟩, fun p => ⟨ ⟨ p.1.val, p.2.val ⟩, p.1.prop.1, p.2.prop.1, p.1.prop.2.1, p.2.prop.2.1, p.1.prop.2.2, p.2.prop.2.2 ⟩, fun p => rfl, fun p => rfl ⟩;
      convert h_card_eq using 2;
      · rw [ tsub_eq_of_eq_add_rev ];
        rw [ show { n : ℕ | n ∈ A ∧ ( n : ℝ ) ≤ x } = { n : ℕ | n ∈ A ∧ ( n : ℝ ) ≤ x / 2 } ∪ { n : ℕ | n ∈ A ∧ ( n : ℝ ) ≤ x ∧ ( n : ℝ ) > x / 2 } from ?_, Nat.card_congr ( Equiv.Set.union <| ?_ ) ];
        · apply_rules [ Nat.card_sum ];
          · exact Set.Finite.to_subtype <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x / 2⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
          · exact Set.Finite.to_subtype <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2.1 ⟩;
        · exact Set.disjoint_left.mpr fun n hn hn' => hn'.2.2.not_ge hn.2;
        · ext; simp [Set.mem_union, Set.mem_setOf_eq];
          exact ⟨ fun h => if h' : ( ↑‹ℕ› : ℝ ) ≤ x / 2 then Or.inl ⟨ h.1, h' ⟩ else Or.inr ⟨ ⟨ h.1, h.2 ⟩, h.1, not_le.mp h' ⟩, fun h => h.elim ( fun h => ⟨ h.1, by linarith ⟩ ) fun h => ⟨ h.2.1, by linarith ⟩ ⟩;
      · rw [ show { n : ℕ | n ∈ B ∧ ( n : ℝ ) ≤ x } = { n : ℕ | n ∈ B ∧ ( n : ℝ ) ≤ x ∧ ( n : ℝ ) > x / 2 } ∪ { n : ℕ | n ∈ B ∧ ( n : ℝ ) ≤ x / 2 } from ?_, Nat.card_congr ( Equiv.Set.union <| ?_ ) ];
        · simp +decide [ Nat.card ];
          rw [ Cardinal.toNat_add ];
          · rw [ Nat.add_sub_cancel ];
          · exact Cardinal.lt_aleph0_iff_finite.mpr <| Set.Finite.to_subtype <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.1.2 ⟩;
          · exact Cardinal.lt_aleph0_iff_finite.mpr <| Set.Finite.to_subtype <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x / 2⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
        · exact Set.disjoint_left.mpr fun n hn hn' => hn.2.2.not_ge hn'.2;
        · ext n; simp [Set.mem_union, Set.mem_setOf_eq];
          exact ⟨ fun h => if h' : ( n : ℝ ) ≤ x / 2 then Or.inr ⟨ h.1, h' ⟩ else Or.inl ⟨ ⟨ h.1, h.2 ⟩, h.1, by linarith ⟩, fun h => h.elim ( fun h => ⟨ h.1.1, h.1.2 ⟩ ) fun h => ⟨ h.1, by linarith ⟩ ⟩;
    norm_cast;
    rw [ Int.subNatNat_of_le, Int.subNatNat_of_le ] <;> norm_cast;
    · exact h_card_eq ▸ h_card_bound;
    · apply_rules [ Nat.card_mono ];
      · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
      · exact fun n hn => ⟨ hn.1, hn.2.trans ( by linarith ) ⟩;
    · apply_rules [ Nat.card_mono ];
      · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
      · exact fun n hn => ⟨ hn.1, hn.2.trans ( by linarith ) ⟩;
  have h_lim : Filter.Tendsto (fun x => (counting_function A x * counting_function B x : ℝ) / x) Filter.atTop (nhds 1) := by
    convert h_hyp.2 using 1;
  have h_deriv : Filter.Tendsto (fun x => (counting_function A x * counting_function B x - (counting_function A x - counting_function A (x / 2)) * (counting_function B x - counting_function B (x / 2)) : ℝ) / x) Filter.atTop (nhds (1 - 0)) := by
    have h_deriv : Filter.Tendsto (fun x => ((counting_function A x - counting_function A (x / 2)) * (counting_function B x - counting_function B (x / 2)) : ℝ) / x) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ hF;
      filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( mul_nonneg ( sub_nonneg.2 <| Nat.cast_le.2 <| by
        apply_rules [ Nat.card_mono ];
        · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
        · exact fun n hn => ⟨ hn.1, hn.2.trans <| by linarith ⟩ ) ( sub_nonneg.2 <| Nat.cast_le.2 <| by
        apply_rules [ Nat.card_mono ];
        · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
        · exact fun n hn => ⟨ hn.1, hn.2.trans <| by linarith ⟩ ) ) <| by positivity ) ] ; exact div_le_div_of_nonneg_right ( h_bound x hx ) <| by positivity;
    simpa [ sub_div ] using h_lim.sub h_deriv;
  convert h_deriv.add ( h_lim.comp ( show Filter.Tendsto ( fun x : ℝ => x / 2 ) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_mul_const ( by norm_num ) ) |> ( ·.div_const 2 ) ) using 2 <;> ring_nf;
  grind

/-
Lemma: The difference between A(x/2)B(x)/x and A(x/2)/A(x) tends to 0.
-/
theorem lemma_term1_diff_zero (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B) :
    Filter.Tendsto (fun x : ℝ => (counting_function A (x / 2) * counting_function B x : ℝ) / x - (counting_function A (x / 2) : ℝ) / counting_function A x) Filter.atTop (nhds 0) := by
  -- We'll use that $A(x)$ is eventually greater than some constant $c > 0$ for large $x$.
  have h_bound : ∃ c > 0, ∀ᶠ x in Filter.atTop, counting_function A x ≥ c := by
    use 1; norm_num; (
    obtain ⟨ a, ha ⟩ := h_inf_A.exists_gt 0;
    use a;
    intro b hb; rw [ counting_function ] ;
    refine Nat.card_pos_iff.mpr ?_;
    exact ⟨ ⟨ a, ha.1, hb ⟩, Set.Finite.to_subtype <| Set.finite_iff_bddAbove.mpr ⟨ ⌊b⌋₊, fun x hx => Nat.le_floor <| hx.2 ⟩ ⟩);
  obtain ⟨c, hc_pos, hc_bound⟩ : ∃ c > 0, ∀ᶠ x in Filter.atTop, counting_function A x ≥ c := h_bound;
  have h_frac_bound : ∀ᶠ x in Filter.atTop, (counting_function A (x / 2) : ℝ) / (counting_function A x : ℝ) ≤ 1 := by
    have h_frac_bound : ∀ x : ℝ, 0 < x → (counting_function A (x / 2) : ℝ) ≤ (counting_function A x : ℝ) := by
      intros x hx_pos
      simp [counting_function];
      apply_rules [ Nat.card_mono ];
      · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
      · exact fun n hn => ⟨ hn.1, hn.2.trans ( by linarith ) ⟩;
    filter_upwards [ Filter.eventually_gt_atTop 0, hc_bound ] with x hx₁ hx₂ using div_le_one_of_le₀ ( h_frac_bound x hx₁ ) ( Nat.cast_nonneg _ );
  have h_term_zero : Filter.Tendsto (fun x : ℝ => ((counting_function A (x / 2)) : ℝ) / (counting_function A x : ℝ) * ((counting_function A x * counting_function B x : ℝ) / x - 1)) Filter.atTop (nhds 0) := by
    exact squeeze_zero_norm' ( by filter_upwards [ h_frac_bound ] with x hx using by simpa [ abs_mul, abs_div ] using mul_le_mul_of_nonneg_right hx <| abs_nonneg _ ) <| by simpa using h_hyp.2.sub_const 1 |> Filter.Tendsto.abs;;
  refine h_term_zero.congr' ?_ ; filter_upwards [ hc_bound, h_frac_bound ] with x hx₁ hx₂ ; by_cases hx₃ : counting_function A x = 0 <;> simp_all +decide [division_def,
    mul_comm, mul_left_comm] ; ring_nf;
  rw [ mul_inv_cancel₀ ( by positivity ), one_mul ] ; ring;

/-
Lemma: The difference between A(x)B(x/2)/x and A(x)/(2A(x/2)) tends to 0.
-/
theorem lemma_term2_diff_zero (A B : Set ℕ)
    (h_hyp : exact_complements A B) :
    Filter.Tendsto (fun x : ℝ => (counting_function A x * counting_function B (x / 2) : ℝ) / x - (counting_function A x : ℝ) / (2 * counting_function A (x / 2))) Filter.atTop (nhds 0) := by
  -- We know that $E(x) = \frac{2A(x/2)B(x/2)}{x} - 1$ tends to 0 as $x \to \infty$.
  have h_E_zero : Filter.Tendsto (fun x : ℝ => ((2 * counting_function A (x / 2) * counting_function B (x / 2)) / x : ℝ) - 1) Filter.atTop (nhds 0) := by
    have h_E_zero : Filter.Tendsto (fun x : ℝ => ((counting_function A x : ℝ) * (counting_function B x : ℝ)) / x) Filter.atTop (nhds 1) := by
      exact h_hyp.2;
    convert Filter.Tendsto.sub ( h_E_zero.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2⁻¹ : ℝ ) ) ) |> Filter.Tendsto.const_mul 1 ) tendsto_const_nhds using 2 <;> norm_num
    focus
      ring_nf
    exacts [ by rw [ neg_add_eq_sub ], by norm_num ];
  -- We have $\frac{A(x)}{2A(x/2)} (1 + E(x)) = \frac{A(x)B(x/2)}{x}$.
  suffices h_suff' : Filter.Tendsto (fun x : ℝ => ((counting_function A x : ℝ) / (2 * (counting_function A (x / 2) : ℝ))) * ((2 * (counting_function A (x / 2) : ℝ) * (counting_function B (x / 2) : ℝ)) / x - 1)) Filter.atTop (nhds 0) by
    refine h_suff'.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 0, h_E_zero.eventually ( Metric.ball_mem_nhds _ zero_lt_one ) ] with x hx₁ hx₂ ; by_cases h : counting_function A ( x / 2 ) = 0 <;> simp_all +decide [div_eq_mul_inv,
      mul_assoc, mul_comm] ; ring_nf;
    simpa [ h ] using by ring;
  -- Since $B(x/2) \le B(x)$, we have $\frac{A(x)B(x/2)}{x} \le \frac{A(x)B(x)}{x} \to 1$.
  have h_bound : ∀ᶠ x in Filter.atTop, ((counting_function A x : ℝ) * (counting_function B (x / 2) : ℝ)) / x ≤ 1 + 1 := by
    have h_bound : Filter.Tendsto (fun x : ℝ => ((counting_function A x : ℝ) * (counting_function B x : ℝ)) / x) Filter.atTop (nhds 1) := by
      convert h_hyp.2 using 1;
    filter_upwards [ h_bound.eventually ( gt_mem_nhds <| show 1 < 1 + 1 by norm_num ), Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂;
    refine le_trans ?_ hx₁.le;
    gcongr;
    apply_rules [ Nat.card_mono ];
    · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
    · exact fun n hn => ⟨ hn.1, hn.2.trans ( by linarith ) ⟩;
  -- Since $1+E(x) \to 1$, this implies $\frac{A(x)}{2A(x/2)}$ is eventually bounded.
  have h_bounded : ∃ C > 0, ∀ᶠ x in Filter.atTop, ((counting_function A x : ℝ) / (2 * (counting_function A (x / 2) : ℝ))) ≤ C := by
    have h_bounded : ∀ᶠ x in Filter.atTop, ((counting_function A x : ℝ) / (2 * (counting_function A (x / 2) : ℝ))) * (1 + (2 * (counting_function A (x / 2) : ℝ) * (counting_function B (x / 2) : ℝ)) / x - 1) ≤ 1 + 1 := by
      filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂;
      by_cases h : counting_function A ( x / 2 ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    have h_bounded : ∀ᶠ x in Filter.atTop, (1 + (2 * (counting_function A (x / 2) : ℝ) * (counting_function B (x / 2) : ℝ)) / x - 1) ≥ 1 / 2 := by
      have h_bounded : Filter.Tendsto (fun x : ℝ => (2 * (counting_function A (x / 2) : ℝ) * (counting_function B (x / 2) : ℝ)) / x) Filter.atTop (nhds 1) := by
        simpa using h_E_zero.add_const 1;
      filter_upwards [ h_bounded.eventually ( lt_mem_nhds <| show 1 > 1 / 2 by norm_num ) ] with x hx using by linarith;
    exact ⟨ 4, by norm_num, by filter_upwards [ ‹∀ᶠ x in Filter.atTop, ( counting_function A x : ℝ ) / ( 2 * counting_function A ( x / 2 ) ) * ( 1 + 2 * counting_function A ( x / 2 ) * counting_function B ( x / 2 ) / x - 1 ) ≤ 1 + 1›, h_bounded ] with x hx₁ hx₂ using by nlinarith [ show ( 0 : ℝ ) ≤ ( counting_function A x : ℝ ) / ( 2 * counting_function A ( x / 2 ) ) by positivity ] ⟩;
  refine squeeze_zero_norm'
    ( a := fun x => h_bounded.choose *
      |2 * ( counting_function A ( x / 2 ) : ℝ ) * ( counting_function B ( x / 2 ) : ℝ ) / x - 1| ) ?_ ?_;
  · filter_upwards [ h_bounded.choose_spec.2 ] with x hx using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ ( counting_function A x : ℝ ) / ( 2 * ( counting_function A ( x / 2 ) : ℝ ) ) ) ] ; exact mul_le_mul_of_nonneg_right hx ( abs_nonneg _ ) ;
  · simpa using tendsto_const_nhds.mul ( h_E_zero.abs )

/-
Lemma: Under the assumptions, lim_{x -> infinity} (A(x/2)/A(x) + A(x)/(2A(x/2))) = 3/2.
-/
theorem lemma_alpha_limit (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => (counting_function A (x / 2) : ℝ) / counting_function A x + counting_function A x / (2 * counting_function A (x / 2))) Filter.atTop (nhds (3 / 2)) := by
  -- By combining the results from `lemma_limit_3_2`, `lemma_term1_diff_zero`, and `lemma_term2_diff_zero`, we conclude the proof.
  have h_combined : Filter.Tendsto (fun x : ℝ => ((counting_function A (x / 2) * counting_function B x : ℝ) / x + (counting_function A x * counting_function B (x / 2) : ℝ) / x) - ((counting_function A (x / 2) : ℝ) / (counting_function A x : ℝ) + (counting_function A x : ℝ) / (2 * (counting_function A (x / 2) : ℝ)))) Filter.atTop (nhds 0) := by
    convert Filter.Tendsto.sub ( Filter.Tendsto.add ( lemma_term1_diff_zero A B h_inf_A h_hyp ) ( lemma_term2_diff_zero A B h_hyp ) ) tendsto_const_nhds using 2
    focus
      ring_nf!
    rotate_right;
    exacts [ 0, by ring, by ring ];
  have := lemma_limit_3_2 A B h_hyp h_r; convert this.sub h_combined using 2 <;> ring;

/-
Lemma: If alpha(x_n) converges to L, then L = 1 or L = 1/2.
-/
theorem lemma_accumulation_points (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (x : ℕ → ℝ) (hx : Filter.Tendsto x Filter.atTop Filter.atTop)
    (L : ℝ) (hL : Filter.Tendsto (fun n => (counting_function A (x n / 2) : ℝ) / counting_function A (x n)) Filter.atTop (nhds L)) :
    L = 1 ∨ L = 1 / 2 := by
  have h_eq : L + 1 / (2 * L) = 3 / 2 := by
    have h_eq : Filter.Tendsto (fun n => (counting_function A (x n / 2) / counting_function A (x n) : ℝ) + 1 / (2 * (counting_function A (x n / 2) / counting_function A (x n) : ℝ))) Filter.atTop (nhds (3 / 2)) := by
      convert Filter.Tendsto.comp ( lemma_alpha_limit A B h_inf_A h_hyp h_r ) hx using 2 ; norm_num ; ring;
    by_cases hL' : L = 0 <;> simp_all +decide [ division_def ];
    · have := h_eq.sub hL; norm_num at this;
      have := this.inv₀ ; norm_num at this;
      exact absurd ( tendsto_nhds_unique this ( hL.const_mul 2 |> Filter.Tendsto.congr ( by intros; ring_nf ) ) ) ( by norm_num );
    · have := h_eq.sub ( hL.add ( hL.inv₀ hL' |> Filter.Tendsto.mul_const ( 2⁻¹ : ℝ ) ) ) ; norm_num at * ; nlinarith [ mul_inv_cancel₀ hL' ] ;
  grind

/-
Lemma: If A(x_n/2)/A(x_n) -> 1, then A(x_n)/A(3x_n/4) -> 1.
-/
theorem lemma_alpha_implies_three_quarters (A : Set ℕ) (x : ℕ → ℝ) (hx : Filter.Tendsto x Filter.atTop Filter.atTop)
    (h_alpha : Filter.Tendsto (fun n => (counting_function A (x n / 2) : ℝ) / counting_function A (x n)) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => (counting_function A (x n) : ℝ) / counting_function A (3 * x n / 4)) Filter.atTop (nhds 1) := by
  -- Since $x_n / 2 \leq 3x_n / 4 \leq x_n$ for large $n$, and $A(x)$ is non-decreasing, we have $A(x_n / 2) \leq A(3x_n / 4) \leq A(x_n)$.
  have h_bounds : ∀ᶠ n in Filter.atTop, (counting_function A (x n / 2) : ℝ) ≤ (counting_function A (3 * x n / 4) : ℝ) ∧ (counting_function A (3 * x n / 4) : ℝ) ≤ (counting_function A (x n) : ℝ) := by
    filter_upwards [ hx.eventually_gt_atTop 0 ] with n hn;
    constructor <;> norm_cast <;> unfold counting_function <;> norm_num [ Nat.card_eq_fintype_card ];
    · apply_rules [ Nat.card_mono ];
      · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊3 * x n / 4⌋₊, fun y hy => Nat.le_floor <| hy.2 ⟩;
      · exact fun x hx => ⟨ hx.1, by linarith [ hx.2 ] ⟩;
    · apply_rules [ Nat.card_mono ];
      · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x n⌋₊, fun y hy => Nat.le_floor <| hy.2 ⟩;
      · exact fun x hx => ⟨ hx.1, by linarith [ hx.2 ] ⟩;
  have h_squeeze : Filter.Tendsto (fun n => (counting_function A (3 * x n / 4) : ℝ) / (counting_function A (x n) : ℝ)) Filter.atTop (nhds 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_alpha tendsto_const_nhds ?_ ?_;
    · filter_upwards [ h_bounds ] with n hn using div_le_div_of_nonneg_right hn.1 <| Nat.cast_nonneg _;
    · filter_upwards [ h_bounds ] with n hn using div_le_one_of_le₀ hn.2 ( Nat.cast_nonneg _ );
  simpa using h_squeeze.inv₀

/-
Lemma: The limit of (A(x/4)B(x) + A(x)B(3x/4) - A(x/4)B(3x/4))/x is 1.
-/
theorem lemma_quarter_limit_expression (A B : Set ℕ) (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => (counting_function A (x / 4) * counting_function B x + counting_function A x * counting_function B (3 * x / 4) - counting_function A (x / 4) * counting_function B (3 * x / 4) : ℝ) / x) Filter.atTop (nhds 1) := by
      sorry
/-
Lemma: If alpha(x_i) -> 1, then A(x_i/4)/A(x_i) -> 1.
-/
theorem lemma_quarter (A B : Set ℕ)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (x : ℕ → ℝ) (hx : Filter.Tendsto x Filter.atTop Filter.atTop)
    (h_alpha : Filter.Tendsto (fun n => (counting_function A (x n / 2) : ℝ) / counting_function A (x n)) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => (counting_function A (x n / 4) : ℝ) / counting_function A (x n)) Filter.atTop (nhds 1) := by
  -- We have established that the expression involving A(x/4), B(x), A(x), B(3x/4) tends to 1.
  have h_expr_limit : Filter.Tendsto (fun n => (counting_function A (x n / 4) * counting_function B (x n) + counting_function A (x n) * counting_function B (3 * x n / 4) - counting_function A (x n / 4) * counting_function B (3 * x n / 4) : ℝ) / x n) Filter.atTop (nhds 1) := by
    exact (lemma_quarter_limit_expression A B h_hyp h_r).comp hx;
  -- We also know that A(x_n)/A(3x_n/4) -> 1.
  have h_ratio_limit : Filter.Tendsto (fun n => (counting_function A (x n) : ℝ) / counting_function A (3 * x n / 4)) Filter.atTop (nhds 1) := by
    exact lemma_alpha_implies_three_quarters A x hx h_alpha;
  -- We can rewrite the expression in terms of ratios.
  -- Let L_n = A(x_n/4)/A(x_n). We want to show L_n -> 1.
  -- The expression is roughly L_n * (A(x_n)B(x_n)/x_n) + (A(x_n)/A(3x_n/4)) * (A(3x_n/4)B(3x_n/4)/x_n) - L_n * (A(x_n)/A(3x_n/4)) * (A(3x_n/4)B(3x_n/4)/x_n).
  -- We know A(y)B(y)/y -> 1.
  have h_AB_limit : Filter.Tendsto (fun y => (counting_function A y * counting_function B y : ℝ) / y) Filter.atTop (nhds 1) := h_hyp.2;
  have h_AB_xn : Filter.Tendsto (fun n => (counting_function A (x n) * counting_function B (x n) : ℝ) / x n) Filter.atTop (nhds 1) := h_AB_limit.comp hx;
  have h_AB_3xn4 : Filter.Tendsto (fun n => (counting_function A (3 * x n / 4) * counting_function B (3 * x n / 4) : ℝ) / (3 * x n / 4)) Filter.atTop (nhds 1) := by
    refine h_AB_limit.comp ?_;
    refine Filter.tendsto_atTop_atTop.mpr (fun b => ?_);
    have ha := hx.eventually_ge_atTop (4 * b / 3);
    rw [Filter.eventually_atTop] at ha;
    obtain ⟨a, ha⟩ := ha;
    use a; intro n hn;
    specialize ha n hn;
    linarith;
  -- Now we construct the limit of the rewritten expression.
  -- We want to prove that L_n * 1 + 1 * (3/4) * 1 - L_n * 1 * (3/4) * 1 -> 1.
  -- This simplifies to L_n * (1 - 3/4) + 3/4 -> 1, i.e., L_n/4 -> 1/4, so L_n -> 1.
  -- To do this formally, we'll show that the difference between the original expression and the simplified one tends to 0.
  -- By combining the limits, we can isolate the term involving $A(x_n/4)$.
  have h_isolate : Filter.Tendsto (fun n => ((counting_function A (x n / 4) : ℝ) * (counting_function B (x n) : ℝ) - (counting_function A (x n / 4) : ℝ) * (counting_function B (3 * x n / 4) : ℝ)) / x n) Filter.atTop (nhds (1 - 3 / 4)) := by
    have h_isolate : Filter.Tendsto (fun n => ((counting_function A (x n) : ℝ) * (counting_function B (3 * x n / 4) : ℝ)) / x n) Filter.atTop (nhds (3 / 4)) := by
      have h_rewrite : Filter.Tendsto (fun n => ((counting_function A (3 * x n / 4) : ℝ) * (counting_function B (3 * x n / 4) : ℝ)) / (3 * x n / 4) * ((counting_function A (x n) : ℝ) / (counting_function A (3 * x n / 4) : ℝ)) * (3 / 4)) Filter.atTop (nhds (3 / 4)) := by
        simpa using Filter.Tendsto.mul ( Filter.Tendsto.mul h_AB_3xn4 h_ratio_limit ) tendsto_const_nhds;
      refine h_rewrite.congr' ?_;
      filter_upwards [ h_ratio_limit.eventually_ne one_ne_zero ] with n hn;
      grind;
    convert h_expr_limit.sub h_isolate using 2 ; ring;
  have h_factor : Filter.Tendsto (fun n => ((counting_function A (x n / 4) : ℝ) / (counting_function A (x n) : ℝ)) * ((counting_function A (x n) : ℝ) * (counting_function B (x n) : ℝ) / x n - (counting_function A (x n) : ℝ) * (counting_function B (3 * x n / 4) : ℝ) / x n)) Filter.atTop (nhds (1 - 3 / 4)) := by
    refine h_isolate.congr' ?_;
    filter_upwards [ h_alpha.eventually_ne one_ne_zero ] with n hn using by rw [ div_mul_eq_mul_div, eq_div_iff ( by aesop ) ] ; ring;
  have h_divide : Filter.Tendsto (fun n => ((counting_function A (x n) : ℝ) * (counting_function B (x n) : ℝ) / x n - (counting_function A (x n) : ℝ) * (counting_function B (3 * x n / 4) : ℝ) / x n)) Filter.atTop (nhds (1 - 3 / 4)) := by
    have h_divide : Filter.Tendsto (fun n => ((counting_function A (x n) : ℝ) * (counting_function B (3 * x n / 4) : ℝ) / x n)) Filter.atTop (nhds (3 / 4)) := by
      have h_divide : Filter.Tendsto (fun n => ((counting_function A (x n) : ℝ) / (counting_function A (3 * x n / 4) : ℝ)) * ((counting_function A (3 * x n / 4) : ℝ) * (counting_function B (3 * x n / 4) : ℝ) / (3 * x n / 4)) * (3 / 4)) Filter.atTop (nhds (3 / 4)) := by
        convert Filter.Tendsto.mul ( Filter.Tendsto.mul h_ratio_limit h_AB_3xn4 ) tendsto_const_nhds using 2 ; ring;
      refine h_divide.congr' ?_;
      filter_upwards [ h_ratio_limit.eventually_ne one_ne_zero ] with n hn;
      grind;
    exact h_AB_xn.sub h_divide;
  have := h_factor.div h_divide; norm_num at *;
  refine this.congr' ( by
    filter_upwards [ h_divide.eventually_ne ( show ( 1 / 4 : ℝ ) ≠ 0 by norm_num ) ] with n hn
    rw [ Pi.div_apply,
      mul_div_cancel_right₀
        ((counting_function A (x n / 4) : ℝ) / (counting_function A (x n) : ℝ)) hn ] )

/-
Definitions of alpha(x) and the set X of x where 1/alpha(x) is close to 1.
-/
noncomputable def alpha (A : Set ℕ) (x : ℝ) : ℝ :=
  (counting_function A (x / 2) : ℝ) / (counting_function A x : ℝ)

def close_to_one_set (A : Set ℕ) : Set ℝ :=
  {x | |(counting_function A x : ℝ) / (counting_function A (x / 2) : ℝ) - 1| < 1 / 4}

/-
The set X is unbounded.
-/
theorem close_to_one_set_unbounded (A : Set ℕ) (x : ℕ → ℝ) (hx : Filter.Tendsto x Filter.atTop Filter.atTop)
    (h_alpha : Filter.Tendsto (fun n => alpha A (x n)) Filter.atTop (nhds 1)) :
    ∀ y, ∃ z ∈ close_to_one_set A, z ≥ y := by
      sorry
/-
The counting function of an infinite set tends to infinity.
-/
theorem counting_function_tendsto_atTop (A : Set ℕ) (h_inf : A.Infinite) :
    Filter.Tendsto (fun x : ℝ => counting_function A x) Filter.atTop Filter.atTop := by
  have h_counting_A_inf : Filter.Tendsto (fun x : ℕ => Nat.card {n ∈ A | n ≤ x}) Filter.atTop Filter.atTop := by
    have h_counting_A_inf : Filter.Tendsto (fun x : ℕ => Finset.card (Finset.filter (fun n => n ∈ A) (Finset.Iic x))) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_atTop.mpr fun n => ?_;
      obtain ⟨ s, hs ⟩ := h_inf.exists_subset_card_eq n;
      exact ⟨ s.sup id, fun x hx => hs.2 ▸ Finset.card_le_card fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Iic.mpr ( le_trans ( Finset.le_sup ( f := id ) hy ) hx ), hs.1 hy ⟩ ⟩;
    convert h_counting_A_inf using 2 ; simp +decide [Set.setOf_and];
    congr ; ext ; aesop;
  refine Filter.tendsto_atTop_atTop.mpr fun n => ?_;
  obtain ⟨ i, hi ⟩ := Filter.eventually_atTop.mp ( h_counting_A_inf.eventually_ge_atTop n ) ; use i; intro x hx; refine le_trans ( hi ( Nat.floor x ) ( Nat.le_floor <| mod_cast hx ) ) ?_ ;
  apply_rules [ Nat.card_mono ];
  · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
  · exact fun n hn => ⟨ hn.1, le_trans ( Nat.cast_le.mpr hn.2 ) ( Nat.floor_le ( by linarith ) ) ⟩

/-
x is in the close_to_one_set iff floor(x) is in the set.
-/
theorem mem_close_to_one_set_iff_floor_mem (A : Set ℕ) (x : ℝ) :
    x ∈ close_to_one_set A ↔ (⌊x⌋ : ℝ) ∈ close_to_one_set A := by
      sorry
/-
Definition of zeta(y) as the infimum of x in X such that x >= y.
-/
noncomputable def erdos785_zeta (A : Set ℕ) (y : ℝ) : ℝ :=
  sInf {x | x ≥ y ∧ x ∈ close_to_one_set A}

local notation "zeta" => erdos785_zeta

/-
If k is in X, then [k, k+1) is in X.
-/
theorem close_to_one_set_is_union_of_intervals (A : Set ℕ) (k : ℤ) (hk : (k : ℝ) ∈ close_to_one_set A) :
    Set.Ico (k : ℝ) (k + 1) ⊆ close_to_one_set A := by
  intro x hx
  rw [mem_close_to_one_set_iff_floor_mem]
  have : ⌊x⌋ = k := Int.floor_eq_iff.mpr hx
  rwa [this]

/-
zeta(y) is in the close_to_one_set.
-/
theorem zeta_mem_close_to_one_set (A : Set ℕ) (y : ℝ)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    zeta A y ∈ close_to_one_set A := by
      -- By definition of $zeta$, we know that $zeta(y)$ is the greatest lower bound (infimum) of the set ${x ∈ close_to_one_set A | y ≤ x}$.
      set S := {x : ℝ | x ≥ y ∧ x ∈ close_to_one_set A} with hS_def
      have hS_nonempty : S.Nonempty := by
        exact Exists.elim ( h_unbounded y ) fun w hw => ⟨ w, hw.2, hw.1 ⟩
      have hS_inf : zeta A y = sInf S := by
        rfl;
      -- Since S is nonempty and bounded below, its infimum is in S.
      have hS_inf_mem : sInf S ∈ S := by
        have hS_inf_mem : ∀ x ∈ S, ∃ k : ℤ, x ∈ Set.Ico (k : ℝ) (k + 1) ∧ (k : ℝ) ∈ close_to_one_set A := by
          exact fun x hx => ⟨ ⌊x⌋, ⟨ Int.floor_le x, Int.lt_floor_add_one x ⟩, by simpa using mem_close_to_one_set_iff_floor_mem A x |>.1 hx.2 ⟩;
        -- Let $k$ be the smallest integer such that $[k, k+1) \cap S \neq \emptyset$.
        obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℝ) ∈ close_to_one_set A ∧ ∃ x ∈ S, x ∈ Set.Ico (k : ℝ) (k + 1) ∧ ∀ m : ℤ, m < k → ¬∃ x ∈ S, x ∈ Set.Ico (m : ℝ) (m + 1) := by
          obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℝ) ∈ close_to_one_set A ∧ ∃ x ∈ S, x ∈ Set.Ico (k : ℝ) (k + 1) := by
            exact Exists.elim ( hS_inf_mem _ hS_nonempty.choose_spec ) fun k hk => ⟨ k, hk.2, _, hS_nonempty.choose_spec, hk.1 ⟩;
          have h_least : ∃ m ∈ {k : ℤ | (k : ℝ) ∈ close_to_one_set A ∧ ∃ x ∈ S, x ∈ Set.Ico (k : ℝ) (k + 1)}, ∀ n ∈ {k : ℤ | (k : ℝ) ∈ close_to_one_set A ∧ ∃ x ∈ S, x ∈ Set.Ico (k : ℝ) (k + 1)}, m ≤ n := by
            apply_rules [ Int.exists_least_of_bdd ];
            · exact ⟨ ⌊y⌋, fun z hz => Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le y, Int.lt_floor_add_one y, hz.2.choose_spec.1.1, hz.2.choose_spec.2.1, hz.2.choose_spec.2.2 ] ⟩;
            · exact ⟨ k, hk ⟩;
          obtain ⟨ m, hm₁, hm₂ ⟩ := h_least; exact ⟨ m, hm₁.1, by obtain ⟨ x, hx₁, hx₂ ⟩ := hm₁.2; exact ⟨ x, hx₁, hx₂, fun n hn₁ hn₂ => not_lt_of_ge ( hm₂ n ⟨ by
            obtain ⟨ x, hx₁, hx₂ ⟩ := hn₂; exact mem_close_to_one_set_iff_floor_mem A x |>.1 hx₁.2 |> fun h => by simpa [ show ⌊x⌋ = n by exact Int.floor_eq_iff.mpr ⟨ by linarith [ hx₂.1 ], by linarith [ hx₂.2 ] ⟩ ] using h;, hn₂ ⟩ ) hn₁ ⟩ ⟩ ;
        -- Since $k$ is the smallest integer such that $[k, k+1) \cap S \neq \emptyset$, we have $sInf S \in [k, k+1)$.
        have h_inf_in_interval : sInf S ∈ Set.Ico (k : ℝ) (k + 1) := by
          have h_inf_in_interval : ∀ x ∈ S, x ≥ k := by
            intros x hx
            obtain ⟨m, hm⟩ := hS_inf_mem x hx
            have hm_ge_k : m ≥ k := by
              exact le_of_not_gt fun h => hk.2.choose_spec.2.2 m h ⟨ x, hx, hm.1 ⟩
            have hx_ge_k : x ≥ k := by
              exact le_trans ( mod_cast hm_ge_k ) hm.1.1
            exact hx_ge_k;
          exact ⟨ le_csInf hS_nonempty h_inf_in_interval, lt_of_le_of_lt ( csInf_le ⟨ k, h_inf_in_interval ⟩ hk.2.choose_spec.1 ) hk.2.choose_spec.2.1.2 ⟩;
        exact ⟨ le_of_not_gt fun h => by linarith [ h_inf_in_interval.1, h_inf_in_interval.2, show ( InfSet.sInf S : ℝ ) ≥ y from le_csInf hS_nonempty fun x hx => hx.1 ], by simpa using close_to_one_set_is_union_of_intervals A k hk.1 h_inf_in_interval ⟩;
      exact hS_inf.symm ▸ hS_inf_mem.2

/-
Definition of zeta_n and proof that it is in X.
-/
noncomputable def zeta_seq (A : Set ℕ) (y : ℕ → ℝ) : ℕ → ℝ :=
  fun n => zeta A (y n)

theorem zeta_seq_mem_close_to_one_set (A : Set ℕ) (y : ℕ → ℝ)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    ∀ n, zeta_seq A y n ∈ close_to_one_set A := by
  intro n
  apply zeta_mem_close_to_one_set A (y n) h_unbounded

/-
zeta_seq tends to infinity.
-/
theorem zeta_seq_tendsto_atTop (A : Set ℕ) (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    Filter.Tendsto (zeta_seq A y) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono ?_ hy;
      intro n; exact (by
      apply le_csInf;
      · exact Exists.elim ( h_unbounded ( y n ) ) fun w hw => ⟨ w, hw.2, hw.1 ⟩;
      · aesop)

/-
If x is in X, then 4/5 < alpha(x) < 4/3.
-/
theorem lemma_alpha_bounds_in_X (A : Set ℕ) (x : ℝ) (hx : x ∈ close_to_one_set A) :
    4 / 5 < alpha A x ∧ alpha A x < 4 / 3 := by
      unfold close_to_one_set at hx;
      unfold alpha; constructor <;> norm_num at *;
      · by_cases h : counting_function A ( x / 2 ) = 0 <;> simp_all +decide [ abs_lt ];
        · norm_num at hx;
        · rw [ div_lt_div_iff₀ ] <;> norm_num at *;
          · rw [ div_sub_one, div_lt_iff₀ ] at hx <;> first | positivity | linarith;
          · exact Nat.pos_of_ne_zero ( by rintro h'; norm_num [ h' ] at hx );
      · by_cases h : counting_function A ( x / 2 ) = 0 <;> simp_all +decide [ abs_lt ];
        rw [ div_lt_iff₀ ] <;> nlinarith [ show ( counting_function A ( x / 2 ) : ℝ ) > 0 by positivity, div_mul_cancel₀ ( counting_function A x : ℝ ) ( show ( counting_function A ( x / 2 ) : ℝ ) ≠ 0 by positivity ) ]

/-
alpha(zeta_n) converges to 1.
-/
theorem lemma_zeta_alpha_limit (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    Filter.Tendsto (fun n => alpha A (zeta_seq A y n)) Filter.atTop (nhds 1) := by
      sorry
/-
alpha(zeta_n) is eventually in (4/5, 4/3).
-/
theorem lemma_zeta_alpha_bounded (A : Set ℕ) (y : ℕ → ℝ)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    ∀ᶠ n in Filter.atTop, 4 / 5 < alpha A (zeta_seq A y n) ∧ alpha A (zeta_seq A y n) < 4 / 3 := by
  filter_upwards with n
  have h_mem := zeta_seq_mem_close_to_one_set A y h_unbounded n
  exact lemma_alpha_bounds_in_X A (zeta_seq A y n) h_mem

/-
If a sequence is eventually in (4/5, 4/3) and cluster points are in {1, 1/2}, it converges to 1.
-/
theorem lemma_convergence_helper (u : ℕ → ℝ)
    (h_bounds : ∀ᶠ n in Filter.atTop, 4 / 5 < u n ∧ u n < 4 / 3)
    (h_cluster : ∀ L, ClusterPt L (Filter.map u Filter.atTop) → L = 1 ∨ L = 1 / 2) :
    Filter.Tendsto u Filter.atTop (nhds 1) := by
      sorry
/-
If L is a cluster point of alpha(zeta_n), then L = 1 or L = 1/2.
-/
theorem lemma_accumulation_points_cluster (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z)
    (L : ℝ) (hL : MapClusterPt L Filter.atTop (fun n => alpha A (zeta_seq A y n))) :
    L = 1 ∨ L = 1 / 2 := by
      obtain ⟨x, hx⟩ : ∃ x : ℕ → ℕ, StrictMono x ∧ Filter.Tendsto (fun n => alpha A (zeta_seq A y (x n))) Filter.atTop (nhds L) := by
        rw [ mapClusterPt_iff_frequently ] at hL;
        have h_subseq : ∀ n : ℕ, ∃ m ≥ n, alpha A (zeta_seq A y m) ∈ Metric.ball L (1 / (n + 1)) := by
          intro n; specialize hL ( Metric.ball L ( 1 / ( n + 1 ) ) ) ( Metric.ball_mem_nhds _ <| by positivity ) ; simp_all +decide [ Filter.frequently_atTop ] ;
        choose f hf₁ hf₂ using h_subseq;
        refine ⟨ fun n => f ( Nat.recOn n 0 fun n ih => f ih + 1 ), strictMono_nat_of_lt_succ fun n => ?_, ?_ ⟩;
        · exact lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( hf₁ _ );
        · exact tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => dist_nonneg ) ( fun n => le_of_lt <| Metric.mem_ball.mp <| hf₂ _ ) <| tendsto_one_div_add_atTop_nhds_zero_nat.comp <| Filter.tendsto_atTop_mono ( fun n => Nat.recOn n ( by norm_num ) fun n ihn => by linarith [ hf₁ ( Nat.rec 0 ( fun n ih => f ih + 1 ) n ) ] ) tendsto_natCast_atTop_atTop;
      -- By the properties of the sequence $zeta_seq$, we know that $zeta_seq A y (x n) \to \infty$ as $n \to \infty$.
      have h_zeta_seq_inf : Filter.Tendsto (fun n => zeta_seq A y (x n)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.comp (zeta_seq_tendsto_atTop A y hy h_unbounded) hx.1.tendsto_atTop;
      have := @lemma_accumulation_points A B h_inf_A h_hyp h_r ( fun n => zeta_seq A y ( x n ) ) h_zeta_seq_inf L hx.2; aesop;

/-
alpha(zeta_n) converges to 1.
-/
theorem lemma_zeta_alpha_limit_v2 (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    Filter.Tendsto (fun n => alpha A (zeta_seq A y n)) Filter.atTop (nhds 1) := by
  let u := fun n => alpha A (zeta_seq A y n)
  have h_bounds : ∀ᶠ n in Filter.atTop, 4 / 5 < u n ∧ u n < 4 / 3 :=
    lemma_zeta_alpha_bounded A y h_unbounded
  have h_cluster : ∀ L, MapClusterPt L Filter.atTop u → L = 1 ∨ L = 1 / 2 :=
    fun L hL => lemma_accumulation_points_cluster A B h_inf_A h_hyp h_r y hy h_unbounded L hL
  exact lemma_convergence_helper u h_bounds h_cluster

/-
A(zeta_n/4)/A(zeta_n) converges to 1.
-/
theorem lemma_zeta_one (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    Filter.Tendsto (fun n => (counting_function A (zeta_seq A y n / 4) : ℝ) / counting_function A (zeta_seq A y n)) Filter.atTop (nhds 1) := by
  let x := zeta_seq A y
  have hx : Filter.Tendsto x Filter.atTop Filter.atTop := zeta_seq_tendsto_atTop A y hy h_unbounded
  have h_alpha : Filter.Tendsto (fun n => alpha A (x n)) Filter.atTop (nhds 1) :=
    lemma_zeta_alpha_limit_v2 A B h_inf_A h_hyp h_r y hy h_unbounded
  exact lemma_quarter A B h_hyp h_r x hx h_alpha

/-
A(zeta_n/2)/A(zeta_n/4) converges to 1.
-/
theorem lemma_zeta_halves_limit (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    Filter.Tendsto (fun n => (counting_function A (zeta_seq A y n / 2) : ℝ) / counting_function A (zeta_seq A y n / 4)) Filter.atTop (nhds 1) := by
      sorry
/-
For sufficiently large n, zeta(y_n) / 2 <= y_n.
-/
theorem lemma_zeta_half_le_y (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    ∀ᶠ n in Filter.atTop, zeta_seq A y n / 2 ≤ y n := by
      sorry
/-
zeta(y) >= y.
-/
theorem lemma_zeta_ge_y (A : Set ℕ) (y : ℝ)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    zeta A y ≥ y := by
      apply le_csInf;
      · exact Exists.imp ( by tauto ) ( h_unbounded y );
      · grind

/-
The counting function is monotone.
-/
theorem lemma_counting_function_mono (A : Set ℕ) : Monotone (counting_function A) := by
  intro x y hxy
  have h_subset : {n ∈ A | n ≤ x} ⊆ {n ∈ A | n ≤ y} := by
    exact fun n hn => ⟨ hn.1, le_trans hn.2 hxy ⟩
  exact (by
  apply_rules [ Nat.card_mono ];
  exact Set.finite_iff_bddAbove.mpr ⟨ ⌊y⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩)

/-
The ratio A(y_n)/A(y_n/2) tends to 1.
-/
theorem lemma_y_limit (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    Filter.Tendsto (fun n => (counting_function A (y n) : ℝ) / counting_function A (y n / 2)) Filter.atTop (nhds 1) := by
      -- The ratio A(1/4 zeta_n) / A(zeta_n) tends to 1 by lemma_zeta_one.
      have h_ratio_zeta_one : Filter.Tendsto (fun n => (counting_function A (zeta_seq A y n / 4) : ℝ) / (counting_function A (zeta_seq A y n))) Filter.atTop (nhds 1) := by
        convert lemma_zeta_one A B h_inf_A h_hyp h_r y hy h_unbounded using 1;
      -- By the properties of the counting function, we have that for sufficiently large $n$, $A(1/4 zeta_n) \leq A(1/2 y_n) \leq A(y_n) \leq A(zeta_n)$.
      have h_bounds : ∀ᶠ n in Filter.atTop, (counting_function A (zeta_seq A y n / 4) : ℝ) ≤ (counting_function A (y n / 2) : ℝ) ∧ (counting_function A (y n / 2) : ℝ) ≤ (counting_function A (y n) : ℝ) ∧ (counting_function A (y n) : ℝ) ≤ (counting_function A (zeta_seq A y n) : ℝ) := by
        have h_bounds : ∀ᶠ n in Filter.atTop, zeta_seq A y n / 4 ≤ y n / 2 ∧ y n / 2 ≤ y n ∧ y n ≤ zeta_seq A y n := by
          have h_bounds : ∀ᶠ n in Filter.atTop, zeta_seq A y n / 2 ≤ y n := by
            apply_rules [ lemma_zeta_half_le_y ];
          filter_upwards [ h_bounds, hy.eventually_gt_atTop 0 ] with n hn hn' using ⟨ by linarith, by linarith, by linarith [ show zeta_seq A y n ≥ y n from lemma_zeta_ge_y A ( y n ) h_unbounded ] ⟩;
        field_simp;
        filter_upwards [ h_bounds ] with n hn;
        exact ⟨ mod_cast lemma_counting_function_mono A hn.1, mod_cast lemma_counting_function_mono A hn.2.1, mod_cast lemma_counting_function_mono A hn.2.2 ⟩;
      -- Using the bounds, we can show that the ratio $A(y_n)/A(y_n/2)$ is squeezed between two sequences that tend to 1.
      have h_squeeze : ∀ᶠ n in Filter.atTop, (counting_function A (zeta_seq A y n) : ℝ) / (counting_function A (zeta_seq A y n / 4) : ℝ) ≥ (counting_function A (y n) : ℝ) / (counting_function A (y n / 2) : ℝ) ∧ (counting_function A (y n) : ℝ) / (counting_function A (y n / 2) : ℝ) ≥ 1 := by
        filter_upwards [ h_bounds, h_ratio_zeta_one.eventually ( lt_mem_nhds one_pos ) ] with n hn hn';
        constructor;
        · rw [ ge_iff_le, div_le_div_iff₀ ];
          · nlinarith;
          · contrapose! hn'; aesop;
          · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero fun h => by norm_num [ h ] at hn' );
        · exact one_le_div ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop_cat ) |>.2 hn.2.1;
      have h_squeeze : Filter.Tendsto (fun n => (counting_function A (zeta_seq A y n) : ℝ) / (counting_function A (zeta_seq A y n / 4) : ℝ)) Filter.atTop (nhds 1) := by
        simpa using h_ratio_zeta_one.inv₀;
      rw [ Metric.tendsto_nhds ] at *;
      intro ε hε; filter_upwards [ h_squeeze ε hε, ‹∀ᶠ n in Filter.atTop, _› ] with n hn hn'; exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp hn, hn'.1, hn'.2 ], by linarith [ abs_lt.mp hn, hn'.1, hn'.2 ] ⟩ ;

/-
If the set X is unbounded, then A(x)/A(x/2) tends to 1.
-/
noncomputable def beta (B : Set ℕ) (x : ℝ) : ℝ :=
  (counting_function B (x / 2) : ℝ) / (counting_function B x : ℝ)

theorem lemma_limit_A_ratio_one_of_unbounded (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z) :
    Filter.Tendsto (fun x : ℝ => (counting_function A x : ℝ) / counting_function A (x / 2)) Filter.atTop (nhds 1) := by
      sorry
/-
If 1 is a cluster point of alpha(x), then X is unbounded.
-/
theorem lemma_X_unbounded_of_cluster_one (A : Set ℕ)
    (h_cluster : MapClusterPt 1 Filter.atTop (fun x => alpha A x)) :
    ∀ y, ∃ z ∈ close_to_one_set A, z ≥ y := by
      sorry
/-
If 1 is a cluster point of alpha(x), then alpha(x) converges to 1.
-/
theorem lemma_limit_one_of_cluster_one (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (h_cluster : MapClusterPt 1 Filter.atTop (fun x => alpha A x)) :
    Filter.Tendsto (fun x => alpha A x) Filter.atTop (nhds 1) := by
      -- Since 1 is a cluster point of alpha(x), by lemma_X_unbounded_of_cluster_one, the set X is unbounded. Therefore, we can apply lemma_limit_A_ratio_one_of_unbounded.
      have h_unbounded : ∀ z, ∃ w ∈ close_to_one_set A, w ≥ z := by
        exact fun z => lemma_X_unbounded_of_cluster_one A h_cluster z;
      convert Filter.Tendsto.inv₀ ( lemma_limit_A_ratio_one_of_unbounded A B h_inf_A h_hyp h_r h_unbounded ) _ using 1 <;> norm_num [ alpha ]

/-
The product alpha(x) * beta(x) tends to 1/2.
-/
theorem lemma_alpha_beta_product (A B : Set ℕ)
    (h_hyp : exact_complements A B) :
    Filter.Tendsto (fun x => alpha A x * beta B x) Filter.atTop (nhds (1 / 2)) := by
      obtain ⟨ h₁, h₂ ⟩ := h_hyp;
      -- We need to show that $\frac{A(x/2)B(x/2)}{x}$ tends to $\frac{1}{2}$.
      have h_lim : Filter.Tendsto (fun x : ℝ => ((counting_function A (x / 2)) * (counting_function B (x / 2)) : ℝ) / x) Filter.atTop (nhds (1 / 2)) := by
        convert h₂.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < ( 1 / 2 : ℝ ) by norm_num ) ) |> Filter.Tendsto.div_const <| 2 using 2 ; norm_num ; ring_nf;
      have := h_lim.div h₂; norm_num at *;
      refine this.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx ; unfold alpha beta ; norm_num [ hx.ne', div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;

/-
alpha(x) is bounded between 0 and 1 eventually.
-/
theorem lemma_alpha_bounded (A : Set ℕ) : ∀ᶠ x in Filter.atTop, 0 ≤ alpha A x ∧ alpha A x ≤ 1 := by
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx
  have h_nonneg : 0 ≤ alpha A x := by
    exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ )
  have h_le_one : alpha A x ≤ 1 := by
    refine div_le_one_of_le₀ ?_ ?_ <;> norm_num [ alpha ];
    -- Apply the monotonicity of the counting function.
    apply lemma_counting_function_mono; exact div_le_self hx.le (by norm_num)
  exact ⟨h_nonneg, h_le_one⟩

/-
The sum of representation counts equals the product of the counting functions.
-/
theorem lemma_sum_representation_count (A B : Set ℕ) (x : ℝ) :
    ∑ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), representation_count A B x l = counting_function A x * counting_function B x := by
      by_contra h_neq;
      have h_sum_eq : ∑ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 + p.2 = l} = Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x} := by
        have h_sum_eq : ∑ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 + p.2 = l} = Nat.card (⋃ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≤ x ∧ p.2 ≤ x ∧ p.1 + p.2 = l}) := by
          have h_sum_eq : ∀ {S : Finset ℕ} {f : ℕ → Set (ℕ × ℕ)}, (∀ l ∈ S, Set.Finite (f l)) → (∀ l₁ l₂, l₁ ∈ S → l₂ ∈ S → l₁ ≠ l₂ → Disjoint (f l₁) (f l₂)) → ∑ l ∈ S, Nat.card (f l) = Nat.card (⋃ l ∈ S, f l) := by
            intros S f hf_finite hf_disjoint; induction S using Finset.induction with
            | empty => aesop
            | insert l S hl ih =>
            simp_all +decide [Finset.sum_insert hl];
            rw [ @Set.ncard_union_eq ];
            · simp_all +decide [ Set.disjoint_left ];
              exact fun a b ha x hx => hf_disjoint l x ( Or.inl rfl ) ( Or.inr hx ) ( by aesop ) a b ha;
            · exact hf_finite.1;
            · exact Set.Finite.biUnion ( Finset.finite_toSet S ) hf_finite.2;
          apply h_sum_eq;
          · exact fun l hl => Set.finite_iff_bddAbove.mpr ⟨ ⟨ ⌊x⌋₊, ⌊x⌋₊ ⟩, by rintro ⟨ a, b ⟩ ⟨ ha, hb, ha', hb', hab ⟩ ; exact ⟨ Nat.le_floor <| mod_cast ha', Nat.le_floor <| mod_cast hb' ⟩ ⟩;
          · exact fun l₁ l₂ hl₁ hl₂ hne => Set.disjoint_left.mpr fun p hp₁ hp₂ => hne <| by linarith [ hp₁.2.2.2.2, hp₂.2.2.2.2 ] ;
        convert h_sum_eq using 3;
        ext ⟨a, b⟩; simp [Finset.mem_range];
        intro ha hb ha' hb'
        have hsum_le : ((a + b : ℕ) : ℝ) ≤ 2 * x := by
          rw [Nat.cast_add]
          linarith
        exact Nat.le_floor hsum_le
      refine h_neq <| h_sum_eq.trans ?_;
      unfold counting_function;
      rw [ ← Nat.card_prod ];
      fapply Nat.card_congr; exact ⟨fun p => ⟨⟨p.val.1, p.prop.1, p.prop.2.2.1⟩, ⟨p.val.2, p.prop.2.1, p.prop.2.2.2⟩⟩, fun p => ⟨⟨p.1.val, p.2.val⟩, p.1.prop.1, p.2.prop.1, p.1.prop.2, p.2.prop.2⟩, fun p => rfl, fun p => rfl⟩;

/-
A(x)B(x) is the sum of F(x) and the small sum.
-/
theorem lemma_decomposition (A B : Set ℕ) (x : ℝ) :
    counting_function A x * counting_function B x = large_sum_count A B x + ∑ l ∈ Finset.range (⌊x⌋.toNat + 1), representation_count A B x l := by
      have h_split : ∑ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), representation_count A B x l = ∑ l ∈ Finset.range (⌊x⌋.toNat + 1), representation_count A B x l + ∑ l ∈ Finset.Ioc (⌊x⌋.toNat) (⌊2 * x⌋.toNat), representation_count A B x l := by
        rw [← Finset.sum_range_add_sum_Ico _]
        focus
          have h_Ico : Finset.Ico (⌊x⌋.toNat + 1) (⌊2 * x⌋.toNat + 1) = Finset.Ioc ⌊x⌋.toNat ⌊2 * x⌋.toNat := by
            ext n
            simp only [Finset.mem_Ico, Finset.mem_Ioc]
            omega
        focus
          rw [h_Ico]
        by_cases hx : x < 0
        · norm_num [Int.toNat_of_nonpos (Int.floor_nonpos hx.le), Int.toNat_of_nonpos (Int.floor_nonpos (mul_nonpos_of_nonneg_of_nonpos zero_le_two hx.le))]
        · simp +zetaDelta at *
          exact Or.inl (Int.floor_mono <| by linarith)
      rw [add_comm, ← lemma_sum_representation_count, h_split]
      rfl

/-
If l <= x is in A+B, then its representation count is at least 1.
-/
theorem lemma_representation_count_pos (A B : Set ℕ) (x : ℝ) (l : ℕ)
    (hl : l ≤ x) (h_mem : l ∈ A + B) :
    representation_count A B x l ≥ 1 := by
      refine Nat.card_pos_iff.mpr ?_;
      refine ⟨ ?_, Set.Finite.to_subtype ?_ ⟩;
      · rcases h_mem with ⟨ a, ha, b, hb, rfl ⟩ ; exact ⟨ ⟨ a, b ⟩, ha, hb, by exact_mod_cast le_trans ( Nat.cast_le.mpr <| Nat.le_add_right _ _ ) hl, by exact_mod_cast le_trans ( Nat.cast_le.mpr <| Nat.le_add_left _ _ ) hl, rfl ⟩;
      · exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ l, l ⟩, by rintro ⟨ a, b ⟩ ⟨ ha, hb, ha', hb', hab ⟩ ; exact ⟨ by linarith, by linarith ⟩ ⟩

/-
For x >= 0, the number of elements in A+B up to x is floor(x) + 1 - r(x).
-/
theorem lemma_card_A_plus_B_inter_le_x (A B : Set ℕ) (x : ℝ) (hx : x ≥ 0) :
    Nat.card {n : ℕ | n ≤ x ∧ n ∈ A + B} = ⌊x⌋.toNat + 1 - missing_sum_count A B x := by
      rw [ tsub_eq_of_eq_add_rev ];
      -- The set of natural numbers n ≤ x is the disjoint union of those in A+B and those not in A+B.
      have h_union : {n : ℕ | (n : ℝ) ≤ x ∧ n ∈ A + B} ∪ {n : ℕ | (n : ℝ) ≤ x ∧ n∉A + B} = {n : ℕ | n ≤ ⌊x⌋.toNat} := by
        ext n; by_cases hn : n ∈ A + B <;> simp_all +decide [ Int.le_floor ] ;
      -- Since these two sets are disjoint and their union is {n | n ≤ ⌊x⌋.toNat}, we can apply the cardinality addition formula.
      have h_card_add : Nat.card {n : ℕ | n ≤ ⌊x⌋.toNat} = Nat.card {n : ℕ | (n : ℝ) ≤ x ∧ n ∈ A + B} + Nat.card {n : ℕ | (n : ℝ) ≤ x ∧ n∉A + B} := by
        rw [ ← h_union, Nat.card_congr ( Equiv.Set.union <| _ ) ];
        · apply_rules [ Nat.card_sum ];
          · exact Set.Finite.to_subtype <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋.toNat, fun n hn => h_union.subset ( Or.inl hn ) ⟩;
          · exact Set.Finite.to_subtype <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋.toNat, fun n hn => h_union.subset ( Or.inr hn ) ⟩;
        · exact Set.disjoint_left.mpr fun n hn hn' => hn'.2 hn.2;
      convert h_card_add using 1 <;> norm_num [ Set.Iic_def ] ; ring_nf;
      rw [ add_comm ] ; rfl;

/-
exact_complements is symmetric.
-/
theorem lemma_exact_complements_symm (A B : Set ℕ) (h : exact_complements A B) : exact_complements B A := by
  obtain ⟨ h₁, h₂ ⟩ := h;
  constructor;
  · rw [ is_additive_complement ] at *;
    simpa only [ add_comm, Set.diff_eq ] using h₁;
  · simpa only [ mul_comm ] using h₂

/-
Narkiewicz's dichotomy: either A(2x)/A(x) -> 1 and B(2x)/B(x) -> 2, or vice versa.
-/
theorem narkiewicz_dichotomy (A B : Set ℕ) (h_inf_A : A.Infinite) (h_inf_B : B.Infinite)
    (h_hyp : exact_complements A B)
    (h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0)) :
    (Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1) ∧
     Filter.Tendsto (fun x => (counting_function B (2 * x) : ℝ) / counting_function B x) Filter.atTop (nhds 2)) ∨
    (Filter.Tendsto (fun x => (counting_function B (2 * x) : ℝ) / counting_function B x) Filter.atTop (nhds 1) ∧
     Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 2)) := by
       sorry
/-
Definitions of sigma(n) and delta(n) for finite sets U, V.
-/
def sigma_count (U V : Finset ℤ) (n : ℤ) : ℕ :=
  ((U ×ˢ V).filter (fun p => p.1 + p.2 = n)).card

def delta_count (U V : Finset ℤ) (n : ℤ) : ℕ :=
  ((U ×ˢ V).filter (fun p => p.2 - p.1 = n)).card

/-
Lemma deltaszigma: sum_{sigma>1} (sigma-1) >= 1/|U| sum_{delta>1} (delta-1).
-/
theorem lemma_deltaszigma (U V : Finset ℤ) :
    let S := (U ×ˢ V).image (fun p => p.1 + p.2)
    let D := (U ×ˢ V).image (fun p => p.2 - p.1)
    (∑ n ∈ S, if sigma_count U V n > 1 then sigma_count U V n - 1 else 0) * U.card ≥
    ∑ n ∈ D, if delta_count U V n > 1 then delta_count U V n - 1 else 0 := by
      -- We have sum sigma(n)^2 = sum delta(n)^2 by double counting u+v=u'+v' <=> v-u'=v'-u.
      have h_double_count : ∑ n ∈ Finset.image (fun p => p.1 + p.2) (U ×ˢ V), (sigma_count U V n)^2 = ∑ n ∈ Finset.image (fun p => p.2 - p.1) (U ×ˢ V), (delta_count U V n)^2 := by
        -- By definition of sigma_count and delta_count, we can rewrite the sums.
        have h_sigma_delta : ∑ n ∈ Finset.image (fun p => p.1 + p.2) (U ×ˢ V), (sigma_count U V n)^2 = ∑ p ∈ U ×ˢ V, ∑ q ∈ U ×ˢ V, if p.1 + p.2 = q.1 + q.2 then 1 else 0 := by
          rw [ Finset.sum_image' ];
          simp +decide [ sigma_count ];
          intro a b ha hb; rw [ sq ] ; rw [ Finset.sum_congr rfl fun x hx => by aesop ] ; simp +decide [Finset.sum_const] ;
          exact Or.inl ( congr_arg Finset.card ( Finset.filter_congr fun x hx => by rw [ eq_comm ] ) );
        have h_delta_sigma : ∑ n ∈ Finset.image (fun p => p.2 - p.1) (U ×ˢ V), (delta_count U V n)^2 = ∑ p ∈ U ×ˢ V, ∑ q ∈ U ×ˢ V, if p.2 - p.1 = q.2 - q.1 then 1 else 0 := by
          rw [ Finset.sum_image' ];
          simp +decide [ delta_count ];
          intro a b ha hb; rw [ sq ] ; rw [ Finset.sum_congr rfl fun x hx => by aesop ] ; simp +decide ;
          exact Or.inl ( congr_arg Finset.card ( Finset.filter_congr fun x hx => by rw [ eq_comm ] ) )
        -- By definition of delta_count, we can rewrite the sum of squares of delta counts.
        rw [h_sigma_delta, h_delta_sigma];
        rw [ Finset.sum_sigma', Finset.sum_sigma' ];
        apply Finset.sum_bij (fun x _ => ⟨⟨x.fst.1, x.snd.2⟩, ⟨x.snd.1, x.fst.2⟩⟩);
        · aesop;
        · aesop;
        · aesop;
        · grind +ring;
      -- We have sum_{delta(n)>1} (delta(n)-1) <= sum (delta(n)^2 - delta(n)) = sum (sigma(n)^2 - sigma(n)) <= |U| sum_{sigma(n)>1} (sigma(n)-1).
      have h_sum_bound : ∑ n ∈ Finset.image (fun p => p.2 - p.1) (U ×ˢ V), (if 1 < delta_count U V n then delta_count U V n - 1 else 0) ≤ ∑ n ∈ Finset.image (fun p => p.1 + p.2) (U ×ˢ V), (sigma_count U V n ^ 2 - sigma_count U V n) := by
        have h_sum_bound : ∑ n ∈ Finset.image (fun p => p.2 - p.1) (U ×ˢ V), (delta_count U V n - 1) ≤ ∑ n ∈ Finset.image (fun p => p.1 + p.2) (U ×ˢ V), (sigma_count U V n ^ 2 - sigma_count U V n) := by
          have h_sum_bound : ∑ n ∈ Finset.image (fun p => p.2 - p.1) (U ×ˢ V), (delta_count U V n ^ 2 - delta_count U V n) = ∑ n ∈ Finset.image (fun p => p.1 + p.2) (U ×ˢ V), (sigma_count U V n ^ 2 - sigma_count U V n) := by
            have h_sum_bound : ∑ n ∈ Finset.image (fun p => p.2 - p.1) (U ×ˢ V), delta_count U V n = ∑ n ∈ Finset.image (fun p => p.1 + p.2) (U ×ˢ V), sigma_count U V n := by
              rw [ Finset.sum_image', Finset.sum_image' ];
              focus
                use fun _ => 1
              · unfold sigma_count; aesop;
              · unfold delta_count; aesop;
            zify at *;
            rw [ Finset.sum_congr rfl fun x hx => Nat.cast_sub <| Nat.le_self_pow ( by norm_num ) _, Finset.sum_congr rfl fun x hx => Nat.cast_sub <| Nat.le_self_pow ( by norm_num ) _ ] ; aesop;
          refine h_sum_bound ▸ Finset.sum_le_sum fun x hx => ?_;
          exact Nat.le_sub_of_add_le ( by nlinarith only [ Nat.sub_add_cancel ( show 1 ≤ delta_count U V x from Finset.card_pos.mpr ⟨ Classical.choose ( Finset.mem_image.mp hx ), Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ Finset.mem_product.mp ( Classical.choose_spec ( Finset.mem_image.mp hx ) |>.1 ) |>.1, Finset.mem_product.mp ( Classical.choose_spec ( Finset.mem_image.mp hx ) |>.1 ) |>.2 ⟩, by linarith [ Classical.choose_spec ( Finset.mem_image.mp hx ) |>.2 ] ⟩ ⟩ ) ] );
        exact le_trans ( Finset.sum_le_sum fun x hx => by split_ifs <;> omega ) h_sum_bound;
      -- Since $\sigma(n) \leq |U|$ for all $n$, we have $\sigma(n)^2 - \sigma(n) \leq |U|(\sigma(n) - 1)$ for all $n$.
      have h_sigma_bound : ∀ n ∈ Finset.image (fun p => p.1 + p.2) (U ×ˢ V), sigma_count U V n ^ 2 - sigma_count U V n ≤ U.card * (if 1 < sigma_count U V n then sigma_count U V n - 1 else 0) := by
        intro n hn
        have h_sigma_le_card : sigma_count U V n ≤ U.card := by
          refine le_trans
            ( Finset.card_le_card ( t := Finset.image ( fun x => ( x, n - x ) ) U ) ?_ ) ?_;
          · grind;
          · exact Finset.card_image_le;
        split_ifs <;> norm_num at *;
        · nlinarith only [ h_sigma_le_card, ‹1 < sigma_count U V n›, Nat.sub_add_cancel ( by linarith : 1 ≤ sigma_count U V n ) ];
        · interval_cases sigma_count U V n <;> trivial;
      exact h_sum_bound.trans ( by simpa only [ mul_comm, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum h_sigma_bound )

/-
If A(2x)/A(x) -> 1, then A(2^k x)/A(x) -> 1 for all integer k.
-/
theorem lemma_limit_powers_of_two (A : Set ℕ)
    (h_double : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1)) :
    ∀ k : ℤ, Filter.Tendsto (fun x => (counting_function A (2 ^ k * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1) := by
      -- For $k > 0$, we use induction on $k$.
      have h_pos : ∀ k : ℕ, Filter.Tendsto (fun x => ((counting_function A (2 ^ k * x)) : ℝ) / (counting_function A x)) Filter.atTop (nhds 1) := by
        intro k
        induction k with
        | zero =>
          refine tendsto_const_nhds.congr' ?_;
          filter_upwards [ h_double.eventually_ne one_ne_zero ] with x hx using by aesop;
        | succ k ih =>
          have h_succ : Filter.Tendsto (fun x => ((counting_function A (2 * (2 ^ k * x)) : ℝ) / (counting_function A (2 ^ k * x))) * ((counting_function A (2 ^ k * x) : ℝ) / (counting_function A x))) Filter.atTop (nhds 1) := by
            simpa using Filter.Tendsto.mul ( h_double.comp ( Filter.tendsto_id.const_mul_atTop ( by positivity ) ) ) ih;
          refine h_succ.congr' ( by filter_upwards [ ih.eventually_ne one_ne_zero ] with x hx using by rw [ div_mul_div_cancel₀ ( by aesop ) ] ; ring_nf );
      intro k
      by_cases hk : k ≥ 0;
      · cases k <;> aesop;
      · -- For $k < 0$, we can write $k = -m$ for some $m > 0$.
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -m := by
          exact ⟨ Int.toNat ( -k ), by rw [ Int.toNat_of_nonneg ( by linarith ) ] ; ring ⟩;
        -- By substituting $y = 2^{-m} x$, we can rewrite the limit expression.
        suffices h_subst : Filter.Tendsto (fun y => ((counting_function A y) : ℝ) / (counting_function A (2 ^ m * y))) Filter.atTop (nhds 1) by
          convert h_subst.comp ( show Filter.Tendsto ( fun x : ℝ => 2 ^ ( -m : ℤ ) * x ) Filter.atTop Filter.atTop from Filter.tendsto_id.const_mul_atTop ( by positivity ) ) using 2 ; norm_num [ mul_comm ];
        simpa using Filter.Tendsto.inv₀ ( h_pos m ) ( by norm_num )

/-
If A(2x)/A(x) -> 1, then A(cx)/A(x) -> 1 for any c > 0.
-/
theorem lemma_limit_general_c (A : Set ℕ)
    (h_double : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1))
    (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun x => (counting_function A (c * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1) := by
      -- By the properties of logarithms and powers, we can find integers $k$ such that $2^k \leq c \leq 2^{k+1}$.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (2 : ℝ) ^ k ≤ c ∧ c ≤ (2 : ℝ) ^ (k + 1) := by
        have := Int.floor_le ( Real.logb 2 c ) ; ( have := Int.lt_floor_add_one ( Real.logb 2 c ) ; ( rw [ Real.le_logb_iff_rpow_le, Real.logb_lt_iff_lt_rpow ] at * <;> norm_cast at * ; ) );
        exact ⟨ _, ‹_›, le_of_lt ‹_› ⟩;
      -- Using the bounds, we can show that the ratio is squeezed between two sequences that both converge to 1.
      have h_squeeze : Filter.Tendsto (fun x => (counting_function A ((2 : ℝ) ^ k * x) : ℝ) / (counting_function A x)) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun x => (counting_function A ((2 : ℝ) ^ (k + 1) * x) : ℝ) / (counting_function A x)) Filter.atTop (nhds 1) := by
        have := lemma_limit_powers_of_two A h_double; aesop;
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_squeeze.1 h_squeeze.2 ?_ ?_;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx;
        gcongr;
        apply_rules [ Nat.card_mono ];
        · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊c * x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
        · exact fun n hn => ⟨ hn.1, by nlinarith [ hn.2 ] ⟩;
      · refine Filter.eventually_atTop.mpr ⟨ 1, fun x hx => ?_ ⟩;
        gcongr;
        apply_rules [ Nat.card_mono ];
        · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊2 ^ ( k + 1 ) * x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
        · exact fun n hn => ⟨ hn.1, hn.2.trans ( mul_le_mul_of_nonneg_right hk.2 ( by positivity ) ) ⟩

/-
Definition of the sum of elements of A up to x.
-/
noncomputable def sum_elements (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1)), (a : ℝ)

/-
Bound for sum_elements A x.
-/
theorem lemma_sum_bound (A : Set ℕ) (x : ℝ) (ε : ℝ) (hx : x ≥ 0) (hε : ε > 0) :
    sum_elements A x ≤ ε * x * counting_function A (ε * x) + x * (counting_function A x - counting_function A (ε * x)) := by
      by_cases h₂ : ε * x < x <;> simp_all +decide [mul_assoc];
      · -- Split the sum into two parts: $a \leq \epsilon x$ and $\epsilon x < a \leq x$.
        have h_split : sum_elements A x = ∑ a ∈ Finset.filter (fun n => n ∈ A) (Finset.range (Nat.floor (ε * x) + 1)), (a : ℝ) + ∑ a ∈ Finset.filter (fun n => n ∈ A) (Finset.Ico (Nat.floor (ε * x) + 1) (Nat.floor x + 1)), (a : ℝ) := by
          rw [ ← Finset.sum_union ];
          · rw [ ← Finset.filter_union, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico ] <;> norm_num [ Nat.floor_mono, hx, hε.le, h₂.le ]
            focus
              ring_nf
            · unfold sum_elements; simp +decide [ add_comm ] ;
              congr! 2;
            · exact Nat.floor_mono h₂.le;
          · exact Finset.disjoint_left.mpr fun n hn₁ hn₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hn₁ |>.1 ), Finset.mem_Ico.mp ( Finset.mem_filter.mp hn₂ |>.1 ) ] ;
        -- Apply the bounds to each part of the sum.
        have h_bounds : (∑ a ∈ Finset.filter (fun n => n ∈ A) (Finset.range (Nat.floor (ε * x) + 1)), (a : ℝ)) ≤ (ε * x) * (counting_function A (ε * x)) ∧ (∑ a ∈ Finset.filter (fun n => n ∈ A) (Finset.Ico (Nat.floor (ε * x) + 1) (Nat.floor x + 1)), (a : ℝ)) ≤ x * (counting_function A x - counting_function A (ε * x)) := by
          constructor;
          · refine le_trans ( Finset.sum_le_sum fun i hi => Nat.floor_le ( mul_nonneg hε.le hx ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp <| Finset.mem_filter.mp hi |>.1 ) ) ?_ ; norm_num [ mul_comm, counting_function ];
            rw [ ← Nat.card_eq_finsetCard ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Nat.floor_le, hx, hε.le ];
            gcongr;
            apply_rules [ Nat.card_mono ];
            · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x * ε⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
            · exact fun n hn => ⟨ hn.2, le_trans ( Nat.cast_le.mpr hn.1 ) ( Nat.floor_le ( by positivity ) ) ⟩;
          · refine le_trans ( Finset.sum_le_sum fun i hi => Nat.floor_le hx |> le_trans ( Nat.cast_le.mpr <| Finset.mem_Ico.mp ( Finset.mem_filter.mp hi |>.1 ) |>.2 |> Nat.lt_succ_iff.mp ) ) ?_ ; norm_num [ mul_comm ];
            rw [ show counting_function A x = Finset.card ( Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x⌋₊ + 1 ) ) ) from ?_, show counting_function A ( x * ε ) = Finset.card ( Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x * ε⌋₊ + 1 ) ) ) from ?_ ];
            · rw [ show ( Finset.filter ( fun n => n ∈ A ) ( Finset.Ico ( ⌊x * ε⌋₊ + 1 ) ( ⌊x⌋₊ + 1 ) ) ) = Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x⌋₊ + 1 ) ) \ Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x * ε⌋₊ + 1 ) ) from ?_, Finset.card_sdiff ];
              · rw [ Nat.cast_sub ] <;> norm_num [ Finset.inter_comm ];
                · rw [ show ( Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x⌋₊ + 1 ) ) ∩ Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x * ε⌋₊ + 1 ) ) ) = Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x * ε⌋₊ + 1 ) ) from Finset.inter_eq_right.mpr <| Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ <| Nat.floor_mono <| by nlinarith ];
                · exact Finset.card_mono fun x hx => by aesop;
              · ext; aesop;
            · convert Nat.card_eq_finsetCard ( Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x * ε⌋₊ + 1 ) ) ) using 1;
              rw [ ← Nat.card_congr ]
              focus
                aesop
              exact ⟨ fun n => ⟨ n, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_floor ( by simpa using n.2.2 ) ) ), n.2.1 ⟩ ⟩, fun n => ⟨ n, Finset.mem_filter.mp n.2 |>.2, by simpa using Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp n.2 |>.1 ) ) ) ⟩, fun n => rfl, fun n => rfl ⟩;
            · convert Nat.card_eq_finsetCard ( Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x⌋₊ + 1 ) ) ) using 1;
              rw [ ← Nat.card_congr ]
              focus
                aesop
              exact ⟨ fun n => ⟨ n, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_floor ( mod_cast n.2.2 ) ) ), n.2.1 ⟩ ⟩, fun n => ⟨ n, n.2 |> Finset.mem_filter.mp |>.2, mod_cast Nat.floor_le hx |> le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp <| Finset.mem_filter.mp n.2 |>.1 ) ⟩, fun n => rfl, fun n => rfl ⟩;
        linarith;
      · -- Since $x \leq \epsilon x$, we have $\sum_{a \in A, a \leq x} a \leq x \cdot \text{card}(A(x))$.
        have h_sum_le : sum_elements A x ≤ x * (counting_function A x : ℝ) := by
          have h_sum_le : sum_elements A x ≤ ∑ a ∈ Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1)), x := by
            exact Finset.sum_le_sum fun a ha => by linarith [ show ( a : ℝ ) ≤ x by exact le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp <| Finset.mem_filter.mp ha |>.1 ) <| Nat.floor_le hx ] ;
          convert h_sum_le using 1 ; norm_num [ mul_comm, counting_function ];
          rw [ ← Nat.card_eq_finsetCard ] ; norm_num [ and_comm ];
          refine Or.inl ( congr_arg _ ( congr_arg _ ( Set.ext fun n => ⟨ fun hn => ⟨ Nat.le_floor hn.2, hn.1 ⟩, fun hn => ⟨ hn.2, Nat.floor_le hx |> le_trans ( mod_cast hn.1 ) ⟩ ⟩ ) ) );
        nlinarith [ show ( counting_function A ( ε * x ) : ℝ ) ≥ counting_function A x from mod_cast by
                      apply_rules [ Set.ncard_le_ncard ];
                      · exact fun n hn => ⟨ hn.1, hn.2.trans h₂ ⟩;
                      · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊ε * x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ]

/-
sum_{a in A, a <= x} a = o(x A(x)).
-/
theorem lemma_aatlag_sum (A : Set ℕ) (h_smallbig_A : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun x => sum_elements A x / (x * counting_function A x)) Filter.atTop (nhds 0) := by
      sorry
/-
Definition of a*(x) = max {a in A, a <= x}.
-/
noncomputable def a_star (A : Set ℕ) (x : ℝ) : ℕ :=
  if _h : (A ∩ {n | n ≤ x}).Nonempty then sSup (A ∩ {n | n ≤ x}) else 0

/-
Identity: A(x)B(x) = excess + large + small.
-/
noncomputable def excess_count (A B : Set ℕ) (x : ℝ) : ℕ :=
  ∑ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), (representation_count A B x l - 1)

noncomputable def large_element_count (A B : Set ℕ) (x : ℝ) : ℕ :=
  Nat.card {n : ℕ | (n : ℝ) > x ∧ representation_count A B x n > 0}

theorem lemma_identity (A B : Set ℕ) (x : ℝ) (hx : x ≥ 0) :
    counting_function A x * counting_function B x = excess_count A B x + large_element_count A B x + (⌊x⌋.toNat + 1 - missing_sum_count A B x) := by
      rw [ ← lemma_card_A_plus_B_inter_le_x A B x hx ];
      unfold excess_count large_element_count;
      rw [ show Nat.card { n : ℕ | ( n : ℝ ) > x ∧ representation_count A B x n > 0 } = ∑ l ∈ Finset.Ioc ( ⌊x⌋.toNat ) ( ⌊2 * x⌋.toNat ), ( if representation_count A B x l > 0 then 1 else 0 ) from ?_, show Nat.card { n : ℕ | ( n : ℝ ) ≤ x ∧ n ∈ A + B } = ∑ l ∈ Finset.range ( ⌊x⌋.toNat + 1 ), ( if representation_count A B x l > 0 then 1 else 0 ) from ?_ ];
      · have h_split_sum : ∑ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), (representation_count A B x l - 1) + ∑ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), (if representation_count A B x l > 0 then 1 else 0) = ∑ l ∈ Finset.range (⌊2 * x⌋.toNat + 1), representation_count A B x l := by
          rw [ ← Finset.sum_add_distrib ] ; congr ; ext l ; cases h : representation_count A B x l <;> aesop;
        convert h_split_sum.symm using 1;
        · convert lemma_decomposition A B x |> Eq.symm using 1;
          · convert lemma_decomposition A B x using 1;
          · convert lemma_sum_representation_count A B x using 1;
        · rw [ add_assoc, ← Finset.sum_union ];
          · rw [ show ( Finset.Ioc ⌊x⌋.toNat ⌊2 * x⌋.toNat ∪ Finset.range ( ⌊x⌋.toNat + 1 ) ) = Finset.range ( ⌊2 * x⌋.toNat + 1 ) from ?_ ];
            ext l
            simp [Finset.mem_union, Finset.mem_Ioc, Finset.mem_range];
            have hmono : ⌊x⌋.toNat ≤ ⌊2 * x⌋.toNat :=
              Int.toNat_le_toNat (show ⌊x⌋ ≤ ⌊2 * x⌋ by gcongr; linarith)
            exact ⟨
              fun h => by
                rcases h with h | h
                · exact h.2
                · exact le_trans h hmono,
              fun h => by
                by_cases h' : l ≤ ⌊x⌋.toNat
                · exact Or.inr h'
                · exact Or.inl ⟨Nat.lt_of_not_ge h', h⟩ ⟩;
          · exact Finset.disjoint_left.mpr fun y hy₁ hy₂ => by linarith [ Finset.mem_Ioc.mp hy₁, Finset.mem_range.mp hy₂ ] ;
      · rw [ show { n : ℕ | ( n : ℝ ) ≤ x ∧ n ∈ A + B } = Finset.filter ( fun n => representation_count A B x n > 0 ) ( Finset.range ( ⌊x⌋.toNat + 1 ) ) from ?_, Nat.card_eq_fintype_card ]
        focus
          aesop
        ext n;
        -- If $n$ is in the set $\{n | n \leq x \land n \in A + B\}$, then $n$ is a natural number, $n \leq x$, and there exist $a \in A$ and $b \in B$ such that $a + b = n$. Since $n \leq x$, $n$ must be in the range up to $\lfloor x \rfloor + 1$. Also, the representation count for $n$ should be at least 1 because there's at least one pair $(a, b)$ that sums to $n$. So, the representation count is positive.
        apply Iff.intro
        · intro hn
          have h_range : n ≤ ⌊x⌋.toNat := by
            exact Nat.le_floor <| hn.1
          have h_rep : representation_count A B x n > 0 := by
            exact lemma_representation_count_pos A B x n hn.1 hn.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by linarith), h_rep⟩
        · intro hn
          have h_le : (n : ℝ) ≤ x := by
            exact le_trans
              (Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp <| Finset.mem_filter.mp hn |>.1)
              (Nat.floor_le hx)
          have h_in_sum : n ∈ A + B := by
            simp +zetaDelta at *
            obtain ⟨ p, hp ⟩ := Nat.card_pos_iff.mp hn.2
            obtain ⟨ p, hp ⟩ := p
            exact ⟨p.1, hp.1, p.2, hp.2.1, by linarith [hp.2.2.2.2]⟩
          exact ⟨h_le, h_in_sum⟩
      · rw [ show { n : ℕ | ( n : ℝ ) > x ∧ representation_count A B x n > 0 } = Finset.filter ( fun n => representation_count A B x n > 0 ) ( Finset.Ioc ⌊x⌋.toNat ⌊2 * x⌋.toNat ) from ?_, Nat.card_eq_fintype_card ]
        focus
          aesop
        ext n;
        simp +zetaDelta at *;
        intro hn_pos
        constructor
        · intro hn_gt_x
          have hn_le_2x : n ≤ ⌊2 * x⌋.toNat := by
            contrapose! hn_pos
            unfold representation_count
            rw [ Nat.card_eq_zero.mpr ]
            left
            constructor
            rintro ⟨ p, hp ⟩
            linarith [
              hp.2.2.1,
              hp.2.2.2.1,
              show ( p.1 : ℝ ) + p.2 = n by exact_mod_cast hp.2.2.2.2,
              show ( ⌊2 * x⌋.toNat : ℝ ) + 1 ≤ n by exact_mod_cast hn_pos,
              Int.lt_floor_add_one ( 2 * x ),
              show ( ⌊2 * x⌋.toNat : ℝ ) = ⌊2 * x⌋ from
                mod_cast Int.toNat_of_nonneg <| Int.floor_nonneg.mpr <| by positivity
            ]
          exact
            ⟨by
              exact Nat.lt_of_not_ge fun h =>
                hn_gt_x.not_ge <| Nat.floor_le hx |> le_trans ( mod_cast h ),
              hn_le_2x⟩
        · intro hn_bounds
          have hn_gt_x : x < n := by
            exact Nat.lt_of_floor_lt hn_bounds.1
          exact hn_gt_x

/-
large_element_count >= B(x) - B(x - a*(x)).
-/
theorem lemma_large_element_lower_bound (A B : Set ℕ) (x : ℝ) :
    large_element_count A B x ≥ counting_function B x - counting_function B (x - a_star A x) := by
      by_contra h_contra;
      -- Let $t = a^*(x)$.
      set t := a_star A x with ht_def;
      -- Consider the set $S = \{b \in B \mid x - t < b \leq x\}$.
      set S := {b ∈ B | x - t < b ∧ b ≤ x} with hS_def;
      have hS_card : S.ncard = counting_function B x - counting_function B (x - t) := by
        rw [ show S = { n ∈ B | ( n : ℝ ) ≤ x } \ { n ∈ B | ( n : ℝ ) ≤ x - t } from ?_, @Set.ncard_diff ];
        · rfl;
        · exact fun n hn => ⟨ hn.1, hn.2.trans ( sub_le_self _ <| Nat.cast_nonneg _ ) ⟩;
        · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊x - t⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
        · ext; aesop;
      -- For each $b \in S$, let $n = t + b$.
      have h_n_in_large : ∀ b ∈ S, t + b ∈ {n : ℕ | (n : ℝ) > x ∧ representation_count A B x n > 0} := by
        intro b hb
        have h_t_in_A : t ∈ A ∧ t ≤ x := by
          by_cases h : ( A ∩ { n | n ≤ x } ).Nonempty <;> simp_all +decide [ a_star ];
          have := Nat.sSup_mem h;
          exact ⟨ this ( by exact ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ) |>.1, this ( by exact ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ) |>.2 ⟩;
        refine ⟨ ?_, ?_ ⟩ <;> norm_num at *;
        · linarith [ hb.2.1 ];
        · refine Nat.card_pos_iff.mpr ?_;
          exact ⟨ ⟨ ⟨ t, b ⟩, h_t_in_A.1, hb.1, h_t_in_A.2, hb.2.2, rfl ⟩, Set.Finite.to_subtype <| Set.finite_iff_bddAbove.mpr ⟨ ⟨ ⌊x⌋₊, ⌊x⌋₊ ⟩, by rintro ⟨ a, b ⟩ ⟨ ha, hb, ha', hb', hab ⟩ ; exact ⟨ Nat.le_floor <| by linarith, Nat.le_floor <| by linarith ⟩ ⟩ ⟩;
      -- The map $b \mapsto t + b$ is injective.
      have h_injective : Set.InjOn (fun b => t + b) S := by
        aesop_cat;
      have h_image_card : (Set.image (fun b => t + b) S).ncard ≤ large_element_count A B x := by
        apply_rules [ Set.ncard_le_ncard ];
        · exact Set.image_subset_iff.mpr h_n_in_large;
        · refine Set.finite_iff_bddAbove.mpr ⟨ ⌊2 * x⌋.toNat, fun n hn => ?_ ⟩;
          -- Since $n$ is in the image of the function $(a, b) \mapsto a + b$ where $a \in A$ and $b \in B$, and both $a$ and $b$ are $\leq x$, we have $n \leq 2x$.
          have h_n_le_2x : n ≤ 2 * x := by
            obtain ⟨ p, hp ⟩ := Nat.card_pos_iff.mp hn.2;
            obtain ⟨ p, hp ⟩ := p; linarith [ hp.2.2.1, hp.2.2.2.1, show ( p.1 : ℝ ) + p.2 = n by exact_mod_cast hp.2.2.2.2 ] ;
          exact Nat.le_floor <| mod_cast h_n_le_2x;
      rw [ Set.InjOn.ncard_image h_injective ] at h_image_card ; linarith

/-
If t = a*(x) < x/2, then A(a+t) = A(x) for all a in A <= x.
-/
theorem lemma_A_at_plus_t_eq_A_x (A : Set ℕ) (x : ℝ) (t : ℕ)
    (ht : t = a_star A x) (ht_small : t < x / 2) :
    ∀ a ∈ Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1)), counting_function A (a + t) = counting_function A x := by
      intro a ha
      have ha_le : (a : ℝ) ≤ t := by
        simp +zetaDelta at *;
        rw [ ht, a_star ];
        split_ifs <;> simp_all +decide [ Set.Nonempty ];
        · refine le_csSup ?_ ?_;
          · exact ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| mod_cast hn.2 ⟩;
          · exact ⟨ ha.2, by exact le_trans ( Nat.cast_le.mpr ha.1 ) ( Nat.floor_le ( show 0 ≤ x by exact le_of_not_gt fun h => by { rw [ Int.toNat_of_nonpos ( Int.floor_nonpos h.le ) ] at ha; linarith } ) ) ⟩;
        · rename_i h; specialize h a ha.2; linarith [ show ( a : ℝ ) ≤ ⌊x⌋.toNat by exact_mod_cast ha.1, Int.floor_le x, Int.lt_floor_add_one x, show ( ⌊x⌋.toNat : ℝ ) ≤ ⌊x⌋ by exact_mod_cast Int.toNat_of_nonneg ( Int.floor_nonneg.mpr <| le_of_not_gt fun hx => by { have := h; norm_num at * ; linarith } ) |> le_of_eq ] ;
      -- Since $t \leq a + t < x$, the interval $(a + t, x]$ contains no elements of $A$.
      have h_no_elements : ∀ n ∈ A, (a : ℝ) + t < (n : ℝ) ∧ (n : ℝ) ≤ x → False := by
        intros n hn hn_bounds
        have hn_le_t : (n : ℝ) ≤ t := by
          unfold a_star at ht;
          split_ifs at ht <;> simp_all +decide [ Set.Nonempty ];
          · exact le_csSup ( by exact Set.Finite.bddAbove <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ) ⟨ hn, hn_bounds.2 ⟩;
          · grind
        linarith [hn_bounds.left, hn_bounds.right, hn_le_t];
      apply Set.ncard_congr;
      case f => exact fun n hn => n;
      · exact fun n hn => ⟨ hn.1, hn.2.trans ( by linarith ) ⟩;
      · aesop;
      · grind

/-
B(y) is bounded by (1+epsilon) y / A(y).
-/
theorem lemma_B_upper_bound (A B : Set ℕ) (h_hyp : exact_complements A B) :
    ∀ ε > 0, ∀ᶠ y in Filter.atTop, (counting_function B y : ℝ) ≤ (1 + ε) * y / counting_function A y := by
      -- By definition of $exact\_complements$, we know that $\lim_{x \to \infty} \frac{A(x)B(x)}{x} = 1$.
      have h_lim : Filter.Tendsto (fun x : ℝ => (counting_function A x * counting_function B x : ℝ) / x) Filter.atTop (nhds 1) := by
        exact h_hyp.2;
      intro ε hε_pos
      have h_bound : ∀ᶠ y in Filter.atTop, (counting_function A y * counting_function B y : ℝ) / y ≤ 1 + ε / 2 := by
        exact h_lim.eventually ( ge_mem_nhds <| by linarith );
      filter_upwards [ h_bound, Filter.eventually_gt_atTop 0, h_lim.eventually ( lt_mem_nhds one_pos ) ] with y hy₁ hy₂ hy₃;
      rw [ le_div_iff₀ ];
      · rw [ div_le_iff₀ ] at hy₁ <;> nlinarith;
      · contrapose! hy₃; aesop

/-
a*(x) tends to infinity.
-/
theorem lemma_a_star_tendsto_infinity (A : Set ℕ) (h_inf : A.Infinite) :
    Filter.Tendsto (a_star A) Filter.atTop Filter.atTop := by
      have := h_inf.exists_gt;
      refine Filter.tendsto_atTop_atTop.mpr ?_;
      intro b;
      -- Choose $i = a$ where $a$ is an element of $A$ such that $a > b$.
      obtain ⟨a, haA, ha_gt⟩ : ∃ a ∈ A, b < a := this b;
      use a;
      intro x hx;
      have ha_le_x : a ≤ x := by
        exact hx;
      exact (by
      unfold a_star;
      split_ifs <;> norm_num at *;
      · exact le_trans ( mod_cast ha_gt.le ) ( le_csSup ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ⟨ haA, ha_le_x ⟩ );
      · exact False.elim <| ‹¬ ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ).Nonempty› ⟨ a, haA, ha_le_x ⟩);

/-
sum_{a in A, a <= x} a = o(a*(x) A(x)).
-/
theorem lemma_sum_elements_a_star (A : Set ℕ) (h_inf_A : A.Infinite)
    (h_smallbig_A : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun x => sum_elements A x / (a_star A x * counting_function A x)) Filter.atTop (nhds 0) := by
      -- Let $t(x) = a_star A x$.
      set t := a_star A;
      -- Since $sum_elements A x = sum_elements A (t x)$ and $counting_function A x = counting_function A (t x)$, we can rewrite the limit expression.
      have h_rewrite : ∀ x ≥ 0, sum_elements A x = sum_elements A (t x) ∧ counting_function A x = counting_function A (t x) := by
        intro x hx_nonneg
        constructor;
        · apply Finset.sum_bij (fun a ha => a);
          · -- Since $t(x)$ is the supremum of $A \cap \{n \mid n \leq x\}$, any $a \in A$ with $a \leq x$ must satisfy $a \leq t(x)$.
            have h_le_t : ∀ a ∈ A, a ≤ x → a ≤ t x := by
              intro a ha hax
              simp [t, a_star];
              rw [ if_pos ⟨ a, ha, hax ⟩ ] ; exact le_csSup ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ⟨ ha, hax ⟩;
            simp +zetaDelta at *;
            exact fun a ha₁ ha₂ => ⟨ h_le_t a ha₂ ( le_trans ( Nat.cast_le.mpr ha₁ ) ( Nat.floor_le hx_nonneg ) ), ha₂ ⟩;
          · aesop;
          · simp +zetaDelta at *;
            intro b hb hbA
            have hb_le_x : b ≤ x := by
              contrapose! hb;
              unfold a_star;
              split_ifs;
              · refine Nat.succ_le_of_lt
                  ( lt_of_le_of_lt
                    ( b := ⌊x⌋₊ )
                    ( csSup_le
                      ( by assumption )
                      ( fun n hn => Nat.le_floor <| hn.2 ) )
                    ( Nat.floor_lt ( by positivity ) |>.2 hb ) )
              · exact Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hb; linarith )
            have hb_le_floor_x : b ≤ ⌊x⌋.toNat := by
              exact Nat.le_floor <| mod_cast hb_le_x
            exact ⟨by linarith, hbA⟩;
          · aesop;
        · unfold counting_function t;
          unfold a_star;
          split_ifs <;> simp_all +decide [ Set.Nonempty ];
          · congr with n;
            constructor <;> intro hn <;> refine ⟨ hn.1, ?_ ⟩;
            · exact le_csSup ⟨ ⌊x⌋₊, fun m hm => Nat.le_floor <| hm.2 ⟩ ⟨ hn.1, hn.2 ⟩;
            · contrapose! hn;
              intro hnA;
              refine lt_of_le_of_lt
                ( b := ⌊x⌋₊ )
                ( csSup_le
                  ( by
                    obtain ⟨ m, hm₁, hm₂ ⟩ := ‹∃ m ∈ A, ( m : ℝ ) ≤ x›
                    exact ⟨ m, hm₁, hm₂ ⟩ )
                  ( fun m hm => Nat.le_floor <| hm.2 ) )
                ( Nat.floor_lt ( by positivity ) |>.2 <| by linarith );
          · rw [ Nat.card_eq_zero.mpr, Nat.card_eq_zero.mpr ];
            · exact Or.inl ⟨ fun ⟨ n, hn₁, hn₂ ⟩ => by have := ‹∀ x_1 ∈ A, x < ( x_1 : ℝ ) › n hn₁; norm_num [ hn₂ ] at this; linarith ⟩;
            · exact Or.inl ⟨ fun n => by linarith [ n.2.2, ‹∀ x_1 ∈ A, x < ( x_1 : ℝ ) › n.1 n.2.1 ] ⟩;
      -- Using the fact that $t(x) \to \infty$ as $x \to \infty$, we can rewrite the limit expression.
      have h_tendsto : Filter.Tendsto (fun x => sum_elements A (t x) / ((t x : ℝ) * counting_function A (t x))) Filter.atTop (nhds 0) := by
        have h_tendsto : Filter.Tendsto (fun x => sum_elements A x / ((x : ℝ) * counting_function A x)) Filter.atTop (nhds 0) := by
          convert lemma_aatlag_sum A h_smallbig_A using 1;
        refine h_tendsto.comp ?_;
        exact tendsto_natCast_atTop_atTop.comp ( lemma_a_star_tendsto_infinity A h_inf_A );
      exact h_tendsto.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 0 ] with x hx; rw [ h_rewrite x hx |>.1, h_rewrite x hx |>.2 ] )

/-
Bound for B(a+t) when t < x/2.
-/
theorem lemma_B_at_plus_t_bound (A B : Set ℕ) (h_inf_A : Set.Infinite A)
    (h_hyp : exact_complements A B) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop,
      let t := a_star A x
      t < x / 2 →
      ∀ a ∈ Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1)),
        (counting_function B (a + t) : ℝ) ≤ (1 + ε) * (a + t) / counting_function A x := by
          intro ε hε_pos
          obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, ∀ y ≥ y₀, (counting_function B y : ℝ) ≤ (1 + ε) * y / (counting_function A y) := by
            have := lemma_B_upper_bound A B h_hyp ε hε_pos; aesop;
          -- By lemma_a_star_tendsto_infinity, for large x, a_star A x is large.
          obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, a_star A x ≥ y₀ := by
            have := lemma_a_star_tendsto_infinity A h_inf_A;
            exact Filter.eventually_atTop.mp ( this.eventually_ge_atTop ⌈y₀⌉₊ ) |> fun ⟨ x₀, hx₀ ⟩ => ⟨ x₀, fun x hx => le_trans ( Nat.le_ceil _ ) ( mod_cast hx₀ x hx ) ⟩;
          -- By lemma_A_at_plus_t_eq_A_x, for large x, counting_function A (a + t) = counting_function A x.
          have h_counting_function_eq : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, t = a_star A x → t < x / 2 → ∀ a ∈ Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1)), counting_function A (a + t) = counting_function A x := by
            filter_upwards [ Filter.eventually_gt_atTop x₀ ] with x hx;
            intros t ht ht_lt_half a ha
            apply lemma_A_at_plus_t_eq_A_x A x t ht ht_lt_half a ha;
          filter_upwards [ Filter.eventually_ge_atTop x₀, h_counting_function_eq ] with x hx₁ hx₂;
          intro t ht a ha; specialize hx₂ t rfl ht a ha; specialize hy₀ ( a + t ) ( by linarith [ hx₀ x hx₁ ] ) ; aesop;

/-
Sum of B(a+t) is bounded by (1+epsilon)t.
-/
theorem lemma_sum_B_bound (A B : Set ℕ) (h_inf_A : A.Infinite) (h_hyp : exact_complements A B)
    (h_smallbig_A : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1)) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop,
      let t := a_star A x
      t < x / 2 →
      ∑ a ∈ Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1)), (counting_function B (a + t) : ℝ) ≤ (1 + ε) * t := by
        sorry
/-
The number of pairs (u,v) with v-u <= t is bounded by the sum of B(u+t).
-/
theorem lemma_pairs_le_sum_B (B : Set ℕ) (t : ℕ)
    (U : Finset ℤ) (V' : Finset ℤ)
    (hV' : ∀ v ∈ V', ∃ b ∈ B, v = (b : ℤ)) :
    ((U ×ˢ V').filter (fun p => p.2 - p.1 ≤ (t : ℤ))).card ≤
    ∑ u ∈ U, counting_function B ((u : ℝ) + t) := by
      sorry
/-
The sum of delta counts for differences <= t equals the number of pairs with difference <= t.
-/
theorem lemma_sum_delta_eq_card_pairs (U V' : Finset ℤ) (t : ℤ) :
    ∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (if n ≤ t then delta_count U V' n else 0) =
    ((U ×ˢ V').filter (fun p => p.2 - p.1 ≤ t)).card := by
      unfold delta_count; simp +decide [ Finset.sum_ite ] ;
      rw [ ← Finset.card_biUnion ]
      focus
        congr
      focus
        ext
      focus
        aesop
      exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;

/-
The support of delta for n > t is contained in [t+1, floor(x-t)-1].
-/
theorem lemma_delta_support_bound (x : ℝ) (t : ℕ)
    (U : Finset ℤ) (V' : Finset ℤ)
    (hU : ∀ u ∈ U, 1 ≤ u)
    (hV' : ∀ v ∈ V', v ≤ ⌊x - t⌋) :
    ((U ×ˢ V').image (fun p => p.2 - p.1)).filter (fun n => n > (t : ℤ)) ⊆ Finset.Icc (t + 1 : ℤ) (⌊x - t⌋ - 1) := by
      -- To prove the subset relationship, take any $n$ in the set and show that $t + 1 \leq n \leq \lfloor x - t \rfloor - 1$.
      intro n hn
      obtain ⟨u, hu, v, hv, hn_eq⟩ : ∃ u ∈ U, ∃ v ∈ V', n = v - u := by
        aesop
      have h_lower : t + 1 ≤ n := by
        linarith [ Finset.mem_filter.mp hn ]
      have h_upper : n ≤ ⌊x - t⌋ - 1 := by
        linarith [ hU u hu, hV' v hv ]
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩

/-
The number of large differences is bounded by x - 2t.
-/
theorem lemma_large_diff_count_bound (x : ℝ) (t : ℕ)
    (U : Finset ℤ) (V' : Finset ℤ)
    (hU : ∀ u ∈ U, 1 ≤ u)
    (hV' : ∀ v ∈ V', v ≤ ⌊x - t⌋)
    (ht : t < x / 2) :
    (((U ×ˢ V').image (fun p => p.2 - p.1)).filter (fun n => n > (t : ℤ))).card ≤ x - 2 * t := by
      -- The set of large differences is a subset of [t+1, floor(x-t)-1].
      have h_subset : {n ∈ (U ×ˢ V').image (fun p => p.2 - p.1) | n > (t : ℤ)} ⊆ Finset.Icc (t + 1 : ℤ) (⌊x - t⌋ - 1) := by
        exact lemma_delta_support_bound x t U V' hU hV';
      refine le_trans ?_ ( le_trans ( sub_le_sub_right ( Int.floor_le ( x - t ) ) (t : ℝ) ) ( by ring_nf; exact le_rfl ) );
      refine le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_subset ) ?_ ; norm_num ; ring_nf ; norm_cast ; norm_num;
      exact ⟨ by decide, Int.le_floor.2 <| by norm_num; linarith ⟩

/-
The sum of delta counts equals the product of the cardinalities of U and V'.
-/
theorem lemma_sum_delta_eq_product_card (U V' : Finset ℤ) :
    ∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (delta_count U V' n : ℝ) = (U.card : ℝ) * (V'.card : ℝ) := by
      rw_mod_cast [ ← Finset.card_product ];
      rw [ Finset.card_eq_sum_ones, Finset.sum_image' ] ; aesop

/-
If A and B are exact complements and A(cx)/A(x) tends to 1, then B(cx)/B(x) tends to c.
-/
theorem lemma_limit_linear_B (A B : Set ℕ)
    (h_hyp : exact_complements A B)
    (h_limit_A : ∀ c > 0, Filter.Tendsto (fun x => (counting_function A (c * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1))
    (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun x => (counting_function B (c * x) : ℝ) / counting_function B x) Filter.atTop (nhds c) := by
      -- From \eqref{hyp} we have $A(x)B(x)/x \to 1$.
      have h_lim : Filter.Tendsto (fun x => ((counting_function A x) * (counting_function B x) : ℝ) / x) Filter.atTop (nhds 1) := by
        unfold exact_complements at h_hyp; aesop;
      -- Thus $B(cx)/B(x) = \frac{B(cx)A(cx)/(cx)}{B(x)A(x)/x} \cdot \frac{A(x)}{A(cx)} \cdot c$.
      have h_ratio : Filter.Tendsto (fun x => ((counting_function B (c * x) * counting_function A (c * x) : ℝ) / (c * x)) / ((counting_function B x * counting_function A x : ℝ) / x) * (counting_function A x / counting_function A (c * x)) * c) Filter.atTop (nhds c) := by
        convert Filter.Tendsto.mul ( Filter.Tendsto.mul ( Filter.Tendsto.div ( h_lim.comp ( Filter.tendsto_id.const_mul_atTop hc ) ) h_lim _ ) ( h_limit_A c hc |> Filter.Tendsto.inv₀ <| by positivity ) ) tendsto_const_nhds using 2 <;> norm_num [ mul_assoc, mul_comm, mul_left_comm, hc.ne' ];
        exacts [ Or.inl rfl, rfl ];
      refine h_ratio.congr' ?_;
      filter_upwards [ h_lim.eventually_ne one_ne_zero, h_limit_A c hc |> Filter.Tendsto.eventually_ne <| show ( 1 : ℝ ) ≠ 0 by norm_num ] with x hx₁ hx₂ ; by_cases hx₃ : x = 0 <;> simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
      norm_num [ hc.ne' ]

/-
The sum of (delta-1) is at least A(x)B(x-t) - x + (1-epsilon)t.
-/
theorem lemma_sum_delta_minus_one_bound (A B : Set ℕ) (x : ℝ) (t : ℕ) (ε : ℝ)
    (hx : x ≥ 0) (ht : t < x / 2) (ht_pos : t > 0)
    (h_pos_A : ∀ a ∈ A, a ≠ 0) (h_pos_B : ∀ b ∈ B, b ≠ 0)
    (h_small_diff : (((Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩ ×ˢ
                     (Finset.filter (fun n => n ∈ B) (Finset.range (⌊x - t⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩).filter (fun p => p.2 - p.1 ≤ (t : ℤ))).card ≤ (1 + ε) * t) :
    let U := (Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩
    let V' := (Finset.filter (fun n => n ∈ B) (Finset.range (⌊x - t⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩
    let D := (U ×ˢ V').image (fun p => p.2 - p.1)
    ∑ n ∈ D, (if delta_count U V' n > 1 then (delta_count U V' n : ℝ) - 1 else 0) ≥
    (counting_function A x * counting_function B (x - t) : ℝ) - x + (1 - ε) * t := by
      have h_large_diff : (((Finset.map { toFun := Int.ofNat, inj' := Int.ofNat_injective } ({n ∈ Finset.range (⌊x⌋.toNat + 1) | n ∈ A}) ×ˢ Finset.map { toFun := Int.ofNat, inj' := Int.ofNat_injective } ({n ∈ Finset.range (⌊x - ↑t⌋.toNat + 1) | n ∈ B})).image (fun p => p.2 - p.1)).filter (fun n => n > ↑t)).card ≤ x - 2 * t := by
                                                                                                                                                          apply_rules [ lemma_large_diff_count_bound ];
                                                                                                                                                          · simp +zetaDelta at *;
                                                                                                                                                            exact fun u n hn hn' hn'' => hn''.symm ▸ mod_cast Nat.pos_of_ne_zero ( h_pos_A n hn' );
                                                                                                                                                          · simp +zetaDelta at *;
                                                                                                                                                            grind;
      -- Let $S = |U||V'| = A(x)B(x-t)$.
      set U := (Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩
      set V' := (Finset.filter (fun n => n ∈ B) (Finset.range (⌊x - ↑t⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩
      set S := (U.card : ℝ) * (V'.card : ℝ);
      have h_sum_delta_sub_one : (∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (if delta_count U V' n > 1 then (delta_count U V' n : ℝ) - 1 else 0)) ≥ S - (1 + ε) * t - (x - 2 * t) := by
        have h_sum_delta_sub_one : (∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (if delta_count U V' n > 1 then (delta_count U V' n : ℝ) - 1 else 0)) ≥ (∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (delta_count U V' n : ℝ)) - (1 + ε) * t - (x - 2 * t) := by
          have h_sum_delta_sub_one : ∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (if delta_count U V' n > 1 then (delta_count U V' n : ℝ) - 1 else 0) ≥ ∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (delta_count U V' n : ℝ) - ∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (if n ≤ (t : ℤ) then (delta_count U V' n : ℝ) else 0) - ∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (if n > (t : ℤ) then (1 : ℝ) else 0) := by
            rw [ ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib ];
            refine Finset.sum_le_sum fun n hn => ?_;
            split_ifs <;> norm_num
            focus
              linarith [ show delta_count U V' n ≥ 0 from Nat.cast_nonneg _ ]
            · linarith;
            · linarith;
            · linarith;
          have h_sum_delta_sub_one : ∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (if n ≤ (t : ℤ) then (delta_count U V' n : ℝ) else 0) ≤ (1 + ε) * t := by
            convert h_small_diff using 1;
            convert lemma_sum_delta_eq_card_pairs U V' t using 1;
            norm_cast;
          have h_sum_delta_sub_one : ∑ n ∈ (U ×ˢ V').image (fun p => p.2 - p.1), (if n > (t : ℤ) then (1 : ℝ) else 0) ≤ x - 2 * t := by
            convert h_large_diff using 1 ; norm_num [ Finset.sum_ite ];
          linarith;
        refine le_trans ?_ h_sum_delta_sub_one;
        rw [ lemma_sum_delta_eq_product_card ];
      convert h_sum_delta_sub_one using 1
      focus
        ring_nf!
      rw [ Finset.card_map, Finset.card_map ] ; unfold counting_function ; ring_nf!;
      rw [ show { n : ℕ | n ∈ A ∧ ( n : ℝ ) ≤ x } = Finset.filter ( fun n => n ∈ A ) ( Finset.range ( 1 + ⌊x⌋.toNat ) ) from ?_, show { n : ℕ | n ∈ B ∧ ( n : ℝ ) ≤ x - t } = Finset.filter ( fun n => n ∈ B ) ( Finset.range ( 1 + ⌊x - t⌋.toNat ) ) from ?_ ] <;> norm_num [ add_comm, Nat.card_eq_fintype_card ]
      focus
        ring_nf!
      · rw [ ← Nat.card_eq_finsetCard, ← Nat.card_eq_finsetCard ] ; norm_num;
        have hAcard :
            Nat.card { x_1 : ℕ // x_1 ≤ ⌊x⌋.toNat ∧ x_1 ∈ A } =
              Nat.card { x_1 : ℕ // x_1 < 1 + ⌊x⌋.toNat ∧ x_1 ∈ A } := by
          refine Nat.card_congr ?_
          exact
            { toFun := fun n => ⟨ n.1, ⟨ by omega, n.2.2 ⟩ ⟩
              invFun := fun n => ⟨ n.1, ⟨ by omega, n.2.2 ⟩ ⟩
              left_inv := fun n => rfl
              right_inv := fun n => rfl }
        have hBcard :
            Nat.card { x_1 : ℕ // x_1 ≤ ⌊x⌋.toNat - t ∧ x_1 ∈ B } =
              Nat.card { x_1 : ℕ // x_1 < 1 + (⌊x⌋.toNat - t) ∧ x_1 ∈ B } := by
          refine Nat.card_congr ?_
          exact
            { toFun := fun n => ⟨ n.1, ⟨ by omega, n.2.2 ⟩ ⟩
              invFun := fun n => ⟨ n.1, ⟨ by omega, n.2.2 ⟩ ⟩
              left_inv := fun n => rfl
              right_inv := fun n => rfl }
        rw [hAcard, hBcard]
        ring
      · ext n; simp [Set.mem_setOf_eq];
        have ht_le_x : (t : ℝ) ≤ x := by linarith
        have ht_le_floor : t ≤ ⌊x⌋.toNat := Nat.le_floor ht_le_x
        constructor
        · intro h
          have hn_add_real : ((n + t : ℕ) : ℝ) ≤ x := by
            rw [Nat.cast_add]
            linarith [h.2]
          have hn_add : n + t ≤ ⌊x⌋.toNat := Nat.le_floor hn_add_real
          exact ⟨ (Nat.le_sub_iff_add_le ht_le_floor).2 hn_add, h.1 ⟩
        · intro h
          have hn_add : n + t ≤ ⌊x⌋.toNat := (Nat.le_sub_iff_add_le ht_le_floor).1 h.1
          have hn_add_real : ((n + t : ℕ) : ℝ) ≤ x :=
            le_trans (Nat.cast_le.mpr hn_add) (Nat.floor_le hx)
          have hn_real : (n : ℝ) + t ≤ x := by
            simpa [Nat.cast_add] using hn_add_real
          exact ⟨ h.2, by linarith ⟩
      · ext; simp [Set.mem_setOf_eq];
        exact ⟨ fun h => ⟨ Nat.le_floor <| mod_cast h.2, h.1 ⟩, fun h => ⟨ h.2, Nat.floor_le hx |> le_trans ( mod_cast h.1 ) ⟩ ⟩ ;

/-
The excess count is bounded below by B(x-t) - (x-(1-epsilon)t)/A(x).
-/
theorem lemma_y_lower_bound (A B : Set ℕ) (x : ℝ) (t : ℕ) (ε : ℝ)
    (hx : x ≥ 0) (ht : t < x / 2) (ht_pos : t > 0)
    (h_pos_A : ∀ a ∈ A, a ≠ 0) (h_pos_B : ∀ b ∈ B, b ≠ 0)
    (h_small_diff : (((Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩ ×ˢ
                     (Finset.filter (fun n => n ∈ B) (Finset.range (⌊x - t⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩).filter (fun p => p.2 - p.1 ≤ (t : ℤ))).card ≤ (1 + ε) * t)
    (h_A_pos : counting_function A x > 0) :
    (excess_count A B x : ℝ) ≥ counting_function B (x - t) - (x - (1 - ε) * t) / counting_function A x := by
      sorry
/-
B(x) is eventually at least (1-epsilon)x/A(x).
-/
theorem lemma_B_lower_bound (A B : Set ℕ) (h_hyp : exact_complements A B) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop, (counting_function B x : ℝ) ≥ (1 - ε) * x / counting_function A x := by
      have := lemma_B_upper_bound A B h_hyp;
      intro ε hε_pos
      obtain ⟨N, hN⟩ : ∃ N, ∀ x ≥ N, (counting_function A x : ℝ) * (counting_function B x : ℝ) / x ≥ 1 - ε / 2 := by
        have := h_hyp.2;
        exact Filter.eventually_atTop.mp ( this.eventually ( le_mem_nhds <| by linarith ) );
      have := this ( ε / 2 ) ( half_pos hε_pos ) ; filter_upwards [ this, Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ hx₃ ; by_cases hx₄ : counting_function A x = 0 <;> simp_all +decide [ division_def ] ;
      field_simp at *;
      have := hN x hx₂; rw [ div_add', le_div_iff₀ ] at this <;> nlinarith;

/-
The convergence of B(cx)/B(x) to c is uniform for c in [0, 1].
-/
theorem lemma_uniform_convergence_B (B : Set ℕ)
    (h_limit_B : ∀ c > 0, Filter.Tendsto (fun x => (counting_function B (c * x) : ℝ) / counting_function B x) Filter.atTop (nhds c)) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop, ∀ c ∈ Set.Icc 0 1, |(counting_function B (c * x) : ℝ) / counting_function B x - c| < ε := by
      intro ε hε_pos
      obtain ⟨k, hk⟩ : ∃ k : ℕ, k > 0 ∧ 1 / k < ε / 2 := by
        exact ⟨ ⌊ε⁻¹ * 2⌋₊ + 1, Nat.succ_pos _, by rw [ div_lt_iff₀ ] <;> push_cast <;> nlinarith [ Nat.lt_floor_add_one ( ε⁻¹ * 2 ), mul_inv_cancel₀ hε_pos.ne' ] ⟩;
      -- For each fixed $c$, $f_x(c) \to c$ as $x \to \infty$.
      have h_fixed_c : ∀ i ∈ Finset.range (k + 1), Filter.Tendsto (fun x => (counting_function B ((i : ℝ) / k * x) : ℝ) / counting_function B x) Filter.atTop (nhds ((i : ℝ) / k)) := by
        intro i hi; by_cases hi0 : i = 0 <;> simp_all +decide [ div_eq_mul_inv ] ;
        · -- Since $B$ is infinite, $counting_function B x$ tends to infinity as $x$ tends to infinity.
          have h_counting_B_inf : Filter.Tendsto (fun x => counting_function B x : ℝ → ℕ) Filter.atTop Filter.atTop := by
            apply counting_function_tendsto_atTop B (by
            contrapose! h_limit_B;
            -- Since $B$ is finite, there exists some $M$ such that for all $x \geq M$, $B(x) = B(M)$.
            obtain ⟨M, hM⟩ : ∃ M, ∀ x ≥ M, counting_function B x = counting_function B M := by
              have h_finite : B.Finite := by
                exact h_limit_B
              obtain ⟨M, hM⟩ : ∃ M, ∀ b ∈ B, b ≤ M := by
                exact h_finite.bddAbove
              use M
              intro x hx
              simp [counting_function];
              rw [ show { n : ℕ // n ∈ B ∧ ( n : ℝ ) ≤ x } = { n : ℕ // n ∈ B ∧ n ≤ M } from ?_ ];
              exact congr_arg _ ( by ext; exact ⟨ fun h => ⟨ h.1, hM _ h.1 ⟩, fun h => ⟨ h.1, le_trans ( mod_cast h.2 ) hx ⟩ ⟩ );
            refine ⟨ 2, by norm_num, ?_ ⟩ ; rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_ge_atTop M, Filter.eventually_ge_atTop ( M / 2 ) ] with x hx₁ hx₂ using by rw [ hM ( 2 * x ) ( by linarith ), hM x hx₁ ] ) ] ; norm_num [ hM ];
            by_cases h : counting_function B M = 0 <;> norm_num [ h ]);
          exact tendsto_const_nhds.div_atTop ( tendsto_natCast_atTop_atTop.comp h_counting_B_inf );
        · exact h_limit_B _ ( by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hi0 ) ) ( inv_pos.mpr ( Nat.cast_pos.mpr hk.1 ) ) );
      -- For large $x$, $|f_x(c_i) - c_i| < \epsilon/2$ for all $i$.
      obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ i ∈ Finset.range (k + 1), |(counting_function B ((i : ℝ) / k * x) : ℝ) / counting_function B x - (i : ℝ) / k| < ε / 2 := by
        choose! x₀ hx₀ using fun i hi => Metric.tendsto_atTop.mp ( h_fixed_c i hi ) ( ε / 2 ) ( half_pos hε_pos ) ; exact ⟨ Finset.max' ( Finset.image x₀ ( Finset.range ( k + 1 ) ) ) ⟨ x₀ 0, Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) ⟩, fun x hx i hi => hx₀ i hi x ( le_trans ( Finset.le_max' _ _ <| Finset.mem_image_of_mem _ hi ) hx ) ⟩ ;
      filter_upwards [ Filter.eventually_ge_atTop x₀, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ c hc;
      -- For any $c \in [c_i, c_{i+1}]$, $f_x(c_i) \le f_x(c) \le f_x(c_{i+1})$.
      obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range k, (i : ℝ) / k ≤ c ∧ c ≤ (i + 1 : ℝ) / k := by
        by_cases hc_eq : c = 1;
        · exact ⟨ k - 1, Finset.mem_range.mpr ( Nat.sub_lt hk.1 zero_lt_one ), by rw [ hc_eq, div_le_iff₀ ] <;> cases k <;> norm_num <;> linarith, by rw [ hc_eq, le_div_iff₀ ] <;> cases k <;> norm_num <;> linarith ⟩;
        · use Nat.floor (c * k);
          exact ⟨ Finset.mem_range.mpr <| Nat.floor_lt ( mul_nonneg hc.1 <| Nat.cast_nonneg _ ) |>.2 <| by nlinarith [ hc.1, hc.2, show ( k : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr hk.1, mul_div_cancel₀ 1 <| show ( k : ℝ ) ≠ 0 by exact Nat.cast_ne_zero.mpr hk.1.ne', lt_of_le_of_ne hc.2 hc_eq ], by rw [ div_le_iff₀ <| Nat.cast_pos.mpr hk.1 ] ; exact Nat.floor_le <| mul_nonneg hc.1 <| Nat.cast_nonneg _, by rw [ le_div_iff₀ <| Nat.cast_pos.mpr hk.1 ] ; exact Nat.lt_floor_add_one _ |> le_of_lt ⟩;
      -- Since $f_x$ is monotone, we have $f_x(c_i) \le f_x(c) \le f_x(c_{i+1})$.
      have h_monotone : (counting_function B ((i : ℝ) / k * x) : ℝ) / counting_function B x ≤ (counting_function B (c * x) : ℝ) / counting_function B x ∧ (counting_function B (c * x) : ℝ) / counting_function B x ≤ (counting_function B ((i + 1 : ℝ) / k * x) : ℝ) / counting_function B x := by
        constructor <;> gcongr;
        · apply_rules [ Set.ncard_le_ncard ];
          · exact fun n hn => ⟨ hn.1, mul_le_mul_of_nonneg_right hi.2.1 hx₂.le |> le_trans hn.2 ⟩;
          · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊c * x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
        · apply_rules [ Set.ncard_le_ncard ];
          · exact fun n hn => ⟨ hn.1, hn.2.trans ( mul_le_mul_of_nonneg_right hi.2.2 hx₂.le ) ⟩;
          · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊ ( i + 1 : ℝ ) / k * x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩;
      have := hx₀ x hx₁ i ( Finset.mem_range.mpr ( by linarith [ Finset.mem_range.mp hi.1 ] ) ) ; have := hx₀ x hx₁ ( i + 1 ) ( Finset.mem_range.mpr ( by linarith [ Finset.mem_range.mp hi.1 ] ) ) ; simp_all +decide [ abs_lt ] ;
      constructor <;> ring_nf at * <;> nlinarith [ inv_mul_cancel₀ ( by norm_cast; linarith : ( k : ℝ ) ≠ 0 ) ]

/-
If t >= x/2, then z >= (1-epsilon) t / A(x).
-/
theorem lemma_z_lower_bound_large_t (A B : Set ℕ) (_h_inf_B : B.Infinite)
    (h_hyp : exact_complements A B)
    (h_limit_B : ∀ c > 0, Filter.Tendsto (fun x => (counting_function B (c * x) : ℝ) / counting_function B x) Filter.atTop (nhds c)) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop,
      let t := a_star A x
      t ≥ x / 2 →
      (large_element_count A B x : ℝ) ≥ (1 - ε) * t / counting_function A x := by
        -- Let $c = (x - t) / x = 1 - t / x$. Since $t \ge x / 2$, $c \in [0, 1 / 2]$.
        intros ε hεpos
        obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, δ < ε / 3 ∧ δ < 1 / 3 := by
          exact ⟨ Min.min ( ε / 6 ) ( 1 / 6 ), by positivity, by linarith [ min_le_left ( ε / 6 ) ( 1 / 6 ) ], by linarith [ min_le_right ( ε / 6 ) ( 1 / 6 ) ] ⟩;
        -- By `lemma_uniform_convergence_B`, for any $\delta > 0$, eventually $|B(cx)/B(x) - c| < \delta$ for all $c \in [0, 1]$.
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ c ∈ Set.Icc 0 1, |(counting_function B (c * x) : ℝ) / (counting_function B x) - c| < δ := by
          have := @lemma_uniform_convergence_B B h_limit_B δ hδpos; aesop;
        -- By `lemma_B_lower_bound`, $B(x) \ge (1-\delta) x/A(x)$.
        obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, ∀ x ≥ x₁, (counting_function B x : ℝ) ≥ (1 - δ) * x / (counting_function A x) := by
          have := lemma_B_lower_bound A B h_hyp δ hδpos; aesop;
        -- Let $c = (x - t) / x = 1 - t / x$. Since $t \ge x / 2$, $c \in [0, 1 / 2]$. By `lemma_uniform_convergence_B`, for any $\delta > 0$, eventually $|B(cx)/B(x) - c| < \delta$ for all $c \in [0, 1]$.
        have h_bound : ∀ᶠ x in Filter.atTop, let t := a_star A x; t ≥ x / 2 → (counting_function B (x - t) : ℝ) ≤ (counting_function B x) * (1 - t / x + δ) := by
          filter_upwards [ Filter.eventually_gt_atTop x₀, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ hx₃ ; specialize hx₀ x hx₁.le ( 1 - a_star A x / x ) ⟨ ?_, ?_ ⟩ <;> norm_num at *;
          · rw [ div_le_iff₀ hx₂ ];
            unfold a_star;
            split_ifs <;> norm_num;
            · exact_mod_cast Set.mem_setOf.mp ( show ( sSup ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ) : ℕ ) ∈ A ∩ { n : ℕ | ( n : ℝ ) ≤ x } from by exact ( IsCompact.sSup_mem ( show IsCompact ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ) from Set.Finite.isCompact <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ) <| by aesop ) ) |>.2;
            · linarith;
          · positivity;
          · intro hx₄; rw [ abs_lt ] at hx₀; simp_all +decide [ ne_of_gt, sub_mul ] ;
            by_cases h : counting_function B x = 0;
            · have h_empty : IsEmpty { n : ℕ // n ∈ B ∧ ( n : ℝ ) ≤ x } := by
                have h_zero_or : IsEmpty { n : ℕ // n ∈ B ∧ ( n : ℝ ) ≤ x } ∨
                    Infinite { n : ℕ // n ∈ B ∧ ( n : ℝ ) ≤ x } := by
                  simpa [counting_function] using (Nat.card_eq_zero.mp h)
                rcases h_zero_or with h_empty | h_inf
                · exact h_empty
                · exact False.elim <| h_inf.not_finite <|
                    Set.Finite.to_subtype <|
                      Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩
              have h_sub_zero : counting_function B (x - hx₃) = 0 := by
                rw [counting_function]
                apply Nat.card_eq_zero.mpr
                exact Or.inl ⟨ fun n => h_empty.elim ⟨ n.1, n.2.1, by linarith [n.2.2] ⟩ ⟩
              simp [h, h_sub_zero, div_eq_mul_inv, mul_comm] at *;
            · simp_all +decide [ div_eq_mul_inv, mul_comm ];
              nlinarith [ inv_mul_cancel_left₀ ( show ( counting_function B x : ℝ ) ≠ 0 by positivity ) ( counting_function B ( x - hx₃ ) ), inv_mul_cancel₀ ( show ( counting_function B x : ℝ ) ≠ 0 by positivity ), inv_mul_cancel₀ ( show x ≠ 0 by positivity ) ];
        -- By `lemma_large_element_lower_bound`, $large_element_count A B x \ge B(x) - B(x-t)$.
        have h_large_element_bound : ∀ᶠ x in Filter.atTop, let t := a_star A x; t ≥ x / 2 → (large_element_count A B x : ℝ) ≥ (counting_function B x) - (counting_function B (x - t) : ℝ) := by
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx;
          have := lemma_large_element_lower_bound A B x;
          norm_num +zetaDelta at *;
          exact fun _ => mod_cast this;
        filter_upwards [ h_bound, h_large_element_bound, Filter.eventually_gt_atTop 0, Filter.eventually_ge_atTop x₀, Filter.eventually_ge_atTop x₁ ] with x hx₁ hx₂ hx₃ hx₄ hx₅;
        intro ht
        have h_bound : (counting_function B x : ℝ) ≥ (1 - δ) * x / (counting_function A x) := by
          grind;
        intro ht_ge_half
        have h_bound : (large_element_count A B x : ℝ) ≥ (counting_function B x) * (ht / x - δ) := by
          linarith [ hx₁ ht_ge_half, hx₂ ht_ge_half ];
        refine le_trans ?_ h_bound;
        refine le_trans ?_ ( mul_le_mul_of_nonneg_right ‹_› ?_ ) <;> ring_nf <;> norm_num [ hx₃.ne' ];
        · field_simp;
          gcongr ; nlinarith [ mul_le_mul_of_nonneg_left hδ.2.le hx₃.le ];
        · nlinarith [ mul_inv_cancel₀ hx₃.ne' ]

/-
If A and B are exact complements, then r(x) is bounded.
-/
theorem lemma_r_bounded (A B : Set ℕ) (h_hyp : exact_complements A B) :
    ∃ C, ∀ x, missing_sum_count A B x ≤ C := by
      sorry
/-
A(x)/a*(x) tends to 0.
-/
theorem lemma_A_div_a_star_tendsto_zero (A B : Set ℕ) (h_inf_A : A.Infinite) (h_inf_B : B.Infinite)
    (h_hyp : exact_complements A B) :
    Filter.Tendsto (fun x => (counting_function A x : ℝ) / a_star A x) Filter.atTop (nhds 0) := by
      have := @h_hyp;
      have h_tendsto_zero : Filter.Tendsto (fun x => (counting_function A x : ℝ) / x) Filter.atTop (nhds 0) := by
        -- Since $B(x)$ tends to infinity as $x$ tends to infinity, we have $1/B(x)$ tends to $0$.
        have h_B_inf : Filter.Tendsto (fun x => (counting_function B x : ℝ)) Filter.atTop Filter.atTop := by
          refine tendsto_natCast_atTop_atTop.comp ?_;
          exact counting_function_tendsto_atTop B h_inf_B;
        -- Since $A(x)B(x) \sim x$, we have $\frac{A(x)}{x} \sim \frac{1}{B(x)}$.
        have h_similar : Filter.Tendsto (fun x => (counting_function A x : ℝ) * (counting_function B x : ℝ) / x) Filter.atTop (nhds 1) := by
          have := this.2;
          convert this using 1;
        have := h_similar.div_atTop h_B_inf;
        refine this.congr' ( by
          filter_upwards [ h_B_inf.eventually_ne_atTop 0 ] with x hx
          field_simp [ hx ] );
      -- Since $A$ is infinite, $a^*(x) \to \infty$ as $x \to \infty$.
      have h_a_star_inf : Filter.Tendsto (fun x => (a_star A x : ℝ)) Filter.atTop Filter.atTop := by
        refine tendsto_natCast_atTop_atTop.comp ?_;
        exact lemma_a_star_tendsto_infinity A h_inf_A;
      have := h_tendsto_zero.comp h_a_star_inf;
      have h_eq : ∀ x : ℝ, x ≥ 0 → (counting_function A x : ℝ) ≤ (counting_function A (a_star A x) : ℝ) := by
        intros x hx_nonneg
        have h_subset : {n ∈ A | n ≤ x} ⊆ {n ∈ A | n ≤ a_star A x} := by
          intros n hn
          obtain ⟨hnA, hn_le⟩ := hn
          have hn_le_a_star : n ≤ a_star A x := by
            unfold a_star;
            split_ifs <;> [ exact le_csSup ( by exact Set.Finite.bddAbove <| Set.finite_iff_bddAbove.mpr ⟨ ⌊x⌋₊, fun y hy => Nat.le_floor <| hy.2 ⟩ ) ⟨ hnA, hn_le ⟩ ; exact False.elim <| ‹¬ ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ).Nonempty› ⟨ n, hnA, hn_le ⟩ ]
          exact ⟨hnA, hn_le_a_star⟩;
        refine mod_cast ?_;
        apply_rules [ Set.ncard_le_ncard ];
        · exact fun n hn => ⟨ hn.1, mod_cast h_subset hn |>.2 ⟩;
        · exact Set.finite_iff_bddAbove.mpr ⟨ a_star A x, fun n hn => mod_cast hn.2 ⟩;
      refine squeeze_zero_norm' ?_ this;
      filter_upwards [ Filter.eventually_ge_atTop 0 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( h_eq x hx ) ( Nat.cast_nonneg _ ) ;


/-
Inequality for small t.
-/
theorem lemma_estimate_inequality_small_t (A B : Set ℕ) (x : ℝ) (t : ℕ) (ε : ℝ)
    (h_excess : (excess_count A B x : ℝ) ≥ counting_function B (x - t) - (x - (1 - ε) * t) / counting_function A x)
    (h_large : large_element_count A B x ≥ counting_function B x - counting_function B (x - t))
    (h_identity : counting_function A x * counting_function B x = excess_count A B x + large_element_count A B x + (⌊x⌋.toNat + 1 - missing_sum_count A B x))
    (h_A_gt_1 : counting_function A x > 1) :
    (counting_function A x * counting_function B x : ℝ) - x ≥ ((1 - ε) * t - missing_sum_count A B x * counting_function A x) / (counting_function A x - 1) := by
      rw [ ge_iff_le, div_le_iff₀ ];
      · rw [ ← @Nat.cast_inj ℝ ] at * ; norm_num at *;
        rw [ Nat.cast_sub ] at *;
        · rw [ add_div', le_div_iff₀ ] at * <;> norm_num at * <;> try linarith;
          nlinarith [ show ( counting_function A x : ℝ ) ≥ 2 by norm_cast, show ( counting_function B x : ℝ ) ≤ large_element_count A B x + counting_function B ( x - t ) by exact_mod_cast h_large, Int.floor_le x, Int.lt_floor_add_one x, show ( Int.toNat ⌊x⌋ : ℝ ) ≥ ⌊x⌋ by exact_mod_cast Int.self_le_toNat _ ];
        · refine le_trans ( Set.ncard_le_ncard <| show { n : ℕ | n ≤ x ∧ n∉A + B } ⊆ Finset.Icc 0 ( ⌊x⌋.toNat ) from fun n hn => Finset.mem_Icc.mpr ⟨ Nat.zero_le n, Nat.le_floor <| mod_cast hn.1 ⟩ ) ?_ ; norm_num [ Set.ncard_eq_toFinset_card' ];
      · exact sub_pos_of_lt ( mod_cast h_A_gt_1 )

/-
Inequality for large t.
-/
theorem lemma_estimate_inequality_large_t (A B : Set ℕ) (x : ℝ) (t : ℕ) (ε : ℝ)
    (h_large : (large_element_count A B x : ℝ) ≥ (1 - ε) * t / counting_function A x)
    (h_identity : counting_function A x * counting_function B x = excess_count A B x + large_element_count A B x + (⌊x⌋.toNat + 1 - missing_sum_count A B x)) :
    (counting_function A x * counting_function B x : ℝ) - x ≥ (1 - ε) * t / counting_function A x - missing_sum_count A B x := by
      refine le_trans ( sub_le_sub_right h_large _ ) ?_;
      norm_cast;
      rw [ Int.subNatNat_eq_coe ] ; norm_num [ h_identity ];
      rw [ Nat.cast_sub ] <;> norm_num;
      · linarith [ show ( ⌊x⌋.toNat : ℝ ) ≥ ⌊x⌋ by exact_mod_cast Int.self_le_toNat _, Int.floor_le x, Int.lt_floor_add_one x ];
      · exact le_trans ( Set.ncard_le_ncard ( show { n : ℕ | n ≤ x ∧ n∉A + B } ⊆ Finset.Icc 0 ( ⌊x⌋.toNat ) from fun n hn => Finset.mem_Icc.mpr ⟨ Nat.zero_le _, Nat.le_floor <| mod_cast hn.1 ⟩ ) ) ( by norm_num [ Set.ncard_eq_toFinset_card' ] )

/-
a*(x)/A(x) tends to infinity.
-/
theorem lemma_t_div_A_tendsto_atTop (A B : Set ℕ) (h_inf_A : A.Infinite) (h_inf_B : B.Infinite)
    (h_hyp : exact_complements A B) :
    Filter.Tendsto (fun x => (a_star A x : ℝ) / counting_function A x) Filter.atTop Filter.atTop := by
      convert Filter.Tendsto.inv_tendsto_nhdsGT_zero _ using 1;
      rotate_left;
      all_goals try infer_instance;
      focus
        exact fun x => ( a_star A x : ℝ ) ⁻¹ * counting_function A x
      · rw [ tendsto_nhdsWithin_iff ];
        field_simp;
        refine ⟨ ?_, ?_ ⟩;
        · convert lemma_A_div_a_star_tendsto_zero A B h_inf_A h_inf_B h_hyp using 1;
        · -- Since $A$ is infinite, there exists some $x$ such that for all $n \geq x$, $A(n) > 0$ and $a^*(n) > 0$.
          obtain ⟨x, hx⟩ : ∃ x, ∀ n ≥ x, 0 < counting_function A n ∧ 0 < a_star A n := by
            have h_pos : ∃ x, ∀ n ≥ x, 0 < counting_function A n := by
              have h_pos : Filter.Tendsto (fun x => counting_function A x) Filter.atTop Filter.atTop := by
                exact counting_function_tendsto_atTop A h_inf_A;
              exact Filter.eventually_atTop.mp ( h_pos.eventually_gt_atTop 0 );
            have h_pos_a_star : Filter.Tendsto (a_star A) Filter.atTop Filter.atTop := by
              exact lemma_a_star_tendsto_infinity A h_inf_A;
            exact Filter.eventually_atTop.mp ( h_pos_a_star.eventually_gt_atTop 0 ) |> fun ⟨ x, hx ⟩ => ⟨ Max.max h_pos.choose x, fun n hn => ⟨ h_pos.choose_spec n ( le_trans ( le_max_left _ _ ) hn ), hx n ( le_trans ( le_max_right _ _ ) hn ) ⟩ ⟩;
          filter_upwards [ Filter.eventually_ge_atTop x ] with n hn using div_pos ( Nat.cast_pos.mpr ( hx n hn |>.1 ) ) ( Nat.cast_pos.mpr ( hx n hn |>.2 ) ) |> fun h => by simpa using h;
      · ext; simp +decide [ div_eq_mul_inv ] ;
        ring

/-
r(x)A(x)/a*(x) tends to 0.
-/
theorem lemma_r_mul_A_div_t_tendsto_zero (A B : Set ℕ) (h_inf_A : A.Infinite) (h_inf_B : B.Infinite)
    (h_hyp : exact_complements A B) :
    Filter.Tendsto (fun x => (missing_sum_count A B x : ℝ) * counting_function A x / a_star A x) Filter.atTop (nhds 0) := by
      obtain ⟨ C, hC ⟩ := lemma_r_bounded A B h_hyp;
      -- We know $A(x)/a^*(x) \to 0$ as $x \to \infty$.
      have h_A_div_a_star_tendsto_zero : Filter.Tendsto (fun x => (counting_function A x : ℝ) / a_star A x) Filter.atTop (nhds 0) := by
        convert lemma_A_div_a_star_tendsto_zero A B h_inf_A h_inf_B h_hyp using 1;
      norm_num [ mul_div_assoc ];
      exact squeeze_zero ( fun x => by positivity ) ( fun x => mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( hC x ) ) ( by positivity ) ) ( by simpa using h_A_div_a_star_tendsto_zero.const_mul _ )

/-
B(cx)/B(x) tends to c.
-/
theorem lemma_limit_B_general_c (A B : Set ℕ)
    (h_hyp : exact_complements A B)
    (h_smallbig_A : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1)) :
    ∀ c > 0, Filter.Tendsto (fun x => (counting_function B (c * x) : ℝ) / counting_function B x) Filter.atTop (nhds c) := by
      apply_rules [ lemma_limit_linear_B ];
      exact fun c a => lemma_limit_general_c A h_smallbig_A c a

/-
Case 2 of the estimate theorem: t >= x/2.
-/
theorem lemma_estimate_case2_apply_large_t (A B : Set ℕ) (h_inf_A : A.Infinite) (h_inf_B : B.Infinite)
    (h_hyp : exact_complements A B)
    (h_smallbig_A : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1)) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop,
      let t := a_star A x
      t ≥ x / 2 →
      (counting_function A x * counting_function B x : ℝ) - x ≥ (1 - ε) * t / counting_function A x := by
        intro ε hε_pos
        have h_large : ∀ ε' > 0, ∀ᶠ x in Filter.atTop, let t := a_star A x; t ≥ x / 2 → (large_element_count A B x : ℝ) ≥ (1 - ε') * t / counting_function A x := by
          intro ε' hε'_pos
          apply_rules [lemma_z_lower_bound_large_t];
          exact fun c a => lemma_limit_B_general_c A B h_hyp h_smallbig_A c a;
        have h_estimate : ∀ ε' > 0, ∀ᶠ x in Filter.atTop, let t := a_star A x; t ≥ x / 2 → (counting_function A x * counting_function B x : ℝ) - x ≥ (1 - ε') * t / counting_function A x - missing_sum_count A B x := by
          intro ε' hε'_pos
          obtain ⟨x₀, hx₀⟩ : ∃ x₀, ∀ x ≥ x₀, let t := a_star A x; t ≥ x / 2 → (large_element_count A B x : ℝ) ≥ (1 - ε') * t / counting_function A x := by
            exact Filter.eventually_atTop.mp ( h_large ε' hε'_pos ) |> fun ⟨ x₀, hx₀ ⟩ => ⟨ x₀, fun x hx => hx₀ x hx ⟩;
          filter_upwards [ Filter.eventually_ge_atTop x₀, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ hx₃;
          intro hx₄;
          have := lemma_identity A B x hx₂.le;
          exact lemma_estimate_inequality_large_t A B x hx₃ ε' (hx₀ x hx₁ hx₄) this;
        -- Choose ε' so that ε' < ε and the term (ε - ε') * t / A(x) is large enough to cover the missing_sum_count A B x.
        obtain ⟨ε', hε'_pos, hε'_lt⟩ : ∃ ε' > 0, ε' < ε ∧ ∀ᶠ x in Filter.atTop, (missing_sum_count A B x : ℝ) ≤ (ε - ε') * (a_star A x : ℝ) / counting_function A x := by
          obtain ⟨C, hC⟩ : ∃ C, ∀ x, missing_sum_count A B x ≤ C := by
            apply lemma_r_bounded A B h_hyp;
          -- Choose ε' such that (ε - ε') * t / A(x) is large enough to cover the missing_sum_count A B x.
          obtain ⟨ε', hε'_pos, hε'_lt⟩ : ∃ ε' > 0, ε' < ε ∧ ∀ᶠ x in Filter.atTop, (ε - ε') * (a_star A x : ℝ) / counting_function A x ≥ C := by
            have h_t_div_A_tendsto_atTop : Filter.Tendsto (fun x => (a_star A x : ℝ) / counting_function A x) Filter.atTop Filter.atTop := by
              convert lemma_t_div_A_tendsto_atTop A B h_inf_A h_inf_B h_hyp using 1;
            have := h_t_div_A_tendsto_atTop.eventually_gt_atTop ( C / ( ε / 2 ) );
            refine ⟨ ε / 2, half_pos hε_pos, half_lt_self hε_pos, ?_ ⟩ ; filter_upwards [ this ] with x hx ; ring_nf at hx ⊢ ; nlinarith [ mul_inv_cancel₀ ( ne_of_gt hε_pos ) ] ;
          exact ⟨ ε', hε'_pos, hε'_lt.1, hε'_lt.2.mono fun x hx => le_trans ( mod_cast hC x ) hx ⟩;
        filter_upwards [ h_estimate ε' hε'_pos, hε'_lt.2 ] with x hx₁ hx₂ using fun hx₃ => by convert le_trans _ ( hx₁ hx₃ ) using 1 ; ring_nf at *; linarith [ hx₂ ] ;

/-
Lemma: If t < x/2, then A(x)B(x) - x >= ((1 - ε)t - r(x)A(x)) / (A(x) - 1) eventually.
-/
theorem lemma_estimate_lower_bound_small_t (A B : Set ℕ) (h_inf_A : A.Infinite)
(h_hyp : exact_complements A B) (h_pos_A : ∀ a ∈ A, a ≠ 0) (h_pos_B : ∀ b ∈ B, b ≠ 0)
    (h_smallbig_A : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1)) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop,
      let t := a_star A x
      t < x / 2 →
      (counting_function A x * counting_function B x : ℝ) - x ≥ ((1 - ε) * t - missing_sum_count A B x * counting_function A x) / (counting_function A x - 1) := by
        intro ε hε_pos
        obtain ⟨h_eventually, h_counting⟩ : (∀ᶠ x in Filter.atTop,
            ((let t := a_star A x
              t < x / 2 →
              let U := (Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩
              let V' := (Finset.filter (fun n => n ∈ B) (Finset.range (⌊x - t⌋.toNat + 1))).map ⟨Int.ofNat, Int.ofNat_injective⟩
              ((U ×ˢ V').filter (fun p => p.2 - p.1 ≤ (t : ℤ))).card ≤ (1 + ε) * t))) ∧ (∀ᶠ x in Filter.atTop, (counting_function A x > 1)) := by
                constructor
                · -- Apply the lemma that gives the upper bound on the number of pairs (u, v) in U × V' such that v - u ≤ t.
                  have h_upper_bound : ∀ᶠ x in Filter.atTop, let t := a_star A x; t < x / 2 → (∑ u ∈ Finset.filter (fun n => n ∈ A) (Finset.range (⌊x⌋.toNat + 1)), (counting_function B (u + t) : ℝ)) ≤ (1 + ε / 2) * t := by
                    convert lemma_sum_B_bound A B h_inf_A h_hyp ( show Filter.Tendsto ( fun x : ℝ => ( counting_function A ( 2 * x ) : ℝ ) / counting_function A x ) Filter.atTop ( nhds 1 ) from h_smallbig_A ) ( ε / 2 ) ( half_pos hε_pos ) using 1
                  filter_upwards [ h_upper_bound ] with x hx hx'
                  refine fun hx'' => le_trans ?_ ( le_trans ( hx hx'' ) ?_ )
                  · convert lemma_pairs_le_sum_B B hx' _ _ _ using 1
                    rotate_left
                    focus
                      exact Finset.filter ( fun n => n ∈ A ) ( Finset.range ( ⌊x⌋.toNat + 1 ) ) |> Finset.map ⟨ Int.ofNat, Int.ofNat_injective ⟩
                    focus
                      exact Finset.map ⟨ Int.ofNat, Int.ofNat_injective ⟩ ( Finset.filter ( fun n => n ∈ B ) ( Finset.range ( ⌊x - hx'⌋.toNat + 1 ) ) )
                    · aesop
                    · norm_cast
                      rw [ Finset.sum_map ]
                      aesop
                  · exact mul_le_mul_of_nonneg_right ( by linarith ) ( Nat.cast_nonneg _ )
                · have h_eventually : Filter.Tendsto (fun x => counting_function A x) Filter.atTop Filter.atTop := by
                    exact counting_function_tendsto_atTop A h_inf_A
                  exact h_eventually.eventually_gt_atTop 1
        filter_upwards [ h_eventually, h_counting, Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop 2 ] with x hx₁ hx₂ hx₃ hx₄;
        intros t ht_lt_x_div_2
        have h_excess : (excess_count A B x : ℝ) ≥ counting_function B (x - t) - (x - (1 - ε) * t) / counting_function A x := by
          convert lemma_y_lower_bound A B x t ε ( by linarith ) ht_lt_x_div_2 ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| ?_ ) h_pos_A h_pos_B ( hx₁ ht_lt_x_div_2 ) ( Nat.cast_pos.mpr <| Nat.zero_lt_of_lt hx₂ ) using 1 ; norm_num [ Nat.cast_add, Nat.cast_one ] ; ring_nf!;
          cases Classical.propDecidable ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ).Nonempty <;> simp_all +decide;
          · exact ‹¬ ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ).Nonempty› ⟨ Classical.choose ( show ∃ a ∈ A, a ≤ x from by
                                                                                        contrapose! hx₂; simp_all +decide [ counting_function ] ;
                                                                                        rw [ Nat.card_eq_zero.mpr ] <;> norm_num;
                                                                                        exact Or.inl ⟨ fun ⟨ n, hn₁, hn₂ ⟩ => by linarith [ hx₂ n hn₁ ] ⟩ ), Classical.choose_spec ( show ∃ a ∈ A, a ≤ x from by
                                                                                                                                                    contrapose! hx₂; simp_all +decide [ counting_function ] ;
                                                                                                                                                    rw [ Nat.card_eq_zero.mpr ] <;> norm_num;
                                                                                                                                                    exact Or.inl ⟨ fun ⟨ n, hn₁, hn₂ ⟩ => by linarith [ hx₂ n hn₁ ] ⟩ ) |>.1, by exact_mod_cast Classical.choose_spec ( show ∃ a ∈ A, a ≤ x from by
                                                                                                                                                                                                                                        contrapose! hx₂; simp_all +decide [ counting_function ] ;
                                                                                                                                                                                                                                        rw [ Nat.card_eq_zero.mpr ] <;> norm_num;
                                                                                                                                                                                                                                        exact Or.inl ⟨ fun ⟨ n, hn₁, hn₂ ⟩ => by linarith [ hx₂ n hn₁ ] ⟩ ) |>.2 ⟩;
          · exact ne_of_gt <| lt_of_lt_of_le ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| h_pos_A _ <| Classical.choose_spec ‹ ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ).Nonempty › |>.1 ) <| le_csSup ( show BddAbove ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ) from ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ) <| Classical.choose_spec ‹ ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ).Nonempty ›;
        have h_large : large_element_count A B x ≥ counting_function B x - counting_function B (x - t) := by
          convert lemma_large_element_lower_bound A B x using 1
        have h_identity : counting_function A x * counting_function B x = excess_count A B x + large_element_count A B x + (⌊x⌋.toNat + 1 - missing_sum_count A B x) := by
          convert lemma_identity A B x hx₃.le using 1
        apply lemma_estimate_inequality_small_t A B x t ε h_excess h_large h_identity hx₂

/-
Lemma: If t < x/2, then A(x)B(x) - x > (1 - ε) t / A(x) eventually.
-/
theorem lemma_estimate_case_small_t (A B : Set ℕ) (h_inf_A : A.Infinite)
    (h_hyp : exact_complements A B) (h_pos_A : ∀ a ∈ A, a ≠ 0) (h_pos_B : ∀ b ∈ B, b ≠ 0)
    (h_smallbig_A : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1))
    (h_r_very_small : Filter.Tendsto (fun x => (missing_sum_count A B x : ℝ) * counting_function A x / a_star A x) Filter.atTop (nhds 0)) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop,
      let t := a_star A x
      t < x / 2 →
      (counting_function A x * counting_function B x : ℝ) - x > (1 - ε) * t / counting_function A x := by
        intro ε hε_pos
        have h_eventually_small : ∀ᶠ x in Filter.atTop, let t := a_star A x; t < x / 2 → (missing_sum_count A B x * counting_function A x : ℝ) / t < ε / 2 := by
          have := h_r_very_small.eventually ( gt_mem_nhds <| half_pos hε_pos ) ; aesop;
        have h_eventually_large : ∀ᶠ x in Filter.atTop, let t := a_star A x; t < x / 2 → (counting_function A x * counting_function B x : ℝ) - x ≥ ((1 - ε / 2) * t - missing_sum_count A B x * counting_function A x) / (counting_function A x - 1) := by
          have := lemma_estimate_lower_bound_small_t A B h_inf_A h_hyp h_pos_A h_pos_B h_smallbig_A ( ε / 2 ) ( half_pos hε_pos ) ; aesop;
        -- Since $A(x) \to \infty$, we have $A(x) / (A(x) - 1) \to 1$.
        have h_A_div_A_minus_one : Filter.Tendsto (fun x => (counting_function A x : ℝ) / (counting_function A x - 1)) Filter.atTop (nhds 1) := by
          have h_A_div_A_minus_one : Filter.Tendsto (fun x => (counting_function A x : ℝ)) Filter.atTop Filter.atTop := by
            have h_counting_function_A_unbounded : Filter.Tendsto (fun x => (counting_function A x : ℝ)) Filter.atTop Filter.atTop := by
              have h_counting_function_A_unbounded : Filter.Tendsto (fun x => (counting_function A x : ℕ)) Filter.atTop Filter.atTop := by
                exact counting_function_tendsto_atTop A h_inf_A
              exact tendsto_natCast_atTop_atTop.comp h_counting_function_A_unbounded;
            convert h_counting_function_A_unbounded using 1;
          have h_A_div_A_minus_one : Filter.Tendsto (fun x => 1 / (1 - 1 / (counting_function A x : ℝ))) Filter.atTop (nhds 1) := by
            exact le_trans ( tendsto_const_nhds.div ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop h_A_div_A_minus_one ) <| by norm_num ) <| by norm_num;
          refine h_A_div_A_minus_one.congr' ( by filter_upwards [ ‹Filter.Tendsto ( fun x : ℝ => ( counting_function A x : ℝ ) ) Filter.atTop Filter.atTop›.eventually_gt_atTop 1 ] with x hx using by rw [ one_sub_div ( by linarith ) ] ; norm_num );
        have h_eventually_final : ∀ᶠ x in Filter.atTop, let t := a_star A x; t < x / 2 → ((1 - ε / 2) * t - missing_sum_count A B x * counting_function A x) / (counting_function A x - 1) > (1 - ε) * t / counting_function A x := by
          have h_eventually_final : ∀ᶠ x in Filter.atTop, let t := a_star A x; t < x / 2 → (1 - ε / 2 - (missing_sum_count A B x * counting_function A x : ℝ) / t) * (counting_function A x : ℝ) / (counting_function A x - 1) > 1 - ε := by
            have h_eventually_final : Filter.Tendsto (fun x => (1 - ε / 2 - (missing_sum_count A B x * counting_function A x : ℝ) / (a_star A x)) * (counting_function A x : ℝ) / (counting_function A x - 1)) Filter.atTop (nhds ((1 - ε / 2) * 1)) := by
              simpa [ mul_div_assoc ] using Filter.Tendsto.mul ( tendsto_const_nhds.sub h_r_very_small ) h_A_div_A_minus_one;
            filter_upwards [ h_eventually_final.eventually ( lt_mem_nhds <| show ( 1 - ε / 2 ) * 1 > 1 - ε by linarith ) ] with x hx using fun hx' => hx.trans_le' <| by linarith;
          filter_upwards [ h_eventually_final, h_eventually_small, h_A_div_A_minus_one.eventually ( lt_mem_nhds one_pos ) ] with x hx₁ hx₂ hx₃;
          by_cases h : a_star A x = 0 <;> simp_all +decide [ sub_mul, mul_div_assoc ];
          · intro hx_pos
            have h_contra : ∃ a ∈ A, a ≤ x := by
              contrapose! hx₃; simp_all +decide [ counting_function ] ;
              rw [ Nat.card_eq_zero.mpr ] <;> norm_num;
              exact Or.inl ⟨ fun ⟨ n, hn₁, hn₂ ⟩ => by linarith [ hx₃ n hn₁ ] ⟩;
            obtain ⟨ a, ha₁, ha₂ ⟩ := h_contra; unfold a_star at h; simp_all +decide [ Set.Nonempty ] ;
            exact absurd ( h a ha₁ ha₂ ) ( ne_of_gt <| lt_of_lt_of_le ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| h_pos_A a ha₁ ) <| le_csSup ( show BddAbove ( A ∩ { n : ℕ | ( n : ℝ ) ≤ x } ) from ⟨ ⌊x⌋₊, fun n hn => Nat.le_floor <| hn.2 ⟩ ) <| Set.mem_inter ha₁ ha₂ );
          · intro hx₄; specialize hx₁ hx₄; specialize hx₂ hx₄; rw [ div_lt_iff₀ ] at *;
            · convert mul_lt_mul_of_pos_right hx₁ ( show 0 < ( a_star A x : ℝ ) by positivity ) using 1 <;> ring_nf;
              simpa [ h, sq, mul_assoc, mul_comm, mul_left_comm ] using by ring;
            · contrapose! hx₃; aesop;
        filter_upwards [ h_eventually_small, h_eventually_large, h_eventually_final ] with x hx₁ hx₂ hx₃ using fun hx₄ => lt_of_lt_of_le ( hx₃ hx₄ ) ( hx₂ hx₄ )

/-
Theorem 3.4: Under the assumptions, A(x)B(x) - x > (1 - ε) a*(x)/A(x) eventually.
-/
theorem theorem_estimate (A B : Set ℕ) (h_inf_A : A.Infinite) (h_inf_B : B.Infinite)
    (h_hyp : exact_complements A B)
    (h_pos_A : ∀ a ∈ A, a ≠ 0) (h_pos_B : ∀ b ∈ B, b ≠ 0)
    (h_smallbig_A : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1))
    (_h_r : Filter.Tendsto (fun x : ℝ => (missing_sum_count A B x : ℝ) / x) Filter.atTop (nhds 0))
    (h_r_very_small : Filter.Tendsto (fun x => (missing_sum_count A B x : ℝ) * counting_function A x / a_star A x) Filter.atTop (nhds 0)) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop, (counting_function A x * counting_function B x : ℝ) - x > (1 - ε) * a_star A x / counting_function A x := by
      intro ε hε_pos
      obtain ⟨h_case1, h_case2⟩ : (∀ᶠ x in Filter.atTop, a_star A x ≥ x / 2 → let t := a_star A x; (counting_function A x * counting_function B x : ℝ) - x ≥ (1 - ε / 2) * t / counting_function A x) ∧ (∀ᶠ x in Filter.atTop, a_star A x < x / 2 → (counting_function A x * counting_function B x : ℝ) - x > (1 - ε) * a_star A x / counting_function A x) := by
        constructor <;> norm_num +zetaDelta at *;
        · have := @lemma_estimate_case2_apply_large_t A B h_inf_A h_inf_B h_hyp h_smallbig_A ( ε / 2 ) ( half_pos hε_pos ) ; aesop;
        · have := @lemma_estimate_case_small_t A B h_inf_A h_hyp h_pos_A h_pos_B h_smallbig_A h_r_very_small ε hε_pos; aesop;
      filter_upwards [ h_case1, h_case2, Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ hx₄;
      by_cases hx₅ : a_star A x ≥ x / 2 <;> simp_all +decide ;
      refine lt_of_lt_of_le ?_ hx₁;
      gcongr <;> try linarith;
      refine Nat.cast_pos.mpr ?_;
      exact Nat.pos_of_ne_zero ( by intro h; norm_num [ h ] at hx₁; linarith )

/-
Corollary 3.5: If A and B are exact complements, then A(x)B(x) - x tends to infinity.
-/
theorem corollary_erdos_785 (A B : Set ℕ) (h_inf_A : A.Infinite) (h_inf_B : B.Infinite)
    (h_pos_A : ∀ a ∈ A, a ≠ 0) (h_pos_B : ∀ b ∈ B, b ≠ 0)
    (h_hyp : exact_complements A B) :
    Filter.Tendsto (fun x : ℝ => counting_function A x * counting_function B x - x) Filter.atTop Filter.atTop := by
      -- We use Narkiewicz's dichotomy.
      by_cases h_case : Filter.Tendsto (fun x => (counting_function A (2 * x) : ℝ) / counting_function A x) Filter.atTop (nhds 1);
      · have h_a_star_div_A_inf : Filter.Tendsto (fun x => (a_star A x : ℝ) / counting_function A x) Filter.atTop Filter.atTop := by
          exact lemma_t_div_A_tendsto_atTop A B h_inf_A h_inf_B h_hyp;
        have h_estimate : ∀ ε > 0, ∀ᶠ x in Filter.atTop, (counting_function A x * counting_function B x : ℝ) - x > (1 - ε) * a_star A x / counting_function A x := by
          apply theorem_estimate A B h_inf_A h_inf_B h_hyp h_pos_A h_pos_B h_case (by
          have := lemma_r_bounded A B h_hyp;
          exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun x hx => by simpa [ abs_div ] using div_le_div_of_nonneg_right ( show ( |↑ ( missing_sum_count A B x ) - 0| : ℝ ) ≤ this.choose by simpa using mod_cast this.choose_spec x ) ( by positivity ) ⟩ ) ( tendsto_const_nhds.div_atTop Filter.tendsto_abs_atTop_atTop )) (by
          convert lemma_r_mul_A_div_t_tendsto_zero A B h_inf_A h_inf_B h_hyp using 1);
        rw [ Filter.tendsto_atTop_atTop ] at *;
        intro b; rcases h_a_star_div_A_inf ( Max.max b 1 * 2 ) with ⟨ i, hi ⟩ ; rcases Filter.eventually_atTop.mp ( h_estimate ( 1 / 2 ) ( by norm_num ) ) with ⟨ j, hj ⟩ ; refine ⟨ Max.max i j, fun x hx => ?_ ⟩ ; specialize hj x ( le_trans ( le_max_right ?_ ?_ ) hx ) ; specialize hi x ( le_trans ( le_max_left ?_ ?_ ) hx ) ; norm_num at * ; ring_nf at * ; nlinarith [ le_max_left b 1, le_max_right b 1 ] ;
      · -- Since $B(2x)/B(x) \to 1$, we can apply `theorem_estimate` to $B$ and $A$.
        have h_case_B : Filter.Tendsto (fun x => (counting_function B (2 * x) : ℝ) / counting_function B x) Filter.atTop (nhds 1) := by
          have := narkiewicz_dichotomy A B h_inf_A h_inf_B h_hyp ( by
            have := lemma_r_bounded A B h_hyp;
            exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun x hx => by simpa [ abs_of_nonneg ( show 0 ≤ x by positivity ) ] using div_le_div_of_nonneg_right ( Nat.cast_le.mpr ( this.choose_spec x ) ) ( by positivity ) ⟩ ) ( tendsto_const_nhds.div_atTop Filter.tendsto_abs_atTop_atTop ) ) ; aesop;
        have := @theorem_estimate B A h_inf_B h_inf_A ( lemma_exact_complements_symm A B h_hyp ) h_pos_B h_pos_A h_case_B ?_ ?_ ?_ <;> norm_num at *;
        any_goals exact 1 / 2;
        · -- Since $a_star B x / counting_function B x$ tends to infinity, multiplying by $(1/2)$ still gives something that tends to infinity.
          have h_inf : Filter.Tendsto (fun x => (a_star B x : ℝ) / counting_function B x) Filter.atTop Filter.atTop := by
            convert lemma_t_div_A_tendsto_atTop B A h_inf_B h_inf_A ( lemma_exact_complements_symm A B h_hyp ) using 1;
          rw [ Filter.tendsto_atTop_atTop ] at *;
          intro b; obtain ⟨ i, hi ⟩ := h_inf ( b * 2 ) ; obtain ⟨ j, hj ⟩ := this ( by norm_num ) ; exact ⟨ Max.max i j, fun x hx => by have := hi x ( le_trans ( le_max_left _ _ ) hx ) ; have := hj x ( le_trans ( le_max_right _ _ ) hx ) ; ring_nf at *; linarith ⟩ ;
        · have h_r_bound : ∃ C, ∀ x, missing_sum_count B A x ≤ C := by
            apply lemma_r_bounded B A (lemma_exact_complements_symm A B h_hyp) |> fun ⟨C, hC⟩ => ⟨C, fun x => hC x⟩
          generalize_proofs at *
          obtain ⟨ C, hC ⟩ := h_r_bound
          exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun x hx => by simpa [ abs_div, abs_of_nonneg ( show 0 ≤ x by positivity ) ] using div_le_div_of_nonneg_right ( Nat.cast_le.mpr ( hC x ) ) ( show 0 ≤ x by positivity ) ⟩ ) ( tendsto_const_nhds.div_atTop Filter.tendsto_abs_atTop_atTop )
        · convert lemma_r_mul_A_div_t_tendsto_zero B A h_inf_B h_inf_A ( lemma_exact_complements_symm A B h_hyp ) using 1

end

end Erdos785

#print axioms Erdos785.corollary_erdos_785
-- 'Erdos785.corollary_erdos_785' depends on axioms: [propext, Classical.choice, Quot.sound]
