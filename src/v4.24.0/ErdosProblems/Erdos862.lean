/-

This is a Lean formalization of a solution to Erdős Problem 862.
https://www.erdosproblems.com/forum/thread/862

The original proof was found by: Saxton & Thomason

 [SaTh15] Saxton, David and Thomason, Andrew, Hypergraph
 containers. Invent. Math. (2015), 925--992.


A proof of ChatGPT's choice was auto-formalized by Aristotle (from
Harmonic).  The final theorem statement was written by Aristotle.

Some results were taken from Kevin Barreto's proof for Erdős Problem
43 (but they were proven by Aristotle also).

The proof assumes a consequence of the Prime Number Theorem as an
axiom ("no multiplicative gaps").  That statement was taken directly
from the PrimeNumberTheoremAnd project.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

/-
We formalized the proof that there are many maximal Sidon subsets of an interval.
Key results include:
- `lem_extend`: Every Sidon set is contained in a maximal Sidon set.
- `lem_cover`: A bound relating A(N), A_1(N), and f(N).
- `lem_ruzsa_group` and `lem_modular`: Construction of modular Sidon sets.
- `lem_four_block`: A construction lifting modular Sidon sets to integers.
- `prop_lower_special_ineq`: Lower bound for A(N) at special N.
- `eventually_lower_bound`: Lower bound for A(N) for all large N.
- `thm_main`: The main lower bound for A_1(N).
- `cor_answers_1` and `cor_answers_2`: Corollaries regarding the growth of A_1(N).

In `eventually_lower_bound`, we avoid issues with `liminf` in `Real` for potentially unbounded sequences. The main theorem and corollaries follow from this bound.
-/

import Mathlib


set_option maxHeartbeats 0

open scoped BigOperators

noncomputable section

open Real Filter Asymptotics

axiom prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x

/-- A Sidon set: any equation a+b=c+d with all terms in S forces {a,b}={c,d}. -/
def Sidon {α : Type} [AddCommMonoid α] (S : Set α) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d → ({a, b} : Set α) = {c, d}

/-- Sidon modulo M: the image of S in ZMod M is Sidon. -/
def SidonMod (M : ℕ) (S : Set ℕ) : Prop :=
  Sidon ((fun x : ℕ => (x : ZMod M)) '' S)

/-- f(N): maximum size of a Sidon subset of [1..N]. -/
noncomputable def f (N : ℕ) : ℕ :=
  let rangeN : Finset ℕ := Finset.Icc 1 N
  letI : DecidablePred (fun A => Sidon (A : Set ℕ)) := Classical.decPred _
  let sidonSets : Finset (Finset ℕ) :=
    rangeN.powerset.filter (fun A => Sidon (A : Set ℕ))
  sidonSets.sup Finset.card

/-- Sidon of order h: sums of h elements determine multisets. -/
def SidonOfOrder {α : Type*} [AddCommMonoid α] (h : ℕ) (S : Set α) : Prop :=
  ∀ u v : Fin h → α, (∀ i, u i ∈ S) → (∀ i, v i ∈ S) →
    (∑ i, u i) = (∑ i, v i) → List.Perm (List.ofFn u) (List.ofFn v)

/-- Sidon of order h modulo M. -/
def SidonModOfOrder (h M : ℕ) (S : Set ℕ) : Prop :=
  SidonOfOrder h ((fun n : ℕ => (n : ZMod M)) '' S)

section ErdosTuran

/-- Inequality for Sidon sets derived from the difference set argument. -/
lemma erdos_turan_inequality {N m : ℕ} (hm : 0 < m) (A : Finset ℕ)
    (hSidon : Sidon (A : Set ℕ)) (hA : A ⊆ Finset.Icc 1 N) :
    (A.card ^ 2 : ℝ) ≤ (N + m : ℝ) * (A.card / m + 1) := by
  have h_cauchy_schwarz :
      ((Finset.card A * m : ℝ)) ^ 2 ≤
      ((Finset.card (Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A))) : ℝ) *
      ((Finset.card A * m : ℝ) + (m * (m - 1))) := by
    have h_cs_inner :
        ((Finset.card A * m : ℝ)) ^ 2 ≤
        ((Finset.card (Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A))) : ℝ) *
        ((∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A),
          ((∑ j ∈ Finset.Icc 1 m,
            (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2)) := by
      have h_cs : ∀ (S : Finset ℕ) (g : ℕ → ℝ),
          (∑ x ∈ S, g x) ^ 2 ≤ (Finset.card S : ℝ) * ∑ x ∈ S, g x ^ 2 := by
        intro S g
        have := Finset.sum_le_sum fun x (_ : x ∈ S) =>
          mul_self_nonneg (g x - (∑ y ∈ S, g y) / S.card)
        by_cases hS : S = ∅
        · simp_all
        · have hne : (S.card : ℝ) ≠ 0 := by
            exact Nat.cast_ne_zero.mpr <| Finset.card_ne_zero_of_mem <|
              Classical.choose_spec <| Finset.nonempty_of_ne_empty hS
          have h2 : (∑ y ∈ S, g y) / ↑S.card * ↑S.card = ∑ y ∈ S, g y := by
            rw [mul_comm]; exact mul_div_cancel₀ (∑ y ∈ S, g y) hne
          have h_exp : ∑ x ∈ S, (g x - (∑ y ∈ S, g y) / ↑S.card) ^ 2 =
              ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 / ↑S.card := by
            calc ∑ x ∈ S, (g x - (∑ y ∈ S, g y) / ↑S.card) ^ 2
                = ∑ x ∈ S, (g x ^ 2 - 2 * g x * ((∑ y ∈ S, g y) / ↑S.card) +
                    ((∑ y ∈ S, g y) / ↑S.card) ^ 2) := by congr 1 with x; rw [sub_sq]
              _ = ∑ x ∈ S, g x ^ 2 - ∑ x ∈ S, 2 * g x * ((∑ y ∈ S, g y) / ↑S.card) +
                    ∑ x ∈ S, ((∑ y ∈ S, g y) / ↑S.card) ^ 2 := by
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              _ = ∑ x ∈ S, g x ^ 2 - 2 * ((∑ y ∈ S, g y) / ↑S.card) * (∑ x ∈ S, g x) +
                    ↑S.card * ((∑ y ∈ S, g y) / ↑S.card) ^ 2 := by
                  rw [Finset.sum_const, nsmul_eq_mul]
                  have : ∑ x ∈ S, 2 * g x * ((∑ y ∈ S, g y) / ↑S.card) =
                      2 * ((∑ y ∈ S, g y) / ↑S.card) * (∑ x ∈ S, g x) := by
                    rw [Finset.mul_sum]; congr 1 with x; ring
                  rw [this]
              _ = ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 / ↑S.card := by
                  rw [sq]; field_simp [hne]; ring
          have h_ge : ∑ x ∈ S, (g x - (∑ y ∈ S, g y) / ↑S.card) ^ 2 ≥ 0 := by
            refine Finset.sum_nonneg fun x _ => sq_nonneg _
          rw [h_exp] at h_ge
          have hScard : (S.card : ℝ) > 0 := Nat.cast_pos.mpr (Finset.card_pos.mpr
            (Finset.nonempty_of_ne_empty hS))
          have h_expand : ↑S.card * (∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 / ↑S.card) =
              ↑S.card * ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 := by field_simp [hne]
          have h_prod : ↑S.card * ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 ≥ 0 := by
            rw [← h_expand]; exact mul_nonneg (le_of_lt hScard) h_ge
          nlinarith [sq_nonneg (∑ y ∈ S, g y)]
      convert h_cs _ _ using 2
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl fun x _ => ?_]
      · rw [Finset.sum_const, Finset.card_eq_sum_ones]
        · norm_num
          rw [mul_comm]
      · simp +zetaDelta at *
        rw [show { x_1 ∈ Finset.biUnion (Finset.Icc 1 m)
            (fun j => Finset.image (fun a => a + j) A) |
            ∃ a ∈ A, a + x = x_1 } = Finset.image (fun a => a + x) A from ?_]
        · exact Finset.card_image_of_injective _ (add_left_injective x)
        · ext; aesop
    have h_sum_r_sq :
        (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A),
          ((∑ j ∈ Finset.Icc 1 m,
            (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2) ≤
        (A.card * m : ℝ) + (m * (m - 1)) := by
      have h_sum_bound :
          ∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
            (fun j => Finset.image (fun a => a + j) A),
            ((∑ j ∈ Finset.Icc 1 m,
              (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2 ≤
          ∑ j ∈ Finset.Icc 1 m, ∑ j' ∈ Finset.Icc 1 m,
            (if j = j' then (A.card : ℝ) else 1) := by
        have h_pair_bound : ∀ j j' : ℕ, j ∈ Finset.Icc 1 m → j' ∈ Finset.Icc 1 m →
            (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
              (fun j => Finset.image (fun a => a + j) A),
              (if ∃ a ∈ A, a + j = x then 1 else 0) *
              (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) ≤
            if j = j' then (A.card : ℝ) else 1 := by
          intros j j' hj hj'
          have h_le_filter :
              (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
                (fun j => Finset.image (fun a => a + j) A),
                (if ∃ a ∈ A, a + j = x then 1 else 0) *
                (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) ≤
              (Finset.filter (fun x => ∃ a ∈ A, a + j = x ∧ ∃ a ∈ A, a + j' = x)
                (Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A))).card := by
            rw [Finset.card_filter]
            push_cast [Finset.sum_mul _ _ _]
            gcongr; aesop
          split_ifs
          · simp_all
            exact le_trans (Finset.card_le_card
              (show Finset.filter (fun x => ∃ a ∈ A, a + j' = x)
                (Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A)) ⊆
                Finset.image (fun a => a + j') A from fun x hx => by aesop))
              Finset.card_image_le
          · refine le_trans h_le_filter ?_
            have h_unique : ∀ x y : ℕ,
                x ∈ Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A) →
                y ∈ Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A) →
                (∃ a ∈ A, a + j = x ∧ ∃ a ∈ A, a + j' = x) →
                (∃ a ∈ A, a + j = y ∧ ∃ a ∈ A, a + j' = y) → x = y := by
              intros x y _ _ hx' hy'
              obtain ⟨a, haA, ha_eq_x, b, hbA, hb_eq_x⟩ := hx'
              obtain ⟨c, hcA, hc_eq_y, d, hdA, hd_eq_y⟩ := hy'
              have := hSidon a d b c haA hdA hbA hcA
              simp_all [add_comm]; grind
            exact_mod_cast Finset.card_le_one.mpr fun x hx y hy =>
              h_unique x y (Finset.mem_filter.mp hx |>.1)
                (Finset.mem_filter.mp hy |>.1)
                (Finset.mem_filter.mp hx |>.2) (Finset.mem_filter.mp hy |>.2)
        have h_expand :
            ∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
              (fun j => Finset.image (fun a => a + j) A),
              (∑ j ∈ Finset.Icc 1 m,
                (if ∃ a ∈ A, a + j = x then 1 else 0) : ℝ) ^ 2 =
            ∑ j ∈ Finset.Icc 1 m, ∑ j' ∈ Finset.Icc 1 m,
              (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
                (fun j => Finset.image (fun a => a + j) A),
                (if ∃ a ∈ A, a + j = x then 1 else 0) *
                (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) := by
          simp +decide only [pow_two, Finset.sum_mul _ _ _]
          rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
          simp +decide only [Finset.mul_sum _ _ _]
        exact h_expand.symm ▸ Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun j hj => by aesop
      simp_all [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne]; linarith
    exact h_cs_inner.trans (mul_le_mul_of_nonneg_left h_sum_r_sq <|
      Nat.cast_nonneg _)
  have h_support_size :
      (Finset.card (Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A))) ≤ (N + m - 1 : ℝ) := by
    norm_cast
    rw [Int.subNatNat_of_le (by omega)]; norm_cast
    exact le_trans (Finset.card_le_card
      (show Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A) ⊆ Finset.Icc 2 (N + m) from
        Finset.biUnion_subset.2 fun j hj =>
          Finset.image_subset_iff.2 fun a ha =>
            Finset.mem_Icc.2 ⟨by
              have := Finset.mem_Icc.1 (hA ha)
              have := Finset.mem_Icc.1 hj
              omega, by
              have := Finset.mem_Icc.1 (hA ha)
              have := Finset.mem_Icc.1 hj
              omega⟩)) (by norm_num; omega)
  have h_sub : ((Finset.card A * m : ℝ)) ^ 2 ≤
      ((N + m - 1 : ℝ)) * ((Finset.card A * m : ℝ) + (m * (m - 1))) :=
    h_cauchy_schwarz.trans (mul_le_mul_of_nonneg_right h_support_size <|
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) <| Nat.cast_nonneg _) <|
      mul_nonneg (Nat.cast_nonneg _) <| sub_nonneg.mpr <|
      Nat.one_le_cast.mpr hm)
  field_simp at *
  nlinarith [show (m : ℝ) ≥ 1 by norm_cast]

/-
Algebraic bound for x satisfying a quadratic inequality x^2 ≤ bx + c.
-/
lemma quadratic_bound_pos {x b c : ℝ} (c_nonneg : 0 ≤ c) (h : x^2 ≤ b * x + c) :
    x ≤ (b + Real.sqrt (b^2 + 4 * c)) / 2 := by
      nlinarith [ Real.sqrt_nonneg ( b^2 + 4 * c ), Real.mul_self_sqrt ( by positivity : 0 ≤ b^2 + 4 * c ) ]

/-
Limit lemma for Erdős-Turán (sequence version).
-/
lemma erdos_turan_limit_lemma_nat {m : ℕ → ℝ} (hm_pos : ∀ᶠ n in atTop, 0 < m n)
    (hm1 : Tendsto (fun (n : ℕ) => m n / (n : ℝ)) atTop (nhds 0))
    (hm2 : Tendsto (fun (n : ℕ) => Real.sqrt (n : ℝ) / m n) atTop (nhds 0)) :
    Tendsto (fun (n : ℕ) => ( ((n : ℝ) + m n)/ (m n) + Real.sqrt ( (((n : ℝ) + m n)/ (m n))^2 + 4 * ((n : ℝ) + m n) ) ) / (2 * Real.sqrt (n : ℝ))) atTop (nhds 1) := by
      -- Let's simplify the expression inside the limit.
      suffices h_simp : Filter.Tendsto (fun n : ℕ => ((Real.sqrt n / m n + 1 / Real.sqrt n) + Real.sqrt ((Real.sqrt n / m n + 1 / Real.sqrt n)^2 + 4 * (1 + m n / n))) / 2) Filter.atTop (nhds 1) by
        refine h_simp.congr' ?_;
        filter_upwards [ hm_pos, Filter.eventually_gt_atTop 0 ] with n hn hn';
        field_simp [hn, hn']
        ring_nf;
        norm_num [ show Real.sqrt n ^ 4 = ( Real.sqrt n ^ 2 ) ^ 2 by ring, hn.ne', hn'.ne', mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
        field_simp;
        rw [ show ( m n * ( ( m n * 4 + 2 ) * n + m n ^ 2 * 4 ) + n ^ 2 + m n ^ 2 : ℝ ) / ( m n ^ 2 * n ) = ( ( m n * ( m n + 2 * n + m n ^ 2 * 4 ) + n ^ 2 + m n ^ 2 * 4 * n ) / m n ^ 2 ) / n by rw [ div_div ] ; ring ] ; norm_num [ hn.ne', hn'.ne' ] ; ring_nf;
        exact mul_div_cancel_left₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr hn';
      convert Filter.Tendsto.div_const ( Filter.Tendsto.add ( hm2.add ( tendsto_inverse_atTop_nhds_zero_nat.sqrt ) ) ( Filter.Tendsto.sqrt ( Filter.Tendsto.add ( Filter.Tendsto.pow ( hm2.add ( tendsto_inverse_atTop_nhds_zero_nat.sqrt ) ) 2 ) ( tendsto_const_nhds.mul ( tendsto_const_nhds.add hm1 ) ) ) ) ) 2 using 2 ; norm_num;
      congr! 1;
      norm_num

/-
Explicit algebraic bound for the size of a Sidon set using the Erdős-Turán inequality.
-/
lemma erdos_turan_explicit_bound {N m : ℕ} (hm : 0 < m) (A : Finset ℕ)
    (hSidon : Sidon (A : Set ℕ)) (hA : A ⊆ Finset.Icc 1 N) :
    (A.card : ℝ) ≤ ( (N + m : ℝ)/m + Real.sqrt ( ((N + m : ℝ)/m)^2 + 4 * (N + m) ) ) / 2 := by
      have := @erdos_turan_inequality N m hm A hSidon hA;
      convert quadratic_bound_pos ?_ ?_ using 1;
      · positivity;
      · convert this using 1 ; ring

/- Erdős-Turán Theorem: f(N) ≤ (1+ε)√N for large N. -/
theorem ErdosTuran : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (f N : ℝ) ≤ (1 + ε) * Real.sqrt N := by
  intro ε hε_pos
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ N ≥ N0, ((N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) / Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) + Real.sqrt (((N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) / Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 + 4 * (N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))))) / (2 * Real.sqrt N) < 1 + ε := by
    have h_limit : Filter.Tendsto (fun N : ℕ => ((N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) / Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) + Real.sqrt (((N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) / Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 + 4 * (N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))))) / (2 * Real.sqrt N)) Filter.atTop (nhds 1) := by
      have h_m_pos : ∀ᶠ N in Filter.atTop, 0 < Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) := by
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN using Nat.floor_pos.mpr ( Real.one_le_rpow hN.le ( by norm_num ) )
      have h_m1 : Filter.Tendsto (fun N : ℕ => (Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) : ℝ) / N) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊ \leq (N : ℝ) ^ (3 / 4 : ℝ)$ and $(N : ℝ) ^ (3 / 4 : ℝ) / N = N^{-1/4}$.
        have h_floor_le : ∀ N : ℕ, (Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) : ℝ) / N ≤ (N : ℝ) ^ (-1 / 4 : ℝ) := by
          intro N; by_cases hN : N = 0 <;> norm_num [ hN ];
          rw [ div_le_iff₀ ( by positivity ) ];
          exact le_trans ( Nat.floor_le ( by positivity ) ) ( by rw [ ← Real.rpow_add_one ( by positivity ) ] ; norm_num );
        exact squeeze_zero ( fun N => by positivity ) h_floor_le ( by simpa [ neg_div ] using tendsto_rpow_neg_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop )
      have h_m2 : Filter.Tendsto (fun N : ℕ => Real.sqrt N / (Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) : ℝ)) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $\sqrt{N} / \lfloor N^{3/4} \rfloor \leq \sqrt{N} / (N^{3/4} - 1)$.
        suffices h_sqrt_div_floor_le : Filter.Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) / ((N : ℝ) ^ (3 / 4 : ℝ) - 1)) Filter.atTop (nhds 0) by
          refine' squeeze_zero_norm' _ h_sqrt_div_floor_le;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_left ( by positivity ) ( sub_pos.mpr <| Real.one_lt_rpow ( by norm_cast ) <| by norm_num ) <| by linarith [ Nat.lt_floor_add_one ( ( n : ℝ ) ^ ( 3 / 4 : ℝ ) ) ] ;
        -- We can simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) / ((N : ℝ) ^ (3 / 4 : ℝ) - 1)) Filter.atTop (nhds 0) by
          simpa only [ Real.sqrt_eq_rpow ] using h_simplify;
        -- We can divide the numerator and the denominator by $N^{3/4}$.
        suffices h_div : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 - 3 / 4 : ℝ) / (1 - 1 / (N : ℝ) ^ (3 / 4 : ℝ))) Filter.atTop (nhds 0) by
          refine h_div.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by rw [ one_sub_div ( by positivity ) ] ; rw [ div_div_eq_mul_div ] ; rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf;
        norm_num [ Real.rpow_neg ];
        exact le_trans ( Filter.Tendsto.div ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) ) ( tendsto_const_nhds.sub <| tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) ) <| by norm_num ) <| by norm_num;
      convert erdos_turan_limit_lemma_nat _ _ _ using 2;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| Real.one_le_rpow ( mod_cast hN ) <| by norm_num;
      · convert h_m1 using 1;
      · convert h_m2 using 1;
    simpa using h_limit.eventually ( gt_mem_nhds <| by linarith );
  use N0 + 1;
  -- By definition of $f$, we know that $f(N)$ is the maximum size of a Sidon subset of $[1, N]$.
  intro N hN
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Sidon (A : Set ℕ) ∧ A.card = f N := by
    -- By definition of $f$, we know that $f(N)$ is the maximum size of a Sidon subset of $[1, N]$. Hence, there exists a Sidon subset $A$ of $[1, N]$ with $|A| = f(N)$.
    obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Sidon (A : Set ℕ) ∧ ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 N → Sidon (B : Set ℕ) → B.card ≤ A.card := by
      have h_finite : Set.Finite {B : Finset ℕ | B ⊆ Finset.Icc 1 N ∧ Sidon (B : Set ℕ)} := by
        exact Set.finite_iff_bddAbove.mpr ⟨ Finset.Icc 1 N, fun B hB => Finset.le_iff_subset.mpr hB.1 ⟩;
      have h_max : ∃ A ∈ {B : Finset ℕ | B ⊆ Finset.Icc 1 N ∧ Sidon (B : Set ℕ)}, ∀ B ∈ {B : Finset ℕ | B ⊆ Finset.Icc 1 N ∧ Sidon (B : Set ℕ)}, A.card ≥ B.card := by
        apply_rules [ Set.exists_max_image ];
        exact ⟨ ∅, by simp +decide [ Sidon ] ⟩;
      exact ⟨ h_max.choose, h_max.choose_spec.1.1, h_max.choose_spec.1.2, fun B hB₁ hB₂ => h_max.choose_spec.2 B ⟨ hB₁, hB₂ ⟩ ⟩;
    refine' ⟨ A, hA.1, hA.2.1, le_antisymm _ _ ⟩;
    · refine' Finset.le_sup ( f := Finset.card ) _;
      aesop;
    · exact Finset.sup_le fun B hB => by aesop;
  have := erdos_turan_explicit_bound ( show 0 < Nat.floor ( ( N : ℝ ) ^ ( 3 / 4 : ℝ ) ) from Nat.floor_pos.mpr <| Real.one_le_rpow ( mod_cast by linarith ) <| by norm_num ) A hA.2.1 hA.1;
  have := hN0 N ( by linarith ) ; rw [ div_lt_iff₀ ( mul_pos zero_lt_two <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by linarith ) ] at this; nlinarith [ Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, show ( A.card : ℝ ) = f N from mod_cast hA.2.2 ] ;

end ErdosTuran

/-!
## Bose-Chowla Theorem

**Theorem (Bose-Chowla, 1962):** For any prime power $q$, there exists a set
$S \subseteq \{1, 2, \ldots, q^2 - 2\}$ of size $|S| = q$ that is Sidon modulo $q^2 - 1$.

**Construction:** We follow the proof in Nathanson (2021).
Let $\mathbb{F}_q$ be the finite field of order $q$, and let $\mathbb{F}_{q^2}$ be
its quadratic extension. Let $\theta \in \mathbb{F}_{q^2}$ be a primitive
$(q^2 - 1)$-th root of unity. For each $x \in \mathbb{F}_q$, there exists a unique
$k_x \in \{1, 2, \ldots, q^2 - 2\}$ such that $\theta^{k_x} = \theta - x$.
The set $S = \{k_x : x \in \mathbb{F}_q\}$ is Sidon modulo $q^2 - 1$.

**Key ideas:**
- $\theta \notin \mathbb{F}_q$ (since $\theta$ is a primitive $(q^2-1)$-th root but $q^2-1$
  does not divide $q-1$).
- The map $x \mapsto k_x$ is well-defined and injective.
- The polynomial identity argument shows that distinct $h$-fold sums from $S$ yield distinct
  products of roots in $\mathbb{F}_{q^2}$, establishing the Sidon property modulo $q^2 - 1$.
-/

section BoseChowla

variable {Fq Fqh : Type*} [Field Fq] [Fintype Fq]

variable [Field Fqh] [Fintype Fqh]

variable [Algebra Fq Fqh]

/-- The modulus q^h - 1 in the Bose–Chowla theorem. -/
def boseChowlaMod (h : ℕ) : ℕ := (Fintype.card Fq) ^ h - 1

omit [Fintype Fqh] in
theorem theta_not_in_Fq {h : ℕ} (hh : 2 ≤ h) (_hdeg : Module.finrank Fq Fqh = h)
    (theta : Fqh) (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h)) :
    ∀ x : Fq, theta ≠ algebraMap Fq Fqh x := by
  unfold boseChowlaMod at htheta
  intro x hx
  have := htheta.pow_eq_one
  rw [hx] at this
  have := htheta.2
  simp_all [IsPrimitiveRoot.iff_def]
  contrapose! this
  refine ⟨Fintype.card Fq - 1, ?_, ?_⟩
  · by_cases hx0 : x = 0
    · simp_all [Nat.sub_ne_zero_of_lt (Fintype.one_lt_card)]
      rw [zero_pow (Nat.sub_ne_zero_of_lt
        (one_lt_pow₀ (Fintype.one_lt_card) (by linarith)))] at this
      simp_all
    · rw [← map_pow, FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
  · refine Nat.not_dvd_of_pos_of_lt ?_ ?_
    · exact Nat.sub_pos_of_lt (Fintype.one_lt_card)
    · rw [tsub_lt_tsub_iff_right
        (Nat.one_le_iff_ne_zero.mpr <| Fintype.card_ne_zero)]
      exact lt_self_pow₀ (Fintype.one_lt_card) hh

theorem bose_chowla_exponents {h : ℕ} (hh : 2 ≤ h)
    (hdeg : Module.finrank Fq Fqh = h) (theta : Fqh)
    (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h)) :
    ∀ x : Fq, ∃! k : ℕ, 0 < k ∧ k < boseChowlaMod (Fq := Fq) h ∧
      theta ^ k = theta - algebraMap Fq Fqh x := by
  intro x
  have h_neq : theta ≠ algebraMap Fq Fqh x :=
    theta_not_in_Fq hh hdeg theta htheta x
  have h_sub_neq_zero : theta - algebraMap Fq Fqh x ≠ 0 := sub_ne_zero.mpr h_neq
  have h_card : Fintype.card Fqh = Fintype.card Fq ^ h := by
    rw [← hdeg]; exact Module.card_eq_pow_finrank (K := Fq) (V := Fqh)
  have h_mod : boseChowlaMod (Fq := Fq) h = Fintype.card Fqh - 1 := by
    unfold boseChowlaMod; rw [h_card]
  rw [h_mod] at htheta ⊢
  have h_order : ∀ y : Fqh, y ≠ 0 →
      ∃ k : ℕ, 0 ≤ k ∧ k < Fintype.card Fqh - 1 ∧ theta ^ k = y := by
    intro y hy_ne_zero
    have h_ord : y ∈ Set.range (fun k : ℕ => theta ^ k) := by
      have h_cyclic : ∀ y : Fqhˣ,
          y ∈ Subgroup.zpowers (Units.mk0 theta (by
            intro hzero; simp_all [IsPrimitiveRoot.iff_def]
            have hpos : 0 < Fintype.card Fq ^ h - 1 := Nat.sub_pos_of_lt
              (one_lt_pow₀ (Fintype.one_lt_card) (by linarith))
            simp [zero_pow hpos.ne'] at htheta)) := by
        generalize_proofs at *
        have h_gen : Subgroup.zpowers (Units.mk0 theta (by aesop)) = ⊤ := by
          refine Subgroup.eq_top_of_card_eq _ ?_
          rw [Nat.card_zpowers, orderOf_eq_iff]
          · simp_all [Units.ext_iff]
            intro m hm₁ hm₂ hm₃
            have := htheta.pow_eq_one_iff_dvd m
            simp_all
            exact hm₁.not_ge (Nat.le_of_dvd hm₂
              (by simpa [Nat.card_eq_fintype_card, h_card, Nat.card_units]
                using hm₃))
          · simp +decide
        generalize_proofs at *; aesop
      obtain ⟨k, hk⟩ := h_cyclic (Units.mk0 y hy_ne_zero)
      rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩ <;>
        simp_all [Units.ext_iff]
      · use k
      · use (Fintype.card Fqh - 1) - k % (Fintype.card Fqh - 1)
        rw [← hk, ← Nat.mod_add_div k (Fintype.card Fqh - 1)]
        have h_ord' : theta ^ (Fintype.card Fqh - 1) = 1 := by
          have := htheta.pow_eq_one; aesop
        simp +decide [pow_add, pow_mul, h_ord']
        exact eq_inv_of_mul_eq_one_left (by
          rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt
            (Nat.mod_lt _ (Nat.sub_pos_of_lt Fintype.one_lt_card))), h_ord'])
    simp +zetaDelta at *
    obtain ⟨k, rfl⟩ := h_ord
    exact ⟨k % (Fintype.card Fqh - 1),
      Nat.mod_lt _ (Nat.sub_pos_of_lt (Fintype.one_lt_card)), by
        rw [← Nat.mod_add_div k (Fintype.card Fqh - 1), pow_add, pow_mul]
        simp +decide [htheta.pow_eq_one]⟩
  obtain ⟨k, _, hk₂, hk₃⟩ := h_order _ h_sub_neq_zero
  refine ⟨k, ⟨Nat.pos_of_ne_zero ?_, hk₂, hk₃⟩, fun m ⟨hm₁, hm₂, hm₃⟩ => ?_⟩
  · rintro rfl; simp_all
    have := theta_not_in_Fq hh hdeg theta htheta
    simp_all
    exact this (x + 1) (by simpa using eq_add_of_sub_eq' hk₃.symm)
  · have := htheta.pow_inj (by linarith : m < Fintype.card Fqh - 1)
      (by linarith : k < Fintype.card Fqh - 1)
    aesop

theorem minpoly_degree_eq_h {h : ℕ} (hh : 2 ≤ h)
    (hdeg : Module.finrank Fq Fqh = h) (theta : Fqh)
    (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h)) :
    (minpoly Fq theta).natDegree = h := by
  have h_subfield : (IntermediateField.adjoin Fq {theta}) = ⊤ := by
    have h_pow : ∀ x : Fqh, x ≠ 0 → ∃ k : ℕ, x = theta ^ k := by
      intro x hx_ne_zero
      have h_ord : IsPrimitiveRoot theta (Fintype.card Fqh - 1) := by
        have h_card : Fintype.card Fqh = (Fintype.card Fq) ^ h := by
          have := Module.card_eq_pow_finrank (K := Fq) (V := Fqh)
          rw [this, hdeg]
        aesop
      have h_inner : ∀ x : Fqh, x ≠ 0 → ∃ k : ℕ, x = theta ^ k := by
        intro x hx_ne
        have h_units : ∀ y : Fqhˣ, ∃ k : ℕ, y = theta ^ k := by
          intro y
          have h_mem : y ∈ Subgroup.zpowers (Units.mk0 theta
              (h_ord.ne_zero (Nat.sub_ne_zero_of_lt (Fintype.one_lt_card)))) := by
            generalize_proofs at *
            have h_top : Subgroup.zpowers (Units.mk0 theta ‹_›) = ⊤ := by
              refine Subgroup.eq_top_of_card_eq _ ?_
              simp +zetaDelta at *
              rw [orderOf_eq_iff]
              · simp_all +decide [Units.ext_iff, IsPrimitiveRoot.iff_def]
                intro m hm₁ hm₂ hm₃
                have := h_ord.2 m hm₃
                rw [Nat.dvd_iff_mod_eq_zero] at this
                rw [Nat.mod_eq_of_lt] at this <;>
                  simp_all +decide
                rw [Nat.card_units] at hm₁; aesop
              · simp +decide
            aesop
          generalize_proofs at *
          obtain ⟨k, hk⟩ := h_mem
          rw [← hk]
          rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩ <;> norm_num
          use (Fintype.card Fqh - 1) - k % (Fintype.card Fqh - 1)
          rw [inv_eq_of_mul_eq_one_right]
          rw [← pow_add, ← Nat.mod_add_div k (Fintype.card Fqh - 1), add_comm]
          simp +decide
          rw [show Fintype.card Fqh - 1 - k % (Fintype.card Fqh - 1) +
              (k % (Fintype.card Fqh - 1) +
                (Fintype.card Fqh - 1) * (k / (Fintype.card Fqh - 1))) =
              (Fintype.card Fqh - 1) * (k / (Fintype.card Fqh - 1) + 1) by
            linarith [Nat.sub_add_cancel (show k % (Fintype.card Fqh - 1) ≤
              Fintype.card Fqh - 1 from Nat.le_of_lt (Nat.mod_lt _
                (Nat.sub_pos_of_lt (Fintype.one_lt_card))))]]
          simp +decide [pow_mul, h_ord.pow_eq_one]
        simpa using h_units (Units.mk0 x hx_ne)
      exact h_inner x hx_ne_zero
    ext x
    by_cases hx : x = 0 <;>
      simp_all +decide [IntermediateField.mem_adjoin_simple_iff]
    obtain ⟨k, rfl⟩ := h_pow x hx
    exact ⟨Polynomial.X ^ k, 1, by simp +decide⟩
  have := IntermediateField.adjoin.finrank
    (show IsIntegral Fq theta from Algebra.IsIntegral.isIntegral theta)
  · rw [← this, ← hdeg, h_subfield]; simp +decide

theorem multiset_prod_X_sub_C_injective {F : Type*} [Field F] (s t : Multiset F) :
    (s.map (fun x => Polynomial.X - Polynomial.C x)).prod =
    (t.map (fun x => Polynomial.X - Polynomial.C x)).prod ↔ s = t := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  replace h := congr_arg (fun p => Polynomial.roots p) h
  simp_all +decide

theorem bose_chowla_poly_identity {h : ℕ} (hh : 2 ≤ h)
    (hdeg : Module.finrank Fq Fqh = h) (theta : Fqh)
    (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h))
    (s t : Multiset Fq) (hs : s.card = h) (ht : t.card = h)
    (heq : (s.map (fun x => theta - algebraMap Fq Fqh x)).prod =
           (t.map (fun x => theta - algebraMap Fq Fqh x)).prod) :
    s = t := by
  set Ps : Polynomial Fq :=
    Multiset.prod (Multiset.map (fun x => Polynomial.X - Polynomial.C x) s)
  set Pt : Polynomial Fq :=
    Multiset.prod (Multiset.map (fun x => Polynomial.X - Polynomial.C x) t)
  set Q : Polynomial Fq := Ps - Pt
  have hQ : Polynomial.aeval theta Q = 0 := by
    simp +zetaDelta at *
    simp_all +decide [Polynomial.aeval_def, Polynomial.eval₂_multiset_prod]
  have hQ_zero : Q = 0 := by
    have hQ_div_minpoly : minpoly Fq theta ∣ Q := minpoly.dvd Fq theta hQ
    have hQ_deg : Q.degree < h := by
      refine lt_of_lt_of_le (Polynomial.degree_sub_lt ?_ ?_ ?_) ?_
      · rw [Polynomial.degree_multiset_prod, Polynomial.degree_multiset_prod]
        aesop
      · simp +zetaDelta at *
        exact fun x hx => Polynomial.X_sub_C_ne_zero x
      · rw [Polynomial.leadingCoeff_multiset_prod,
          Polynomial.leadingCoeff_multiset_prod]
        aesop
      · erw [Polynomial.degree_multiset_prod]; aesop
    have hQ_minpoly_deg : (minpoly Fq theta).degree = h := by
      convert minpoly_degree_eq_h hh hdeg theta htheta
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero
        (show IsIntegral Fq theta from IsIntegral.of_finite Fq theta))]
      norm_cast
    contrapose! hQ_deg
    exact hQ_minpoly_deg ▸ Polynomial.degree_le_of_dvd hQ_div_minpoly hQ_deg
  apply (multiset_prod_X_sub_C_injective s t).mp
  exact eq_of_sub_eq_zero hQ_zero

theorem bose_chowla {h : ℕ} (hh : 2 ≤ h)
    (hdeg : Module.finrank Fq Fqh = h) (theta : Fqh)
    (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h)) :
    ∃ a : Fq → {k : ℕ // 0 < k ∧ k < boseChowlaMod (Fq := Fq) h},
      (∀ x : Fq, theta ^ (a x).1 = theta - algebraMap Fq Fqh x) ∧
      (∀ x : Fq, ∀ e : {k : ℕ // 0 < k ∧ k < boseChowlaMod (Fq := Fq) h},
        theta ^ e.1 = theta - algebraMap Fq Fqh x → e = a x) ∧
      (let A : Finset ℕ := Finset.univ.image (fun x : Fq => (a x).1)
       SidonModOfOrder h (boseChowlaMod (Fq := Fq) h) (A : Set ℕ) ∧
          A.card = Fintype.card Fq) := by
  classical
  -- Abbreviation for the repeated exponents call
  let BC := bose_chowla_exponents hh hdeg theta htheta
  let k := fun x : Fq => (BC x).exists.choose
  have hk₁ := fun x => (BC x).exists.choose_spec.1
  have hk₂ := fun x => (BC x).exists.choose_spec.2.1
  have hk₃ := fun x => (BC x).exists.choose_spec.2.2
  refine ⟨fun x => ⟨k x, hk₁ x, hk₂ x⟩,
          fun x => hk₃ x,
          fun x e he => Subtype.ext (ExistsUnique.unique (BC x) ⟨e.2.1, e.2.2, he⟩
            (ExistsUnique.exists (BC x) |> Classical.choose_spec)),
          ?_, ?_⟩
  · intro u v hu hv heq
    obtain ⟨xu, hxu⟩ : ∃ x : Fin h → Fq, ∀ i, u i = k (x i) := by
      choose x hx using hu
      choose g hg using fun i => Finset.mem_image.mp (hx i |>.1)
      exact ⟨g, fun i => hx i |>.2.symm.trans (congr_arg _ (hg i |>.2.symm))⟩
    obtain ⟨xv, hxv⟩ : ∃ y : Fin h → Fq, ∀ i, v i = k (y i) := by
      choose y hy using hv
      choose g hg using fun i => Finset.mem_image.mp (hy i |>.1)
      exact ⟨g, fun i => hy i |>.2.symm.trans (congr_arg _ (hg i |>.2.symm))⟩
    have h_prod_eq :
        (Finset.univ.prod (fun i => theta - algebraMap Fq Fqh (xu i))) =
        (Finset.univ.prod (fun i => theta - algebraMap Fq Fqh (xv i))) := by
      have h_pow_prod :
          (Finset.univ.prod (fun i => theta ^ (BC (xu i)).exists.choose)) =
          (Finset.univ.prod (fun i => theta ^ (BC (xv i)).exists.choose)) := by
        have h_pow_sum :
            (∏ i, theta ^ (BC (xu i)).exists.choose) =
            theta ^ (∑ i, (BC (xu i)).exists.choose) ∧
            (∏ i, theta ^ (BC (xv i)).exists.choose) =
            theta ^ (∑ i, (BC (xv i)).exists.choose) :=
          ⟨by rw [Finset.prod_pow_eq_pow_sum], by rw [Finset.prod_pow_eq_pow_sum]⟩
        simp_all +decide
        norm_cast at *
        rw [ZMod.natCast_eq_natCast_iff] at heq
        rw [← Nat.mod_add_div (∑ i, _) _, ← Nat.mod_add_div (∑ i, _) _, heq]
        · rw [← Nat.mod_add_div (∑ i, _) _]
          · simp +decide [pow_add, pow_mul]
            rw [htheta.pow_eq_one]; norm_num
      convert h_pow_prod using 2 <;>
        have := (BC (xu ‹_›)).exists.choose_spec <;>
        have := (BC (xv ‹_›)).exists.choose_spec <;>
        aesop
    have h_multiset_eq := bose_chowla_poly_identity hh hdeg theta htheta
      (Multiset.ofList (List.ofFn xu)) (Multiset.ofList (List.ofFn xv))
      (by simp +decide) (by simp +decide) (by simp_all +decide [List.prod_ofFn])
    have h_multiset_exp : Multiset.ofList (List.ofFn (fun i => k (xu i))) =
        Multiset.ofList (List.ofFn (fun i => k (xv i))) := by
      convert congr_arg (Multiset.map (fun x : Fq => k x)) h_multiset_eq using 1 <;>
        simp +decide [List.ofFn_eq_map] <;>
        exact List.Perm.map _ (List.Perm.symm <| List.perm_of_nodup_nodup_toFinset_eq
          (List.nodup_finRange _) (List.nodup_finRange _) <| by simp)
    simp_all +decide [List.ofFn_eq_map]
    convert h_multiset_exp.map (fun x : ℕ => (x : ZMod (boseChowlaMod h))) using 1 <;>
      simp +decide [hxu, hxv]
  · rw [Finset.card_image_of_injective _ fun x y hxy => ?_, Finset.card_univ]
    have := hk₃ x; have := hk₃ y; aesop

/-- Sidon of order 2 is equivalent to the standard Sidon definition. -/
lemma SidonOfOrder_two_iff_Sidon {α : Type} [AddCommMonoid α] (S : Set α) :
    SidonOfOrder 2 S ↔ Sidon S := by
  constructor
  · intro h x y z w hx hy hz hw hsum
    specialize h (fun i => if i = 0 then x else y)
      (fun i => if i = 0 then z else w)
    simp_all +decide
    ext a; simpa using h.mem_iff
  · intro h_Sidon u v hu hv h_eq_sum
    have h_eq_set : ({(u 0), (u 1)} : Set α) = ({(v 0), (v 1)} : Set α) :=
      h_Sidon _ _ _ _ (hu 0) (hu 1) (hv 0) (hv 1)
        (by simpa [add_comm] using h_eq_sum)
    simp_all +decide [Set.Subset.antisymm_iff, Set.subset_def]
    rcases h_eq_set with ⟨⟨h₀ | h₀, h₁ | h₁⟩, _, _⟩ <;>
      simp_all +decide [List.Perm.swap]

/-- There exists an irreducible polynomial of degree 2 over any finite field. -/
lemma exists_irreducible_poly_of_degree_two {F : Type*} [Field F] [Fintype F] :
    ∃ f : Polynomial F, Polynomial.natDegree f = 2 ∧ Irreducible f := by
  set q := Fintype.card F with hq_def
  have h_card : 2 ≤ q := Fintype.one_lt_card
  have h_exists_a : ∃ a : F, ¬∃ x : F, x ^ 2 - x = a := by
    by_contra h_contra
    push_neg at h_contra
    have h_surj : Function.Surjective (fun x : F => x ^ 2 - x) := fun x => h_contra x
    have h_inj : Function.Injective (fun x : F => x ^ 2 - x) :=
      Finite.injective_iff_surjective.mpr h_surj
    have := @h_inj 0 1; simp_all +decide
  obtain ⟨a, ha⟩ : ∃ a : F, ¬∃ x : F, x ^ 2 - x = a := h_exists_a
  use Polynomial.X ^ 2 - Polynomial.X - Polynomial.C a
  rw [Polynomial.natDegree_sub_C,
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
  have h_no_roots :
      ¬∃ x : F, Polynomial.eval x
        (Polynomial.X ^ 2 - Polynomial.X - Polynomial.C a) = 0 := by
    simp_all +decide [sub_eq_iff_eq_add]
  have h_irred : ∀ p q : Polynomial F, p.degree > 0 → q.degree > 0 →
      Polynomial.X ^ 2 - Polynomial.X - Polynomial.C a = p * q → False := by
    intros p q hp hq h_factor
    have h_deg : p.degree + q.degree = 2 := by
      rw [← Polynomial.degree_mul, ← h_factor, Polynomial.degree_sub_C] <;>
        rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num
    have h_linear : p.degree = 1 ∧ q.degree = 1 := by
      rw [Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hp),
        Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hq)] at *
      norm_cast at *
      exact ⟨by linarith, by linarith⟩
    exact h_no_roots <| by
      obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one h_linear.1
      exact ⟨x, by aesop⟩
  constructor
  · exact fun h => absurd (Polynomial.degree_eq_zero_of_isUnit h) (by
      erw [Polynomial.degree_sub_C] <;>
        erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num)
  · contrapose! h_irred
    rcases h_irred with ⟨p, q, hpq, hp, hq⟩
    exact ⟨p, q, not_le.mp fun h => hp <|
      Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <|
        le_of_not_gt fun h' => by aesop,
      not_le.mp fun h => hq <| Polynomial.isUnit_iff_degree_eq_zero.mpr <|
        le_antisymm h <| le_of_not_gt fun h' => by aesop, hpq, trivial⟩

/-- For any prime power q, there exists a field extension of degree 2. -/
lemma exists_field_extension_of_degree_two (q : ℕ) (hq : IsPrimePow q) :
    ∃ (Fq Fqh : Type) (_ : Field Fq) (_ : Fintype Fq)
      (_ : Field Fqh) (_ : Fintype Fqh)
      (_ : Algebra Fq Fqh) (_ : FiniteDimensional Fq Fqh),
      Fintype.card Fq = q ∧ Module.finrank Fq Fqh = 2 := by
  -- By definition of prime powers, there exists a finite field Fq with cardinality q.
  obtain ⟨Fq, hFq⟩ : ∃ Fq : Type, ∃ (x : Field Fq) (x_1 : Fintype Fq), Fintype.card Fq = q := by
    obtain ⟨ p, k, hp, hk, rfl ⟩ := hq;
    haveI := Fact.mk hp.nat_prime;
    -- By definition of finite fields, there exists a finite field Fq with cardinality p^k.
    use (GaloisField p k);
    refine' ⟨ _, _, _ ⟩;
    exact inferInstance;
    exact Fintype.ofFinite (GaloisField p k);
    convert GaloisField.card p k;
    simp +decide [ hk.ne', Fintype.card_eq_nat_card ];
  obtain ⟨x, x_1, hx⟩ := hFq;
  -- Let $f(x)$ be an irreducible polynomial of degree 2 over $Fq$.
  obtain ⟨f, hf⟩ : ∃ f : Polynomial Fq, Polynomial.natDegree f = 2 ∧ Irreducible f := by
    exact exists_irreducible_poly_of_degree_two;
  -- Let $Fqh$ be the extension field of $Fq$ obtained by adjoining a root of $f$.
  obtain ⟨Fqh, hFqh⟩ : ∃ Fqh : Type, ∃ (x_3 : Field Fqh) (x_4 : Fintype Fqh) (x_5 : Algebra Fq Fqh), FiniteDimensional Fq Fqh ∧ Module.finrank Fq Fqh = 2 := by
    -- Let $Fqh$ be the extension field of $Fq$ obtained by adjoining a root of $f$. We can construct $Fqh$ as the quotient ring $Fq[x]/(f(x))$.
    use AdjoinRoot f;
    haveI := Fact.mk hf.2;
    refine' ⟨ _, _, _, _, _ ⟩;
    all_goals try infer_instance;
    · convert Fintype.ofFinite ( AdjoinRoot f );
      have h_finite : FiniteDimensional Fq (AdjoinRoot f) := by
        exact FiniteDimensional.of_fintype_basis ( AdjoinRoot.powerBasis hf.2.ne_zero ).basis;
      have h_finite : Finite (AdjoinRoot f) := by
        have h_finite : FiniteDimensional Fq (AdjoinRoot f) := h_finite
        have h_finite : Finite Fq := by
          infer_instance
        (expose_names; exact Module.finite_iff_finite.mp h_finite_1);
      exact h_finite;
    · exact finite_of_finite_type_of_isJacobsonRing Fq (AdjoinRoot f);
    · rw [ Module.finrank_eq_card_basis ( PowerBasis.basis ( AdjoinRoot.powerBasis ( by aesop ) ) ) ] ; aesop;
  exact ⟨ Fq, Fqh, x, x_1, hFqh.choose, hFqh.choose_spec.choose, hFqh.choose_spec.choose_spec.choose, hFqh.choose_spec.choose_spec.choose_spec.1, hx, hFqh.choose_spec.choose_spec.choose_spec.2 ⟩

/-- Bose–Chowla for h=2: for prime power q, exists Sidon set of size q in ZMod(q²-1). -/
theorem bose_chowla_at_h_eq_2 : ∀ q : ℕ, IsPrimePow q →
    ∃ S : Finset (ZMod (q ^ 2 - 1)),
      Sidon (S : Set (ZMod (q ^ 2 - 1))) ∧ S.card = q := by
  intro q hq
  obtain ⟨Fq, Fqh, hFq, hFqh, hFintypeFq, hFintypeFqh, hAlgebra, hFiniteDim,
      hcardFq, hfinrankFqh⟩ := exists_field_extension_of_degree_two q hq
  obtain ⟨theta, htheta⟩ : ∃ theta : Fqh,
      IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) 2) := by
    have h_cyclic : IsCyclic (Fqhˣ) := inferInstance
    obtain ⟨theta, htheta⟩ : ∃ theta : Fqhˣ, orderOf theta = q ^ 2 - 1 := by
      obtain ⟨g, hg⟩ := h_cyclic.exists_generator
      use g
      rw [orderOf_eq_card_of_forall_mem_zpowers hg]
      have h_card : Nat.card Fqh = q ^ 2 := by
        have h_card' : Nat.card Fqh = Nat.card Fq ^ Module.finrank Fq Fqh :=
          Module.natCard_eq_pow_finrank
        aesop
      rw [← h_card, Nat.card_units]
    use theta
    convert htheta ▸ IsPrimitiveRoot.orderOf (theta : Fqhˣ) using 1
    · ext; simp +decide [IsPrimitiveRoot.iff_def, Units.ext_iff]
    · unfold boseChowlaMod; aesop
  have := bose_chowla (by linarith) (by linarith) theta htheta
  obtain ⟨a, ha₁, ha₂, ha₃, ha₄⟩ := this
  refine ⟨Finset.image (fun x : Fq => (a x : ZMod (q ^ 2 - 1))) Finset.univ,
    ?_, ?_⟩
  · convert ha₃ using 1
    rw [← SidonOfOrder_two_iff_Sidon]
    unfold SidonModOfOrder SidonOfOrder; aesop
  · rw [Finset.card_image_of_injective]
    · aesop
    · intro x y hxy
      have h_eq : (a x : ℕ) = (a y : ℕ) := by
        have h_mod : (a x : ℕ) ≡ (a y : ℕ) [MOD (boseChowlaMod (Fq := Fq) 2)] := by
          erw [← ZMod.natCast_eq_natCast_iff]; aesop
        exact Nat.mod_eq_of_lt (a x |>.2.2) ▸
          Nat.mod_eq_of_lt (a y |>.2.2) ▸ h_mod
      have := ha₁ x; aesop

end BoseChowla

section Construction

/-- ZMod equality implies ℕ equality when both values are small. -/
lemma eq_of_zmod_eq_of_lt (M : ℕ) [NeZero M] (a b : ℕ) (ha : a < M) (hb : b < M)
    (h : (a : ZMod M) = (b : ZMod M)) : a = b :=
  (ZMod.val_natCast_of_lt ha).symm.trans ((congrArg ZMod.val h).trans (ZMod.val_natCast_of_lt hb))

/-- ZMod pair equality implies ℕ pair equality when all values are small. -/
lemma set_pair_eq_of_zmod_pair_eq (M : ℕ) [NeZero M] {a b c d : ℕ}
    (ha : a < M) (hb : b < M) (hc : c < M) (hd : d < M)
    (h : ({(a : ZMod M), (b : ZMod M)} : Set (ZMod M)) = {(c : ZMod M), (d : ZMod M)}) :
    ({a, b} : Set ℕ) = {c, d} := by
  rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> apply Set.pair_eq_pair_iff.mpr
  · exact Or.inl ⟨eq_of_zmod_eq_of_lt M a c ha hc h1, eq_of_zmod_eq_of_lt M b d hb hd h2⟩
  · exact Or.inr ⟨eq_of_zmod_eq_of_lt M a d ha hd h1, eq_of_zmod_eq_of_lt M b c hb hc h2⟩

/-- Translate a Sidon set to avoid 0. -/
lemma shift_sidon_mod (M : ℕ) (hM : 1 < M) (S : Finset (ZMod M))
    (hS : Sidon (S : Set (ZMod M))) (hcard : S.card < M) :
    ∃ S' : Finset (ZMod M), Sidon (S' : Set (ZMod M)) ∧
      S'.card = S.card ∧ (0 : ZMod M) ∉ S' := by
  classical
  haveI : Fact (1 < M) := ⟨hM⟩
  have ⟨x, hx⟩ : ∃ x : ZMod M, x ∉ S := by
    by_contra h; push_neg at h
    simp [Finset.eq_univ_iff_forall.mpr h, ZMod.card M] at hcard
  let S' := S.image (· - x)
  have hinj : Function.Injective (fun y : ZMod M => y - x) := sub_left_injective
  refine ⟨S', ?_, Finset.card_image_of_injective S hinj, ?_⟩
  · intro a b c d ha hb hc hd habcd
    have hmem : ∀ z, z ∈ S' → z + x ∈ (S : Set _) := fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz; simp [hy]
    have hEq := hS _ _ _ _ (hmem a ha) (hmem b hb) (hmem c hc) (hmem d hd)
      (by linear_combination habcd)
    have h1 : (· - x) '' ({a + x, b + x} : Set _) = {a, b} := by
      simp only [Set.image_insert_eq, Set.image_singleton, add_sub_cancel_right]
    have h2 : (· - x) '' ({c + x, d + x} : Set _) = {c, d} := by
      simp only [Set.image_insert_eq, Set.image_singleton, add_sub_cancel_right]
    rw [← h1, ← h2, Set.image_eq_image hinj]; exact hEq
  · intro h0; obtain ⟨y, hyS, hy0⟩ := Finset.mem_image.1 h0
    exact hx (sub_eq_zero.mp hy0 ▸ hyS)

/-- Lift a Sidon set from ZMod M to naturals. -/
lemma lift_sidon_mod (M : ℕ) (hM : 1 < M) (S : Finset (ZMod M))
    (hS : Sidon (S : Set (ZMod M))) (h0 : (0 : ZMod M) ∉ S) :
    ∃ S_nat : Finset ℕ, SidonMod M (S_nat : Set ℕ) ∧ S_nat.card = S.card ∧
      (S_nat : Set ℕ) ⊆ Finset.Icc 1 (M - 1) ∧ S_nat = S.image ZMod.val := by
  classical
  haveI : NeZero M := ⟨by linarith⟩
  have hinj : Function.Injective (ZMod.val : ZMod M → ℕ) := ZMod.val_injective M
  refine ⟨S.image ZMod.val, ?_, Finset.card_image_of_injective S hinj, ?_, rfl⟩
  · intro a b c d ha hb hc hd habcd
    obtain ⟨na, hna, rfl⟩ := ha; obtain ⟨nb, hnb, rfl⟩ := hb
    obtain ⟨nc, hnc, rfl⟩ := hc; obtain ⟨nd, hnd, rfl⟩ := hd
    obtain ⟨za, hza, rfl⟩ := Finset.mem_image.1 hna; obtain ⟨zb, hzb, rfl⟩ := Finset.mem_image.1 hnb
    obtain ⟨zc, hzc, rfl⟩ := Finset.mem_image.1 hnc; obtain ⟨zd, hzd, rfl⟩ := Finset.mem_image.1 hnd
    simp only [ZMod.natCast_zmod_val] at habcd ⊢
    exact hS za zb zc zd hza hzb hzc hzd habcd
  · intro n hn
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.1 hn
    have hx0 : x.val ≠ 0 := fun h => h0 ((ZMod.val_eq_zero x).1 h ▸ hxS)
    exact Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero hx0, Nat.le_pred_of_lt (ZMod.val_lt x)⟩

end Construction

/-
Every Sidon set S ⊆ [N] is contained in some maximal Sidon set M ⊆ [N].
-/
def MaximalSidonSubset (U : Finset ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ U ∧ Sidon (S : Set ℕ) ∧ ∀ S' : Finset ℕ, S' ⊆ U → Sidon (S' : Set ℕ) → S ⊆ S' → S = S'

lemma lem_extend (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) (hSidon : Sidon (S : Set ℕ)) :
    ∃ M, MaximalSidonSubset (Finset.range N) M ∧ S ⊆ M := by
      -- By definition of maximal Sidon subset, there exists a maximal Sidon subset $M$ of $Finset.range N$ such that $S \subseteq M$.
      have h_max : ∃ M : Finset ℕ, S ⊆ M ∧ Sidon (M : Set ℕ) ∧ M ⊆ Finset.range N ∧ ∀ M' : Finset ℕ, Sidon (M' : Set ℕ) → M ⊆ M' → M' ⊆ Finset.range N → M = M' := by
        -- Apply the definition of maximalSidonSubset to obtain such an M.
        obtain ⟨M, hM⟩ : ∃ M ∈ {M : Finset ℕ | S ⊆ M ∧ Sidon (M : Set ℕ) ∧ M ⊆ Finset.range N}, ∀ M' ∈ {M : Finset ℕ | S ⊆ M ∧ Sidon (M : Set ℕ) ∧ M ⊆ Finset.range N}, M.card ≥ M'.card := by
          apply_rules [ Set.exists_max_image ];
          · exact Set.finite_iff_bddAbove.mpr ⟨ Finset.range N, fun M hM => Finset.le_iff_subset.mpr hM.2.2 ⟩;
          · exact ⟨ S, ⟨ Finset.Subset.refl _, hSidon, hS ⟩ ⟩;
        refine' ⟨ M, hM.1.1, hM.1.2.1, hM.1.2.2, fun M' hM' hM'' hM''' => _ ⟩;
        exact Finset.eq_of_subset_of_card_le hM'' ( by linarith [ hM.2 M' ⟨ Finset.Subset.trans hM.1.1 hM'', hM', hM''' ⟩ ] );
      obtain ⟨ M, hM₁, hM₂, hM₃, hM₄ ⟩ := h_max; use M; unfold MaximalSidonSubset; aesop;

/-
Let A(N) denote the number of Sidon subsets of [N], and let A_1(N) denote the number of maximal Sidon subsets of [N].
-/
open Classical

noncomputable def A (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => Sidon (S : Set ℕ))).card

noncomputable def A1 (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => MaximalSidonSubset (Finset.range N) S)).card

set_option maxHeartbeats 0 in
/-
For every N >= 1, A(N) <= A_1(N) * 2^(f(N)).
-/
lemma lem_cover (N : ℕ) : (A N : ℝ) ≤ (A1 N : ℝ) * (2 : ℝ) ^ (f N : ℝ) := by
  -- Every Sidon set is contained in at least one maximal Sidon set.
  have h_contained : ∀ S ∈ Finset.filter (fun S => Sidon (S : Set ℕ)) (Finset.powerset (Finset.range N)), ∃ M ∈ Finset.filter (fun S => MaximalSidonSubset (Finset.range N) S) (Finset.powerset (Finset.range N)), S ⊆ M := by
    intro S hS;
    -- By Lemma~\ref{lem:extend}, every Sidon set is contained in at least one maximal Sidon set. Let's obtain such a maximal Sidon set $M$.
    obtain ⟨M, hM⟩ : ∃ M : Finset ℕ, MaximalSidonSubset (Finset.range N) M ∧ S ⊆ M := by
      have hS_finset : ∃ S' : Finset ℕ, S' ⊆ Finset.range N ∧ S = S' := by
        aesop
      obtain ⟨ S', hS'_subset, rfl ⟩ := hS_finset; exact lem_extend N S' hS'_subset ( by aesop ) |> fun ⟨ M, hM₁, hM₂ ⟩ => ⟨ M, hM₁, hM₂ ⟩ ;
    exact ⟨ M, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hM.1.1, hM.1 ⟩, hM.2 ⟩;
  -- Since $\abs{M}\le f(N)$, the family of all Sidon sets is contained in the union
  -- of the families of subsets of maximal Sidon sets, hence
  have h_union : Finset.filter (fun S => Sidon (S : Set ℕ)) (Finset.powerset (Finset.range N)) ⊆ Finset.biUnion (Finset.filter (fun S => MaximalSidonSubset (Finset.range N) S) (Finset.powerset (Finset.range N))) (fun M => Finset.powerset M) := by
    intro S hS; specialize h_contained S hS; aesop;
  -- Since $\abs{M}\le f(N)$, each maximal Sidon set $M$ contains at most $2^{f(N)}$ Sidon subsets.
  have h_max_subset : ∀ M ∈ Finset.filter (fun S => MaximalSidonSubset (Finset.range N) S) (Finset.powerset (Finset.range N)), (Finset.powerset M).card ≤ 2 ^ (f N : ℕ) := by
    -- Since $\abs{M}\le f(N)$, each maximal Sidon set $M$ contains at most $2^{f(N)}$ subsets.
    intros M hM
    have h_card_M : M.card ≤ f N := by
      refine' le_trans _ ( Finset.le_sup <| show M.image ( fun x => x + 1 ) ∈ _ from _ );
      · rw [ Finset.card_image_of_injective _ Nat.succ_injective ];
      · simp_all +decide [ Finset.subset_iff, MaximalSidonSubset ];
        refine' ⟨ fun x hx => Nat.succ_le_of_lt ( hM.1 hx ), _ ⟩;
        intro a b c d ha hb hc hd habcd; obtain ⟨ x, hx, rfl ⟩ := ha; obtain ⟨ y, hy, rfl ⟩ := hb; obtain ⟨ z, hz, rfl ⟩ := hc; obtain ⟨ w, hw, rfl ⟩ := hd; simp_all +decide [ Sidon ] ;
        convert congr_arg ( fun s : Set ℕ => s.image ( fun n => n + 1 ) ) ( hM.2.1 x y z w hx hy hz hw ( by linarith ) ) using 1 <;> ext <;> simp +decide
        · tauto;
        · tauto
    simp
    exact pow_le_pow_right₀ ( by decide ) h_card_M;
  have h_card_union : (Finset.filter (fun S => Sidon (S : Set ℕ)) (Finset.powerset (Finset.range N))).card ≤ (Finset.filter (fun S => MaximalSidonSubset (Finset.range N) S) (Finset.powerset (Finset.range N))).card * 2 ^ (f N : ℕ) := by
    refine le_trans ( Finset.card_le_card h_union ) ?_;
    refine' le_trans ( Finset.card_biUnion_le ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => show Finset.card _ ≤ 2 ^ f N from _ ) _;
    · convert h_max_subset x hx using 1;
      convert Finset.card_image_of_injective _ Finset.coe_injective;
      ext; simp [Finset.mem_image];
    · norm_num [ Finset.sum_const ];
  norm_cast

/-
For every N >= 1, A_1(N) >= A(N) * 2^(-f(N)).
-/
lemma cor_ratio (N : ℕ) : (A1 N : ℝ) ≥ (A N : ℝ) * (2 : ℝ) ^ (-(f N : ℝ)) := by
  have := @lem_cover N;
  norm_num [ Real.rpow_neg ] at *;
  rwa [ ← div_eq_mul_inv, div_le_iff₀ ( by positivity ) ]

/-
Let p be prime, and let g be a generator of the multiplicative group F_p^x.
In the abelian group G := Z_{p-1} x Z_p, define S := {(i, g^i) : i in Z_{p-1}}.
Then S is Sidon in G.
-/
def ruzsa_set (p : ℕ) (g : ZMod p) : Finset (ZMod (p - 1) × ZMod p) :=
  (Finset.range (p - 1)).image (fun (i : ℕ) => ((i : ZMod (p - 1)), g ^ i))

lemma lem_ruzsa_group (p : ℕ) (hp : p.Prime) (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) :
    Sidon (ruzsa_set p g : Set (ZMod (p - 1) × ZMod p)) := by
      intro a b c d;
      simp [ruzsa_set];
      rintro x hx rfl y hy rfl z hz rfl w hw rfl h; haveI := Fact.mk hp; simp_all +decide
      -- Since $g$ is a generator of the multiplicative group modulo $p$, we have $g^{i_1}g^{i_2} \equiv g^{i_3}g^{i_4} \pmod{p}$.
      have h_prod : g ^ x * g ^ y = g ^ z * g ^ w := by
        have h_exp : (x + y : ℕ) ≡ (z + w : ℕ) [MOD (p - 1)] := by
          haveI := Fact.mk hp; rw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
        rw [ ← pow_add, ← pow_add, ← Nat.mod_add_div ( x + y ) ( p - 1 ), ← Nat.mod_add_div ( z + w ) ( p - 1 ), h_exp ];
        simp +decide [ pow_add, pow_mul, hg.pow_eq_one ];
      -- Since $g$ is a generator of the multiplicative group modulo $p$, we have $g^{i_1}g^{i_2} \equiv g^{i_3}g^{i_4} \pmod{p}$ implies $g^{i_1} = g^{i_3}$ and $g^{i_2} = g^{i_4}$ or $g^{i_1} = g^{i_4}$ and $g^{i_2} = g^{i_3}$.
      have h_cases : g ^ x = g ^ z ∧ g ^ y = g ^ w ∨ g ^ x = g ^ w ∧ g ^ y = g ^ z := by
        have h_cases : (g ^ x - g ^ z) * (g ^ y - g ^ z) = 0 := by
          grind +ring;
        haveI := Fact.mk hp; simp_all +decide [ sub_eq_iff_eq_add ] ;
        grind;
      cases h_cases <;> simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
      · have := hg.pow_inj ( by linarith : x < p - 1 ) ( by linarith : z < p - 1 ) ; have := hg.pow_inj ( by linarith : y < p - 1 ) ( by linarith : w < p - 1 ) ; aesop;
      · have := hg.pow_inj ( by linarith : x < p - 1 ) ( by linarith : w < p - 1 ) ; have := hg.pow_inj ( by linarith : y < p - 1 ) ( by linarith : z < p - 1 ) ; simp_all +decide [ add_comm ] ;

/-
Let p be prime and set m := p(p-1). There exists a set T in Z_m with |T| = p-1 such that T is a Sidon set modulo m.
-/
lemma lem_modular (p : ℕ) (hp : p.Prime) :
    ∃ T : Finset (ZMod (p * (p - 1))), T.card = p - 1 ∧ Sidon (T : Set (ZMod (p * (p - 1)))) := by
      -- Let $g$ be a generator of the multiplicative group of integers modulo $p$.
      obtain ⟨g, hg⟩ : ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) := by
        haveI := Fact.mk hp;
        exact HasEnoughRootsOfUnity.prim;
      -- By Lemma 4.1, the set $S = \{(i, g^i) : i \in \mathbb{Z}_{p-1}\}$ is Sidon in the group $G = \mathbb{Z}_{p-1} \times \mathbb{Z}_p$.
      have h_Sidon_S : Sidon (ruzsa_set p g : Set (ZMod (p - 1) × ZMod p)) := by
        convert lem_ruzsa_group p hp g hg;
      -- Since $\gcd(p, p-1) = 1$, the Chinese Remainder Theorem gives a group isomorphism $\mathbb{Z}_{p-1} \times \mathbb{Z}_p \cong \mathbb{Z}_m$.
      have h_iso : Nonempty (ZMod (p - 1) × ZMod p ≃+ ZMod (p * (p - 1))) := by
        have h_iso : Nonempty (ZMod (p - 1) × ZMod p ≃+ ZMod ((p - 1) * p)) := by
          have h_coprime : Nat.gcd (p - 1) p = 1 := by
            simp +decide [ hp.one_lt.le ]
          refine' ⟨ _ ⟩;
          exact ( ZMod.chineseRemainder h_coprime ).toAddEquiv.symm
        generalize_proofs at *;
        rwa [ Nat.mul_comm ] at h_iso;
      obtain ⟨ f ⟩ := h_iso;
      refine' ⟨ Finset.image ( fun x : ZMod ( p - 1 ) × ZMod p => f x ) ( ruzsa_set p g ), _, _ ⟩ <;> simp_all +decide [ Sidon ];
      · rw [ Finset.card_image_of_injective _ f.injective, Finset.card_eq_of_bijective ];
        use fun i hi => ( i, g ^ i );
        · unfold ruzsa_set; aesop;
        · exact fun i hi => Finset.mem_image.mpr ⟨ i, Finset.mem_range.mpr hi, rfl ⟩;
        · simp +contextual [ ZMod.natCast_eq_natCast_iff' ];
          exact fun i j hi hj hij h => Nat.mod_eq_of_lt hi ▸ Nat.mod_eq_of_lt hj ▸ hij ▸ rfl;
      · intro a b c d x y hx hy z t hz ht u v hu hv w x' hw hx' habcd; have := f.injective; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
        specialize h_Sidon_S x y z t u v w x' hx hz hu hw ; simp_all +decide [ ← hy, ← ht, ← hv, ← hx', ← map_add ] ;

/-
S_chi is a subset of [4m].
-/
def S_chi (m : ℕ) (T : Finset ℕ) (chi : {x // x ∈ T} → Fin 5) : Finset ℕ :=
  (T.attach.filter (fun t => chi t ≠ 0)).image (fun t => t.val + ((chi t).val - 1) * m)

lemma S_chi_subset (m : ℕ) (hm : m ≥ 1) (T : Finset ℕ) (hT : T ⊆ Finset.range m)
    (chi : {x // x ∈ T} → Fin 5) :
    S_chi m T chi ⊆ Finset.range (4 * m) := by
      rintro x hx;
      obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx;
      have := Finset.mem_range.mp ( hT y.2 ) ; rcases x : ( chi y : Fin 5 ) with ( _ | _ | _ | _ | _ | k ) <;> simp_all +decide ; linarith;
      · grind;
      · linarith;
      · grind;
      · linarith

/-
S_chi is a Sidon set.
-/
lemma S_chi_is_Sidon (m : ℕ) (hm : m ≥ 1) (T : Finset ℕ) (hT : T ⊆ Finset.range m)
    (hSidon : SidonMod m (T : Set ℕ)) (chi : {x // x ∈ T} → Fin 5) :
    Sidon (S_chi m T chi : Set ℕ) := by
      intro a ha b hb c hc d hd habcd;
      -- By definition of $S_\chi$, there exist $t_a, t_b, t_c, t_d \in T$ such that $a = t_a + (\chi(t_a)-1)m$, $b = t_b + (\chi(t_b)-1)m$, $c = t_c + (\chi(t_c)-1)m$, and $d = t_d + (\chi(t_d)-1)m$.
      obtain ⟨ta, hta, ha_eq⟩ : ∃ ta : T, a = ta.val + ((chi ta).val - 1) * m := by
        unfold S_chi at c; aesop;
      obtain ⟨tb, htb, hb_eq⟩ : ∃ tb : T, ha = tb.val + ((chi tb).val - 1) * m := by
        unfold S_chi at hc; aesop;
      obtain ⟨tc, htc, hc_eq⟩ : ∃ tc : T, b = tc.val + ((chi tc).val - 1) * m := by
        unfold S_chi at d; aesop;
      obtain ⟨td, htd, hd_eq⟩ : ∃ td : T, hb = td.val + ((chi td).val - 1) * m := by
        unfold S_chi at hd; aesop;
      -- Since $T$ is Sidon modulo $m$, we have $\{t_a, t_b\} = \{t_c, t_d\}$ as multisets in $Z_m$.
      have h_multiset_eq : ({(ta : ℕ), (tb : ℕ)} : Set ℕ) = ({(tc : ℕ), (td : ℕ)} : Set ℕ) := by
        have h_multiset_eq : ({(ta : ZMod m), (tb : ZMod m)} : Set (ZMod m)) = ({(tc : ZMod m), (td : ZMod m)} : Set (ZMod m)) := by
          replace habcd := congr_arg ( ( ↑ ) : ℕ → ZMod m ) habcd ; aesop;
        convert set_pair_eq_of_zmod_pair_eq m _ _ _ _ h_multiset_eq using 1;
        · exact ⟨ by linarith ⟩;
        · exact Finset.mem_range.mp ( hT ta.2 );
        · exact Finset.mem_range.mp ( hT tb.2 );
        · exact Finset.mem_range.mp ( hT tc.2 );
        · exact Finset.mem_range.mp ( hT td.2 );
      grind

/-
The map chi -> S_chi is injective.
-/
lemma S_chi_injective (m : ℕ) (hm : m ≥ 1) (T : Finset ℕ) (hT : T ⊆ Finset.range m) :
    Function.Injective (S_chi m T) := by
      -- If $S_{\chi_1} = S_{\chi_2}$, then for every $t \in T$, $\chi_1(t) = \chi_2(t)$.
      intros chi1 chi2 h_eq
      have h_eq_values : ∀ t : T, chi1 t ≠ 0 → chi2 t ≠ 0 → chi1 t = chi2 t := by
        intro t ht1 ht2
        have h_eq_t : t.val + ((chi1 t).val - 1) * m ∈ S_chi m T chi2 := by
          exact h_eq ▸ Finset.mem_image.mpr ⟨ t, Finset.mem_filter.mpr ⟨ Finset.mem_attach _ _, ht1 ⟩, rfl ⟩;
        -- Since $t$ is in $T$, we know that $t.val < m$.
        have h_t_val_lt_m : t.val < m := by
          exact Finset.mem_range.mp ( hT t.2 );
        -- Since $t$ is in $T$, we know that $t.val < m$, so we can write $t.val + ((chi1 t).val - 1) * m = t.val + ((chi2 t).val - 1) * m + k * m$ for some integer $k$.
        obtain ⟨t', ht', ht'_eq⟩ : ∃ t' : T, t'.val = t.val ∧ ((chi1 t).val - 1) = ((chi2 t').val - 1) := by
          obtain ⟨ t', ht', ht'_eq ⟩ := Finset.mem_image.mp h_eq_t;
          have := congr_arg ( · % m ) ht'_eq; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt h_t_val_lt_m, Nat.mod_eq_of_lt ( show ( t' : ℕ ) < m from Finset.mem_range.mp ( hT t'.2 ) ) ] at this; aesop;
        grind;
      ext t; specialize h_eq_values t; by_cases h1 : chi1 t = 0 <;> by_cases h2 : chi2 t = 0 <;> simp_all +decide [ Finset.ext_iff ] ;
      · contrapose! h_eq; simp_all +decide [ S_chi ] ;
        refine' ⟨ _, Or.inr ⟨ _, t, t.2, h2, rfl ⟩ ⟩;
        intro x hx hx' H; have := congr_arg ( · % m ) H; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ( show x < m from Finset.mem_range.mp ( hT hx ) ), Nat.mod_eq_of_lt ( show ( t : ℕ ) < m from Finset.mem_range.mp ( hT t.2 ) ) ] at this;
        cases t ; aesop;
      · contrapose! h_eq;
        refine' ⟨ _, Or.inl ⟨ Finset.mem_image.mpr ⟨ t, Finset.mem_filter.mpr ⟨ Finset.mem_attach _ _, h1 ⟩, rfl ⟩, _ ⟩ ⟩ ; simp_all +decide [ S_chi ];
        intro x hx hx' H; have := congr_arg ( · % m ) H; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ( show t.val < m from Finset.mem_range.mp ( hT t.2 ) ), Nat.mod_eq_of_lt ( show x < m from Finset.mem_range.mp ( hT hx ) ) ] at this;
        cases t ; aesop

/-
A(4m) >= 5^|T|.
-/
lemma lem_four_block (m : ℕ) (hm : m ≥ 1) (T : Finset ℕ) (hT : T ⊆ Finset.range m)
    (hSidon : SidonMod m (T : Set ℕ)) :
    A (4 * m) ≥ 5 ^ T.card := by
      have hA_ge : Set.ncard (Set.image (fun f : { x // x ∈ T } → Fin 5 => S_chi m T f) (Set.univ : Set (_ → Fin 5))) ≥ 5 ^ T.card := by
        rw [ Set.ncard_image_of_injective _ ( S_chi_injective m hm T hT ), Set.ncard_univ ] ; norm_num [ Set.ncard_eq_toFinset_card' ] ;
      refine' le_trans hA_ge _;
      have h_image_subset : Set.image (fun f : { x // x ∈ T } → Fin 5 => S_chi m T f) (Set.univ : Set (_ → Fin 5)) ⊆ {S : Finset ℕ | S ⊆ Finset.range (4 * m) ∧ Sidon (S : Set ℕ)} := by
        intro S hSaesop;
        obtain ⟨ f, _, rfl ⟩ := hSaesop; exact ⟨ S_chi_subset m hm T hT f, S_chi_is_Sidon m hm T hT hSidon f ⟩ ;
      have h_card_image : Set.ncard {S : Finset ℕ | S ⊆ Finset.range (4 * m) ∧ Sidon (S : Set ℕ)} ≤ (Finset.powerset (Finset.range (4 * m)) |>.filter (fun S => Sidon (S : Set ℕ))).card := by
        convert Set.ncard_coe_finset _ |> le_of_eq;
        any_goals exact Finset.filter ( fun S => Sidon ( S : Set ℕ ) ) ( Finset.powerset ( Finset.range ( 4 * m ) ) );
        · aesop;
        · refine' Finset.card_bij _ _ _ _;
          use fun S hS => Finset.filter ( fun x => x ∈ S ) ( Finset.range ( 4 * m ) );
          · simp +contextual [ Finset.subset_iff ];
            intro a ha hSidon x y z w hx hy hz hw h; specialize hSidon x y z w; aesop;
          · simp +contextual [ Finset.ext_iff, Set.ext_iff ];
            grind;
          · simp +zetaDelta at *;
            grind;
      refine le_trans ?_ h_card_image;
      apply_rules [ Set.ncard_le_ncard ];
      exact Set.finite_iff_bddAbove.mpr ⟨ Finset.range ( 4 * m ), fun S hS => Finset.subset_iff.mpr hS.1 ⟩

/-
Let p be prime. Then A(4p(p-1)) >= 5^(p-1).
-/
lemma prop_lower_special_ineq (p : ℕ) (hp : p.Prime) :
    A (4 * p * (p - 1)) ≥ 5 ^ (p - 1) := by
      have := lem_modular p hp;
      -- Let $T$ be a Sidon set modulo $m = p(p-1)$ with $|T| = p-1$.
      obtain ⟨T, hT_card, hT_sidon⟩ := this;
      -- Let $T$ be a Sidon set modulo $m = p(p-1)$ with $|T| = p-1$. We can lift $T$ to a Sidon set $T'$ in $\mathbb{N}$.
      obtain ⟨T', hT'_card, hT'_sidon⟩ : ∃ T' : Finset ℕ, T'.card = p - 1 ∧ SidonMod (p * (p - 1)) (T' : Set ℕ) ∧ (T' : Set ℕ) ⊆ Finset.Icc 1 (p * (p - 1) - 1) := by
        -- Apply the shift_sidon_mod lemma to obtain a Sidon set $T'$ in $\mathbb{N}$ with the desired properties.
        obtain ⟨T', hT'_card, hT'_sidon, hT'_subset⟩ : ∃ T' : Finset (ZMod (p * (p - 1))), T'.card = p - 1 ∧ Sidon (T' : Set (ZMod (p * (p - 1)))) ∧ (0 : ZMod (p * (p - 1))) ∉ T' := by
          have := shift_sidon_mod ( p * ( p - 1 ) ) ( by nlinarith [ hp.two_le, Nat.sub_pos_of_lt hp.one_lt ] ) T hT_sidon ( by nlinarith [ hp.two_le, Nat.sub_pos_of_lt hp.one_lt ] );
          grind +ring;
        have := @lift_sidon_mod ( p * ( p - 1 ) ) ?_ T' hT'_sidon hT'_subset;
        · aesop;
        · rcases p with ( _ | _ | p ) <;> simp_all +decide;
          nlinarith only [ hp.two_le ];
      have := @lem_four_block ( p * ( p - 1 ) ) ?_ T' ?_ ?_ <;> simp_all +decide [ mul_assoc ];
      · exact Nat.mul_pos hp.pos ( Nat.sub_pos_of_lt hp.one_lt );
      · exact fun x hx => Finset.mem_range.mpr ( lt_of_le_of_lt ( hT'_sidon.2 hx |>.2 ) ( Nat.pred_lt ( ne_bot_of_gt ( Nat.mul_pos hp.pos ( Nat.sub_pos_of_lt hp.one_lt ) ) ) ) )

/-
For every fixed epsilon in (0,1) and all sufficiently large x, the interval ((1-epsilon)x, x] contains a prime.
-/
lemma lem_prime_near (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    ∀ᶠ x : ℝ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * x < p ∧ p ≤ x := by
      -- By the Prime Number Theorem, there exists a prime $p$ in the interval $(x, (1 + \epsilon)x)$ for sufficiently large $x$.
      have h_prime_between : ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
        convert prime_between hε.1 using 1;
      -- Let $y = (1 - \epsilon)x$. Then $(1 + \delta)y = (1 + \frac{\epsilon}{1-\epsilon})(1-\epsilon)x = x$.
      have := h_prime_between;
      norm_num at *;
      obtain ⟨ a, ha ⟩ := this; use ( a : ℝ ) / ( 1 - ε ) ; intro b hb; obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := ha ( ( 1 - ε ) * b ) ( by nlinarith [ mul_div_cancel₀ ( a : ℝ ) ( by linarith : ( 1 - ε ) ≠ 0 ) ] ) ; exact ⟨ p, hp₁, by nlinarith, by nlinarith ⟩ ;

/-
A(N) is monotonically increasing.
-/
lemma A_mono {N M : ℕ} (h : N ≤ M) : A N ≤ A M := by
  -- By definition of $A$, we know that every Sidon subset of $[N]$ is also a subset of $[M]$.
  have h_subset : ∀ S : Finset ℕ, S ⊆ Finset.range N → Sidon (S : Set ℕ) → S ⊆ Finset.range M := by
    exact fun S hS hSidon => Finset.Subset.trans hS ( Finset.range_mono h );
  refine' Finset.card_le_card _;
  intro S hS; aesop;

/-
For any c < 1/2 log 5, eventually log A(N) / sqrt N >= c.
-/
lemma eventually_lower_bound (c : ℝ) (hc : c < Real.log 5 / 2) :
    ∀ᶠ N : ℕ in Filter.atTop, Real.log (A N : ℝ) / Real.sqrt N ≥ c := by
      -- Since $c < \frac{1}{2}\log 5$, we can choose $\varepsilon > 0$ such that $c < (1-\varepsilon)\frac{1}{2}\log 5$.
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, c < (1 - ε) * (Real.log 5 / 2) := by
        exact ⟨ ( 1 - c / ( Real.log 5 / 2 ) ) / 2, by nlinarith [ Real.log_pos ( show ( 5 : ℝ ) > 1 by norm_num ), mul_div_cancel₀ c ( ne_of_gt ( by positivity : 0 < Real.log 5 / 2 ) ) ], by nlinarith [ Real.log_pos ( show ( 5 : ℝ ) > 1 by norm_num ), mul_div_cancel₀ c ( ne_of_gt ( by positivity : 0 < Real.log 5 / 2 ) ) ] ⟩;
      -- For large $N$, let $x = \frac{1}{2}\sqrt{N}$. By `lem_prime_near`, there exists a prime $p \in ((1-\varepsilon)x, x]$.
      have h_prime : ∀ᶠ N : ℕ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * (1 / 2) * Real.sqrt N < p ∧ p ≤ (1 / 2) * Real.sqrt N := by
        have h_prime : ∀ᶠ x : ℝ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * x < p ∧ p ≤ x := by
          by_cases hε_lt_1 : ε < 1;
          · convert lem_prime_near ε ⟨ hε_pos, hε_lt_1 ⟩ using 1;
          · exact Filter.eventually_atTop.mpr ⟨ 2, fun x hx => ⟨ 2, by norm_num, by norm_num; nlinarith [ Real.log_pos ( show 5 > 1 by norm_num ) ], by norm_num; linarith ⟩ ⟩;
        rw [ Filter.eventually_atTop ] at *;
        obtain ⟨ a, ha ⟩ := h_prime; use Nat.ceil ( a ^ 2 * 4 ) ; intro b hb; obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := ha ( Real.sqrt b / 2 ) ( by nlinarith [ Nat.ceil_le.mp hb, Real.sqrt_nonneg b, Real.sq_sqrt ( Nat.cast_nonneg b ) ] ) ; exact ⟨ p, hp₁, by nlinarith [ Real.sqrt_nonneg b, Real.sq_sqrt ( Nat.cast_nonneg b ) ], by nlinarith [ Real.sqrt_nonneg b, Real.sq_sqrt ( Nat.cast_nonneg b ) ] ⟩ ;
      -- Let $N_p = 4p(p-1)$. Then $N_p \le 4x^2 = N$.
      have h_Np : ∀ᶠ N : ℕ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * (1 / 2) * Real.sqrt N < p ∧ p ≤ (1 / 2) * Real.sqrt N ∧ 4 * p * (p - 1) ≤ N := by
        filter_upwards [ h_prime, Filter.eventually_gt_atTop 0 ] with N hN hN' ; rcases hN with ⟨ p, hp₁, hp₂, hp₃ ⟩ ; refine' ⟨ p, hp₁, hp₂, hp₃, _ ⟩ ; rcases p with ( _ | _ | p ) <;> norm_num at *;
        exact_mod_cast ( by nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg N ) ] : ( 4 : ℝ ) * ( p + 1 + 1 ) * ( p + 1 ) ≤ N );
      -- By monotonicity (`A_mono`), $A(N) \ge A(N_p)$.
      have h_monotone : ∀ᶠ N : ℕ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * (1 / 2) * Real.sqrt N < p ∧ p ≤ (1 / 2) * Real.sqrt N ∧ 4 * p * (p - 1) ≤ N ∧ (A N : ℝ) ≥ 5 ^ (p - 1) := by
        filter_upwards [ h_Np ] with N hN;
        obtain ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ := hN; exact ⟨ p, hp₁, hp₂, hp₃, hp₄, by exact_mod_cast le_trans ( prop_lower_special_ineq p hp₁ ) ( A_mono ( by linarith ) ) ⟩ ;
      -- So $\frac{\log A(N)}{\sqrt{N}} > \frac{((1-\varepsilon)\frac{1}{2}\sqrt{N} - 1)\log 5}{\sqrt{N}} = \frac{1-\varepsilon}{2}\log 5 - \frac{\log 5}{\sqrt{N}}$.
      have h_bound : ∀ᶠ N : ℕ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * (1 / 2) * Real.sqrt N < p ∧ p ≤ (1 / 2) * Real.sqrt N ∧ 4 * p * (p - 1) ≤ N ∧ (Real.log (A N)) / Real.sqrt N ≥ ((1 - ε) / 2) * Real.log 5 - Real.log 5 / Real.sqrt N := by
        field_simp;
        filter_upwards [ h_monotone, Filter.eventually_gt_atTop 0 ] with N hN hN' ; rcases hN with ⟨ p, hp₁, hp₂, hp₃, hp₄, hp₅ ⟩ ; refine' ⟨ p, hp₁, _, _, hp₄, _ ⟩ <;> try linarith;
        -- Using the fact that $A(N) \geq 5^{p-1}$, we have $\log A(N) \geq (p-1) \log 5$.
        have h_log_bound : Real.log (A N) ≥ (p - 1) * Real.log 5 := by
          rcases p with ( _ | _ | p ) <;> norm_num at *;
          simpa using Real.log_le_log ( by positivity ) hp₅;
        rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr hN' ) ) ] ; nlinarith [ Real.sqrt_nonneg N, Real.sq_sqrt ( Nat.cast_nonneg N ), Real.log_pos ( show ( 5 : ℝ ) > 1 by norm_num ), mul_div_cancel₀ ( 2 : ℝ ) ( ne_of_gt ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr hN' ) ) ) ] ;
      -- As $N \to \infty$, the term $\frac{\log 5}{\sqrt{N}}$ tends to $0$.
      have h_log_div_sqrt : Filter.Tendsto (fun N : ℕ => Real.log 5 / Real.sqrt N) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul ( tendsto_inverse_atTop_nhds_zero_nat.sqrt );
      filter_upwards [ h_bound, h_log_div_sqrt.eventually ( gt_mem_nhds <| show 0 < ( 1 - ε ) * ( Real.log 5 / 2 ) - c by linarith ) ] with N hN₁ hN₂ using by obtain ⟨ p, hp₁, hp₂, hp₃, hp₄, hp₅ ⟩ := hN₁; linarith;

/-
Assume the prime number theorem, and assume the standard extremal bound f(N)=(1+o(1))sqrt(N). Then log A_1(N) >= (eta + o(1))sqrt(N).
-/
noncomputable def eta : ℝ := 1 / 2 * Real.log (5 / 4)

theorem thm_main (h_f : Filter.Tendsto (fun N => (f N : ℝ) / Real.sqrt N) Filter.atTop (nhds 1)) :
    ∀ c < eta, ∀ᶠ N : ℕ in Filter.atTop, Real.log (A1 N : ℝ) / Real.sqrt N ≥ c := by
      field_simp;
      -- By definition of eta, we have eta = log(5 / 4) / 2.
      have h_eta : eta = Real.log (5 / 4) / 2 := by
        unfold eta; norm_num; ring;
      -- By definition of $A1$, we know that $A1(N) \geq A(N) \cdot 2^{-f(N)}$.
      have h_A1_lower_bound : ∀ N, A1 N ≥ A N * (2 : ℝ) ^ (-(f N) : ℝ) := by
        exact fun N => cor_ratio N;
      -- Taking logarithms on both sides of the inequality $A1(N) \geq A(N) \cdot 2^{-f(N)}$, we get $\log A1(N) \geq \log A(N) - f(N) \log 2$.
      have h_log_A1_lower_bound : ∀ N, Real.log (A1 N : ℝ) ≥ Real.log (A N : ℝ) - (f N : ℝ) * Real.log 2 := by
        intro N; specialize h_A1_lower_bound N; by_cases h : A N = 0 <;> simp_all +decide [ Real.rpow_def_of_pos ] ;
        · -- Since $A N = 0$ implies there are no Sidon subsets of $[N]$, which contradicts the existence of the empty set, we have a contradiction.
          have h_contra : A N ≠ 0 := by
            refine' ne_of_gt ( Finset.card_pos.mpr _ );
            refine' ⟨ ∅, _ ⟩ ; simp +decide [ Sidon ];
          contradiction;
        · have := Real.log_le_log ( by positivity ) h_A1_lower_bound; norm_num [ Real.log_mul, Real.exp_ne_zero, h ] at this ⊢; linarith;
      -- By definition of $A$, we know that $\log A(N) \geq (\frac{1}{2} \log 5 + o(1)) \sqrt{N}$.
      have h_log_A_lower_bound : ∀ c < Real.log 5 / 2, ∀ᶠ N in Filter.atTop, Real.log (A N : ℝ) ≥ (c : ℝ) * Real.sqrt N := by
        intro c hc
        have h_log_A_lower_bound : ∀ᶠ N in Filter.atTop, Real.log (A N : ℝ) / Real.sqrt N ≥ c := by
          exact eventually_lower_bound c hc;
        filter_upwards [ h_log_A_lower_bound, Filter.eventually_gt_atTop 0 ] with N hN hN' using by rw [ ge_iff_le ] at *; rw [ le_div_iff₀ ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr hN' ) ] at *; linarith;
      -- By definition of $f$, we know that $f(N) = (1 + o(1)) \sqrt{N}$.
      have h_f_lower_bound : ∀ ε > 0, ∀ᶠ N in Filter.atTop, (f N : ℝ) ≤ (1 + ε) * Real.sqrt N := by
        intro ε hε_pos
        have h_f_lower_bound : ∀ᶠ N in Filter.atTop, (f N : ℝ) / Real.sqrt N ≤ 1 + ε := by
          exact h_f.eventually ( ge_mem_nhds <| by linarith );
        filter_upwards [ h_f_lower_bound, Filter.eventually_gt_atTop 0 ] with N hN hN' using by rwa [ div_le_iff₀ ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr hN' ) ) ] at hN;
      -- By combining the inequalities from h_log_A_lower_bound and h_f_lower_bound, we can derive the desired result.
      intros c hc
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, (Real.log 5 / 2 - ε) - (1 + ε) * Real.log 2 > c := by
        have h_eps : Filter.Tendsto (fun ε : ℝ => (Real.log 5 / 2 - ε) - (1 + ε) * Real.log 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 5 / 2 - Real.log 2)) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
        have := h_eps.eventually ( lt_mem_nhds <| show log 5 / 2 - log 2 > c by rw [ h_eta ] at hc; rw [ show ( 5 / 4 : ℝ ) = 5 / 2 ^ 2 by norm_num, Real.log_div, Real.log_pow ] at hc <;> norm_num at * ; linarith ) ; have := this.and self_mem_nhdsWithin ; obtain ⟨ ε, hε₁, hε₂ ⟩ := this.exists ; exact ⟨ ε, hε₂, hε₁ ⟩ ;
      filter_upwards [ h_log_A_lower_bound ( Real.log 5 / 2 - ε ) ( by linarith ), h_f_lower_bound ε hε_pos, Filter.eventually_gt_atTop 0 ] with N hN₁ hN₂ hN₃ using by rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr hN₃ ) ) ] ; nlinarith [ h_log_A1_lower_bound N, Real.sqrt_nonneg N, Real.sq_sqrt ( Nat.cast_nonneg N ), Real.log_nonneg one_le_two ] ;

/-
A_1(N) is not of the form 2^(o(sqrt(N))).
-/
theorem cor_answers_1 (h_f : Filter.Tendsto (fun N => (f N : ℝ) / Real.sqrt N) Filter.atTop (nhds 1)) :
    ¬ (fun N => Real.log (A1 N)) =o[Filter.atTop] (fun N => Real.sqrt N) := by
      -- By definition of `o`, we need to show that $\lim_{N \to \infty} \frac{\log A_1(N)}{\sqrt{N}} \neq 0$.
      suffices h_lim : Filter.Tendsto (fun N => Real.log (A1 N : ℝ) / Real.sqrt N) Filter.atTop (nhds (0)) → False by
        contrapose! h_lim; rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> aesop;
      -- By Lemma `thm_main`, for any $c < \eta$, there exists $N_0$ such that for all $N \geq N_0$, $\frac{\log A_1(N)}{\sqrt{N}} \geq c$.
      have h_log_lower_bound : ∀ c < eta, ∀ᶠ N : ℕ in Filter.atTop, Real.log (A1 N : ℝ) / Real.sqrt N ≥ c := by
        convert thm_main h_f using 1;
      intro H; specialize h_log_lower_bound ( eta / 2 ) ( by linarith [ show 0 < eta by exact mul_pos ( by norm_num ) ( Real.log_pos ( by norm_num ) ) ] ) ; replace h_log_lower_bound := h_log_lower_bound.and ( H.eventually ( gt_mem_nhds ( show 0 < eta / 2 by exact div_pos ( mul_pos ( by norm_num ) ( Real.log_pos ( by norm_num ) ) ) zero_lt_two ) ) ) ; obtain ⟨ N, hN₁, hN₂ ⟩ := h_log_lower_bound.exists; linarith;

/-
For every fixed c in (0, 1/2), A_1(N) >= 2^(N^c) for all sufficiently large N.
-/
theorem cor_answers_2 (h_f : Filter.Tendsto (fun N => (f N : ℝ) / Real.sqrt N) Filter.atTop (nhds 1)) :
    ∀ c ∈ Set.Ioo 0 (1 / 2 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, (A1 N : ℝ) ≥ 2 ^ ((N : ℝ) ^ c) := by
      field_simp;
      intro c hc
      have h_eventually : ∀ᶠ N : ℕ in Filter.atTop, Real.log (A1 N) ≥ (eta / 2) * Real.sqrt N := by
        have := thm_main h_f ( eta / 2 ) ( by linarith [ show eta > 0 by exact mul_pos ( by norm_num ) ( Real.log_pos ( by norm_num ) ) ] );
        filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with N hN hN' using by rw [ ge_iff_le ] at *; rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr hN' ) ) ] at *; linarith;
      -- Since $N^c = o(\sqrt{N})$, for all sufficiently large $N$ we have $(\eta/2)\sqrt{N} \ge N^c$.
      have h_eventually_ge : ∀ᶠ N : ℕ in Filter.atTop, (eta / 2) * Real.sqrt N ≥ (N : ℝ) ^ c * Real.log 2 := by
        field_simp;
        -- We can divide both sides by $\sqrt{N}$ to get $N^{c - 1/2} * \log 2 * 2 \leq \eta$.
        suffices h_div : ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ (c - 1 / 2) * Real.log 2 * 2 ≤ eta by
          filter_upwards [ h_div, Filter.eventually_gt_atTop 0 ] with N hN hN' ; rw [ Real.sqrt_eq_rpow ] ; convert mul_le_mul_of_nonneg_right hN ( Real.rpow_nonneg ( Nat.cast_nonneg N ) ( 1 / 2 : ℝ ) ) using 1 ; rw [ show ( N : ℝ ) ^ c = ( N : ℝ ) ^ ( c - 1 / 2 ) * ( N : ℝ ) ^ ( 1 / 2 : ℝ ) by rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf ] ; ring;
        field_simp;
        exact Filter.Tendsto.eventually ( by simpa using Filter.Tendsto.mul ( Filter.Tendsto.mul tendsto_const_nhds <| tendsto_rpow_neg_atTop ( show 0 < - ( ( c * 2 - 1 ) / 2 ) by linarith [ hc.1, hc.2 ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ( ge_mem_nhds <| show 0 < eta from mul_pos ( by norm_num ) <| Real.log_pos <| by norm_num );
      filter_upwards [ h_eventually, h_eventually_ge, Filter.eventually_gt_atTop 0 ] with N hN₁ hN₂ hN₃;
      rw [ ← Real.log_le_log_iff ( by positivity ) ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by intro h; norm_num [ h ] at *; nlinarith [ Real.log_pos one_lt_two, show ( N :ℝ ) ^ c > 0 by positivity ] ), Real.log_rpow ] <;> norm_num ; linarith [ Real.log_pos one_lt_two ]

/-
f(N) is monotonically increasing.
-/
theorem f_mono {N M : ℕ} (h : N ≤ M) : f N ≤ f M := by
  exact Finset.sup_mono ( Finset.filter_subset_filter _ <| Finset.powerset_mono.mpr <| Finset.Icc_subset_Icc_right h )

/-
Lower bound for f(N): f(N) ≥ (1-ε)√N for large N.
-/
lemma f_ge_one_sub_eps_mul_sqrt (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, (1 - ε) * Real.sqrt N ≤ f N := by
  by_cases hε1 : ε < 1;
  · -- By `lem_prime_near`, for large N there exists a prime p such that (1 - ε)√N < p ≤ √N.
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ N ≥ N0, ∃ p : ℕ, p.Prime ∧ (1 - ε) * Real.sqrt N < p ∧ p ≤ Real.sqrt N := by
      have := @lem_prime_near;
      rcases Filter.eventually_atTop.mp ( this ε ⟨ hε, hε1 ⟩ ) with ⟨ N0, hN0 ⟩ ; use Nat.ceil ( N0 ^ 2 ) ; intro N hN ; specialize hN0 ( Real.sqrt N ) ( Real.le_sqrt_of_sq_le <| by nlinarith [ Nat.ceil_le.mp hN ] ) ; aesop;
    -- By `shift_sidon_mod` and `lift_sidon_mod`, we can find a Sidon set in [1, p^2 - 2] of size p.
    have h_sidon_set : ∀ p : ℕ, p.Prime → (f (p^2 - 2) : ℝ) ≥ p := by
      intros p hp
      obtain ⟨T, hT_card, hT_sidon⟩ : ∃ T : Finset ℕ, T.card = p ∧ SidonMod (p^2 - 1) (T : Set ℕ) ∧ T ⊆ Finset.Icc 1 (p^2 - 2) := by
        have := @bose_chowla_at_h_eq_2 p;
        -- By `shift_sidon_mod`, we can find a Sidon set in ZMod (p^2 - 1) of size p.
        obtain ⟨S, hS⟩ : ∃ S : Finset (ZMod (p^2 - 1)), Sidon (S : Set (ZMod (p^2 - 1))) ∧ S.card = p ∧ (0 : ZMod (p^2 - 1)) ∉ S := by
          by_cases h : p = 1 <;> simp_all +decide [ Nat.Prime.isPrimePow ];
          obtain ⟨ S, hS₁, hS₂ ⟩ := this;
          have := shift_sidon_mod ( p ^ 2 - 1 ) ( by
            exact lt_tsub_iff_left.mpr ( by nlinarith only [ hp.two_le ] ) ) S hS₁ ( by
            exact hS₂.symm ▸ lt_tsub_iff_left.mpr ( by nlinarith only [ hp.two_le ] ) )
          generalize_proofs at *;
          aesop;
        have := @lift_sidon_mod ( p ^ 2 - 1 );
        rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.succ_mul, sq ];
        specialize this ( by nlinarith ) S hS.1 hS.2.2;
        use Finset.image ZMod.val S;
        simp_all +decide [ Finset.subset_iff, Set.subset_def ];
        exact fun x hx => Nat.le_sub_of_add_le ( by linarith [ this.2.2 x hx ] );
      refine' mod_cast le_trans _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hT_sidon.2, _ ⟩ );
      · linarith;
      · intro a b c d ha hb hc hd habcd;
        have := hT_sidon.1 ( ↑a ) ( ↑b ) ( ↑c ) ( ↑d ) ; simp_all +decide
        simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
        specialize this a ha rfl b hb rfl c hc rfl d hd rfl ; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ];
        norm_cast at *;
        simp_all +decide [ Nat.mod_eq_of_lt ( show a < p ^ 2 - 1 from lt_of_le_of_lt ( Finset.mem_Icc.mp ( hT_sidon.2 ha ) |>.2 ) ( Nat.pred_lt ( ne_bot_of_gt ( Nat.sub_pos_of_lt ( by nlinarith only [ hp.two_le ] ) ) ) ) ), Nat.mod_eq_of_lt ( show b < p ^ 2 - 1 from lt_of_le_of_lt ( Finset.mem_Icc.mp ( hT_sidon.2 hb ) |>.2 ) ( Nat.pred_lt ( ne_bot_of_gt ( Nat.sub_pos_of_lt ( by nlinarith only [ hp.two_le ] ) ) ) ) ), Nat.mod_eq_of_lt ( show c < p ^ 2 - 1 from lt_of_le_of_lt ( Finset.mem_Icc.mp ( hT_sidon.2 hc ) |>.2 ) ( Nat.pred_lt ( ne_bot_of_gt ( Nat.sub_pos_of_lt ( by nlinarith only [ hp.two_le ] ) ) ) ) ), Nat.mod_eq_of_lt ( show d < p ^ 2 - 1 from lt_of_le_of_lt ( Finset.mem_Icc.mp ( hT_sidon.2 hd ) |>.2 ) ( Nat.pred_lt ( ne_bot_of_gt ( Nat.sub_pos_of_lt ( by nlinarith only [ hp.two_le ] ) ) ) ) ) ];
    -- By combining the results from `hN0` and `h_sidon_set`, we get the desired inequality.
    have h_final : ∀ N ≥ N0, ∃ p : ℕ, p.Prime ∧ (1 - ε) * Real.sqrt N < p ∧ p ≤ Real.sqrt N ∧ (f N : ℝ) ≥ p := by
      intros N hN
      obtain ⟨p, hp_prime, hp_bounds⟩ := hN0 N hN
      have hp_f : (f N : ℝ) ≥ f (p^2 - 2) := by
        exact_mod_cast f_mono ( show p ^ 2 - 2 ≤ N from Nat.sub_le_of_le_add <| by rw [ Real.le_sqrt ] at hp_bounds <;> norm_cast at * <;> nlinarith );
      exact ⟨ p, hp_prime, hp_bounds.1, hp_bounds.2, le_trans ( h_sidon_set p hp_prime ) hp_f ⟩;
    filter_upwards [ Filter.eventually_ge_atTop N0 ] with N hN using by obtain ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ := h_final N hN; linarith;
  · exact Filter.Eventually.of_forall fun N => by nlinarith [ Real.sqrt_nonneg N ] ;

theorem sqrt_asymptotic : Filter.Tendsto (fun N => (f N : ℝ) / Real.sqrt N) Filter.atTop (nhds 1) := by
  have := @ErdosTuran;
  -- To prove the lower bound, use the fact that for any ε > 0, there exists N₀ such that for all N ≥ N₀, (1 - ε) * Real.sqrt N ≤ f N.
  have h_lower_bound : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (1 - ε) * Real.sqrt N ≤ f N := by
    intro ε hε_pos
    have := f_ge_one_sub_eps_mul_sqrt ε hε_pos
    aesop;
  rw [ Metric.tendsto_nhds ];
  intro ε hε; rcases this ( ε / 2 ) ( half_pos hε ) with ⟨ N0, HN0 ⟩ ; rcases h_lower_bound ( ε / 2 ) ( half_pos hε ) with ⟨ N1, HN1 ⟩ ; refine Filter.eventually_atTop.mpr ⟨ Max.max N0 N1 + 1, fun N hN => abs_lt.mpr ⟨ ?lb, ?ub ⟩ ⟩ <;> nlinarith [ HN0 N ( by linarith [ le_max_left N0 N1 ] ), HN1 N ( by linarith [ le_max_right N0 N1 ] ), Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, show ( N : ℝ ) ≥ Max.max N0 N1 + 1 by exact_mod_cast hN, mul_div_cancel₀ ( f N : ℝ ) <| ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| pos_of_gt hN ] ;

theorem cor_answers_1_unconditional :
    ¬ (fun N => Real.log (A1 N)) =o[Filter.atTop] (fun N => Real.sqrt N) := by
  apply cor_answers_1
  exact sqrt_asymptotic

theorem cor_answers_2_unconditional :
    ∀ c ∈ Set.Ioo 0 (1 / 2 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, (A1 N : ℝ) ≥ 2 ^ ((N : ℝ) ^ c) := by
  apply cor_answers_2
  exact sqrt_asymptotic

theorem erdos_862 :
    ∀ c < eta, ∀ᶠ N : ℕ in Filter.atTop, Real.log (A1 N : ℝ) / Real.sqrt N ≥ c := by
  apply thm_main
  exact sqrt_asymptotic

#print axioms erdos_862
-- 'erdos_862' depends on axioms: [prime_between, propext, Classical.choice, Quot.sound]
