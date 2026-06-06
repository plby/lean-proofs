/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 476.
https://www.erdosproblems.com/forum/thread/476

Informal authors:
- J. A. Dias da Silva
- Yahya Ould Hamidoune
- Noga Alon
- Melvyn B. Nathanson
- Imre Z. Ruzsa
- ChatGPT

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos476.md
-/
/-
We proved the Erdős-Heilbronn inequality in $\mathbb F_p$.
The main theorem is `erdos_heilbronn`.
We followed the proof outline provided, formalizing the necessary lemmas about Lagrange interpolation, the Combinatorial Nullstellensatz, and properties of restricted sumsets.
Key definitions include `restrictedSumset`, `P_S`, `L_s`, `Lambda_ST`, and `F_poly`.
Key lemmas include `two_variable_combinatorial_nullstellensatz`, `large_set_full`, `binomial_coeff_computation`, and `erdos_heilbronn_small`.
-/

import Mathlib

namespace Erdos476

-- These generated proof scripts still rely on style-heavy tactic automation.
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.multiGoal false

attribute [local instance] Classical.propDecidable

open Polynomial Finset

/-
The restricted sumset of A is the set of all sums a+b where a,b are in A and a is not equal to b.
-/
def restrictedSumset {R : Type*} [Add R] [DecidableEq R] (A : Finset R) : Finset R :=
  (A.product A).filter (fun x => x.1 ≠ x.2) |>.image (fun x => x.1 + x.2)

/-
Define $P_S(x) = \prod_{s \in S} (x-s)$.
-/

variable {F : Type*} [Field F]

/-- The polynomial $P_S(x) = \prod_{s \in S} (x-s)$. -/
noncomputable def P_S (S : Finset F) : F[X] := ∏ s ∈ S, (X - C s)

/-
The derivative of $P_S$ evaluated at $s \in S$ is $\prod_{u \in S, u \neq s} (s-u)$.
-/
lemma P_S_derivative_eval_eq_prod (S : Finset F) (s : F) (hs : s ∈ S) :
    (derivative (P_S S)).eval s = ∏ u ∈ S.erase s, (s - u) := by
      -- By definition of $P_S$, we can write it as $(X - C s) \cdot Q$, where $Q = \prod_{u \in S \setminus \{s\}} (X - C u)$.
      set Q : F[X] := ∏ u ∈ S.erase s, (X - C u)
      have hPS : P_S S = (X - C s) * Q := by
        unfold P_S; rw [ ← Finset.mul_prod_erase _ _ hs ] ;
      simp +decide [ hPS, Polynomial.derivative_mul ];
      simp +decide [ Q, Polynomial.eval_prod ]

/-
Define $L_s(x) = \frac{P_S(x)}{(x-s)P_S'(s)}$.
-/
/-- The Lagrange basis polynomial $L_s(x)$. -/
noncomputable def L_s (S : Finset F) (s : F) : F[X] :=
  (P_S S) /ₘ (X - C s) * C (1 / (derivative (P_S S)).eval s)

/-
The degree of $L_s$ is $|S|-1$.
-/
lemma L_s_natDegree (S : Finset F) (s : F) (hs : s ∈ S) :
    (L_s S s).natDegree = S.card - 1 := by
      -- By definition of $L_s$, we know that $L_s(x) = \frac{P_S(x)}{(x-s)P_S'(s)}$.
      have hL_s : L_s S s = (P_S S) /ₘ (X - C s) * C (1 / (derivative (P_S S)).eval s) := by
        rfl;
      -- By definition of $P_S$, we know that $P_S(x) = (x-s)P_S'(s) + \prod_{u \in S, u \neq s} (x-u)$.
      have hP_S_def : P_S S = (X - C s) * ((P_S S) /ₘ (X - C s)) := by
        rw [ Polynomial.divByMonic_eq_div _ ( Polynomial.monic_X_sub_C s ), EuclideanDomain.mul_div_cancel' ];
        · exact Polynomial.X_sub_C_ne_zero s;
        · exact Polynomial.dvd_iff_isRoot.mpr ( by simp +decide [ P_S, Finset.prod_eq_prod_diff_singleton_mul hs ] );
      -- The degree of $P_S(x)$ is $|S|$.
      have hP_S_deg : (P_S S).natDegree = S.card := by
        erw [ Polynomial.natDegree_prod _ _ fun x hx => Polynomial.X_sub_C_ne_zero x ];
        simp +decide [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
      rw [ hL_s, Polynomial.natDegree_mul' ] <;> norm_num [ hP_S_deg ];
      · rw [ Polynomial.natDegree_divByMonic _ ( Polynomial.monic_X_sub_C s ), Polynomial.natDegree_X_sub_C, hP_S_deg ];
      · refine ⟨ ?_, ?_ ⟩;
        · intro h; simp_all +singlePass ;
          exact hP_S_deg.not_lt ( Finset.card_pos.mpr ⟨ s, hs ⟩ );
        · rw [ P_S_derivative_eval_eq_prod _ _ hs ];
          exact Finset.prod_ne_zero_iff.mpr fun u hu => sub_ne_zero_of_ne <| by rintro rfl; exact Finset.notMem_erase _ _ hu;

/-
$L_s(s)=1$.
-/
lemma L_s_eval_self (S : Finset F) (s : F) (hs : s ∈ S) :
    (L_s S s).eval s = 1 := by
      -- By definition of $L_s$, we know that
      have hL_s : (P_S S) = (Polynomial.X - Polynomial.C s) * (P_S S /ₘ (Polynomial.X - Polynomial.C s)) := by
        rw [ Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ];
        simp +decide [ P_S, Finset.prod_eq_prod_diff_singleton_mul hs ];
      unfold L_s at *; replace hL_s := congr_arg ( Polynomial.derivative ) hL_s; norm_num at hL_s; rcases eq_or_ne ( Polynomial.derivative ( P_S S ) |> Polynomial.eval s ) 0 <;> simp_all +singlePass ;
      · replace hL_s := congr_arg ( Polynomial.eval s ) hL_s ; simp_all
        exact absurd hL_s ( by rw [ P_S_derivative_eval_eq_prod S s hs ] ; exact Finset.prod_ne_zero_iff.2 fun x hx => sub_ne_zero_of_ne <| by aesop );
      · exact mul_inv_cancel₀ ‹_›

/-
$L_s(s')=0$ for all $s'\in S, s'\neq s$.
-/
lemma L_s_eval_ne (S : Finset F) (s s' : F) (hs : s ∈ S) (hs' : s' ∈ S) (h : s' ≠ s) :
    (L_s S s).eval s' = 0 := by
      unfold L_s;
      have h_div : (P_S S) = (X - C s) * ((P_S S) /ₘ (X - C s)) := by
        rw [ Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ];
        simp +decide [ P_S, Finset.prod_eq_prod_diff_singleton_mul hs ];
      replace h_div := congr_arg ( Polynomial.eval s' ) h_div ; simp_all
      -- Since $s' \neq s$, we have $P_S(s') = 0$.
      have h_P_S_s'_zero : Polynomial.eval s' (P_S S) = 0 := by
        simp +decide [ P_S, Polynomial.eval_prod, Finset.prod_eq_zero hs' ];
      exact Or.inl ( mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linear_combination' h_div.symm + h_P_S_s'_zero )

/-
Lemma 4: Univariate leading coefficient identity.
If $g\in \Bbb F[x]$ has $\deg g\le m-1$, then $[x^{m-1}]\,g(x) = \sum_{s\in S}\frac{g(s)}{P_S'(s)}$.
-/
lemma univariate_leading_coeff_identity (S : Finset F) (g : F[X]) (hS : S.Nonempty) (hg : g.natDegree ≤ S.card - 1) :
    g.coeff (S.card - 1) = ∑ s ∈ S, g.eval s / (derivative (P_S S)).eval s := by
      -- By Lagrange interpolation, we have $g(x) = \sum_{s \in S} g(s) L_s(x)$.
      have h_interpolate : g = ∑ s ∈ S, Polynomial.C (g.eval s) * L_s S s := by
        refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq S ?_ ?_;
        · refine lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) ( max_lt ( lt_of_le_of_lt Polynomial.degree_le_natDegree ( WithBot.coe_lt_coe.mpr ( Nat.lt_of_le_of_lt hg ( Nat.pred_lt ( ne_bot_of_gt ( Finset.card_pos.mpr hS ) ) ) ) ) ) ( lt_of_le_of_lt ( Polynomial.degree_sum_le _ _ ) ?_ ) );
          erw [ Finset.sup_lt_iff ];
          · intro s hs;
            refine lt_of_le_of_lt ( Polynomial.degree_mul_le _ _ ) ?_;
            refine lt_of_le_of_lt ( add_le_add ( Polynomial.degree_C_le ) ( Polynomial.degree_le_of_natDegree_le ( L_s_natDegree S s hs |> le_of_eq ) ) ) ?_
            aesop;
          · exact WithBot.bot_lt_coe _;
        · intro s hs; simp +decide [ Polynomial.eval_finset_sum ] ;
          rw [ Finset.sum_eq_single s ];
          · rw [ L_s_eval_self S s hs, mul_one ];
          · exact fun t ht hts => mul_eq_zero_of_right _ ( L_s_eval_ne _ _ _ ht hs hts.symm );
          · aesop;
      -- By definition of $L_s$, we know that $[x^{m-1}]L_s(x) = \frac{1}{P_S'(s)}$.
      have h_leading_coeff : ∀ s ∈ S, Polynomial.coeff (L_s S s) (S.card - 1) = 1 / (Polynomial.derivative (P_S S)).eval s := by
        intro s hs
        have h_leading_coeff : Polynomial.leadingCoeff (L_s S s) = 1 / (Polynomial.derivative (P_S S)).eval s := by
          unfold L_s P_S; simp
          rw [ show ( ∏ s ∈ S, ( Polynomial.X - Polynomial.C s ) ) = ( Polynomial.X - Polynomial.C s ) * ( ∏ s ∈ S \ { s }, ( Polynomial.X - Polynomial.C s ) ) by rw [ Finset.prod_eq_mul_prod_diff_singleton_of_mem hs ], Polynomial.divByMonic_eq_div _ ( Polynomial.monic_X_sub_C s ) ];
          rw [ mul_div_cancel_left₀ _ ( Polynomial.X_sub_C_ne_zero s ) ] ; simp +decide [ Polynomial.leadingCoeff_prod ] ;
        rw [ ← h_leading_coeff, Polynomial.leadingCoeff, L_s_natDegree S s hs ];
      nth_rw 1 [ h_interpolate ];
      norm_num at *;
      exact Finset.sum_congr rfl fun x hx => by rw [ h_leading_coeff x hx, div_eq_mul_inv ] ;

/-
Define $\Lambda_{S,T}(f) = \sum_{s\in S}\sum_{t\in T}\frac{f(s,t)}{P_S'(s)Q_T'(t)}$.
-/
noncomputable def Lambda_ST (S T : Finset F) (f : MvPolynomial (Fin 2) F) : F :=
  ∑ s ∈ S, ∑ t ∈ T, (MvPolynomial.eval (![s, t]) f) / ((derivative (P_S S)).eval s * (derivative (P_S T)).eval t)

/-
Lemma 5: Two-variable coefficient functional.
If $f\in \Bbb F[x,y]$ has total degree $\deg(f)\le m+n-2$, then $\Lambda_{S,T}(f)=[x^{m-1}y^{n-1}]\,f$.
-/
lemma two_variable_functional_eq_coeff (S T : Finset F) (f : MvPolynomial (Fin 2) F)
    (hS : S.Nonempty) (hT : T.Nonempty) (hf : f.totalDegree ≤ S.card + T.card - 2) :
    Lambda_ST S T f = f.coeff (Finsupp.equivFunOnFinite.symm ![S.card - 1, T.card - 1]) := by
      unfold Lambda_ST;
      -- By definition of $f$, we can write it as a sum of monomials.
      have h_monomial : ∑ s ∈ S, ∑ t ∈ T, (MvPolynomial.eval ![s, t] f) / ((derivative (P_S S)).eval s * (derivative (P_S T)).eval t) =
                    ∑ m ∈ f.support, (MvPolynomial.coeff m f) * (∑ s ∈ S, s ^ (m 0) / ((derivative (P_S S)).eval s)) * (∑ t ∈ T, t ^ (m 1) / ((derivative (P_S T)).eval t)) := by
                      simp +decide [ MvPolynomial.eval_eq' ];
                      simp +decide only [div_eq_mul_inv, sum_mul, mul_assoc, Finset.mul_sum _ _ _,
                                                mul_left_comm];
                      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; rw [ Finset.sum_comm ] ; ring_nf;
                      exact fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      -- By Lemma 4, we know that $\sum_{s \in S} \frac{s^i}{P_S'(s)} = 0$ for $i < m-1$ and $\sum_{t \in T} \frac{t^j}{Q_T'(t)} = 0$ for $j < n-1$.
      have h_zero_sum : ∀ i < S.card - 1, ∑ s ∈ S, s ^ i / ((derivative (P_S S)).eval s) = 0 := by
        intro i hi;
        have := univariate_leading_coeff_identity S ( Polynomial.X ^ i ) hS ( by simpa using by omega ) ; aesop;
      have h_zero_sum_T : ∀ j < T.card - 1, ∑ t ∈ T, t ^ j / ((derivative (P_S T)).eval t) = 0 := by
        intro j hj;
        have := univariate_leading_coeff_identity T ( Polynomial.X ^ j ) hT ( by simpa using hj.le );
        simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
      rw [ h_monomial, Finset.sum_eq_single ( Finsupp.equivFunOnFinite.symm ![#S - 1, #T - 1] ) ];
      · -- By Lemma 4, we know that $\sum_{s \in S} \frac{s^{m-1}}{P_S'(s)} = 1$ and $\sum_{t \in T} \frac{t^{n-1}}{Q_T'(t)} = 1$.
        have h_one_sum : ∑ s ∈ S, s ^ (S.card - 1) / ((derivative (P_S S)).eval s) = 1 := by
          have := univariate_leading_coeff_identity S ( Polynomial.X ^ ( S.card - 1 ) ) hS ?_ <;> aesop
        have h_one_sum_T : ∑ t ∈ T, t ^ (T.card - 1) / ((derivative (P_S T)).eval t) = 1 := by
          have := univariate_leading_coeff_identity T ( Polynomial.X ^ ( T.card - 1 ) ) hT ?_ <;> aesop;
        simp_all +decide [ Finsupp.equivFunOnFinite ];
      · intro m hm hne
        by_cases h_cases : m 0 < S.card - 1 ∨ m 1 < T.card - 1;
        · cases h_cases <;> simp +decide [ * ];
        · -- Since $m \neq (Finsupp.equivFunOnFinite.symm ![#S - 1, #T - 1])$, we have $m 0 + m 1 > #S + #T - 2$.
          have h_deg : m 0 + m 1 > #S + #T - 2 := by
            contrapose! hne;
            ext i; fin_cases i <;> norm_num <;> omega;
          contrapose! hf;
          refine lt_of_lt_of_le h_deg ?_;
          refine le_trans ?_ ( Finset.le_sup hm );
          simp +decide [ Finsupp.sum_fintype ];
      · aesop

/-
Lemma 6: Two-variable Combinatorial Nullstellensatz.
If $[x^{m-1}y^{n-1}]\,f\neq 0$, then there exists $(s,t)\in S\times T$ such that $f(s,t)\neq 0$.
-/
lemma two_variable_combinatorial_nullstellensatz (S T : Finset F) (f : MvPolynomial (Fin 2) F)
    (hS : S.Nonempty) (hT : T.Nonempty) (hf : f.totalDegree ≤ S.card + T.card - 2)
    (h_coeff : f.coeff (Finsupp.equivFunOnFinite.symm ![S.card - 1, T.card - 1]) ≠ 0) :
    ∃ s ∈ S, ∃ t ∈ T, MvPolynomial.eval ![s, t] f ≠ 0 := by
      by_contra! h_contra;
      exact h_coeff ( by rw [ ← two_variable_functional_eq_coeff S T f hS hT hf ] ; exact Finset.sum_eq_zero fun s hs => Finset.sum_eq_zero fun t ht => by aesop )

/-
$|A \cap (t-A)| \ge 3$.
-/
lemma intersection_size_ge (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (A : Finset (ZMod p)) (t : ZMod p)
    (hA : A.card ≥ (p + 3) / 2) :
    (A ∩ (A.image (fun x => t - x))).card ≥ 3 := by
      have h_card_union : (A ∪ (A.image (fun x => t - x))).card ≤ p := by
        exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
      have := Finset.card_union_add_card_inter A ( Finset.image ( fun x => t - x ) A );
      rw [ Finset.card_image_of_injective _ ( sub_right_injective ) ] at * ; linarith [ Nat.div_mul_cancel ( show 2 ∣ p + 3 from even_iff_two_dvd.mp ( by simpa [ parity_simps ] using Nat.Prime.odd_of_ne_two Fact.out hp ) ) ]

/-
Lemma 7: Large set full.
Let $p$ be a prime and let $A\subseteq \Fp$ with $|A|\ge (p+3)/2$. Then $A\hat{+}A=\Fp$.
-/
lemma large_set_full (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (A : Finset (ZMod p))
    (hA : A.card ≥ (p + 3) / 2) :
    restrictedSumset A = Finset.univ := by
      -- Let $t\in \Fp$ be arbitrary.
      have h_arbitrary : ∀ t : ZMod p, ∃ s₁ s₂ : ZMod p, s₁ ∈ A ∧ s₂ ∈ A ∧ s₁ ≠ s₂ ∧ s₁ + s₂ = t := by
        intro t
        obtain ⟨x, hx⟩ : ∃ x ∈ A ∩ (A.image (fun x => t - x)), x ≠ t - x := by
          have h_inter : (A ∩ (A.image (fun x => t - x))).card ≥ 3 := by
            exact intersection_size_ge p hp A t hA;
          contrapose! h_inter;
          -- If for every $x \in A \cap (t - A)$, we have $x = t - x$, then $2x = t$, which implies $x = t/2$.
          have h_eq : ∀ x ∈ A ∩ (A.image (fun x => t - x)), x = t / 2 := by
            intro x hx; specialize h_inter x hx; rw [ eq_div_iff ] <;> norm_num ; linear_combination' h_inter;
            erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp ) );
          exact lt_of_le_of_lt ( Finset.card_le_one.mpr fun x hx y hy => by rw [ h_eq x hx, h_eq y hy ] ) ( by norm_num )
        generalize_proofs at *;
        use x, t - x; simp_all
        grind;
      ext t;
      obtain ⟨ s₁, s₂, hs₁, hs₂, hs₁₂, rfl ⟩ := h_arbitrary t; exact ⟨ fun h => Finset.mem_univ _, fun h => Finset.mem_image.mpr ⟨ ( s₁, s₂ ), Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ hs₁, hs₂ ⟩, hs₁₂ ⟩, rfl ⟩ ⟩ ;

/-
Lemma 8: A binomial coefficient computation.
Let $n\ge 2$ be an integer and put $m:=2n-4$.
In $\mathbb Z[x,y]$ one has $[x^{n-1}y^{n-2}]\,(x-y)(x+y)^m = \binom{m}{n-2}-\binom{m}{n-1}$.
-/
lemma binomial_coeff_computation (n : ℕ) (hn : n ≥ 2) :
    let m := 2 * n - 4
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm ![n - 1, n - 2])
      ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ m : MvPolynomial (Fin 2) ℤ)) =
    (Nat.choose m (n - 2) - Nat.choose m (n - 1) : ℤ) := by
      norm_num [ mul_assoc, mul_add, sub_mul, MvPolynomial.coeff_mul ];
      rw [ Finset.sum_eq_single ( Finsupp.single 0 1, Finsupp.equivFunOnFinite.symm ![ n - 2, n - 2 ] ), Finset.sum_eq_single ( Finsupp.single 1 1, Finsupp.equivFunOnFinite.symm ![ n - 1, n - 3 ] ) ] <;> simp +decide [ MvPolynomial.coeff_X' ];
      · -- By definition of polynomial multiplication and the binomial theorem, we can expand $(x + y)^{2n-4}$.
        have h_expand : (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) ^ (2 * n - 4) = ∑ k ∈ Finset.range (2 * n - 3), MvPolynomial.monomial (Finsupp.single 0 k + Finsupp.single 1 (2 * n - 4 - k)) (Nat.choose (2 * n - 4) k : ℤ) := by
          rw [ add_pow ];
          simp +decide [ MvPolynomial.monomial_eq, Finsupp.single_apply ];
          exact Eq.symm ( by rw [ show 2 * n - 3 = 2 * n - 4 + 1 by omega ] ; ac_rfl );
        rcases n with ( _ | _ | n ) <;> simp_all
        simp +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial ];
        rw [ Finset.sum_eq_single n, Finset.sum_eq_single ( n + 1 ) ] <;> simp +decide [ Finsupp.ext_iff ];
        · grind;
        · aesop;
        · exact fun h₁ h₂ => Nat.choose_eq_zero_of_lt <| by omega;
        · aesop;
        · intros; omega;
      · intros; subst_vars; simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ] ;
        omega;
      · rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ];
        · erw [ MvPolynomial.coeff_C ];
          simp +decide [ Finsupp.ext_iff ];
        · exact fun h => False.elim <| h <| add_comm _ _;
      · rintro a b h₁ h₂ rfl; simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ] ;
        omega;
      · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ];
        exact fun h => False.elim <| h <| add_comm _ _

open MvPolynomial

/-- The polynomial $F(x,y) = (x-y)\prod_{c\in C}(x+y-c)$. -/
noncomputable def F_poly {p : ℕ} (C : Finset (ZMod p)) : MvPolynomial (Fin 2) (ZMod p) :=
  (X 0 - X 1) * ∏ c ∈ C, (X 0 + X 1 - MvPolynomial.C c)

/-
The polynomial $\prod_{c\in S}(x+y-c) - (x+y)^{|S|}$ has total degree at most $|S|-1$.
-/
set_option maxHeartbeats 2000000 in -- polynomial product expansion needs extra heartbeats
lemma prod_linear_factors_degree_sub_leading {p : ℕ} (S : Finset (ZMod p)) :
    (∏ c ∈ S, (X 0 + X 1 - MvPolynomial.C c) - (X 0 + X 1) ^ S.card).totalDegree ≤ S.card - 1 := by
      -- Let's expand the product $\prod_{c\in S}(x+y-c)$ using the binomial theorem.
      have h_expand : ∏ c ∈ S, (MvPolynomial.X 0 + MvPolynomial.X 1 - (MvPolynomial.C c) : MvPolynomial (Fin 2) (ZMod p)) = ∑ k ∈ Finset.range (S.card + 1), (MvPolynomial.X 0 + MvPolynomial.X 1) ^ k * MvPolynomial.C (∑ T ∈ Finset.powersetCard (S.card - k) S, (-1) ^ (S.card - k) * ∏ c ∈ T, c) := by
        have h_expand : ∏ c ∈ S, ((MvPolynomial.X 0 + MvPolynomial.X 1) - (MvPolynomial.C c) : MvPolynomial (Fin 2) (ZMod p)) = ∑ T ∈ Finset.powerset S, (-1) ^ (Finset.card T) * (∏ c ∈ T, MvPolynomial.C c) * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (S.card - Finset.card T) := by
          simp +decide [ sub_eq_add_neg, Finset.prod_add ];
          rw [ ← Finset.sum_bij ( fun T _ => S \ T ) ];
          · simp +contextual [ Finset.mem_powerset ];
          · simp +contextual [ Finset.ext_iff ];
            intro a₁ a₂ ha₁ ha₂ h x; specialize h x; aesop;
          · exact fun b hb => ⟨ S \ b, by aesop ⟩;
          · simp +contextual [ mul_comm, Finset.card_sdiff ];
            intro a ha; rw [ Finset.inter_eq_left.mpr ha ] ; rw [ Finset.prod_congr rfl fun x hx => neg_eq_neg_one_mul _, Finset.prod_mul_distrib ] ; aesop;
        rw [ h_expand, Finset.sum_powerset ];
        rw [ ← Finset.sum_flip ];
        refine Finset.sum_congr rfl fun k hk => ?_;
        rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        rw [ Nat.sub_sub_self ( Finset.mem_range_succ_iff.mp hk ) ];
      -- Let's simplify the expression for the total degree.
      have h_simplify : (∑ k ∈ Finset.range S.card, (MvPolynomial.X 0 + MvPolynomial.X 1) ^ k * MvPolynomial.C (∑ T ∈ Finset.powersetCard (S.card - k) S, (-1) ^ (S.card - k) * ∏ c ∈ T, c)).totalDegree ≤ S.card - 1 := by
        -- Each term in the sum has total degree at most $S.card - 1$.
        have h_term_deg : ∀ k ∈ Finset.range S.card, ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ k * MvPolynomial.C (∑ T ∈ Finset.powersetCard (S.card - k) S, (-1) ^ (S.card - k) * ∏ c ∈ T, c)).totalDegree ≤ S.card - 1 := by
          intro k hk;
          refine le_trans ( MvPolynomial.totalDegree_mul _ _ ) ?_;
          refine le_trans ( add_le_add ( MvPolynomial.totalDegree_pow _ _ ) ( MvPolynomial.totalDegree_C _ |> le_of_eq ) ) ?_;
          simp +zetaDelta at *;
          refine le_trans ( Nat.mul_le_mul_right _ ( Nat.le_sub_one_of_lt hk ) ) ?_;
          refine mul_le_of_le_one_right ( Nat.zero_le _ ) ?_;
          norm_num [ MvPolynomial.totalDegree ];
          intro b hb; rw [ MvPolynomial.coeff_X', MvPolynomial.coeff_X' ] at hb; aesop;
        exact totalDegree_finsetSum_le h_term_deg;
      simp_all +decide [ Finset.sum_range_succ ];
      convert h_simplify using 1;
      rw [ show ( ∏ c ∈ S, ( MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c ) : MvPolynomial ℕ ( ZMod p ) ) = ∑ x ∈ Finset.range S.card, ( MvPolynomial.X 0 + MvPolynomial.X 1 ) ^ x * ∑ x_1 ∈ Finset.powersetCard ( S.card - x ) S, ( -1 ) ^ ( S.card - x ) * ∏ x ∈ x_1, ( MvPolynomial.C : ZMod p → MvPolynomial ℕ ( ZMod p ) ) x + ( MvPolynomial.X 0 + MvPolynomial.X 1 ) ^ S.card from ?_ ] ; ring_nf;
      convert congr_arg ( MvPolynomial.eval₂ MvPolynomial.C ( fun i => if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 1 ) ) h_expand using 1;
      · simp +decide [ MvPolynomial.eval₂_prod ];
      · norm_num [ MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X ]

/-
The coefficient of $x^{n-1}y^{n-2}$ in $(x-y)(x+y)^{2n-4}$ over $\mathbb{Z}_p$ is $\binom{2n-4}{n-2} - \binom{2n-4}{n-1}$.
-/
lemma binomial_coeff_computation_zmod {p : ℕ} (n : ℕ) (hn : n ≥ 2) :
    let m := 2 * n - 4
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm ![n - 1, n - 2])
      ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ m : MvPolynomial (Fin 2) (ZMod p))) =
    (Nat.choose m (n - 2) - Nat.choose m (n - 1) : ZMod p) := by
      -- This follows from Lemma 8 by applying the ring homomorphism $\mathbb{Z} \to \mathbb{Z}_p$.
      have h_binom : (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm ![n - 1, n - 2]) ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (2 * n - 4) : MvPolynomial (Fin 2) ℤ)) = (Nat.choose (2 * n - 4) (n - 2) - Nat.choose (2 * n - 4) (n - 1) : ℤ) := by
        exact binomial_coeff_computation n hn;
      convert congr_arg ( ( ↑ ) : ℤ → ZMod p ) h_binom using 1;
      · norm_num [ MvPolynomial.coeff_mul ];
        congr! 2;
        · simp +decide [ MvPolynomial.coeff_X' ];
        · norm_num [ MvPolynomial.coeff_X_pow, add_pow ];
          simp +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_mul, MvPolynomial.coeff_X_pow ];
          congr! 3;
          erw [ MvPolynomial.coeff_C, MvPolynomial.coeff_C ] ; aesop;
      · norm_num

/-
The coefficient of $x^{n-1}y^{n-2}$ in $F$ is $\binom{2n-4}{n-2} - \binom{2n-4}{n-1}$.
-/
set_option maxHeartbeats 2000000 in -- coefficient extraction needs extra heartbeats
lemma F_poly_coeff {p : ℕ} (C : Finset (ZMod p)) (n : ℕ) (hC : C.card = 2 * n - 4) (hn : n ≥ 2) :
    (F_poly C).coeff (Finsupp.equivFunOnFinite.symm ![n - 1, n - 2]) =
    (Nat.choose (2 * n - 4) (n - 2) - Nat.choose (2 * n - 4) (n - 1) : ZMod p) := by
      -- We'll use the fact that $F(x,y) = (x-y)(x+y)^{2n-4}$ to compute the coefficient.
      have hF : F_poly C = (MvPolynomial.X 0 - MvPolynomial.X 1) * ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ C.card) + (MvPolynomial.X 0 - MvPolynomial.X 1) * (∏ c ∈ C, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c) - (MvPolynomial.X 0 + MvPolynomial.X 1) ^ C.card) := by
        unfold F_poly; ring;
      -- Since the total degree of $g(x,y)$ is at most $2n-4$, the coefficient of $x^{n-1}y^{n-2}$ in $(x-y)g(x,y)$ is zero.
      have h_coeff_zero : (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm ![n - 1, n - 2]) ((MvPolynomial.X 0 - MvPolynomial.X 1) * (∏ c ∈ C, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c) - (MvPolynomial.X 0 + MvPolynomial.X 1) ^ C.card) : MvPolynomial (Fin 2) (ZMod p))) = 0 := by
        have h_deg : (∏ c ∈ C, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c) - (MvPolynomial.X 0 + MvPolynomial.X 1) ^ C.card : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ C.card - 1 := by
          convert prod_linear_factors_degree_sub_leading C using 1;
          convert rfl;
          -- The total degree of a polynomial is invariant under the choice of variables.
          have h_total_degree_invariant : ∀ (p : MvPolynomial (Fin 2) (ZMod p)), MvPolynomial.totalDegree p = MvPolynomial.totalDegree (MvPolynomial.rename (fun i => if i = 0 then 0 else 1) p) := by
            intro p; exact (by
            refine le_antisymm ?_ ?_;
            · simp +decide [ MvPolynomial.totalDegree ];
              intro b hb; refine le_trans ?_ ( Finset.le_sup <| show ( Finsupp.mapDomain ( fun i => if i = 0 then 0 else 1 ) b ) ∈ ( MvPolynomial.rename ( fun i => if i = 0 then 0 else 1 ) p |> MvPolynomial.support ) from ?_ ) ; simp +decide [ Finsupp.sum_mapDomain_index ] ;
              simp +decide [ MvPolynomial.rename, Finsupp.mapDomain ];
              erw [ MvPolynomial.aeval_def ];
              erw [ MvPolynomial.eval₂_eq' ];
              simp +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, Finsupp.sum_fintype ];
              rw [ Finset.sum_eq_single b ] <;> simp +contextual [ MvPolynomial.coeff_mul, MvPolynomial.coeff_X_pow ];
              · rw [ Finset.sum_eq_single ( ( Finsupp.single 0 ( b 0 ), Finsupp.single 1 ( b 1 ) ) ) ] <;> aesop;
              · intro c hc hbc; rw [ Finset.sum_eq_zero ] <;> simp
                intro a b_1 h₁ h₂ h₃; subst_vars; simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ] ;
                have := h₁ 0; have := h₁ 1; simp_all +decide [ Finsupp.single_apply ] ;
            · exact totalDegree_rename_le (fun i => if i = 0 then 0 else 1) p);
          convert h_total_degree_invariant _ |> Eq.symm using 2;
          simp +decide [ MvPolynomial.rename_X ];
        rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ];
        -- The total degree of $(x-y)g(x,y)$ is at most $1 + (2n-5) = 2n-4$.
        have h_total_deg : ((MvPolynomial.X 0 - MvPolynomial.X 1) * (∏ c ∈ C, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c) - (MvPolynomial.X 0 + MvPolynomial.X 1) ^ C.card) : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ 1 + (C.card - 1) := by
          refine le_trans ( MvPolynomial.totalDegree_mul _ _ ) ?_;
          refine add_le_add ?_ h_deg;
          norm_num [ MvPolynomial.totalDegree ];
          intro b hb; rw [ MvPolynomial.coeff_X', MvPolynomial.coeff_X' ] at hb; aesop;
        rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide;
        · simp [Function.support]
          rw [Finset.sum_filter]
          norm_num [Fin.sum_univ_two]
        · simp [Function.support]
          rw [Finset.sum_filter]
          norm_num [Fin.sum_univ_two]
          omega
      simp_all
      convert binomial_coeff_computation_zmod n hn using 1

/-
If $|S| \le k \le |\alpha|$, there exists $C \supseteq S$ with $|C| = k$.
-/
lemma exists_superset_card_eq {α : Type*} [Fintype α] (S : Finset α) (k : ℕ)
    (h_le : S.card ≤ k) (h_lt : k ≤ Fintype.card α) :
    ∃ C : Finset α, S ⊆ C ∧ C.card = k := by
      classical
      exact Finset.exists_superset_card_eq h_le h_lt

/-
If $2n-3 < p$, then $\binom{2n-4}{n-2} - \binom{2n-4}{n-1} \ne 0 \pmod p$.
-/
lemma binomial_coeff_nonzero {p : ℕ} [Fact p.Prime] (n : ℕ) (h_small : 2 * n - 3 < p) (hn : n ≥ 2) :
    (Nat.choose (2 * n - 4) (n - 2) - Nat.choose (2 * n - 4) (n - 1) : ZMod p) ≠ 0 := by
      rcases n with ( _ | _ | n ) <;> simp_all
      -- Using the identity $\binom{2n}{n} - \binom{2n}{n+1} = \binom{2n}{n} \left(1 - \frac{n}{n+1}\right) = \frac{1}{n+1} \binom{2n}{n}$.
      have h_identity : (Nat.choose (2 * n) n : ZMod p) - (Nat.choose (2 * n) (n + 1) : ZMod p) = (Nat.choose (2 * n) n : ZMod p) * (1 / (n + 1) : ZMod p) := by
        have h_identity : (Nat.choose (2 * n) n : ZMod p) - (Nat.choose (2 * n) (n + 1) : ZMod p) = (Nat.choose (2 * n) n : ZMod p) * (1 - (n : ZMod p) / (n + 1)) := by
          have h_identity : (Nat.choose (2 * n) (n + 1) : ZMod p) = (Nat.choose (2 * n) n : ZMod p) * (n : ZMod p) / (n + 1) := by
            have h_identity : (Nat.choose (2 * n) (n + 1) : ℚ) = (Nat.choose (2 * n) n : ℚ) * (n : ℚ) / (n + 1 : ℚ) := by
              rw [ eq_div_iff ] <;> norm_cast;
              nlinarith [ Nat.add_one_mul_choose_eq ( 2 * n ) n, Nat.choose_succ_succ ( 2 * n ) n ];
            rw [ eq_div_iff ] at * <;> norm_cast at * ; aesop;
            rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ ) ( by omega );
          rw [ h_identity, mul_sub, mul_one, mul_div_assoc ];
        rw [ h_identity, one_sub_div ] ; aesop;
        norm_cast;
        rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ ) ( by omega );
      simp_all +decide [ Nat.mul_succ ];
      constructor;
      · rw [ ZMod.natCast_eq_zero_iff ];
        rw [ Nat.Prime.dvd_iff_one_le_factorization ] <;> norm_num;
        · rw [ Nat.factorization_choose_eq_zero_of_lt ] ; linarith;
        · exact Fact.out;
        · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
      · norm_cast;
        rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ ) ( by linarith )

/-
If $2|A|-3 < p$, then $|A\hat{+}A| \ge 2|A|-3$.
-/
theorem erdos_heilbronn_small (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p))
    (h_small : 2 * A.card - 3 < p) :
    (restrictedSumset A).card ≥ 2 * A.card - 3 := by
      by_contra h_contra;
      -- Choose a set $C\subseteq \Fp$ such that $A\hat{+}A\subseteq C$ and $|C|=2n-4$.
      obtain ⟨C, hC_sub, hC_card⟩ : ∃ C : Finset (ZMod p), restrictedSumset A ⊆ C ∧ C.card = 2 * A.card - 4 := by
        have h_card_C : (restrictedSumset A).card ≤ 2 * A.card - 4 := by
          omega;
        have := exists_superset_card_eq ( restrictedSumset A ) ( 2 * Finset.card A - 4 ) ( by linarith ) ( by
          rw [ ZMod.card ] ; omega; ) ; aesop;
      -- Fix an element $a_0\in A$ and define $B:=A\setminus\{a_0\}$.
      obtain ⟨a₀, ha₀⟩ : ∃ a₀ ∈ A, True := by
        rcases A.eq_empty_or_nonempty with ( rfl | ⟨ a₀, ha₀ ⟩ ) <;> aesop
      set B := A.erase a₀;
      -- Apply Lemma 6 with $S:=A \quad(|S|=n),\qquad T:=B \quad(|T|=n-1)$, and $f:=F$.
      have h_lemma6 : ∃ a ∈ A, ∃ b ∈ B, (MvPolynomial.eval ![a, b] (F_poly C)) ≠ 0 := by
        apply two_variable_combinatorial_nullstellensatz A B (F_poly C);
        · exact ⟨ a₀, ha₀.1 ⟩;
        · rcases k : Finset.card A with ( _ | _ | k ) <;> simp_all +decide;
          exact Finset.card_pos.mp ( by rw [ Finset.card_erase_of_mem ha₀, k ] ; simp +arith +decide );
        · -- The total degree of $F$ is $1 + |C| = 1 + (2n-4) = 2n-3$.
          have h_deg_F : (F_poly C).totalDegree ≤ 1 + C.card := by
            refine le_trans ( MvPolynomial.totalDegree_mul _ _ ) ?_;
            refine add_le_add ?_ ?_;
            · norm_num [ MvPolynomial.totalDegree ];
              intro b hb; rw [ MvPolynomial.coeff_X', MvPolynomial.coeff_X' ] at hb; aesop;
            · -- The total degree of a product of polynomials is the sum of their total degrees.
              have h_deg_prod : ∀ (S : Finset (ZMod p)), (∏ c ∈ S, (MvPolynomial.X 0 + MvPolynomial.X 1 - (MvPolynomial.C : ZMod p → MvPolynomial (Fin 2) (ZMod p)) c)).totalDegree ≤ S.card := by
                intro S
                induction S using Finset.induction with
                | empty => norm_num;
                | insert c S' hc ih =>
                  rw [ Finset.prod_insert hc ];
                  refine le_trans ( MvPolynomial.totalDegree_mul _ _ ) ?_;
                  refine le_trans ( add_le_add ( MvPolynomial.totalDegree_sub _ _ ) ih ) ?_;
                  simp +decide [ Finset.card_insert_of_notMem hc ];
                  rw [ add_comm ];
                  norm_num [ MvPolynomial.totalDegree ];
                  intro b hb; rw [ MvPolynomial.coeff_X', MvPolynomial.coeff_X' ] at hb; aesop;
              exact h_deg_prod C;
          grind;
        · -- By Lemma 8, we know that the coefficient of $x^{n-1}y^{n-2}$ in $F$ is $\binom{2n-4}{n-2} - \binom{2n-4}{n-1}$.
          have h_coeff : (F_poly C).coeff (Finsupp.equivFunOnFinite.symm ![A.card - 1, B.card - 1]) = (Nat.choose (2 * A.card - 4) (A.card - 2) - Nat.choose (2 * A.card - 4) (A.card - 1) : ZMod p) := by
            convert F_poly_coeff C ( A.card ) hC_card ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩ ) using 1;
            grind;
          rcases n : Finset.card A with ( _ | _ | n ) <;> simp_all
          exact binomial_coeff_nonzero _ h_small ( by linarith );
      obtain ⟨ a, ha, b, hb, h ⟩ := h_lemma6; simp_all +decide [ F_poly ] ;
      simp_all +decide [ Finset.prod_eq_zero_iff, sub_eq_zero ];
      exact h.2 <| hC_sub <| Finset.mem_image.mpr ⟨ ( a, b ), Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ ha, by aesop ⟩, by aesop ⟩, by aesop ⟩

/-
Theorem: The Erdős-Heilbronn inequality in $\mathbb F_p$.
Let $p$ be a prime and let $A\subseteq \Fp$. Then $|A\hat{+}A|\ \ge\ \min(2|A|-3,\ p)$.
-/
theorem erdos_476 (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p)) :
    (restrictedSumset A).card ≥ min (2 * A.card - 3) p := by
      -- Let $n := |A|$.
      set n := A.card with hn_def;
      by_cases h_case : 2 * n - 3 < p;
      · rw [ min_eq_left h_case.le ];
        exact erdos_heilbronn_small p A h_case;
      · by_cases hA : A.card ≥ (p + 3) / 2;
        · have := large_set_full p ( show p ≠ 2 from ?_ ) A hA; aesop;
          rintro rfl ; norm_num at *;
          fin_cases A <;> contradiction;
        · omega

end Erdos476

#print axioms Erdos476.erdos_476
-- 'Erdos476.erdos_476' depends on axioms: [propext, Classical.choice, Quot.sound]
