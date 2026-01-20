/-

This is a Lean formalization of a solution to Erdős Problem 275.
https://www.erdosproblems.com/forum/thread/275

The original proof was found by: Selfridge and Crittenden & Vanden
Eynden.

[CrVE70] Crittenden, R. B. and Vanden Eynden, C. L., Any $n$
arithmetic progressions covering the first $2^n$ integers cover all
integers. Proc. Amer. Math. Soc. (1970), 475-481.

This file follows the proof by P. Balister, B. Bollobas, R. Morris,
J. Sahasrabudhe & M. Tiba:

https://link.springer.com/article/10.1007/s10474-019-00980-z


That proof was auto-formalized by Aristotle (from Harmonic).  The
final theorem statement was available from the Formal Conjectures
project.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


import Mathlib

open scoped Classical

/-
Definition of an arithmetic progression and what it means for a family of arithmetic progressions to cover a set or be a covering system.
-/
structure ArithmeticProgression where
  a : ℤ
  d : ℤ
  d_pos : 0 < d

instance : Coe ArithmeticProgression (Set ℤ) where
  coe ap := {x | ∃ n : ℤ, x = ap.a + n * ap.d}

def covers (A : List ArithmeticProgression) (S : Set ℤ) : Prop :=
  S ⊆ ⋃ ap ∈ A, (ap : Set ℤ)

def IsCoveringSystem (A : List ArithmeticProgression) : Prop :=
  covers A Set.univ

/-
Definition of the polynomial $P(z)$ and the lemma that if $x$ is covered by the family, then $\omega^x$ is a root of $P(z)$.
-/
noncomputable def omega (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

noncomputable def associatedPolynomial (A : List ArithmeticProgression) (q : ℕ) : Polynomial ℂ :=
  (A.map (fun ap =>
    let d := ap.d.natAbs
    let term := q / d
    Polynomial.X ^ term - Polynomial.C (omega q ^ (ap.a * term : ℤ))
  )).prod

lemma associatedPolynomial_root_iff_covered (A : List ArithmeticProgression) (q : ℕ) (hq : q > 0)
    (h_dvd : ∀ ap ∈ A, ap.d.natAbs ∣ q) (x : ℤ) :
    (∃ ap ∈ A, x ∈ (ap : Set ℤ)) → (associatedPolynomial A q).eval (omega q ^ x) = 0 := by
  intro h;
  obtain ⟨ ap, hap, n, rfl ⟩ := h;
  -- By definition of $P(z)$, we know that $(\omega^x)^{q/d_i} = \omega^{q/d_i}(\omega^{a_i q/d_i})^n$.
  have h_eval : (omega q ^ (ap.a + n * ap.d)) ^ (q / ap.d.natAbs) = omega q ^ (ap.a * (q / ap.d.natAbs)) := by
    have h_root : omega q ^ (n * ap.d * (q / ap.d.natAbs)) = 1 := by
      have h_root : omega q ^ (ap.d * (q / ap.d.natAbs)) = 1 := by
        have h_root : omega q ^ (q : ℤ) = 1 := by
          norm_num [ omega ];
          rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff ] ; use 1 ; ring_nf ; norm_num [ hq.ne' ];
        cases abs_cases ( ap.d : ℤ ) <;> simp_all +decide
        · rw [ abs_of_nonneg ‹_› ];
          rw [ Int.mul_ediv_cancel' ];
          · exact_mod_cast h_root;
          · exact Int.ofNat_dvd_right.mpr (h_dvd ap hap);
        · exact absurd ‹_› ( not_and_of_not_right _ ( not_lt_of_ge ( le_of_lt ap.d_pos ) ) );
      rw [ mul_assoc, zpow_mul', h_root, one_zpow ];
    convert congr_arg ( fun x : ℂ => x * omega q ^ ( ap.a * ( q / ap.d.natAbs ) ) ) h_root using 1 <;> ring_nf;
    rw [ ← zpow_natCast, ← zpow_mul ] ; ring_nf;
    rw [ ← zpow_add₀ ( show omega q ≠ 0 from by exact ne_of_apply_ne Complex.normSq <| by unfold omega; norm_num [ Complex.normSq_eq_norm_sq, Complex.norm_exp, hq.ne' ] ) ] ; ring_nf;
    grind;
  rw [ associatedPolynomial ];
  rw [ Polynomial.eval_list_prod ];
  rw [ List.prod_eq_zero_iff ] ; aesop

/-
Lemma stating that if a polynomial $P$ has roots at $1, \dots, s-1$ and not at $s$ (where $s > k$), then the shifted polynomials $P_0, \dots, P_k$ are linearly independent.
-/
noncomputable def shiftedPolynomial (P : Polynomial ℂ) (m : ℤ) (q : ℕ) : Polynomial ℂ :=
  P.comp (Polynomial.C (omega q ^ (-m)) * Polynomial.X)

lemma linear_independent_of_triangular (P : Polynomial ℂ) (q : ℕ) (k : ℕ) (s : ℤ)
    (h_root : ∀ x ∈ Finset.Icc 1 (s - 1), P.eval (omega q ^ x) = 0)
    (h_s : P.eval (omega q ^ s) ≠ 0)
    (h_s_gt : s > k) :
    LinearIndependent ℂ (fun m : Fin (k + 1) => shiftedPolynomial P m q) := by
  -- Assume for contradiction that the polynomials $P_0, \ldots, P_k$ are linearly dependent.
  by_contra h_lin_dep
  obtain ⟨f, hf⟩ : ∃ f : Fin (k + 1) → ℂ, (∑ i ∈ Finset.univ, f i • shiftedPolynomial P i q) = 0 ∧ (∃ i, f i ≠ 0) := by
    rw [ Fintype.not_linearIndependent_iff ] at h_lin_dep ; tauto;
  -- Let $\ell$ be the smallest index such that $f_\ell \neq 0$.
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin (k + 1), f ℓ ≠ 0 ∧ ∀ m : Fin (k + 1), m < ℓ → f m = 0 := by
    exact ⟨ Finset.min' ( Finset.univ.filter fun i => f i ≠ 0 ) ⟨ hf.2.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hf.2.choose_spec ⟩ ⟩, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun i => f i ≠ 0 ) ⟨ hf.2.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hf.2.choose_spec ⟩ ⟩ ) |>.2, fun m mn => Classical.not_not.1 fun hnm => mn.not_ge ( Finset.min'_le _ _ <| by aesop ) ⟩;
  -- Since $P(\omega^s) \neq 0$, we have $P_\ell(\omega^{s+\ell}) = P(\omega^s) \neq 0$.
  have h_eval_ell : (shiftedPolynomial P ℓ q).eval (omega q ^ (s + ℓ)) ≠ 0 := by
    unfold shiftedPolynomial; simp_all +decide [ Polynomial.eval_X, Polynomial.eval_C ] ;
    convert h_s using 2 ; group;
    norm_num [ zpow_add₀ ( show omega q ≠ 0 from Complex.exp_ne_zero _ ), zpow_neg ] ; ring_nf;
    norm_num [ show omega q ≠ 0 from Complex.exp_ne_zero _ ];
  -- Since $P(\omega^s) \neq 0$, we have $P_m(\omega^{s+\ell}) = P(\omega^{s-(m-\ell)}) = 0$ for all $m > \ell$.
  have h_eval_m : ∀ m : Fin (k + 1), m > ℓ → (shiftedPolynomial P m q).eval (omega q ^ (s + ℓ)) = 0 := by
    intro m hm_gt_ell
    have h_eval_m_step : (shiftedPolynomial P m q).eval (omega q ^ (s + ℓ)) = P.eval (omega q ^ (s - (m - ℓ))) := by
      unfold shiftedPolynomial; ring_nf;
      simp +decide [ zpow_add₀ ( show omega q ≠ 0 from Complex.exp_ne_zero _ ), zpow_sub₀ ( show omega q ≠ 0 from Complex.exp_ne_zero _ ) ] ; ring_nf;
    rw [ h_eval_m_step, h_root ];
    exact Finset.mem_Icc.mpr ⟨ by linarith [ show ( m : ℤ ) ≤ k from mod_cast Fin.le_last m, show ( ℓ : ℤ ) < m from mod_cast hm_gt_ell ], by linarith [ show ( m : ℤ ) ≤ k from mod_cast Fin.le_last m, show ( ℓ : ℤ ) < m from mod_cast hm_gt_ell ] ⟩;
  replace hf := congr_arg ( Polynomial.eval ( omega q ^ ( s + ℓ ) ) ) hf.1 ; simp_all +decide [ Polynomial.eval_finset_sum ] ;
  rw [ Finset.sum_eq_single ℓ ] at hf <;> simp_all +decide
  exact fun m hm => if hm' : m < ℓ then Or.inl ( hℓ.2 m hm' ) else Or.inr ( h_eval_m m ( lt_of_le_of_ne ( le_of_not_gt hm' ) ( Ne.symm hm ) ) )

/-
Definition of the set of exponents using list sublists to account for duplicates, and the bound on its cardinality.
-/
def exponents_list (A : List ArithmeticProgression) (q : ℕ) : Finset ℕ :=
  (A.sublists.map (fun S => (S.map (fun ap => q / ap.d.natAbs)).sum)).toFinset

lemma exponents_list_card_le (A : List ArithmeticProgression) (q : ℕ) :
    (exponents_list A q).card ≤ 2 ^ A.length := by
  -- The number of sublists of $A$ is $2^{|A|}$.
  have h_sublists : (A.sublists).length = 2 ^ A.length := by
    exact List.length_sublists A;
  exact le_trans ( List.toFinset_card_le _ ) ( h_sublists ▸ by simp +decide )

/-
Lemma stating that the exponents of the associated polynomial are contained in the set of subset sums of the terms $q/d_i$.
-/
lemma support_associatedPolynomial_subset_exponents_list (A : List ArithmeticProgression) (q : ℕ) :
    (associatedPolynomial A q).support ⊆ exponents_list A q := by
  -- By definition of $associatedPolynomial$, its support is contained in the set of subset sums of the terms $q/d_i$.
  intros x hx
  induction' A with ap A ih generalizing x <;> simp_all +decide [ associatedPolynomial ];
  · simp_all +decide [ Polynomial.coeff_one ];
    exact Finset.mem_singleton_self _ |> Finset.mem_of_subset ( Finset.singleton_subset_iff.mpr ( by simp +decide [ exponents_list ] ) );
  · rw [ Polynomial.coeff_mul ] at hx;
    obtain ⟨ y, hy ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx; simp_all +decide [ Polynomial.coeff_X_pow, Polynomial.coeff_C ] ;
    -- By definition of $exponents_list$, we know that $y.2 \in exponents_list A q$.
    have hy2 : y.2 ∈ exponents_list A q := by
      exact ih hy.2.2;
    -- Since $y.1$ is either $0$ or $q / ap.d.natAbs$, we can split into these cases.
    by_cases hy1 : y.1 = 0 ∨ y.1 = q / ap.d.natAbs;
    · cases hy1 <;> simp_all +decide [ exponents_list ];
      · exact ⟨ hy2.choose, List.Sublist.trans hy2.choose_spec.1 ( List.sublist_cons_self _ _ ), hy2.choose_spec.2 ⟩;
      · obtain ⟨ a, ha₁, ha₂ ⟩ := ih hy.2.2; use ap :: a; aesop;
    · grind

/-
Lemma stating that the shifted polynomial lies in the linear span of the monomials corresponding to the support of the original polynomial.
-/
lemma shiftedPolynomial_mem_span_support (P : Polynomial ℂ) (m : ℤ) (q : ℕ) :
    shiftedPolynomial P m q ∈ Submodule.span ℂ (Set.image (fun n => Polynomial.X ^ n) (P.support : Set ℕ)) := by
  -- By definition of $P_m(z)$, we can write it as a linear combination of $z^n$ for $n \in \text{supp}(P)$.
  have h_poly_comb : ∃ (c : ℕ → ℂ), shiftedPolynomial P m q = ∑ n ∈ P.support, c n • (Polynomial.X ^ n) := by
    use fun n => Polynomial.coeff ( shiftedPolynomial P m q ) n;
    ext; simp [shiftedPolynomial];
    grind;
  exact h_poly_comb.elim fun c hc => hc ▸ Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ ( Submodule.subset_span <| Set.mem_image_of_mem _ hn )

/-
Lemma bounding the dimension of the span of the shifted polynomials by $2^{|A|}$.
-/
lemma dimension_span_shiftedPolynomial_le (A : List ArithmeticProgression) (q : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun m : Fin (2 ^ A.length + 1) => shiftedPolynomial (associatedPolynomial A q) m q))) ≤ 2 ^ A.length := by
  -- Let $W$ be the span of the shifted polynomials. We know each shifted polynomial lies in the span of $\{X^n \mid n \in \text{supp}(P)\}$.
  set W := Submodule.span ℂ (Set.range (fun m : Fin (2 ^ A.length + 1) => shiftedPolynomial (associatedPolynomial A q) (m : ℤ) q)) with hW;
  -- Let $V = \text{span}(\{X^n \mid n \in \text{supp}(P)\})$.
  set V := Submodule.span ℂ (Set.image (fun n => Polynomial.X ^ n : ℕ → Polynomial ℂ) (associatedPolynomial A q).support) with hV;
  -- Then $W \subseteq V$.
  have hW_sub_V : W ≤ V := by
    exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr fun m => shiftedPolynomial_mem_span_support _ _ _ );
  -- $\dim(V) \le \dim(\text{span}(\{X^n \mid n \in \text{exponents\_list } A\}))$.
  have hV_dim_le : Module.finrank ℂ V ≤ (exponents_list A q).card := by
    -- Since the support of the associated polynomial is a subset of the exponents list, the dimension of the span of the monomials corresponding to the support is at most the cardinality of the exponents list.
    have h_support_subset_exponents_list : (associatedPolynomial A q).support ⊆ exponents_list A q := by
      exact support_associatedPolynomial_subset_exponents_list A q;
    have hV_dim_le : Module.finrank ℂ V ≤ Finset.card (Finset.image (fun n => Polynomial.X ^ n : ℕ → Polynomial ℂ) (exponents_list A q)) := by
      refine' le_trans ( finrank_span_le_card _ ) _;
      exact Finset.card_le_card fun x hx => by aesop;
    exact hV_dim_le.trans ( Finset.card_image_le );
  refine' le_trans _ ( hV_dim_le.trans _ );
  · apply_rules [ Submodule.finrank_mono ];
    exact Module.Finite.span_of_finite _ <| Set.Finite.image _ <| Set.toFinite _;
  · exact exponents_list_card_le A q

/-
Lemma stating that the associated polynomial evaluates to zero at $\omega^x$ if and only if $x$ is covered by the family of arithmetic progressions.
-/
lemma associatedPolynomial_eval_eq_zero_iff_covered (A : List ArithmeticProgression) (q : ℕ) (hq : q > 0)
    (h_dvd : ∀ ap ∈ A, ap.d.natAbs ∣ q) (x : ℤ) :
    (associatedPolynomial A q).eval (omega q ^ x) = 0 ↔ ∃ ap ∈ A, x ∈ (ap : Set ℤ) := by
  constructor;
  · intro h_eval_zero;
    -- Since $\omega^x$ is a root of $P(z)$, there exists an arithmetic progression $ap$ in $A$ such that $\omega^{xq/d} = \omega^{aq/d}$.
    obtain ⟨ap, hapA, hap_root⟩ : ∃ ap ∈ A, (omega q ^ x) ^ (q / ap.d.natAbs) = (omega q ^ (ap.a * (q / ap.d.natAbs) : ℤ)) := by
      unfold associatedPolynomial at h_eval_zero;
      simp_all +decide [ Polynomial.eval_list_prod ];
      exact ⟨ h_eval_zero.choose, h_eval_zero.choose_spec.1, sub_eq_zero.mp h_eval_zero.choose_spec.2 ⟩;
    -- Since $\omega^{xq/d} = \omega^{aq/d}$, we have $xq/d \equiv aq/d \pmod{q}$.
    have h_cong : (x * (q / ap.d.natAbs) : ℤ) ≡ (ap.a * (q / ap.d.natAbs) : ℤ) [ZMOD q] := by
      have h_cong : Complex.exp (2 * Real.pi * Complex.I * (x * (q / ap.d.natAbs) : ℤ) / q) = Complex.exp (2 * Real.pi * Complex.I * (ap.a * (q / ap.d.natAbs) : ℤ) / q) := by
        convert hap_root using 1 <;> push_cast [ omega ] <;> ring_nf;
        · rw [ ← Complex.exp_int_mul, ← Complex.exp_nat_mul ] ; push_cast [ abs_of_nonneg ( show 0 ≤ ap.d from le_of_lt ( by cases ap ; aesop ) ) ] ; ring_nf;
          cases abs_cases ap.d <;> simp +decide [ * ] ; ring_nf;
          · rw [ Int.cast_div ] <;> norm_num ; ring_nf;
            · simpa [ ← Int.natCast_dvd_natCast, abs_of_nonneg ( by linarith : 0 ≤ ap.d ) ] using h_dvd ap hapA;
            · linarith [ ap.d_pos ];
          · exact absurd ‹_› ( by linarith [ ap.d_pos ] );
        · rw [ ← Complex.exp_int_mul ] ; push_cast ; ring_nf;
      rw [ Complex.exp_eq_exp_iff_exists_int ] at h_cong;
      obtain ⟨ n, hn ⟩ := h_cong; rw [ div_add', div_eq_div_iff ] at hn <;> norm_num [ Complex.ext_iff, Real.pi_ne_zero, hq.ne' ] at *;
      exact Int.modEq_iff_dvd.mpr ⟨ -n, by push_cast [ ← @Int.cast_inj ℝ ] ; nlinarith [ Real.pi_pos ] ⟩;
    -- Since $q$ divides $(x - ap.a) * (q / ap.d.natAbs)$, and $q$ is positive, it follows that $ap.d.natAbs$ divides $(x - ap.a)$.
    have h_div : (ap.d.natAbs : ℤ) ∣ (x - ap.a) := by
      have h_div : (q : ℤ) ∣ ((x - ap.a) * (q / ap.d.natAbs : ℤ)) := by
        convert h_cong.symm.dvd using 1 ; ring;
      refine' Int.dvd_of_mul_dvd_mul_right ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.div_pos ( Nat.le_of_dvd hq <| h_dvd ap hapA ) <| Nat.pos_of_dvd_of_pos ( h_dvd ap hapA ) hq ) _;
      convert h_div using 1 ; norm_cast ; rw [ Nat.mul_div_cancel' ( h_dvd ap hapA ) ];
    cases abs_cases ap.d <;> simp_all +decide
    · exact ⟨ ap, hapA, h_div.choose, by linarith [ h_div.choose_spec ] ⟩;
    · exact ⟨ ap, hapA, h_div.choose, by linarith [ h_div.choose_spec ] ⟩;
  · exact fun a => associatedPolynomial_root_iff_covered A q hq h_dvd x a

/-
Definition of the LCM of the moduli of a list of arithmetic progressions, and a lemma stating it is positive.
-/
def lcmModuli (A : List ArithmeticProgression) : ℕ :=
  A.foldr (fun ap acc => Nat.lcm ap.d.natAbs acc) 1

lemma lcmModuli_pos (A : List ArithmeticProgression) : 0 < lcmModuli A := by
  induction' A using List.reverseRecOn with A ih;
  · exact Nat.zero_lt_succ 0;
  · induction A <;> simp_all +decide [ lcmModuli ];
    linarith [ ih.d_pos ]

/-
Lemma stating that the property of being covered by the family $A$ is periodic with period $\text{lcmModuli}(A)$.
-/
lemma dvd_lcmModuli (A : List ArithmeticProgression) (ap : ArithmeticProgression) (hap : ap ∈ A) :
  ap.d.natAbs ∣ lcmModuli A := by
  induction A generalizing ap with
  | nil => contradiction
  | cons head tail ih =>
    simp [lcmModuli]
    cases hap with
    | head => exact Nat.dvd_lcm_left _ _
    | tail _ h => exact Nat.dvd_trans (ih _ h) (Nat.dvd_lcm_right _ _)

/-
Lemma stating that if $A$ is not a covering system but covers $[1, 2^k]$, there is an uncovered integer in $(2^k, q]$.
-/
lemma exists_uncovered_of_not_covering_system (A : List ArithmeticProgression)
    (h_not_cover : ¬ IsCoveringSystem A)
    (h_cover_interval : Set.Icc 1 (2 ^ A.length) ⊆ ⋃ ap ∈ A, (ap : Set ℤ)) :
    ∃ c : ℤ, 2 ^ A.length < c ∧ c ≤ lcmModuli A ∧ ∀ ap ∈ A, c ∉ (ap : Set ℤ) := by
  -- By `covers_periodic`, for any $k \in \mathbb{Z}$, $x + k q$ is also not covered by $A$.
  obtain ⟨x, hx⟩ : ∃ x : ℤ, (∀ ap ∈ A, ¬(x ∈ (ap : Set ℤ))) := by
    contrapose! h_not_cover;
    exact fun x _ => by obtain ⟨ ap, hap, ⟨ n, hn ⟩ ⟩ := h_not_cover x; exact Set.mem_iUnion₂.mpr ⟨ ap, hap, hn ▸ Set.mem_setOf.mpr ⟨ n, rfl ⟩ ⟩ ;
  -- By `covers_periodic`, for any $k \in \mathbb{Z}$, $x + k q$ is also not covered by $A$. Let's choose $k$ such that $c = x + k q$ satisfies $1 \le c \le q$.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 1 ≤ x + k * (lcmModuli A : ℤ) ∧ x + k * (lcmModuli A : ℤ) ≤ (lcmModuli A : ℤ) := by
    use -((x - 1) / (lcmModuli A : ℤ));
    constructor <;> nlinarith [ Int.mul_ediv_add_emod ( x - 1 ) ( lcmModuli A ), Int.emod_nonneg ( x - 1 ) ( by linarith [ lcmModuli_pos A ] : ( lcmModuli A : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( x - 1 ) ( by linarith [ lcmModuli_pos A ] : ( lcmModuli A : ℤ ) > 0 ), lcmModuli_pos A ];
  -- By `covers_periodic`, $x + k q$ is also not covered by $A$.
  have h_not_covered : ∀ ap ∈ A, ¬(x + k * (lcmModuli A : ℤ) ∈ (ap : Set ℤ)) := by
    intro ap hap
    have h_periodic : ∀ n : ℤ, x + n * (lcmModuli A : ℤ) ∉ (ap : Set ℤ) := by
      intro n hn
      have h_div : ap.d ∣ (lcmModuli A : ℤ) := by
        have h_div : ap.d.natAbs ∣ lcmModuli A := by
          exact dvd_lcmModuli A ap hap;
        exact Int.ofNat_dvd_right.mpr h_div;
      exact hx ap hap <| by obtain ⟨ m, hm ⟩ := hn; obtain ⟨ d, hd ⟩ := h_div; exact ⟨ m - n * d, by linear_combination hm - hd * n ⟩ ;
    exact h_periodic k;
  by_cases h_case : x + k * (lcmModuli A : ℤ) ≤ 2 ^ A.length;
  · exact absurd ( h_cover_interval ⟨ by linarith, h_case ⟩ ) ( by aesop );
  · exact ⟨ x + k * ( lcmModuli A : ℤ ), not_le.mp h_case, hk.2, h_not_covered ⟩

/-
Definition of translation of an arithmetic progression and lemma stating that $x$ is in the translated progression iff $x+k$ is in the original progression.
-/
def translateAP (ap : ArithmeticProgression) (k : ℤ) : ArithmeticProgression where
  a := ap.a - k
  d := ap.d
  d_pos := ap.d_pos

/-
Lemma stating that covering properties are preserved under translation.
-/
lemma covers_translateAP_iff (A : List ArithmeticProgression) (S : Set ℤ) (k : ℤ) :
    covers (A.map (fun ap => translateAP ap k)) {x | x + k ∈ S} ↔ covers A S := by
  unfold covers at *;
  simp_all +decide [ Set.subset_def, translateAP ];
  exact ⟨ fun h x hx => by obtain ⟨ i, hi, n, hn ⟩ := h ( x - k ) ( by simpa ) ; exact ⟨ i, hi, n, by linear_combination' hn ⟩, fun h x hx => by obtain ⟨ i, hi, n, hn ⟩ := h ( x + k ) hx; exact ⟨ i, hi, n, by linear_combination' hn ⟩ ⟩

/-
Lemma stating that the property of being a covering system is preserved under translation.
-/
lemma isCoveringSystem_translateAP_iff (A : List ArithmeticProgression) (k : ℤ) :
    IsCoveringSystem (A.map (fun ap => translateAP ap k)) ↔ IsCoveringSystem A := by
  convert covers_translateAP_iff A Set.univ k using 1

/-
The main theorem: if a family of arithmetic progressions covers $2^k$ consecutive integers, it covers all integers.
-/
theorem theorem_1 (A : List ArithmeticProgression)
    (h : ∃ a, Set.Ioc a (a + (2 : ℤ) ^ A.length) ⊆ ⋃ ap ∈ A, (ap : Set ℤ)) :
    IsCoveringSystem A := by
      by_contra h_not_covering_system;
      -- Let $a$ be such that $A$ covers $(a, a + 2^k]$.
      obtain ⟨a, ha⟩ := h;
      -- Translate the family $A$ by $a$, so that it covers $(0, 2^k]$.
      let A_translated := A.map (fun ap => translateAP ap a);
      have h_translated : Set.Ioc 0 (2 ^ A.length) ⊆ ⋃ ap ∈ A_translated, (ap : Set ℤ) := by
        intro x hx
        have hx_translated : x + a ∈ ⋃ ap ∈ A, (ap : Set ℤ) := by
          exact ha ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩;
        simp +zetaDelta at *;
        obtain ⟨ i, hi, n, hn ⟩ := hx_translated; exact ⟨ i, hi, n, by rw [ show translateAP i a = ⟨ i.a - a, i.d, i.d_pos ⟩ from rfl ] ; linear_combination hn ⟩ ;
      -- Assume for contradiction that $A'$ is not a covering system.
      have h_not_covering_system_translated : ¬IsCoveringSystem A_translated := by
        exact fun h => h_not_covering_system <| by simpa using isCoveringSystem_translateAP_iff _ _ |>.1 h;
      -- Let $q = \text{lcmModuli}(A')$.
      set q := lcmModuli A_translated;
      -- There exists an uncovered integer $c$ with $2^k < c \le q$.
      obtain ⟨c, hc₁, hc₂⟩ : ∃ c : ℤ, 2 ^ A.length < c ∧ c ≤ q ∧ ∀ ap ∈ A_translated, c ∉ (ap : Set ℤ) := by
        have := exists_uncovered_of_not_covering_system A_translated h_not_covering_system_translated;
        simp +zetaDelta at *;
        exact this fun x hx => by rcases Set.mem_iUnion₂.mp ( h_translated ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ) with ⟨ y, hy, ⟨ n, hn ⟩ ⟩ ; exact Set.mem_iUnion₂.mpr ⟨ y, hy, ⟨ n, hn ⟩ ⟩ ;
      -- Let $P$ be the associated polynomial.
      set P := associatedPolynomial A_translated q;
      -- Let $s$ be the minimal positive integer such that $P(\omega^s) \ne 0$.
      obtain ⟨s, hs₁, hs₂⟩ : ∃ s : ℕ, 0 < s ∧ s ≤ q ∧ P.eval (omega q ^ s) ≠ 0 ∧ ∀ t : ℕ, 0 < t → t < s → P.eval (omega q ^ t) = 0 := by
        have h_exists_s : ∃ s : ℕ, 0 < s ∧ s ≤ q ∧ P.eval (omega q ^ s) ≠ 0 := by
          refine' ⟨ Int.natAbs c, _, _, _ ⟩;
          · exact Int.natAbs_pos.mpr ( by linarith [ pow_pos ( zero_lt_two' ℤ ) A.length ] );
          · linarith [ abs_of_pos ( by linarith [ pow_pos ( zero_lt_two' ℤ ) A.length ] : 0 < c ) ];
          · convert associatedPolynomial_eval_eq_zero_iff_covered A_translated q ( Nat.pos_of_ne_zero ?_ ) ?_ c |>.not.mpr ?_ using 1;
            · rw [ ← Int.natAbs_of_nonneg ( by linarith [ pow_pos ( zero_lt_two' ℤ ) A.length ] : 0 ≤ c ) ];
              norm_cast;
            · exact Nat.ne_of_gt <| lcmModuli_pos _;
            · exact fun ap a => dvd_lcmModuli A_translated ap a;
            · aesop;
        exact ⟨ Nat.find h_exists_s, Nat.find_spec h_exists_s |>.1, Nat.find_spec h_exists_s |>.2.1, Nat.find_spec h_exists_s |>.2.2, fun t ht₁ ht₂ => Classical.not_not.1 fun ht₃ => Nat.find_min h_exists_s ht₂ ⟨ ht₁, by linarith [ Nat.find_spec h_exists_s |>.2.1 ], ht₃ ⟩ ⟩;
      -- Since $P$ vanishes on $\{1, \dots, 2^k\}$, we must have $s > 2^k$.
      have hs_gt : s > 2 ^ A.length := by
        have hs_gt : ∀ t : ℕ, 1 ≤ t → t ≤ 2 ^ A.length → P.eval (omega q ^ t) = 0 := by
          intros t ht₁ ht₂;
          apply associatedPolynomial_eval_eq_zero_iff_covered A_translated q (by
          exact Nat.pos_of_ne_zero ( by aesop_cat )) (by
          exact fun ap a => dvd_lcmModuli A_translated ap a) t |>.2;
          simpa using h_translated ⟨ by linarith, by linarith ⟩;
        exact not_le.mp fun h => hs₂.2.1 <| hs_gt s hs₁ h;
      -- By `linear_independent_of_triangular`, the shifted polynomials $P_0, \dots, P_{2^k}$ are linearly independent.
      have h_linear_independent : LinearIndependent ℂ (fun m : Fin (2 ^ A.length + 1) => shiftedPolynomial P m q) := by
        apply linear_independent_of_triangular;
        any_goals exact Nat.cast s;
        · simp +zetaDelta at *;
          intro x hx₁ hx₂; specialize hs₂; have := hs₂.2.2 ( Int.natAbs x ) ( by positivity ) ( by omega ) ; cases abs_cases x <;> simp_all +decide ;
          · cases x <;> aesop;
          · linarith;
        · exact_mod_cast hs₂.2.1;
        · exact_mod_cast hs_gt;
      -- But by `dimension_span_shiftedPolynomial_le`, the dimension is at most $2^k$.
      have h_dimension : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun m : Fin (2 ^ A.length + 1) => shiftedPolynomial P m q))) ≤ 2 ^ A.length := by
        convert dimension_span_shiftedPolynomial_le A_translated q using 1;
        · rw [ List.length_map ];
        · rw [ List.length_map ];
      exact h_dimension.not_gt ( by rw [ finrank_span_eq_card ] <;> aesop )

/-
Definition of minimal covering system and Corollary 2: in a minimal covering system of $k$ progressions, every modulus is at most $2^{k-1}$.
-/
def IsMinimalCoveringSystem (A : List ArithmeticProgression) : Prop :=
  IsCoveringSystem A ∧ ∀ ap ∈ A, ¬ IsCoveringSystem (A.erase ap)

theorem corollary_2 (A : List ArithmeticProgression) (h_min : IsMinimalCoveringSystem A) :
    ∀ ap ∈ A, ap.d.natAbs ≤ 2 ^ (A.length - 1) := by
  intros ap hap
  by_contra h_contra
  have h_I : Set.Ioc ap.a (ap.a + ap.d.natAbs - 1) ⊆ ⋃ ap' ∈ A.erase ap, (ap' : Set ℤ) := by
    intro x hx
    have h_not_ap : x ∉ (ap : Set ℤ) := by
      simp +zetaDelta at *;
      intro n hn; cases abs_cases ap.d <;> nlinarith [ show n = 0 by nlinarith ] ;
    have h_covered : x ∈ ⋃ ap' ∈ A, (ap' : Set ℤ) := by
      exact h_min.1 ( Set.mem_univ x );
    simp +zetaDelta at *;
    grind;
  -- Applying Theorem 1 to $A'$, we conclude that $A'$ covers $\mathbb{Z}$.
  have h_A'_covers : IsCoveringSystem (A.erase ap) := by
    apply theorem_1
    use ap.a;
    refine' Set.Subset.trans _ h_I;
    refine' Set.Ioc_subset_Ioc_right _;
    grind;
  exact absurd h_A'_covers ( by have := h_min.2 ( by aesop ) ; aesop )

/-
Lemma stating that the number of integers in $[0, q)$ congruent to $a$ modulo $d$ is $q/d$ when $d \mid q$.
-/
lemma card_congruence_in_Ico (q : ℕ) (d : ℕ) (a : ℤ) (hq : q > 0) (hd : d > 0) (h_dvd : d ∣ q) :
    ((Finset.Ico 0 q).filter (fun x => (x : ℤ) ≡ a [ZMOD d])).card = q / d := by
  obtain ⟨ k, rfl ⟩ := h_dvd;
  -- The set of integers in [0, d*k) congruent to a modulo d is exactly the set {a_mod_d + m*d | m ∈ Finset.range k}.
  have h_set_eq : Finset.filter (fun x : ℤ => x ≡ a [ZMOD d]) (Finset.Ico 0 (d * k)) = Finset.image (fun m => a % d + m * d) (Finset.range k) := by
    ext aesop;
    simp +zetaDelta at *;
    constructor <;> intro h;
    · rw [ Int.ModEq ] at h;
      exact ⟨ Int.toNat ( aesop / d ), by nlinarith [ Int.emod_add_mul_ediv aesop d, Int.emod_nonneg aesop ( by linarith : ( d : ℤ ) ≠ 0 ), Int.emod_lt_of_pos aesop ( by linarith : ( d : ℤ ) > 0 ), Int.toNat_of_nonneg ( Int.ediv_nonneg ( by linarith : 0 ≤ aesop ) ( by linarith : ( d : ℤ ) ≥ 0 ) ) ], by nlinarith [ Int.emod_add_mul_ediv aesop d, Int.emod_nonneg aesop ( by linarith : ( d : ℤ ) ≠ 0 ), Int.emod_lt_of_pos aesop ( by linarith : ( d : ℤ ) > 0 ), Int.toNat_of_nonneg ( Int.ediv_nonneg ( by linarith : 0 ≤ aesop ) ( by linarith : ( d : ℤ ) ≥ 0 ) ) ] ⟩;
    · rcases h with ⟨ m, hm, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Int.emod_nonneg a ( by linarith : ( d : ℤ ) ≠ 0 ) ], by nlinarith [ Int.emod_lt_of_pos a ( by linarith : ( d : ℤ ) > 0 ) ] ⟩, by simp +decide [ Int.ModEq, Int.add_emod ] ⟩ ;
  convert congr_arg Finset.card h_set_eq using 2;
  · norm_num [ Finset.ext_iff ];
    exact fun x hx => ⟨ fun ⟨ y, hy, hy' ⟩ => ⟨ by linarith, by linarith ⟩, fun ⟨ hy₁, hy₂ ⟩ => ⟨ Int.toNat x, by nlinarith [ Int.toNat_of_nonneg hy₁ ], by rw [ Int.toNat_of_nonneg hy₁ ] ⟩ ⟩;
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hd.ne' ];
    norm_num [ Finset.card_image_of_injective, Function.Injective ]

/-
Lemma stating that the number of integers in $[0, q)$ covered by $A$ is at most the sum of $q/d_i$.
-/
lemma card_intersection_le_sum_div (A : List ArithmeticProgression) (q : ℕ) (hq : q > 0)
    (h_dvd : ∀ ap ∈ A, ap.d.natAbs ∣ q) :
    ((Finset.Ico 0 q).filter (fun x => ∃ ap ∈ A, x ∈ (ap : Set ℤ))).card ≤ (A.map (fun ap => q / ap.d.natAbs)).sum := by
  -- The set of integers in [0, q) covered by A is the union of the sets S_ap = {x ∈ [0, q) | x ∈ ap} for each ap in A.
  set covered_set := ((Finset.Ico 0 q).filter (fun x => ∃ ap ∈ A, x ∈ (ap : Set ℤ))) with hcovered_set_def
  have h_union : covered_set.card ≤ Finset.sum A.toFinset (fun ap => Finset.card ((Finset.Ico 0 q).filter (fun x => x ∈ (ap : Set ℤ)))) := by
    refine' le_trans ( Finset.card_le_card _ ) ( Finset.card_biUnion_le );
    intro x hx; aesop;
  -- For each $ap \in A$, the number of elements in $[0, q)$ that are in $ap$ is exactly $q / ap.d$.
  have h_card_ap : ∀ ap ∈ A, Finset.card ((Finset.Ico 0 q).filter (fun x => x ∈ (ap : Set ℤ))) ≤ q / ap.d.natAbs := by
    intro ap hap
    have h_card_ap_step : Finset.card ((Finset.Ico 0 q).filter (fun x => x ∈ (ap : Set ℤ))) ≤ Finset.card ((Finset.Ico 0 q).filter (fun x => (x : ℤ) ≡ ap.a [ZMOD ap.d])) := by
      refine Finset.card_mono ?_;
      simp +contextual [ Finset.subset_iff, Int.ModEq ];
    refine le_trans h_card_ap_step ?_;
    convert card_congruence_in_Ico q ( Int.natAbs ap.d ) ap.a hq ( Int.natAbs_pos.mpr ap.d_pos.ne' ) ( h_dvd ap hap ) |> le_of_eq using 1;
    cases abs_cases ap.d <;> simp +decide [ *, Int.ModEq ];
  refine le_trans h_union <| le_trans ( Finset.sum_le_sum fun x hx => h_card_ap x <| List.mem_toFinset.mp hx ) ?_;
  have h_sum_le : ∀ (l : List ArithmeticProgression), (∑ x ∈ l.toFinset, q / x.d.natAbs) ≤ (List.map (fun ap => q / ap.d.natAbs) l).sum := by
    intros l
    induction' l with ap l ih;
    · norm_num;
    · by_cases h : ap ∈ l.toFinset <;> simp_all +decide [ Finset.sum_insert ];
      exact le_trans ih ( Nat.le_add_left _ _ );
  exact h_sum_le A

/-
Lemma stating that if the sum of reciprocals of moduli is less than 1, then the sum of $q/d_i$ is less than $q$.
-/
lemma sum_div_lt_q (A : List ArithmeticProgression) (q : ℕ) (hq : q > 0)
    (h_dvd : ∀ ap ∈ A, ap.d.natAbs ∣ q)
    (h_sum : (A.map (fun ap => 1 / (ap.d : ℚ))).sum < 1) :
    (A.map (fun ap => q / ap.d.natAbs)).sum < q := by
  -- By multiplying both sides of the inequality $\sum (1 / d_i) < 1$ by $q$, we obtain $\sum (q / d_i) < q$.
  have h_mul_q : (A.map (fun ap => (q : ℚ) / (ap.d.natAbs : ℚ))).sum < q := by
    convert mul_lt_mul_of_pos_left h_sum ( Nat.cast_pos.mpr hq ) using 1 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, List.sum_map_mul_right ];
    · exact Or.inl ( by congr; ext; rw [ abs_of_pos ] ; exact_mod_cast ArithmeticProgression.d_pos _ );
    · ring;
  have h_mul_q : (A.map (fun ap => (q : ℚ) / (ap.d.natAbs : ℚ))).sum = (A.map (fun ap => (q / ap.d.natAbs : ℕ))).sum := by
    have h_mul_q : ∀ ap ∈ A, (q : ℚ) / (ap.d.natAbs : ℚ) = (q / ap.d.natAbs : ℕ) := by
      intro ap hap; rw [ Nat.cast_div ( h_dvd ap hap ) ] ; norm_num;
      exact ne_of_gt ap.d_pos;
    rw [ List.map_congr_left h_mul_q ] ; norm_num;
    rfl;
  exact_mod_cast h_mul_q ▸ ‹ ( List.map ( fun ap : ArithmeticProgression => ( q : ℚ ) / ap.d.natAbs ) A |> List.sum ) < q ›

/-
Corollary 3: If the sum of reciprocals of moduli is less than 1, then no set of $2^k$ consecutive numbers is covered.
-/
theorem corollary_3 (A : List ArithmeticProgression)
    (h_sum : (A.map (fun ap => 1 / (ap.d : ℚ))).sum < 1) :
    ¬ ∃ a, Set.Ioc a (a + (2 : ℤ) ^ A.length) ⊆ ⋃ ap ∈ A, (ap : Set ℤ) := by
      by_contra h_contra
      obtain ⟨a, ha⟩ := h_contra
      have hq : (Finset.Ico 0 (lcmModuli A)).filter (fun x => ∃ ap ∈ A, (x : ℤ) ∈ (ap : Set ℤ)) = Finset.Ico 0 (lcmModuli A) := by
        -- Since $A$ is a covering system, for any integer $x$, there exists an arithmetic progression $ap \in A$ such that $x \in ap$.
        have h_cover : ∀ x : ℤ, ∃ ap ∈ A, x ∈ (ap : Set ℤ) := by
          have h_cover : IsCoveringSystem A := by
            convert theorem_1 A ⟨ a, ha ⟩ using 1;
          intro x; specialize h_cover; have := h_cover ( Set.mem_univ x ) ; aesop;
        aesop;
      have h_card : ((Finset.Ico 0 (lcmModuli A)).filter (fun x => ∃ ap ∈ A, (x : ℤ) ∈ (ap : Set ℤ))).card ≤ (A.map (fun ap => lcmModuli A / ap.d.natAbs)).sum := by
        convert card_intersection_le_sum_div A ( lcmModuli A ) ( lcmModuli_pos A ) _;
        exact fun ap a => dvd_lcmModuli A ap a;
      have h_card_lt : (A.map (fun ap => lcmModuli A / ap.d.natAbs)).sum < lcmModuli A := by
        convert sum_div_lt_q A ( lcmModuli A ) ( lcmModuli_pos A ) _ h_sum;
        exact fun ap a => dvd_lcmModuli A ap a;
      exact h_card_lt.not_ge ( h_card.trans' ( by rw [ hq ] ; simp +decide [ Finset.card_image_of_injective, Function.Injective ] ) )

open Set

/-
If a family of arithmetic progressions A and a finite set of points S cover an interval of length 2^(|A| + |S|), then A is a covering system.
-/
lemma erdos_275_helper (A : List ArithmeticProgression) (S : Finset ℤ) (k : ℤ)
    (h_cover : Set.Ico k (k + 2 ^ (A.length + S.card)) ⊆ (⋃ ap ∈ A, (ap : Set ℤ)) ∪ S) :
    IsCoveringSystem A := by
      -- Let's choose any $a$ such that the interval $[a, a + 2^{|A|}]$ is covered by $S$.
      obtain ⟨a, ha⟩ : ∃ a : ℤ, Set.Ico a (a + (2 : ℤ) ^ A.length) ⊆ (⋃ ap ∈ A, {x | ∃ n : ℤ, x = ap.a + n * ap.d}) := by
        -- Since $S$ is finite, the interval $[k, k + 2^{|A| + |S|})$ can be split into $2^{|S|}$ intervals of length $2^{|A|}$.
        have h_split : ∃ i ∈ Finset.range (2 ^ S.card), ∀ x ∈ Finset.Ico (k + i * 2 ^ A.length) (k + i * 2 ^ A.length + 2 ^ A.length), x ∉ S := by
          by_contra h_contra;
          -- If for every $i \in \{0, 1, ..., 2^{|S|} - 1\}$, there exists $x \in [k + i * 2^{|A|}, k + i * 2^{|A|} + 2^{|A|})$ such that $x \in S$, then $S$ would contain at least $2^{|S|}$ elements, contradicting its finiteness.
          have h_card_S : S.card ≥ 2 ^ S.card := by
            simp +zetaDelta at *;
            choose! f hf using h_contra;
            have h_card_S : Finset.card (Finset.image f (Finset.range (2 ^ S.card))) ≤ S.card := by
              exact Finset.card_le_card ( Finset.image_subset_iff.mpr fun x hx => hf x ( Finset.mem_range.mp hx ) |>.2.2 );
            rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => by have := hf x ( Finset.mem_range.mp hx ) ; have := hf y ( Finset.mem_range.mp hy ) ; exact_mod_cast ( by nlinarith [ pow_pos ( zero_lt_two' ℤ ) A.length ] : ( x : ℤ ) = y ), Finset.card_range ] at h_card_S;
          exact h_card_S.not_gt ( Nat.recOn S.card ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ ] at * ; linarith );
        obtain ⟨ i, hi, hi' ⟩ := h_split; use k + i * 2 ^ A.length; intro x hx; specialize h_cover ( show x ∈ Set.Ico k ( k + 2 ^ ( A.length + S.card ) ) from ⟨ by nlinarith [ hx.1, pow_pos ( zero_lt_two' ℤ ) A.length, pow_pos ( zero_lt_two' ℤ ) S.card, Finset.mem_range.mp hi, pow_add ( 2 : ℤ ) A.length S.card ], by nlinarith [ hx.2, pow_pos ( zero_lt_two' ℤ ) A.length, pow_pos ( zero_lt_two' ℤ ) S.card, Finset.mem_range.mp hi, pow_add ( 2 : ℤ ) A.length S.card ] ⟩ ) ; aesop;
      -- By Theorem 1, if a family of arithmetic progressions covers $2^k$ consecutive integers, it covers all integers.
      apply theorem_1;
      exact ⟨ a - 1, fun x hx => ha ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ⟩

/--
If a finite system of $r$ congruences $\{ a_i\pmod{n_i} : 1\leq i\leq r\}$ (the $n_i$ are not
necessarily distinct) covers $2^r$ consecutive integers then it covers all integers.

This is best possible as the system $2^{i-1}\pmod{2^i}$ shows. This was proved independently by
Selfridge and Crittenden and Vanden Eynden [CrVE70].
-/
theorem erdos_275 (r : ℕ) (a : Fin r → ℤ) (n : Fin r → ℕ)
    (H : ∃ k : ℤ, ∀ x ∈ Ico k (k + 2 ^ r), ∃ i, x ≡ a i [ZMOD n i]) (x : ℤ) :
    ∃ i, x ≡ a i [ZMOD n i] := by
  have := @erdos_275_helper;
  contrapose! this;
  refine' ⟨ _, _, H.choose, _, _ ⟩;
  exact List.map ( fun i => ⟨ a i, if n i = 0 then 1 else n i, by
    grind ⟩ ) ( List.filter ( fun i => n i ≠ 0 ) ( List.finRange r ) )
  all_goals generalize_proofs at *;
  exact Finset.image ( fun i => a i ) ( Finset.filter ( fun i => n i = 0 ) Finset.univ );
  · intro x hx;
    obtain ⟨ i, hi ⟩ := H.choose_spec x ⟨ hx.1, hx.2.trans_le <| by
      simp +zetaDelta at *;
      refine' pow_le_pow_right₀ ( by decide ) _;
      refine' le_trans ( add_le_add_left ( Finset.card_image_le ) _ ) _;
      rw [ ← Multiset.coe_card ];
      rw [ ← Multiset.toFinset_card_of_nodup ] <;> norm_num [ List.nodup_finRange ];
      · rw [ Finset.card_filter, Finset.card_filter ];
        rw [ ← Finset.sum_add_distrib ] ; exact le_trans ( Finset.sum_le_sum fun _ _ => by aesop ) ( by norm_num ) ;
      · exact List.Nodup.filter _ ( List.nodup_finRange _ ) ⟩;
    by_cases hi' : n i = 0 <;> simp_all +decide [ Int.ModEq ];
    · exact Or.inr ⟨ i, hi', rfl ⟩;
    · exact Or.inl ⟨ i, hi', ( x - a i ) / ( n i : ℤ ), by linarith [ Int.ediv_mul_cancel ( show ( n i : ℤ ) ∣ x - a i from Int.modEq_iff_dvd.mp hi.symm ) ] ⟩;
  · intro h;
    have := h ( Set.mem_univ x ) ; simp_all +decide [ IsCoveringSystem ] ;
    obtain ⟨ i, hi, y, hy ⟩ := this; specialize ‹∀ x_1 : Fin r, ¬x ≡ a x_1 [ZMOD ( n x_1 : ℤ ) ] › i; simp_all +decide [ Int.ModEq ] ;

#print axioms erdos_275
-- 'erdos_275' depends on axioms: [propext, Classical.choice, Quot.sound]
