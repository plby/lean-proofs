/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 124.
https://www.erdosproblems.com/forum/thread/124

Formalization status:
- Partial

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos124b.md
-/
import Mathlib

set_option linter.style.setOption false
set_option aesop.warn.nonterminal false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.unusedSimpArgs false

namespace Erdos124b

/-
An algebraic inequality derived from the sum of reciprocals condition: any lower
bound `m` of `y` is less than or equal to
`1 + \sum (y_i - 1)/(d_i - 1)`.
-/
lemma algebraic_gap (k : ℕ) (d : Fin k → ℕ) (y : Fin k → ℕ)
    (h_ge : ∀ i, 2 ≤ d i)
    (h_sum : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1))
    (h_pos : ∀ i, 0 < y i) :
    ∀ m : ℕ, (∀ i, m ≤ y i) →
      (m : ℚ) ≤ 1 + ∑ i, ((y i : ℚ) - 1) / (d i - 1) := by
  -- Assume m is a lower bound of y.
  intro m hm
  -- Then each fraction is bounded below by the corresponding `m` fraction.
  have h2 : ∀ i,
      ((y i : ℚ) - 1) / ((d i : ℚ) - 1) ≥
        ((m : ℚ) - 1) / ((d i : ℚ) - 1) := by
    exact fun i =>
      div_le_div_of_nonneg_right
        (sub_le_sub_right (mod_cast hm i) _)
        (sub_nonneg.2 <| mod_cast by linarith [h_ge i]);
  -- Sum the inequalities from h2 over all i.
  have h3 :
      ∑ i, ((y i : ℚ) - 1) / ((d i : ℚ) - 1) ≥
        (m - 1) * ∑ i, (1 : ℚ) / ((d i : ℚ) - 1) := by
    simpa only [mul_one_div, Finset.mul_sum _ _ _] using
      Finset.sum_le_sum fun i _ => h2 i;
  by_cases hm0 : m = 0
  · subst m
    have hsum_nonneg : 0 ≤ ∑ i, ((y i : ℚ) - 1) / ((d i : ℚ) - 1) := by
      exact Finset.sum_nonneg fun i _ =>
        div_nonneg
          (sub_nonneg.2 <| by norm_cast; exact Nat.succ_le_of_lt (h_pos i))
          (sub_nonneg.2 <| by norm_cast; linarith [h_ge i])
    linarith
  · have hm_ge_one : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hmminus_nonneg : 0 ≤ (m : ℚ) - 1 := by
      exact sub_nonneg.2 (by exact_mod_cast hm_ge_one)
    have hmul : (m : ℚ) - 1 ≤ ((m : ℚ) - 1) * ∑ i, (1 : ℚ) / ((d i : ℚ) - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left h_sum hmminus_nonneg]
    nlinarith

/-
Brown's criterion: if a sequence of integers starts with 1 and has small gaps,
then every integer is a subset sum.
-/
lemma browns_criterion {f : ℕ → ℕ} (h_mono : Monotone f) (h0 : f 0 = 1)
    (h_gap : ∀ n, f (n + 1) ≤ 1 + ∑ i ∈ Finset.range (n + 1), f i) :
    ∀ n, ∃ s : Finset ℕ, n = ∑ i ∈ s, f i := by
  intro n;
  -- Let's denote the partial sums by $S_n = \sum_{i=0}^n f(i)$.
  set Sn : ℕ → ℕ := fun n => ∑ i ∈ Finset.range (n + 1), f i;
  -- Inductively, every integer bounded by a partial sum is a subset sum.
  have h_ind :
      ∀ n, ∀ m ≤ Sn n,
        ∃ s : Finset ℕ, s ⊆ Finset.range (n + 1) ∧ m = ∑ i ∈ s, f i := by
    -- We proceed by induction on $n$.
    intro n
    induction' n with n ih;
    · -- The base case uses only `f 0 = 1`.
      intro m hm
      cases' m with m m <;> aesop;
    · -- Consider two cases: $m \leq S_n$ and $m > S_n$.
      intro m hm
      by_cases h_case : m ≤ Sn n;
      · exact Exists.elim (ih m h_case) fun s hs =>
          ⟨s, Finset.Subset.trans hs.1 (Finset.range_mono (Nat.le_succ _)), hs.2⟩;
      · -- Since $m > S_n$, we have $m - f(n+1) \leq S_n$.
        have h_sub : m - f (n + 1) ≤ Sn n := by
          simp +zetaDelta at *;
          simpa [ Finset.sum_range_succ ] using hm;
        obtain ⟨ s, hs₁, hs₂ ⟩ := ih ( m - f ( n + 1 ) ) h_sub;
        use s ∪ { n + 1 };
        grind;
  -- The partial sums are large enough to dominate any fixed `n`.
  obtain ⟨k, hk⟩ : ∃ k, Sn k ≥ n := by
    exact ⟨n, le_trans (by norm_num)
      (Finset.sum_le_sum fun _ _ =>
        Nat.one_le_iff_ne_zero.mpr <| by linarith [h_mono <| Nat.zero_le ‹_›])⟩;
  exact Exists.imp ( fun s => And.right ) ( h_ind k n hk )

noncomputable def min_index {k : ℕ} (d : Fin k → ℕ) (e : Fin k → ℕ) (h : k ≠ 0) : Fin k :=
  Classical.choose
    (Finset.exists_min_image Finset.univ (fun i => d i ^ e i)
      (Finset.univ_nonempty_iff.mpr
        (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero h))))

noncomputable def next_e {k : ℕ} (d : Fin k → ℕ) (e : Fin k → ℕ) : Fin k → ℕ :=
  if h : k = 0 then e else
  let i := min_index d e h
  Function.update e i (e i + 1)

noncomputable def e_seq {k : ℕ} (d : Fin k → ℕ) : ℕ → Fin k → ℕ
  | 0 => (fun _ => 0)
  | n + 1 => next_e d (e_seq d n)

noncomputable def u_seq {k : ℕ} (d : Fin k → ℕ) (n : ℕ) : ℕ :=
  let e := e_seq d n
  if h : k ≠ 0 then
    let i := min_index d e h
    d i ^ e i
  else 1

/-
The sequence `u_seq` is non-decreasing.
-/
lemma u_seq_monotone {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0)
    (h_ge : ∀ i, 2 ≤ d i) : Monotone (u_seq d) := by
  -- `u_seq d n` is the minimum value of `d i ^ e_seq d n i` over all `i`.
  have h_min : ∀ n,
      u_seq d n = (Finset.univ.image (fun i => d i ^ (e_seq d n i))).min' (by
        exact ⟨_, Finset.mem_image_of_mem _
          (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hk⟩)⟩) := by
    unfold u_seq; aesop;
    refine' le_antisymm _ _ <;> simp_all +decide [ Finset.min' ];
    · exact fun i =>
        Classical.choose_spec
          (Finset.exists_min_image Finset.univ (fun i => d i ^ e_seq d n i)
            (Finset.univ_nonempty_iff.mpr
              (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)))) |>.2 i
          (Finset.mem_univ i);
    · exact ⟨ _, le_rfl ⟩
  generalize_proofs at *;
  -- `e_seq d (n + 1)` increases one of the components of `e_seq d n` by 1.
  have h_next_e : ∀ n i, e_seq d (n + 1) i ≥ e_seq d n i := by
    -- The updated component increases, and all other components stay fixed.
    intros n i
    simp [next_e];
    rw [show e_seq d (n + 1) = next_e d (e_seq d n) by rfl];
    unfold next_e; aesop;
    rw [ Function.update_apply ] ; aesop;
  intro m n hmn; induction hmn <;> aesop;
  exact le_trans (a_ih a_1)
    (pow_le_pow_right₀ (by linarith [h_ge a_1]) (h_next_e _ _))

/-
The sum of the first `n` terms of `u_seq` is equal to the sum of geometric
series of the bases up to the exponents given by `e_seq d n`.
-/
lemma sum_u_seq_eq {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (h_ge : ∀ i, 2 ≤ d i) :
    ∀ n, ∑ j ∈ Finset.range n, u_seq d j = ∑ i, (d i ^ e_seq d n i - 1) / (d i - 1) := by
  -- We proceed by induction on $n$.
  intro n
  induction' n with n ih;
  · -- At zero, each geometric sum is zero.
    simp [e_seq];
  · -- `u_seq d n` is the power at the current minimum index.
    have h_u_seq :
        u_seq d n =
          d (min_index d (e_seq d n) hk) ^
            (e_seq d n (min_index d (e_seq d n) hk)) := by
      -- Unfold `u_seq` at the nonzero `k`.
      simp [u_seq, min_index];
      -- Since $k \neq 0$, the if condition is false, so we take the else part.
      simp [hk];
    -- `e_seq` increments exactly the current minimum index.
    have h_e_seq : ∀ i,
        e_seq d (n + 1) i =
          if i = min_index d (e_seq d n) hk then e_seq d n i + 1 else e_seq d n i := by
      -- By definition of $e_seq$, we have $e_seq d (n + 1) = next_e d (e_seq d n)$.
      have h_e_seq_def : e_seq d (n + 1) = next_e d (e_seq d n) := by
        rw [show e_seq d (n + 1) = next_e d (e_seq d n) from rfl];
      unfold next_e at h_e_seq_def; aesop;
    simp_all +decide [ Finset.sum_range_succ ];
    -- Split the sum into all indices except the minimum index and the minimum term.
    have h_split :
        ∑ i : Fin k,
          ((if i = min_index d (e_seq d n) hk then
              d (min_index d (e_seq d n) hk) ^
                (e_seq d n (min_index d (e_seq d n) hk) + 1)
            else d i ^ e_seq d n i) - 1) / (d i - 1) =
          (∑ i ∈ Finset.univ.erase (min_index d (e_seq d n) hk),
            ((d i ^ e_seq d n i) - 1) / (d i - 1)) +
          ((d (min_index d (e_seq d n) hk) ^
              (e_seq d n (min_index d (e_seq d n) hk) + 1) - 1) /
            (d (min_index d (e_seq d n) hk) - 1)) := by
      rw [← Finset.sum_erase_add _ _
        (Finset.mem_univ (min_index d (e_seq d n) hk))];
      exact congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun i hi => by aesop) (by aesop);
    rw [h_split, ← Finset.sum_erase_add _ _
      (Finset.mem_univ (min_index d (e_seq d n) hk))];
    simp +decide [Nat.pow_succ', Nat.mul_sub_left_distrib, Nat.mul_div_assoc,
      Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_two.trans_le (h_ge _)))];
    rw [add_assoc, ← Nat.add_mul_div_left _ _ (Nat.sub_pos_of_lt (h_ge _))];
    rw [show
        d (min_index d (e_seq d n) hk) *
            d (min_index d (e_seq d n) hk) ^
              e_seq d n (min_index d (e_seq d n) hk) - 1 =
          (d (min_index d (e_seq d n) hk) ^
              e_seq d n (min_index d (e_seq d n) hk) - 1) +
            (d (min_index d (e_seq d n) hk) - 1) *
              d (min_index d (e_seq d n) hk) ^
                e_seq d n (min_index d (e_seq d n) hk) from
        Nat.sub_eq_of_eq_add <| by
          nlinarith only [
            Nat.sub_add_cancel <| show
              1 ≤ d (min_index d (e_seq d n) hk) from by
                linarith only [h_ge (min_index d (e_seq d n) hk)],
            Nat.sub_add_cancel <| show
              1 ≤ d (min_index d (e_seq d n) hk) ^
                  e_seq d n (min_index d (e_seq d n) hk) from
                Nat.one_le_pow _ _ <| by
                  linarith only [h_ge (min_index d (e_seq d n) hk)]]]

/-
The constructed sequence `u_seq` satisfies the gap condition required by Brown's criterion.
-/
set_option maxHeartbeats 50000000 in
lemma u_seq_gap {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (h_ge : ∀ i, 2 ≤ d i)
    (h_sum : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1)) :
    ∀ n, u_seq d (n + 1) ≤ 1 + ∑ j ∈ Finset.range (n + 1), u_seq d j := by
  -- Let's choose any $n$ and derive the inequality for $u_{n+1}$.
  intro n
  have h_min : ∃ i, ∀ j, d j ^ e_seq d (n + 1) j ≥ d i ^ e_seq d (n + 1) i := by
    simpa using Finset.exists_min_image Finset.univ
      (fun i => d i ^ e_seq d (n + 1) i)
      ⟨⟨0, Nat.pos_of_ne_zero hk⟩, Finset.mem_univ _⟩;
  obtain ⟨i, hi⟩ := h_min
  have h_u_n1 : u_seq d (n + 1) = d i ^ e_seq d (n + 1) i := by
    unfold u_seq; aesop;
    refine' le_antisymm _ _;
    · exact Classical.choose_spec
        (Finset.exists_min_image Finset.univ
          (fun i => d i ^ e_seq d (n + 1) i) ⟨i, Finset.mem_univ i⟩) |>.2 _
        (Finset.mem_univ _) |> le_trans <| by aesop;
    · exact hi _
  have h_sum_u :
      ∑ j ∈ Finset.range (n + 1), u_seq d j =
        ∑ j ∈ Finset.univ, (d j ^ e_seq d (n + 1) j - 1) / (d j - 1) := by
    exact sum_u_seq_eq hk h_ge (n + 1)
  have h_gap :
      d i ^ e_seq d (n + 1) i ≤
        1 + ∑ j ∈ Finset.univ,
          (d j ^ e_seq d (n + 1) j - 1) / (d j - 1) := by
    have h_gap :
        d i ^ e_seq d (n + 1) i ≤
          1 + ∑ j ∈ Finset.univ,
            ((d j ^ e_seq d (n + 1) j - 1) / (d j - 1) : ℚ) := by
      have h_lower_bound :
          ∑ j ∈ Finset.univ,
              ((d j ^ e_seq d (n + 1) j - 1) / (d j - 1) : ℚ) ≥
            ∑ j ∈ Finset.univ,
              ((d i ^ e_seq d (n + 1) i - 1) / (d j - 1) : ℚ) := by
        gcongr ; aesop
        generalize_proofs at *; (
        linarith [ h_ge i_1 ]);
        exact_mod_cast hi _
      generalize_proofs at *; (
      simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
      rw [← Finset.mul_sum _ _ _] at *;
      nlinarith [show (d i : ℚ) ^ e_seq d (n + 1) i ≥ 1 from
        mod_cast Nat.one_le_pow _ _ (by linarith [h_ge i])] ;);
    -- The natural and rational versions of each exact quotient agree.
    have h_sum_eq : ∀ j,
        ((d j ^ e_seq d (n + 1) j - 1) / (d j - 1) : ℚ) =
          ((d j ^ e_seq d (n + 1) j - 1) / (d j - 1) : ℕ) := by
      -- Since $d_j \geq 2$, we have $d_j - 1 \geq 1$, and thus the division is exact.
      intros j
      have h_div_exact :
          (d j ^ e_seq d (n + 1) j - 1) =
            (d j - 1) * (∑ i ∈ Finset.range (e_seq d (n + 1) j), d j ^ i) := by
        zify [ Nat.mul_comm ];
        cases d j <;> cases e_seq d ( n + 1 ) j <;> norm_num [ ← geom_sum_mul ] at *;
      rw [ Nat.cast_div ] <;> norm_num [ h_div_exact ];
      · rw [ Nat.cast_sub ( by linarith [ h_ge j ] ) ] ; norm_num [ ← geom_sum_mul ] ; ring;
      · exact Nat.sub_ne_zero_of_lt ( h_ge j );
    rw [ ← @Nat.cast_le ℚ ] ; aesop;
  aesop

noncomputable def chosen_index {k : ℕ} (d : Fin k → ℕ) (n : ℕ) (hk : k ≠ 0) : Fin k :=
  min_index d (e_seq d n) hk

noncomputable def chosen_exponent {k : ℕ} (d : Fin k → ℕ) (n : ℕ) (hk : k ≠ 0) : ℕ :=
  e_seq d n (chosen_index d n hk)

/-
`u_seq d n` is equal to the power determined by `chosen_index` and `chosen_exponent`.
-/
lemma u_seq_eq_power {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (n : ℕ) :
    u_seq d n = d (chosen_index d n hk) ^ (chosen_exponent d n hk) := by
  unfold u_seq chosen_index chosen_exponent; aesop;

/-
If the same index is chosen at two different steps, the exponent at the later
step is strictly larger.
-/
lemma chosen_exponent_strict_mono {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) :
    ∀ n1 n2, n1 < n2 → chosen_index d n1 hk = chosen_index d n2 hk →
    chosen_exponent d n1 hk < chosen_exponent d n2 hk := by
  intro n1 n2 hn h;
  -- At each step, `e_seq` increments the chosen index and leaves others fixed.
  have h_e_seq : ∀ n i,
      e_seq d (n + 1) i =
        if i = chosen_index d n hk then e_seq d n i + 1 else e_seq d n i := by
    -- This is the definition of `next_e`.
    intros n i
    simp [next_e, e_seq];
    unfold chosen_index; aesop;
  -- For any later `m`, the chosen exponent has increased by at least one.
  have h_exp_inc : ∀ m,
      n1 < m → m ≤ n2 →
        e_seq d m (chosen_index d n1 hk) ≥
          e_seq d n1 (chosen_index d n1 hk) + 1 := by
    -- Induct on the strict inequality from `n1` to `m`.
    intros m hm1 hm2
    induction' hm1 with m ih;
    · aesop;
    · grind;
  exact h_exp_inc n2 hn le_rfl |>
    lt_of_lt_of_le (Nat.lt_succ_self _) |> lt_of_lt_of_le <| by aesop;

/-
The map from step number `n` to the chosen `(index, exponent)` pair is injective.
-/
lemma chosen_pair_injective {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) :
    Function.Injective (fun n => (chosen_index d n hk, chosen_exponent d n hk)) := by
  intros m n hmn
  by_contra hmn_ne;
  norm_num +zetaDelta at *;
  cases lt_or_gt_of_ne hmn_ne <;>
    [ exact absurd
        (chosen_exponent_strict_mono hk _ _ ‹_› hmn.1) (by aesop)
    ; exact absurd
        (chosen_exponent_strict_mono hk _ _ ‹_› (hmn.1.symm)) (by aesop) ]

/-
A subset sum of `u_seq` can be decomposed into numbers `a_i` with 0/1 digits
in base `d_i`.
-/
set_option maxHeartbeats 50000000 in
lemma digits_of_subset_sum_u_seq {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0)
    (h_ge : ∀ i, 2 ≤ d i)
    (S : Finset ℕ) :
    ∃ a : Fin k → ℕ,
      (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧
        ∑ j ∈ S, u_seq d j = ∑ i, a i := by
  -- `E i` collects the exponents chosen at index `i` among the subset `S`.
  set E : Fin k → Finset ℕ := fun i =>
    Finset.image (fun j => chosen_exponent d j hk)
      (Finset.filter (fun j => chosen_index d j hk = i) S);
  refine' ⟨ fun i => ∑ e ∈ E i, d i ^ e, _, _ ⟩ <;> aesop;
  · -- A sum of powers corresponds to digits supported on `E`.
    have h_shift : ∀ (E : Finset ℕ),
        (∑ e ∈ E, d i ^ e) =
          Nat.ofDigits (d i)
            (List.map (fun e => if e ∈ E then 1 else 0)
              (List.range (E.sup id + 1))) := by
      intro E
      have h_shift :
          ∑ e ∈ E, d i ^ e =
            ∑ e ∈ Finset.range (E.sup id + 1), (if e ∈ E then d i ^ e else 0) := by
        simp +decide [ Finset.sum_ite ];
        rw [Finset.inter_eq_right.mpr fun x hx =>
          Finset.mem_range_succ_iff.mpr (Finset.le_sup (f := id) hx)];
      have h_shift : ∀ (n : ℕ) (f : ℕ → ℕ),
          (∑ e ∈ Finset.range n, f e * d i ^ e) =
            Nat.ofDigits (d i) (List.map f (List.range n)) := by
        intro n f;
        induction' n with n ih <;>
          simp_all +decide [Nat.ofDigits, Finset.sum_range_succ];
        ring_nf;
        rw [add_comm 1 n, List.range_succ];
        simp +decide [Nat.ofDigits_append, List.map_append];
        ring_nf;
      convert h_shift ( E.sup id + 1 ) ( fun e => if e ∈ E then 1 else 0 ) using 1 ; aesop;
    rw [ h_shift ];
    intro x hx; rw [ Nat.digits_ofDigits ] at hx <;> norm_num at *;
    · grind +ring;
    · linarith [ h_ge i ];
    · intro a ha; split_ifs <;> linarith [ h_ge i ] ;
    · have :=
        Finset.exists_max_image
          (Finset.filter (fun j => chosen_index d j hk = i) S)
          (fun j => chosen_exponent d j hk)
          ⟨Classical.choose
              (Finset.nonempty_of_ne_empty
                (by aesop_cat :
                  Finset.filter (fun j => chosen_index d j hk = i) S ≠ ∅)),
            Classical.choose_spec
              (Finset.nonempty_of_ne_empty
                (by aesop_cat :
                  Finset.filter (fun j => chosen_index d j hk = i) S ≠ ∅))⟩;
      aesop;
      have :=
        Finset.exists_max_image
          (Finset.filter
            (fun j => chosen_index d j hk = chosen_index d w hk) S)
          (fun j => chosen_exponent d j hk) ⟨w, by aesop⟩;
      aesop;
      exact ⟨w_1, left_1, right_2,
        le_antisymm
          (Finset.le_sup (f := fun j => chosen_exponent d j hk) (by aesop))
          (Finset.sup_le fun x hx =>
            right_1 x (Finset.mem_filter.mp hx |>.1)
              (Finset.mem_filter.mp hx |>.2))⟩;
  · -- Rewrite the sum over `S` as a double sum grouped by chosen index.
    have h_double_sum :
        ∑ j ∈ S, u_seq d j =
          ∑ i, ∑ j ∈ Finset.filter (fun j => chosen_index d j hk = i) S,
            d i ^ (chosen_exponent d j hk) := by
      simp +decide only [Finset.sum_filter];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
      exact u_seq_eq_power hk x;
    rw [ h_double_sum, Finset.sum_congr rfl ] ; aesop;
    rw [ Finset.sum_image ] ; aesop;
    exact fun a ha b hb hab =>
      Classical.not_not.1 fun h =>
        h <| by
          have := chosen_pair_injective hk
            (show
              (chosen_index d a hk, chosen_exponent d a hk) =
                (chosen_index d b hk, chosen_exponent d b hk) from by
              aesop)
          aesop;

/-
The first term of `u_seq` is 1.
-/
lemma u_seq_zero {k : ℕ} {d : Fin k → ℕ} : u_seq d 0 = 1 := by
  unfold u_seq; aesop;

/-
If the sum of reciprocals is 1, then the number of terms `k` cannot be 0.
-/
lemma k_ne_zero_of_sum_eq_one {k : ℕ} {d : Fin k → ℕ}
    (h : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1)) : k ≠ 0 := by
  bound

/-
The Erdos conjecture is true: under the given conditions, every sufficiently
large integer is representable.
-/
theorem erdos_conjecture_true (k : ℕ) (d : Fin k → ℕ)
    (h_ge : ∀ i, 2 ≤ d i)
    (h_sum : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1)) :
    ∀ n, ∃ a : Fin k → ℕ,
    (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧
    n = ∑ i, a i := by
  -- Every natural number can be represented as a sum of terms of `u_seq`.
  have h_dense : ∀ n : ℕ, ∃ s : Finset ℕ, n = ∑ j ∈ s, u_seq d j := by
    -- Apply Brown's criterion with the given hypotheses.
    apply browns_criterion;
    · apply u_seq_monotone;
      · -- The reciprocal sum condition rules out `k = 0`.
        apply k_ne_zero_of_sum_eq_one; assumption;
      · exact fun i => le_trans ( by norm_num ) ( h_ge i );
    · exact u_seq_zero;
    · apply_rules [ u_seq_gap ];
      · aesop;
        norm_num at h_sum;
  -- Each subset sum of `u_seq` decomposes into base-`d i` 0/1 digit numbers.
  have h_terms : ∀ s : Finset ℕ,
      ∃ a : Fin k → ℕ,
        (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧
          ∑ j ∈ s, u_seq d j = ∑ i, a i := by
    -- Apply the lemma `digits_of_subset_sum_u_seq` to the set `s`.
    intros s
    apply digits_of_subset_sum_u_seq;
    · rintro rfl; norm_num at h_sum;
    · exact fun i => le_trans ( by norm_num ) ( h_ge i );
  exact fun n => by
    obtain ⟨s, hs⟩ := h_dense n
    obtain ⟨a, ha₁, ha₂⟩ := h_terms s
    exact ⟨a, ha₁, hs.trans ha₂⟩;

/--
This is a version of Erdős problem 124 that removes a lot of the
unnecessary assumptions made in the other statements, making the
statement stronger.  Compared to the other statements: we assume d_i
is at least 2, instead of 3; we don't assume the d_i are monotonic; we
set c_i = 1; and the conclusion does not have "sufficiently large".
-/
theorem erdos_124 : ∀ k, ∀ d : Fin k → ℕ,
    (∀ i, 2 ≤ d i) → 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1) →
    ∀ n, ∃ a : Fin k → ℕ,
    ∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1} ∧
    n = ∑ i, a i := by
  -- By the induction hypothesis, there exists a sequence $a$ for $n$.
  intro k d hd h_sum n
  obtain ⟨a, ha⟩ :
      ∃ a : Fin k → ℕ,
        (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧ n = ∑ i, a i := by
    -- Apply the theorem erdos_conjecture_true_d with the given conditions.
    apply erdos_conjecture_true k d hd h_sum;
  -- Use this sequence to satisfy the goal.
  use a;
  -- The digit condition and sum identity come from `ha`.
  intro i
  exact ⟨ha.left i, ha.right⟩

open Filter

/--
This is the statement of Erdős problem 124 in the Formal Conjectures
project organized by Google Deep Mind.  Unfortunately, it has an
error, which is that the comment accompanying it says "\geq 1" while
the formal statement says "= 1".  This makes the statement weaker, so
it is still proven.

Here is the original comment:

Let $3\leq d_1 < d_2 < \cdots < d_k$ be integers such that
$$\sum_{1\leq i\leq k}\frac{1}{d_i-1}\geq 1.$$
Can all sufficiently large integers be written as a sum of the shape $\sum_i c_ia_i$
where $c_i\in \{0, 1\}$ and $a_i$ has only the digits $0, 1$ when written in base $d_i$?

Conjectured by Burr, Erdős, Graham, and Li [BEGL96]
-/
theorem formal_conjectures_erdos_124 : (∀ k, ∀ d : Fin k → ℕ,
    (∀ i, 3 ≤ d i) →  StrictMono d → ∑ i : Fin k, (1 : ℚ) / (d i - 1) = 1 →
    ∀ᶠ n in atTop, ∃ c : Fin k → ℕ, ∃ a : Fin k → ℕ,
    ∀ i, c i ∈ ({0, 1} : Finset ℕ) ∧
    ∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1} ∧
    n = ∑ i, c i * a i) ↔ true := by
  constructor
  · intro
    trivial
  · intro _ k d h_ge _ h_sum
    have h_erdos : ∀ n : ℕ, ∃ a : Fin k → ℕ,
        (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧ n = ∑ i, a i := by
      exact erdos_conjecture_true k d (fun i => by linarith [h_ge i]) (by rw [h_sum])
    refine' Filter.Eventually.of_forall fun n => _
    obtain ⟨a, ha_digits, ha_sum⟩ := h_erdos n
    refine' ⟨fun _ => 1, a, fun i => ?_⟩
    exact ⟨by simp, fun j => ⟨ha_digits j, by simpa using ha_sum⟩⟩

set_option maxHeartbeats 50000000 in
/--
This is a modification of the statement of Erdős problem 124 from the
Formal Conjectures project, correcting the "\geq 1" issue.
-/
theorem formal_conjectures_erdos_124_corrected : (∀ k, ∀ d : Fin k → ℕ,
    (∀ i, 3 ≤ d i) →  StrictMono d → 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1) →
    ∀ᶠ n in atTop, ∃ c : Fin k → ℕ, ∃ a : Fin k → ℕ,
    ∀ i, c i ∈ ({0, 1} : Finset ℕ) ∧
    ∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1} ∧
    n = ∑ i, c i * a i) ↔ true := by
  -- Apply the formal_conjectures_erdos_124 theorem to conclude the proof.
  apply Iff.intro;
  · -- The theorem statement is equivalent to `true`.
    apply fun h => rfl;
  · intro ; aesop;
    have := erdos_conjecture_true k d
      (fun i => by linarith [a_1 i])
      (by simpa [← @Rat.cast_inj ℝ] using a_3);
    -- Choose `a = 0`, then use `this` to find the required witnesses.
    use 0;
    intro n hn; obtain ⟨ a, ha₁, ha₂ ⟩ := this n; use fun _ => 1; aesop;

#print axioms erdos_124
-- 'Erdos124b.erdos_124' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms formal_conjectures_erdos_124_corrected
-- 'Erdos124b.formal_conjectures_erdos_124_corrected' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end Erdos124b
