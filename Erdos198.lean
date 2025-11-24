/-

The original human proof was found by: James E. Baumgartner

Baumgartner, James E. Canonical partition relations. Journal of Symbolic Logic, 40(4):541–554, 1975

That proof was explained by ChatGPT 5.1 Pro from OpenAI.

The LaTeX file output from the previous step was auto-formalized into
Lean by Aristotle from Harmonic.

The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind.

The proof is verified by Lean.  The exact version numbers below may be
necessary to type-check this proof.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

def IsInfiniteAP (P : Set ℕ) : Prop :=
  ∃ a d, 0 < d ∧ P = {x | ∃ t : ℕ, x = a + t * d}

def A_seq (n : ℕ) : ℕ := (n + 1).factorial + n

def A : Set ℕ := Set.range A_seq

theorem A_is_Sidon : IsSidon A := by
  -- Let's assume that $a, b, c, d \in A$ and $a \leq b$, $c \leq d$, and $a + b = c + d$. We need to show that $a = c$ and $b = d$.
  intros a ha b hb c hc d hd hab hcd hsum
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq⟩ := hd;
  -- Without loss of generality, assume $m \leq n$ and $p \leq q$.
  suffices h_wlog : ∀ {m n p q : ℕ}, m ≤ n → p ≤ q → A_seq m + A_seq n = A_seq p + A_seq q → (m = p ∧ n = q) ∨ (m = q ∧ n = p) by
    specialize @h_wlog m n p q ; aesop;
    · by_cases hmn : m ≤ n <;> by_cases hpq : p ≤ q <;> aesop;
      · rw [ le_antisymm hmn hpq ];
      · -- Since $A_seq$ is strictly increasing, we have $A_seq q < A_seq p$.
        have h_A_seq_q_lt_A_seq_p : A_seq q < A_seq p := by
          exact add_lt_add_of_le_of_lt ( Nat.factorial_le ( by linarith ) ) hpq;
        linarith;
      · exact False.elim <| hab.not_lt <| by rw [ A_seq, A_seq ] ; gcongr;
      · unfold A_seq at *;
        linarith [ Nat.factorial_le ( by linarith : m + 1 ≥ n + 1 ), Nat.factorial_le ( by linarith : p + 1 ≥ q + 1 ) ];
    · unfold A_seq at *;
      by_cases hmn : m ≤ n <;> by_cases hpq : p ≤ q <;> aesop;
      · grind;
      · linarith [ Nat.factorial_le ( by linarith : n + 1 ≥ m + 1 ), Nat.factorial_le ( by linarith : p + 1 ≥ q + 1 ) ];
      · linarith [ Nat.factorial_le ( by linarith : n + 1 ≤ m + 1 ) ];
      · linarith [ Nat.factorial_le ( by linarith : n + 1 ≤ m + 1 ), Nat.factorial_le ( by linarith : q + 1 ≤ p + 1 ) ];
  -- Assume $m \leq n$, $p \leq q$, and $A_seq m + A_seq n = A_seq p + A_seq q$.
  intro m n p q hmn hpq hsum
  -- Without loss of generality, assume $n \geq q$.
  suffices h_wlog2 : ∀ {m n p q : ℕ}, m ≤ n → p ≤ q → n ≥ q → A_seq m + A_seq n = A_seq p + A_seq q → (m = p ∧ n = q) ∨ (m = q ∧ n = p) by
    by_cases hnq : n ≥ q;
    · exact h_wlog2 hmn hpq hnq hsum;
    · specialize @h_wlog2 p q m n hpq hmn ( by linarith ) ( by linarith ) ; aesop;
  -- If $n > q$, then $A_seq n > A_seq q + A_seq p$ since $A_seq$ is strictly increasing.
  intros m n p q hmn hpq hnq hsum
  by_cases hn : n > q;
  · -- Since $n > q$, we have $A_seq n \geq A_seq (q + 1)$.
    have h_an_ge_aq1 : A_seq n ≥ A_seq (q + 1) := by
      exact monotone_nat_of_le_succ ( fun n => by unfold A_seq; gcongr <;> linarith ) hn;
    -- Since $A_seq$ is strictly increasing, we have $A_seq (q + 1) > A_seq q + A_seq p$.
    have h_aq1_gt_aq_ap : A_seq (q + 1) > A_seq q + A_seq p := by
      unfold A_seq;
      norm_num [ Nat.factorial_succ ];
      nlinarith only [ mul_pos ( Nat.succ_pos q ) ( Nat.factorial_pos q ), mul_pos ( Nat.succ_pos p ) ( Nat.factorial_pos p ), hpq, Nat.factorial_le hpq ];
    linarith [ show A_seq m ≥ 0 from Nat.zero_le _ ];
  · norm_num [ show n = q by linarith ] at *;
    unfold A_seq at hsum;
    exact Or.inl ( le_antisymm ( le_of_not_gt fun h => by linarith [ Nat.factorial_le ( by linarith : m + 1 ≥ p + 1 ) ] ) ( le_of_not_gt fun h => by linarith [ Nat.factorial_le ( by linarith : p + 1 ≥ m + 1 ) ] ) )

theorem A_intersects_every_infinite_AP (P : Set ℕ) (hP : IsInfiniteAP P) : (A ∩ P).Nonempty := by
  obtain ⟨ a, n, hn, h ⟩ := hP ; aesop;
  -- Let $m = a + n$. Then $a_m = (m+1)! + m$ is in the arithmetic progression $a + tn$.
  set m : ℕ := a + n
  have hm : (Nat.factorial (m + 1)) + m ∈ A ∧ ∃ t : ℕ, (Nat.factorial (m + 1)) + m = a + t * n := by
    aesop;
    · exact ⟨ _, rfl ⟩;
    · exact ⟨ ( Nat.factorial ( a + n + 1 ) + n ) / n, by linarith [ Nat.div_mul_cancel ( show n ∣ Nat.factorial ( a + n + 1 ) + n from dvd_add ( Nat.dvd_factorial hn ( by linarith ) ) ( dvd_refl n ) ) ] ⟩
  use (Nat.factorial (m + 1)) + m; aesop

theorem complement_A_no_infinite_AP : ¬ ∃ P, IsInfiniteAP P ∧ P ⊆ Aᶜ := by
  -- Assume there exists an infinite AP $P$ in the complement of $A$.
  by_contra h_contra
  obtain ⟨P, hP_inf, hP_compl⟩ := h_contra

  -- Since $P$ is an infinite AP, it must intersect $A$ by the theorem.
  have hP_inter_A : P ∩ A ≠ ∅ := by
    have := A_intersects_every_infinite_AP P hP_inf; aesop;
    rw [ Set.inter_comm ] at a; aesop;
  exact hP_inter_A <| Set.eq_empty_of_forall_not_mem fun x hx => hP_compl hx.1 hx.2
variable {α : Type*} [AddCommMonoid α]

def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

theorem erdos_198 : (∀ A : Set ℕ, IsSidon A → (∃ Y, IsAPOfLength Y ⊤ ∧ Y ⊆ Aᶜ)) ↔ False := by
  bound;
  · -- Apply the assumption `a` to the specific Sidon set `A` we constructed.
    obtain ⟨Y, hY⟩ := a A A_is_Sidon;
    -- Since Y is an infinite arithmetic progression, there must be some element in Y that is also in A.
    obtain ⟨y, hyY, hyA⟩ : ∃ y ∈ Y, y ∈ A := by
      obtain ⟨ a, d, hd, h ⟩ := hY.1;
      -- Since $A$ intersects every infinite arithmetic progression, there must be some element in $Y$ that is also in $A$.
      have h_inter : (A ∩ {x | ∃ n : ℕ, x = a + n * d}).Nonempty := by
        have := A_intersects_every_infinite_AP { x | ∃ n : ℕ, x = a + n * d } ⟨ a, d, by
          rcases d with ( _ | _ | d ) <;> simp_all +decide [ Set.subset_def ], rfl ⟩ ; aesop;
      obtain ⟨ y, hyA, hyY ⟩ := h_inter; use y; aesop;
    exact hY.2 hyY hyA;
  · -- Since we have a contradiction, we can use the `contradiction` tactic to close the goal.
    contradiction