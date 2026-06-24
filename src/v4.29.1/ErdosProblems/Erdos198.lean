/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 198.
https://www.erdosproblems.com/forum/thread/198

Informal authors:
- James E. Baumgartner
- ChatGPT 5.1 Pro
- AlphaProof

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos198.md
-/
import Mathlib

namespace Erdos198

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

def IsInfiniteAP (P : Set ℕ) : Prop :=
  ∃ a d, 0 < d ∧ P = {x | ∃ t : ℕ, x = a + t * d}

def A_seq (n : ℕ) : ℕ := (n + 1).factorial + n

def A : Set ℕ := Set.range A_seq

theorem A_is_Sidon : IsSidon A := by
  -- Assume that $a, b, c, d \in A$ with ordered pairs and equal sums.
  intros a ha b hb c hc d hd hab hcd hsum
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq⟩ := hd;
  -- Without loss of generality, assume $m \leq n$ and $p \leq q$.
  suffices h_wlog :
      ∀ {m n p q : ℕ}, m ≤ n → p ≤ q →
        A_seq m + A_seq n = A_seq p + A_seq q →
        (m = p ∧ n = q) ∨ (m = q ∧ n = p) by
    have hmn : m ≤ n := by
      by_contra hmn
      have hlt : A_seq n < A_seq m := by
        unfold A_seq
        exact add_lt_add_of_le_of_lt (Nat.factorial_le (by omega)) (by omega)
      exact (not_lt_of_ge hab) (by simpa [hm, hn] using hlt)
    have hpq : p ≤ q := by
      by_contra hpq
      have hlt : A_seq q < A_seq p := by
        unfold A_seq
        exact add_lt_add_of_le_of_lt (Nat.factorial_le (by omega)) (by omega)
      exact (not_lt_of_ge hcd) (by simpa [hp, hq] using hlt)
    have hsum_index : A_seq m + A_seq n = A_seq p + A_seq q := by
      simpa [← hm, ← hn, ← hp, ← hq] using hsum
    rcases h_wlog hmn hpq hsum_index with ⟨hmp, hnq⟩ | ⟨hmq, hnp⟩
    · exact ⟨by rw [← hm, ← hp, hmp], by rw [← hn, ← hq, hnq]⟩
    · have hmp : m = p := by omega
      have hnq : n = q := by omega
      exact ⟨by rw [← hm, ← hp, hmp], by rw [← hn, ← hq, hnq]⟩
  -- Assume $m \leq n$, $p \leq q$, and $A_seq m + A_seq n = A_seq p + A_seq q$.
  intro m n p q hmn hpq hsum
  -- Without loss of generality, assume $n \geq q$.
  suffices h_wlog2 :
      ∀ {m n p q : ℕ}, m ≤ n → p ≤ q → n ≥ q →
        A_seq m + A_seq n = A_seq p + A_seq q →
        (m = p ∧ n = q) ∨ (m = q ∧ n = p) by
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
      nlinarith only [mul_pos (Nat.succ_pos q) (Nat.factorial_pos q),
        mul_pos (Nat.succ_pos p) (Nat.factorial_pos p), hpq, Nat.factorial_le hpq];
    linarith [ show A_seq m ≥ 0 from Nat.zero_le _ ];
  · norm_num [ show n = q by linarith ] at *;
    unfold A_seq at hsum;
    exact Or.inl
      (le_antisymm
        (le_of_not_gt fun h => by
          linarith [Nat.factorial_le (by linarith : m + 1 ≥ p + 1)])
        (le_of_not_gt fun h => by
          linarith [Nat.factorial_le (by linarith : p + 1 ≥ m + 1)]))

theorem A_intersects_every_infinite_AP (P : Set ℕ) (hP : IsInfiniteAP P) : (A ∩ P).Nonempty := by
  obtain ⟨a, n, hn, hP_eq⟩ := hP
  -- Let $m = a + n$. Then $a_m = (m+1)! + m$ is in the arithmetic progression $a + tn$.
  set m : ℕ := a + n
  have hm : (Nat.factorial (m + 1)) + m ∈ A ∧ ∃ t : ℕ, (Nat.factorial (m + 1)) + m = a + t * n := by
    constructor
    · exact ⟨_, rfl⟩
    · exact
        ⟨(Nat.factorial (a + n + 1) + n) / n, by
          change Nat.factorial (a + n + 1) + (a + n) =
            a + ((Nat.factorial (a + n + 1) + n) / n) * n
          rw [Nat.div_mul_cancel
            (show n ∣ Nat.factorial (a + n + 1) + n from
              dvd_add (Nat.dvd_factorial hn (by linarith)) (dvd_refl n))]
          omega⟩
  exact ⟨(Nat.factorial (m + 1)) + m, hm.1, by rw [hP_eq]; exact hm.2⟩

theorem complement_A_no_infinite_AP : ¬ ∃ P, IsInfiniteAP P ∧ P ⊆ Aᶜ := by
  -- Assume there exists an infinite AP $P$ in the complement of $A$.
  by_contra h_contra
  obtain ⟨P, hP_inf, hP_compl⟩ := h_contra
  -- Since $P$ is an infinite AP, it must intersect $A$ by the theorem.
  have hP_inter_A : P ∩ A ≠ ∅ := by
    rcases A_intersects_every_infinite_AP P hP_inf with ⟨x, hxA, hxP⟩
    exact Set.nonempty_iff_ne_empty.mp ⟨x, hxP, hxA⟩
  exact hP_inter_A <| Set.eq_empty_iff_forall_notMem.mpr fun x hx => hP_compl hx.1 hx.2
variable {α : Type*} [AddCommMonoid α]

def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

lemma isInfiniteAP_of_IsAPOfLength_top {Y : Set ℕ} (hY : IsAPOfLength Y ⊤) :
    IsInfiniteAP Y := by
  obtain ⟨a, d, hcard, hYeq⟩ := hY
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    have hYsingle : Y = {a} := by
      rw [hYeq, hd0]
      ext x
      simp
    have hfinite : Y.Finite := by
      rw [hYsingle]
      exact Set.finite_singleton a
    have hlt : ENat.card Y < (⊤ : ℕ∞) := by
      simpa using hfinite.encard_lt_top
    rw [hcard] at hlt
    exact (not_lt_of_ge le_rfl) hlt
  refine ⟨a, d, hdpos, ?_⟩
  rw [hYeq]
  ext x
  constructor
  · rintro ⟨n, hn, hx⟩
    refine ⟨n, ?_⟩
    rw [← hx]
    simp
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_, ?_⟩
    · simp
    · simp

theorem erdos_198 : (∀ A : Set ℕ, IsSidon A → (∃ Y, IsAPOfLength Y ⊤ ∧ Y ⊆ Aᶜ)) ↔ False := by
  constructor
  · intro h
    obtain ⟨Y, hYap, hYcomp⟩ := h A A_is_Sidon
    exact complement_A_no_infinite_AP ⟨Y, isInfiniteAP_of_IsAPOfLength_top hYap, hYcomp⟩
  · intro h
    exact False.elim h

#print axioms erdos_198
-- 'Erdos198.erdos_198' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos198
