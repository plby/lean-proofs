/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1187.
https://www.erdosproblems.com/forum/thread/1187

Formalization status:
- Partial

Formal authors:
- Codex
- GPT-5.5 xhigh
- Kenta Kitamura

URLs:
- https://www.erdosproblems.com/forum/thread/1187#post-6429
- https://github.com/KitaKen1/erdos-1187-lean
- https://github.com/KitaKen1/erdos-1187-lean/blob/main/SecondSolution.lean
-/
namespace Erdos1187

def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def MonochromaticAP {c : Nat} (color : Nat → Fin c) (a d k : Nat) : Prop :=
  ∀ i : Nat, i < k → color (a + i * d) = color a

def SecondQuestionStatement : Prop :=
  ∀ (c k : Nat), 0 < c → 3 ≤ k → ∀ color : Nat → Fin c,
    ∃ a p : Nat, Prime p ∧ MonochromaticAP color a p k

def color4 (n : Nat) : Fin 4 :=
  ⟨n % 4, Nat.mod_lt n (by decide)⟩

private theorem add_mod_four_eq_self_implies_zero
    (r s : Nat) (hr : r < 4) (hs : s < 4)
    (h : (r + s) % 4 = r) : s = 0 := by
  cases r with
  | zero =>
      cases s with
      | zero => rfl
      | succ s1 =>
          cases s1 with
          | zero => simp at h
          | succ s2 =>
              cases s2 with
              | zero => simp at h
              | succ s3 =>
                  cases s3 with
                  | zero => simp at h
                  | succ _ => contradiction
  | succ r1 =>
      cases r1 with
      | zero =>
          cases s with
          | zero => rfl
          | succ s1 =>
              cases s1 with
              | zero => simp at h
              | succ s2 =>
                  cases s2 with
                  | zero => simp at h
                  | succ s3 =>
                      cases s3 with
                      | zero => simp at h
                      | succ _ => contradiction
      | succ r2 =>
          cases r2 with
          | zero =>
              cases s with
              | zero => rfl
              | succ s1 =>
                  cases s1 with
                  | zero => simp at h
                  | succ s2 =>
                      cases s2 with
                      | zero => simp at h
                      | succ s3 =>
                          cases s3 with
                          | zero => simp at h
                          | succ _ => contradiction
          | succ r3 =>
              cases r3 with
              | zero =>
                  cases s with
                  | zero => rfl
                  | succ s1 =>
                      cases s1 with
                      | zero => simp at h
                      | succ s2 =>
                          cases s2 with
                          | zero => simp at h
                          | succ s3 =>
                              cases s3 with
                              | zero => simp at h
                              | succ _ => contradiction
              | succ _ => contradiction

private theorem step_mod_zero_of_same_color (a p : Nat)
    (h : color4 (a + p) = color4 a) : p % 4 = 0 := by
  have hNat : (a + p) % 4 = a % 4 := by
    simpa [color4] using congrArg Fin.val h
  have h' : ((a % 4) + (p % 4)) % 4 = a % 4 := by
    simpa [Nat.add_mod] using hNat
  exact add_mod_four_eq_self_implies_zero (a % 4) (p % 4)
    (Nat.mod_lt a (by decide)) (Nat.mod_lt p (by decide)) h'

private theorem prime_not_mod_four_zero (p : Nat) (hp : Prime p) :
    p % 4 ≠ 0 := by
  intro hmod
  have h4div : 4 ∣ p := Nat.dvd_of_mod_eq_zero hmod
  have h4 := hp.2 4 h4div
  cases h4 with
  | inl _ => contradiction
  | inr h4p =>
      have h2div : 2 ∣ p := by
        exact ⟨2, by rw [← h4p]⟩
      have h2 := hp.2 2 h2div
      cases h2 with
      | inl _ => contradiction
      | inr h2p =>
          have h42 : (4 : Nat) = 2 := by
            rw [h4p, ← h2p]
          contradiction

theorem prime_step_changes_color4 (a p : Nat) (hp : Prime p) :
    color4 (a + p) ≠ color4 a := by
  intro hsame
  exact prime_not_mod_four_zero p hp (step_mod_zero_of_same_color a p hsame)

theorem no_mono_prime_step_ap_color4
    (a p k : Nat) (hp : Prime p) (hk : 3 ≤ k) :
    ¬ MonochromaticAP color4 a p k := by
  intro hmono
  have h2k : 2 ≤ k := Nat.le_trans (by decide) hk
  have hsame : color4 (a + p) = color4 a := by
    simpa using hmono 1 h2k
  exact prime_step_changes_color4 a p hp hsame

theorem second_question_four_color_counterexample :
    ∃ color : Nat → Fin 4,
      ∀ a p k : Nat, Prime p → 3 ≤ k → ¬ MonochromaticAP color a p k := by
  exact ⟨color4, no_mono_prime_step_ap_color4⟩

theorem second_question_general_statement_is_false :
    ¬ SecondQuestionStatement := by
  intro h
  rcases h 4 3 (by decide) (by decide) color4 with ⟨a, p, hp, hmono⟩
  exact no_mono_prime_step_ap_color4 a p 3 hp (by decide) hmono

#print axioms second_question_general_statement_is_false
-- 'Erdos1187.second_question_general_statement_is_false' depends on axioms: [propext]

end Erdos1187
