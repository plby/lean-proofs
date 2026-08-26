/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A finite avoidance recurrence for the Lovasz local lemma.
Informal argument: the usual induction on the family of avoided events.
Formal author: OpenAI Codex.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos1189

open Finset

variable {α : Type*} [DecidableEq α]

/-- Multiply successive lower bounds for the probability of avoiding one more event. -/
lemma avoidance_product_lower (p : Finset α → ℝ) (r : α → ℝ) (S T D : Finset α)
    (hr : ∀ a ∈ S, 0 ≤ r a)
    (hstep : ∀ U ⊆ S, ∀ a ∈ S, a ∉ U → r a * p U ≤ p (insert a U))
    (hT : T ⊆ S) (hD : D ⊆ S) (hdisj : Disjoint T D) :
    (∏ a ∈ D, r a) * p T ≤ p (T ∪ D) := by
  revert hD hdisj
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D ha ih =>
    intro hD hdisj
    have haS : a ∈ S := hD (mem_insert_self _ _)
    have hDS : D ⊆ S := (subset_insert _ _).trans hD
    have hTD : Disjoint T D := hdisj.mono_right (subset_insert _ _)
    have haT : a ∉ T := fun haT => disjoint_left.mp hdisj haT (mem_insert_self _ _)
    have hp := ih hDS hTD
    have hs := hstep (T ∪ D) (union_subset hT hDS) a haS (by simpa only [mem_union] using
      (show ¬ (a ∈ T ∨ a ∈ D) from fun h => h.elim haT ha))
    rw [prod_insert ha, mul_assoc, union_insert]
    exact (mul_le_mul_of_nonneg_left hp (hr a haS)).trans hs

/-- The conditional avoidance estimate underlying the asymmetric local lemma.
`p S` denotes avoidance probability; the two difference assumptions are event
monotonicity and independence from non-neighbours, respectively. -/
theorem localLemma_avoidance_step (A : Finset α) (N : α → Finset α)
    (p : Finset α → ℝ) (μ x : α → ℝ)
    (hp : ∀ S, 0 ≤ p S) (hN : ∀ a ∈ A, N a ⊆ A)
    (hx : ∀ a ∈ A, 0 ≤ x a ∧ x a < 1)
    (hmono : ∀ a ∈ A, ∀ S ⊆ A, ∀ T ⊆ S,
      p S - p (insert a S) ≤ p T - p (insert a T))
    (hind : ∀ a ∈ A, ∀ T ⊆ A, a ∉ T → Disjoint T (N a) →
      p T - p (insert a T) ≤ μ a * p T)
    (hμ : ∀ a ∈ A, μ a ≤ x a * ∏ b ∈ N a, (1 - x b)) :
    ∀ S ⊆ A, ∀ a ∈ A, a ∉ S → (1 - x a) * p S ≤ p (insert a S) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hSA a ha haS
    let I := S \ N a
    let D := S ∩ N a
    have hIS : I ⊆ S := sdiff_subset
    have hDS : D ⊆ S := inter_subset_left
    have hDN : D ⊆ N a := inter_subset_right
    have hdisj : Disjoint I (N a) := sdiff_disjoint
    have hID : I ∪ D = S := by
      ext b
      simp only [I, D, mem_union, mem_sdiff, mem_inter]
      tauto
    have hchain : (∏ b ∈ D, (1 - x b)) * p I ≤ p S := by
      have hstep : ∀ U ⊆ S, ∀ b ∈ S, b ∉ U → (1 - x b) * p U ≤ p (insert b U) := by
        intro U hUS b hb hbU
        have hproper : U ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hUS, by
          intro heq
          exact hbU (heq.symm ▸ hb)⟩
        exact ih U hproper (hUS.trans hSA) b (hSA hb) hbU
      have h := avoidance_product_lower p (fun b => 1 - x b) S I D
        (fun b hb => sub_nonneg.mpr (hx b (hSA hb)).2.le) hstep hIS hDS
        (hdisj.mono_right hDN)
      simpa only [hID] using h
    have hprod : (∏ b ∈ N a, (1 - x b)) ≤ ∏ b ∈ D, (1 - x b) :=
      prod_le_prod_of_subset_of_le_one hDN
        (fun b hb => sub_nonneg.mpr (hx b (hN a ha hb)).2.le)
        (fun b hb _ => sub_le_self _ (hx b (hN a ha hb)).1)
    have hbad : p S - p (insert a S) ≤ x a * p S := calc
      p S - p (insert a S) ≤ p I - p (insert a I) := hmono a ha S hSA I hIS
      _ ≤ μ a * p I := hind a ha I (hIS.trans hSA) (fun hi => haS (hIS hi)) hdisj
      _ ≤ (x a * ∏ b ∈ N a, (1 - x b)) * p I :=
        mul_le_mul_of_nonneg_right (hμ a ha) (hp I)
      _ ≤ (x a * ∏ b ∈ D, (1 - x b)) * p I :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (hx a ha).1) (hp I)
      _ = x a * ((∏ b ∈ D, (1 - x b)) * p I) := mul_assoc _ _ _
      _ ≤ x a * p S := mul_le_mul_of_nonneg_left hchain (hx a ha).1
    linarith

/-- A finite family satisfying the local lemma inequalities has positive avoidance probability. -/
theorem localLemma_avoidance_positive (A : Finset α) (N : α → Finset α)
    (p : Finset α → ℝ) (μ x : α → ℝ)
    (hp0 : 0 < p ∅) (hp : ∀ S, 0 ≤ p S) (hN : ∀ a ∈ A, N a ⊆ A)
    (hx : ∀ a ∈ A, 0 ≤ x a ∧ x a < 1)
    (hmono : ∀ a ∈ A, ∀ S ⊆ A, ∀ T ⊆ S,
      p S - p (insert a S) ≤ p T - p (insert a T))
    (hind : ∀ a ∈ A, ∀ T ⊆ A, a ∉ T → Disjoint T (N a) →
      p T - p (insert a T) ≤ μ a * p T)
    (hμ : ∀ a ∈ A, μ a ≤ x a * ∏ b ∈ N a, (1 - x b)) : 0 < p A := by
  have hstep := localLemma_avoidance_step A N p μ x hp hN hx hmono hind hμ
  have hprod := avoidance_product_lower p (fun a => 1 - x a) A ∅ A
    (fun a ha => sub_nonneg.mpr (hx a ha).2.le) hstep (empty_subset _) Subset.rfl
    (by simp)
  rw [empty_union] at hprod
  exact (mul_pos (prod_pos fun a ha => sub_pos.mpr (hx a ha).2) hp0).trans_le hprod

end Erdos1189
