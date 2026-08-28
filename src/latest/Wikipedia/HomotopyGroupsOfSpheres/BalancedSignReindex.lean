import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
import Mathlib.Logic.Equiv.Fintype

/-! # Reindexing a trace-zero list of signs into equal positive and negative blocks -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

theorem exists_sign_reindex (n : ℕ) (μ : Index n → ℝ)
    (hμ : ∀ a, μ a = 1 ∨ μ a = -1) (hsum : ∑ a, μ a = 0) :
    ∃ e : Equiv.Perm (Index n), ∀ a, μ (e a) = sign n a := by
  classical
  let P := {a : Index n // μ a = 1}
  let Q := {a : Index n // μ a ≠ 1}
  have hP : (∑ a : P, μ a.val) = (Fintype.card P : ℝ) := by
    have he : (fun a : P ↦ μ a.val) = fun _ ↦ (1 : ℝ) := funext fun a ↦ a.property
    rw [he]
    simp
  have hQ : (∑ a : Q, μ a.val) = -(Fintype.card Q : ℝ) := by
    have he : (fun a : Q ↦ μ a.val) = fun _ ↦ (-1 : ℝ) :=
      funext fun a ↦ (hμ a.val).resolve_left a.property
    rw [he]
    simp
  have heqR : (Fintype.card P : ℝ) = (Fintype.card Q : ℝ) := by
    have he := Fintype.sum_subtype_add_sum_subtype (fun a ↦ μ a = 1) μ
    change (∑ a : P, μ a.val) + (∑ a : Q, μ a.val) = ∑ a, μ a at he
    rw [hP, hQ, hsum] at he
    linarith
  have heq : Fintype.card P = Fintype.card Q := by exact_mod_cast heqR
  have hcard : Fintype.card P + Fintype.card Q = n + n := by
    have he := Fintype.card_congr (Equiv.sumCompl (fun a : Index n ↦ μ a = 1))
    simpa only [Fintype.card_sum, Fintype.card_fin] using he
  have hcP : Fintype.card P = n := by omega
  have hcQ : Fintype.card Q = n := by omega
  let eP : Fin n ≃ P := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcP])
  let eQ : Fin n ≃ Q := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcQ])
  let e : Equiv.Perm (Index n) :=
    (Equiv.sumCongr eP eQ).trans (Equiv.sumCompl (fun a ↦ μ a = 1))
  refine ⟨e, ?_⟩
  intro a
  cases a with
  | inl a =>
    change μ (eP a).val = 1
    exact (eP a).property
  | inr a =>
    change μ (eQ a).val = -1
    exact (hμ (eQ a).val).resolve_left (eQ a).property

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
