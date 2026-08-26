import ErdosProblems.Erdos1123.Coupling
import Mathlib.Tactic.Tauto

/-! # Adjoining one pair of sets to a countable Boolean algebra -/

namespace Erdos1123

variable {α β : Type*}

/-- Use one old pair on the new set and another old pair on its complement. -/
def mix (x p q : Set α × Set β) : Set α × Set β := (p ⊓ x) ⊔ (q ⊓ xᶜ)

theorem mix_sup (x p q r s : Set α × Set β) :
    mix x p q ⊔ mix x r s = mix x (p ⊔ r) (q ⊔ s) := by
  apply Prod.ext <;> ext z <;> simp [mix] <;> tauto

theorem mix_inf (x p q r s : Set α × Set β) :
    mix x p q ⊓ mix x r s = mix x (p ⊓ r) (q ⊓ s) := by
  apply Prod.ext <;> ext z <;> simp [mix] <;> tauto

theorem mix_compl (x p q : Set α × Set β) :
    (mix x p q)ᶜ = mix x pᶜ qᶜ := by
  apply Prod.ext <;> ext z <;> simp [mix] <;> tauto

@[simp] theorem mix_same (x p : Set α × Set β) : mix x p p = p := by
  apply Prod.ext <;> ext z <;> simp [mix]

@[simp] theorem mix_top_bot (x : Set α × Set β) : mix x ⊤ ⊥ = x := by
  simp [mix]

/-- The Boolean algebra obtained by adjoining `x`; its two-piece normal form
makes both countability and the mass-preservation argument explicit. -/
def splitAlgebra (L : BooleanSubalgebra (Set α × Set β)) (x : Set α × Set β) :
    BooleanSubalgebra (Set α × Set β) where
  carrier := {a | ∃ p ∈ L, ∃ q ∈ L, a = mix x p q}
  supClosed' := by
    rintro a ⟨p, hp, q, hq, rfl⟩ b ⟨r, hr, s, hs, rfl⟩
    exact ⟨p ⊔ r, L.sup_mem hp hr, q ⊔ s, L.sup_mem hq hs, mix_sup x p q r s⟩
  infClosed' := by
    rintro a ⟨p, hp, q, hq, rfl⟩ b ⟨r, hr, s, hs, rfl⟩
    exact ⟨p ⊓ r, L.inf_mem hp hr, q ⊓ s, L.inf_mem hq hs, mix_inf x p q r s⟩
  compl_mem' := by
    rintro a ⟨p, hp, q, hq, rfl⟩
    exact ⟨pᶜ, L.compl_mem hp, qᶜ, L.compl_mem hq, mix_compl x p q⟩
  bot_mem' := ⟨⊥, L.bot_mem, ⊥, L.bot_mem, (mix_same x ⊥).symm⟩

theorem le_splitAlgebra (L : BooleanSubalgebra (Set α × Set β)) (x : Set α × Set β) :
    L ≤ splitAlgebra L x := by
  intro p hp
  exact ⟨p, hp, p, hp, (mix_same x p).symm⟩

theorem mem_splitAlgebra (L : BooleanSubalgebra (Set α × Set β)) (x : Set α × Set β) :
    x ∈ splitAlgebra L x :=
  ⟨⊤, L.top_mem, ⊥, L.bot_mem, (mix_top_bot x).symm⟩

theorem splitAlgebra_countable (L : BooleanSubalgebra (Set α × Set β)) [Countable L]
    (x : Set α × Set β) : (splitAlgebra L x : Set (Set α × Set β)).Countable := by
  have h := Set.countable_range (fun pq : L × L => mix x pq.1.val pq.2.val)
  apply h.mono
  rintro a ⟨p, hp, q, hq, rfl⟩
  exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩

end Erdos1123
