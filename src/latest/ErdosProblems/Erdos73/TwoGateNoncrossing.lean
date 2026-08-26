import ErdosProblems.Erdos73.NoncrossingPortBlocks
import ErdosProblems.Erdos73.TreeSwitchContour

/-! Two-gate cuts rule out alternating labels in a contour. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_predicate_change_between {N : ℕ} (P : Fin N → Prop) (i j : Fin N)
    (hij : i ≤ j) (hdiff : ¬(P i ↔ P j)) :
    ∃ s t : Fin N, i ≤ s ∧ s.val + 1 = t.val ∧ t ≤ j ∧ ¬(P s ↔ P t) := by
  by_contra hn
  push Not at hn
  have hh : ∀ m, i.val ≤ m → m ≤ j.val → ∀ hm : m < N, P i ↔ P ⟨m, hm⟩ := by
    intro m him
    induction m, him using Nat.le_induction with
    | base =>
      intro _ _
      rfl
    | succ m him ih =>
      intro hmj hm
      have hm' : m < N := by omega
      exact (ih (by omega) hm').trans
        (hn ⟨m, hm'⟩ ⟨m + 1, hm⟩ (by exact him) rfl (by exact hmj))
  exact hdiff (hh j.val hij (le_refl _) j.isLt)

theorem noncrossing_of_two_gate_cuts {D U : Type*} {N : ℕ}
    (label : D → U) (ρ : Equiv.Perm D) (e : Fin N → D) (hinj : Function.Injective e)
    (hsucc : ∀ i j, i.val + 1 = j.val → e j = ρ (e i))
    (hcuts : ∀ u v, u ≠ v → ∃ P : U → Prop, P u ∧ ¬P v ∧
      ∃ a b : D, ∀ d, ¬(P (label d) ↔ P (label (ρ d))) → d = a ∨ d = b) :
    NoncrossingPortWord (fun i => label (e i)) := by
  intro a b c d hab hbc hcd hac hbd
  dsimp only at hac hbd
  by_contra huv
  obtain ⟨P, ha, hb, x, y, hxy⟩ := hcuts (label (e a)) (label (e b)) huv
  have hc : P (label (e c)) := hac ▸ ha
  have hd : ¬P (label (e d)) := hbd ▸ hb
  obtain ⟨s₁, t₁, has₁, hst₁, ht₁b, h₁⟩ :=
    exists_predicate_change_between (fun i => P (label (e i))) a b hab.le
      (fun he => hb (he.mp ha))
  obtain ⟨s₂, t₂, hbs₂, hst₂, ht₂c, h₂⟩ :=
    exists_predicate_change_between (fun i => P (label (e i))) b c hbc.le
      (fun he => hb (he.mpr hc))
  obtain ⟨s₃, t₃, hcs₃, hst₃, ht₃d, h₃⟩ :=
    exists_predicate_change_between (fun i => P (label (e i))) c d hcd.le
      (fun he => hd (he.mp hc))
  have hs₁₂ : s₁ < s₂ := by exact Fin.mk_lt_mk.mpr (by omega)
  have hs₂₃ : s₂ < s₃ := by exact Fin.mk_lt_mk.mpr (by omega)
  have he₁₂ : e s₁ ≠ e s₂ := fun he => hs₁₂.ne (hinj he)
  have he₂₃ : e s₂ ≠ e s₃ := fun he => hs₂₃.ne (hinj he)
  have he₁₃ : e s₁ ≠ e s₃ := fun he => (hs₁₂.trans hs₂₃).ne (hinj he)
  rw [hsucc s₁ t₁ hst₁] at h₁
  rw [hsucc s₂ t₂ hst₂] at h₂
  rw [hsucc s₃ t₃ hst₃] at h₃
  have hx₁ := hxy (e s₁) h₁
  have hx₂ := hxy (e s₂) h₂
  have hx₃ := hxy (e s₃) h₃
  rcases hx₁ with h | h <;> rcases hx₂ with h' | h' <;> rcases hx₃ with h'' | h''
  all_goals first | exact he₁₂ (h.trans h'.symm) | exact he₂₃ (h'.trans h''.symm) |
    exact he₁₃ (h.trans h''.symm)

namespace TreeSwitchSystem

variable {D U : Type*} [Finite D] (C : TreeSwitchSystem D U)

theorem contour_word_noncrossing {N : ℕ} (e : Fin N → D) (hinj : Function.Injective e)
    (hsucc : ∀ i j, i.val + 1 = j.val → e j = C.contour (e i)) :
    NoncrossingPortWord (fun i => C.label (e i)) := by
  apply noncrossing_of_two_gate_cuts C.label C.contour e hinj hsucc
  intro u v huv
  obtain ⟨w, huw, hv⟩ := exists_treeEdgeSide_separating C.tree C.isTree huv
  exact ⟨treeEdgeSide C.tree u w, treeEdgeSide_self _ _ _, hv, C.cut_crossing_ports huw⟩

end TreeSwitchSystem
end
end Erdos73
