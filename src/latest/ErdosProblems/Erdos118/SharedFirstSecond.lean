import ErdosProblems.Erdos118.SharedFirstLast
import ErdosProblems.Erdos118.LabelOverlays

/-! A common first selection, and, unless the lower label is singleton,
the lower last selection is the upper second selection. -/

namespace Erdos118.SharedFirstSecond

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open Erdos590.Larson

def Aligned (C D : List ℕ) : Prop :=
  C.length = 1 ∨ (C.headD 0 < C.getLastD 0 ∧ C.getLastD 0 ∈ D ∧
    ∀ x ∈ D, C.headD 0 < x → C.getLastD 0 ≤ x)

theorem labels {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ)
    (hcompat : 0 < k → 0 < l) :
    ∃ C D : List ℕ, C.length = k + 1 ∧ D.length = l + 1 ∧
      C.Pairwise (· < ·) ∧ D.Pairwise (· < ·) ∧
      C.headD 0 = D.headD 0 ∧ Aligned C D ∧
      (∀ x ∈ C, x ∈ H ∧ b < x) ∧ (∀ x ∈ D, x ∈ H ∧ b < x) := by
  obtain ⟨i, hiH, hbi⟩ := hH.exists_gt b
  by_cases hk : k = 0
  · subst k
    obtain ⟨E, hEl, hEi, hE⟩ := InteriorWords.fresh_list hH i l
    refine ⟨[i], i :: E, rfl, by simp [hEl], by simp, ?_, rfl, Or.inl rfl, ?_, ?_⟩
    · exact List.pairwise_cons.mpr ⟨fun x hx ↦ (hE x hx).2, hEi⟩
    · intro x hx
      exact (List.mem_singleton.mp hx).symm ▸ ⟨hiH, hbi⟩
    · intro x hx
      exact (List.mem_cons.mp hx).elim (fun he ↦ he.symm ▸ ⟨hiH, hbi⟩)
        (fun hx ↦ ⟨(hE x hx).1, hbi.trans (hE x hx).2⟩)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hlpos := hcompat hkpos
    obtain ⟨A, E, j, hAk, hEl, hAi, hEi, hAj, _, hjA, hjE, _, hA, hE⟩ :=
      LabelOverlays.shared_extreme_labels hH i (k - 1) (l - 1)
    have hAne : A ≠ [] := by intro he; simp [he] at hAk
    have hlast : (i :: A).getLastD 0 = j := by
      rw [List.getLastD_eq_getLast?, List.getLast?_cons_of_ne_nil hAne]
      simpa only [List.getLastD_eq_getLast?] using hAj
    refine ⟨i :: A, i :: E, ?_, ?_, ?_, ?_, rfl, Or.inr ?_, ?_, ?_⟩
    · simp only [List.length_cons, hAk]; omega
    · simp only [List.length_cons, hEl]; omega
    · exact List.pairwise_cons.mpr ⟨fun x hx ↦ (hA x hx).2.1, hAi⟩
    · exact List.pairwise_cons.mpr ⟨fun x hx ↦ (hE x hx).2.1, hEi⟩
    · rw [hlast]
      refine ⟨(hA j hjA).2.1, List.mem_cons_of_mem _ hjE, ?_⟩
      intro x hx hix
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (Nat.lt_irrefl _ hix).elim
      · exact (hE x hx).2.2
    · intro x hx
      exact (List.mem_cons.mp hx).elim (fun he ↦ he.symm ▸ ⟨hiH, hbi⟩)
        (fun hx ↦ ⟨(hA x hx).1, hbi.trans (hA x hx).2.1⟩)
    · intro x hx
      exact (List.mem_cons.mp hx).elim (fun he ↦ he.symm ▸ ⟨hiH, hbi⟩)
        (fun hx ↦ ⟨(hE x hx).1, hbi.trans (hE x hx).2.1⟩)

theorem body_pair {H : Set ℕ} (hH : H.Infinite)
    (S E : Stem) (hSroom : S.done.length + 1 < S.root) (hEroom : E.done.length + 1 < E.root)
    (hord : S.ordinary = E.ordinary) (b k l : ℕ) (hcompat : 0 < k → 0 < l) :
    ∃ A : BodyResponses.Setup S k, ∃ F : BodyResponses.Setup E l,
      A.position.ordinary = F.position.ordinary ∧ A.position.size = F.position.size ∧
      A.position.entries = F.position.entries ∧
      A.position.label.headD 0 = F.position.label.headD 0 ∧
      Aligned A.position.label F.position.label ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) ∧
      (∀ x ∈ BodyResponses.newWord F.position, x ∈ H ∧ b < x) := by
  obtain ⟨C, D, hCk, hDl, hCi, hDi, hfirst, halign, hC, hD⟩ :=
    labels hH (max b (max S.decorated.sum E.decorated.sum)) k l hcompat
  obtain ⟨A, F, hord, hm, he, hAC, hFD, hAf, hFf⟩ := SharedFirstLast.body_pair_of_labels
    hH S E hSroom hEroom hord b k l C D hCk hDl hCi hDi hfirst hC hD
  exact ⟨A, F, hord, hm, he, by rw [hAC, hFD]; exact hfirst,
    by rw [hAC, hFD]; exact halign, hAf, hFf⟩

end Erdos118.SharedFirstSecond
