import ErdosProblems.Erdos118.RootBuffer

/-! Keep an old root reserve on H while sampling only its new ordinary
suffix in K. Old decorations need not belong to the later alphabet. -/

namespace Erdos118.RootBufferOn

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates

theorem buffer {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) {b k : ℕ} (P : Pending)
    (Z : RootBuffer.Reserve H b k P.position.stem) (hP : ExactSlots.Exact (.leaf P)) {c : ℕ}
    (hR : P.roots = [c]) (hOrd : ∀ x ∈ P.position.ordinary, x ∈ H ∧ b < x) (d : ℕ) :
    ∃ A : RootResponses.Setup k, ∃ w : List ℕ,
      A.stem.ordinary = P.position.ordinary ++ w ∧
      A.stem.root = P.position.stem.root ∧ A.stem.rootLabel = Z.label ∧
      (∀ x ∈ w, x ∈ K ∧ d < x) ∧
      (∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x) := by
  have hc := ExactSlots.pending_next_last_root P hP hR
  have hslot := P.rootSlots.bounded c (hR ▸ List.mem_singleton_self _)
  have hfirst : P.position.stem.done.length + 1 < Z.label.headD 0 :=
    Z.early _ P.rootSelected (hc ▸ hslot.1)
  have hne : Z.label ≠ [] := by intro hnil; have h := Z.card; simp [hnil] at h
  have hlast := Z.below _ (first_mem hne)
  have hmore : P.position.stem.done.length < Z.label.headD 0 - 1 := by omega
  have hroot : Z.label.headD 0 - 1 ≤ P.position.stem.root := by omega
  obtain ⟨A₀, hw⟩ := StemResponses.setup_above P.position (Z.label.headD 0 - 1)
    hmore hroot hK (max b d)
  have hbelow : ∀ x ∈ Z.label, x < A₀.stem.root := by rw [A₀.root_eq]; exact Z.below
  have hcount : A₀.stem.done.length + 1 = Z.label.headD 0 := by rw [A₀.count]; omega
  let A := LabelOverlays.rootSetup A₀.stem Z.label Z.increasing hbelow k Z.card hcount
  have hord : A.stem.ordinary = P.position.ordinary ++ A₀.newWord :=
    (LabelOverlays.plainStem_ordinary A₀.stem Z.label Z.increasing hbelow).trans A₀.ordinary
  refine ⟨A, A₀.newWord, hord, A₀.root_eq, rfl,
    fun x hx ↦ ⟨(hw x hx).1, (le_max_right _ _).trans_lt (hw x hx).2⟩, ?_⟩
  change ∀ x ∈ (LabelOverlays.plainStem A₀.stem Z.label Z.increasing hbelow).decorated,
    x ∈ H ∧ b < x
  apply LabelOverlays.plainStem_supported _ _ _ _ Z.fresh
  rw [A₀.ordinary]
  intro x hx
  exact (List.mem_append.mp hx).elim (hOrd x)
    (fun hx ↦ ⟨hKH (hw x hx).1, (le_max_left _ _).trans_lt (hw x hx).2⟩)

end Erdos118.RootBufferOn
