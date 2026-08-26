import ErdosProblems.Erdos118.CutOrder
import ErdosProblems.Erdos118.ExactSlots

/-!
An actual first joint cut decodes into the initial root and body fronts.
The resulting pending state has canonical exact slots; the input pending
frame's possibly different unused lists are not substituted for them.
-/

namespace Erdos118.FirstCutFronts

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates

private theorem head_eq_of_le_all (C : List ℕ) (hC : C.Pairwise (· < ·))
    (i : ℕ) (hi : i ∈ C) (hmin : ∀ x ∈ C, i ≤ x) : C.headD 0 = i := by
  cases C with
  | nil => simp at hi
  | cons c C =>
    have hci : c ≤ i := by simpa using (hC.imp Nat.le_of_lt).rel_head hi
    exact le_antisymm hci (hmin c (List.mem_cons_self ..))

theorem first_root_head (P : Pending) (S T : Stem) (hS : S.done.length = S.root)
    (hcut : JointCut P S hS T.root) (hexact : ExactAnnotations S T) :
    P.position.stem.rootLabel.headD 0 = P.position.stem.done.length + 1 := by
  have hC : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hcut.labels.root _ rfl)
  apply head_eq_of_le_all _ P.position.stem.label_pairwise _ P.rootSelected
  intro x hx
  have hxS : x ∈ S.rootLabel := by rw [hC]; exact hx
  obtain ⟨i, j, hc, hi⟩ := (hexact.root x).mp hxS
  have hb := (CutOrder.first_cut_bounds S T P.position.toInterior
    (P.position.toInterior_word.trans hcut.ordinary) hc).1
  have hbi : P.position.stem.done.length ≤ i := by simpa [Position.toInterior] using hb
  omega

theorem first_leaf_head (P : Pending) (S T : Stem) (hS : S.done.length = S.root)
    (hcut : JointCut P S hS T.root) (hexact : ExactAnnotations S T) :
    P.position.label.headD 0 = P.position.entries.length := by
  have hiP : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hlabels : P.position.bodyLabels <+: S.bodyLabels := hcut.labels.bodies
  have hiS := hiP.trans_le hlabels.length_le
  have he := hlabels.getElem hiP
  have hlabel : S.bodyLabels[P.position.stem.done.length] = P.position.label := by
    rw [← he]
    simp [Position.bodyLabels, Stem.bodyLabels]
  apply head_eq_of_le_all _ P.position.label_pairwise _ P.leafSelected
  intro x hx
  have hc := (hexact.body P.position.stem.done.length hiS x).mp (hlabel ▸ hx)
  have hb := (CutOrder.first_cut_bounds S T P.position.toInterior
    (P.position.toInterior_word.trans hcut.ordinary) hc).2
  simpa [Position.toInterior] using hb (by simp [Position.toInterior])

theorem earlier_bodies_plain (P : Pending) (S T : Stem) (hS : S.done.length = S.root)
    (hcut : JointCut P S hS T.root) (hexact : ExactAnnotations S T) :
    ∀ a ∈ P.position.stem.done, a.label = [] := by
  intro a ha
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hiP : i < P.position.bodyLabels.length := by
    simp only [Position.bodyLabels, Stem.bodyLabels, List.length_append,
      List.length_map, List.length_singleton]
    omega
  have hlabels : P.position.bodyLabels <+: S.bodyLabels := hcut.labels.bodies
  have hiS := hiP.trans_le hlabels.length_le
  have hxS : x ∈ S.bodyLabels[i] := by
    rw [← hlabels.getElem hiP]
    simpa [Position.bodyLabels, Stem.bodyLabels, List.getElem_append_left, hi] using hx
  have hc := (hexact.body i hiS x).mp hxS
  have hb := (CutOrder.first_cut_bounds S T P.position.toInterior
    (P.position.toInterior_word.trans hcut.ordinary) hc).1
  have hbi : P.position.stem.done.length ≤ i := by simpa [Position.toInterior] using hb
  omega

theorem first_fronts (P : Pending) (S T : Stem) (hS : S.done.length = S.root)
    (hcut : JointCut P S hS T.root) (hexact : ExactAnnotations S T) :
    ∃ k n : ℕ, ∃ A : RootResponses.Setup k, ∃ B : BodyResponses.Setup A.stem n,
      A.stem = P.position.stem ∧ B.position = P.position ∧
      ExactSlots.Exact (.leaf (applyBody (ofRoot A) B)) := by
  have hCpos : 0 < P.position.stem.rootLabel.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem P.rootSelected)
  have hDpos : 0 < P.position.label.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem P.leafSelected)
  let k := P.position.stem.rootLabel.length - 1
  let n := P.position.label.length - 1
  let A : RootResponses.Setup k :=
    { stem := P.position.stem
      label_length := by dsimp [k]; omega
      first_body := (first_root_head P S T hS hcut hexact).symm
      plain := earlier_bodies_plain P S T hS hcut hexact }
  let B : BodyResponses.Setup A.stem n :=
    { position := P.position
      stem_eq := rfl
      label_length := by dsimp [n]; omega
      entries_length := (first_leaf_head P S T hS hcut hexact).symm }
  exact ⟨k, n, A, B, rfl, rfl,
    ExactSlots.step_exact (DecisionStates.Step.body (ofRoot A) B)
      (ExactSlots.step_exact (DecisionStates.Step.root A) trivial)⟩

end Erdos118.FirstCutFronts
