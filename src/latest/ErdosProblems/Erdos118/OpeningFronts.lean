import ErdosProblems.Erdos118.DecoratedFrontiers

/-!
Initial fronts at an arbitrary first proper threshold. This permits a
second word to open after an already realized opposite prefix.
-/

namespace Erdos118.OpeningFronts

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates
open PrefixRealization (below)

theorem cut_minimal_of_split (S T : Stem) (hS : S.done.length = S.root)
    (P : Pending) (z : ℕ) (hP : JointCut P S hS z) (p u : List ℕ)
    (hsplit : T.ordinary = p ++ z :: u) (hbefore : ∀ x ∈ p, x < S.root)
    (i j : ℕ) (hc : Cut S T i j) :
    P.position.stem.done.length ≤ i ∧
      (P.position.stem.done.length = i → P.position.entries.length ≤ j) := by
  obtain ⟨y, hy, hp, Q, hQ, hi, hj⟩ := hc
  have hzy : z ≤ y := by
    rw [hsplit] at hy
    rcases List.mem_append.mp hy with hy | hy
    · have hnil : below y S.ordinary = [] := by
        simp [below, Stem.ordinary, Nat.not_lt.mpr (hbefore y hy).le]
      exact (hp.1 hnil).elim
    · have htail := (List.pairwise_append.mp
        (hsplit ▸ T.increasing.sublist T.ordinary_sublist)).2.1
      simpa only [List.head_cons] using (htail.imp Nat.le_of_lt).rel_head hy
  have hprefix : P.position.toInterior.word <+: Q.word := by
    rw [Position.toInterior_word, hP.ordinary, hQ]
    exact CutOrder.below_prefix hzy _
  have hb := CutOrder.interior_prefix_counts hprefix
  have hbi : P.position.stem.done.length ≤ i := by
    simpa only [Position.toInterior, List.length_map, hi] using hb.1
  refine ⟨hbi, ?_⟩
  intro he
  have he' : P.position.toInterior.done.length = Q.done.length := by
    simpa only [Position.toInterior, List.length_map, hi] using he
  simpa only [Position.toInterior, hj] using (hb.2 he').2.2.length_le

private theorem head_eq_of_le_all (C : List ℕ) (hC : C.Pairwise (· < ·))
    (i : ℕ) (hi : i ∈ C) (hmin : ∀ x ∈ C, i ≤ x) : C.headD 0 = i := by
  cases C with
  | nil => simp at hi
  | cons c C =>
    have hci : c ≤ i := by simpa using (hC.imp Nat.le_of_lt).rel_head hi
    exact le_antisymm hci (hmin c (List.mem_cons_self ..))

theorem fronts_of_minimal (S T : Stem) (hS : S.done.length = S.root)
    (P : Pending) {z : ℕ} (hP : JointCut P S hS z) (hexact : ExactAnnotations S T)
    (hmin : ∀ i j, Cut S T i j → P.position.stem.done.length ≤ i ∧
      (P.position.stem.done.length = i → P.position.entries.length ≤ j)) :
    ∃ k n : ℕ, ∃ A : RootResponses.Setup k, ∃ Q : BodyResponses.Setup A.stem n,
      A.stem = P.position.stem ∧ Q.position = P.position ∧
      ExactSlots.Exact (.leaf (applyBody (ofRoot A) Q)) := by
  have hC : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hP.labels.root _ rfl)
  have hrootHead : P.position.stem.rootLabel.headD 0 = P.position.stem.done.length + 1 := by
    apply head_eq_of_le_all _ P.position.stem.label_pairwise _ P.rootSelected
    intro x hx
    have hxS : x ∈ S.rootLabel := hC ▸ hx
    obtain ⟨i, j, hc, hi⟩ := (hexact.root x).mp hxS
    have hbi := (hmin i j hc).1
    omega
  have hlabels : P.position.bodyLabels <+: S.bodyLabels := hP.labels.bodies
  have hiP : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hiS := hiP.trans_le hlabels.length_le
  have hD : S.bodyLabels[P.position.stem.done.length] = P.position.label := by
    rw [← hlabels.getElem hiP]
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hleafHead : P.position.label.headD 0 = P.position.entries.length := by
    apply head_eq_of_le_all _ P.position.label_pairwise _ P.leafSelected
    intro x hx
    have hc := (hexact.body P.position.stem.done.length hiS x).mp (hD ▸ hx)
    exact (hmin _ _ hc).2 rfl
  have hplain : ∀ a ∈ P.position.stem.done, a.label = [] := by
    intro a ha
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hiP' : i < P.position.bodyLabels.length := by
      simp only [Position.bodyLabels, Stem.bodyLabels, List.length_append,
        List.length_map, List.length_singleton]
      omega
    have hiS' := hiP'.trans_le hlabels.length_le
    have hxS : x ∈ S.bodyLabels[i] := by
      rw [← hlabels.getElem hiP']
      simpa [Position.bodyLabels, Stem.bodyLabels, List.getElem_append_left, hi] using hx
    have hc := (hexact.body i hiS' x).mp hxS
    have hbi := (hmin i x hc).1
    omega
  have hCpos : 0 < P.position.stem.rootLabel.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem P.rootSelected)
  have hDpos : 0 < P.position.label.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem P.leafSelected)
  let k := P.position.stem.rootLabel.length - 1
  let n := P.position.label.length - 1
  let A : RootResponses.Setup k :=
    { stem := P.position.stem
      label_length := by dsimp [k]; omega
      first_body := hrootHead.symm, plain := hplain }
  let Q : BodyResponses.Setup A.stem n :=
    { position := P.position, stem_eq := rfl
      label_length := by dsimp [n]; omega
      entries_length := hleafHead.symm }
  exact ⟨k, n, A, Q, rfl, rfl,
    ExactSlots.step_exact (DecisionStates.Step.body (ofRoot A) Q)
      (ExactSlots.step_exact (DecisionStates.Step.root A) trivial)⟩

end Erdos118.OpeningFronts
