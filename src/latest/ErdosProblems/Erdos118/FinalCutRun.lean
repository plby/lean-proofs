import ErdosProblems.Erdos118.NextLeafCuts

/-!
After the last selected body, exact annotations force the remaining body
labels to be empty. Literal completion therefore returns the actual final
decorated word. A conservative step still requires the chronological bounds.
-/

namespace Erdos118.FinalCutRun

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates AdaptiveGame

theorem later_label_empty (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (hR : P.roots = [])
    (i : ℕ) (hi : i < S.bodyLabels.length) (hlate : P.position.stem.done.length < i) :
    S.bodyLabels[i] = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro j hj
  have hc := (hexact.body i hi j).mp hj
  have hir : i + 1 ∈ S.rootLabel := (hexact.root (i + 1)).mpr ⟨i, j, hc, rfl⟩
  have hr : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hP.labels.root _ rfl)
  have hm : i + 1 ∈ ExactSlots.above P.position.stem.rootLabel
      (P.position.stem.done.length + 1) := by
    apply List.mem_filter.mpr
    exact ⟨hr ▸ hir, decide_eq_true (Nat.add_lt_add_right hlate 1)⟩
  rw [← hslots.1, hR] at hm
  exact List.not_mem_nil hm

theorem completion_labels (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (hR : P.roots = []) :
    S.bodyLabels = P.position.bodyLabels ++
      List.replicate (S.root - (P.position.stem.done.length + 1)) [] := by
  have hlabels : P.position.bodyLabels <+: S.bodyLabels := hP.labels.bodies
  obtain ⟨ds, hds⟩ := hlabels
  have hlen : ds.length = S.root - (P.position.stem.done.length + 1) := by
    have he := congrArg List.length hds
    simp only [List.length_append, Position.bodyLabels, Stem.bodyLabels,
      List.length_map, List.length_singleton, hS] at he
    omega
  have hd : ∀ D ∈ ds, D = [] := by
    intro D hD
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
    let k := P.position.bodyLabels.length + i
    have hk : k < S.bodyLabels.length := by
      rw [← hds, List.length_append]
      exact Nat.add_lt_add_left hi _
    have hlate : P.position.stem.done.length < k := by
      simp only [k, Position.bodyLabels, Stem.bodyLabels, List.length_append,
        List.length_map, List.length_singleton]
      omega
    have he := later_label_empty S T hS hexact P hP hslots hR k hk hlate
    simpa only [← hds, k, List.getElem_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left] using he
  rw [← hds, List.eq_replicate_of_mem hd, hlen]

private theorem stem_ext (S T : Stem) (hr : S.root = T.root)
    (hc : S.rootLabel = T.rootLabel) (hd : S.done = T.done) : S = T := by
  cases S
  cases T
  cases hr
  cases hc
  cases hd
  rfl

theorem completed_stem_eq (S T : Stem) (hS : S.done.length = S.root)
    (hT : T.done.length = T.root) (ho : S.ordinary = T.ordinary)
    (hr : S.rootLabel = T.rootLabel) (hb : S.bodyLabels = T.bodyLabels) : S = T := by
  have hw : word (S.toGood hS).1 = word (T.toGood hT).1 := by
    rw [Stem.toGood_word, Stem.toGood_word, ho]
  have hv : S.done.map Body.values = T.done.map Body.values :=
    WordResponses.word_prefix_rigid (hw ▸ List.prefix_rfl)
  have hd := StemResponses.bodies_eq_of_projections hv hb
  apply stem_ext S T
  · have he := congrArg List.length hd
    simpa only [hS, hT] using he
  · exact hr
  · exact hd

theorem completion_setup (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (hR : P.roots = []) :
    ∃ A : StemResponses.Setup P.position P.position.stem.root, A.stem = S := by
  have hp : P.position.ordinary <+: S.ordinary := by
    rw [hP.ordinary]
    exact List.takeWhile_prefix _
  obtain ⟨v, hv⟩ := hp
  have he := cutExtension_of_prefix P S hS hP.labels (by
    rw [hP.decorated]; exact List.takeWhile_prefix _)
  obtain ⟨A, _, ho⟩ := CompletionReplay.setup_of_literal_stem P.position S
    P.position.stem.root he.root (hS.trans he.root)
    (by have hr := P.position.room; omega) v hv.symm
  refine ⟨A, completed_stem_eq A.stem S (A.count.trans A.root_eq.symm) hS ho ?_ ?_⟩
  · exact A.rootLabel_eq.trans he.rootLabel.symm
  · rw [A.labels, completion_labels S T hS hexact P hP hslots hR, he.root]

theorem finish_step {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (hguard : FiniteGuards.Sparse H K payoff)
    (right : Bool) (T : State) (P : Pending) (hR : P.roots = []) (hL : P.leaves = [])
    (A : StemResponses.Setup P.position P.position.stem.root)
    (hside : allowedSide (PreparedRelays.pair right (.leaf P) T) right = true)
    (hTK : ∀ x ∈ T.decorated, x ∈ K) (hPK : ∀ x ∈ P.position.decorated, x ∈ K)
    (hAK : ∀ x ∈ A.newWord, x ∈ K) (b : ℕ) (hb : b ∈ K)
    (hbase : ∀ x ∈ A.newWord, b < x)
    (hbefore : ∀ y ∈ T.decorated, ∀ x ∈ A.newWord, y < x) :
    ConservativeRuns.Step H payoff (PreparedRelays.pair right (.leaf P) T)
      (PreparedRelays.pair right (.complete (ofCompletion P A)) T) := by
  let W := PreparedRelays.pair right (.leaf P) T
  have hwK : (∀ x ∈ W.1.decorated, x ∈ K) ∧ (∀ x ∈ W.2.decorated, x ∈ K) := by
    cases right <;> simp_all [W, PreparedRelays.pair, State.decorated]
  have hown : ∀ y ∈ P.position.decorated, ∀ x ∈ A.newWord, y < x :=
    (List.pairwise_append.mp (A.decorated ▸ A.stem.increasing)).2.2
  have hlarge : ∀ x ∈ A.newWord,
      pairBound W < x ∧ ConservativeRuns.leftGuard H payoff W 0 < x ∧
        ConservativeRuns.rightGuard H payoff W 0 < x := by
    intro x hx
    apply hguard W hwK.1 hwK.2 0 b hb (Nat.zero_le _) x (hAK x hx) (hbase x hx)
    · cases right <;> simp_all [W, PreparedRelays.pair, State.decorated]
    · cases right <;> simp_all [W, PreparedRelays.pair, State.decorated]
  have hc : ∀ x ∈ A.newWord, pairBound W < x := fun x hx ↦ (hlarge x hx).1
  let a := ReservedResponses.finishMember P hR hL (pairBound W) A hc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hKH (hAK x (List.mem_toFinset.mp hx))
  have ha : (finishResponse P hR hL (pairBound W)).result a =
      .complete (ofCompletion P A) := ReservedResponses.finishMember_result ..
  cases right with
  | false =>
    have hs := ConservativeRuns.Step.left W 0 (finishResponse P hR hL (pairBound W))
      hside (SecondWhole.finish_selector P hR hL _ 0) a haH
      (fun x hx ↦ (hlarge x (List.mem_toFinset.mp hx)).2.1)
    rw [ha] at hs
    exact hs
  | true =>
    have hs := ConservativeRuns.Step.right W 0 (finishResponse P hR hL (pairBound W))
      hside (SecondWhole.finish_selector P hR hL _ 0) a haH
      (fun x hx ↦ (hlarge x (List.mem_toFinset.mp hx)).2.2)
    rw [ha] at hs
    exact hs

end Erdos118.FinalCutRun
