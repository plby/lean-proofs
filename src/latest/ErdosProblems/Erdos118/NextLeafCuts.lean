import ErdosProblems.Erdos118.InitialSplit
import ErdosProblems.Erdos118.LeafReplay

/-!
Decode a retained next leaf into the literal response ending at a joint cut.
This is local decoding; scheduling its suffix above the opposite state is a
separate requirement, not inferred merely from the existence of the cut.
-/

namespace Erdos118.NextLeafCuts

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates AdaptiveGame

private theorem stem_ext (S T : Stem) (hr : S.root = T.root)
    (hc : S.rootLabel = T.rootLabel) (hd : S.done = T.done) : S = T := by
  cases S
  cases T
  cases hr
  cases hc
  cases hd
  rfl

private theorem position_ext (P Q : Position) (hs : P.stem = Q.stem)
    (hn : P.size = Q.size) (hd : P.label = Q.label) (he : P.entries = Q.entries) : P = Q := by
  cases P
  cases Q
  cases hs
  cases hn
  cases hd
  cases he
  rfl

theorem same_body {P Q : Pending} {S : Stem} {hS : S.done.length = S.root} {y z : ℕ}
    (hP : JointCut P S hS y) (hQ : JointCut Q S hS z)
    (hi : P.position.stem.done.length = Q.position.stem.done.length)
    (hj : P.position.entries.length ≤ Q.position.entries.length) :
    Q.position.stem = P.position.stem ∧ Q.position.size = P.position.size ∧
      Q.position.label = P.position.label ∧ P.position.entries <+: Q.position.entries := by
  have hpe := cutExtension_of_prefix P S hS hP.labels (by
    rw [hP.decorated]; exact List.takeWhile_prefix _)
  have hqe := cutExtension_of_prefix Q S hS hQ.labels (by
    rw [hQ.decorated]; exact List.takeWhile_prefix _)
  obtain ⟨a, as, hpd, hpa, hpn, hpu⟩ := hpe.bodies
  obtain ⟨c, cs, hqd, hqa, hqn, hqu⟩ := hqe.bodies
  obtain ⟨hd, htail⟩ := List.append_inj (hpd.symm.trans hqd) hi
  have hac : a = c := (List.cons.inj htail).1
  subst c
  refine ⟨?_, hqn.symm.trans hpn, hqa.symm.trans hpa, ?_⟩
  · exact stem_ext _ _ (hqe.root.symm.trans hpe.root)
      (hqe.rootLabel.symm.trans hpe.rootLabel) hd.symm
  · exact List.prefix_of_prefix_length_le hpu hqu hj

theorem setup_of_same_body (P Q : Pending) (j : ℕ) (rest : List ℕ)
    (hnext : P.leaves = j :: rest)
    (hstem : Q.position.stem = P.position.stem) (hsize : Q.position.size = P.position.size)
    (hlabel : Q.position.label = P.position.label) (hlen : Q.position.entries.length = j)
    (hprefix : P.position.entries <+: Q.position.entries) :
    ∃ A : LeafResponses.Setup P.position j,
      (LeafResponses.toPending P j rest hnext A).position = Q.position := by
  obtain ⟨v, hv⟩ := hprefix
  have hlenv : v.length = j - P.position.entries.length := by
    have he := congrArg List.length hv
    simp only [List.length_append, hlen] at he
    omega
  have hdecor : Q.position.decorated = P.position.decorated ++ v := by
    simp only [Position.decorated, hstem, hsize, hlabel, ← hv,
      List.cons_append, List.append_assoc]
  let A : LeafResponses.Setup P.position j :=
    { newWord := v, length_eq := hlenv, increasing := hdecor ▸ Q.position.increasing }
  refine ⟨A, ?_⟩
  apply position_ext
  · exact hstem.symm
  · exact hsize.symm
  · exact hlabel.symm
  · exact hv

theorem retained_leaf (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T)
    (hcuts : ∀ y ∈ T.ordinary, ProperBelow y S → ∃ Q : Pending, JointCut Q S hS y)
    (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (j : ℕ) (rest : List ℕ) (hnext : P.leaves = j :: rest) :
    ∃ y ∈ T.ordinary, ∃ A : LeafResponses.Setup P.position j,
      JointCut (LeafResponses.toPending P j rest hnext A) S hS y := by
  have hslot := P.leafSlots.bounded j (hnext ▸ List.mem_cons_self ..)
  have hlabels : P.position.bodyLabels <+: S.bodyLabels := hP.labels.bodies
  have hiP : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hiS := hiP.trans_le hlabels.length_le
  have hjS : j ∈ S.bodyLabels[P.position.stem.done.length] := by
    rw [← hlabels.getElem hiP]
    simpa [Position.bodyLabels, Stem.bodyLabels] using hslot.2.2
  have hc := (hexact.body P.position.stem.done.length hiS j).mp hjS
  obtain ⟨y, hy, hp, I, hI, hi, hj⟩ := hc
  obtain ⟨Q, hQ⟩ := hcuts y hy hp
  have hindex := jointCut_indices hQ hI
  have hiQ : P.position.stem.done.length = Q.position.stem.done.length := hi.symm.trans hindex.1
  have hjQ : Q.position.entries.length = j := hindex.2.symm.trans hj
  have hlen : P.position.entries.length ≤ Q.position.entries.length := by
    rw [hjQ]
    exact hslot.1.le
  obtain ⟨hstem, hsize, hlabel, hprefix⟩ := same_body hP hQ hiQ hlen
  obtain ⟨A, hA⟩ := setup_of_same_body P Q j rest hnext hstem hsize hlabel hjQ hprefix
  exact ⟨y, hy, A, InitialSplit.jointCut_of_position_eq hA hQ⟩

theorem next_leaf_minimal (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (j : ℕ) (rest : List ℕ)
    (hnext : P.leaves = j :: rest) (k : ℕ)
    (hcut : Cut S T P.position.stem.done.length k)
    (hafter : P.position.entries.length < k) : j ≤ k := by
  have hlabels : P.position.bodyLabels <+: S.bodyLabels := hP.labels.bodies
  have hiP : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hiS := hiP.trans_le hlabels.length_le
  have hkS := (hexact.body P.position.stem.done.length hiS k).mpr hcut
  have hkP : k ∈ P.position.label := by
    rw [← hlabels.getElem hiP] at hkS
    simpa [Position.bodyLabels, Stem.bodyLabels] using hkS
  have hm : k ∈ ExactSlots.above P.position.label P.position.entries.length :=
    List.mem_filter.mpr ⟨hkP, decide_eq_true hafter⟩
  rw [← hslots.2, hnext] at hm
  have hinc : (j :: rest).Pairwise (· < ·) := hnext ▸ P.leafSlots.increasing
  simpa only [List.head_cons] using (hinc.imp Nat.le_of_lt).rel_head hm

theorem leaf_step {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (hguard : FiniteGuards.Sparse H K payoff)
    (right : Bool) (T : State) (P : Pending) (j : ℕ) (rest : List ℕ)
    (hnext : P.leaves = j :: rest) (A : LeafResponses.Setup P.position j)
    (hside : allowedSide (PreparedRelays.pair right (.leaf P) T) right = true)
    (hTK : ∀ x ∈ T.decorated, x ∈ K) (hPK : ∀ x ∈ P.position.decorated, x ∈ K)
    (hAK : ∀ x ∈ A.newWord, x ∈ K) (b : ℕ) (hb : b ∈ K)
    (hbase : ∀ x ∈ A.newWord, b < x)
    (hbefore : ∀ y ∈ T.decorated, ∀ x ∈ A.newWord, y < x) :
    ConservativeRuns.Step H payoff (PreparedRelays.pair right (.leaf P) T)
      (PreparedRelays.pair right (.leaf (LeafResponses.toPending P j rest hnext A)) T) := by
  let W := PreparedRelays.pair right (.leaf P) T
  have hwK : (∀ x ∈ W.1.decorated, x ∈ K) ∧ (∀ x ∈ W.2.decorated, x ∈ K) := by
    cases right <;> simp_all [W, PreparedRelays.pair, State.decorated]
  have hown : ∀ y ∈ P.position.decorated, ∀ x ∈ A.newWord, y < x :=
    (List.pairwise_append.mp A.increasing).2.2
  have hlarge : ∀ x ∈ A.newWord,
      pairBound W < x ∧ ConservativeRuns.leftGuard H payoff W 0 < x ∧
        ConservativeRuns.rightGuard H payoff W 0 < x := by
    intro x hx
    apply hguard W hwK.1 hwK.2 0 b hb (Nat.zero_le _) x (hAK x hx) (hbase x hx)
    · cases right <;> simp_all [W, PreparedRelays.pair, State.decorated]
    · cases right <;> simp_all [W, PreparedRelays.pair, State.decorated]
  have hc : ∀ x ∈ A.newWord, pairBound W < x := fun x hx ↦ (hlarge x hx).1
  let a := LeafReplay.member P j rest hnext (pairBound W) A hc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hKH (hAK x (List.mem_toFinset.mp hx))
  have ha : (leafResponse P j rest hnext (pairBound W)).result a =
      .leaf (LeafResponses.toPending P j rest hnext A) := LeafReplay.member_result ..
  cases right with
  | false =>
    have hs := ConservativeRuns.Step.left W 0 (leafResponse P j rest hnext (pairBound W))
      hside (LeafReplay.selector P j rest hnext _ 0) a haH
      (fun x hx ↦ (hlarge x (List.mem_toFinset.mp hx)).2.1)
    rw [ha] at hs
    exact hs
  | true =>
    have hs := ConservativeRuns.Step.right W 0 (leafResponse P j rest hnext (pairBound W))
      hside (LeafReplay.selector P j rest hnext _ 0) a haH
      (fun x hx ↦ (hlarge x (List.mem_toFinset.mp hx)).2.2)
    rw [ha] at hs
    exact hs

end Erdos118.NextLeafCuts
