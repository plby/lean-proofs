import ErdosProblems.Erdos118.NextBodyCuts

/-!
Conservative execution of a next-body response followed by its forced body
response. The command anchor is recovered from an actual projection. The
opposite-side freshness premise remains explicit for the global scheduler.
-/

namespace Erdos118.NextBodyRun

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open DecisionStates AdaptiveGame

theorem stem_step {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (hguard : FiniteGuards.Sparse H K payoff)
    (right : Bool) (T : State) (P : Pending) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hL : P.leaves = [])
    (A : StemResponses.Setup P.position (c - 1))
    (hside : allowedSide (PreparedRelays.pair right (.leaf P) T) right = true)
    (hTK : ∀ x ∈ T.decorated, x ∈ K) (hPK : ∀ x ∈ P.position.decorated, x ∈ K)
    (hAK : ∀ x ∈ A.newWord, x ∈ K) (b : ℕ) (hb : b ∈ K)
    (hbase : ∀ x ∈ A.newWord, b < x)
    (hbefore : ∀ y ∈ T.decorated, ∀ x ∈ A.newWord, y < x) :
    ConservativeRuns.Step H payoff (PreparedRelays.pair right (.leaf P) T)
      (PreparedRelays.pair right (.body (ofStem P c rest hR A)) T) := by
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
  let a := StemReplay.member P c rest hR hL (pairBound W) A hc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hKH (hAK x (List.mem_toFinset.mp hx))
  have ha : (nextBodyResponse P c rest hR hL (pairBound W)).result a =
      .body (ofStem P c rest hR A) := StemReplay.member_result ..
  cases right with
  | false =>
    have hs := ConservativeRuns.Step.left W 0 (nextBodyResponse P c rest hR hL (pairBound W))
      hside (StemReplay.selector P c rest hR hL _ 0) a haH
      (fun x hx ↦ (hlarge x (List.mem_toFinset.mp hx)).2.1)
    rw [ha] at hs
    exact hs
  | true =>
    have hs := ConservativeRuns.Step.right W 0 (nextBodyResponse P c rest hR hL (pairBound W))
      hside (StemReplay.selector P c rest hR hL _ 0) a haH
      (fun x hx ↦ (hlarge x (List.mem_toFinset.mp hx)).2.2)
    rw [ha] at hs
    exact hs

private theorem after_nonempty_prefix (C v : List ℕ) (hinc : (C ++ v).Pairwise (· < ·))
    (hne : C ≠ []) (q : ℕ) (hq : ∀ x ∈ C, q < x) : ∀ x ∈ C ++ v, q < x := by
  obtain ⟨c, C, rfl⟩ := List.exists_cons_of_ne_nil hne
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hq x hx
  · exact (hq c (List.mem_cons_self ..)).trans
      ((List.pairwise_append.mp hinc).2.2 c (List.mem_cons_self ..) x hx)

theorem projection_body_anchor {K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K)
    (b : ℕ) (hb : b ∈ K) (htail : ∀ x ∈ L, b < x)
    (s : G2) {U : Stem} {hU : U.done.length = U.root} {ys : List ℕ}
    (J : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full ys U hU)
    (F : Pending) {y : ℕ} (hF : JointCut F U hU y) :
    ∃ q ∈ K, F.position.label.length - 1 ≤ q ∧
      ∀ x ∈ BodyResponses.newWord F.position, q < x := by
  have hFL : ∀ x ∈ F.position.decorated, x ∈ L := by
    intro x hx
    apply LabelledRealization.output_supported hL s x
    apply J.decorated.subset
    apply (List.takeWhile_sublist (fun z ↦ decide (z < y))).subset
    change x ∈ PrefixRealization.below y U.decorated
    exact hF.decorated ▸ hx
  have hlabels : F.position.bodyLabels <+: U.bodyLabels := hF.labels.bodies
  have hiF : F.position.stem.done.length < F.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hiU := hiF.trans_le hlabels.length_le
  have he : U.bodyLabels[F.position.stem.done.length] = F.position.label := by
    rw [← hlabels.getElem hiF]
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hne : F.position.label ≠ [] := List.ne_nil_of_mem F.leafSelected
  have hneU : U.bodyLabels[F.position.stem.done.length] ≠ [] := he ▸ hne
  have hcommand := ProjectionBounds.projection_body_command hL s J
    F.position.stem.done.length hiU hneU
  rw [he] at hcommand
  rcases hcommand with hz | ⟨q, hq, hn, hlabel⟩
  · refine ⟨b, hb, ?_, ?_⟩
    · rw [hz]
      exact Nat.zero_le _
    · intro x hx
      exact htail x (hFL x (List.mem_append_right _ hx))
  · exact ⟨q, hLK hq, hn, after_nonempty_prefix _ _
      (BodyResponses.newWord_pairwise F.position) hne q hlabel⟩

theorem two_steps {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (hguard : FiniteGuards.Sparse H K (GraphPayoff.payoff B o))
    (b : ℕ) (hb : b ∈ K) (htail : ∀ x ∈ L, b < x)
    (s : G2) {U : Stem} {hU : U.done.length = U.root} {ys : List ℕ}
    (J : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full ys U hU)
    (right : Bool) (T : State) (P : Pending) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hLeaf : P.leaves = [])
    (A : StemResponses.Setup P.position (c - 1)) {n : ℕ} (Q : BodyResponses.Setup A.stem n)
    {y : ℕ} (hcut : JointCut (applyBody (ofStem P c rest hR A) Q) U hU y)
    (hside : allowedSide (PreparedRelays.pair right (.leaf P) T) right = true)
    (hTK : ∀ x ∈ T.decorated, x ∈ K)
    (hbefore : ∀ z ∈ T.decorated, ∀ x ∈ A.newWord ++ BodyResponses.newWord Q.position, z < x) :
    ConservativeRuns.Run H (GraphPayoff.payoff B o) (PreparedRelays.pair right (.leaf P) T)
      (PreparedRelays.pair right (.leaf (applyBody (ofStem P c rest hR A) Q)) T) := by
  let D := ofStem P c rest hR A
  let F := applyBody D Q
  have hFL : ∀ x ∈ Q.position.decorated, x ∈ L := by
    intro x hx
    apply LabelledRealization.output_supported hL s x
    apply J.decorated.subset
    apply (List.takeWhile_sublist (fun z ↦ decide (z < y))).subset
    change x ∈ PrefixRealization.below y U.decorated
    exact hcut.decorated ▸ hx
  have hAL : ∀ x ∈ A.stem.decorated, x ∈ L := by
    intro x hx
    apply hFL x
    rw [BodyResponses.setup_decorated Q]
    exact List.mem_append_left _ hx
  have hPL : ∀ x ∈ P.position.decorated, x ∈ L := by
    intro x hx
    apply hAL x
    rw [A.decorated]
    exact List.mem_append_left _ hx
  have hAwL : ∀ x ∈ A.newWord, x ∈ L := by
    intro x hx
    apply hAL x
    rw [A.decorated]
    exact List.mem_append_right _ hx
  have hQL : ∀ x ∈ BodyResponses.newWord Q.position, x ∈ L := by
    intro x hx
    apply hFL x
    rw [BodyResponses.setup_decorated Q]
    exact List.mem_append_right _ hx
  have hstem := stem_step hKH (GraphPayoff.payoff B o) hguard right T P c rest hR hLeaf A
    hside hTK (fun x hx ↦ hLK (hPL x hx)) (fun x hx ↦ hLK (hAwL x hx)) b hb
    (fun x hx ↦ htail x (hAwL x hx))
    (fun z hz x hx ↦ hbefore z hz x (List.mem_append_left _ hx))
  obtain ⟨q, hq, hnq, hqQ⟩ := projection_body_anchor hL hLK b hb htail s J F hcut
  have hn : n ≤ q := by
    have hlen := Q.label_length
    change Q.position.label.length - 1 ≤ q at hnq
    omega
  have hown : ∀ z ∈ A.stem.decorated, ∀ x ∈ BodyResponses.newWord Q.position, z < x :=
    (List.pairwise_append.mp ((BodyResponses.setup_decorated Q) ▸ Q.position.increasing)).2.2
  let W := PreparedRelays.pair right (.body D) T
  have hWK : (∀ x ∈ W.1.decorated, x ∈ K) ∧ (∀ x ∈ W.2.decorated, x ∈ K) := by
    have hAK : ∀ x ∈ A.stem.decorated, x ∈ K := fun x hx ↦ hLK (hAL x hx)
    cases right <;> simp_all [W, D, PreparedRelays.pair, State.decorated, ofStem]
  have hlarge : ∀ x ∈ BodyResponses.newWord Q.position,
      pairBound W < x ∧ ConservativeRuns.leftGuard H (GraphPayoff.payoff B o) W n < x ∧
        ConservativeRuns.rightGuard H (GraphPayoff.payoff B o) W n < x := by
    intro x hx
    apply hguard W hWK.1 hWK.2 n q hq hn x (hLK (hQL x hx)) (hqQ x hx)
    · cases right <;> simp_all [W, D, PreparedRelays.pair, State.decorated, ofStem]
    · cases right <;> simp_all [W, D, PreparedRelays.pair, State.decorated, ofStem]
  have hallowed : allowedSide W right = true := by
    cases right <;> cases T <;> simp_all [W, PreparedRelays.pair, allowedSide]
  have hg : ∀ x ∈ BodyResponses.newWord Q.position,
      PreparedRelays.guard H B o right D T n < x := by
    intro x hx
    cases right with
    | false => exact (hlarge x hx).2.1
    | true => exact (hlarge x hx).2.2
  have hbody := PreparedRelays.body_step B o right D T Q hallowed
    (fun x hx ↦ hKH (hLK (hQL x hx))) (fun x hx ↦ (hlarge x hx).1) hg
  exact (Relation.ReflTransGen.single hstem).tail hbody

end Erdos118.NextBodyRun
