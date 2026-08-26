import ErdosProblems.Erdos118.TerminalFrontiers

/-!
Actual advances at a pending frontier, with all opposite-state coordinate
bounds derived from its ordinary equations and clear-pair geometry.
-/

namespace Erdos118.FrontierSteps

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates AdaptiveGame ClearPairs
open PrefixRealization (below)
open PreparedRelays (pair)

theorem pair_swap (right : Bool) (S T : State) : pair (!right) T S = pair right S T := by
  cases right <;> rfl

theorem split_joint (S : Completed) (P : Pending) {t : ℕ}
    (hP : JointCut P S.stem S.full t) :
    ∃ z : ℕ, ∃ u : List ℕ, S.stem.ordinary = P.position.ordinary ++ z :: u := by
  have hp : P.position.ordinary <+: S.stem.ordinary := by
    rw [hP.ordinary]
    exact List.takeWhile_prefix _
  obtain ⟨v, hv⟩ := hp
  have hvne : v ≠ [] := by
    intro he
    have hlen := CutFrontiers.joint_cut_length hP
    rw [← hv, he, List.append_nil] at hlen
    omega
  obtain ⟨z, u, rfl⟩ := List.exists_cons_of_ne_nil hvne
  exact ⟨z, u, hv.symm⟩

theorem joint_supported {K : Set ℕ} (S : Completed)
    (hSK : ∀ x ∈ S.stem.decorated, x ∈ K) (P : Pending) {t : ℕ}
    (hP : JointCut P S.stem S.full t) : ∀ x ∈ P.position.decorated, x ∈ K := by
  intro x hx
  apply hSK x
  apply (List.takeWhile_sublist (fun a ↦ decide (a < t))).subset
  change x ∈ below t S.stem.decorated
  exact hP.decorated ▸ hx

theorem next_ne (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (P Q : Pending) (z w : ℕ) (u v : List ℕ)
    (hS : S.stem.ordinary = P.position.ordinary ++ z :: u)
    (hT : T.stem.ordinary = Q.position.ordinary ++ w :: v) : z ≠ w := by
  have hz : z ∈ S.stem.ordinary := by rw [hS]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hw : w ∈ T.stem.ordinary := by rw [hT]; exact List.mem_append_right _ (List.mem_cons_self ..)
  exact (foreign_ne hclear.disjoint hw (S.stem.ordinary_sublist.subset hz)).symm

theorem opposite_before (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (P Q : Pending) {t z : ℕ} (hP : JointCut P S.stem S.full t)
    (hQ : JointCut Q T.stem T.full z) (u : List ℕ)
    (hsplit : S.stem.ordinary = P.position.ordinary ++ z :: u)
    (e : List ℕ) (he : P.position.decorated ++ e <+: S.stem.decorated) :
    ∀ y ∈ Q.position.decorated, ∀ x ∈ e, y < x := by
  have hqPrefix : State.ordinary (.leaf Q) <+: T.stem.ordinary := by
    change Q.position.ordinary <+: T.stem.ordinary
    rw [hQ.ordinary]
    exact List.takeWhile_prefix _
  apply DecoratedFrontiers.response_after_state S.stem T.stem S.full hclear.separatedLeft
    P hP (.leaf Q) hqPrefix (z :: u) hsplit _ e he
  intro y hy x hx
  have hyz : y < z := by
    change y ∈ Q.position.ordinary at hy
    rw [hQ.ordinary] at hy
    exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun a ↦ decide (a < z)) hy)
  have hinc := (List.pairwise_append.mp
    (hsplit ▸ S.stem.increasing.sublist S.stem.ordinary_sublist)).2.1
  have hzx : z ≤ x := by
    simpa only [List.head_cons] using (hinc.imp Nat.le_of_lt).rel_head hx
  exact hyz.trans_le hzx

theorem advance_leaf {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (hguard : FiniteGuards.Sparse H K payoff)
    (right : Bool) (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hcuts : JointCuts S.stem S.full T.stem)
    (hSK : ∀ x ∈ S.stem.decorated, x ∈ K) (hTK : ∀ x ∈ T.stem.decorated, x ∈ K)
    (b : ℕ) (hb : b ∈ K) (hbase : ∀ x ∈ S.stem.decorated, b < x)
    (P Q : Pending) {t z : ℕ} (hP : JointCut P S.stem S.full t)
    (hQ : JointCut Q T.stem T.full z) (hExact : ExactSlots.Exact (.leaf P))
    (u v : List ℕ) (w : ℕ)
    (hsplit : S.stem.ordinary = P.position.ordinary ++ z :: u)
    (htsplit : T.stem.ordinary = Q.position.ordinary ++ w :: v)
    (j : ℕ) (rest : List ℕ) (hleaves : P.leaves = j :: rest) :
    ∃ F : Pending, ExactSlots.Exact (.leaf F) ∧ JointCut F S.stem S.full w ∧
      P.position.ordinary.length < F.position.ordinary.length ∧
      ConservativeRuns.Run H payoff (pair right (.leaf P) (.leaf Q))
        (pair right (.leaf F) (.leaf Q)) := by
  obtain ⟨y, hy, A, hF⟩ := NextLeafCuts.retained_leaf S.stem T.stem S.full
    hclear.exactLeft hcuts P hP j rest hleaves
  let F := LeafResponses.toPending P j rest hleaves A
  have hslot := P.leafSlots.bounded j (hleaves ▸ List.mem_cons_self ..)
  have ho : F.position.ordinary = P.position.ordinary ++ A.newWord :=
    LeafResponses.position_ordinary A hslot.1 hslot.2.1
  have hd : F.position.decorated = P.position.decorated ++ A.newWord :=
    LeafResponses.position_decorated A hslot.1 hslot.2.1
  have hlong : P.position.ordinary.length < F.position.ordinary.length := by
    rw [ho, List.length_append]
    have hpos := List.length_pos_iff.mpr (LeafResponses.newWord_ne_nil A hslot.1)
    omega
  have hFP : F.position.decorated <+: S.stem.decorated := by
    rw [hF.decorated]
    exact List.takeWhile_prefix _
  have hAP : P.position.decorated ++ A.newWord <+: S.stem.decorated := by rwa [hd] at hFP
  have hAS : ∀ x ∈ A.newWord, x ∈ S.stem.decorated :=
    fun x hx ↦ hAP.subset (List.mem_append_right _ hx)
  have hbefore := opposite_before S T hclear P Q hP hQ u hsplit A.newWord hAP
  have hallowed : allowedSide (pair right (.leaf P) (.leaf Q)) right = true := by
    cases right <;> rfl
  have hs := NextLeafCuts.leaf_step hKH payoff hguard right (.leaf Q) P j rest hleaves A
    hallowed (joint_supported T hTK Q hQ) (joint_supported S hSK P hP)
    (fun x hx ↦ hSK x (hAS x hx)) b hb (fun x hx ↦ hbase x (hAS x hx)) hbefore
  have hjF : F.position.entries.length = j := LeafResponses.position_length A hslot.1 hslot.2.1
  have hnext := CutSuccessors.leaf_successor S.stem T.stem S.full hclear.exactLeft
    P F hP hF hExact j rest hleaves rfl hjF
  have hboundary := CutFrontiers.successor_eq_frontier S.stem T.stem S.full
    hclear.interiorLeft P F hy hF hlong hnext Q.position.ordinary u v z w hsplit htsplit
    hQ.ordinary.symm (next_ne S T hclear P Q z w u v hsplit htsplit)
  have hw : w ∈ T.stem.ordinary := by
    rw [htsplit]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hFw := DecoratedFrontiers.joint_cut_retarget S.stem T.stem S.full
    hclear.separatedLeft hclear.disjoint F hF w hw hboundary
  exact ⟨F, ExactSlots.step_exact (DecisionStates.Step.leaf P j rest hleaves A) hExact,
    hFw, hlong, Relation.ReflTransGen.single hs⟩

theorem advance_body {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (hguard : FiniteGuards.Sparse H K (GraphPayoff.payoff B o))
    (b : ℕ) (hb : b ∈ K) (htail : ∀ x ∈ L, b < x)
    (s : G2) (S T : Completed) {ys : List ℕ}
    (J : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full ys S.stem S.full)
    (hclear : ClearPair S.stem T.stem) (hcuts : JointCuts S.stem S.full T.stem)
    (hTK : ∀ x ∈ T.stem.decorated, x ∈ K) (right : Bool)
    (P Q : Pending) {t z : ℕ} (hP : JointCut P S.stem S.full t)
    (hQ : JointCut Q T.stem T.full z) (hExact : ExactSlots.Exact (.leaf P))
    (u v : List ℕ) (w : ℕ)
    (hsplit : S.stem.ordinary = P.position.ordinary ++ z :: u)
    (htsplit : T.stem.ordinary = Q.position.ordinary ++ w :: v)
    (c : ℕ) (rest : List ℕ) (hroots : P.roots = c :: rest) (hleaves : P.leaves = []) :
    ∃ F : Pending, ExactSlots.Exact (.leaf F) ∧ JointCut F S.stem S.full w ∧
      P.position.ordinary.length < F.position.ordinary.length ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B o) (pair right (.leaf P) (.leaf Q))
        (pair right (.leaf F) (.leaf Q)) := by
  obtain ⟨y, hy, A, n, C, hF, heF⟩ := NextBodyCuts.retained_body S.stem T.stem S.full
    hclear.exactLeft hcuts P hP hExact c rest hroots hleaves
  let F := applyBody (ofStem P c rest hroots A) C
  have ho : F.position.ordinary = P.position.ordinary ++
      (A.newWord ++ C.position.size :: C.position.entries) := by
    change C.position.ordinary = _
    rw [BodyResponses.setup_ordinary C, A.ordinary, List.append_assoc]
  have hd : F.position.decorated = P.position.decorated ++
      (A.newWord ++ BodyResponses.newWord C.position) := by
    change C.position.decorated = _
    rw [BodyResponses.setup_decorated C, A.decorated, List.append_assoc]
  have hlong : P.position.ordinary.length < F.position.ordinary.length := by
    rw [ho, List.length_append, List.length_append, List.length_cons]
    omega
  have hFP : F.position.decorated <+: S.stem.decorated := by
    rw [hF.decorated]
    exact List.takeWhile_prefix _
  have hAP : P.position.decorated ++ (A.newWord ++ BodyResponses.newWord C.position) <+:
      S.stem.decorated := by rwa [hd] at hFP
  have hbefore := opposite_before S T hclear P Q hP hQ u hsplit
    (A.newWord ++ BodyResponses.newWord C.position) hAP
  have hallowed : allowedSide (pair right (.leaf P) (.leaf Q)) right = true := by
    cases right <;> rfl
  have hs := NextBodyRun.two_steps hL hLK hKH B o hguard b hb htail s J right
    (.leaf Q) P c rest hroots hleaves A C hF hallowed (joint_supported T hTK Q hQ) hbefore
  have hiF : F.position.stem.done.length = c - 1 := by
    change C.position.stem.done.length = _
    rw [C.stem_eq, A.count]
  have hhead : F.position.entries.length = F.position.label.headD 0 := C.entries_length
  have hnext := CutSuccessors.body_successor S.stem T.stem S.full hclear.exactLeft
    P F hP hF hExact c rest hroots hleaves hiF hhead
  have hboundary := CutFrontiers.successor_eq_frontier S.stem T.stem S.full
    hclear.interiorLeft P F hy hF hlong hnext Q.position.ordinary u v z w hsplit htsplit
    hQ.ordinary.symm (next_ne S T hclear P Q z w u v hsplit htsplit)
  have hw : w ∈ T.stem.ordinary := by
    rw [htsplit]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hFw := DecoratedFrontiers.joint_cut_retarget S.stem T.stem S.full
    hclear.separatedLeft hclear.disjoint F hF w hw hboundary
  exact ⟨F, heF, hFw, hlong, hs⟩

private theorem completed_ext (S T : Completed) (h : S.stem = T.stem) : S = T := by
  cases S
  cases T
  cases h
  rfl

theorem finish {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (hguard : FiniteGuards.Sparse H K payoff)
    (right : Bool) (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hSK : ∀ x ∈ S.stem.decorated, x ∈ K) (hTK : ∀ x ∈ T.stem.decorated, x ∈ K)
    (b : ℕ) (hb : b ∈ K) (hbaseS : ∀ x ∈ S.stem.decorated, b < x)
    (hbaseT : ∀ x ∈ T.stem.decorated, b < x)
    (P Q : Pending) {t z : ℕ} (hP : JointCut P S.stem S.full t)
    (hQ : JointCut Q T.stem T.full z)
    (heP : ExactSlots.Exact (.leaf P)) (heQ : ExactSlots.Exact (.leaf Q))
    (u v : List ℕ) (w : ℕ)
    (hsplit : S.stem.ordinary = P.position.ordinary ++ z :: u)
    (htsplit : T.stem.ordinary = Q.position.ordinary ++ w :: v)
    (hroots : P.roots = []) (hleaves : P.leaves = []) :
    ConservativeRuns.Run H payoff (pair right (.leaf P) (.leaf Q))
      (pair right (.complete S) (.complete T)) := by
  have hbefore := TerminalFrontiers.last_before_next S.stem T.stem S.full hclear P hP
    heP hroots hleaves Q.position.ordinary u v z w hsplit htsplit hQ.ordinary.symm
    (next_ne S T hclear P Q z w u v hsplit htsplit)
  obtain ⟨A, hA⟩ := FinalCutRun.completion_setup S.stem T.stem S.full hclear.exactLeft
    P hP heP hroots
  have hAP : P.position.decorated ++ A.newWord <+: S.stem.decorated := by
    rw [← A.decorated, hA]
  have hAS : ∀ x ∈ A.newWord, x ∈ S.stem.decorated :=
    fun x hx ↦ hAP.subset (List.mem_append_right _ hx)
  have hdecBefore := opposite_before S T hclear P Q hP hQ u hsplit A.newWord hAP
  have hallowed : allowedSide (pair right (.leaf P) (.leaf Q)) right = true := by
    cases right <;> rfl
  have hfirst := FinalCutRun.finish_step hKH payoff hguard right (.leaf Q) P hroots hleaves A
    hallowed (joint_supported T hTK Q hQ) (joint_supported S hSK P hP)
    (fun x hx ↦ hSK x (hAS x hx)) b hb (fun x hx ↦ hbaseS x (hAS x hx)) hdecBefore
  have he : ofCompletion P A = S := completed_ext _ _ hA
  rw [he] at hfirst
  have hsecond := TerminalFrontiers.finish_after_complete hKH payoff hguard (!right) T S
    hclear.symm Q hQ heQ w v htsplit hbefore hTK hSK b hb hbaseT
  rw [pair_swap, pair_swap] at hsecond
  exact (Relation.ReflTransGen.single hfirst).tail hsecond

end Erdos118.FrontierSteps
