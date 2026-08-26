import ErdosProblems.Erdos118.CoupledRelays
import ErdosProblems.Erdos118.OutsideEndgame
import ErdosProblems.Erdos118.RightRelays

/-!
The outside blue-to-triangle argument. Both old last leaves are relayed to
fresh games, the common third word is relayed on the right, and all three
edges are obtained by exact ordinary completion replay. The inside game
and full-order conservative realization are not asserted here.
-/

namespace Erdos118.OutsideTriangle

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses

theorem triangle_of_forks {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .outside (.initial, .initial)) true)
    (F : CoupledRelays.ForkedPair H B .outside) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  let payoff := GraphPayoff.payoff B .outside
  have hfirst := OutsideEndgame.last_right_leftBlue hH B F.left F.right
    F.rightLast.1 F.rightLast.2 F.blue
  obtain ⟨bS, hbS⟩ := CompletionReplay.left_finish_words payoff F.left (.leaf F.right)
    F.leftLast.1 F.leftLast.2 hfirst
  obtain ⟨l, bT, hbT⟩ := BlueReservations.second_root_setups hH B hB .outside hinit
    F.rightRelay F.rightHandoff
  let L := max bS bT
  let K := H \ Set.Iic L
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic L)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  have hKbS : ∀ x ∈ K, bS < x :=
    fun x hx ↦ (le_max_left _ _).trans_lt (Nat.lt_of_not_ge hx.2)
  have hKbT : ∀ x ∈ K, bT < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (Nat.lt_of_not_ge hx.2)
  obtain ⟨k, A, C, hA, hC, hstart⟩ := BlueReservations.second_root_reserved hH B hB .outside
    hinit F.leftRelay F.leftHandoff l L
  have hAbT : ∀ x ∈ A.stem.decorated, x ∈ H ∧ bT < x :=
    fun x hx ↦ ⟨(hA x hx).1, (le_max_right _ _).trans_lt (hA x hx).2⟩
  have hCbT : ∀ x ∈ C.label, x ∈ H ∧ bT < x :=
    fun x hx ↦ ⟨(hC x hx).1, (le_max_right _ _).trans_lt (hC x hx).2⟩
  obtain ⟨U, V, U', hUR, hUL, hrun, _, hleft, hUord, hTU⟩ :=
    RightRelays.root_to_last hK hKH bT hKbT B .outside F.leftRelay F.rightRelay
      hbT A hAbT C hCbT hstart
  have hV : V ≠ .initial := by
    intro he
    have hprefix := (SkippedCuts.run_extensions hrun).1.ordinary
    have hm : F.leftRelay.position.stem.root ∈ F.leftRelay.position.ordinary :=
      List.mem_append_left _ (List.mem_cons_self ..)
    have hmem := hprefix.subset hm
    simp only [he, State.ordinary, List.not_mem_nil] at hmem
  obtain ⟨S, rfl, hSR, hSL⟩ :=
    OutsideEndgame.last_right_left_command hH B V U hUR hUL hV hleft
  obtain ⟨v, w, hv, _, hvK, _⟩ := CompletionReplay.run_supported_suffixes hrun
  change S.position.ordinary = F.leftRelay.position.ordinary ++ v at hv
  rw [F.leftOrdinary] at hv
  obtain ⟨bF, hbF⟩ := CompletionReplay.left_finish_words payoff S (.leaf U) hSR hSL hleft
  have hroom : S.position.stem.done.length < S.position.stem.root := by
    have h := S.position.room
    omega
  obtain ⟨A', hA'⟩ := StemResponses.setup_above S.position S.position.stem.root hroom le_rfl
    hH (max bS bF)
  let s := GraphPayoff.vertex (ofCompletion S A')
  have hs : word s.1 = S.position.ordinary ++ A'.newWord := by
    change word ((ofCompletion S A').stem.toGood (ofCompletion S A').full).1 = _
    rw [Stem.toGood_word]
    exact A'.ordinary
  have hA'H : ∀ x ∈ A'.newWord, x ∈ H := fun x hx ↦ (hA' x hx).1
  have hA'bS : ∀ x ∈ A'.newWord, bS < x :=
    fun x hx ↦ (le_max_left _ _).trans_lt (hA' x hx).2
  have hA'bF : ∀ x ∈ A'.newWord, bF < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hA' x hx).2
  obtain ⟨CSU, hCSU, hblueSU⟩ := hbF s A'.newWord hs hA'H hA'bF
  have hsOld : word s.1 = F.left.position.ordinary ++ (v ++ A'.newWord) := by
    rw [hs, hv, List.append_assoc]
  have hvH : ∀ x ∈ v ++ A'.newWord, x ∈ H := by
    intro x hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ hKH (hvK x hx)) (hA'H x)
  have hvbS : ∀ x ∈ v ++ A'.newWord, bS < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ hKbS x (hvK x hx)) (hA'bS x)
  obtain ⟨CST, hCST, hblueST⟩ := hbS s (v ++ A'.newWord) hsOld hvH hvbS
  obtain ⟨cT, hcT⟩ := CompletionReplay.right_completion_edges_of_word hH B .outside
    CST F.right hblueST
  obtain ⟨cU, hcU⟩ := CompletionReplay.right_completion_edges_of_word hH B .outside
    CSU U hblueSU
  let J := H \ Set.Iic (max cT cU)
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic (max cT cU))
  have hJH : J ⊆ H := fun _ hx ↦ hx.1
  have hblueJ := hTU.almost_mono (RamseyGame.almostSubset_of_subset hJH)
  obtain ⟨Tfinal, Ufinal, hfinal, hpay⟩ := blue_completion hJ payoff
    (.leaf F.rightRelay, .leaf U') hblueJ
  obtain ⟨vT, vU, hTword, hUword, hvT, hvU⟩ := CompletionReplay.run_supported_suffixes hfinal
  have ht : word (GraphPayoff.vertex Tfinal).1 = F.right.position.ordinary ++ vT := by
    rw [GraphPayoff.vertex, Stem.toGood_word]
    change Tfinal.stem.ordinary = F.rightRelay.position.ordinary ++ vT at hTword
    rwa [F.rightOrdinary] at hTword
  have hu : word (GraphPayoff.vertex Ufinal).1 = U.position.ordinary ++ vU := by
    rw [GraphPayoff.vertex, Stem.toGood_word]
    change Ufinal.stem.ordinary = U'.position.ordinary ++ vU at hUword
    rwa [hUord] at hUword
  have hst := hcT (GraphPayoff.vertex Tfinal) vT ht (fun x hx ↦ hJH (hvT x hx))
    (fun x hx ↦ (le_max_left _ _).trans_lt (Nat.lt_of_not_ge (hvT x hx).2))
  have hsu := hcU (GraphPayoff.vertex Ufinal) vU hu (fun x hx ↦ hJH (hvU x hx))
    (fun x hx ↦ (le_max_right _ _).trans_lt (Nat.lt_of_not_ge (hvU x hx).2))
  rw [hCST] at hst
  rw [hCSU] at hsu
  exact ⟨s, GraphPayoff.vertex Tfinal, GraphPayoff.vertex Ufinal, hst, hsu,
    ((GraphPayoff.payoff_true_iff B .outside Tfinal Ufinal).mp hpay).2.2.2⟩

theorem initial_not_blue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B .outside (.initial, .initial)) true := by
  intro hblue
  obtain ⟨F⟩ := CoupledRelays.initial_forks hH B hB .outside hblue
  obtain ⟨s, t, u, hst, hsu, htu⟩ := triangle_of_forks hH B hB hblue F
  exact hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)

theorem red_outcome (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧
      RamseyGame.Outcome H (GraphPayoff.game B .outside (.initial, .initial)) false := by
  obtain ⟨H, hHN, hH, value, hval⟩ :=
    RamseyGame.dichotomy (GraphPayoff.game B .outside (.initial, .initial)) N hN
  cases value with
  | false => exact ⟨H, hHN, hH, hval⟩
  | true => exact (initial_not_blue hH B hB hval).elim

end Erdos118.OutsideTriangle
