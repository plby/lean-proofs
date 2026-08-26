import ErdosProblems.Erdos118.SharedLast
import ErdosProblems.Erdos118.InitialRelays
import ErdosProblems.Erdos118.InsideCompletion

/-!
The inside construction with one selected root body. A shared-last body
label begins a new play inside the original last selected-leaf response.
The old bound is fixed before all coordinates in that buffered suffix.
-/

namespace Erdos118.InsideSingleton

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays

theorem triangle_of_reserve {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (P T T₁ : Pending) (hPR : P.roots = []) (hP : ExactSlots.Exact (.leaf P))
    (hT : T.roots = [] ∧ T.leaves = [])
    (hleft : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf T))
    (hentries : ∀ x ∈ P.position.entries, x ∈ H)
    (E : BodyDecision) (hE : ExactSlots.Exact (.body E)) (hER : E.roots = [])
    (hEstem : E.stem = P.position.stem) (k b : ℕ)
    (Z : SharedLast.Reserve H b k P.position)
    (hbound : pairBound (.body E, .initial) ≤ b)
    (hbody : ∀ A : BodyResponses.Setup E.stem k,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf (applyBody E A), .initial)) true)
    (hTord : T₁.position.ordinary = T.position.ordinary)
    (hTright : RightBlue H (GraphPayoff.payoff B .inside) (.leaf T₁, .initial)) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  let payoff := GraphPayoff.payoff B .inside
  obtain ⟨j, hPL⟩ := InsideEndgame.penultimate_left hH B P T hPR hT.1 hT.2 hleft
  have hj := ExactSlots.pending_next_last P hP hPL
  obtain ⟨bS, hbS⟩ := LeafReplay.left_leaf_words_slots payoff P (.leaf T) j [] hPL hleft
  obtain ⟨A, v₀, hAord, hAentries, hAsize, hAlabel, hv₀, hAfresh⟩ :=
    Z.buffer hH P hP hPL hentries bS
  let A' : BodyResponses.Setup E.stem k :=
    { position := A.position, stem_eq := A.stem_eq.trans hEstem.symm
      label_length := A.label_length, entries_length := A.entries_length }
  let S₁ := applyBody E A'
  have hS₁R : S₁.roots = [] := hER
  have hS₁exact : ExactSlots.Exact (.leaf S₁) :=
    ExactSlots.step_exact (DecisionStates.Step.body E A') hE
  have hblueS₁ := hbody A' (fun x hx ↦ (hAfresh x hx).1) (fun x hx ↦ (hAfresh x hx).2)
  let c := pairBound (.body E, .initial)
  have hAc : ∀ x ∈ BodyResponses.newWord A'.position, c < x :=
    fun x hx ↦ hbound.trans_lt (hAfresh x hx).2
  have hS₁hand : RightBlue H payoff (.leaf S₁, .initial) :=
    handoff_after_left hH B .inside (.body E, .initial) (bodyResponse E k c)
      (bodyMember E c A' hAc) S₁ (bodyMember_result E c A' hAc) hblueS₁
  obtain ⟨l, bU, hbU⟩ := BlueReservations.second_root_setups hH B hB .inside hinit T₁ hTright
  let L := max bS bU
  let K := H \ Set.Iic L
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic L)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  have hKbS : ∀ x ∈ K, bS < x :=
    fun x hx ↦ (le_max_left _ _).trans_lt (Nat.lt_of_not_ge hx.2)
  have hKbU : ∀ x ∈ K, bU < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (Nat.lt_of_not_ge hx.2)
  obtain ⟨m, Aᵤ, Cᵤ, hAᵤ, hCᵤ, hstart⟩ := BlueReservations.second_root_reserved hH B hB
    .inside hinit S₁ hS₁hand l L
  obtain ⟨U, V, U₁, hUR, hUL, hrun, hblueV, hleftV, hUord, hTU⟩ :=
    RightRelays.root_to_last hK hKH bU hKbU B .inside S₁ T₁ hbU Aᵤ
      (fun x hx ↦ ⟨(hAᵤ x hx).1, (le_max_right _ _).trans_lt (hAᵤ x hx).2⟩)
      Cᵤ (fun x hx ↦ ⟨(hCᵤ x hx).1, (le_max_right _ _).trans_lt (hCᵤ x hx).2⟩) hstart
  rcases run_last_body_left_cases S₁ (.body (ofRoot Aᵤ)) V (.leaf U) hS₁R hrun with
    ⟨S₂, hS₂, hsame₂⟩ | ⟨C, hC⟩
  · subst V
    obtain ⟨Q, hQR, hQL, hs, hblueQ, _⟩ :=
      InsideEndgame.advance_last_left hK hKH B S₂ U hsame₂.1 hUR hUL hleftV
    have hwhole := hrun.tail hs
    have hQexact := ExactSlots.run_exact_left hwhole hS₁exact
    have hsame := run_last_body_left S₁ Q (.body (ofRoot Aᵤ)) (.leaf U) hS₁R hwhole
    have hQstem : Q.position.stem = P.position.stem := hsame.2.1.trans A.stem_eq
    have hQsize : Q.position.size = P.position.size := hsame.2.2.1.trans hAsize
    have hQlabel : Q.position.label = Z.label := hsame.2.2.2.1.trans hAlabel
    have hQlen : Q.position.entries.length = j := by
      have hlast := ExactSlots.pending_last_leaf Q hQexact hQL
      rw [hQlabel, Z.sameLast, hj] at hlast
      exact hlast.symm
    obtain ⟨v₁, w, hv₁word, _, hv₁K, _⟩ := CompletionReplay.run_supported_suffixes hwhole
    change Q.position.ordinary = S₁.position.ordinary ++ v₁ at hv₁word
    have hQord : Q.position.ordinary = P.position.ordinary ++ (v₀ ++ v₁) := by
      rw [hv₁word]
      change A.position.ordinary ++ v₁ = _
      rw [hAord, List.append_assoc]
    have hQentries : Q.position.entries = P.position.entries ++ (v₀ ++ v₁) := by
      have he : P.position.size :: Q.position.entries =
          P.position.size :: (P.position.entries ++ (v₀ ++ v₁)) := by
        apply List.append_cancel_left (as := P.position.stem.ordinary)
        simpa only [Position.ordinary, hQstem, hQsize, List.append_assoc,
          List.cons_append] using hQord
      exact (List.cons.inj he).2
    have hvH : ∀ x ∈ v₀ ++ v₁, x ∈ H := by
      intro x hx
      exact (List.mem_append.mp hx).elim (fun hx ↦ (hv₀ x hx).1) (fun hx ↦ hKH (hv₁K x hx))
    have hvb : ∀ x ∈ v₀ ++ v₁, bS < x := by
      intro x hx
      exact (List.mem_append.mp hx).elim (fun hx ↦ (hv₀ x hx).2) (fun hx ↦ hKbS x (hv₁K x hx))
    obtain ⟨Q₀, hQ₀R, hQ₀L, hQ₀ord, hST⟩ := hbS Q.position (v₀ ++ v₁)
      (congrArg Stem.ordinary hQstem) hQsize hQlen hQentries hvH hvb
    exact InsideCompletion.triangle hH B Q₀ Q T U T₁ U₁
      ⟨hQ₀R.trans hPR, hQ₀L⟩ ⟨hQR, hQL⟩ hT ⟨hUR, hUL⟩ hQ₀ord hTord hUord hST hblueQ hTU
  · rw [hC] at hblueV
    exact (InsideEndgame.complete_incomplete_not_blue hH B C (.leaf U) (by simp) hblueV).elim

theorem no_singleton_root_certificate {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (b₀ : ℕ)
    (hroot : ∀ A : RootResponses.Setup 0,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b₀ < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.body (ofRoot A), .initial)) true) :
    False := by
  obtain ⟨A₀, _, hA₀, _⟩ := ReservedResponses.root_reserved hH b₀ 0 0
  let E := ofRoot A₀
  have hE : ExactSlots.Exact (.body E) :=
    ExactSlots.step_exact (DecisionStates.Step.root A₀) trivial
  have hER : E.roots = [] := by
    change A₀.stem.rootLabel.tail = []
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_tail, A₀.label_length]
  have hblueE := hroot A₀ (fun x hx ↦ (hA₀ x hx).1) (fun x hx ↦ (hA₀ x hx).2)
  have hleftE : LeftBlue H (GraphPayoff.payoff B .inside) (.body E, .initial) := by
    rcases blue_command (GraphPayoff.payoff B .inside) (.body E, .initial) rfl hblueE with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨k, bBody, hbBody⟩ := BlueReservations.left_body_setups
    (GraphPayoff.payoff B .inside) E .initial hleftE
  let c := pairBound (.body E, .initial)
  let L := max bBody c
  obtain ⟨A, Z, hA⟩ := SharedLast.body_reserved E.stem E.room hH L k
  let S := applyBody E A
  have hSR : S.roots = [] := hER
  have hS : ExactSlots.Exact (.leaf S) := ExactSlots.step_exact (DecisionStates.Step.body E A) hE
  have hbody : ∀ A' : BodyResponses.Setup E.stem k,
      (∀ x ∈ BodyResponses.newWord A'.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A'.position, L < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf (applyBody E A'), .initial)) true :=
    fun A' hAH hAL ↦ hbBody A' hAH (fun x hx ↦ (le_max_left _ _).trans_lt (hAL x hx))
  have hblueS := hbody A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hA x hx).2
  have hhand : RightBlue H (GraphPayoff.payoff B .inside) (.leaf S, .initial) :=
    handoff_after_left hH B .inside (.body E, .initial) (bodyResponse E k c)
      (bodyMember E c A hAc) S (bodyMember_result E c A hAc) hblueS
  obtain ⟨m, At, Ct, hAt, hCt, hstart⟩ :=
    BlueReservations.second_root_reserved hH B hB .inside hinit S hhand 0 b₀
  let K := H \ Set.Iic b₀
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic b₀)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  have hKb : ∀ x ∈ K, b₀ < x := fun x hx ↦ Nat.lt_of_not_ge hx.2
  obtain ⟨T, V, T₁, hTR, hTL, hrun, hblueV, hleftV, hTord, _, hTright⟩ :=
    InitialRelays.root_to_last_first hK hKH b₀ hKb B .inside hroot At hAt Ct hCt
      (.leaf S) hS hstart
  rcases run_last_body_left_cases S (.body (ofRoot At)) V (.leaf T) hSR hrun with
    ⟨P, hPstate, hsame⟩ | ⟨C, hC⟩
  · subst V
    have hP := ExactSlots.run_exact_left hrun hS
    have hEstem : E.stem = P.position.stem := (hsame.2.1.trans A.stem_eq).symm
    let Z' := Z.move P.position hsame.2.1 hsame.2.2.1 hsame.2.2.2.1
    have hSsupport : ∀ x ∈ State.decorated (.leaf S), x ∈ H := by
      change ∀ x ∈ A.position.decorated, x ∈ H
      rw [BodyResponses.setup_decorated]
      intro x hx
      exact (List.mem_append.mp hx).elim (fun hx ↦ (hA₀ x hx).1) (fun hx ↦ (hA x hx).1)
    obtain ⟨v, w, hv, _, hvK, _⟩ := CompletionReplay.run_supported_suffixes hrun
    change P.position.ordinary = S.position.ordinary ++ v at hv
    have hsupport : ∀ x ∈ P.position.ordinary, x ∈ H := by
      rw [hv]
      intro x hx
      exact (List.mem_append.mp hx).elim
        (fun hx ↦ hSsupport x (S.position.ordinary_sublist.subset hx)) (fun hx ↦ hKH (hvK x hx))
    have hentries : ∀ x ∈ P.position.entries, x ∈ H := fun x hx ↦
      hsupport x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    obtain ⟨s, t, u, hst, hsu, htu⟩ := triangle_of_reserve hH B hB hinit P T T₁ hsame.1 hP
      ⟨hTR, hTL⟩ hleftV hentries E hE hER hEstem k L Z' (le_max_right _ _) hbody hTord hTright
    exact hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)
  · rw [hC] at hblueV
    exact InsideEndgame.complete_incomplete_not_blue hH B C (.leaf T) (by simp) hblueV

theorem initial_root_setups_at_least_two {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ k b : ℕ, 0 < k ∧ ∀ A : RootResponses.Setup k,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.body (ofRoot A), .initial)) true := by
  obtain ⟨k, b, hb⟩ := BlueReservations.initial_root_setups hH B hB .inside hinit
  have hk : k ≠ 0 := by
    intro he
    subst k
    exact no_singleton_root_certificate hH B hB hinit b hb
  exact ⟨k, b, Nat.pos_of_ne_zero hk, hb⟩

end Erdos118.InsideSingleton
