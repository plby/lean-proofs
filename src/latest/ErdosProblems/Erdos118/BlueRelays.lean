import ErdosProblems.Erdos118.BlueReservations
import ErdosProblems.Erdos118.BlueCheckpoints
import ErdosProblems.Erdos118.BoundaryRelays
import ErdosProblems.Erdos118.CompletionReplay

/-!
An actual blue last-body relay: one word's last selected leaf in a first
game is its first selected leaf in a second game. Both root-stage blue
certificates are explicit inputs, and every response bound is announced
before the coordinates it governs. This is not the full triangle theorem.
-/

namespace Erdos118.BlueRelays

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays

theorem left_root_relay {H K : Set ℕ} (hKH : K ⊆ H) (b : ℕ)
    (hKb : ∀ x ∈ K, b < x) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    {k l : ℕ}
    (hrootBlue : ∀ A : RootResponses.Setup l,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.body (ofRoot A), .initial)) true)
    (A : RootResponses.Setup k) (hA : ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x)
    (C : Reserve A.stem.rootLabel A.stem.root l) (hC : ∀ x ∈ C.label, x ∈ H ∧ b < x)
    (T : State) (hT : ExactSlots.Exact T) (D : BodyDecision) (U : State)
    (hrun : ConservativeRuns.Run K (GraphPayoff.payoff B o)
      (.body (ofRoot A), T) (.body D, U)) (hR : D.roots = []) :
    ∃ hD : ExactSlots.Exact (.body D), ∃ C' : Reserve D.stem.rootLabel D.stem.root l,
      C'.label = C.label ∧ RamseyGame.Outcome H (GraphPayoff.game B o
        (.body (ofRoot (rootAtLastBody D hD hR C')), .initial)) true := by
  have hD := (ExactSlots.run_exact hrun
    ⟨ExactSlots.step_exact (DecisionStates.Step.root A) trivial, hT⟩).1
  have hext := (SkippedCuts.run_extensions hrun).1
  have hlabel : D.stem.rootLabel = A.stem.rootLabel :=
    Option.some.inj (hext.labels.root A.stem.rootLabel rfl)
  have hmarker : A.stem.root = D.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1
  let C' : Reserve D.stem.rootLabel D.stem.root l :=
    { label := C.label, card := C.card, increasing := C.increasing
      first := by rw [hlabel]; exact C.first
      below := by intro x hx; rw [← hmarker]; exact C.below x hx
      shared := by intro x; rw [hlabel]; exact C.shared x }
  obtain ⟨v, w, hv, _, hvK, _⟩ := CompletionReplay.run_supported_suffixes hrun
  have hstem : ∀ x ∈ D.stem.ordinary, x ∈ H ∧ b < x := by
    intro x hx
    change D.stem.ordinary = A.stem.ordinary ++ v at hv
    rw [hv] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hA x (A.stem.ordinary_sublist.subset hx)
    · exact ⟨hKH (hvK x hx), hKb x (hvK x hx)⟩
  have hfresh := rootAtLastBody_supported D hD hR C' hC hstem
  exact ⟨hD, C', rfl, hrootBlue (rootAtLastBody D hD hR C')
    (fun x hx ↦ (hfresh x hx).1) (fun x hx ↦ (hfresh x hx).2)⟩

theorem right_root_relay {H K : Set ℕ} (hKH : K ⊆ H) (b : ℕ)
    (hKb : ∀ x ∈ K, b < x) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    {k l : ℕ}
    (hrootBlue : ∀ A : RootResponses.Setup l,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.body (ofRoot A), .initial)) true)
    (A : RootResponses.Setup k) (hA : ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x)
    (C : Reserve A.stem.rootLabel A.stem.root l) (hC : ∀ x ∈ C.label, x ∈ H ∧ b < x)
    (T : State) (hT : ExactSlots.Exact T) (D : BodyDecision) (U : State)
    (hrun : ConservativeRuns.Run K (GraphPayoff.payoff B o)
      (T, .body (ofRoot A)) (U, .body D)) (hR : D.roots = []) :
    ∃ hD : ExactSlots.Exact (.body D), ∃ C' : Reserve D.stem.rootLabel D.stem.root l,
      C'.label = C.label ∧ RamseyGame.Outcome H (GraphPayoff.game B o
        (.body (ofRoot (rootAtLastBody D hD hR C')), .initial)) true := by
  have hD := (ExactSlots.run_exact hrun
    ⟨hT, ExactSlots.step_exact (DecisionStates.Step.root A) trivial⟩).2
  have hext := (SkippedCuts.run_extensions hrun).2
  have hlabel : D.stem.rootLabel = A.stem.rootLabel :=
    Option.some.inj (hext.labels.root A.stem.rootLabel rfl)
  have hmarker : A.stem.root = D.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1
  let C' : Reserve D.stem.rootLabel D.stem.root l :=
    { label := C.label, card := C.card, increasing := C.increasing
      first := by rw [hlabel]; exact C.first
      below := by intro x hx; rw [← hmarker]; exact C.below x hx
      shared := by intro x; rw [hlabel]; exact C.shared x }
  obtain ⟨w, v, _, hv, _, hvK⟩ := CompletionReplay.run_supported_suffixes hrun
  have hstem : ∀ x ∈ D.stem.ordinary, x ∈ H ∧ b < x := by
    intro x hx
    change D.stem.ordinary = A.stem.ordinary ++ v at hv
    rw [hv] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hA x (A.stem.ordinary_sublist.subset hx)
    · exact ⟨hKH (hvK x hx), hKb x (hvK x hx)⟩
  have hfresh := rootAtLastBody_supported D hD hR C' hC hstem
  exact ⟨hD, C', rfl, hrootBlue (rootAtLastBody D hD hR C')
    (fun x hx ↦ (hfresh x hx).1) (fun x hx ↦ (hfresh x hx).2)⟩

theorem left_last_body_relay {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (D : BodyDecision) (T : State)
    (hD : ExactSlots.Exact (.body D)) (hT : ExactSlots.Exact T) (hR : D.roots = [])
    {l : ℕ} (C : Reserve D.stem.rootLabel D.stem.root l)
    (hfirst : LeftBlue H (GraphPayoff.payoff B o) (.body D, T))
    (hsecond : RamseyGame.Outcome H (GraphPayoff.game B o
      (.body (ofRoot (rootAtLastBody D hD hR C)), .initial)) true) (d : ℕ) :
    let E := ofRoot (rootAtLastBody D hD hR C)
    ∃ K : Set ℕ, K.Infinite ∧ K ⊆ H ∧ (∀ x ∈ K, d < x) ∧
      ∃ P : Pending, ∃ U : State, ∃ k : ℕ, ∃ A : BodyResponses.Setup E.stem k,
        P.roots = [] ∧ P.leaves = [] ∧
        ConservativeRuns.Run K (GraphPayoff.payoff B o) (.body D, T) (.leaf P, U) ∧
        RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, U)) true ∧
        RightBlue H (GraphPayoff.payoff B o) (.leaf P, U) ∧
        (applyBody E A).position.ordinary = P.position.ordinary ∧
        RamseyGame.Outcome H (GraphPayoff.game B o (.leaf (applyBody E A), .initial)) true ∧
        RightBlue H (GraphPayoff.payoff B o) (.leaf (applyBody E A), .initial) := by
  let payoff := GraphPayoff.payoff B o
  let E := ofRoot (rootAtLastBody D hD hR C)
  have hsecondLeft : LeftBlue H payoff (.body E, .initial) := by
    rcases blue_command payoff (.body E, .initial) rfl hsecond with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨k₂, b₂, hb₂⟩ := BlueReservations.left_body_setups payoff E .initial hsecondLeft
  obtain ⟨k₁, b₁, hb₁⟩ := BlueReservations.left_body_setups payoff D T hfirst
  let c₁ := pairBound (.body D, T)
  let c₂ := pairBound (.body E, .initial)
  let L := max b₂ (max c₂ d)
  let K := H \ Set.Iic L
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic L)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  have hdL : d ≤ L := (le_max_right c₂ d).trans (le_max_right b₂ _)
  let g := ConservativeRuns.leftGuard K payoff (.body D, T) k₁
  let M := max b₁ (max c₁ (max L g))
  obtain ⟨A₁, R, hA₁, hreserve, hbefore⟩ := body_reserved D.stem D.room hH M k₁ k₂
  have hb₁M : b₁ ≤ M := le_max_left _ _
  have hc₁M : c₁ ≤ M := (le_max_left c₁ _).trans (le_max_right b₁ _)
  have hLM : L ≤ M := (le_max_left L g).trans
    ((le_max_right c₁ _).trans (le_max_right b₁ _))
  have hgM : g ≤ M := (le_max_right L g).trans
    ((le_max_right c₁ _).trans (le_max_right b₁ _))
  have hA₁c : ∀ x ∈ BodyResponses.newWord A₁.position, c₁ < x :=
    fun x hx ↦ hc₁M.trans_lt (hA₁ x hx).2
  let a₁ := bodyMember D c₁ A₁ hA₁c
  let P₀ := applyBody D A₁
  have ha₁K : (↑a₁.1 : Set ℕ) ⊆ K := by
    intro x hx
    have hm := hA₁ x (List.mem_toFinset.mp hx)
    exact ⟨hm.1, Nat.not_le_of_gt (hLM.trans_lt hm.2)⟩
  have ha₁g : ∀ x ∈ a₁.1, g < x :=
    fun x hx ↦ hgM.trans_lt (hA₁ x (List.mem_toFinset.mp hx)).2
  have hstep : ConservativeRuns.Step K payoff (.body D, T) (.leaf P₀, T) := by
    have hs := ConservativeRuns.Step.left (.body D, T) k₁ (bodyResponse D k₁ c₁)
      rfl rfl a₁ ha₁K ha₁g
    simpa only [a₁, bodyMember_result] using hs
  have hb₀ : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P₀, T)) true :=
    hb₁ A₁ (fun x hx ↦ (hA₁ x hx).1) (fun x hx ↦ hb₁M.trans_lt (hA₁ x hx).2)
  have hh₀ : RightBlue H payoff (.leaf P₀, T) :=
    handoff_after_left hH B o (.body D, T) (bodyResponse D k₁ c₁) a₁ P₀
      (bodyMember_result D c₁ A₁ hA₁c) hb₀
  obtain ⟨P, U, hPR, hPL, hrun, hbP, hhP⟩ := BlueCheckpoints.left_last_leaf_handoff
    hK hKH B o (.leaf P₀) T trivial hb₀ (fun _ ↦ hh₀)
  have hwhole : ConservativeRuns.Run K payoff (.body D, T) (.leaf P, U) :=
    Relation.ReflTransGen.head hstep hrun
  have hPexact := (ExactSlots.run_exact hwhole ⟨hD, hT⟩).1
  have hP₀R : P₀.roots = [] := hR
  have hsame := run_last_body_left P₀ P T U hP₀R hrun
  have hPstem : P.position.stem = D.stem := hsame.2.1.trans A₁.stem_eq
  have hPsize : P.position.size = A₁.position.size := hsame.2.2.1
  have hPlabel : P.position.label = A₁.position.label := hsame.2.2.2.1
  let R' : Reserve P.position.label P.position.size k₂ :=
    { label := R.label, card := R.card, increasing := R.increasing
      first := R.first.trans (congrArg (fun a : List ℕ ↦ a.getLastD 0) hPlabel).symm
      below := by intro x hx; rw [hPsize]; exact R.below x hx
      shared := by intro x; rw [hPlabel]; exact R.shared x }
  have hCroot : ∀ x ∈ C.label, x < P.position.stem.root := by
    rw [hPstem]
    exact C.below
  have hbefore' : ∀ x ∈ P.position.stem.decorated, ∀ y ∈ R'.label, x < y := by
    rw [hPstem]
    exact hbefore
  let A₀ := bodyAtLastLeaf P hPexact hPL C.label C.increasing hCroot R' hbefore'
  have hstemOverlay :
      (LabelOverlays.plainStem P.position.stem C.label C.increasing hCroot) = E.stem := by
    change LabelOverlays.plainStem P.position.stem C.label C.increasing hCroot =
      LabelOverlays.plainStem D.stem C.label C.increasing C.below
    congr 1
  let A₂ : BodyResponses.Setup E.stem k₂ :=
    { position := A₀.position, stem_eq := A₀.stem_eq.trans hstemOverlay
      label_length := A₀.label_length, entries_length := A₀.entries_length }
  have hA₂word : BodyResponses.newWord A₂.position =
      R.label ++ P.position.size :: P.position.entries :=
    bodyAtLastLeaf_newWord P hPexact hPL C.label C.increasing hCroot R' hbefore'
  obtain ⟨v, w, hv, _, hvK, _⟩ := CompletionReplay.run_supported_suffixes hrun
  have htail : P.position.size :: P.position.entries =
      (A₁.position.size :: A₁.position.entries) ++ v := by
    have hP₀stem : P₀.position.stem = D.stem := A₁.stem_eq
    simp only [State.ordinary, Position.ordinary, hPstem, hP₀stem, List.append_assoc] at hv
    exact List.append_cancel_left hv
  have hA₂ : ∀ x ∈ BodyResponses.newWord A₂.position, x ∈ H ∧ L < x := by
    rw [hA₂word, htail]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(hreserve x hx).1, hLM.trans_lt (hreserve x hx).2⟩
    · rcases List.mem_append.mp hx with hx | hx
      · have hm := hA₁ x (List.mem_append_right _ hx)
        exact ⟨hm.1, hLM.trans_lt hm.2⟩
      · have hm := hvK x hx
        exact ⟨hm.1, Nat.lt_of_not_ge hm.2⟩
  have hb₂L : b₂ ≤ L := le_max_left _ _
  have hc₂L : c₂ ≤ L := (le_max_left c₂ d).trans (le_max_right b₂ _)
  have hbQ : RamseyGame.Outcome H (GraphPayoff.game B o
      (.leaf (applyBody E A₂), .initial)) true :=
    hb₂ A₂ (fun x hx ↦ (hA₂ x hx).1) (fun x hx ↦ hb₂L.trans_lt (hA₂ x hx).2)
  have hA₂c : ∀ x ∈ BodyResponses.newWord A₂.position, c₂ < x :=
    fun x hx ↦ hc₂L.trans_lt (hA₂ x hx).2
  have hhQ : RightBlue H payoff (.leaf (applyBody E A₂), .initial) :=
    handoff_after_left hH B o (.body E, .initial) (bodyResponse E k₂ c₂)
      (bodyMember E c₂ A₂ hA₂c) (applyBody E A₂) (bodyMember_result E c₂ A₂ hA₂c) hbQ
  refine ⟨K, hK, hKH, fun x hx ↦ hdL.trans_lt (Nat.lt_of_not_ge hx.2),
    P, U, k₂, A₂, hPR, hPL, hwhole, hbP, hhP, ?_, hbQ, hhQ⟩
  exact bodyAtLastLeaf_ordinary P hPexact hPL C.label C.increasing hCroot R' hbefore'

theorem right_last_body_relay {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (D : BodyDecision) (T : State)
    (hD : ExactSlots.Exact (.body D)) (hT : ExactSlots.Exact T) (hR : D.roots = [])
    {l : ℕ} (C : Reserve D.stem.rootLabel D.stem.root l)
    (hfirst : RightBlue H (GraphPayoff.payoff B o) (T, .body D))
    (hsecond : RamseyGame.Outcome H (GraphPayoff.game B o
      (.body (ofRoot (rootAtLastBody D hD hR C)), .initial)) true) (d : ℕ) :
    let E := ofRoot (rootAtLastBody D hD hR C)
    ∃ K : Set ℕ, K.Infinite ∧ K ⊆ H ∧ (∀ x ∈ K, d < x) ∧
      ∃ P : Pending, ∃ U : State, ∃ k : ℕ, ∃ A : BodyResponses.Setup E.stem k,
        P.roots = [] ∧ P.leaves = [] ∧
        ConservativeRuns.Run K (GraphPayoff.payoff B o) (T, .body D) (U, .leaf P) ∧
        RamseyGame.Outcome H (GraphPayoff.game B o (U, .leaf P)) true ∧
        LeftBlue H (GraphPayoff.payoff B o) (U, .leaf P) ∧
        (applyBody E A).position.ordinary = P.position.ordinary ∧
        RamseyGame.Outcome H (GraphPayoff.game B o (.leaf (applyBody E A), .initial)) true ∧
        RightBlue H (GraphPayoff.payoff B o) (.leaf (applyBody E A), .initial) := by
  let payoff := GraphPayoff.payoff B o
  let E := ofRoot (rootAtLastBody D hD hR C)
  have hallowed : allowedSide (T, .body D) true = true := by
    obtain ⟨n, R, hs, _⟩ := hfirst
    exact hs
  have hsecondLeft : LeftBlue H payoff (.body E, .initial) := by
    rcases blue_command payoff (.body E, .initial) rfl hsecond with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨k₂, b₂, hb₂⟩ := BlueReservations.left_body_setups payoff E .initial hsecondLeft
  obtain ⟨k₁, b₁, hb₁⟩ := BlueReservations.right_body_setups payoff T D hfirst
  let c₁ := pairBound (T, .body D)
  let c₂ := pairBound (.body E, .initial)
  let L := max b₂ (max c₂ d)
  let K := H \ Set.Iic L
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic L)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  have hdL : d ≤ L := (le_max_right c₂ d).trans (le_max_right b₂ _)
  let g := ConservativeRuns.rightGuard K payoff (T, .body D) k₁
  let M := max b₁ (max c₁ (max L g))
  obtain ⟨A₁, R, hA₁, hreserve, hbefore⟩ := body_reserved D.stem D.room hH M k₁ k₂
  have hb₁M : b₁ ≤ M := le_max_left _ _
  have hc₁M : c₁ ≤ M := (le_max_left c₁ _).trans (le_max_right b₁ _)
  have hLM : L ≤ M := (le_max_left L g).trans
    ((le_max_right c₁ _).trans (le_max_right b₁ _))
  have hgM : g ≤ M := (le_max_right L g).trans
    ((le_max_right c₁ _).trans (le_max_right b₁ _))
  have hA₁c : ∀ x ∈ BodyResponses.newWord A₁.position, c₁ < x :=
    fun x hx ↦ hc₁M.trans_lt (hA₁ x hx).2
  let a₁ := bodyMember D c₁ A₁ hA₁c
  let P₀ := applyBody D A₁
  have ha₁K : (↑a₁.1 : Set ℕ) ⊆ K := by
    intro x hx
    have hm := hA₁ x (List.mem_toFinset.mp hx)
    exact ⟨hm.1, Nat.not_le_of_gt (hLM.trans_lt hm.2)⟩
  have ha₁g : ∀ x ∈ a₁.1, g < x :=
    fun x hx ↦ hgM.trans_lt (hA₁ x (List.mem_toFinset.mp hx)).2
  have hstep : ConservativeRuns.Step K payoff (T, .body D) (T, .leaf P₀) := by
    have hs := ConservativeRuns.Step.right (T, .body D) k₁ (bodyResponse D k₁ c₁)
      hallowed rfl a₁ ha₁K ha₁g
    simpa only [a₁, bodyMember_result] using hs
  have hb₀ : RamseyGame.Outcome H (GraphPayoff.game B o (T, .leaf P₀)) true :=
    hb₁ A₁ (fun x hx ↦ (hA₁ x hx).1) (fun x hx ↦ hb₁M.trans_lt (hA₁ x hx).2)
  have hh₀ : LeftBlue H payoff (T, .leaf P₀) :=
    handoff_after_right hH B o (T, .body D) (bodyResponse D k₁ c₁) a₁ P₀
      (bodyMember_result D c₁ A₁ hA₁c) hb₀
  obtain ⟨P, U, hPR, hPL, hrun, hbP, hhP⟩ := BlueCheckpoints.right_last_leaf_handoff
    hK hKH B o T (.leaf P₀) trivial hb₀ (fun _ ↦ hh₀)
  have hwhole : ConservativeRuns.Run K payoff (T, .body D) (U, .leaf P) :=
    Relation.ReflTransGen.head hstep hrun
  have hPexact := (ExactSlots.run_exact hwhole ⟨hT, hD⟩).2
  have hP₀R : P₀.roots = [] := hR
  have hsame := run_last_body_right P₀ P T U hP₀R hrun
  have hPstem : P.position.stem = D.stem := hsame.2.1.trans A₁.stem_eq
  have hPsize : P.position.size = A₁.position.size := hsame.2.2.1
  have hPlabel : P.position.label = A₁.position.label := hsame.2.2.2.1
  let R' : Reserve P.position.label P.position.size k₂ :=
    { label := R.label, card := R.card, increasing := R.increasing
      first := R.first.trans (congrArg (fun a : List ℕ ↦ a.getLastD 0) hPlabel).symm
      below := by intro x hx; rw [hPsize]; exact R.below x hx
      shared := by intro x; rw [hPlabel]; exact R.shared x }
  have hCroot : ∀ x ∈ C.label, x < P.position.stem.root := by
    rw [hPstem]
    exact C.below
  have hbefore' : ∀ x ∈ P.position.stem.decorated, ∀ y ∈ R'.label, x < y := by
    rw [hPstem]
    exact hbefore
  let A₀ := bodyAtLastLeaf P hPexact hPL C.label C.increasing hCroot R' hbefore'
  have hstemOverlay :
      (LabelOverlays.plainStem P.position.stem C.label C.increasing hCroot) = E.stem := by
    change LabelOverlays.plainStem P.position.stem C.label C.increasing hCroot =
      LabelOverlays.plainStem D.stem C.label C.increasing C.below
    congr 1
  let A₂ : BodyResponses.Setup E.stem k₂ :=
    { position := A₀.position, stem_eq := A₀.stem_eq.trans hstemOverlay
      label_length := A₀.label_length, entries_length := A₀.entries_length }
  have hA₂word : BodyResponses.newWord A₂.position =
      R.label ++ P.position.size :: P.position.entries :=
    bodyAtLastLeaf_newWord P hPexact hPL C.label C.increasing hCroot R' hbefore'
  obtain ⟨w, v, _, hv, _, hvK⟩ := CompletionReplay.run_supported_suffixes hrun
  have htail : P.position.size :: P.position.entries =
      (A₁.position.size :: A₁.position.entries) ++ v := by
    have hP₀stem : P₀.position.stem = D.stem := A₁.stem_eq
    simp only [State.ordinary, Position.ordinary, hPstem, hP₀stem, List.append_assoc] at hv
    exact List.append_cancel_left hv
  have hA₂ : ∀ x ∈ BodyResponses.newWord A₂.position, x ∈ H ∧ L < x := by
    rw [hA₂word, htail]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(hreserve x hx).1, hLM.trans_lt (hreserve x hx).2⟩
    · rcases List.mem_append.mp hx with hx | hx
      · have hm := hA₁ x (List.mem_append_right _ hx)
        exact ⟨hm.1, hLM.trans_lt hm.2⟩
      · have hm := hvK x hx
        exact ⟨hm.1, Nat.lt_of_not_ge hm.2⟩
  have hb₂L : b₂ ≤ L := le_max_left _ _
  have hc₂L : c₂ ≤ L := (le_max_left c₂ d).trans (le_max_right b₂ _)
  have hbQ : RamseyGame.Outcome H (GraphPayoff.game B o
      (.leaf (applyBody E A₂), .initial)) true :=
    hb₂ A₂ (fun x hx ↦ (hA₂ x hx).1) (fun x hx ↦ hb₂L.trans_lt (hA₂ x hx).2)
  have hA₂c : ∀ x ∈ BodyResponses.newWord A₂.position, c₂ < x :=
    fun x hx ↦ hc₂L.trans_lt (hA₂ x hx).2
  have hhQ : RightBlue H payoff (.leaf (applyBody E A₂), .initial) :=
    handoff_after_left hH B o (.body E, .initial) (bodyResponse E k₂ c₂)
      (bodyMember E c₂ A₂ hA₂c) (applyBody E A₂) (bodyMember_result E c₂ A₂ hA₂c) hbQ
  refine ⟨K, hK, hKH, fun x hx ↦ hdL.trans_lt (Nat.lt_of_not_ge hx.2),
    P, U, k₂, A₂, hPR, hPL, hwhole, hbP, hhP, ?_, hbQ, hhQ⟩
  exact bodyAtLastLeaf_ordinary P hPexact hPL C.label C.increasing hCroot R' hbefore'

end Erdos118.BlueRelays
