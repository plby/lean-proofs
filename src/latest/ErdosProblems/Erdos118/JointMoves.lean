import ErdosProblems.Erdos118.JointOpening
import ErdosProblems.Erdos118.LeafReplay
import ErdosProblems.Erdos118.StemReplay

/-!
Joint actual pending responses when the two next selected cuts agree.
The old decorations are retained separately and both guards use one fixed
working alphabet. Unequal next cuts are not identified by these theorems.
-/

namespace Erdos118.JointMoves

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

theorem ordinary_components (P Q : Position) (h : P.ordinary = Q.ordinary) :
    P.stem.root = Q.stem.root ∧ P.stem.ordinary = Q.stem.ordinary ∧
      P.stem.done.length = Q.stem.done.length ∧ P.size = Q.size ∧ P.entries = Q.entries := by
  have he : P.toInterior = Q.toInterior := CutIndices.interior_word_injective
    (by simpa only [Position.toInterior_word] using h)
  have hr : P.stem.root = Q.stem.root := congrArg InteriorWords.Position.root he
  have hs : P.size = Q.size := congrArg InteriorWords.Position.size he
  have hu : P.entries = Q.entries := congrArg InteriorWords.Position.entries he
  have hc := congrArg (fun R : InteriorWords.Position ↦ R.done.length) he
  have hstem : P.stem.ordinary = Q.stem.ordinary := by
    apply List.append_cancel_right (bs := P.size :: P.entries)
    simpa only [Position.ordinary, ← hs, ← hu] using h
  exact ⟨hr, hstem, by simpa only [Position.toInterior, List.length_map] using hc, hs, hu⟩

private theorem command_data {H : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (P X : State)
    (h : CommandBlue H B o right P X) :
    ∃ n : ℕ, ∃ R : Response P (pairBound (pair right P X)),
      allowedSide (pair right P X) right = true ∧
      responseFor P (pairBound (pair right P X)) n = some R ∧
      ∃ b : ℕ, ∀ a : R.family.members, (↑a.1 : Set ℕ) ⊆ H →
        (∀ x ∈ a.1, b < x) → Blue H B o right (R.result a) X := by
  cases right <;> exact h

private noncomputable def responseGuard (K : Set ℕ) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (P X : State) : ℕ :=
  if right then ConservativeRuns.rightGuard K (GraphPayoff.payoff B o) (pair right P X) 0
  else ConservativeRuns.leftGuard K (GraphPayoff.payoff B o) (pair right P X) 0

private theorem response_step {K : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (P X : State)
    (R : Response P (pairBound (pair right P X)))
    (hs : allowedSide (pair right P X) right = true)
    (hR : responseFor P (pairBound (pair right P X)) 0 = some R)
    (a : R.family.members) (ha : (↑a.1 : Set ℕ) ⊆ K)
    (hg : ∀ x ∈ a.1, responseGuard K B o right P X < x) :
    ConservativeRuns.Step K (GraphPayoff.payoff B o)
      (pair right P X) (pair right (R.result a) X) := by
  cases right with
  | false => exact ConservativeRuns.Step.left (P, X) 0 R hs hR a ha hg
  | true => exact ConservativeRuns.Step.right (X, P) 0 R hs hR a ha hg

private theorem response_handoff {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (P X : State)
    (R : Response P (pairBound (pair right P X))) (a : R.family.members)
    (Q : Pending) (hQ : R.result a = .leaf Q)
    (hb : Blue H B o right (.leaf Q) X) : OtherBlue H B o right (.leaf Q) X := by
  cases right with
  | false => exact handoff_after_left hH B o (P, X) R a Q hQ hb
  | true => exact handoff_after_right hH B o (X, P) R a Q hQ hb

private theorem body_command {H : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (D : BodyDecision) (X : State)
    (hs : allowedSide (pair right (.body D) X) right = true)
    (hb : Blue H B o right (.body D) X) : CommandBlue H B o right (.body D) X := by
  cases right with
  | false =>
    rcases blue_command (GraphPayoff.payoff B o) (.body D, X) rfl hb with hl | hr
    · exact hl
    · obtain ⟨n, R, ha, _⟩ := hr
      simp [allowedSide] at ha
  | true =>
    have hn : terminalPayoff (GraphPayoff.payoff B o) (X, .body D) = none := by
      cases X <;> rfl
    rcases blue_command (GraphPayoff.payoff B o) (X, .body D) hn hb with hl | hr
    · obtain ⟨n, R, ha, _⟩ := hl
      cases X <;> simp_all [pair, allowedSide]
    · exact hr

theorem leaf_bound {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (right : Bool)
    (P : Pending) (X : State) (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (hblue : CommandBlue H B o right (.leaf P) X) :
    ∃ b : ℕ, ∀ A : LeafResponses.Setup P.position j,
      (∀ x ∈ A.newWord, x ∈ K ∧ b < x) →
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair right (.leaf P) X) (pair right (.leaf (LeafResponses.toPending P j rest hP A)) X) ∧
      Blue H B o right (.leaf (LeafResponses.toPending P j rest hP A)) X ∧
      OtherBlue H B o right (.leaf (LeafResponses.toPending P j rest hP A)) X := by
  obtain ⟨n, R, hs, hresp, b, hb⟩ := command_data B o right (.leaf P) X hblue
  let c := pairBound (pair right (.leaf P) X)
  let g := responseGuard K B o right (.leaf P) X
  have he : R = leafResponse P j rest hP c :=
    Option.some.inj (hresp.symm.trans (LeafReplay.selector P j rest hP c n))
  subst R
  refine ⟨max b (max c g), ?_⟩
  intro A hA
  have hAc : ∀ x ∈ A.newWord, c < x :=
    fun x hx ↦ ((le_max_left c g).trans (le_max_right b _)).trans_lt (hA x hx).2
  let a := LeafReplay.member P j rest hP c A hAc
  have haK : (↑a.1 : Set ℕ) ⊆ K := fun x hx ↦ (hA x (List.mem_toFinset.mp hx)).1
  have hab : ∀ x ∈ a.1, b < x :=
    fun x hx ↦ (le_max_left _ _).trans_lt (hA x (List.mem_toFinset.mp hx)).2
  have hag : ∀ x ∈ a.1, g < x := fun x hx ↦
    ((le_max_right c g).trans (le_max_right b _)).trans_lt (hA x (List.mem_toFinset.mp hx)).2
  have hresult := LeafReplay.member_result P j rest hP c A hAc
  have hnext := hb a (haK.trans hKH) hab
  rw [hresult] at hnext
  have hstep := response_step B o right (.leaf P) X (leafResponse P j rest hP c)
    hs (LeafReplay.selector P j rest hP c 0) a haK hag
  rw [hresult] at hstep
  exact ⟨hstep, hnext, response_handoff (hK.mono hKH) B o right (.leaf P) X
    (leafResponse P j rest hP c) a (LeafResponses.toPending P j rest hP A) hresult hnext⟩

theorem stem_bound {H K : Set ℕ} (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (right : Bool)
    (P : Pending) (X : State) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hL : P.leaves = [])
    (hblue : CommandBlue H B o right (.leaf P) X) :
    ∃ b : ℕ, ∀ A : StemResponses.Setup P.position (c - 1),
      (∀ x ∈ A.newWord, x ∈ K ∧ b < x) →
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair right (.leaf P) X) (pair right (.body (ofStem P c rest hR A)) X) ∧
      Blue H B o right (.body (ofStem P c rest hR A)) X ∧
      CommandBlue H B o right (.body (ofStem P c rest hR A)) X := by
  obtain ⟨n, R, hs, hresp, b, hb⟩ := command_data B o right (.leaf P) X hblue
  let d := pairBound (pair right (.leaf P) X)
  let g := responseGuard K B o right (.leaf P) X
  have he : R = nextBodyResponse P c rest hR hL d :=
    Option.some.inj (hresp.symm.trans (StemReplay.selector P c rest hR hL d n))
  subst R
  refine ⟨max b (max d g), ?_⟩
  intro A hA
  have hAd : ∀ x ∈ A.newWord, d < x :=
    fun x hx ↦ ((le_max_left d g).trans (le_max_right b _)).trans_lt (hA x hx).2
  let a := StemReplay.member P c rest hR hL d A hAd
  have haK : (↑a.1 : Set ℕ) ⊆ K := fun x hx ↦ (hA x (List.mem_toFinset.mp hx)).1
  have hab : ∀ x ∈ a.1, b < x :=
    fun x hx ↦ (le_max_left _ _).trans_lt (hA x (List.mem_toFinset.mp hx)).2
  have hag : ∀ x ∈ a.1, g < x := fun x hx ↦
    ((le_max_right d g).trans (le_max_right b _)).trans_lt (hA x (List.mem_toFinset.mp hx)).2
  have hresult := StemReplay.member_result P c rest hR hL d A hAd
  have hnext := hb a (haK.trans hKH) hab
  rw [hresult] at hnext
  have hstep := response_step B o right (.leaf P) X (nextBodyResponse P c rest hR hL d)
    hs (StemReplay.selector P c rest hR hL d 0) a haK hag
  rw [hresult] at hstep
  have hallowed : allowedSide (pair right (.body (ofStem P c rest hR A)) X) right = true := by
    cases right <;> cases X <;> simp_all [pair, allowedSide]
  exact ⟨hstep, hnext, body_command B o right (ofStem P c rest hR A) X hallowed hnext⟩

theorem respond_leaves {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (r s : Bool)
    (P Q : Pending) (X Y : State) (hord : P.position.ordinary = Q.position.ordinary)
    (j : ℕ) (restP restQ : List ℕ) (hP : P.leaves = j :: restP) (hQ : Q.leaves = j :: restQ)
    (hp : CommandBlue H B o r (.leaf P) X) (hq : CommandBlue H B o s (.leaf Q) Y) (d : ℕ) :
    ∃ A : LeafResponses.Setup P.position j, ∃ C : LeafResponses.Setup Q.position j,
      A.newWord = C.newWord ∧
      (LeafResponses.toPending P j restP hP A).position.ordinary =
        (LeafResponses.toPending Q j restQ hQ C).position.ordinary ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B o) (pair r (.leaf P) X)
        (pair r (.leaf (LeafResponses.toPending P j restP hP A)) X) ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B o) (pair s (.leaf Q) Y)
        (pair s (.leaf (LeafResponses.toPending Q j restQ hQ C)) Y) ∧
      Blue H B o r (.leaf (LeafResponses.toPending P j restP hP A)) X ∧
      Blue H B o s (.leaf (LeafResponses.toPending Q j restQ hQ C)) Y ∧
      OtherBlue H B o r (.leaf (LeafResponses.toPending P j restP hP A)) X ∧
      OtherBlue H B o s (.leaf (LeafResponses.toPending Q j restQ hQ C)) Y ∧
      (∀ x ∈ A.newWord, x ∈ K ∧ d < x) := by
  obtain ⟨bP, hbP⟩ := leaf_bound hK hKH B o r P X j restP hP hp
  obtain ⟨bQ, hbQ⟩ := leaf_bound hK hKH B o s Q Y j restQ hQ hq
  let bound := max bP (max bQ (max d Q.position.decorated.sum))
  have hPb : bP ≤ bound := by dsimp [bound]; omega
  have hQb : bQ ≤ bound := by dsimp [bound]; omega
  have hdb : d ≤ bound := by dsimp [bound]; omega
  have hsum : Q.position.decorated.sum ≤ bound := by dsimp [bound]; omega
  obtain ⟨A, hA⟩ := LeafResponses.setup_above P.position j hK bound
  have hentries := (ordinary_components P.position Q.position hord).2.2.2.2
  let C : LeafResponses.Setup Q.position j :=
    { newWord := A.newWord
      length_eq := by rw [A.length_eq, hentries]
      increasing := List.pairwise_append.mpr ⟨Q.position.increasing,
        LeafResponses.newWord_pairwise A,
        fun x hx y hy ↦ ((nat_le_sum_of_mem hx).trans hsum).trans_lt (hA y hy).2⟩ }
  have hCp : ∀ x ∈ C.newWord, x ∈ K ∧ bQ < x :=
    fun x hx ↦ ⟨(hA x hx).1, hQb.trans_lt (hA x hx).2⟩
  obtain ⟨hstepP, hblueP, hhandP⟩ := hbP A (fun x hx ↦ ⟨(hA x hx).1, hPb.trans_lt (hA x hx).2⟩)
  obtain ⟨hstepQ, hblueQ, hhandQ⟩ := hbQ C hCp
  refine ⟨A, C, rfl, ?_, hstepP, hstepQ, hblueP, hblueQ, hhandP, hhandQ,
    fun x hx ↦ ⟨(hA x hx).1, hdb.trans_lt (hA x hx).2⟩⟩
  have hslotP := P.leafSlots.bounded j (hP ▸ List.mem_cons_self ..)
  have hslotQ := Q.leafSlots.bounded j (hQ ▸ List.mem_cons_self ..)
  change (LeafResponses.position A hslotP.1 hslotP.2.1).ordinary =
    (LeafResponses.position C hslotQ.1 hslotQ.2.1).ordinary
  rw [LeafResponses.position_ordinary, LeafResponses.position_ordinary, hord]

theorem respond_stems {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (r s : Bool)
    (P Q : Pending) (X Y : State) (hord : P.position.ordinary = Q.position.ordinary)
    (c : ℕ) (restP restQ : List ℕ) (hP : P.roots = c :: restP) (hQ : Q.roots = c :: restQ)
    (hPL : P.leaves = []) (hQL : Q.leaves = [])
    (hp : CommandBlue H B o r (.leaf P) X) (hq : CommandBlue H B o s (.leaf Q) Y) (d : ℕ) :
    ∃ A : StemResponses.Setup P.position (c - 1), ∃ C : StemResponses.Setup Q.position (c - 1),
      A.newWord = C.newWord ∧ A.stem.ordinary = C.stem.ordinary ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B o) (pair r (.leaf P) X)
        (pair r (.body (ofStem P c restP hP A)) X) ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B o) (pair s (.leaf Q) Y)
        (pair s (.body (ofStem Q c restQ hQ C)) Y) ∧
      Blue H B o r (.body (ofStem P c restP hP A)) X ∧
      Blue H B o s (.body (ofStem Q c restQ hQ C)) Y ∧
      CommandBlue H B o r (.body (ofStem P c restP hP A)) X ∧
      CommandBlue H B o s (.body (ofStem Q c restQ hQ C)) Y ∧
      (∀ x ∈ A.newWord, x ∈ K ∧ d < x) := by
  obtain ⟨bP, hbP⟩ := stem_bound hKH B o r P X c restP hP hPL hp
  obtain ⟨bQ, hbQ⟩ := stem_bound hKH B o s Q Y c restQ hQ hQL hq
  let bound := max bP (max bQ d)
  have hPb : bP ≤ bound := by dsimp [bound]; omega
  have hQb : bQ ≤ bound := by dsimp [bound]; omega
  have hdb : d ≤ bound := by dsimp [bound]; omega
  have hboundsP := next_body_bounds P c restP hP
  have hboundsQ := next_body_bounds Q c restQ hQ
  obtain ⟨A, hA⟩ := StemResponses.setup_above P.position (c - 1) hboundsP.1 hboundsP.2.1 hK bound
  have hroot := (ordinary_components P.position Q.position hord).1
  obtain ⟨C, hCv, hCord⟩ := CompletionReplay.setup_of_literal_stem Q.position A.stem (c - 1)
    (A.root_eq.trans hroot) A.count hboundsQ.1 A.newWord (by rw [← hord]; exact A.ordinary)
  obtain ⟨hstepP, hblueP, hcmdP⟩ := hbP A (fun x hx ↦ ⟨(hA x hx).1, hPb.trans_lt (hA x hx).2⟩)
  obtain ⟨hstepQ, hblueQ, hcmdQ⟩ := hbQ C (by
    rw [hCv]
    exact fun x hx ↦ ⟨(hA x hx).1, hQb.trans_lt (hA x hx).2⟩)
  exact ⟨A, C, hCv.symm, hCord.symm, hstepP, hstepQ, hblueP, hblueQ, hcmdP, hcmdQ,
    fun x hx ↦ ⟨(hA x hx).1, hdb.trans_lt (hA x hx).2⟩⟩

theorem respond_next_bodies {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (r s : Bool)
    (P Q : Pending) (X Y : State) (hord : P.position.ordinary = Q.position.ordinary)
    (c : ℕ) (restP restQ : List ℕ) (hP : P.roots = c :: restP) (hQ : Q.roots = c :: restQ)
    (hPL : P.leaves = []) (hQL : Q.leaves = [])
    (hp : CommandBlue H B o r (.leaf P) X) (hq : CommandBlue H B o s (.leaf Q) Y) (d : ℕ) :
    ∃ P' Q' : Pending, P'.roots = restP ∧ Q'.roots = restQ ∧
      P'.position.ordinary = Q'.position.ordinary ∧
      (P'.position.label <+: Q'.position.label ∨ Q'.position.label <+: P'.position.label) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (pair r (.leaf P) X) (pair r (.leaf P') X) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (pair s (.leaf Q) Y) (pair s (.leaf Q') Y) ∧
      Blue H B o r (.leaf P') X ∧ Blue H B o s (.leaf Q') Y ∧
      OtherBlue H B o r (.leaf P') X ∧ OtherBlue H B o s (.leaf Q') Y ∧
      ∃ v : List ℕ, P'.position.ordinary = P.position.ordinary ++ v ∧
        Q'.position.ordinary = Q.position.ordinary ++ v ∧
        (∀ x ∈ v, x ∈ K ∧ d < x) := by
  obtain ⟨A, C, _, hstem, hsP, hsQ, _, _, hcP, hcQ, hA⟩ :=
    respond_stems hK hKH B o r s P Q X Y hord c restP restQ hP hQ hPL hQL hp hq d
  let D := ofStem P c restP hP A
  let E := ofStem Q c restQ hQ C
  obtain ⟨k, l, A', C', hnew, hlabels, hbP, hbQ, hblueP, hblueQ, hhP, hhQ, hA', _⟩ :=
    JointOpening.respond_bodies hK hKH B o r s D E X Y hstem hcP hcQ d
  let P' := applyBody D A'
  let Q' := applyBody E C'
  let v := A.newWord ++ A'.position.size :: A'.position.entries
  have hPword : P'.position.ordinary = P.position.ordinary ++ v := by
    change A'.position.ordinary = _
    rw [BodyResponses.setup_ordinary]
    change A.stem.ordinary ++ _ = _
    rw [A.ordinary, List.append_assoc]
  have hQword : Q'.position.ordinary = Q.position.ordinary ++ v := by
    change C'.position.ordinary = Q.position.ordinary ++ v
    rw [← hnew, ← hord]
    exact hPword
  refine ⟨P', Q', rfl, rfl, hnew, hlabels,
    Relation.ReflTransGen.head hsP (Relation.ReflTransGen.single hbP),
    Relation.ReflTransGen.head hsQ (Relation.ReflTransGen.single hbQ),
    hblueP, hblueQ, hhP, hhQ, v, hPword, hQword, ?_⟩
  intro x hx
  exact (List.mem_append.mp hx).elim (hA x)
    (fun hx ↦ hA' x (List.mem_append_right _ hx))

end Erdos118.JointMoves
