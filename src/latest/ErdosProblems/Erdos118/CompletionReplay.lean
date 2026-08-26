import ErdosProblems.Erdos118.SecondWhole

/-!
Every literal completion of an interior ordinary word is an exact final
response after restoring the pending state's own annotations. The suffix,
and therefore all its support and bound obligations, remains unchanged.
-/

namespace Erdos118.CompletionReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open AdaptiveGame BlueRuns ReservedResponses

private theorem response_supported_suffix {H : Set ℕ} {S : State} {b : ℕ}
    (R : Response S b) (a : R.family.members) (ha : (↑a.1 : Set ℕ) ⊆ H) :
    ∃ v : List ℕ, (R.result a).ordinary = S.ordinary ++ v ∧ ∀ x ∈ v, x ∈ H := by
  obtain ⟨v, d, hv, hd, _, hvd⟩ := step_extensions (R.step a)
  obtain ⟨e, he, hes⟩ := R.suffix a
  have hde : d = e := List.append_cancel_left (hd.symm.trans he)
  subst e
  exact ⟨v, hv, fun x hx ↦ ha (hes ▸ List.mem_toFinset.mpr (hvd.subset hx))⟩

theorem run_supported_suffixes {H : Set ℕ} {payoff : Completed → Completed → Bool}
    {S T : State × State} (h : ConservativeRuns.Run H payoff S T) :
    ∃ u v : List ℕ, T.1.ordinary = S.1.ordinary ++ u ∧
      T.2.ordinary = S.2.ordinary ++ v ∧
      (∀ x ∈ u, x ∈ H) ∧ (∀ x ∈ v, x ∈ H) := by
  induction h with
  | refl => exact ⟨[], [], by simp, by simp, by simp, by simp⟩
  | tail hprev hstep ih =>
    obtain ⟨u, v, hu, hv, huH, hvH⟩ := ih
    cases hstep with
    | left n R hs hR a haH hlarge =>
      obtain ⟨w, hw, hwH⟩ := response_supported_suffix R a haH
      exact ⟨u ++ w, v, by rw [hw, hu, List.append_assoc], hv,
        fun x hx ↦ (List.mem_append.mp hx).elim (huH x) (hwH x), hvH⟩
    | right n R hs hR a haH hlarge =>
      obtain ⟨w, hw, hwH⟩ := response_supported_suffix R a haH
      exact ⟨u, v ++ w, hu, by rw [hw, hv, List.append_assoc], huH,
        fun x hx ↦ (List.mem_append.mp hx).elim (hvH x) (hwH x)⟩

theorem partial_completion_decompose {p q : G2} {n : ℕ} {u : List ℕ}
    (hpq : p.length < q.length) (hu : u.length < n)
    (h : p.flatMap levelWord ++ n :: u <+: q.flatMap levelWord) :
    ∃ a : List ℕ, ∃ t : G2, q = p ++ (u ++ a) :: t ∧
      (u ++ a).length = n ∧ a ≠ [] := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp at hpq
    | cons v t =>
      have he : n = v.length ∧ u <+: v ++ t.flatMap levelWord := by
        simpa only [List.flatMap_nil, List.nil_append, List.flatMap_cons,
          levelWord, List.cons_append, List.cons_prefix_cons] using h
      have huv : u <+: v := List.prefix_of_prefix_length_le he.2
        (List.prefix_append _ _) (by omega)
      obtain ⟨a, ha⟩ := huv
      refine ⟨a, t, by simp only [List.nil_append, ha], ha ▸ he.1.symm, ?_⟩
      intro hnil
      simp only [hnil, List.append_nil] at ha
      have hlen := congrArg List.length ha
      omega
  | cons v p ih =>
    cases q with
    | nil => simp at hpq
    | cons w q =>
      have h' : levelWord v ++ (p.flatMap levelWord ++ n :: u) <+:
          levelWord w ++ q.flatMap levelWord := by
        simpa only [List.flatMap_cons, List.append_assoc] using h
      obtain ⟨rfl, htail⟩ := WordResponses.levelWord_prefix_cancel h'
      obtain ⟨a, t, hq, hlen, hne⟩ := ih (by simpa using hpq) htail
      exact ⟨a, t, by simp only [hq, List.cons_append], hlen, hne⟩

theorem setup_of_literal_stem (P : Position) (S : Stem) (j : ℕ)
    (hroot : S.root = P.stem.root) (hcount : S.done.length = j)
    (hmore : P.stem.done.length < j) (v : List ℕ)
    (hword : S.ordinary = P.ordinary ++ v) :
    ∃ A : StemResponses.Setup P j, A.newWord = v ∧
      A.stem.ordinary = S.ordinary := by
  have hbody : Body.ordinary = fun a ↦ levelWord a.values := rfl
  have he : S.root = P.stem.root ∧
      (S.done.map Body.values).flatMap levelWord =
        (P.stem.done.map Body.values).flatMap levelWord ++ P.size :: (P.entries ++ v) := by
    simpa only [Position.ordinary, Stem.ordinary, List.cons_append,
      List.append_assoc, List.cons.injEq, List.flatMap_map, hbody] using hword
  have hprefix : (P.stem.done.map Body.values).flatMap levelWord ++ P.size :: P.entries <+:
      (S.done.map Body.values).flatMap levelWord := by
    refine ⟨v, ?_⟩
    simpa only [List.append_assoc, List.cons_append] using he.2.symm
  have hlength : (P.stem.done.map Body.values).length < (S.done.map Body.values).length := by
    simpa only [List.length_map, hcount] using hmore
  obtain ⟨a, t, hparse, halen, hane⟩ :=
    partial_completion_decompose hlength P.unfinished hprefix
  have htail : a ++ t.flatMap levelWord = v := by
    apply List.append_cancel_left (as := P.ordinary)
    calc
      P.ordinary ++ (a ++ t.flatMap levelWord) = S.ordinary := by
        have hS : S.ordinary = S.root :: (S.done.map Body.values).flatMap levelWord := by
          simp only [Stem.ordinary, List.flatMap_map, hbody]
        rw [hS, hroot, hparse]
        simp only [List.flatMap_append, List.flatMap_cons, levelWord, halen,
          Position.ordinary, Stem.ordinary, List.flatMap_map, hbody,
          List.cons_append, List.append_assoc]
      _ = P.ordinary ++ v := hword
  let bodies := P.stem.done ++ { values := P.entries ++ a, label := P.label } ::
    t.map LabelledExtensions.plain
  have hlen : bodies.length = j := by
    have h := congrArg List.length hparse
    simpa only [List.length_append, List.length_cons, List.length_map, hcount,
      bodies] using h.symm
  have hordinary : P.stem.root :: bodies.flatMap Body.ordinary = P.ordinary ++ v := by
    rw [← htail]
    simp only [bodies, List.flatMap_append, List.flatMap_cons, Body.ordinary,
      plain_ordinary, levelWord, halen, Position.ordinary, Stem.ordinary,
      List.cons_append, List.append_assoc]
  have hdecorated : P.stem.rootLabel ++ (P.stem.root :: bodies.flatMap Body.decorated) =
      P.decorated ++ v := by
    rw [← htail]
    simp only [bodies, List.flatMap_append, List.flatMap_cons, Body.decorated,
      Body.ordinary, plain_decorated, levelWord, halen, Position.decorated, Stem.decorated,
      List.cons_append, List.append_assoc]
  have hincOrd : S.ordinary.Pairwise (· < ·) := S.increasing.sublist S.ordinary_sublist
  have hvinc : v.Pairwise (· < ·) :=
    (List.pairwise_append.mp (hword ▸ hincOrd)).2.1
  have hordBefore : ∀ x ∈ P.ordinary, ∀ y ∈ v, x < y :=
    (List.pairwise_append.mp (hword ▸ hincOrd)).2.2
  have hdecBefore : ∀ x ∈ P.decorated, ∀ y ∈ v, x < y := by
    have hinc : ((P.stem.decorated ++ P.label) ++ P.size :: P.entries).Pairwise (· < ·) := by
      simpa only [Position.decorated, List.append_assoc] using P.increasing
    intro x hx y hy
    have hmem : x ∈ (P.stem.decorated ++ P.label) ++ P.size :: P.entries := by
      simpa only [Position.decorated, List.append_assoc] using hx
    rcases List.mem_append.mp hmem with hx | hx
    · exact ((List.pairwise_append.mp hinc).2.2 x hx P.size
        (List.mem_cons_self ..)).trans
        (hordBefore P.size (List.mem_append_right _ (List.mem_cons_self ..)) y hy)
    · exact hordBefore x (List.mem_append_right _ hx) y hy
  let U : Stem :=
    { root := P.stem.root, rootLabel := P.stem.rootLabel, done := bodies
      count := by rw [hlen, ← hcount, ← hroot]; exact S.count
      increasing := hdecorated ▸ List.pairwise_append.mpr ⟨P.increasing, hvinc, hdecBefore⟩ }
  have htlen : t.length = j - (P.stem.done.length + 1) := by
    have h := hlen
    simp only [bodies, List.length_append, List.length_cons, List.length_map] at h
    omega
  let A : StemResponses.Setup P j :=
    { stem := U, newWord := v, root_eq := rfl, rootLabel_eq := rfl, count := hlen
      labels := by
        change bodies.map Body.label = _
        simp only [bodies, List.map_append, List.map_cons, List.map_map,
          Position.bodyLabels, Stem.bodyLabels, List.append_assoc, List.singleton_append]
        change _ ++ (P.label :: t.map (fun _ ↦ [])) = _
        rw [List.map_const', htlen]
      decorated := hdecorated
      ordinary := hordinary
      nonempty := by
        intro hv
        rw [hv] at htail
        exact hane (List.append_eq_nil_iff.mp htail).1 }
  exact ⟨A, rfl, hordinary.trans hword.symm⟩

theorem setup_of_literal_completion (P : Position) (s : G) (v : List ℕ)
    (hword : word s.1 = P.ordinary ++ v) :
    ∃ A : StemResponses.Setup P P.stem.root, A.newWord = v ∧
      A.stem.ordinary = word s.1 := by
  have hroot : s.1.length = P.stem.root := by
    have h := congrArg (fun w : List ℕ ↦ w.headD 0) hword
    simpa only [word, Position.ordinary, Stem.ordinary, List.cons_append, List.headD_cons] using h
  have hcount : (ofGood s).stem.done.length = P.stem.root := by
    simpa only [ofGood, List.length_map] using hroot
  have hmore : P.stem.done.length < P.stem.root := by have h := P.room; omega
  obtain ⟨A, hv, hA⟩ := setup_of_literal_stem P (ofGood s).stem P.stem.root hroot hcount hmore v
    ((ofGood_ordinary s).trans hword)
  exact ⟨A, hv, hA.trans (ofGood_ordinary s)⟩

theorem left_finish_words {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (P : Pending) (T : State) (hR : P.roots = []) (hL : P.leaves = [])
    (hblue : LeftBlue H payoff (.leaf P, T)) :
    ∃ b : ℕ, ∀ s : G, ∀ v : List ℕ, word s.1 = P.position.ordinary ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
      ∃ C : Completed, GraphPayoff.vertex C = s ∧
        RamseyGame.Outcome H (AdaptiveGame.game payoff (.complete C, T)) true := by
  obtain ⟨n, R, _, hresp, b, hb⟩ := hblue
  let c := pairBound (.leaf P, T)
  have he : R = finishResponse P hR hL c :=
    Option.some.inj (hresp.symm.trans (SecondWhole.finish_selector P hR hL c n))
  subst R
  refine ⟨max b c, ?_⟩
  intro s v hs hvH hvb
  obtain ⟨A, hAv, hAs⟩ := setup_of_literal_completion P.position s v hs
  have hAc : ∀ x ∈ A.newWord, c < x := by
    rw [hAv]
    exact fun x hx ↦ (le_max_right _ _).trans_lt (hvb x hx)
  let a := finishMember P hR hL c A hAc
  have haH : (↑a.1 : Set ℕ) ⊆ H := by
    intro x hx
    exact hvH x (hAv ▸ List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hvb x (hAv ▸ List.mem_toFinset.mp hx))
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (AdaptiveGame.game payoff
    ((finishResponse P hR hL c).result (finishMember P hR hL c A hAc), T)) true at hnext
  rw [finishMember_result] at hnext
  refine ⟨ofCompletion P A, ?_, hnext⟩
  have he := GraphPayoff.vertex_eq_of_ordinary_eq
    (S := ofCompletion P A) (T := ofGood s) (hAs.trans (ofGood_ordinary s).symm)
  simpa only [WholeBlue.plain_vertex] using he

theorem right_finish_words {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (S : State) (P : Pending) (hR : P.roots = []) (hL : P.leaves = [])
    (hblue : RightBlue H payoff (S, .leaf P)) :
    ∃ b : ℕ, ∀ s : G, ∀ v : List ℕ, word s.1 = P.position.ordinary ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
      ∃ C : Completed, GraphPayoff.vertex C = s ∧
        RamseyGame.Outcome H (AdaptiveGame.game payoff (S, .complete C)) true := by
  obtain ⟨n, R, _, hresp, b, hb⟩ := hblue
  let c := pairBound (S, .leaf P)
  have he : R = finishResponse P hR hL c :=
    Option.some.inj (hresp.symm.trans (SecondWhole.finish_selector P hR hL c n))
  subst R
  refine ⟨max b c, ?_⟩
  intro s v hs hvH hvb
  obtain ⟨A, hAv, hAs⟩ := setup_of_literal_completion P.position s v hs
  have hAc : ∀ x ∈ A.newWord, c < x := by
    rw [hAv]
    exact fun x hx ↦ (le_max_right _ _).trans_lt (hvb x hx)
  let a := finishMember P hR hL c A hAc
  have haH : (↑a.1 : Set ℕ) ⊆ H := by
    intro x hx
    exact hvH x (hAv ▸ List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hvb x (hAv ▸ List.mem_toFinset.mp hx))
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (AdaptiveGame.game payoff
    (S, (finishResponse P hR hL c).result (finishMember P hR hL c A hAc))) true at hnext
  rw [finishMember_result] at hnext
  refine ⟨ofCompletion P A, ?_, hnext⟩
  have he := GraphPayoff.vertex_eq_of_ordinary_eq
    (S := ofCompletion P A) (T := ofGood s) (hAs.trans (ofGood_ordinary s).symm)
  simpa only [WholeBlue.plain_vertex] using he

theorem completion_edges_of_word {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (P : Pending) (T : Completed)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, .complete T)) true) :
    ∃ b : ℕ, ∀ s : G, ∀ v : List ℕ, word s.1 = P.position.ordinary ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) → B.Adj s (GraphPayoff.vertex T) := by
  obtain ⟨b, hb⟩ := SecondWhole.completion_edges hH B o P T hblue
  refine ⟨b, ?_⟩
  intro s v hs hH hbv
  obtain ⟨A, hAv, hAs⟩ := setup_of_literal_completion P.position s v hs
  have hadj := hb A (hAv ▸ hH) (hAv ▸ hbv)
  have he : GraphPayoff.vertex (ofCompletion P A) = s := by
    apply Subtype.ext
    apply WordResponses.word_prefix_rigid
    have hw : word (GraphPayoff.vertex (ofCompletion P A)).1 = word s.1 := by
      rw [GraphPayoff.vertex, Stem.toGood_word]
      exact hAs
    exact hw ▸ List.prefix_rfl
  rwa [he] at hadj

theorem right_completion_edges_of_word {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (S : Completed) (P : Pending)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.complete S, .leaf P)) true) :
    ∃ b : ℕ, ∀ t : G, ∀ v : List ℕ, word t.1 = P.position.ordinary ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) → B.Adj (GraphPayoff.vertex S) t := by
  obtain ⟨hR, hL⟩ := EndpointOrder.complete_leaf_slots_empty hH B o S P hblue
  rcases blue_command (GraphPayoff.payoff B o) (.complete S, .leaf P) rfl hblue with hl | hr
  · exact (not_leftBlue_complete H (GraphPayoff.payoff B o) S (.leaf P) hl).elim
  · obtain ⟨b, hb⟩ := right_finish_words (GraphPayoff.payoff B o) (.complete S) P hR hL hr
    refine ⟨b, ?_⟩
    intro t v ht hvH hvb
    obtain ⟨T, hT, hnext⟩ := hb t v ht hvH hvb
    rw [AdaptiveGame.game_complete] at hnext
    have hadj := ((GraphPayoff.payoff_true_iff B o S T).mp
      (RamseyGame.outcome_leaf_iff.mp hnext)).2.2.2
    rwa [hT] at hadj

end Erdos118.CompletionReplay
