import ErdosProblems.Erdos118.CompletionReplay

/-!
Exact blue replay to a later body decision. The target stem may carry
different decorations; the actual response restores the original labels
and preserves the entire ordinary suffix and its original blue bound.
-/

namespace Erdos118.StemReplay

open LabelledExtensions LabelledFrames DecisionStates AdaptiveGame BlueRuns

theorem selector (P : Pending) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hL : P.leaves = []) (b n : ℕ) :
    responseFor (.leaf P) b n = some (nextBodyResponse P c rest hR hL b) := by
  dsimp only [responseFor]
  split
  · rename_i j tail he
    have hbad := he.symm.trans hL
    cases hbad
  · split
    · rename_i j tail he
      obtain ⟨rfl, rfl⟩ := List.cons.inj (he.symm.trans hR)
      rfl
    · rename_i he
      have hbad := he.symm.trans hR
      cases hbad

noncomputable def member (P : Pending) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hL : P.leaves = []) (b : ℕ)
    (A : StemResponses.Setup P.position (c - 1)) (h : ∀ x ∈ A.newWord, b < x) :
    (nextBodyResponse P c rest hR hL b).family.members :=
  ⟨(StemResponses.supportEquiv P.position (c - 1) A).1,
    (StemResponses.supportEquiv P.position (c - 1) A).2,
    fun x hx ↦ h x (List.mem_toFinset.mp hx)⟩

theorem member_result (P : Pending) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hL : P.leaves = []) (b : ℕ)
    (A : StemResponses.Setup P.position (c - 1)) (h : ∀ x ∈ A.newWord, b < x) :
    (nextBodyResponse P c rest hR hL b).result (member P c rest hR hL b A h) =
      .body (ofStem P c rest hR A) := by
  change State.body (ofStem P c rest hR
    ((StemResponses.supportEquiv P.position (c - 1)).symm
      ((StemResponses.supportEquiv P.position (c - 1)) A))) = _
  rw [Equiv.symm_apply_apply]

theorem left_body_words {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (P : Pending) (T : State) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hL : P.leaves = [])
    (hblue : LeftBlue H payoff (.leaf P, T)) :
    ∃ b : ℕ, ∀ Q : Stem, ∀ v : List ℕ,
      Q.root = P.position.stem.root → Q.done.length = c - 1 →
      Q.ordinary = P.position.ordinary ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
      ∃ A : StemResponses.Setup P.position (c - 1), A.newWord = v ∧
        A.stem.ordinary = Q.ordinary ∧
        RamseyGame.Outcome H (AdaptiveGame.game payoff (.body (ofStem P c rest hR A), T)) true := by
  obtain ⟨n, R, _, hresp, b, hb⟩ := hblue
  let d := pairBound (.leaf P, T)
  have he : R = nextBodyResponse P c rest hR hL d :=
    Option.some.inj (hresp.symm.trans (selector P c rest hR hL d n))
  subst R
  refine ⟨max b d, ?_⟩
  intro Q v hroot hcount hword hvH hvb
  obtain ⟨A, hAv, hAQ⟩ := CompletionReplay.setup_of_literal_stem P.position Q (c - 1)
    hroot hcount (next_body_bounds P c rest hR).1 v hword
  have hAd : ∀ x ∈ A.newWord, d < x := by
    rw [hAv]
    exact fun x hx ↦ (le_max_right _ _).trans_lt (hvb x hx)
  let a := member P c rest hR hL d A hAd
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hvH x (hAv ▸ List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hvb x (hAv ▸ List.mem_toFinset.mp hx))
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (AdaptiveGame.game payoff
    ((nextBodyResponse P c rest hR hL d).result (member P c rest hR hL d A hAd), T)) true at hnext
  rw [member_result] at hnext
  exact ⟨A, hAv, hAQ, hnext⟩

theorem left_body_words_step {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (P : Pending) (T : State) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hL : P.leaves = [])
    (hblue : LeftBlue H payoff (.leaf P, T)) :
    ∃ b : ℕ, ∀ Q : Stem, ∀ v : List ℕ,
      Q.root = P.position.stem.root → Q.done.length = c - 1 →
      Q.ordinary = P.position.ordinary ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
      ∃ A : StemResponses.Setup P.position (c - 1), A.newWord = v ∧
        A.stem.ordinary = Q.ordinary ∧
        ConservativeRuns.Step H payoff (.leaf P, T) (.body (ofStem P c rest hR A), T) ∧
        RamseyGame.Outcome H (AdaptiveGame.game payoff (.body (ofStem P c rest hR A), T)) true := by
  obtain ⟨b, hb⟩ := left_body_words payoff P T c rest hR hL hblue
  obtain ⟨n, _, hside, _⟩ := hblue
  let d := pairBound (.leaf P, T)
  let g := ConservativeRuns.leftGuard H payoff (.leaf P, T) n
  refine ⟨max b (max d g), ?_⟩
  intro Q v hr hc hv hvH hvb
  obtain ⟨A, hAv, hAQ, hnext⟩ := hb Q v hr hc hv hvH
    (fun x hx ↦ (le_max_left _ _).trans_lt (hvb x hx))
  have hAd : ∀ x ∈ A.newWord, d < x := by
    rw [hAv]
    exact fun x hx ↦ ((le_max_left d g).trans (le_max_right b _)).trans_lt (hvb x hx)
  let a := member P c rest hR hL d A hAd
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hvH x (hAv ▸ List.mem_toFinset.mp hx)
  have hag : ∀ x ∈ a.1, g < x := fun x hx ↦
    ((le_max_right d g).trans (le_max_right b _)).trans_lt
      (hvb x (hAv ▸ List.mem_toFinset.mp hx))
  have hs := ConservativeRuns.Step.left (.leaf P, T) n
    (nextBodyResponse P c rest hR hL d) hside (selector P c rest hR hL d n) a haH hag
  rw [member_result] at hs
  exact ⟨A, hAv, hAQ, hs, hnext⟩

theorem right_body_words_step {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (T : State) (P : Pending) (c : ℕ) (rest : List ℕ)
    (hR : P.roots = c :: rest) (hL : P.leaves = [])
    (hblue : RightBlue H payoff (T, .leaf P)) :
    ∃ b : ℕ, ∀ Q : Stem, ∀ v : List ℕ,
      Q.root = P.position.stem.root → Q.done.length = c - 1 →
      Q.ordinary = P.position.ordinary ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
      ∃ A : StemResponses.Setup P.position (c - 1), A.newWord = v ∧
        A.stem.ordinary = Q.ordinary ∧
        ConservativeRuns.Step H payoff (T, .leaf P) (T, .body (ofStem P c rest hR A)) ∧
        RamseyGame.Outcome H (AdaptiveGame.game payoff (T, .body (ofStem P c rest hR A))) true := by
  obtain ⟨n, R, hside, hresp, b, hb⟩ := hblue
  let d := pairBound (T, .leaf P)
  let g := ConservativeRuns.rightGuard H payoff (T, .leaf P) n
  have he : R = nextBodyResponse P c rest hR hL d :=
    Option.some.inj (hresp.symm.trans (selector P c rest hR hL d n))
  subst R
  refine ⟨max b (max d g), ?_⟩
  intro Q v hr hc hv hvH hvb
  obtain ⟨A, hAv, hAQ⟩ := CompletionReplay.setup_of_literal_stem P.position Q (c - 1)
    hr hc (next_body_bounds P c rest hR).1 v hv
  have hAd : ∀ x ∈ A.newWord, d < x := by
    rw [hAv]
    exact fun x hx ↦ ((le_max_left d g).trans (le_max_right b _)).trans_lt (hvb x hx)
  let a := member P c rest hR hL d A hAd
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hvH x (hAv ▸ List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hvb x (hAv ▸ List.mem_toFinset.mp hx))
  have hag : ∀ x ∈ a.1, g < x := fun x hx ↦
    ((le_max_right d g).trans (le_max_right b _)).trans_lt
      (hvb x (hAv ▸ List.mem_toFinset.mp hx))
  have hs := ConservativeRuns.Step.right (T, .leaf P) n
    (nextBodyResponse P c rest hR hL d) hside (selector P c rest hR hL d n) a haH hag
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (AdaptiveGame.game payoff
    (T, (nextBodyResponse P c rest hR hL d).result (member P c rest hR hL d A hAd))) true
    at hnext
  rw [member_result] at hs hnext
  exact ⟨A, hAv, hAQ, hs, hnext⟩

end Erdos118.StemReplay
