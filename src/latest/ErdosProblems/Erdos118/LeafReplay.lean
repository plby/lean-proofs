import ErdosProblems.Erdos118.CompletionReplay

/-!
Exact replay at a selected leaf, retaining the old annotations. A second
construction may supply the ordinary extension, but its entire new suffix
must exceed the bound announced by the original blue command.
-/

namespace Erdos118.LeafReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

private theorem restore_increasing (P : Position) (v : List ℕ)
    (h : (P.ordinary ++ v).Pairwise (· < ·)) : (P.decorated ++ v).Pairwise (· < ·) := by
  have hv := (List.pairwise_append.mp h).2.1
  have hbefore := (List.pairwise_append.mp h).2.2
  apply List.pairwise_append.mpr
  refine ⟨P.increasing, hv, ?_⟩
  intro x hx y hy
  have hinc : ((P.stem.decorated ++ P.label) ++ P.size :: P.entries).Pairwise (· < ·) := by
    simpa only [Position.decorated, List.append_assoc] using P.increasing
  have hmem : x ∈ (P.stem.decorated ++ P.label) ++ P.size :: P.entries := by
    simpa only [Position.decorated, List.append_assoc] using hx
  rcases List.mem_append.mp hmem with hx | hx
  · exact ((List.pairwise_append.mp hinc).2.2 x hx P.size (List.mem_cons_self ..)).trans
      (hbefore P.size (List.mem_append_right _ (List.mem_cons_self ..)) y hy)
  · exact hbefore x (List.mem_append_right _ hx) y hy

theorem setup_of_position (P Q : Position) (j : ℕ)
    (hstem : Q.stem.ordinary = P.stem.ordinary) (hsize : Q.size = P.size)
    (hlen : Q.entries.length = j) (v : List ℕ) (hentries : Q.entries = P.entries ++ v) :
    ∃ A : LeafResponses.Setup P j, A.newWord = v ∧ P.ordinary ++ A.newWord = Q.ordinary := by
  have hord : Q.ordinary = P.ordinary ++ v := by
    simp only [Position.ordinary, hstem, hsize, hentries, List.cons_append, List.append_assoc]
  have hlenv : v.length = j - P.entries.length := by
    have h := congrArg List.length hentries
    rw [hlen, List.length_append] at h
    omega
  let A : LeafResponses.Setup P j :=
    { newWord := v, length_eq := hlenv
      increasing := restore_increasing P v
        (hord ▸ Q.increasing.sublist Q.ordinary_sublist) }
  exact ⟨A, rfl, hord.symm⟩

theorem selector (P : Pending) (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (b n : ℕ) : responseFor (.leaf P) b n = some (leafResponse P j rest hP b) := by
  dsimp only [responseFor]
  split
  · rename_i k tail he
    obtain ⟨rfl, rfl⟩ := List.cons.inj (he.symm.trans hP)
    rfl
  · rename_i he
    have hbad : ([] : List ℕ) = j :: rest := he.symm.trans hP
    cases hbad

noncomputable def member (P : Pending) (j : ℕ) (rest : List ℕ)
    (hP : P.leaves = j :: rest) (b : ℕ) (A : LeafResponses.Setup P.position j)
    (h : ∀ x ∈ A.newWord, b < x) : (leafResponse P j rest hP b).family.members :=
  ⟨(LeafResponses.supportEquiv P.position j A).1,
    (LeafResponses.supportEquiv P.position j A).2,
    fun x hx ↦ h x (List.mem_toFinset.mp hx)⟩

theorem member_result (P : Pending) (j : ℕ) (rest : List ℕ)
    (hP : P.leaves = j :: rest) (b : ℕ) (A : LeafResponses.Setup P.position j)
    (h : ∀ x ∈ A.newWord, b < x) :
    (leafResponse P j rest hP b).result (member P j rest hP b A h) =
      .leaf (LeafResponses.toPending P j rest hP A) := by
  change State.leaf (LeafResponses.toPending P j rest hP
    ((LeafResponses.supportEquiv P.position j).symm
      ((LeafResponses.supportEquiv P.position j) A))) = _
  rw [Equiv.symm_apply_apply]

theorem left_leaf_words_slots {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (P : Pending) (T : State) (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (hblue : LeftBlue H payoff (.leaf P, T)) :
    ∃ b : ℕ, ∀ Q : Position, ∀ v : List ℕ,
      Q.stem.ordinary = P.position.stem.ordinary → Q.size = P.position.size →
      Q.entries.length = j → Q.entries = P.position.entries ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
      ∃ U : Pending, U.roots = P.roots ∧ U.leaves = rest ∧ U.position.ordinary = Q.ordinary ∧
        RamseyGame.Outcome H (AdaptiveGame.game payoff (.leaf U, T)) true := by
  obtain ⟨n, R, _, hresp, b, hb⟩ := hblue
  let c := pairBound (.leaf P, T)
  have he : R = leafResponse P j rest hP c :=
    Option.some.inj (hresp.symm.trans (selector P j rest hP c n))
  subst R
  refine ⟨max b c, ?_⟩
  intro Q v hstem hsize hlen hentries hvH hvb
  obtain ⟨A, hAv, hAQ⟩ := setup_of_position P.position Q j hstem hsize hlen v hentries
  have hAc : ∀ x ∈ A.newWord, c < x := by
    rw [hAv]
    exact fun x hx ↦ (le_max_right _ _).trans_lt (hvb x hx)
  let a := member P j rest hP c A hAc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hvH x (hAv ▸ List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hvb x (hAv ▸ List.mem_toFinset.mp hx))
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (AdaptiveGame.game payoff
    ((leafResponse P j rest hP c).result (member P j rest hP c A hAc), T)) true at hnext
  rw [member_result] at hnext
  refine ⟨LeafResponses.toPending P j rest hP A, rfl, rfl, ?_, hnext⟩
  have hslot := P.leafSlots.bounded j (hP ▸ List.mem_cons_self ..)
  change (LeafResponses.position A hslot.1 hslot.2.1).ordinary = Q.ordinary
  rw [LeafResponses.position_ordinary]
  exact hAQ

theorem left_leaf_words {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (P : Pending) (T : State) (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (hblue : LeftBlue H payoff (.leaf P, T)) :
    ∃ b : ℕ, ∀ Q : Position, ∀ v : List ℕ,
      Q.stem.ordinary = P.position.stem.ordinary → Q.size = P.position.size →
      Q.entries.length = j → Q.entries = P.position.entries ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
      ∃ U : Pending, U.position.ordinary = Q.ordinary ∧
        RamseyGame.Outcome H (AdaptiveGame.game payoff (.leaf U, T)) true := by
  obtain ⟨b, hb⟩ := left_leaf_words_slots payoff P T j rest hP hblue
  refine ⟨b, ?_⟩
  intro Q v hstem hsize hlen hentries hvH hvb
  obtain ⟨U, _, _, hord, hnext⟩ := hb Q v hstem hsize hlen hentries hvH hvb
  exact ⟨U, hord, hnext⟩

theorem right_leaf_words {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (S : State) (P : Pending) (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (hblue : RightBlue H payoff (S, .leaf P)) :
    ∃ b : ℕ, ∀ Q : Position, ∀ v : List ℕ,
      Q.stem.ordinary = P.position.stem.ordinary → Q.size = P.position.size →
      Q.entries.length = j → Q.entries = P.position.entries ++ v →
      (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
      ∃ U : Pending, U.position.ordinary = Q.ordinary ∧
        RamseyGame.Outcome H (AdaptiveGame.game payoff (S, .leaf U)) true := by
  obtain ⟨n, R, _, hresp, b, hb⟩ := hblue
  let c := pairBound (S, .leaf P)
  have he : R = leafResponse P j rest hP c :=
    Option.some.inj (hresp.symm.trans (selector P j rest hP c n))
  subst R
  refine ⟨max b c, ?_⟩
  intro Q v hstem hsize hlen hentries hvH hvb
  obtain ⟨A, hAv, hAQ⟩ := setup_of_position P.position Q j hstem hsize hlen v hentries
  have hAc : ∀ x ∈ A.newWord, c < x := by
    rw [hAv]
    exact fun x hx ↦ (le_max_right _ _).trans_lt (hvb x hx)
  let a := member P j rest hP c A hAc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hvH x (hAv ▸ List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hvb x (hAv ▸ List.mem_toFinset.mp hx))
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (AdaptiveGame.game payoff
    (S, (leafResponse P j rest hP c).result (member P j rest hP c A hAc))) true at hnext
  rw [member_result] at hnext
  refine ⟨LeafResponses.toPending P j rest hP A, ?_, hnext⟩
  have hslot := P.leafSlots.bounded j (hP ▸ List.mem_cons_self ..)
  change (LeafResponses.position A hslot.1 hslot.2.1).ordinary = Q.ordinary
  rw [LeafResponses.position_ordinary]
  exact hAQ

end Erdos118.LeafReplay
