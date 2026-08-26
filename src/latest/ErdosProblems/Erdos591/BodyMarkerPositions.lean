import ErdosProblems.Erdos591.WordPositions

/-! # Literal body-marker positions and the suffix they begin -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

def bodyMarkerPosition (s : List (List ℕ)) (i : ℕ) : ℕ :=
  1 + ((s.take i).flatMap levelWord).length

theorem bodyMarkerPosition_mono (s : List (List ℕ)) {i k : ℕ} (hik : i ≤ k) :
    bodyMarkerPosition s i ≤ bodyMarkerPosition s k :=
  Nat.add_le_add_left ((List.take_prefix_take_left (l := s) hik).flatMap levelWord).length_le 1

theorem leafPosition_eq_bodyMarkerPosition (s : List (List ℕ)) (i j : ℕ) :
    leafPosition s i j = bodyMarkerPosition s i + 1 + j := by
  simp only [leafPosition, bodyMarkerPosition, List.length_flatMap, levelWord_length]
  omega

theorem bodyMarkerPosition_succ (s : List (List ℕ)) {i : ℕ} (hi : i < s.length) :
    bodyMarkerPosition s (i + 1) = bodyMarkerPosition s i + (s.getD i []).length + 1 := by
  simp only [bodyMarkerPosition, List.take_succ_eq_append_getElem hi, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    levelWord_length, List.getD_eq_getElem _ _ hi]
  omega

theorem leafPosition_lt_later_marker (s : List (List ℕ)) {i j k : ℕ}
    (hi : i < s.length) (hj : j < (s.getD i []).length) (hik : i < k) :
    leafPosition s i j < bodyMarkerPosition s k := by
  have hmono := bodyMarkerPosition_mono s (Nat.succ_le_of_lt hik)
  rw [bodyMarkerPosition_succ s hi] at hmono
  rw [leafPosition_eq_bodyMarkerPosition]
  omega

theorem marker_le_leafPosition_iff (s : List (List ℕ)) {i j k : ℕ}
    (hi : i < s.length) (hj : j < (s.getD i []).length) :
    bodyMarkerPosition s k ≤ leafPosition s i j ↔ k ≤ i := by
  constructor
  · intro hle
    by_contra hn
    exact (not_lt_of_ge hle) (leafPosition_lt_later_marker s hi hj (lt_of_not_ge hn))
  · intro hki
    have hmono := bodyMarkerPosition_mono s hki
    rw [leafPosition_eq_bodyMarkerPosition]
    omega

theorem leafPosition_lt_of_body_lt (s : List (List ℕ)) {i j k l : ℕ}
    (hi : i < s.length) (hj : j < (s.getD i []).length) (hik : i < k) :
    leafPosition s i j < leafPosition s k l := by
  have hlt := leafPosition_lt_later_marker s hi hj hik
  rw [leafPosition_eq_bodyMarkerPosition s k l]
  omega

theorem leafPosition_le_iff (s : List (List ℕ)) {i j k l : ℕ}
    (hi : i < s.length) (hj : j < (s.getD i []).length)
    (hk : k < s.length) (hl : l < (s.getD k []).length) :
    leafPosition s i j ≤ leafPosition s k l ↔ i < k ∨ i = k ∧ j ≤ l := by
  constructor
  · intro hle
    by_cases hik : i < k
    · exact Or.inl hik
    · have hnot : ¬ k < i := fun hki =>
        (not_lt_of_ge hle) (leafPosition_lt_of_body_lt s hk hl hki)
      have heq : i = k := by omega
      refine Or.inr ⟨heq, ?_⟩
      rw [heq, leafPosition_eq_bodyMarkerPosition, leafPosition_eq_bodyMarkerPosition] at hle
      omega
  · rintro (hik | ⟨rfl, hjl⟩)
    · exact (leafPosition_lt_of_body_lt s hi hj hik).le
    · rw [leafPosition_eq_bodyMarkerPosition, leafPosition_eq_bodyMarkerPosition]
      omega

theorem word_body_split (s : List (List ℕ)) {i : ℕ} (hi : i < s.length) :
    word s = (s.length :: (s.take i).flatMap levelWord) ++
      (levelWord (s.getD i []) ++ (s.drop (i + 1)).flatMap levelWord) := by
  have hshape : s = s.take i ++ s.getD i [] :: s.drop (i + 1) := by
    rw [List.getD_eq_getElem _ _ hi, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hflat := congrArg (fun l : List (List ℕ) => l.flatMap levelWord) hshape
  simp only [List.flatMap_append, List.flatMap_cons] at hflat
  rw [word, hflat]
  rfl

theorem drop_bodyMarkerPosition (s : List (List ℕ)) {i : ℕ} (hi : i < s.length) :
    (word s).drop (bodyMarkerPosition s i) =
      levelWord (s.getD i []) ++ (s.drop (i + 1)).flatMap levelWord := by
  have hlen : (s.length :: (s.take i).flatMap levelWord).length = bodyMarkerPosition s i := by
    simp [bodyMarkerPosition, Nat.add_comm]
  rw [word_body_split s hi, ← hlen, List.drop_left]

theorem bodyMarkerPosition_lt_length (s : List (List ℕ)) {i : ℕ} (hi : i < s.length) :
    bodyMarkerPosition s i < (word s).length := by
  have hdrop := drop_bodyMarkerPosition s hi
  have hlen := congrArg List.length hdrop
  simp only [List.length_drop, List.length_append, levelWord_length] at hlen
  omega

theorem head_drop_bodyMarkerPosition (s : List (List ℕ)) {i : ℕ} (hi : i < s.length) :
    ((word s).drop (bodyMarkerPosition s i)).headD 0 = (s.getD i []).length := by
  rw [drop_bodyMarkerPosition s hi]
  rfl

#print axioms marker_le_leafPosition_iff
#print axioms leafPosition_le_iff
#print axioms drop_bodyMarkerPosition

end Erdos591.Positive.Game.Payoff
