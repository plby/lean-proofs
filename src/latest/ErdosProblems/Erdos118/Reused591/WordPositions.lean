import ErdosProblems.Erdos118.Reused591.BodyMetadata

namespace Erdos118.Reused591

/-!
# Coordinate positions in a literal height-two word

The position of a coordinate determines a body and an offset inside its
self-delimiting level word. Empty-label prefix execution recovers the
same structural counters as any fine-labeled execution of that prefix.
-/

namespace Erdos591.Positive.Game.LabeledCode

open Erdos591.Negative.Exact

theorem flatMap_position (s : List (List ℕ)) (k : ℕ) (hk : k < (s.flatMap levelWord).length) :
    ∃ pre a rest q, s = pre ++ a :: rest ∧ q ≤ a.length ∧
      k = (pre.flatMap levelWord).length + q := by
  induction s generalizing k with
  | nil => simp at hk
  | cons a s ih =>
      by_cases ha : k < a.length + 1
      · exact ⟨[], a, s, k, rfl, by omega, by simp⟩
      · have hk' : k - (a.length + 1) < (s.flatMap levelWord).length := by
          simp only [List.flatMap_cons, List.length_append, levelWord_length] at hk
          omega
        obtain ⟨pre, c, rest, q, hs, hq, heq⟩ := ih _ hk'
        refine ⟨a :: pre, c, rest, q, by simp [hs], hq, ?_⟩
        simp only [List.flatMap_cons, List.length_append, levelWord_length]
        omega

def plainLeafPrefix (pre : List (List ℕ)) (us vs : List ℕ) (rest : List (List ℕ)) :
    LabeledWord :=
  leafPrefixCursor ∅ (pre.map fun a => (∅, a)) ∅ us vs (rest.map fun a => (∅, a))

theorem plainLeafPrefix_run (pre : List (List ℕ)) (us vs : List ℕ)
    (rest : List (List ℕ)) :
    LabeledWord.initial.runAtoms ((plainLeafPrefix pre us vs rest).coordinates.map
      fun n => (∅, n)) = some (plainLeafPrefix pre us vs rest) := by
  have h := run_leafPrefix ∅ (pre.map fun a => (∅, a)) ∅ us vs (rest.map fun a => (∅, a))
  simpa [plainLeafPrefix, leafPrefixAtoms, leafPrefixCursor, unlabeled_bodies,
    erase, List.map_append, Function.comp_def] using h

theorem plainLeafPrefix_prefix (pre : List (List ℕ)) (us vs : List ℕ)
    (rest : List (List ℕ)) :
    List.IsPrefix (plainLeafPrefix pre us vs rest).coordinates
      (word (pre ++ (us ++ vs) :: rest)) := by
  refine ⟨vs ++ rest.flatMap levelWord, ?_⟩
  simp [plainLeafPrefix, leafPrefixCursor, word, levelWord, erase, List.append_assoc,
    Nat.add_comm, Nat.add_left_comm, Function.comp_def]

theorem plainLeafPrefix_length (pre : List (List ℕ)) (us vs : List ℕ)
    (rest : List (List ℕ)) :
    (plainLeafPrefix pre us vs rest).coordinates.length =
      2 + (pre.flatMap levelWord).length + us.length := by
  simp [plainLeafPrefix, leafPrefixCursor, erase, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, Function.comp_def]

theorem plainLeafPrefix_take (pre : List (List ℕ)) (us vs : List ℕ)
    (rest : List (List ℕ)) :
    (word (pre ++ (us ++ vs) :: rest)).take
      (plainLeafPrefix pre us vs rest).coordinates.length =
        (plainLeafPrefix pre us vs rest).coordinates :=
  (List.prefix_iff_eq_take.mp (plainLeafPrefix_prefix pre us vs rest)).symm

/-- A relaxed execution of an actual coordinate prefix ends at a
genuine leaf. Its stored successor indices and literal markers agree
with the complete word's decoded body and leaf positions. -/
theorem relaxed_prefix_indices {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (h : LabeledWord.LegalRun LabeledWord.initial xs v) (s : List (List ℕ)) (k : ℕ)
    (hv : v.coordinates = (word s).take (k + 1)) (hk : k < (word s).length)
    (hr : v.relaxed = true) :
    ∃ i j, i < s.length ∧ j < (s.getD i []).length ∧
      v.bodyLabels.length = i + 1 ∧ v.leafIndex = j + 1 ∧
      v.rootMarker = s.length ∧ v.bodyMarker = (s.getD i []).length ∧
      k = Payoff.leafPosition s i j := by
  have hvalues : xs.map Prod.snd = (word s).take (k + 1) := by
    simpa [LabeledWord.initial] using (LabeledWord.runAtoms_coordinates h.run).symm.trans hv
  have hrel : 0 < v.leafIndex ∧ v.bodyLabels.length ∈ v.rootLabel ∧
      v.leafIndex ∈ v.currentLabel := by simpa [LabeledWord.relaxed] using hr
  by_cases hk0 : k = 0
  · have hz : LabeledWord.Coarsens (rootCursor ∅ s.length) v :=
      (LabeledWord.Coarsens.refl LabeledWord.initial).compare_erased h.run
        (by simp [hvalues, hk0, word, LabeledWord.runAtoms, read_root])
    have hz' : v.leafIndex = 0 := hz.leaf_eq.symm
    omega
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hk' : k - 1 < (s.flatMap levelWord).length := by
      simp only [word, List.length_cons] at hk
      omega
    obtain ⟨pre, a, rest, q, hsplit, hq, hindex⟩ := flatMap_position s (k - 1) hk'
    let us := a.take q
    let vs := a.drop q
    let w := plainLeafPrefix pre us vs rest
    have hshape : s = pre ++ (us ++ vs) :: rest := by
      simpa [us, vs] using hsplit
    have hlen : w.coordinates.length = k + 1 := by
      rw [plainLeafPrefix_length]
      have hu : us.length = q := by simp [us, Nat.min_eq_left hq]
      omega
    have hwcoords : (word s).take (k + 1) = w.coordinates := by
      rw [hshape, ← hlen]
      exact plainLeafPrefix_take pre us vs rest
    have hwrun : LabeledWord.initial.runAtoms (((word s).take (k + 1)).map
        fun n => (∅, n)) = some w := by
      rw [hwcoords]
      exact plainLeafPrefix_run pre us vs rest
    have hz : LabeledWord.Coarsens w v :=
      (LabeledWord.Coarsens.refl LabeledWord.initial).compare_erased h.run
        (by rw [hvalues]; exact hwrun)
    have hI : v.bodyLabels.length = pre.length + 1 := by
      simpa [w, plainLeafPrefix, leafPrefixCursor] using hz.body_length.symm
    have hJ : v.leafIndex = us.length := hz.leaf_eq.symm
    have hu : 0 < us.length := by omega
    have hR : v.rootMarker = s.length := by
      rw [hshape]
      simpa [w, plainLeafPrefix, leafPrefixCursor, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        hz.rootMarker_eq.symm
    have hB : v.bodyMarker = (us ++ vs).length := hz.bodyMarker_eq.symm
    have hget : s.getD pre.length [] = us ++ vs := by
      rw [hshape, List.getD_append_right _ _ _ _ le_rfl]
      simp
    have hi : pre.length < s.length := by rw [hshape]; simp
    have hj : us.length - 1 < (s.getD pre.length []).length := by
      rw [hget, List.length_append]
      omega
    have hpos : w.coordinates.length =
        Payoff.leafPosition s pre.length (us.length - 1) + 1 := by
      rw [hshape]
      simpa [w, plainLeafPrefix, erase, Function.comp_def] using
        leafPrefix_length ∅ (pre.map fun a => (∅, a)) ∅ us vs
          (rest.map fun a => (∅, a)) hu
    exact ⟨pre.length, us.length - 1, hi, hj, hI, by omega, hR,
      by rw [hget]; exact hB, by omega⟩

/-- Conversely, execution through any specified leaf recovers its
successor indices. This also proves uniqueness of the positional code. -/
theorem leaf_prefix_counters (s : List (List ℕ)) (i j : ℕ)
    (hi : i < s.length) (hj : j < (s.getD i []).length) :
    ∃ z, LabeledWord.initial.runAtoms
      (((word s).take (Payoff.leafPosition s i j + 1)).map fun n => (∅, n)) = some z ∧
        z.bodyLabels.length = i + 1 ∧ z.leafIndex = j + 1 := by
  let pre := s.take i
  let a := s.getD i []
  let rest := s.drop (i + 1)
  let us := a.take (j + 1)
  let vs := a.drop (j + 1)
  let z := plainLeafPrefix pre us vs rest
  have hpre : pre.length = i := by simp [pre, Nat.min_eq_left hi.le]
  have hu : us.length = j + 1 := by
    dsimp only [us]
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.succ_le_of_lt hj)
  have hshape : pre ++ (us ++ vs) :: rest = s := by
    simp only [us, vs, List.take_append_drop]
    dsimp only [pre, a, rest]
    rw [List.getD_eq_getElem _ _ hi, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have herase : erase ((pre.map fun a => (∅, a)) ++
      (∅, us ++ vs) :: (rest.map fun a => (∅, a))) = s := by
    simpa [erase, Function.comp_def] using hshape
  have hlen : z.coordinates.length = Payoff.leafPosition s i j + 1 := by
    have hpos := leafPrefix_length ∅ (pre.map fun a => (∅, a)) ∅ us vs
      (rest.map fun a => (∅, a)) (by omega)
    simpa only [z, plainLeafPrefix, herase, List.length_map, hpre, hu,
      Nat.add_sub_cancel] using hpos
  have htake : (word s).take (Payoff.leafPosition s i j + 1) = z.coordinates := by
    rw [← hlen, ← hshape]
    exact plainLeafPrefix_take pre us vs rest
  refine ⟨z, ?_, ?_, hu⟩
  · rw [htake]
    exact plainLeafPrefix_run pre us vs rest
  · simp [z, plainLeafPrefix, leafPrefixCursor, hpre]

theorem leafPosition_injective (s : List (List ℕ)) {i j p q : ℕ}
    (hi : i < s.length) (hj : j < (s.getD i []).length)
    (hp : p < s.length) (hq : q < (s.getD p []).length)
    (hpos : Payoff.leafPosition s i j = Payoff.leafPosition s p q) : i = p ∧ j = q := by
  obtain ⟨z, hz, hI, hJ⟩ := leaf_prefix_counters s i j hi hj
  obtain ⟨w, hw, hP, hQ⟩ := leaf_prefix_counters s p q hp hq
  rw [hpos] at hz
  have heq : z = w := Option.some.inj (hz.symm.trans hw)
  rw [heq] at hI hJ
  constructor <;> omega

#print axioms flatMap_position
#print axioms plainLeafPrefix_run
#print axioms relaxed_prefix_indices
#print axioms leafPosition_injective

end Erdos591.Positive.Game.LabeledCode

end Erdos118.Reused591
