import ErdosProblems.Erdos118.GapCounts
import ErdosProblems.Erdos118.SkippedCuts

/-!
Occupied coordinate gaps correspond to proper below-prefixes and, under
the actual interior-cut condition, to unique interior parses. Finite
selected-label cardinalities are not assumed in this correspondence.
-/

namespace Erdos118.GapPrefixes

open GapCounts Negative Negative.Exact LabelledExtensions LabelCoarsening CutIndices
open PrefixRealization (below)

theorem below_length_of_between (xs : List ℕ) (hx : xs.Pairwise (· < ·)) (y k : ℕ)
    (hk : k + 1 < xs.length) (hleft : xs.getD k 0 < y) (hright : y < xs.getD (k + 1) 0) :
    (below y xs).length = k + 1 := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      cases xs with
      | nil => simp at hk
      | cons a xs =>
        have hxy : x < y := hleft
        have hya : y < a := hright
        simp [below, hxy, Nat.not_lt.mpr hya.le]
    | succ k =>
      have htail : k + 1 < xs.length := by simpa using hk
      have hm : xs.getD k 0 ∈ xs := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      have hxy : x < y := ((List.pairwise_cons.mp hx).1 _ hm).trans hleft
      have hi := ih (List.pairwise_cons.mp hx).2 k htail hleft hright
      simpa only [below, List.takeWhile_cons, decide_eq_true hxy, ↓reduceIte,
        List.length_cons] using congrArg (· + 1) hi

theorem between_of_below_length (xs : List ℕ) (y k : ℕ) (hy : y ∉ xs)
    (hlen : (below y xs).length = k + 1) (hk : k + 1 < xs.length) :
    xs.getD k 0 < y ∧ y < xs.getD (k + 1) 0 := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    by_cases hxy : x < y
    · cases k with
      | zero =>
        cases xs with
        | nil => simp at hk
        | cons a xs =>
          have hnot : ¬ a < y := by
            intro hay
            simp [below, hxy, hay] at hlen
          have hne : a ≠ y := by
            intro he
            exact hy (by simp [he])
          exact ⟨hxy, by change y < a; omega⟩
      | succ k =>
        have hyTail : y ∉ xs := fun h ↦ hy (List.mem_cons_of_mem x h)
        have htail : (below y xs).length = k + 1 := by
          simpa only [below, List.takeWhile_cons, decide_eq_true hxy, ↓reduceIte,
            List.length_cons, Nat.add_right_cancel_iff] using hlen
        have hkt : k + 1 < xs.length := by simpa using hk
        exact ih k hyTail htail hkt
    · simp [below, hxy] at hlen

theorem gap_iff_below_length (xs ys : List ℕ) (hx : xs.Pairwise (· < ·))
    (hd : xs.Disjoint ys) (k : ℕ) :
    Gap xs ys k ↔ k + 1 < xs.length ∧ ∃ y ∈ ys, (below y xs).length = k + 1 := by
  constructor
  · rintro ⟨hk, y, hy, hleft, hright⟩
    exact ⟨hk, y, hy, below_length_of_between xs hx y k hk hleft hright⟩
  · rintro ⟨hk, y, hy, hlen⟩
    exact ⟨hk, y, hy, between_of_below_length xs y k (fun h ↦ hd h hy) hlen hk⟩

theorem interior_prefix_length_injective {P Q : InteriorWords.Position} {xs : List ℕ}
    (hp : P.word <+: xs) (hq : Q.word <+: xs) (hlen : P.word.length = Q.word.length) : P = Q := by
  apply interior_word_injective
  rcases List.prefix_or_prefix_of_prefix hp hq with hpq | hqp
  · exact hpq.eq_of_length hlen
  · exact (hqp.eq_of_length hlen.symm).symm

private theorem prefix_length_lt {xs ys : List ℕ} (hp : xs <+: ys) (hne : xs ≠ ys) :
    xs.length < ys.length := by
  have hle := hp.length_le
  by_contra hn
  exact hne (hp.eq_of_length (by omega))

theorem gap_iff_cut_length (S T : Stem) (hd : S.ordinary.Disjoint T.ordinary)
    (hinterior : InteriorCuts S T) (k : ℕ) :
    Gap S.ordinary T.ordinary k ↔ ∃ P : InteriorWords.Position,
      P.word <+: S.ordinary ∧ P.word.length = k + 1 ∧
        Cut S T P.done.length P.entries.length := by
  rw [gap_iff_below_length S.ordinary T.ordinary
    (S.increasing.sublist S.ordinary_sublist) hd k]
  constructor
  · rintro ⟨hk, y, hy, hlen⟩
    have hp : ProperBelow y S := by
      constructor
      · intro he
        simp [he] at hlen
      · intro he
        rw [he] at hlen
        omega
    obtain ⟨P, hP⟩ := hinterior y hy hp
    refine ⟨P, ?_, by rw [hP]; exact hlen, y, hy, hp, P, hP, rfl, rfl⟩
    rw [hP]
    exact List.takeWhile_prefix _
  · rintro ⟨P, hp, hlen, y, hy, hproper, Q, hQ, hi, hj⟩
    have hq : Q.word <+: S.ordinary := by
      rw [hQ]
      exact List.takeWhile_prefix _
    have he : Q = P := SkippedCuts.interior_common_prefix_same_indices hq hp hi hj
    subst Q
    have hlenBelow : (below y S.ordinary).length = k + 1 := by rw [← hQ]; exact hlen
    have hlt := prefix_length_lt (List.takeWhile_prefix (fun x ↦ decide (x < y)))
      hproper.2
    change (below y S.ordinary).length < S.ordinary.length at hlt
    rw [hlenBelow] at hlt
    exact ⟨hlt, y, hy, hlenBelow⟩

end Erdos118.GapPrefixes
