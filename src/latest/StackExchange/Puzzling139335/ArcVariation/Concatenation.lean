import StackExchange.Puzzling139335.ArcVariation.Defs

/-!
# Concatenation estimates for finite-resolution variation

The lower estimate concatenates two concrete increasing chains.  For the upper
estimate, an increasing chain is split at the common endpoint and that endpoint
is inserted at the join.  The triangle inequality loses at most one `ε`.
-/

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {α X : Type*} [PseudoMetricSpace X]

/-- Inserting an intermediate point into one chord costs at most one penalty. -/
theorem chord_le_add_chord_add {ε : ℝ} (hε : 0 ≤ ε) (x y z : X) :
    chord ε x z ≤ chord ε x y + chord ε y z + ε := by
  unfold chord
  refine max_le ?_ ?_
  · have hxy := le_max_left (dist x y - ε) (0 : ℝ)
    have hyz := le_max_left (dist y z - ε) (0 : ℝ)
    have hdist := dist_triangle x y z
    linarith
  · positivity

/-- Concatenation keeps both scores and adds a nonnegative joining chord. -/
theorem chainScore_add_le_append (ε : ℝ) (f : α → X) (xs ys : List α) :
    chainScore ε f xs + chainScore ε f ys ≤ chainScore ε f (xs ++ ys) := by
  induction xs with
  | nil => simp [chainScore]
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => simp [chainScore]
          | cons y ys =>
              simpa only [List.singleton_append, chainScore, zero_add] using
                le_add_of_nonneg_left (chord_nonneg ε (f x) (f y))
      | cons z xs =>
          simpa only [List.cons_append, chainScore, add_assoc, add_comm, add_left_comm] using
            add_le_add_left ih (chord ε (f x) (f z))

/-- Splitting any list at a join and adjoining `c` loses at most one penalty. -/
theorem chainScore_append_le_insert {ε : ℝ} (hε : 0 ≤ ε)
    (f : α → X) (xs ys : List α) (c : α) :
    chainScore ε f (xs ++ ys) ≤
      chainScore ε f (xs ++ [c]) + chainScore ε f (c :: ys) + ε := by
  induction xs with
  | nil =>
      have h := chainScore_add_le_append ε f [c] ys
      simp only [List.nil_append, chainScore, zero_add, List.singleton_append] at h ⊢
      linarith
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil =>
              simp only [List.append_nil, List.singleton_append, chainScore, add_zero]
              exact add_nonneg (chord_nonneg ε (f x) (f c)) hε
          | cons y ys =>
              have h := chord_le_add_chord_add hε (f x) (f c) (f y)
              simp only [List.singleton_append, chainScore, add_zero]
              linarith
      | cons z xs =>
          simpa only [List.cons_append, chainScore, add_assoc, add_comm, add_left_comm] using
            add_le_add_left ih (chord ε (f x) (f z))

section LinearOrder

variable [LinearOrder α]

/-- An increasing list has a split with all earlier terms at most `c` and all
later terms at least `c`.  Repeated occurrences of `c` are allowed. -/
theorem exists_chain_split (c : α) {xs : List α} (hxs : xs.Pairwise (· ≤ ·)) :
    ∃ ys zs, xs = ys ++ zs ∧ (∀ t ∈ ys, t ≤ c) ∧ ∀ t ∈ zs, c ≤ t := by
  induction xs with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x xs ih =>
      by_cases hxc : x ≤ c
      · obtain ⟨ys, zs, hsplit, hys, hzs⟩ := ih hxs.of_cons
        refine ⟨x :: ys, zs, ?_, ?_, hzs⟩
        · simp only [List.cons_append, hsplit]
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hxc
          · exact hys t ht
      · refine ⟨[], x :: xs, rfl, by simp, ?_⟩
        intro t ht
        have hcx : c ≤ x := (lt_of_not_ge hxc).le
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hcx
        · exact hcx.trans (List.rel_of_pairwise_cons hxs ht)

/-- Chains in two adjacent closed intervals concatenate to a chain in their
union interval. -/
theorem IsChainOn.append_Icc {a b c : α} {xs ys : List α}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hxs : IsChainOn (Icc a c) xs) (hys : IsChainOn (Icc c b) ys) :
    IsChainOn (Icc a b) (xs ++ ys) := by
  refine ⟨List.pairwise_append.mpr ⟨hxs.1, hys.1, ?_⟩, ?_⟩
  · intro x hx y hy
    exact (hxs.2 x hx).2.trans (hys.2 y hy).1
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ⟨(hxs.2 t ht).1, (hxs.2 t ht).2.trans hcb⟩
    · exact ⟨hac.trans (hys.2 t ht).1, (hys.2 t ht).2⟩

/-- Split an interval chain into two chains with the cut point adjoined. -/
theorem IsChainOn.split_Icc {a b c : α} {xs : List α}
    (hac : a ≤ c) (hcb : c ≤ b) (hxs : IsChainOn (Icc a b) xs) :
    ∃ ys zs, xs = ys ++ zs ∧
      IsChainOn (Icc a c) (ys ++ [c]) ∧ IsChainOn (Icc c b) (c :: zs) := by
  obtain ⟨ys, zs, hsplit, hys, hzs⟩ := exists_chain_split c hxs.1
  have hp : (ys ++ zs).Pairwise (· ≤ ·) := hsplit ▸ hxs.1
  have hpy := (List.pairwise_append.mp hp).1
  have hpz := (List.pairwise_append.mp hp).2.1
  have hmy : ∀ t ∈ ys, t ∈ Icc a b := by
    intro t ht
    exact hxs.2 t (hsplit ▸ List.mem_append_left zs ht)
  have hmz : ∀ t ∈ zs, t ∈ Icc a b := by
    intro t ht
    exact hxs.2 t (hsplit ▸ List.mem_append_right ys ht)
  refine ⟨ys, zs, hsplit, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine List.pairwise_append.mpr ⟨hpy, by simp, ?_⟩
    intro t ht u hu
    have : u = c := List.mem_singleton.mp hu
    subst u
    exact hys t ht
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ⟨(hmy t ht).1, hys t ht⟩
    · have : t = c := List.mem_singleton.mp ht
      subst t
      exact ⟨hac, le_rfl⟩
  · exact List.pairwise_cons.mpr ⟨hzs, hpz⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨le_rfl, hcb⟩
    · exact ⟨hzs t ht, (hmz t ht).2⟩

/-- Superadditivity follows by concatenating arbitrary pairs of chains. -/
theorem variationOn_add_le {ε : ℝ} {f : α → X} {a b c : α}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hb : BddAbove (scoresOn ε f (Icc a b))) :
    variationOn ε f (Icc a c) + variationOn ε f (Icc c b) ≤
      variationOn ε f (Icc a b) := by
  suffices variationOn ε f (Icc a c) ≤
      variationOn ε f (Icc a b) - variationOn ε f (Icc c b) by linarith
  apply csSup_le (scoresOn_nonempty ε f (Icc a c))
  rintro _ ⟨xs, hxs, rfl⟩
  have hright : variationOn ε f (Icc c b) ≤
      variationOn ε f (Icc a b) - chainScore ε f xs := by
    apply csSup_le (scoresOn_nonempty ε f (Icc c b))
    rintro _ ⟨ys, hys, rfl⟩
    have hjoin := chainScore_add_le_append ε f xs ys
    have hbound := chainScore_le_variationOn hb (hxs.append_Icc hac hcb hys)
    linarith
  linarith

/-- Subadditivity up to one penalty follows by inserting the cut point into
each finite chain. -/
theorem variationOn_le_add {ε : ℝ} {f : α → X} {a b c : α}
    (hε : 0 ≤ ε) (hac : a ≤ c) (hcb : c ≤ b)
    (hleft : BddAbove (scoresOn ε f (Icc a c)))
    (hright : BddAbove (scoresOn ε f (Icc c b))) :
    variationOn ε f (Icc a b) ≤
      variationOn ε f (Icc a c) + variationOn ε f (Icc c b) + ε := by
  apply csSup_le (scoresOn_nonempty ε f (Icc a b))
  rintro _ ⟨xs, hxs, rfl⟩
  obtain ⟨ys, zs, hsplit, hys, hzs⟩ := hxs.split_Icc hac hcb
  have hinsert := chainScore_append_le_insert hε f ys zs c
  have hleft' := chainScore_le_variationOn hleft hys
  have hright' := chainScore_le_variationOn hright hzs
  rw [hsplit]
  linarith

/-- The concrete finite-resolution variation is additive to within `ε` at a
single cut.  Boundedness of the concrete score sets is the only finiteness input. -/
theorem variationOn_concatenation {ε : ℝ} {f : α → X} {a b c : α}
    (hε : 0 ≤ ε) (hac : a ≤ c) (hcb : c ≤ b)
    (hwhole : BddAbove (scoresOn ε f (Icc a b)))
    (hleft : BddAbove (scoresOn ε f (Icc a c)))
    (hright : BddAbove (scoresOn ε f (Icc c b))) :
    variationOn ε f (Icc a c) + variationOn ε f (Icc c b) ≤
        variationOn ε f (Icc a b) ∧
      variationOn ε f (Icc a b) ≤
        variationOn ε f (Icc a c) + variationOn ε f (Icc c b) + ε :=
  ⟨variationOn_add_le hac hcb hwhole, variationOn_le_add hε hac hcb hleft hright⟩

end LinearOrder

end

end Puzzling139335.ArcVariation
