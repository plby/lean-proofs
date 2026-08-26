import ErdosProblems.Erdos591.AtomicSpacing

/-!
# Combining independently selected projections of one chronological log

The two sides occupy disjoint positions of the original log. Their
coarsened selections therefore have a common chronological interleaving,
with no sorting or extra numerical inputs.
-/

namespace Erdos591.Positive.Game.Atomic

def filterSide (xs : List Atom) (side : Bool) : List Atom :=
  xs.filter fun a => a.side == side

theorem selects_nil_right {xs : List Atom} (h : Selects xs []) : xs = [] := by
  cases h
  rfl

theorem Atom.Coarsens.refl (a : Atom) : a.Coarsens a :=
  ⟨rfl, rfl, Finset.Subset.refl _⟩

theorem Atom.Coarsens.trans {a b c : Atom} (hab : a.Coarsens b) (hbc : b.Coarsens c) :
    a.Coarsens c :=
  ⟨hab.side_eq.trans hbc.side_eq, hab.value_eq.trans hbc.value_eq,
    hab.label_subset.trans hbc.label_subset⟩

theorem Selects.of_sublist {xs ys : List Atom} (h : List.Sublist xs ys) : Selects xs ys := by
  induction h with
  | slnil => exact .nil
  | cons a _ ih => exact .drop a ih
  | cons_cons a _ ih => exact .keep (.refl a) ih

theorem Coarsens.toSelects {xs ys : List Atom} (h : Coarsens xs ys) : Selects xs ys := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .keep ha ih

theorem Selects.trans {xs ys zs : List Atom} (hxy : Selects xs ys) (hyz : Selects ys zs) :
    Selects xs zs := by
  induction hyz generalizing xs with
  | nil =>
      have heq := selects_nil_right hxy
      subst xs
      exact .nil
  | drop A _ ih => exact .drop A (ih hxy)
  | @keep a A ys zs ha _ ih =>
      cases hxy with
      | drop _ hx => exact .drop A (ih hx)
      | @keep x _ xs _ hx hxTail => exact .keep (hx.trans ha) (ih hxTail)

theorem Coarsens.selects_sublist {xs ys zs : List Atom} (h : Coarsens xs ys)
    (hy : List.Sublist ys zs) : Selects xs zs :=
  h.toSelects.trans (Selects.of_sublist hy)

theorem Selects.retag_values {xs ys : List Atom} (h : Selects xs ys) (f : ℕ → Bool) :
    Selects (retag (fun a => f a.value) xs) (retag (fun a => f a.value) ys) := by
  induction h with
  | nil => exact .nil
  | drop A _ ih => exact .drop _ ih
  | keep ha _ ih =>
      exact .keep ⟨congrArg f ha.value_eq, ha.value_eq, ha.label_subset⟩ ih

/-- Merge two independently coarsened side projections while retaining
their exact projected atom lists. -/
theorem selects_merge {xs ys original : List Atom}
    (hx : Selects xs (filterSide original false))
    (hy : Selects ys (filterSide original true)) :
    ∃ zs, Selects zs original ∧ project zs false = project xs false ∧
      project zs true = project ys true := by
  induction original generalizing xs ys with
  | nil =>
      have hxs : xs = [] := selects_nil_right hx
      have hys : ys = [] := selects_nil_right hy
      exact ⟨[], .nil, by simp [hxs], by simp [hys]⟩
  | cons A original ih =>
      cases hA : A.side with
      | false =>
          have hx' : Selects xs (A :: filterSide original false) := by
            simpa [filterSide, hA] using hx
          have hy' : Selects ys (filterSide original true) := by
            simpa [filterSide, hA] using hy
          cases hx' with
          | drop _ hx0 =>
              obtain ⟨zs, hz, hz0, hz1⟩ := ih hx0 hy'
              exact ⟨zs, .drop A hz, hz0, hz1⟩
          | @keep a _ xs _ ha hx0 =>
              obtain ⟨zs, hz, hz0, hz1⟩ := ih hx0 hy'
              have ha0 : a.side = false := ha.side_eq.trans hA
              exact ⟨a :: zs, .keep ha hz,
                by simp [project, ha0, hz0], by simp [project, ha0, hz1]⟩
      | true =>
          have hx' : Selects xs (filterSide original false) := by
            simpa [filterSide, hA] using hx
          have hy' : Selects ys (A :: filterSide original true) := by
            simpa [filterSide, hA] using hy
          cases hy' with
          | drop _ hy0 =>
              obtain ⟨zs, hz, hz0, hz1⟩ := ih hx' hy0
              exact ⟨zs, .drop A hz, hz0, hz1⟩
          | @keep a _ ys _ ha hy0 =>
              obtain ⟨zs, hz, hz0, hz1⟩ := ih hx' hy0
              have ha1 : a.side = true := ha.side_eq.trans hA
              exact ⟨a :: zs, .keep ha hz,
                by simp [project, ha1, hz0], by simp [project, ha1, hz1]⟩

theorem tag_project (xs : List Atom) (side : Bool) :
    tag side (project xs side) = filterSide xs side := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [tag, filterSide] at ih
      by_cases ha : a.side = side
      · have heq : ({side := side, label := a.label, value := a.value} : Atom) = a := by
          cases a
          simpa using ha.symm
        simp [project, filterSide, ha, tag, heq, ih]
      · simp [project, filterSide, ha, tag, ih]

theorem project_tag (xs : List (Finset ℕ × ℕ)) (side : Bool) :
    project (tag side xs) side = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [tag] at ih
      simp [tag, project, ih]

theorem filterSide_tag (xs : List (Finset ℕ × ℕ)) (side : Bool) :
    filterSide (tag side xs) side = tag side xs := by
  rw [← tag_project, project_tag]

theorem tag_sublist_filterSide {xs : List (Finset ℕ × ℕ)} {original : List Atom}
    (side : Bool) (h : List.Sublist (tag side xs) original) :
    List.Sublist (tag side xs) (filterSide original side) := by
  have hh : List.Sublist (filterSide (tag side xs) side) (filterSide original side) :=
    List.Sublist.filter (fun a : Atom => a.side == side) h
  simpa only [filterSide_tag] using hh

theorem selects_merge_programs (program : Bool → List (Finset ℕ × ℕ)) (original : List Atom)
    (h : ∀ side, Selects (tag side (program side)) (tag side (project original side))) :
    ∃ xs, Selects xs original ∧ ∀ side, project xs side = program side := by
  obtain ⟨xs, hx, h0, h1⟩ := selects_merge
    (by simpa [tag_project] using h false) (by simpa [tag_project] using h true)
  refine ⟨xs, hx, ?_⟩
  intro side
  cases side
  · simpa [project_tag] using h0
  · simpa [project_tag] using h1

#print axioms selects_merge
#print axioms selects_merge_programs
#print axioms Selects.trans
#print axioms Selects.retag_values

end Erdos591.Positive.Game.Atomic
