import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A finite greedy coloring lemma for Erdős Problem 814

The coloring step in Sauermann's proof has two kinds of local constraints.  A
color assigned to an item must avoid a prescribed list for every scope
containing that item, and two items in the same scope must receive different
colors.  The theorem below packages the standard greedy argument with the
sharp count needed in the application.
-/

namespace Erdos814

section GreedyColoring

variable {Item Scope : Type*} [Fintype Item] [Fintype Scope]
  [DecidableEq Item]

/--
A finite greedy coloring theorem with local forbidden lists.

Each item occurs in at most `r` scopes, every scope contains at most `a + 1`
items, and its prescribed forbidden list contains at most `b` colors.  While
an item is colored, each of its scopes therefore forbids at most `a + b`
colors: at most `a` colors already used by the other items of that scope and
at most `b` prescribed colors.  Thus `r * (a + b) < q` colors suffice.
-/
theorem exists_scope_coloring
    {r a b q : ℕ}
    (scope : Scope → Finset Item)
    (avoid : Scope → Finset (Fin q))
    (hfrequency : ∀ x : Item,
      (Finset.univ.filter fun s : Scope ↦ x ∈ scope s).card ≤ r)
    (hscope : ∀ s : Scope, (scope s).card ≤ a + 1)
    (havoid : ∀ s : Scope, (avoid s).card ≤ b)
    (hpalette : r * (a + b) < q) :
    ∃ color : Item → Fin q,
      (∀ s : Scope, Set.InjOn color (scope s : Set Item)) ∧
      (∀ s : Scope, ∀ x ∈ scope s, color x ∉ avoid s) := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hpalette
  let ValidOn := fun (U : Finset Item) (color : Item → Fin q) ↦
    (∀ s : Scope, ∀ x ∈ scope s, x ∈ U → color x ∉ avoid s) ∧
    (∀ s : Scope, ∀ x ∈ scope s, x ∈ U →
      ∀ y ∈ scope s, y ∈ U → color x = color y → x = y)
  have hpartial : ∀ U : Finset Item, ∃ color : Item → Fin q, ValidOn U color := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
        refine ⟨fun _ ↦ ⟨0, hq⟩, ?_⟩
        constructor
        · intro s x hx
          simp
        · intro s x hx
          simp
    | @insert v U hv ih =>
        obtain ⟨color, hvalid⟩ := ih
        let containing : Finset Scope :=
          Finset.univ.filter fun s : Scope ↦ v ∈ scope s
        let forbidden : Finset (Fin q) :=
          containing.biUnion fun s ↦ avoid s ∪ (scope s ∩ U).image color
        have hcontaining : containing.card ≤ r := by
          simpa [containing] using hfrequency v
        have hlocal : ∀ s ∈ containing,
            (avoid s ∪ (scope s ∩ U).image color).card ≤ a + b := by
          intro s hs
          have hvs : v ∈ scope s := (Finset.mem_filter.mp hs).2
          have hinter_subset : scope s ∩ U ⊆ (scope s).erase v := by
            intro x hx
            have hxs : x ∈ scope s := (Finset.mem_inter.mp hx).1
            have hxU : x ∈ U := (Finset.mem_inter.mp hx).2
            exact Finset.mem_erase.mpr ⟨fun h ↦ hv (h ▸ hxU), hxs⟩
          have hinter_card : (scope s ∩ U).card ≤ a := by
            have hcard := Finset.card_le_card hinter_subset
            rw [Nat.le_iff_lt_add_one]
            exact (hcard.trans_lt (Finset.card_erase_lt_of_mem hvs)).trans_le (hscope s)
          have himage : ((scope s ∩ U).image color).card ≤ a :=
            (Finset.card_image_le).trans hinter_card
          calc
            (avoid s ∪ (scope s ∩ U).image color).card
                ≤ (avoid s).card + ((scope s ∩ U).image color).card :=
              Finset.card_union_le _ _
            _ ≤ b + a := Nat.add_le_add (havoid s) himage
            _ = a + b := Nat.add_comm b a
        have hforbidden_card : forbidden.card ≤ r * (a + b) := by
          calc
            forbidden.card ≤ containing.card * (a + b) := by
              exact Finset.card_biUnion_le_card_mul containing
                (fun s ↦ avoid s ∪ (scope s ∩ U).image color) (a + b) hlocal
            _ ≤ r * (a + b) := Nat.mul_le_mul_right (a + b) hcontaining
        have hforbidden_lt : forbidden.card < Fintype.card (Fin q) := by
          simpa using hforbidden_card.trans_lt hpalette
        have hforbidden_ne : forbidden ≠ Finset.univ :=
          (Finset.card_lt_iff_ne_univ forbidden).mp hforbidden_lt
        obtain ⟨fresh, hfresh⟩ : ∃ fresh : Fin q, fresh ∉ forbidden := by
          by_contra h
          apply hforbidden_ne
          apply Finset.ext
          intro z
          constructor
          · intro
            exact Finset.mem_univ z
          · intro
            by_contra hz
            exact h ⟨z, hz⟩
        let newColor : Item → Fin q := fun x ↦ if x = v then fresh else color x
        refine ⟨newColor, ?_⟩
        constructor
        · intro s x hxs hxU
          by_cases hxv : x = v
          · subst x
            have hscontaining : s ∈ containing := by
              simp [containing, hxs]
            have havSubset : avoid s ⊆ forbidden := by
              intro z hz
              exact Finset.mem_biUnion.mpr ⟨s, hscontaining,
                Finset.mem_union_left _ hz⟩
            simpa [newColor] using fun hmem ↦ hfresh (havSubset hmem)
          · have hxOld : x ∈ U := (Finset.mem_insert.mp hxU).resolve_left hxv
            simpa [newColor, hxv] using hvalid.1 s x hxs hxOld
        · intro s x hxs hxU y hys hyU hxy
          by_cases hxv : x = v
          · subst x
            by_cases hyv : y = v
            · exact hyv.symm
            · have hyOld : y ∈ U := (Finset.mem_insert.mp hyU).resolve_left hyv
              have hscontaining : s ∈ containing := by
                simp [containing, hxs]
              have hyImage : color y ∈ (scope s ∩ U).image color := by
                exact Finset.mem_image.mpr ⟨y, Finset.mem_inter.mpr ⟨hys, hyOld⟩, rfl⟩
              have hyForbidden : color y ∈ forbidden := by
                exact Finset.mem_biUnion.mpr ⟨s, hscontaining,
                  Finset.mem_union_right _ hyImage⟩
              have heq : fresh = color y := by
                simpa [newColor, hyv] using hxy
              exact (hfresh (heq ▸ hyForbidden)).elim
          · have hxOld : x ∈ U := (Finset.mem_insert.mp hxU).resolve_left hxv
            by_cases hyv : y = v
            · subst y
              have hscontaining : s ∈ containing := by
                simp [containing, hys]
              have hxImage : color x ∈ (scope s ∩ U).image color := by
                exact Finset.mem_image.mpr ⟨x, Finset.mem_inter.mpr ⟨hxs, hxOld⟩, rfl⟩
              have hxForbidden : color x ∈ forbidden := by
                exact Finset.mem_biUnion.mpr ⟨s, hscontaining,
                  Finset.mem_union_right _ hxImage⟩
              have heq : color x = fresh := by
                simpa [newColor, hxv] using hxy
              exact (hfresh (heq ▸ hxForbidden)).elim
            · have hyOld : y ∈ U := (Finset.mem_insert.mp hyU).resolve_left hyv
              apply hvalid.2 s x hxs hxOld y hys hyOld
              simpa [newColor, hxv, hyv] using hxy
  obtain ⟨color, hcolor⟩ := hpartial Finset.univ
  refine ⟨color, ?_, ?_⟩
  · intro s x hxs y hys hxy
    exact hcolor.2 s x hxs (Finset.mem_univ x) y hys (Finset.mem_univ y) hxy
  · intro s x hxs
    exact hcolor.1 s x hxs (Finset.mem_univ x)

/--
The numerical instance used in the proof of Erdős Problem 814: each item is
in at most `200` scopes, each scope has at most `k + 1` items and excludes at
most `k` prescribed colors, so `401 * k` colors suffice when `k > 0`.
-/
theorem exists_erdos814_scope_coloring
    {k : ℕ} (hk : 0 < k)
    (scope : Scope → Finset Item)
    (avoid : Scope → Finset (Fin (401 * k)))
    (hfrequency : ∀ x : Item,
      (Finset.univ.filter fun s : Scope ↦ x ∈ scope s).card ≤ 200)
    (hscope : ∀ s : Scope, (scope s).card ≤ k + 1)
    (havoid : ∀ s : Scope, (avoid s).card ≤ k) :
    ∃ color : Item → Fin (401 * k),
      (∀ s : Scope, Set.InjOn color (scope s : Set Item)) ∧
      (∀ s : Scope, ∀ x ∈ scope s, color x ∉ avoid s) := by
  apply exists_scope_coloring (r := 200) (a := k) (b := k)
    scope avoid hfrequency hscope havoid
  calc
    200 * (k + k) = 200 * k + 200 * k := Nat.mul_add 200 k k
    _ = (200 + 200) * k := (Nat.add_mul 200 200 k).symm
    _ = 400 * k := rfl
    _ < 401 * k := Nat.mul_lt_mul_of_pos_right (by decide) hk

end GreedyColoring

end Erdos814
