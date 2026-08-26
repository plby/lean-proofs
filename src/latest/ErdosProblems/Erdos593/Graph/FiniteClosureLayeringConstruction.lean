import ErdosProblems.Erdos593.Graph.FiniteClosureLayering
import ErdosProblems.Erdos593.Graph.FiniteClosureCardinality
import Mathlib.Data.Finset.Max
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Constructing finite closure layerings from closed covers

This module isolates the order-theoretic part of the positive-atom strategy.
Given a monotone cover by small sets which are closed under a finite-output
operator, it assigns each vertex its first cover index.  That first-entry
rank is a `FiniteClosureLayering`.

The ordinal wrapper below converts any monotone, locally small finite-output
hull into such a cover. Together with `FiniteClosureCardinality`, this also
gives the singular-cardinal-safe construction for countable finite closures.
-/

namespace Erdos593

namespace FiniteClosureLayeringConstruction

open Set
open scoped Ordinal

universe u

variable {V I : Type u}

/-- The least index of a member of a well-founded cover containing `x`. -/
noncomputable def firstRank [LinearOrder I] [WellFoundedLT I]
    (C : I → Set V) (hcover : ∀ x : V, ∃ i : I, x ∈ C i) (x : V) : I :=
  wellFounded_lt.min {i | x ∈ C i} (by
    rcases hcover x with ⟨i, hi⟩
    exact ⟨i, hi⟩)

theorem firstRank_mem [LinearOrder I] [WellFoundedLT I]
    (C : I → Set V) (hcover : ∀ x : V, ∃ i : I, x ∈ C i) (x : V) :
    x ∈ C (firstRank C hcover x) := by
  unfold firstRank
  exact wellFounded_lt.min_mem {i : I | x ∈ C i} _

theorem firstRank_le_of_mem [LinearOrder I] [WellFoundedLT I]
    (C : I → Set V) (hcover : ∀ x : V, ∃ i : I, x ∈ C i)
    {x : V} {i : I} (hx : x ∈ C i) :
    firstRank C hcover x ≤ i := by
  apply le_of_not_gt
  unfold firstRank
  exact wellFounded_lt.not_lt_min {j : I | x ∈ C j} hx

/--
A monotone, small, `Φ`-closed cover produces a finite closure layering.

The condition `0 < r` is essential: when `r = 0`, the defining closure
condition would impose a constraint on the output on the empty input below
every rank, which generally cannot hold for an ordinal-style rank order.
-/
theorem exists_finiteClosureLayering_of_closed_cover
    [LinearOrder I] [WellFoundedLT I]
    {r : Nat} (Φ : {s : Finset V // s.card = r} → Finset V)
    (C : I → Set V)
    (hcover : ∀ x : V, ∃ i : I, x ∈ C i)
    (hmono : Monotone C)
    (hsmall : ∀ i : I, Cardinal.mk (C i) < Cardinal.mk V)
    (hclosed : ∀ (i : I) (s : Finset V) (hs : s.card = r),
      (∀ x ∈ s, x ∈ C i) → ∀ y ∈ Φ ⟨s, hs⟩, y ∈ C i)
    (hr : 0 < r) :
    ∃ L : FiniteClosureLayering r Φ I, L.rank = firstRank C hcover := by
  classical
  refine ⟨{ rank := firstRank C hcover
            fiber_lt := ?_
            earlier_closed := ?_ }, rfl⟩
  · intro i
    apply (Cardinal.mk_subtype_le_of_subset ?_).trans_lt (hsmall i)
    intro x hx
    change firstRank C hcover x = i at hx
    rw [← hx]
    exact firstRank_mem C hcover x
  · intro v s hs hlt
    have hspos : 0 < s.card := by
      simpa only [hs] using! hr
    obtain ⟨m, hm, hmax⟩ :=
      Finset.exists_max_image s (firstRank C hcover) (Finset.card_pos.mp hspos)
    intro y hy
    have hsC : ∀ x ∈ s, x ∈ C (firstRank C hcover m) := by
      intro x hx
      exact hmono (hmax x hx) (firstRank_mem C hcover x)
    have hyC : y ∈ C (firstRank C hcover m) :=
      hclosed _ s hs hsC y hy
    exact (firstRank_le_of_mem C hcover hyC).trans_lt (hlt m hm)

/--
An ordinal-indexed small-hull construction of a finite closure layering.

Only individual initial segments of the canonical well-order of `κ` are used,
so this is valid at singular cardinals. The positive arity condition is needed
solely for the maximum-rank argument in the resulting layering.
-/
theorem exists_finiteClosureLayering_of_small_hull
    {κ : Cardinal.{u}}
    {r : Nat} (Φ : {s : Finset V // s.card = r} → Finset V)
    (hκ : Cardinal.aleph0 ≤ κ) (hV : Cardinal.mk V = κ)
    (Hull : Set V → Set V)
    (hHull_mono : Monotone Hull)
    (hHull_contains : ∀ S : Set V, S ⊆ Hull S)
    (hHull_small : ∀ S : Set V, Cardinal.mk S < κ → Cardinal.mk (Hull S) < κ)
    (hHull_closed : ∀ (S : Set V) (s : Finset V) (hs : s.card = r),
      (∀ x ∈ s, x ∈ Hull S) → ∀ y ∈ Φ ⟨s, hs⟩, y ∈ Hull S)
    (hr : 0 < r) :
    Nonempty (FiniteClosureLayering r Φ κ.ord.ToType) := by
  classical
  have hκtype : Cardinal.mk κ.ord.ToType = κ := by
    simp
  let e : V ≃ κ.ord.ToType :=
    Classical.choice (Cardinal.eq.mp (hV.trans hκtype.symm))
  refine ⟨(exists_finiteClosureLayering_of_closed_cover Φ
      (fun i : κ.ord.ToType => Hull (e.symm '' Set.Iic i)) ?_ ?_ ?_ ?_ hr).choose⟩
  · intro x
    refine ⟨e x, hHull_contains _ ?_⟩
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    change e x ≤ e x
    exact le_rfl
  · intro i j hij
    apply hHull_mono
    rintro x ⟨a, ha, rfl⟩
    exact ⟨a, ha.trans hij, rfl⟩
  · intro i
    rw [hV]
    apply hHull_small
    rw [Cardinal.mk_image_eq e.symm.injective]
    have horder : Cardinal.ord (Cardinal.mk κ.ord.ToType) = typeLT κ.ord.ToType := by
      rw [hκtype]
      exact (Ordinal.type_toType κ.ord).symm
    have htype : Cardinal.aleph0 ≤ Cardinal.mk κ.ord.ToType := by
      rwa [hκtype]
    exact (Cardinal.mk_Iic_lt i horder htype).trans_eq hκtype
  · intro i s hs hsC y hy
    exact hHull_closed _ s hs hsC y hy

/-- Every finite-output operation of positive arity on an uncountable type
has a singular-cardinal-safe finite closure layering. -/
theorem exists_finiteClosureLayering_of_uncountable
    {r : Nat} (Φ : {s : Finset V // s.card = r} → Finset V)
    (hV : Cardinal.aleph0 < Cardinal.mk V) (hr : 0 < r) :
    Nonempty (FiniteClosureLayering r Φ (Cardinal.mk V).ord.ToType) := by
  refine exists_finiteClosureLayering_of_small_hull Φ hV.le rfl
    (FiniteClosureCardinality.closure r Φ) ?_ ?_ ?_ ?_ hr
  · exact FiniteClosureCardinality.closure_mono r Φ
  · exact FiniteClosureCardinality.subset_closure r Φ
  · intro S hS
    exact FiniteClosureCardinality.mk_closure_lt r Φ S (Cardinal.mk V) hV hS
  · intro S s hs hinside y hy
    apply FiniteClosureCardinality.closureStep_closure_subset r Φ S
    rw [FiniteClosureCardinality.mem_closureStep_iff]
    exact Or.inr ⟨⟨s, hs⟩, hinside, hy⟩

end FiniteClosureLayeringConstruction

end Erdos593
