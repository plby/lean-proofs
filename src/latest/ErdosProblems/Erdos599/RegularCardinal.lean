/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FamilyTools
import ErdosProblems.Erdos599.Stationary

/-!
# The regular-cardinal slice construction for Erdős Problem 599

This file isolates the set-theoretic content of Aharoni--Berger,
Section 9, Assertions 9.12--9.15.  The graph-theoretic notions used there
(frontiers, linkages, and maverick paths) are parameters; all cardinal and
club bookkeeping is proved here.

The most important result is `exists_diagonalSlice_superset` (9.13).  Rows
`Z θ` of size at most `κ` are enumerated by ordinals below `κ`.  Regularity
then puts every `< κ` subset of their union into a single diagonal slice
`{z θ γ | θ < α, γ < α}`.  The companion club version chooses that `α` in
an arbitrary club.  The two-sided frontier estimate packages the exact two
cases of 9.12, and the final definitions expose 9.15 without baking any
unproved graph theorem into a data structure.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace RegularCardinal

universe u v

/-- Ordinal stages below the initial ordinal of `κ`. -/
abbrev Stage (κ : Cardinal.{u}) := Stationary.Below κ

/-! ## Club tails and controlled later stages -/

/-- The cofinality of the stage order is not countable when `κ` is regular
and uncountable. -/
theorem cof_stage_ne_aleph0 {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hκu : ℵ₀ < κ) : Order.cof (Stage κ) ≠ ℵ₀ := by
  rw [Stationary.cof_below_eq_lift hκ]
  rw [← Cardinal.lift_aleph0.{u + 1, u}]
  exact (Cardinal.lift_lt.mpr hκu).ne'

/-- Intersecting two clubs below an uncountable regular cardinal again gives
a club. -/
theorem isClubBelow_inter {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hκu : ℵ₀ < κ) {C D : Set (Stage κ)}
    (hC : Stationary.IsClubBelow κ C)
    (hD : Stationary.IsClubBelow κ D) :
    Stationary.IsClubBelow κ (C ∩ D) :=
  hC.inter (cof_stage_ne_aleph0 hκ hκu) hD

/-- A finite intersection of clubs below an uncountable regular cardinal is
club.  The subtype indexing prevents clubs outside `s` from entering the
intersection. -/
theorem isClubBelow_iInter_finset {κ : Cardinal.{u}} {ι : Type v}
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ) (s : Finset ι)
    (C : ι → Set (Stage κ))
    (hC : ∀ i ∈ s, Stationary.IsClubBelow κ (C i)) :
    Stationary.IsClubBelow κ (⋂ i : s, C i.1) := by
  apply IsClub.iInter_of_countable (cof_stage_ne_aleph0 hκ hκu)
  intro i
  exact hC i.1 i.2

/-- A club can be sliced above a prescribed lower bound without ceasing to
be club. -/
theorem isClubBelow_inter_Ici {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hκu : ℵ₀ < κ) {C : Set (Stage κ)}
    (hC : Stationary.IsClubBelow κ C) (a : Stage κ) :
    Stationary.IsClubBelow κ (C ∩ Set.Ici a) :=
  isClubBelow_inter hκ hκu hC (Stationary.isClub_Ici a)

/-- Choose a club point strictly above a prescribed stage. -/
def nextInClub {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : Set (Stage κ)) (hC : Stationary.IsClubBelow κ C)
    (a : Stage κ) : Stage κ :=
  Classical.choose (Stationary.exists_mem_club_strictlyAbove hκ hC a)

@[simp]
theorem nextInClub_mem {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : Set (Stage κ)) (hC : Stationary.IsClubBelow κ C)
    (a : Stage κ) : nextInClub hκ C hC a ∈ C :=
  (Classical.choose_spec
    (Stationary.exists_mem_club_strictlyAbove hκ hC a)).1

theorem lt_nextInClub {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : Set (Stage κ)) (hC : Stationary.IsClubBelow κ C)
    (a : Stage κ) : a < nextInClub hκ C hC a :=
  (Classical.choose_spec
    (Stationary.exists_mem_club_strictlyAbove hκ hC a)).2

/-- A later club point simultaneously exceeds two stage bounds. -/
def aboveInClub {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : Set (Stage κ)) (hC : Stationary.IsClubBelow κ C)
    (a b : Stage κ) : Stage κ :=
  nextInClub hκ C hC (max a b)

@[simp]
theorem aboveInClub_mem {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : Set (Stage κ)) (hC : Stationary.IsClubBelow κ C)
    (a b : Stage κ) : aboveInClub hκ C hC a b ∈ C :=
  nextInClub_mem hκ C hC _

theorem left_lt_aboveInClub {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : Set (Stage κ)) (hC : Stationary.IsClubBelow κ C)
    (a b : Stage κ) : a < aboveInClub hκ C hC a b :=
  (le_max_left a b).trans_lt (lt_nextInClub hκ C hC _)

theorem right_lt_aboveInClub {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : Set (Stage κ)) (hC : Stationary.IsClubBelow κ C)
    (a b : Stage κ) : b < aboveInClub hκ C hC a b :=
  (le_max_right a b).trans_lt (lt_nextInClub hκ C hC _)

/-! ## Bounded birth stages and Assertion 9.12 -/

/-- A set which injects into the stages below one fixed `α < κ` has
cardinality `< κ`.  This formulation avoids any unnecessary universe
restriction on the stage type itself: the ranked objects live in the same
universe as `κ`, while their ranks are ordinals below `κ`. -/
theorem mk_lt_of_injective_bounded_stage {κ : Cardinal.{u}} {X : Type u}
    (α : Stage κ) {S : Set X} (rank : S → Stage κ)
    (hinj : Function.Injective rank) (hrank : ∀ x, rank x < α) :
    #S < κ := by
  let f : S → Set.Iio α.1 := fun x ↦ ⟨(rank x).1, hrank x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply hinj
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val hxy
  have hleLift := Cardinal.lift_mk_le_lift_mk_of_injective hf
  have hle : #S ≤ α.1.card := by
    apply Cardinal.lift_le.mp
    simpa only [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift] using hleLift
  exact hle.trans_lt (Cardinal.lt_ord.mp α.2)

/-- Abstract form of Assertion 9.12.

For increasing frontiers, an old-minus-new path is inessential at the new
stage.  In the reverse direction, every new-minus-old path has a distinct
birth stage below the newer frontier.  If every inessential part has size
`< κ`, both orientations of the frontier difference have size `< κ`. -/
def frontierDiff {κ : Cardinal.{u}} {Path : Type u}
    (frontier : Stage κ → Set Path) (α β : Stage κ) : Set Path :=
  frontier α \ frontier β

theorem frontier_difference_lt {κ : Cardinal.{u}} {Path : Type u}
    (hκ : κ.IsRegular) (frontier inessential : Stage κ → Set Path)
    (birth : Path → Stage κ)
    (hbirth : ∀ α β, Set.InjOn birth (frontierDiff frontier α β))
    (hinessential : ∀ α, #(inessential α) < κ)
    (hforward : ∀ ⦃α β⦄, α < β → frontierDiff frontier α β ⊆ inessential β)
    (hbackward : ∀ ⦃α β p⦄, β < α →
      p ∈ frontierDiff frontier α β → birth p < α) :
    ∀ α β, #(frontierDiff frontier α β) < κ := by
  intro α β
  rcases lt_trichotomy α β with hαβ | rfl | hβα
  · exact (Cardinal.mk_le_mk_of_subset (hforward hαβ)).trans_lt
      (hinessential β)
  · simpa [frontierDiff] using Cardinal.aleph0_pos.trans_le hκ.aleph0_le
  · let rank : frontierDiff frontier α β → Stage κ :=
      fun p ↦ birth p.1
    apply mk_lt_of_injective_bounded_stage α rank
    · intro p q hpq
      apply Subtype.ext
      apply hbirth α β p.2 q.2
      simpa only [rank] using hpq
    · intro p
      exact hbackward hβα p.2

/-! ## Regular-cardinal union estimates used by the closing-up recursion -/

/-- The union of two `< κ` sets is `< κ` when `κ` is regular (indeed,
when it is merely infinite). -/
theorem mk_union_lt {κ : Cardinal.{u}} {X : Type u}
    (hκ : κ.IsRegular) {S T : Set X} (hS : #S < κ) (hT : #T < κ) :
    #(S ∪ T : Set X) < κ :=
  (Cardinal.mk_union_le S T).trans_lt
    (Cardinal.add_lt_of_lt hκ.aleph0_le hS hT)

/-- One closing-up row remains `< κ`: start with a `< κ` core and adjoin
fewer than `κ` pieces, each of size `< κ`.  This is the cardinal calculation
behind every line of the source recursion (9.13a). -/
theorem mk_closureRow_lt {κ : Cardinal.{u}} {ι X : Type u}
    (hκ : κ.IsRegular) {I : Set ι} {core : Set X} {piece : ι → Set X}
    (hcore : #core < κ) (hI : #I < κ)
    (hpiece : ∀ i ∈ I, #(piece i) < κ) :
    #(core ∪ ⋃ i ∈ I, piece i : Set X) < κ := by
  apply mk_union_lt hκ hcore
  exact FamilyTools.mk_biUnion_lt_of_isRegular hκ hI hpiece

/-- The vertex union of fewer than `κ` finite maverick paths has size
`< κ`.  In 9.15 the mavericks form a subfamily of a finite-path linkage. -/
theorem mk_maverickVertexSet_lt {κ : Cardinal.{u}} {Path V : Type u}
    (hκ : κ.IsRegular) {M : Set Path} {support : Path → Set V}
    (hM : #M < κ) (hfinite : ∀ p ∈ M, (support p).Finite) :
    #(⋃ p ∈ M, support p) < κ :=
  FamilyTools.mk_biUnion_lt_of_finite_of_isRegular hκ hM hfinite

/-! ## The diagonal closure of the `Z_θ` rows (Assertion 9.13) -/

/-- The union `Z` of all rows in the regular-cardinal construction. -/
def rowUnion {κ : Cardinal.{u}} {X : Type u}
    (Z : Stage κ → Set X) : Set X :=
  ⋃ θ, Z θ

/-- The source's diagonal set
`Z^{<α}_{<α} = {z^γ_θ | θ < α, γ < α}`.

An `Option`-valued enumeration lets empty rows be represented without a
spurious `Nonempty X` assumption. -/
def diagonalSlice {κ : Cardinal.{u}} {X : Type u}
    (row : Stage κ → Stage κ → Option X) (α : Stage κ) : Set X :=
  {x | ∃ θ γ, θ < α ∧ γ < α ∧ row θ γ = some x}

/-- `row` enumerates every member of every `Z θ`.  Values outside the rows
are harmless, so only coverage (not exactness) is required. -/
def EnumeratesRows {κ : Cardinal.{u}} {X : Type u}
    (Z : Stage κ → Set X) (row : Stage κ → Stage κ → Option X) : Prop :=
  ∀ θ x, x ∈ Z θ → ∃ γ, row θ γ = some x

/-- A cardinal bound `#S ≤ κ` supplies an embedding of `S` into the stage
order below `κ`. -/
theorem nonempty_embedding_stage_of_mk_le {κ : Cardinal.{u}} {X : Type u}
    {S : Set X} (hS : #S ≤ κ) : Nonempty (S ↪ Stage κ) := by
  apply Cardinal.lift_mk_le'.mp
  rw [Stationary.mk_below]
  simpa only [Cardinal.lift_lift] using Cardinal.lift_le.mpr hS

/-- Turn an embedding of a subtype into a partial enumeration of its ambient
values. -/
def enumerateAlong {I X : Type*} {S : Set X} (e : S ↪ I) : I → Option X :=
  by
    classical
    exact fun i ↦
      if h : ∃ x : S, e x = i then some (Classical.choose h).1 else none

@[simp]
theorem enumerateAlong_apply {I X : Type*} {S : Set X} (e : S ↪ I)
    (x : S) : enumerateAlong e (e x) = some x.1 := by
  classical
  rw [enumerateAlong, dif_pos ⟨x, rfl⟩]
  have he : e (Classical.choose (show ∃ y : S, e y = e x from ⟨x, rfl⟩)) = e x :=
    Classical.choose_spec (show ∃ y : S, e y = e x from ⟨x, rfl⟩)
  have hchosen :
      Classical.choose (show ∃ y : S, e y = e x from ⟨x, rfl⟩) = x :=
    e.injective he
  rw [hchosen]

/-- A canonical embedding of the row `Z θ` into the stage order. -/
def rowEmbedding {κ : Cardinal.{u}} {X : Type u}
    (Z : Stage κ → Set X) (hZ : ∀ θ, #(Z θ) ≤ κ) (θ : Stage κ) :
    Z θ ↪ Stage κ :=
  Classical.choice (nonempty_embedding_stage_of_mk_le (hZ θ))

/-- The partial row enumeration produced from the cardinal bounds
`#(Z θ) ≤ κ`. -/
def rowEnumeration {κ : Cardinal.{u}} {X : Type u}
    (Z : Stage κ → Set X) (hZ : ∀ θ, #(Z θ) ≤ κ) :
    Stage κ → Stage κ → Option X :=
  fun θ ↦ enumerateAlong (rowEmbedding Z hZ θ)

/-- The canonical partial enumeration covers every row. -/
theorem rowEnumeration_enumerates {κ : Cardinal.{u}} {X : Type u}
    (Z : Stage κ → Set X) (hZ : ∀ θ, #(Z θ) ≤ κ) :
    EnumeratesRows Z (rowEnumeration Z hZ) := by
  intro θ x hx
  let xs : Z θ := ⟨x, hx⟩
  exact ⟨rowEmbedding Z hZ θ xs,
    enumerateAlong_apply (rowEmbedding Z hZ θ) xs⟩

@[simp]
theorem mem_rowUnion {κ : Cardinal.{u}} {X : Type u}
    {Z : Stage κ → Set X} {x : X} :
    x ∈ rowUnion Z ↔ ∃ θ, x ∈ Z θ := by
  simp [rowUnion]

@[simp]
theorem mem_diagonalSlice {κ : Cardinal.{u}} {X : Type u}
    {row : Stage κ → Stage κ → Option X} {α : Stage κ} {x : X} :
    x ∈ diagonalSlice row α ↔
      ∃ θ γ, θ < α ∧ γ < α ∧ row θ γ = some x :=
  Iff.rfl

theorem diagonalSlice_mono {κ : Cardinal.{u}} {X : Type u}
    (row : Stage κ → Stage κ → Option X) {α β : Stage κ} (hαβ : α ≤ β) :
    diagonalSlice row α ⊆ diagonalSlice row β := by
  rintro x ⟨θ, γ, hθα, hγα, hx⟩
  exact ⟨θ, γ, hθα.trans_le hαβ, hγα.trans_le hαβ, hx⟩

/-- Assertion 9.13: every `< κ` subset of the row union is captured by a
single diagonal slice. -/
theorem exists_diagonalSlice_superset {κ : Cardinal.{u}} {X : Type u}
    (hκ : κ.IsRegular) {Z : Stage κ → Set X}
    {row : Stage κ → Stage κ → Option X} (hrow : EnumeratesRows Z row)
    {U : Set X} (hUZ : U ⊆ rowUnion Z) (hU : #U < κ) :
    ∃ α : Stage κ, U ⊆ diagonalSlice row α := by
  classical
  have hcoordinates : ∀ x : U,
      ∃ θ γ : Stage κ, x.1 ∈ Z θ ∧ row θ γ = some x.1 := by
    intro x
    obtain ⟨θ, hxθ⟩ := mem_rowUnion.mp (hUZ x.2)
    obtain ⟨γ, hγ⟩ := hrow θ x.1 hxθ
    exact ⟨θ, γ, hxθ, hγ⟩
  choose θ γ hxθ hγ using hcoordinates
  let bound : U → Ordinal.{u} := fun x ↦ max (θ x).1 (γ x).1
  have hbound : ∀ x, bound x < κ.ord := by
    intro x
    exact max_lt (θ x).2 (γ x).2
  have hsup : iSup (fun x ↦ bound x + 1) < κ.ord :=
    Stationary.iSup_add_one_lt_ord_of_lt hκ hU hbound
  let α : Stage κ := ⟨iSup (fun x ↦ bound x + 1), hsup⟩
  refine ⟨α, ?_⟩
  intro x hxU
  let xu : U := ⟨x, hxU⟩
  have hθbound : (θ xu).1 < bound xu + 1 := by
    exact lt_of_le_of_lt (le_max_left _ _) (lt_succ _)
  have hγbound : (γ xu).1 < bound xu + 1 := by
    exact lt_of_le_of_lt (le_max_right _ _) (lt_succ _)
  have hterm : bound xu + 1 ≤ iSup (fun y ↦ bound y + 1) :=
    Ordinal.le_iSup (fun y ↦ bound y + 1) xu
  exact ⟨θ xu, γ xu, hθbound.trans_le hterm,
    hγbound.trans_le hterm, hγ xu⟩

/-- Assertion 9.13 directly from the source's row-cardinality hypothesis. -/
theorem exists_diagonalSlice_superset_of_mk_le
    {κ : Cardinal.{u}} {X : Type u} (hκ : κ.IsRegular)
    {Z : Stage κ → Set X} (hZ : ∀ θ, #(Z θ) ≤ κ)
    {U : Set X} (hUZ : U ⊆ rowUnion Z) (hU : #U < κ) :
    ∃ α : Stage κ, U ⊆ diagonalSlice (rowEnumeration Z hZ) α :=
  exists_diagonalSlice_superset hκ (rowEnumeration_enumerates Z hZ) hUZ hU

/-- Club-strengthened 9.13.  After obtaining a diagonal bound, move to a
strictly later point of the prescribed club; monotonicity retains all
captured objects. -/
theorem exists_mem_club_diagonalSlice_superset {κ : Cardinal.{u}}
    {X : Type u} (hκ : κ.IsRegular) {C : Set (Stage κ)}
    (hC : Stationary.IsClubBelow κ C) {Z : Stage κ → Set X}
    {row : Stage κ → Stage κ → Option X} (hrow : EnumeratesRows Z row)
    {U : Set X} (hUZ : U ⊆ rowUnion Z) (hU : #U < κ) :
    ∃ α ∈ C, U ⊆ diagonalSlice row α := by
  obtain ⟨β, hUβ⟩ := exists_diagonalSlice_superset hκ hrow hUZ hU
  let α := nextInClub hκ C hC β
  exact ⟨α, nextInClub_mem hκ C hC β,
    hUβ.trans (diagonalSlice_mono row (lt_nextInClub hκ C hC β).le)⟩

/-- Club-strengthened diagonal capture above an additional prescribed
stage.  This is the form used when the current frontier is already fixed. -/
theorem exists_mem_club_diagonalSlice_superset_above
    {κ : Cardinal.{u}} {X : Type u} (hκ : κ.IsRegular)
    {C : Set (Stage κ)} (hC : Stationary.IsClubBelow κ C)
    {Z : Stage κ → Set X} {row : Stage κ → Stage κ → Option X}
    (hrow : EnumeratesRows Z row) {U : Set X}
    (hUZ : U ⊆ rowUnion Z) (hU : #U < κ) (a : Stage κ) :
    ∃ α ∈ C, a < α ∧ U ⊆ diagonalSlice row α := by
  obtain ⟨β, hUβ⟩ := exists_diagonalSlice_superset hκ hrow hUZ hU
  let α := aboveInClub hκ C hC a β
  refine ⟨α, aboveInClub_mem hκ C hC a β,
    left_lt_aboveInClub hκ C hC a β, ?_⟩
  exact hUβ.trans
    (diagonalSlice_mono row (right_lt_aboveInClub hκ C hC a β).le)

/-- The directly usable club form of 9.13: cardinally bounded rows, a
`< κ` request, and a current stage produce a later diagonal club stage. -/
theorem exists_mem_club_diagonalSlice_superset_above_of_mk_le
    {κ : Cardinal.{u}} {X : Type u} (hκ : κ.IsRegular)
    {C : Set (Stage κ)} (hC : Stationary.IsClubBelow κ C)
    {Z : Stage κ → Set X} (hZ : ∀ θ, #(Z θ) ≤ κ)
    {U : Set X} (hUZ : U ⊆ rowUnion Z) (hU : #U < κ)
    (a : Stage κ) :
    ∃ α ∈ C, a < α ∧ U ⊆ diagonalSlice (rowEnumeration Z hZ) α :=
  exists_mem_club_diagonalSlice_superset_above hκ hC
    (rowEnumeration_enumerates Z hZ) hUZ hU a

/-! ## Roof closure (Assertion 9.14) -/

/-- Every object inserted in row `Z θ` is already roofed at some (possibly
later) ladder stage.  This is the local, graph-parameterized premise of
Assertion 9.14. -/
def EventuallyIn {κ : Cardinal.{u}} {X : Type u}
    (roof : Stage κ → Set X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∃ β, x ∈ roof β

/-- If every row is eventually roofed, their union is contained in the
limiting roof.  This is exactly the set-theoretic conclusion of 9.14; the
proof that each kind of object added by recursion is eventually roofed is
left to the corresponding web lemma. -/
theorem rowUnion_subset_iUnion_of_eventuallyIn
    {κ : Cardinal.{u}} {X : Type u} {Z roof : Stage κ → Set X}
    (hZ : ∀ θ, EventuallyIn roof (Z θ)) :
    rowUnion Z ⊆ ⋃ β, roof β := by
  intro x hx
  obtain ⟨θ, hxθ⟩ := mem_rowUnion.mp hx
  obtain ⟨β, hxβ⟩ := hZ θ x hxθ
  exact Set.mem_iUnion.2 ⟨β, hxβ⟩

/-- A frequently used monotone specialization of 9.14: objects put in row
`θ` are roofed by one specified later stage. -/
theorem rowUnion_subset_iUnion_of_stagewise
    {κ : Cardinal.{u}} {X : Type u} {Z roof : Stage κ → Set X}
    (later : Stage κ → Stage κ) (hZ : ∀ θ, Z θ ⊆ roof (later θ)) :
    rowUnion Z ⊆ ⋃ β, roof β :=
  rowUnion_subset_iUnion_of_eventuallyIn fun θ _x hx ↦
    ⟨later θ, hZ θ hx⟩

/-! ## The parameterized slice interface (Assertion 9.15) -/

/-- The graph-theoretic payload of a controlled slice.

`Good L α β U` says that `L` is a `T_α`--`T_β` linkage which links `U`
to the final target.  The remaining conjuncts state that its maverick
subfamily has cardinality `< κ` and every vertex on a maverick lies in the
closing-up set `Z`.
No existence theorem is stored in this definition. -/
def maverickVertexSet {Link Maverick V : Type u}
    (mavericks : Link → Set Maverick) (support : Maverick → Set V)
    (L : Link) : Set V :=
  ⋃ p ∈ mavericks L, support p

def IsControlledSlice {κ : Cardinal.{u}} {V Link Maverick : Type u}
    (Good : Link → Stage κ → Stage κ → Set V → Prop)
    (mavericks : Link → Set Maverick) (support : Maverick → Set V)
    (Z : Set V)
    (α β : Stage κ) (U : Set V) (L : Link) : Prop :=
  Good L α β U ∧ #(mavericks L) < κ ∧
    maverickVertexSet mavericks support L ⊆ Z

/-- Assertion 9.15, parameterized only by the concrete web predicates that
the cardinal layer must not define. -/
def HasControlledSlices {κ : Cardinal.{u}} {V Link Maverick : Type u}
    (C : Set (Stage κ)) (frontier : Stage κ → Set V) (Z : Set V)
    (Good : Link → Stage κ → Stage κ → Set V → Prop)
    (mavericks : Link → Set Maverick) (support : Maverick → Set V) : Prop :=
  ∀ α ∈ C, ∀ U : Set V, U ⊆ frontier α ∩ Z → #U < κ →
    ∃ β ∈ C, α < β ∧
      ∃ L, IsControlledSlice Good mavericks support Z α β U L

/-- The next stage chosen from a 9.15 slice witness. -/
def controlledNext {κ : Cardinal.{u}} {V Link Maverick : Type u}
    {C : Set (Stage κ)} {frontier : Stage κ → Set V} {Z : Set V}
    {Good : Link → Stage κ → Stage κ → Set V → Prop}
    {mavericks : Link → Set Maverick} {support : Maverick → Set V}
    (hslice : HasControlledSlices C frontier Z Good mavericks support)
    (α : Stage κ) (hα : α ∈ C) (U : Set V)
    (hUsub : U ⊆ frontier α ∩ Z) (hU : #U < κ) : Stage κ :=
  Classical.choose (hslice α hα U hUsub hU)

@[simp]
theorem controlledNext_mem {κ : Cardinal.{u}} {V Link Maverick : Type u}
    {C : Set (Stage κ)} {frontier : Stage κ → Set V} {Z : Set V}
    {Good : Link → Stage κ → Stage κ → Set V → Prop}
    {mavericks : Link → Set Maverick} {support : Maverick → Set V}
    (hslice : HasControlledSlices C frontier Z Good mavericks support)
    (α : Stage κ) (hα : α ∈ C) (U : Set V)
    (hUsub : U ⊆ frontier α ∩ Z) (hU : #U < κ) :
    controlledNext hslice α hα U hUsub hU ∈ C :=
  (Classical.choose_spec (hslice α hα U hUsub hU)).1

theorem lt_controlledNext {κ : Cardinal.{u}} {V Link Maverick : Type u}
    {C : Set (Stage κ)} {frontier : Stage κ → Set V} {Z : Set V}
    {Good : Link → Stage κ → Stage κ → Set V → Prop}
    {mavericks : Link → Set Maverick} {support : Maverick → Set V}
    (hslice : HasControlledSlices C frontier Z Good mavericks support)
    (α : Stage κ) (hα : α ∈ C) (U : Set V)
    (hUsub : U ⊆ frontier α ∩ Z) (hU : #U < κ) :
    α < controlledNext hslice α hα U hUsub hU :=
  (Classical.choose_spec (hslice α hα U hUsub hU)).2.1

/-- The linkage chosen together with `controlledNext`. -/
def controlledLink {κ : Cardinal.{u}} {V Link Maverick : Type u}
    {C : Set (Stage κ)} {frontier : Stage κ → Set V} {Z : Set V}
    {Good : Link → Stage κ → Stage κ → Set V → Prop}
    {mavericks : Link → Set Maverick} {support : Maverick → Set V}
    (hslice : HasControlledSlices C frontier Z Good mavericks support)
    (α : Stage κ) (hα : α ∈ C) (U : Set V)
    (hUsub : U ⊆ frontier α ∩ Z) (hU : #U < κ) : Link :=
  Classical.choose
    (Classical.choose_spec (hslice α hα U hUsub hU)).2.2

theorem controlledLink_spec {κ : Cardinal.{u}} {V Link Maverick : Type u}
    {C : Set (Stage κ)} {frontier : Stage κ → Set V} {Z : Set V}
    {Good : Link → Stage κ → Stage κ → Set V → Prop}
    {mavericks : Link → Set Maverick} {support : Maverick → Set V}
    (hslice : HasControlledSlices C frontier Z Good mavericks support)
    (α : Stage κ) (hα : α ∈ C) (U : Set V)
    (hUsub : U ⊆ frontier α ∩ Z) (hU : #U < κ) :
    IsControlledSlice Good mavericks support Z α
      (controlledNext hslice α hα U hUsub hU) U
      (controlledLink hslice α hα U hUsub hU) :=
  Classical.choose_spec
    (Classical.choose_spec (hslice α hα U hUsub hU)).2.2

end RegularCardinal
end Erdos599
