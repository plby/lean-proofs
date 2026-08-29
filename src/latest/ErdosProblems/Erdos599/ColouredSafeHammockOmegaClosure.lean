/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeHammockClosure

/-!
# Simultaneous small closure under native safe-occurrence hammocks

For a fixed reference warp and a fixed per-source route filter, this file
closes a small vertex set under the actual maximal-up-to native hammocks at
every endpoint pair which enters the set. Both the ordinary hammock and,
at finite endpoints, the relationally
nondegenerate hammock are selected.  Countability of each occurrence carrier
and an omega iteration keep the resulting set small.

This is only a static carrier closure.  It does not assert moving-reference,
roof, source, or endpoint membership facts needed by later applications.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeHammockOmegaClosure

open Cardinal Set Order DirectedPath
open ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Simultaneous closure at every currently present source, at the infinite
endpoint, and at every currently present finite endpoint.  The second finite
closure retains the native relational nondegeneracy filter. -/
def FilteredOmegaClosed (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u}) (Z : Set V) : Prop :=
  (∀ s, s ∈ Z →
    ColouredSafeHammock.ClosedAt Y s none (extra s) rho Z) /\
  (∀ s, s ∈ Z → ∀ t, t ∈ Z →
    ColouredSafeHammock.ClosedAt Y s (some t) (extra s) rho Z /\
    ColouredSafeHammock.ClosedAt Y s (some t)
      (fun A => extra s A ∧ ¬A.HasFiniteSwitchedPathTo t) rho Z)

/-- A fixed actual ordinary maximal-up-to family for one endpoint pair. -/
def chosenOrdinaryFamily (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (s : V) (e : Option V) : Set (Occurrence Y s) :=
  Classical.choose
    (ColouredSafeHammock.exists_maximalUpTo Y s e (extra s) rho)

theorem chosenOrdinaryFamily_spec (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (s : V) (e : Option V) :
    MaximalUpTo
      {K | ColouredSafeHammock.Hammock Y s e (extra s) K} rho
      (chosenOrdinaryFamily Y extra rho s e) :=
  Classical.choose_spec
    (ColouredSafeHammock.exists_maximalUpTo Y s e (extra s) rho)

/-- A fixed actual maximal-up-to family of finite occurrences which do not
already have a finite switched path to their displayed endpoint. -/
def chosenNondegenerateFamily (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (s t : V) : Set (Occurrence Y s) :=
  Classical.choose (ColouredSafeHammock.exists_maximalUpTo Y s (some t)
    (fun A => extra s A ∧ ¬A.HasFiniteSwitchedPathTo t) rho)

theorem chosenNondegenerateFamily_spec
    (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u}) (s t : V) :
    MaximalUpTo
      {K | ColouredSafeHammock.Hammock Y s (some t)
        (fun A => extra s A ∧ ¬A.HasFiniteSwitchedPathTo t) K} rho
      (chosenNondegenerateFamily Y extra rho s t) :=
  Classical.choose_spec (ColouredSafeHammock.exists_maximalUpTo Y s (some t)
    (fun A => extra s A ∧ ¬A.HasFiniteSwitchedPathTo t) rho)

/-- The union of the literal carriers of an occurrence family. -/
def familyVertices {Y : Set Gamma.DPath} {s : V}
    (H : Set (Occurrence Y s)) : Set V :=
  ⋃ A : H, A.1.vertexSet

private theorem mk_iUnion_le_of_le {I X : Type u} {f : I → Set X}
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) (hI : #I ≤ rho)
    (hf : ∀ i, #(f i) ≤ rho) : #(⋃ i, f i) ≤ rho := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hrho hI (ciSup_le' hf)

theorem mk_familyVertices_le {Y : Set Gamma.DPath} {s : V}
    {rho : Cardinal.{u}} {H : Set (Occurrence Y s)}
    (hrho : aleph0 ≤ rho)
    (hH : #H ≤ rho) : #(familyVertices H) ≤ rho := by
  apply mk_iUnion_le_of_le hrho hH
  intro A
  exact A.1.vertexSet_countable.le_aleph0.trans hrho

/-- Carriers selected at the infinite endpoint for all sources in `X`. -/
def ordinaryNoneVertices (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (X : Set V) : Set V :=
  ⋃ s : X, familyVertices (chosenOrdinaryFamily Y extra rho s.1 none)

/-- Carriers selected at every finite endpoint pair in `X`. -/
def ordinarySomeVertices (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (X : Set V) : Set V :=
  ⋃ s : X, ⋃ t : X,
    familyVertices (chosenOrdinaryFamily Y extra rho s.1 (some t.1))

/-- Carriers selected at every finite endpoint pair in `X`, with the native
nondegeneracy filter. -/
def nondegenerateVertices (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (X : Set V) : Set V :=
  ⋃ s : X, ⋃ t : X,
    familyVertices (chosenNondegenerateFamily Y extra rho s.1 t.1)

/-- One simultaneous closing step. -/
def closingStep (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (X : Set V) : Set V :=
  ((X ∪ ordinaryNoneVertices Y extra rho X) ∪
    ordinarySomeVertices Y extra rho X) ∪ nondegenerateVertices Y extra rho X

/-- Finite stages of the native hammock closing process. -/
def closureStage (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (X0 : Set V) : Nat → Set V
  | 0 => X0
  | n + 1 => closingStep Y extra rho (closureStage Y extra rho X0 n)

/-- The union of all finite native-hammock closing stages. -/
def omegaClosure (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (X0 : Set V) : Set V :=
  ⋃ n, closureStage Y extra rho X0 n

theorem subset_closingStep (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (X : Set V) : X ⊆ closingStep Y extra rho X := by
  intro x hx
  exact Or.inl (Or.inl (Or.inl hx))

theorem closureStage_mono (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop) (rho : Cardinal.{u})
    (X0 : Set V) : Monotone (closureStage Y extra rho X0) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_closingStep Y extra rho (closureStage Y extra rho X0 n)

theorem closureStage_subset_omegaClosure (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop)
    (rho : Cardinal.{u}) (X0 : Set V) (n : Nat) :
    closureStage Y extra rho X0 n ⊆ omegaClosure Y extra rho X0 :=
  Set.subset_iUnion _ n

private theorem mk_union_le_of_le {rho : Cardinal.{u}} {A B : Set V}
    (hrho : aleph0 ≤ rho) (hA : #A ≤ rho) (hB : #B ≤ rho) :
    #(A ∪ B : Set V) ≤ rho :=
  (Cardinal.mk_union_le A B).trans
    (Cardinal.add_le_of_le hrho hA hB)

theorem mk_ordinaryNoneVertices_le (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {X : Set V}
    (hX : #X ≤ rho) : #(ordinaryNoneVertices Y extra rho X) ≤ rho := by
  apply mk_iUnion_le_of_le hrho hX
  intro s
  exact mk_familyVertices_le hrho
    (MaximalUpTo.card_le (chosenOrdinaryFamily_spec Y extra rho s.1 none))

theorem mk_ordinarySomeVertices_le (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {X : Set V}
    (hX : #X ≤ rho) : #(ordinarySomeVertices Y extra rho X) ≤ rho := by
  apply mk_iUnion_le_of_le hrho hX
  intro s
  apply mk_iUnion_le_of_le hrho hX
  intro t
  exact mk_familyVertices_le hrho
    (MaximalUpTo.card_le
      (chosenOrdinaryFamily_spec Y extra rho s.1 (some t.1)))

theorem mk_nondegenerateVertices_le (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {X : Set V}
    (hX : #X ≤ rho) : #(nondegenerateVertices Y extra rho X) ≤ rho := by
  apply mk_iUnion_le_of_le hrho hX
  intro s
  apply mk_iUnion_le_of_le hrho hX
  intro t
  exact mk_familyVertices_le hrho
    (MaximalUpTo.card_le
      (chosenNondegenerateFamily_spec Y extra rho s.1 t.1))

theorem mk_closingStep_le (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {X : Set V}
    (hX : #X ≤ rho) : #(closingStep Y extra rho X) ≤ rho := by
  apply mk_union_le_of_le hrho
  · apply mk_union_le_of_le hrho
    · exact mk_union_le_of_le hrho hX
        (mk_ordinaryNoneVertices_le Y extra hrho hX)
    · exact mk_ordinarySomeVertices_le Y extra hrho hX
  · exact mk_nondegenerateVertices_le Y extra hrho hX

theorem mk_closureStage_le (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {X0 : Set V}
    (hX0 : #X0 ≤ rho) : ∀ n, #(closureStage Y extra rho X0 n) ≤ rho
  | 0 => hX0
  | n + 1 => mk_closingStep_le Y extra hrho (mk_closureStage_le Y extra hrho hX0 n)

/-- An infinite cardinal supports a simultaneous omega closure under all
ordinary native hammocks and all finite relationally nondegenerate native
hammocks.  Switching applications may separately assume that `Y` is an
honest finite-character warp; the static selection itself does not need it. -/
theorem exists_filteredOmegaClosed_superset (Y : Set Gamma.DPath)
    (extra : ∀ s, Occurrence Y s → Prop)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {X0 : Set V}
    (hX0 : #X0 ≤ rho) :
    ∃ Z : Set V, X0 ⊆ Z ∧ #Z ≤ rho ∧ FilteredOmegaClosed Y extra rho Z := by
  let Z := omegaClosure Y extra rho X0
  have hstageCard : ∀ n, #(closureStage Y extra rho X0 n) ≤ rho :=
    mk_closureStage_le Y extra hrho hX0
  have hZcard : #Z ≤ rho := by
    change #(⋃ n, closureStage Y extra rho X0 n) ≤ rho
    let stages : ULift.{u} Nat → Set V := fun n => closureStage Y extra rho X0 n.down
    have heq : (⋃ n, closureStage Y extra rho X0 n) = ⋃ i, stages i := by
      ext x
      simp [stages]
    rw [heq]
    apply mk_iUnion_le_of_le hrho
    · simpa [Cardinal.mk_nat] using hrho
    · intro i
      exact hstageCard i.down
  have hmono : Monotone (closureStage Y extra rho X0) :=
    closureStage_mono Y extra rho X0
  have hclosed : FilteredOmegaClosed Y extra rho Z := by
    constructor
    · intro s hs
      obtain ⟨n, hsn⟩ := Set.mem_iUnion.1 hs
      refine ⟨chosenOrdinaryFamily Y extra rho s none,
        chosenOrdinaryFamily_spec Y extra rho s none, ?_⟩
      intro A hA x hx
      apply closureStage_subset_omegaClosure Y extra rho X0 (n + 1)
      exact Or.inl (Or.inl (Or.inr
        (Set.mem_iUnion.2 ⟨⟨s, hsn⟩,
          Set.mem_iUnion.2 ⟨⟨A, hA⟩, hx⟩⟩)))
    · intro s hs t ht
      obtain ⟨ns, hsns⟩ := Set.mem_iUnion.1 hs
      obtain ⟨nt, htnt⟩ := Set.mem_iUnion.1 ht
      let n := max ns nt
      have hsn : s ∈ closureStage Y extra rho X0 n :=
        hmono (Nat.le_max_left ns nt) hsns
      have htn : t ∈ closureStage Y extra rho X0 n :=
        hmono (Nat.le_max_right ns nt) htnt
      constructor
      · refine ⟨chosenOrdinaryFamily Y extra rho s (some t),
          chosenOrdinaryFamily_spec Y extra rho s (some t), ?_⟩
        intro A hA x hx
        apply closureStage_subset_omegaClosure Y extra rho X0 (n + 1)
        exact Or.inl (Or.inr
          (Set.mem_iUnion.2 ⟨⟨s, hsn⟩,
            Set.mem_iUnion.2 ⟨⟨t, htn⟩,
              Set.mem_iUnion.2 ⟨⟨A, hA⟩, hx⟩⟩⟩))
      · refine ⟨chosenNondegenerateFamily Y extra rho s t,
          chosenNondegenerateFamily_spec Y extra rho s t, ?_⟩
        intro A hA x hx
        apply closureStage_subset_omegaClosure Y extra rho X0 (n + 1)
        exact Or.inr
          (Set.mem_iUnion.2 ⟨⟨s, hsn⟩,
            Set.mem_iUnion.2 ⟨⟨t, htn⟩,
              Set.mem_iUnion.2 ⟨⟨A, hA⟩, hx⟩⟩⟩)
  refine ⟨Z, ?_, hZcard, hclosed⟩
  exact closureStage_subset_omegaClosure Y extra rho X0 0

#print axioms exists_filteredOmegaClosed_superset

/-- A genuine carrier filter permits restriction to its prescribed region
without changing any of the selected maximal families. -/
theorem FilteredOmegaClosed.inter_of_extra_subset
    {Y : Set Gamma.DPath} {extra : ∀ s, Occurrence Y s → Prop}
    {rho : Cardinal.{u}} {X R : Set V}
    (hclosed : FilteredOmegaClosed Y extra rho X)
    (hR : ∀ s A, extra s A → A.vertexSet ⊆ R) :
    FilteredOmegaClosed Y extra rho (X ∩ R) := by
  constructor
  · intro s hs
    exact (hclosed.1 s hs.1).inter_of_extra_subset (hR s)
  · intro s hs t ht
    have hpair := hclosed.2 s hs.1 t ht.1
    exact ⟨hpair.1.inter_of_extra_subset (hR s),
      hpair.2.inter_of_extra_subset (fun A hA ↦ hR s A hA.1)⟩

/-- Small simultaneous closure inside an actual region, when every route
allowed by the filter lies there. No roof containment is postulated for an
unfiltered maximal family. -/
theorem exists_filteredOmegaClosed_superset_within
    (Y : Set Gamma.DPath) (extra : ∀ s, Occurrence Y s → Prop)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {X0 R : Set V}
    (hX0 : #X0 ≤ rho) (hX0R : X0 ⊆ R)
    (hR : ∀ s A, extra s A → A.vertexSet ⊆ R) :
    ∃ Z : Set V, X0 ⊆ Z ∧ #Z ≤ rho ∧ Z ⊆ R ∧
      FilteredOmegaClosed Y extra rho Z := by
  obtain ⟨X, hsub, hcard, hclosed⟩ :=
    exists_filteredOmegaClosed_superset Y extra hrho hX0
  refine ⟨X ∩ R, fun x hx ↦ ⟨hsub hx, hX0R hx⟩,
    (Cardinal.mk_subtype_mono Set.inter_subset_left).trans hcard,
    Set.inter_subset_right, hclosed.inter_of_extra_subset hR⟩

#print axioms exists_filteredOmegaClosed_superset_within

/-- Increasing countable unions retain simultaneous pair closure: both
endpoints occur together in one approximation. -/
theorem FilteredOmegaClosed.iUnion_nat
    {Y : Set Gamma.DPath} {extra : ∀ s, Occurrence Y s → Prop}
    {rho : Cardinal.{u}} {X : Nat → Set V}
    (hmono : Monotone X) (hclosed : ∀ n, FilteredOmegaClosed Y extra rho (X n)) :
    FilteredOmegaClosed Y extra rho (⋃ n, X n) := by
  constructor
  · intro s hs
    obtain ⟨n, hsn⟩ := Set.mem_iUnion.mp hs
    exact ((hclosed n).1 s hsn).mono (Set.subset_iUnion X n)
  · intro s hs t ht
    obtain ⟨ns, hsn⟩ := Set.mem_iUnion.mp hs
    obtain ⟨nt, htn⟩ := Set.mem_iUnion.mp ht
    have hpair := (hclosed (max ns nt)).2 s
      (hmono (Nat.le_max_left ns nt) hsn) t (hmono (Nat.le_max_right ns nt) htn)
    exact ⟨hpair.1.mono (Set.subset_iUnion X (max ns nt)),
      hpair.2.mono (Set.subset_iUnion X (max ns nt))⟩

/-- Unfiltered specialization retained for ordinary native shortcuts. -/
def OmegaClosed (Y : Set Gamma.DPath) (rho : Cardinal.{u}) (Z : Set V) : Prop :=
  (∀ s, s ∈ Z →
    ColouredSafeHammock.ClosedAt Y s none (fun _ => True) rho Z) /\
  (∀ s, s ∈ Z → ∀ t, t ∈ Z →
    ColouredSafeHammock.ClosedAt Y s (some t) (fun _ => True) rho Z /\
    ColouredSafeHammock.ClosedAt Y s (some t)
      (fun A => ¬A.HasFiniteSwitchedPathTo t) rho Z)

theorem exists_omegaClosed_superset (Y : Set Gamma.DPath)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {X0 : Set V}
    (hX0 : #X0 ≤ rho) :
    ∃ Z : Set V, X0 ⊆ Z ∧ #Z ≤ rho ∧ OmegaClosed Y rho Z := by
  obtain ⟨Z, hsub, hcard, hclosed⟩ :=
    exists_filteredOmegaClosed_superset Y (fun _ _ => True) hrho hX0
  exact ⟨Z, hsub, hcard, by
    simpa only [FilteredOmegaClosed, OmegaClosed, true_and] using hclosed⟩

#print axioms exists_omegaClosed_superset

end Erdos599.Blueprint.ColouredSafeHammockOmegaClosure
