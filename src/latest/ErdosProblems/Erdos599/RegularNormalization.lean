/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction

/-!
# Transporting the extension clause through normalization

An `A`--`B` linkage in an arbitrary web need not remain source-starting
after the web is normalized: the canonical normalized subpath starts at the
last source on the old path.  This file records the accompanying exchange of
exceptional source vertices.  Disjointness of the old linkage makes the
exchange cardinality preserving.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

universe u

open DirectedPath

variable {V : Type u} {Γ : DWeb V} {A₀ : Set V}
    {F : Set Γ.DPath}

namespace RegularNormalization

variable (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)

/-- The finite path underlying a member of the given linkage. -/
abbrev oldPath (p : F) : DirectedPath.FinitePath Γ.graph :=
  Γ.finiteMemberPath F hF.finiteCharacter p

@[simp] theorem oldPath_eq (p : F) :
    p.1 = (.inl (oldPath hF p) : Γ.DPath) :=
  Γ.finiteMemberPath_eq F hF.finiteCharacter p

theorem oldStart_mem (p : F) :
    (oldPath hF p).start ∈ Γ.source \ A₀ := by
  have hp : p.1.initial ∈ Γ.initialSet F := ⟨p.1, p.2, rfl⟩
  rw [hF.initialSet_eq] at hp
  rw [oldPath_eq hF p] at hp
  exact hp

theorem oldFinish_mem (p : F) :
    (oldPath hF p).finish ∈ Γ.target := by
  apply hF.terminalFrontier_subset
  refine ⟨p.1, p.2, ?_⟩
  simp [oldPath_eq hF p]

/-- The canonical normalized subpath associated to an old linkage member. -/
def newPath (p : F) : DirectedPath.FinitePath Γ.normalized.graph :=
  Γ.normalizeFinitePath (oldPath hF p) (oldStart_mem hF p).1
    (oldFinish_mem hF p)

@[simp] theorem newStart_mem (p : F) :
    (newPath hF p).start ∈ Γ.source :=
  Γ.normalizeFinitePath_start_mem (oldPath hF p) (oldStart_mem hF p).1
    (oldFinish_mem hF p)

@[simp] theorem newFinish_mem (p : F) :
    (newPath hF p).finish ∈ Γ.target :=
  Γ.normalizeFinitePath_finish_mem (oldPath hF p) (oldStart_mem hF p).1
    (oldFinish_mem hF p)

theorem newSupport_subset (p : F) :
    (newPath hF p).support ⊆ p.1.support := by
  intro x hx
  rw [oldPath_eq hF p]
  exact Γ.normalizeFinitePath_support_subset (oldPath hF p)
    (oldStart_mem hF p).1 (oldFinish_mem hF p) hx

/-- The normalized family obtained by truncating every old member. -/
def newFamily : Set Γ.normalized.DPath :=
  Set.range (fun p : F ↦ (.inl (newPath hF p) : Γ.normalized.DPath))

theorem newFamily_isWarp : Γ.normalized.IsWarp (newFamily hF) := by
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
  apply Set.disjoint_left.2
  intro x hxp hxq
  have hxp' : x ∈ p.1.support := newSupport_subset hF p hxp
  have hxq' : x ∈ q.1.support := newSupport_subset hF q hxq
  have hpqval : p.1 = q.1 := by
    by_contra hne
    exact Set.disjoint_left.1 (hF.isWarp p.2 q.2 hne) hxp' hxq'
  have hpqsub : p = q := Subtype.ext hpqval
  subst q
  exact hpq rfl

theorem newFamily_finiteCharacter :
    Γ.normalized.HasFiniteCharacter (newFamily hF) := by
  rintro _ ⟨p, rfl⟩
  exact ⟨newPath hF p, rfl⟩

theorem newInitialSet_subset_source :
    Γ.normalized.initialSet (newFamily hF) ⊆ Γ.source := by
  rintro x ⟨_, ⟨p, rfl⟩, rfl⟩
  exact newStart_mem hF p

theorem newTerminalFrontier_subset_target :
    Γ.normalized.terminalFrontier (newFamily hF) ⊆ Γ.target := by
  rintro x ⟨_, ⟨p, rfl⟩, hx⟩
  have hxeq : (newPath hF p).finish = x := Option.some.inj hx
  exact hxeq ▸ newFinish_mem hF p

theorem newPath_isPathBetween (p : F) :
    IsPathBetween Γ.normalized
      (Γ.normalized.initialSet (newFamily hF)) Γ.target
      (.inl (newPath hF p) : Γ.normalized.DPath) := by
  refine ⟨newPath hF p, rfl, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxs, hx⟩
      rcases hx with hx | hx
      · have hxsource : x ∈ Γ.normalized.source :=
          newInitialSet_subset_source hF hx
        have hxeq := DWeb.IsNormalized.eq_start_of_mem_walk
          (Γ := Γ.normalized) Γ.normalized_isNormalized
          (newPath hF p).walk hxs hxsource
        simp [hxeq]
      · have hxeq := DWeb.IsNormalized.eq_finish_of_mem_walk
          (Γ := Γ.normalized) Γ.normalized_isNormalized
          (newPath hF p).walk hxs hx
        simp [hxeq]
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨(newPath hF p).start_mem_support,
          Or.inl ⟨(.inl (newPath hF p) : Γ.normalized.DPath),
            ⟨p, rfl⟩, rfl⟩⟩
      · have hxeq : x = (newPath hF p).finish := by simpa using hx
        subst x
        exact ⟨(newPath hF p).finish_mem_support,
          Or.inr (newFinish_mem hF p)⟩
  · ext x
    constructor
    · rintro ⟨hxs, hxinitial⟩
      have hxsource : x ∈ Γ.normalized.source :=
        newInitialSet_subset_source hF hxinitial
      exact DWeb.IsNormalized.eq_start_of_mem_walk
        (Γ := Γ.normalized) Γ.normalized_isNormalized
        (newPath hF p).walk hxs hxsource
    · intro hx
      have hxeq : x = (newPath hF p).start := by simpa using hx
      subst x
      exact ⟨(newPath hF p).start_mem_support,
        ⟨(.inl (newPath hF p) : Γ.normalized.DPath),
          ⟨p, rfl⟩, rfl⟩⟩

theorem newFamily_isLinkage :
    IsLinkageBetween Γ.normalized
      (Γ.normalized.initialSet (newFamily hF)) Γ.target
      (newFamily hF) := by
  refine ⟨newFamily_isWarp hF, newFamily_finiteCharacter hF, rfl,
    newTerminalFrontier_subset_target hF, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact newPath_isPathBetween hF p

/-- The new exceptional set: source vertices not occupied by the new starts. -/
def newExceptional : Set V :=
  Γ.source \ Γ.normalized.initialSet (newFamily hF)

theorem newExceptional_subset_source : newExceptional hF ⊆ Γ.source :=
  fun _ hx ↦ hx.1

theorem newFamily_initialSet_eq :
    Γ.normalized.initialSet (newFamily hF) =
      Γ.normalized.source \ newExceptional hF := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨newInitialSet_subset_source hF hx, fun h ↦ h.2 hx⟩
  · rintro x ⟨hxsource, hxnot⟩
    by_contra hx
    exact hxnot ⟨hxsource, hx⟩

/-! ## Restriction after enlarging the exceptional set -/

/-- Keep exactly those normalized paths whose new initial vertex is not in
the enlarged exceptional set. -/
def restrictedFamily (E : Set V) : Set Γ.normalized.DPath :=
  {p | p ∈ newFamily hF ∧ p.initial ∉ E}

/-- Enlarging `newExceptional` only requires discarding the normalized
paths which start in the added vertices.  The retained paths are still an
exact linkage of the complementary normalized sources. -/
theorem restrictedFamily_isLinkage (E : Set V)
    (hnewE : newExceptional hF ⊆ E) :
    IsLinkageBetween Γ.normalized
      (Γ.normalized.source \ E) Γ.normalized.target
      (restrictedFamily hF E) := by
  have hnew := newFamily_isLinkage hF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    exact hnew.isWarp hp.1 hq.1 hpq
  · intro p hp
    exact hnew.finiteCharacter hp.1
  · ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hxsource : p.initial ∈ Γ.normalized.source := by
        have hx : p.initial ∈ Γ.normalized.initialSet (newFamily hF) :=
          ⟨p, hp.1, rfl⟩
        rw [newFamily_initialSet_eq hF] at hx
        exact hx.1
      exact ⟨hxsource, hp.2⟩
    · rintro ⟨hxsource, hxE⟩
      have hxnew : x ∈ Γ.normalized.initialSet (newFamily hF) := by
        rw [newFamily_initialSet_eq hF]
        exact ⟨hxsource, fun hx ↦ hxE (hnewE hx)⟩
      obtain ⟨p, hp, hpstart⟩ := hxnew
      refine ⟨p, ⟨hp, ?_⟩, hpstart⟩
      simpa only [hpstart] using hxE
  · intro x hx
    obtain ⟨p, hp, hpterm⟩ := hx
    exact hnew.terminalFrontier_subset ⟨p, hp.1, hpterm⟩
  · intro p hp
    obtain ⟨q, rfl, hends, hsource⟩ := hnew.endpointPure p hp.1
    have oldInitial_of_newSource {x : V}
        (hx : x ∈ Γ.normalized.source \ E) :
        x ∈ Γ.normalized.initialSet (newFamily hF) := by
      rw [newFamily_initialSet_eq hF]
      exact ⟨hx.1, fun hxnew ↦ hx.2 (hnewE hxnew)⟩
    have source_of_oldInitial {x : V}
        (hx : x ∈ Γ.normalized.initialSet (newFamily hF)) :
        x ∈ Γ.normalized.source := by
      rw [newFamily_initialSet_eq hF] at hx
      exact hx.1
    refine ⟨q, rfl, ?_, ?_⟩
    · rw [← hends]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
      constructor
      · rintro ⟨hxs, ⟨hxa, hxE⟩ | hxtarget⟩
        · exact ⟨hxs, Or.inl (oldInitial_of_newSource ⟨hxa, hxE⟩)⟩
        · exact ⟨hxs, Or.inr hxtarget⟩
      · rintro ⟨hxs, hxa | hxtarget⟩
        · have hxstart : x = q.start := by
            have hxold : x ∈ q.support ∩
                (Γ.normalized.initialSet (newFamily hF)) := ⟨hxs, hxa⟩
            rw [hsource] at hxold
            simpa only [Set.mem_singleton_iff] using hxold
          subst x
          exact ⟨q.start_mem_support,
            Or.inl ⟨source_of_oldInitial hxa, hp.2⟩⟩
        · exact ⟨hxs, Or.inr hxtarget⟩
    · rw [← hsource]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨hxs, hxa, hxE⟩
        exact ⟨hxs, oldInitial_of_newSource ⟨hxa, hxE⟩⟩
      · rintro ⟨hxs, hxa⟩
        have hxstart : x = q.start := by
          have hxold : x ∈ q.support ∩
              (Γ.normalized.initialSet (newFamily hF)) := ⟨hxs, hxa⟩
          rw [hsource] at hxold
          simpa only [Set.mem_singleton_iff] using hxold
        subst x
        exact ⟨q.start_mem_support, source_of_oldInitial hxa, hp.2⟩

/-! ## Cardinality of the exchanged exceptional set -/

theorem newStart_eq_oldStart_of_not_mem (p : F)
    (hp : (newPath hF p).start ∉ A₀) :
    (newPath hF p).start = (oldPath hF p).start := by
  rcases hF.endpointPure p.1 p.2 with ⟨q, hpq, _hends, hsource⟩
  have hq : q = oldPath hF p := by
    exact Sum.inl.inj (hpq.symm.trans (oldPath_eq hF p))
  subst q
  have hsupport' :=
    newSupport_subset hF p (newPath hF p).start_mem_support
  have hsupport : (newPath hF p).start ∈ (oldPath hF p).support := by
    rw [oldPath_eq hF p] at hsupport'
    exact hsupport'
  have hsingleton : (newPath hF p).start ∈
      ({(oldPath hF p).start} : Set V) := by
    rw [← hsource]
    exact ⟨hsupport, (newStart_mem hF p), hp⟩
  exact Set.mem_singleton_iff.mp hsingleton

theorem oldStart_injective : Function.Injective
    (fun p : F ↦ (oldPath hF p).start) := by
  intro p q hpq
  change (oldPath hF p).start = (oldPath hF q).start at hpq
  apply Subtype.ext
  by_contra hne
  have hpstart : (oldPath hF p).start ∈ p.1.support := by
    rw [oldPath_eq hF p]
    exact (oldPath hF p).start_mem_support
  have hqstart : (oldPath hF p).start ∈ q.1.support := by
    rw [oldPath_eq hF q]
    rw [hpq]
    exact (oldPath hF q).start_mem_support
  exact Set.disjoint_left.1 (hF.isWarp p.2 q.2 hne)
    hpstart hqstart

theorem newStart_injective : Function.Injective
    (fun p : F ↦ (newPath hF p).start) := by
  intro p q hpq
  change (newPath hF p).start = (newPath hF q).start at hpq
  apply Subtype.ext
  by_contra hne
  have hd := hF.isWarp p.2 q.2 hne
  have hqstart : (newPath hF p).start ∈ (newPath hF q).support := by
    rw [hpq]
    exact (newPath hF q).start_mem_support
  exact Set.disjoint_left.1 hd
    (newSupport_subset hF p (newPath hF p).start_mem_support)
    (newSupport_subset hF q hqstart)

theorem exists_oldOwner (x : newExceptional hF) (hx : x.1 ∉ A₀) :
    ∃ p : F, (oldPath hF p).start = x.1 := by
  have hxinit : x.1 ∈ Γ.initialSet F := by
    rw [hF.initialSet_eq]
    exact ⟨x.2.1, hx⟩
  obtain ⟨p, hpF, hpstart⟩ := hxinit
  let pF : F := ⟨p, hpF⟩
  refine ⟨pF, ?_⟩
  change pF.1.initial = x.1 at hpstart
  rw [oldPath_eq hF pF] at hpstart
  exact hpstart

noncomputable def oldOwner (x : newExceptional hF) (hx : x.1 ∉ A₀) : F :=
  Classical.choose (exists_oldOwner hF x hx)

@[simp] theorem oldOwner_start (x : newExceptional hF) (hx : x.1 ∉ A₀) :
    (oldPath hF (oldOwner hF x hx)).start = x.1 :=
  Classical.choose_spec (exists_oldOwner hF x hx)

theorem oldOwner_newStart_mem (x : newExceptional hF) (hx : x.1 ∉ A₀) :
    (newPath hF (oldOwner hF x hx)).start ∈ A₀ := by
  by_contra hnot
  have heq := newStart_eq_oldStart_of_not_mem hF (oldOwner hF x hx) hnot
  apply x.2.2
  refine ⟨(.inl (newPath hF (oldOwner hF x hx)) : Γ.normalized.DPath),
    ⟨oldOwner hF x hx, rfl⟩, ?_⟩
  change (newPath hF (oldOwner hF x hx)).start = x.1
  exact heq.trans (oldOwner_start hF x hx)

/-- Injection from the new exceptional set to the old one.  A source which
was already exceptional is fixed unless it is a new start; every lost old
start is sent to the new start of its unique path. -/
noncomputable def toOldExceptional (x : newExceptional hF) : A₀ := by
  classical
  by_cases hx : x.1 ∈ A₀
  · exact ⟨x.1, hx⟩
  · exact ⟨(newPath hF (oldOwner hF x hx)).start,
      oldOwner_newStart_mem hF x hx⟩

theorem toOldExceptional_injective :
    Function.Injective (toOldExceptional hF) := by
  classical
  intro x y hxy
  by_cases hx : x.1 ∈ A₀ <;> by_cases hy : y.1 ∈ A₀
  · apply Subtype.ext
    simpa [toOldExceptional, hx, hy] using congrArg Subtype.val hxy
  · have hval : x.1 = (newPath hF (oldOwner hF y hy)).start := by
      simpa [toOldExceptional, hx, hy] using congrArg Subtype.val hxy
    exfalso
    apply x.2.2
    refine ⟨(.inl (newPath hF (oldOwner hF y hy)) : Γ.normalized.DPath),
      ⟨oldOwner hF y hy, rfl⟩, ?_⟩
    exact hval.symm
  · have hval : (newPath hF (oldOwner hF x hx)).start = y.1 := by
      simpa [toOldExceptional, hx, hy] using congrArg Subtype.val hxy
    exfalso
    apply y.2.2
    refine ⟨(.inl (newPath hF (oldOwner hF x hx)) : Γ.normalized.DPath),
      ⟨oldOwner hF x hx, rfl⟩, ?_⟩
    exact hval
  · have hstarts :
        (newPath hF (oldOwner hF x hx)).start =
          (newPath hF (oldOwner hF y hy)).start := by
      simpa [toOldExceptional, hx, hy] using congrArg Subtype.val hxy
    have howners : oldOwner hF x hx = oldOwner hF y hy :=
      newStart_injective hF hstarts
    apply Subtype.ext
    rw [← oldOwner_start hF x hx, ← oldOwner_start hF y hy, howners]

/-! ## Transport of the extension clause -/

/-- The extension clause transports from the normalized web back to the
original web.  Normalizing the old complementary linkage may exchange some
of its source vertices with vertices of `A₀`.  Taking the union of the old
and new exceptional sets restores the exact cardinal `κ`; the preceding
restriction lemma supplies the complementary normalized linkage. -/
theorem extensionClauseAt_of_normalized
    (κ : Cardinal.{u}) (hκinf : ℵ₀ ≤ κ)
    (hnormalized : ExtensionClauseAt Γ.normalized κ) :
    ExtensionClauseAt Γ κ := by
  intro A₀ hA₀source hA₀card hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  let E : Set V := A₀ ∪ newExceptional hF
  have hnewCard : #(newExceptional hF) ≤ #A₀ :=
    Cardinal.mk_le_of_injective (toOldExceptional_injective hF)
  have hEcard : #E = κ := by
    apply le_antisymm
    · refine (Cardinal.mk_union_le A₀ (newExceptional hF)).trans ?_
      apply Cardinal.add_le_of_le hκinf
      · exact hA₀card.le
      · exact hnewCard.trans hA₀card.le
    · rw [← hA₀card]
      exact Cardinal.mk_subtype_mono Set.subset_union_left
  have hEsource : E ⊆ Γ.normalized.source := by
    rintro x (hx | hx)
    · exact hA₀source hx
    · exact (newExceptional_subset_source hF hx)
  have hrestricted : IsLinkageBetween Γ.normalized
      (Γ.normalized.source \ E) Γ.normalized.target
      (restrictedFamily hF E) := by
    apply restrictedFamily_isLinkage hF E
    exact Set.subset_union_right
  apply IsLinkable.of_normalized
  exact hnormalized E hEsource hEcard ⟨restrictedFamily hF E, hrestricted⟩

end RegularNormalization

end CardinalInduction
end Erdos599
