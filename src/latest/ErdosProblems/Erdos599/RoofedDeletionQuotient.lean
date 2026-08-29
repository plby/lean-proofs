/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkReducedProperties
import ErdosProblems.Erdos599.SingularExtension

/-!
# Deleting a roofed carrier before taking the stopover quotient

Deleting an arbitrary carrier may destroy unhinderedness.  If that carrier
is roofed by a trimmed separator `C`, its deletion *before quotienting by C*
is exactly deletion of its `C`-vertices from the old quotient.  Those are
sources of the old quotient, so its unhinderedness is preserved.

This is the protected quotient required by restoration, not an assertion of
unhinderedness for the whole deleted ambient web.  No bound on the deleted
set and no cardinal-induction hypothesis is required.
-/

namespace Erdos599.DWeb

open Set DirectedPath

universe u

variable {V : Type u} (G : DWeb V) {X C : Set V}

/-- A deletion contained in the roof cannot destroy a path avoiding the
boundary: every vertex of such a path is already outside that roof. -/
theorem delete_roof_eq_of_subset_roof (hX : X ⊆ G.roof C) :
    (G.delete X).roof C = G.roof C := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxOld
    obtain ⟨p, hp, hpAvoid⟩ := (G.not_mem_roof_iff C x).1 hxOld
    have havoid : SafeLink.Walk.Avoids p.walk X := by
      intro y hyp hyX
      exact RelationalRoof.not_mem_roof_of_mem_targetPath
        G.graph.Adj G.target (S := C) p hp
        (fun {_} hy hyC ↦ Set.disjoint_left.1 hpAvoid hy hyC)
        hyp (hX hyX)
    let q := SafeLink.FinitePath.toDelete G X p havoid
    obtain ⟨y, hyq, hyC⟩ := hx q
      ⟨hp.1, hp.2, havoid p.finish p.finish_mem_support⟩
    have hyp : y ∈ p.support := by simpa only [q,
      SafeLink.FinitePath.support_toDelete] using hyq
    exact Set.disjoint_left.1 hpAvoid hyp hyC
  · exact G.roof_subset_delete_roof C X

/-- Essential boundary vertices survive a roofed deletion precisely when
they are not themselves deleted. -/
theorem delete_essential_eq_sdiff_of_subset_roof (hX : X ⊆ G.roof C) :
    (G.delete X).essential C = G.essential C \ X := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨G.delete_essential_subset_essential C X hx,
      fun hxX ↦ Set.disjoint_left.1
        (G.disjoint_delete_essential_deleted C X) hx hxX⟩
  · rintro x ⟨hx, hxX⟩
    refine ⟨hx.1, ?_⟩
    obtain ⟨p, hp, hpAvoid⟩ := (G.not_mem_roof_iff (C \ {x}) x).1 hx.2
    have havoid : SafeLink.Walk.Avoids p.walk X := by
      intro y hyp hyX
      by_cases hyStart : y = p.start
      · exact hxX (hyStart.trans hp.1 ▸ hyX)
      · apply RelationalRoof.not_mem_roof_of_later_mem_targetPath
          G.graph.Adj G.target p hp _ hyp hyStart (hX hyX)
        intro z hzp hzC
        apply Set.disjoint_left.1 hpAvoid hzp
        exact ⟨hzC.1, by simpa only [hp.1] using hzC.2⟩
    let q := SafeLink.FinitePath.toDelete G X p havoid
    apply ((G.delete X).not_mem_roof_iff (C \ {x}) x).2
    refine ⟨q, ⟨hp.1, hp.2, havoid p.finish p.finish_mem_support⟩, ?_⟩
    change Disjoint q.support (C \ {x})
    rw [SafeLink.FinitePath.support_toDelete]
    exact hpAvoid

theorem delete_strictRoof_eq_union_of_subset_roof (hX : X ⊆ G.roof C) :
    (G.delete X).strictRoof C = G.strictRoof C ∪ X := by
  change (G.delete X).roof C \ (G.delete X).essential C = _
  rw [G.delete_roof_eq_of_subset_roof hX,
    G.delete_essential_eq_sdiff_of_subset_roof hX]
  change G.roof C \ (G.essential C \ X) = (G.roof C \ G.essential C) ∪ X
  ext x
  constructor
  · rintro ⟨hxRoof, hxNot⟩
    by_cases hxX : x ∈ X
    · exact Or.inr hxX
    · exact Or.inl ⟨hxRoof, fun hxEss ↦ hxNot ⟨hxEss, hxX⟩⟩
  · rintro (⟨hxRoof, hxNot⟩ | hxX)
    · exact ⟨hxRoof, fun hx ↦ hxNot hx.1⟩
    · exact ⟨hX hxX, fun hx ↦ hx.2 hxX⟩

/-- Removing the deleted boundary points does not change the surviving
roof.  This is the separator to use in the genuinely deleted ambient web. -/
theorem delete_roof_sdiff_eq_of_subset_roof
    (hX : X ⊆ G.roof C) (hC : G.essential C = C) :
    (G.delete X).roof (C \ X) = G.roof C := by
  have hess : (G.delete X).essential C = C \ X := by
    rw [G.delete_essential_eq_sdiff_of_subset_roof hX, hC]
  rw [← hess, (G.delete X).roof_essential,
    G.delete_roof_eq_of_subset_roof hX]

/-- The surviving boundary is trimmed in the deleted web. -/
theorem delete_essential_sdiff_eq_of_subset_roof
    (hX : X ⊆ G.roof C) (hC : G.essential C = C) :
    (G.delete X).essential (C \ X) = C \ X := by
  have hess : (G.delete X).essential C = C \ X := by
    rw [G.delete_essential_eq_sdiff_of_subset_roof hX, hC]
  calc
    (G.delete X).essential (C \ X) = (G.delete X).essential C :=
      (G.delete X).essential_eq_of_essential_subset_of_subset
        hess.le Set.sdiff_subset
    _ = C \ X := hess

/-- The exact common-deletion identity; outside `C`, the protected carrier
was already deleted by the strict roof. -/
theorem delete_quotient_eq_quotient_delete_inter_of_subset_roof
    (hX : X ⊆ G.roof C) (hC : G.essential C = C)
    (hsep : G.source ⊆ G.roof C) :
    (G.delete X).quotient C = (G.quotient C).delete (X ∩ C) := by
  have hsource : (G.quotient C).source = C := by
    change G.essential (G.source ∪ C) = C
    calc
      G.essential (G.source ∪ C) = G.essential C := by
        rw [Set.union_comm]
        exact RelationalRoof.essential_union_eq_of_subset_roof
          G.graph.Adj G.target hsep
      _ = C := hC
  have hsourceDel : ((G.delete X).quotient C).source = C \ X := by
    have hsepDel : (G.delete X).source ⊆ (G.delete X).roof C := by
      rw [G.delete_roof_eq_of_subset_roof hX]
      exact Set.sdiff_subset.trans hsep
    change (G.delete X).essential ((G.delete X).source ∪ C) = C \ X
    calc
      (G.delete X).essential ((G.delete X).source ∪ C) =
          (G.delete X).essential C := by
        rw [Set.union_comm]
        exact RelationalRoof.essential_union_eq_of_subset_roof
          (G.delete X).graph.Adj (G.delete X).target hsepDel
      _ = G.essential C \ X := G.delete_essential_eq_sdiff_of_subset_roof hX
      _ = C \ X := by rw [hC]
  have hXsurvives {x : V} (hx : x ∉ G.strictRoof C) (hxX : x ∈ X) : x ∈ C := by
    have hxEss : x ∈ G.essential C := by
      by_contra hxNot
      exact hx ⟨hX hxX, hxNot⟩
    exact hC ▸ hxEss
  have htarget {b : V} (hb : b ∈ G.target) (hbX : b ∈ X) : b ∈ C := by
    let p : FinitePath G.graph := FinitePath.trivial G.graph b
    obtain ⟨x, hxp, hxC⟩ := hX hbX p ⟨rfl, hb⟩
    have hxb : x = b := by simpa [p, FinitePath.support] using hxp
    exact hxb ▸ hxC
  rw [DWeb.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    change ((G.graph.Adj a b ∧ a ∉ X ∧ b ∉ X) ∧
      a ∉ (G.delete X).strictRoof C ∧
      b ∉ (G.delete X).strictRoof C ∧ b ∉ C) ↔
      ((G.graph.Adj a b ∧ a ∉ G.strictRoof C ∧
        b ∉ G.strictRoof C ∧ b ∉ C) ∧ a ∉ X ∩ C ∧ b ∉ X ∩ C)
    rw [G.delete_strictRoof_eq_union_of_subset_roof hX]
    constructor
    · rintro ⟨⟨hab, haX, hbX⟩, ha, hb, hbC⟩
      exact ⟨⟨hab, fun h ↦ ha (Or.inl h), fun h ↦ hb (Or.inl h), hbC⟩,
        fun h ↦ haX h.1, fun h ↦ hbX h.1⟩
    · rintro ⟨⟨hab, ha, hb, hbC⟩, haXC, hbXC⟩
      have haX : a ∉ X := fun h ↦ haXC ⟨h, hXsurvives ha h⟩
      have hbX : b ∉ X := fun h ↦ hbXC ⟨h, hXsurvives hb h⟩
      exact ⟨⟨hab, haX, hbX⟩, fun h ↦ h.elim ha haX,
        fun h ↦ h.elim hb hbX, hbC⟩
  · change ((G.delete X).quotient C).source = (G.quotient C).source \ (X ∩ C)
    rw [hsourceDel, hsource]
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  · change G.target \ X = G.target \ (X ∩ C)
    ext b
    constructor
    · rintro ⟨hb, hbX⟩
      exact ⟨hb, fun h ↦ hbX h.1⟩
    · rintro ⟨hb, hbXC⟩
      exact ⟨hb, fun hbX ↦ hbXC ⟨hbX, htarget hb hbX⟩⟩

/-- Roofed protected carriers preserve unhinderedness of the stopover
quotient, even when deleting the carrier alone creates a hindrance. -/
theorem delete_quotient_isUnhindered_of_subset_roof
    (hX : X ⊆ G.roof C) (hC : G.essential C = C)
    (hsep : G.source ⊆ G.roof C)
    (hunhindered : (G.quotient C).IsUnhindered) :
    ((G.delete X).quotient C).IsUnhindered := by
  rw [G.delete_quotient_eq_quotient_delete_inter_of_subset_roof hX hC hsep]
  apply CardinalInduction.SingularExtension.delete_sourceSet_isUnhindered
    (G.quotient C) hunhindered
  have hsource : (G.quotient C).source = C := by
    change G.essential (G.source ∪ C) = C
    calc
      G.essential (G.source ∪ C) = G.essential C := by
        rw [Set.union_comm]
        exact RelationalRoof.essential_union_eq_of_subset_roof
          G.graph.Adj G.target hsep
      _ = C := hC
  rw [hsource]
  exact Set.inter_subset_right

#print axioms delete_quotient_eq_quotient_delete_inter_of_subset_roof
#print axioms delete_quotient_isUnhindered_of_subset_roof

/-- The same protected quotient is obtained using only the surviving,
trimmed separator rather than retaining dead vertices in its presentation. -/
theorem delete_quotient_sdiff_eq_quotient_delete_inter_of_subset_roof
    (hX : X ⊆ G.roof C) (hC : G.essential C = C)
    (hsep : G.source ⊆ G.roof C) :
    (G.delete X).quotient (C \ X) = (G.quotient C).delete (X ∩ C) := by
  have hsepDel : (G.delete X).source ⊆ (G.delete X).roof C := by
    rw [G.delete_roof_eq_of_subset_roof hX]
    exact Set.sdiff_subset.trans hsep
  have hess : (G.delete X).essential C = C \ X := by
    rw [G.delete_essential_eq_sdiff_of_subset_roof hX, hC]
  calc
    (G.delete X).quotient (C \ X) = (G.delete X).quotient C := by
      rw [← hess]
      exact (G.delete X).quotient_essential_eq_of_subset_roof C hsepDel
    _ = (G.quotient C).delete (X ∩ C) :=
      G.delete_quotient_eq_quotient_delete_inter_of_subset_roof hX hC hsep

#print axioms delete_quotient_sdiff_eq_quotient_delete_inter_of_subset_roof

end Erdos599.DWeb
