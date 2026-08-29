/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSmallCarrierObstruction

/-!
# Restoring the source part of a deleted carrier

The obstruction to lifting a wave through a vertex deletion comes only
from paths which enter the deleted set.  Deleted vertices which are ambient
sources are harmless: put a trivial path at each of them.  Every ambient
source--target path which enters that source set is then stopped immediately,
and every path which avoids it is handled by the wave in the deletion.

For an arbitrary deleted set `X`, this observation can be applied first to
`G.source ∩ X`.  After the dependent deletion equality is transported, it
produces a wave in `G.delete (X \ G.source)`.  Thus the only carrier still to
be restored is the source-disjoint set `X \ G.source`.  When `X` is the
carrier of a bounded linkage, that remaining set is still below the
induction cardinal.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSourcePartRestoration

open SingularSafeDesignatedLimit SingularSmallCarrierObstruction
  SingularSafeCarrierCardinal

universe u

variable {V : Type u}

/-- Initial vertices are invariant under transport of a bundled wave along
an equality of webs. -/
theorem initialSet_castWave {H K : DWeb V} (h : H = K)
    (W : H.Wave) :
    K.initialSet (h ▸ W).1 = H.initialSet W.1 := by
  cases h
  rfl

/-- A residual wave can always be lifted through a deletion consisting
entirely of ambient sources: trivial paths at the restored sources supply
the missing part of the separator. -/
theorem resurrectedWaveFamily_isWave_of_subset_source
    (G : DWeb V) {Q : Set V} (hQ : Q ⊆ G.source)
    (M : (G.delete Q).Wave) :
    G.IsWave (resurrectedWaveFamily G Q M) := by
  apply (isWave_resurrectedWaveFamily_iff G Q M).2
  rw [ResurrectionSeparates]
  have hsource :=
    source_subset_roof_terminalFrontier_union_deleted G Q M.2
  simpa only [Set.inter_eq_right.mpr hQ] using hsource

/-- Exact initial profile of source-only restoration.  No maximality of the
residual wave is needed. -/
theorem initialSet_resurrectedWaveFamily_of_subset_source
    (G : DWeb V) {Q : Set V} (hQ : Q ⊆ G.source)
    (M : (G.delete Q).Wave) :
    G.initialSet (resurrectedWaveFamily G Q M) =
      (G.delete Q).initialSet M.1 ∪ Q := by
  rw [initialSet_resurrectedWaveFamily]
  simp only [Set.inter_eq_right.mpr hQ]

/-- Splitting an arbitrary set into its source and non-source parts.  The
order is chosen to match `delete_delete`: first delete the non-source part,
then delete the source part. -/
theorem sdiff_source_union_inter_source (G : DWeb V) (X : Set V) :
    (X \ G.source) ∪ (G.source ∩ X) = X := by
  ext x
  by_cases hxSource : x ∈ G.source <;> simp [hxSource]

/-- After restoring the source vertices of an arbitrary deleted carrier,
one obtains a wave in the web which still deletes only the non-source part.
Its initial set is exactly the restored ambient sources together with the
old residual-wave initials.

This is the dependent transport seam needed before applying the general
delete/quotient arrow to the remaining source-disjoint carrier. -/
theorem exists_wave_after_restoring_sourcePart
    (G : DWeb V) (X : Set V) (M : (G.delete X).Wave) :
    ∃ W : Set (G.delete (X \ G.source)).DPath,
      (G.delete (X \ G.source)).IsWave W ∧
        (G.delete (X \ G.source)).initialSet W =
          (G.source ∩ X) ∪ (G.delete X).initialSet M.1 := by
  let Q : Set V := X \ G.source
  let A : Set V := G.source ∩ X
  let H : DWeb V := G.delete Q
  have hdelete : H.delete A = G.delete X := by
    dsimp only [H, Q, A]
    rw [G.delete_delete]
    congr 1
    exact sdiff_source_union_inter_source G X
  let M' : (H.delete A).Wave := hdelete.symm ▸ M
  have hAsource : A ⊆ H.source := by
    intro a ha
    exact ⟨ha.1, fun haQ ↦ haQ.2 ha.1⟩
  let W : Set H.DPath := resurrectedWaveFamily H A M'
  refine ⟨W, resurrectedWaveFamily_isWave_of_subset_source H hAsource M', ?_⟩
  rw [initialSet_resurrectedWaveFamily_of_subset_source H hAsource M']
  have htransport : (H.delete A).initialSet M'.1 =
      (G.delete X).initialSet M.1 := by
    exact initialSet_castWave hdelete.symm M
  rw [htransport]
  exact Set.union_comm _ _

/-- The hard remainder in the preceding source/non-source split is still
strictly below an uncountable induction cardinal when the original deleted
set is the carrier of a bounded linkage. -/
theorem mk_nonSourceCarrier_lt
    {G : DWeb V} {A B : Set V} {P : Set G.DPath}
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa)
    (hP : IsLinkageBetween G A B P) (hA : #A < kappa) :
    #((G.vertexSet P \ G.source : Set V)) < kappa := by
  exact (mk_subtype_mono Set.sdiff_subset).trans_lt
    (mk_vertexSet_lt_of_mk_initial_lt hkappa hP hA)

/-- Complete small-carrier decomposition used by the M-dependent exchange:
the source part is restored unconditionally, while the remaining deleted
set is source-disjoint and has cardinality below `kappa`. -/
theorem exists_small_nonSourceRestoration
    {G : DWeb V} {A B : Set V} {P : Set G.DPath}
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa)
    (hP : IsLinkageBetween G A B P) (hA : #A < kappa)
    (M : (G.delete (G.vertexSet P)).Wave) :
    let Q := G.vertexSet P \ G.source
    #(Q) < kappa ∧ Disjoint G.source Q ∧
      ∃ W : Set (G.delete Q).DPath,
        (G.delete Q).IsWave W ∧
          (G.delete Q).initialSet W =
            (G.source ∩ G.vertexSet P) ∪
              (G.delete (G.vertexSet P)).initialSet M.1 := by
  dsimp only
  refine ⟨mk_nonSourceCarrier_lt hkappa hP hA, ?_, ?_⟩
  · exact Set.disjoint_sdiff_right
  · exact exists_wave_after_restoring_sourcePart
      G (G.vertexSet P) M

#print axioms resurrectedWaveFamily_isWave_of_subset_source
#print axioms exists_wave_after_restoring_sourcePart
#print axioms mk_nonSourceCarrier_lt
#print axioms exists_small_nonSourceRestoration

end SingularSourcePartRestoration
end CardinalInduction
end Erdos599
