/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim617Switch
import ErdosProblems.Erdos547b.SourceMatchingInclusion

/-! # The switched and reserved physical matchings have a separated union -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSwitchUnion

open Finset SimpleGraph Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceClaim617Switch Erdos547b.ZhaoMatchingSupportSeparation
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoSourceMatchingRowIdentity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (sw : Switch W Q S O)

def fullMatching : (padGraph (reduced W)).Subgraph := sw.switched ⊔ O.D.Mb

theorem switched_disjoint_reserved :
    Disjoint (matchingSupport sw.switched) (matchingSupport O.D.Mb) :=
  (switched_properties W Q S O sw).2.1.mono_right Finset.subset_union_left

theorem fullMatching_isMatching : (fullMatching W Q S O sw).IsMatching := by
  have hs := (switched_properties W Q S O sw).1
  have hb := O.D.Mb_isMatching
  apply hs.sup hb
  rw [hs.support_eq_verts, hb.support_eq_verts, Set.disjoint_left]
  intro x hx hy
  exact Finset.disjoint_left.mp (switched_disjoint_reserved W Q S O sw)
    ((mem_matchingSupport _ _).mpr hx) ((mem_matchingSupport _ _).mpr hy)

theorem fullMatching_support : matchingSupport (fullMatching W Q S O sw) =
    matchingSupport sw.switched ∪ matchingSupport O.D.Mb := by
  ext x
  simp only [mem_matchingSupport, fullMatching, Subgraph.verts_sup,
    Set.mem_union, Finset.mem_union]

theorem reserved_disjoint_roots :
    Disjoint (matchingSupport O.D.Mb) {Sum.inl Q.A, Sum.inl Q.B} := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨e, he, c, hc⟩ :=
    (mem_selectedSupport_iff Q.claim67.M (padFinset (large W)) O.D.mbEdges x).mp hx
  have haway := O.reserved.subset_away (O.reserved_eq ▸ he)
  have hn := endpoint_ne_distinguished_of_mem_away Q.claim67.M (padFinset (large W))
    (Sum.inl Q.A) (Sum.inl Q.B) haway c
  rcases Finset.mem_insert.mp hy with h | h
  · exact hn.1 (hc.trans h)
  · exact hn.2 (hc.trans (Finset.mem_singleton.mp h))

theorem fullMatching_disjoint_roots :
    Disjoint (matchingSupport (fullMatching W Q S O sw)) {Sum.inl Q.A, Sum.inl Q.B} := by
  rw [fullMatching_support, Finset.disjoint_union_left]
  exact ⟨(switched_properties W Q S O sw).2.1.mono_right Finset.subset_union_right,
    reserved_disjoint_roots W Q S O⟩

theorem fullMatching_all_edges_away :
    allMatchingEdges (fullMatching W Q S O sw) ⊆
      edgesAwayFromDistinguished (fullMatching W Q S O sw) (padFinset (large W))
        (Sum.inl Q.A) (Sum.inl Q.B) :=
  all_edges_away W Q _ (fullMatching_disjoint_roots W Q S O sw)

theorem partners_disjoint_reserved : Disjoint sw.partnerSet (matchingSupport O.D.Mb) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.disjoint_left.mp (min_disjoint_excluded W Q S O)
    (sw.partner_mem_support e) (Finset.mem_union_left _ hy)

theorem partners_disjoint_fullMatching :
    Disjoint sw.partnerSet (matchingSupport (fullMatching W Q S O sw)) := by
  rw [fullMatching_support, Finset.disjoint_union_right]
  exact ⟨(switched_properties W Q S O sw).2.2.1, partners_disjoint_reserved W Q S O sw⟩

end Erdos547b.ZhaoSourceSwitchUnion

#print axioms Erdos547b.ZhaoSourceSwitchUnion.fullMatching_isMatching
#print axioms Erdos547b.ZhaoSourceSwitchUnion.fullMatching_all_edges_away
#print axioms Erdos547b.ZhaoSourceSwitchUnion.partners_disjoint_fullMatching
