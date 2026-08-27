/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveSupportedResidualLink
import ErdosProblems.Erdos207.ReserveStrongWellDistributed

/-!
# The augmented reserve after the preliminary cover

The Bernoulli reserve sampled at the beginning of a KSSS master step is not
quite the set supporting the final residual links.  The preliminary packing
may leave a small number of additional crossing edges uncovered.  Adjoining
exactly those edges to the sampled reserve gives the correct object: coverage
outside it is tautological, while its probability law follows by combining
the Bernoulli factors with the preliminary selected/uncovered estimate.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Crossing edges of `G` which are not covered by the preliminary family. -/
def preliminaryResidualCrossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    Finset (Sym2 V) :=
  crossingEdges G U \ graphEdges (coveredGraph P)

/-- The sampled reserve enlarged by every crossing edge missed by the
preliminary family. -/
def preliminaryAugmentedReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (sampled : Finset (Sym2 V))
    (P : TripleSystemOn V) : Finset (Sym2 V) :=
  sampled ∪ preliminaryResidualCrossingEdges G U P

lemma preliminaryResidualCrossingEdges_subset_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    preliminaryResidualCrossingEdges G U P ⊆ crossingEdges G U :=
  sdiff_subset

/-- If every edge of `G` is uncovered by an old family `P`, then removing
`P` from a later family does not change which crossing edges of `G` remain
uncovered.  This is the relative-to-absolute conversion used by a master
preliminary step. -/
lemma preliminaryResidualCrossingEdges_sdiff_eq_of_le_leaveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P Q : TripleSystemOn V}
    (hGleave : G ≤ leaveGraph P) :
    preliminaryResidualCrossingEdges G U Q =
      preliminaryResidualCrossingEdges G U (Q \ P) := by
  ext e
  simp only [preliminaryResidualCrossingEdges, mem_sdiff]
  constructor
  · rintro ⟨hecross, hnotCovered⟩
    refine ⟨hecross, ?_⟩
    intro hcovered
    apply hnotCovered
    induction e using Sym2.inductionOn with
    | _ u v =>
        obtain ⟨T, hT, huT, hvT, huv⟩ :=
          coveredGraph_adj.mp (mem_graphEdges_iff.mp hcovered)
        exact mem_graphEdges_iff.mpr <| coveredGraph_adj.mpr
          ⟨T, (mem_sdiff.mp hT).1, huT, hvT, huv⟩
  · rintro ⟨hecross, hnotCovered⟩
    refine ⟨hecross, ?_⟩
    intro hcovered
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hGset : s(u, v) ∈ G.edgeSet :=
          (mem_crossingEdges_iff.mp hecross).1
        have hGedge : G.Adj u v := by
          change G.Adj u v at hGset
          exact hGset
        obtain ⟨T, hTQ, huT, hvT, huv⟩ :=
          coveredGraph_adj.mp (mem_graphEdges_iff.mp hcovered)
        by_cases hTP : T ∈ P
        · exact (leaveGraph_adj.mp (hGleave hGedge)).2
            ⟨T, hTP, huT, hvT, huv⟩
        · apply hnotCovered
          exact mem_graphEdges_iff.mpr <| coveredGraph_adj.mpr
            ⟨T, mem_sdiff.mpr ⟨hTQ, hTP⟩, huT, hvT, huv⟩

/-- By construction, every crossing edge outside the augmented reserve was
covered by the preliminary family. -/
theorem coversCrossingOutsideReserve_preliminaryAugmentedReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (sampled : Finset (Sym2 V))
    (P : TripleSystemOn V) :
    CoversCrossingOutsideReserve G U
      (preliminaryAugmentedReserve G U sampled P) P := by
  intro v x hv hx hG hnot
  have hcross : s(v, x) ∈ crossingEdges G U := by
    rw [mem_crossingEdges_iff]
    exact ⟨hG, isCrossingEdge_mk_iff.mpr (Or.inr ⟨hx, hv⟩)⟩
  have hnotResidual :
      s(v, x) ∉ preliminaryResidualCrossingEdges G U P := by
    intro he
    exact hnot (mem_union_right sampled he)
  have hcovered : s(v, x) ∈ graphEdges (coveredGraph P) := by
    by_contra hnotCovered
    exact hnotResidual (mem_sdiff.mpr ⟨hcross, hnotCovered⟩)
  exact mem_graphEdges_iff.mp hcovered

/-- Membership of a prescribed family in a union splits into a part in the
left set and a complementary part in the right set. -/
lemma exists_powerset_partition_of_subset_union
    {α : Type*} [DecidableEq α]
    {R A B : Finset α} (hR : R ⊆ A ∪ B) :
    ∃ S ∈ R.powerset, S ⊆ A ∧ R \ S ⊆ B := by
  let S := R ∩ A
  refine ⟨S, mem_powerset.mpr inter_subset_left, inter_subset_right, ?_⟩
  intro x hx
  have hxR : x ∈ R := (mem_sdiff.mp hx).1
  have hxnotS : x ∉ S := (mem_sdiff.mp hx).2
  have hxunion := hR hxR
  rw [mem_union] at hxunion
  exact hxunion.resolve_left fun hxA ↦
    hxnotS (mem_inter.mpr ⟨hxR, hxA⟩)

/-- The canonical partition can be sharpened so that its right-hand part is
not only contained in `B` but is disjoint from the already charged left set
`A`. -/
lemma exists_powerset_partition_of_subset_union_sdiff
    {α : Type*} [DecidableEq α]
    {R A B : Finset α} (hR : R ⊆ A ∪ B) :
    ∃ S ∈ R.powerset, S ⊆ A ∧ R \ S ⊆ B \ A := by
  let S := R ∩ A
  refine ⟨S, mem_powerset.mpr inter_subset_left, inter_subset_right, ?_⟩
  intro x hx
  have hxR : x ∈ R := (mem_sdiff.mp hx).1
  have hxnotS : x ∉ S := (mem_sdiff.mp hx).2
  have hxnotA : x ∉ A := by
    intro hxA
    exact hxnotS (mem_inter.mpr ⟨hxR, hxA⟩)
  have hxunion := hR hxR
  exact mem_sdiff.mpr
    ⟨(mem_union.mp hxunion).resolve_left hxnotA, hxnotA⟩

/-- A joint output event for the enlarged later family and augmented reserve
has simultaneous powerset partitions into old/new triangles and
sampled/residual reserve edges. -/
lemma reserveStrongDistributionEvent_preliminary_partition
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq V]
    (initial later : Omega → TripleSystemOn V)
    (sampled : Omega → Finset (Sym2 V))
    (G : Omega → SimpleGraph V) (U : Finset V)
    (added : Omega → Xi → TripleSystemOn V)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V))
    (z : Omega × Xi)
    (hz : ReserveStrongDistributionEvent (jointInitial initial)
      (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (added z.1 z.2)) Ifix Dfix Efix Rfix z) :
    ∃ S ∈ Dfix.powerset, ∃ T ∈ Rfix.powerset,
      ReserveStrongDistributionEvent initial later sampled
        Ifix S Efix T z.1 ∧
      Dfix \ S ⊆ added z.1 z.2 ∧
      Rfix \ T ⊆ preliminaryResidualCrossingEdges
        (G z.1) U (added z.1 z.2) := by
  obtain ⟨S, hSpow, hOld, hNew⟩ :=
    strongDistributionEvent_jointLater_partition initial later added
      Ifix Dfix Efix z hz.1
  obtain ⟨T, hTpow, hTsampled, hTresidual⟩ :=
    exists_powerset_partition_of_subset_union hz.2
  exact ⟨S, hSpow, T, hTpow, ⟨hOld, hTsampled⟩, hNew, hTresidual⟩

/-- Refined preliminary partition in which newly charged residual edges
explicitly exclude the sampled reserve.  This is the exact interface for a
preliminary process run after the reserve has been exposed. -/
lemma reserveStrongDistributionEvent_preliminary_partition_sdiff
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq V]
    (initial later : Omega → TripleSystemOn V)
    (sampled : Omega → Finset (Sym2 V))
    (G : Omega → SimpleGraph V) (U : Finset V)
    (added : Omega → Xi → TripleSystemOn V)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V))
    (z : Omega × Xi)
    (hz : ReserveStrongDistributionEvent (jointInitial initial)
      (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (added z.1 z.2)) Ifix Dfix Efix Rfix z) :
    ∃ S ∈ Dfix.powerset, ∃ T ∈ Rfix.powerset,
      ReserveStrongDistributionEvent initial later sampled
        Ifix S Efix T z.1 ∧
      Dfix \ S ⊆ added z.1 z.2 ∧
      Rfix \ T ⊆
        preliminaryResidualCrossingEdges (G z.1) U (added z.1 z.2) \
          sampled z.1 := by
  obtain ⟨S, hSpow, hOld, hNew⟩ :=
    strongDistributionEvent_jointLater_partition initial later added
      Ifix Dfix Efix z hz.1
  obtain ⟨T, hTpow, hTsampled, hTresidual⟩ :=
    exists_powerset_partition_of_subset_union_sdiff hz.2
  exact ⟨S, hSpow, T, hTpow, ⟨hOld, hTsampled⟩, hNew, hTresidual⟩

end

end Erdos207
