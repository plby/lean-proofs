/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateSourceParity
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Parity of Claim 6.16 cut attachments

When a component-root segment is attached through a coordinate of an earlier
canonical branch, the coordinate is on local side zero of that branch and the
child component uses the same distinguished-reservoir tag as the branch owner.
Equivalently, the literal source reservoir is obtained by applying the branch
orientation to that coordinate side.  This is a source-only consequence of
Zhao's reconnect rule; it has no host or embedding premise.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}
variable {target slack : ℕ}

/-- In a tree, two vertices have the same parity from a fixed root exactly
when their mutual distance is even. -/
private theorem dist_mod_two_eq_zero_iff_rootParity_eq
    (hT : T.IsTree) (r x y : V) :
    T.dist x y % 2 = 0 ↔ T.dist r x % 2 = T.dist r y % 2 := by
  let c : T.Coloring Bool :=
    SimpleGraph.recolorOfEquiv T finTwoEquiv (hT.coloringTwoOfVert r)
  obtain ⟨p, -, hp⟩ := hT.connected.exists_path_of_dist x y
  rw [← hp, ← Nat.even_iff, c.even_length_iff_congr p]
  change (finTwoEquiv ⟨T.dist r x % 2, _⟩ = true ↔
    finTwoEquiv ⟨T.dist r y % 2, _⟩ = true) ↔ _
  rw [← Bool.eq_iff_iff]
  constructor
  · intro h
    exact congrArg Fin.val (finTwoEquiv.injective h)
  · intro h
    apply congrArg finTwoEquiv
    apply Fin.ext
    exact h

/-- A recorded cut parent which belongs to canonical branch `j` is on local
side zero of that branch. -/
theorem cutParent_canonicalBranchSide_zero
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (q : Fin P.numParts) (hq : q.val ≠ 0) (j : BranchIndex P)
    (hclass : literalSourceClass P (P.parent q hq) = Sum.inr j) :
    canonicalBranchSide P j (P.parent q hq) = 0 := by
  have hparentNonroot : P.parent q hq ∉ partitionRoots P := by
    intro hp
    have hinl := literalSourceClass_of_root P (P.parent q hq) hp
    rw [hclass] at hinl
    cases hinl
  let z := literalBranchCoordinate P (P.parent q hq) hparentNonroot
  have hzClass := literalSourceClass_eq_inr_literalBranchCoordinate P
    (P.parent q hq) hparentNonroot
  have hzj : z.1 = j := by
    exact Sum.inr.inj (hzClass.symm.trans hclass)
  have hzDecode : (partitionBranchEquivNonroots P z).1 = P.parent q hq :=
    partitionBranchEquivNonroots_literalBranchCoordinate P
      (P.parent q hq) hparentNonroot
  have hpart : P.parentPart q hq = (branchForest P).owner j := by
    have hc := partitionBranchEquivNonroots_component P z
    rw [hzDecode, componentIndex_parent P q hq, hzj] at hc
    exact hc
  have hreconnect :
      T.dist globalRoot (P.roots q) % 2 =
        T.dist globalRoot (P.roots (P.parentPart q hq)) % 2 := by
    rcases P.reconnect_rule q hq with hroot | hparity
    · exfalso
      apply hparentNonroot
      rw [hroot]
      exact Finset.mem_image.mpr
        ⟨P.parentPart q hq, Finset.mem_univ _, rfl⟩
    · exact hparity
  have hchildParent := TreePartition.rootParity_ne_of_adj hT globalRoot
    (P.cut_adj q hq)
  have hownerActualEq := actualBranchRoot_dist_add_one hT P j
  have hownerActual :
      T.dist globalRoot (P.roots ((branchForest P).owner j)) % 2 ≠
        T.dist globalRoot (actualBranchRoot P j) % 2 := by
    omega
  have hsameGlobal :
      T.dist globalRoot (actualBranchRoot P j) % 2 =
        T.dist globalRoot (P.parent q hq) % 2 := by
    rw [hpart] at hreconnect
    have h0 := Nat.mod_lt (T.dist globalRoot (P.roots q)) (by omega : 0 < 2)
    have h1 := Nat.mod_lt (T.dist globalRoot (P.parent q hq)) (by omega : 0 < 2)
    have h2 := Nat.mod_lt
      (T.dist globalRoot (P.roots ((branchForest P).owner j))) (by omega : 0 < 2)
    have h3 := Nat.mod_lt
      (T.dist globalRoot (actualBranchRoot P j)) (by omega : 0 < 2)
    omega
  have hlocal : T.dist (actualBranchRoot P j) (P.parent q hq) % 2 = 0 :=
    (dist_mod_two_eq_zero_iff_rootParity_eq hT globalRoot _ _).2 hsameGlobal
  apply Fin.ext
  exact hlocal

/-- Exact source parity of a component-root attachment whose parent lies in
an earlier branch-class hierarchy segment. -/
theorem componentRoot_cutAttachment_parity
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (i k : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size k))
    (q : Fin P.numParts) (j : BranchIndex P)
    (hi : segmentSourceClass hT P optional i = Sum.inl q)
    (hparent : (AllocationHierarchy hT P optional).parent i = Sum.inr ⟨k, a⟩)
    (hk : segmentSourceClass hT P optional k = Sum.inr j) :
    componentReservoirSide P q =
      orientedSide (componentReservoirSide P ((branchForest P).owner j))
        (segmentEndpointSide hT P optional k j a) := by
  have hroot : SegmentRootOriginal hT P optional i = P.roots q := by
    apply (literalSourceClass_eq_inl_iff P _ q).mp
    exact hi
  have hq : q.val ≠ 0 := by
    intro hq0
    have hqeq : q = ⟨0, P.numParts_pos⟩ := Fin.ext hq0
    have hglobal : P.roots q = globalRoot := by
      rw [hqeq, P.first_root]
    exact segmentRootOriginal_ne_globalRoot hT P optional i
      (hroot.trans hglobal)
  have hparentValue :
      wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional) (Sum.inr ⟨k, a⟩) =
        P.parent q hq := by
    calc
      _ = SegmentParentOriginal hT P optional i := by
        exact congrArg
          (wholeHierarchyOriginalVertex T hT globalRoot
            (AllocationSpecial hT P optional)) hparent.symm
      _ = TreePartition.parent hT globalRoot
          (segmentRootOriginal_ne_globalRoot hT P optional i) :=
        segmentParentOriginal_eq_treeParent hT P optional i
      _ = P.parent q hq := by
        symm
        apply TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
        · simpa only [hroot] using (P.cut_adj q hq).symm
        · simpa only [hroot] using cutParent_dist_add_one hT P q hq
  have hparentClass : literalSourceClass P (P.parent q hq) = Sum.inr j := by
    have hc := wholeSegment_sourceClass_eq_of_boundary hT P optional
      (canonicalWholeSourceBoundary hT P optional) k a
    rw [hk] at hc
    rw [hparentValue] at hc
    exact hc
  have hside : segmentEndpointSide hT P optional k j a = 0 := by
    change canonicalBranchSide P j
      (wholeHierarchyOriginalVertex T hT globalRoot
        (AllocationSpecial hT P optional) (Sum.inr ⟨k, a⟩)) = 0
    rw [hparentValue]
    exact cutParent_canonicalBranchSide_zero hT P q hq j hparentClass
  have hpart : P.parentPart q hq = (branchForest P).owner j := by
    have hparentNonroot : P.parent q hq ∉ partitionRoots P := by
      intro hp
      have hinl := literalSourceClass_of_root P (P.parent q hq) hp
      rw [hparentClass] at hinl
      cases hinl
    let z := literalBranchCoordinate P (P.parent q hq) hparentNonroot
    have hzClass := literalSourceClass_eq_inr_literalBranchCoordinate P
      (P.parent q hq) hparentNonroot
    have hzj : z.1 = j := Sum.inr.inj (hzClass.symm.trans hparentClass)
    have hzDecode : (partitionBranchEquivNonroots P z).1 = P.parent q hq :=
      partitionBranchEquivNonroots_literalBranchCoordinate P
        (P.parent q hq) hparentNonroot
    have hc := partitionBranchEquivNonroots_component P z
    rw [hzDecode, componentIndex_parent P q hq, hzj] at hc
    exact hc
  have hreservoir : componentReservoirSide P q =
      componentReservoirSide P ((branchForest P).owner j) := by
    rcases P.reconnect_rule q hq with hbad | hparity
    · have hpRoot : P.parent q hq ∈ partitionRoots P := by
        rw [hbad]
        exact Finset.mem_image.mpr
          ⟨P.parentPart q hq, Finset.mem_univ _, rfl⟩
      have hinl := literalSourceClass_of_root P (P.parent q hq) hpRoot
      rw [hparentClass] at hinl
      cases hinl
    · rw [hpart] at hparity
      unfold componentReservoirSide
      rw [hparity]
  rw [hside, hreservoir]
  simp [orientedSide]

/-- Selected and residual-major parent branches have owner reservoir side
zero. -/
theorem componentRoot_cutAttachment_parity_selected
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i k : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size k))
    (q : Fin P.numParts) (j : BranchIndex P)
    (hi : segmentSourceClass hT P optional i = Sum.inl q)
    (hparent : (AllocationHierarchy hT P optional).parent i = Sum.inr ⟨k, a⟩)
    (hk : segmentSourceClass hT P optional k = Sum.inr j)
    (hj : j ∈ S.selected) :
    componentReservoirSide P q =
      orientedSide 0 (segmentEndpointSide hT P optional k j a) := by
  have h := componentRoot_cutAttachment_parity
    hT P optional i k a q j hi hparent hk
  rw [Erdos547b.ZhaoClaim616CoordinateSourceParity.componentReservoirSide_owner_eq_zero_of_mem_selected
    P S j hj] at h
  exact h

theorem componentRoot_cutAttachment_parity_majorResidual
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i k : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size k))
    (q : Fin P.numParts) (j : BranchIndex P)
    (hi : segmentSourceClass hT P optional i = Sum.inl q)
    (hparent : (AllocationHierarchy hT P optional).parent i = Sum.inr ⟨k, a⟩)
    (hk : segmentSourceClass hT P optional k = Sum.inr j)
    (hj : j ∈ majorResidualBranches P S) :
    componentReservoirSide P q =
      orientedSide 0 (segmentEndpointSide hT P optional k j a) := by
  have h := componentRoot_cutAttachment_parity
    hT P optional i k a q j hi hparent hk
  rw [Erdos547b.ZhaoClaim616CoordinateSourceParity.componentReservoirSide_owner_eq_zero_of_mem_majorResidual
    P S j hj] at h
  exact h

/-- Minor parent branches have owner reservoir side one. -/
theorem componentRoot_cutAttachment_parity_minor
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i k : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size k))
    (q : Fin P.numParts) (j : BranchIndex P)
    (hi : segmentSourceClass hT P optional i = Sum.inl q)
    (hparent : (AllocationHierarchy hT P optional).parent i = Sum.inr ⟨k, a⟩)
    (hk : segmentSourceClass hT P optional k = Sum.inr j)
    (hj : j ∈ minorBranches P) :
    componentReservoirSide P q =
      orientedSide 1 (segmentEndpointSide hT P optional k j a) := by
  have h := componentRoot_cutAttachment_parity
    hT P optional i k a q j hi hparent hk
  rw [Erdos547b.ZhaoClaim616CoordinateSourceParity.componentReservoirSide_owner_eq_one_of_mem_minorBranches
    P j hj] at h
  exact h

end Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity

#print axioms Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity.cutParent_canonicalBranchSide_zero
#print axioms Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity.componentRoot_cutAttachment_parity
