import Mathlib
import ErdosProblems.Erdos550.HPAllocatedSurplus
import ErdosProblems.Erdos550.HPParityMatchingEmbedding
import ErdosProblems.Erdos550.OffTuranBooleanAllocation
import ErdosProblems.Erdos550.OffTuranContactSets
import ErdosProblems.Erdos550.OffTuranEndpointAccounting
import ErdosProblems.Erdos550.OffTuranHeadCore
import ErdosProblems.Erdos550.OffTuranMatchingGeometry
import ErdosProblems.Erdos550.OffTuranParityTreeData
import ErdosProblems.Erdos550.OffTuranReducedDegreeData

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Reduced-data embedding theorem

This theorem assembles the parity-refined source package, two low-bad head
cores, a split of complete matching edges, one-sided retained contact sets,
and the stateful Hladký--Piguet embedding under the scalar room inequalities
used by the direct off--Turán argument.
-/

open Finset SimpleGraph Finpartition

namespace Erdos550

open Classical

noncomputable def offTuranMatchingTargets
    {ι κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (cL cR : κ → ι) : Finset ι :=
  Finset.univ.image cL ∪ Finset.univ.image cR

noncomputable def offTuranHeadCoreFamily
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (ε d : ℝ)
    (Tset : Finset ι) (thr : ℝ) (X Y : ι) (b : Bool) : Finset V :=
  hpOffTuranHeadCore G R C ε d Tset thr
    (offTuranBoolHead X Y b) (offTuranBoolOtherHead X Y b)

noncomputable def offTuranLeftThreshold
    {V ι κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (K₀ : Finset κ) (X Y : ι)
    (ε : ℝ) (cL : κ → ι) (k : κ) : ℝ :=
  hpTrimmedThreshold
    (hpHeadEndpointWeight G R C
      (offTuranAssignedHead K₀ X Y k) (cL k))
    ε ((C (cL k)).card : ℝ)

noncomputable def offTuranRightThreshold
    {V ι κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (K₀ : Finset κ) (X Y : ι)
    (ε : ℝ) (cR : κ → ι) (k : κ) : ℝ :=
  hpTrimmedThreshold
    (hpHeadEndpointWeight G R C
      (offTuranAssignedHead K₀ X Y k) (cR k))
    ε ((C (cR k)).card : ℝ)

noncomputable def offTuranLeftContact
    {V ι κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (ε d : ℝ)
    (Tset : Finset ι) (thr : ℝ) (K₀ : Finset κ) (X Y : ι)
    (cL : κ → ι) (k : κ) : Finset V :=
  hpHeadContactSet G R C
    (offTuranHeadCoreFamily G R C ε d Tset thr X Y
      (offTuranAssignedBool K₀ k))
    ε (offTuranAssignedHead K₀ X Y k) (cL k)

noncomputable def offTuranRightContact
    {V ι κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (ε d : ℝ)
    (Tset : Finset ι) (thr : ℝ) (K₀ : Finset κ) (X Y : ι)
    (cR : κ → ι) (k : κ) : Finset V :=
  hpHeadContactSet G R C
    (offTuranHeadCoreFamily G R C ε d Tset thr X Y
      (offTuranAssignedBool K₀ k))
    ε (offTuranAssignedHead K₀ X Y k) (cR k)

set_option maxHeartbeats 2000000 in
theorem offTuran_reduced_parity_embedding
    {A : Type} {V κ : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype κ] [DecidableEq κ]
    (T : SimpleGraph A) (hT : T.IsTree)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d base η : ℝ} {m₀ : ℕ}
    (RD : OffTuranReducedDegreeData G ε d base η m₀)
    (X Y : {C // C ∈ RD.P.parts})
    (hXY : (offTuranReducedGraph G RD.P ε d).Adj X Y)
    (cL cR : κ → {C // C ∈ RD.P.parts})
    (hmatch : ∀ k,
      (offTuranReducedGraph G RD.P ε d).Adj (cL k) (cR k))
    (hinj : Function.Injective (Sum.elim cL cR))
    (haway : ∀ k, cL k ≠ X ∧ cL k ≠ Y ∧
      cR k ≠ X ∧ cR k ≠ Y)
    (K₀ : Finset κ)
    (τsep : ℝ) (Q : OffTuranParityTreeData T τsep)
    (thr τ margin retainedLoss err cap edgeCap : ℝ) (Lnat : ℕ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd1 : d ≤ 1)
    (hthr0 : 0 < thr)
    (hheadSeedRoom : ∀ b,
      (Q.S.card : ℝ) +
          hpHeadCoreLoss ε thr
            (offTuranMatchingTargets cL cR)
            ((offTuranBoolHead X Y b).1) <
        ((offTuranBoolHead X Y b).1.card : ℝ))
    (hheadCrossRoom : ∀ b,
      (Q.S.card : ℝ) + 1 +
          hpHeadCoreLoss ε thr
            (offTuranMatchingTargets cL cR)
            ((offTuranBoolHead X Y b).1) ≤
        (d - ε) * ((offTuranBoolHead X Y b).1.card : ℝ))
    (hheadFractionRoom : ∀ b,
      hpHeadCoreLoss ε thr
          (offTuranMatchingTargets cL cR)
          ((offTuranBoolHead X Y b).1) ≤
        (1 - ε) * ((offTuranBoolHead X Y b).1.card : ℝ))
    (hcontactSeedRoom : ∀ b,
      (Q.S.card : ℝ) <
        ε * ((offTuranHeadCoreFamily G
          (offTuranReducedGraph G RD.P ε d)
          (fun i : {C // C ∈ RD.P.parts} => i.1)
          ε d (offTuranMatchingTargets cL cR)
          thr X Y b).card : ℝ))
    (hτ : 0 ≤ τ)
    (hcomponentRoom :
      τsep * Fintype.card A ≤ τ)
    (hLsig : ε * (RD.scale : ℝ) ≤ (Lnat : ℝ))
    (hpairRoom :
      ε * (RD.scale : ℝ) + τ ≤
        (d - 2 * ε) * (Lnat : ℝ))
    (hretainedLoss :
      ε * (RD.scale : ℝ) ≤ retainedLoss)
    (hcap : ∀ i : {C // C ∈ RD.P.parts},
      cap ≤ (i.1.card : ℝ))
    (hleftCap : ∀ k,
      offTuranLeftThreshold G
        (offTuranReducedGraph G RD.P ε d)
        (fun i : {C // C ∈ RD.P.parts} => i.1)
        K₀ X Y ε cL k ≤ cap)
    (hrightCap : ∀ k,
      offTuranRightThreshold G
        (offTuranReducedGraph G RD.P ε d)
        (fun i : {C // C ∈ RD.P.parts} => i.1)
        K₀ X Y ε cR k ≤ cap)
    (herr0 : 0 ≤ err) (herr : retainedLoss ≤ err)
    (hrootFromRoom :
      2 * (Lnat : ℝ) + 2 * err ≤ (Lnat : ℝ) + margin)
    (hrootMargin : (Lnat : ℝ) + τ + err ≤ margin)
    (hlocalMargin : (Lnat : ℝ) + τ ≤ margin)
    (hedgeCap0 : 0 ≤ edgeCap)
    (hreserve0 : 0 ≤ (Lnat : ℝ) + margin)
    (hedgeCap : ∀ k,
      offTuranLeftThreshold G
          (offTuranReducedGraph G RD.P ε d)
          (fun i : {C // C ∈ RD.P.parts} => i.1)
          K₀ X Y ε cL k +
        offTuranRightThreshold G
          (offTuranReducedGraph G RD.P ε d)
          (fun i : {C // C ∈ RD.P.parts} => i.1)
          K₀ X Y ε cR k ≤ edgeCap)
    (hrawAllocated : ∀ b,
      parityRouteDemand T Q.S Q.D Q.col b +
          thr * edgeCap +
          ((offTuranBoolEdges K₀ b).card : ℝ) *
            ((Lnat : ℝ) + margin) +
          2 * ε * Fintype.card V ≤
        ∑ k ∈ offTuranBoolEdges K₀ b,
          hpHeadMatchingWeight G
            (offTuranReducedGraph G RD.P ε d)
            (fun i : {C // C ∈ RD.P.parts} => i.1)
            (offTuranBoolHead X Y b) cL cR k) :
    T ⊑ G := by
  let R := offTuranReducedGraph G RD.P ε d
  let C : {C // C ∈ RD.P.parts} → Finset V := fun i => i.1
  let Tset := offTuranMatchingTargets cL cR
  let head : Bool → {C // C ∈ RD.P.parts} :=
    offTuranBoolHead X Y
  let other : Bool → {C // C ∈ RD.P.parts} :=
    offTuranBoolOtherHead X Y
  let headCore : Bool → Finset V :=
    offTuranHeadCoreFamily G R C ε d Tset thr X Y
  let K : Bool → Finset κ := offTuranBoolEdges K₀
  let left : κ → Finset V := fun k => C (cL k)
  let right : κ → Finset V := fun k => C (cR k)
  let leftThreshold : κ → ℝ :=
    offTuranLeftThreshold G R C K₀ X Y ε cL
  let rightThreshold : κ → ℝ :=
    offTuranRightThreshold G R C K₀ X Y ε cR
  let retainedL : κ → Finset V :=
    offTuranLeftContact G R C ε d Tset thr K₀ X Y cL
  let retainedR : κ → Finset V :=
    offTuranRightContact G R C ε d Tset thr K₀ X Y cR
  let Good : Bool → V → Finset κ := fun b u =>
    hpAllocatedGoodMatchingEdges G C
      (hpHeadDensityCap G R C (head b)) ε (K b) cL cR u
  have hXYne : X ≠ Y := hXY.1
  have hheadEdge : ∀ b, R.Adj (head b) (other b) := by
    intro b
    cases b
    · exact hXY
    · exact hXY.symm
  have hC : ∀ i, (C i).Nonempty := RD.part_nonempty
  have huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j) :=
    fun i j hij => hij.2.1
  have hdens : ∀ i j, R.Adj i j →
      d ≤ (G.edgeDensity (C i) (C j) : ℝ) :=
    fun i j hij => hij.2.2
  have hheadSub : ∀ b, headCore b ⊆ C (head b) := by
    intro b
    exact hpOffTuranHeadCore_subset
      G R C ε d Tset thr (head b) (other b)
  have hheadSig : ∀ b,
      ε * ((C (head b)).card : ℝ) ≤ (headCore b).card := by
    intro b
    exact hpOffTuranHeadCore_epsilon_fraction
      G R C hC ε d hε0 hε1 huni Tset thr hthr0
      (head b) (other b)
      (huni _ _ (hheadEdge b)) (hdens _ _ (hheadEdge b))
      (hheadFractionRoom b)
  have hGoodBundle : ∀ b u, u ∈ headCore b →
      0 < parityRouteDemand T Q.S Q.D Q.col b →
      (Good b u).Nonempty ∧
        parityRouteDemand T Q.S Q.D Q.col b +
            ((Good b u).card : ℝ) * ((Lnat : ℝ) + margin) ≤
          ∑ k ∈ Good b u, (leftThreshold k + rightThreshold k) := by
    intro b u hu hroutePos
    have hbadReal :
        (badCount G C (hpHeadDensityCap G R C (head b))
          ε Tset u : ℝ) ≤ thr := by
      exact hpOffTuranHeadCore_badCount_le
        G R C ε d Tset thr (head b) (other b) hu
    have hsize :
        (∑ k ∈ K b,
          (((C (cL k)).card : ℝ) + ((C (cR k)).card : ℝ))) ≤
          Fintype.card V := by
      simpa [K, C] using!
        matching_endpoint_card_sum_le_univ RD.P cL cR hinj (K b)
    have hstatic :
        parityRouteDemand T Q.S Q.D Q.col b +
              thr * edgeCap +
              ((K b).card : ℝ) * ((Lnat : ℝ) + margin) ≤
          ∑ k ∈ K b, (leftThreshold k + rightThreshold k) := by
      have ht := allocated_matching_trimmed_supply
        G R C (head b) cL cR (K b) ε (Fintype.card V)
          (parityRouteDemand T Q.S Q.D Q.col b +
            thr * edgeCap +
            ((K b).card : ℝ) * ((Lnat : ℝ) + margin))
          hε0.le hsize
          (by simpa [K, R, C, head] using! hrawAllocated b)
      convert! ht using 1
      apply Finset.sum_congr rfl
      intro k hk
      have howner :
          offTuranAssignedHead K₀ X Y k = head b :=
        offTuranAssignedHead_of_mem K₀ X Y b (by simpa [K] using! hk)
      simp only [leftThreshold, rightThreshold, offTuranLeftThreshold,
        offTuranRightThreshold, howner]
    have hsupplyUpper :
        (∑ k ∈ K b, (leftThreshold k + rightThreshold k)) ≤
          ((K b).card : ℝ) * edgeCap := by
      calc
        _ ≤ ∑ _k ∈ K b, edgeCap := by
          exact Finset.sum_le_sum fun k _ => hedgeCap k
        _ = ((K b).card : ℝ) * edgeCap := by simp
    have hedgeCapPos : 0 < edgeCap := by
      by_contra hnot
      have hzero : edgeCap = 0 := le_antisymm (le_of_not_gt hnot) hedgeCap0
      rw [hzero] at hstatic hsupplyUpper
      have hreserveTerm :
          0 ≤ ((K b).card : ℝ) * ((Lnat : ℝ) + margin) :=
        mul_nonneg (Nat.cast_nonneg _) hreserve0
      linarith
    have hthrCard : thr < ((K b).card : ℝ) := by
      have hreserveTerm :
          0 ≤ ((K b).card : ℝ) * ((Lnat : ℝ) + margin) :=
        mul_nonneg (Nat.cast_nonneg _) hreserve0
      nlinarith
    have hbadCard :
        badCount G C (hpHeadDensityCap G R C (head b))
          ε Tset u < (K b).card := by
      exact_mod_cast (show
        (badCount G C (hpHeadDensityCap G R C (head b))
          ε Tset u : ℝ) < ((K b).card : ℝ) by
            exact hbadReal.trans_lt hthrCard)
    have hleftT : ∀ k, cL k ∈ Tset := by
      intro k
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    have hrightT : ∀ k, cR k ∈ Tset := by
      intro k
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    apply allocated_good_nonempty_and_static_surplus
      G C (hpHeadDensityCap G R C (head b)) ε
      Tset (K b) cL cR u hinj hleftT hrightT
      (fun k => leftThreshold k + rightThreshold k)
      (parityRouteDemand T Q.S Q.D Q.col b)
      ((Lnat : ℝ) + margin) edgeCap thr
      hbadCard hbadReal
    · intro k hk
      exact add_nonneg
        (hpTrimmedThreshold_nonneg _ _ _)
        (hpTrimmedThreshold_nonneg _ _ _)
    · intro k hk
      exact hedgeCap k
    · exact hedgeCap0
    · exact hreserve0
    · exact hstatic
  apply hp_parity_matching_tree_embedding
    T G Q.S Q.parent Q.rank Q.rank_decreases Q.edge_parent Q.parent_adj
    Q.D Q.col Q.colour_flips Q.boundary_colour
    headCore K left right retainedL retainedR leftThreshold rightThreshold
    margin τ hτ
    (ε := ε) (d := d) (Good := Good)
    (retainedLoss := retainedLoss) (err := err)
    (cap := cap) (Lnat := Lnat)
  · intro b k
    apply And.intro
    · exact Disjoint.mono (hheadSub b) (show left k ⊆ C (cL k) by rfl)
        ((partition_head_matching_edge_disjoint RD.P (head b) cL cR
          (fun j => by
            cases b <;> simp [head, haway j]) k).mono_right
              Finset.subset_union_left)
    · exact Disjoint.mono (hheadSub b) (show right k ⊆ C (cR k) by rfl)
        ((partition_head_matching_edge_disjoint RD.P (head b) cL cR
          (fun j => by
            cases b <;> simp [head, haway j]) k).mono_right
              Finset.subset_union_right)
  · intro b r
    apply disjoint_hpMatchingRegion_right
    intro k hk
    exact Disjoint.mono (hheadSub b) (by rfl)
      (partition_head_matching_edge_disjoint RD.P (head b) cL cR
        (fun j => by
          cases b <;> simp [head, haway j]) k)
  · exact hpMatchingRegion_disjoint_of_disjoint_indices
      (K false) (K true) left right
      (by simpa [K] using! offTuranBoolEdges_disjoint K₀)
      (fun k j hkj =>
        partition_matching_edges_disjoint RD.P cL cR hinj k j hkj)
  · intro b
    exact hpOffTuranHeadCore_seed_room
      G R C hC ε d hε0 hε1 huni Tset thr hthr0
      (head b) (other b)
      (huni _ _ (hheadEdge b)) (hdens _ _ (hheadEdge b))
      Q.S.card (hheadSeedRoom b)
  · intro b c hbc u hu
    have hc : head c = other b := by
      exact offTuranBoolOtherHead_eq_of_ne X Y b c hbc
    have hc' : other c = head b := by
      cases b <;> cases c <;> simp_all [head, other]
    have hu' :
        u ∈ hpOffTuranHeadCore G R C ε d Tset thr
          (other b) (head b) := by
      change u ∈ hpOffTuranHeadCore G R C ε d Tset thr
        (head c) (other c) at hu
      rw [hc, hc'] at hu
      exact hu
    have hdeg := hpOffTuranHeadCore_cross_degree
      G R C hC ε d hε0 hε1 huni Tset thr hthr0
      (head b) (other b)
      (huni _ _ (hheadEdge b)) (hdens _ _ (hheadEdge b))
      ((Q.S.card : ℝ) + 1) (hheadCrossRoom b) hu'
    exact_mod_cast hdeg
  · intro b k hk u hu
    have hownerB :
        offTuranAssignedBool K₀ k = b :=
      offTuranAssignedBool_of_mem K₀ b hk
    have hownerHead :
        offTuranAssignedHead K₀ X Y k = head b := by
      exact offTuranAssignedHead_of_mem K₀ X Y b hk
    exact hpHeadContactSet_seed_degree
      G R C ε hε0 (headCore b) (head b) (cL k)
      (hC (cL k)) Q.S.card (hcontactSeedRoom b)
      (by simpa [retainedL, offTuranLeftContact,
        headCore, hownerB, hownerHead] using! hu)
  · intro b k hk u hu
    have hownerB :
        offTuranAssignedBool K₀ k = b :=
      offTuranAssignedBool_of_mem K₀ b hk
    have hownerHead :
        offTuranAssignedHead K₀ X Y k = head b :=
      offTuranAssignedHead_of_mem K₀ X Y b hk
    exact hpHeadContactSet_seed_degree
      G R C ε hε0 (headCore b) (head b) (cR k)
      (hC (cR k)) Q.S.card (hcontactSeedRoom b)
      (by simpa [retainedR, offTuranRightContact,
        headCore, hownerB, hownerHead] using! hu)
  · intro k
    exact hC (cL k)
  · intro k
    exact hC (cR k)
  · intro k
    exact partition_matching_left_right_disjoint RD.P cL cR hinj k
  · intro k j hkj
    exact partition_matching_edges_disjoint RD.P cL cR hinj k j hkj
  · intro k
    exact hpHeadContactSet_subset G R C
      (headCore (offTuranAssignedBool K₀ k)) ε
      (offTuranAssignedHead K₀ X Y k) (cL k)
  · intro k
    exact hpHeadContactSet_subset G R C
      (headCore (offTuranAssignedBool K₀ k)) ε
      (offTuranAssignedHead K₀ X Y k) (cR k)
  · exact hε0
  · exact hε1
  · exact hd1
  · intro k
    exact (hmatch k).2.1
  · intro k
    exact (hmatch k).2.2
  · intro b u
    exact hpAllocatedGoodMatchingEdges_subset
      G C (hpHeadDensityCap G R C (head b)) ε (K b) cL cR u
  · intro b u hu hroutePos
    exact (hGoodBundle b u hu hroutePos).1
  · intro b u hu k hk
    have hkK :=
      (mem_hpAllocatedGoodMatchingEdges
        G C (hpHeadDensityCap G R C (head b)) ε
        (K b) cL cR u hk).1
    have howner :
        offTuranAssignedHead K₀ X Y k = head b :=
      offTuranAssignedHead_of_mem K₀ X Y b hkK
    simpa [left, leftThreshold, offTuranLeftThreshold, howner,
      hpHeadEndpointWeight_eq_densityCap_mul] using!
      hpAllocatedGood_left_trimmed_degree
        G C (hpHeadDensityCap G R C (head b)) ε
        (K b) cL cR u hε0.le hk
  · intro b u hu k hk
    have hkK :=
      (mem_hpAllocatedGoodMatchingEdges
        G C (hpHeadDensityCap G R C (head b)) ε
        (K b) cL cR u hk).1
    have howner :
        offTuranAssignedHead K₀ X Y k = head b :=
      offTuranAssignedHead_of_mem K₀ X Y b hkK
    simpa [right, rightThreshold, offTuranRightThreshold, howner,
      hpHeadEndpointWeight_eq_densityCap_mul] using!
      hpAllocatedGood_right_trimmed_degree
        G C (hpHeadDensityCap G R C (head b)) ε
        (K b) cL cR u hε0.le hk
  · intro c
    exact (Q.component_small c).trans hcomponentRoom
  · intro k
    exact (mul_le_mul_of_nonneg_left
      (show ((C (cL k)).card : ℝ) ≤ RD.scale by
        exact_mod_cast RD.part_size_upper (cL k)) hε0.le).trans hLsig
  · intro k
    exact (mul_le_mul_of_nonneg_left
      (show ((C (cR k)).card : ℝ) ≤ RD.scale by
        exact_mod_cast RD.part_size_upper (cR k)) hε0.le).trans hLsig
  · intro c k
    have hmax :
        (max (left k).card (right k).card : ℝ) ≤ RD.scale := by
      exact_mod_cast max_le
        (RD.part_size_upper (cL k)) (RD.part_size_upper (cR k))
    have hc := (Q.component_small c).trans hcomponentRoom
    nlinarith [mul_le_mul_of_nonneg_left hmax hε0.le]
  · intro k hpos
    have hremoved := hpHeadContactSet_removed_lt
      G R C ε hε0 hε1
      (headCore (offTuranAssignedBool K₀ k))
      (offTuranAssignedHead K₀ X Y k) (cL k)
      (by
        rw [offTuranAssignedHead_eq_boolHead]
        exact hheadSub (offTuranAssignedBool K₀ k))
      (by
        rw [offTuranAssignedHead_eq_boolHead]
        exact hheadSig (offTuranAssignedBool K₀ k))
      (hC (cL k))
      (fun h => huni _ _ h)
      (by simpa [leftThreshold, offTuranLeftThreshold] using! hpos)
    have hscale :
        ((C (cL k)).card : ℝ) ≤ RD.scale := by
      exact_mod_cast RD.part_size_upper (cL k)
    exact hremoved.le.trans
      ((mul_le_mul_of_nonneg_left hscale hε0.le).trans hretainedLoss)
  · intro k hpos
    have hremoved := hpHeadContactSet_removed_lt
      G R C ε hε0 hε1
      (headCore (offTuranAssignedBool K₀ k))
      (offTuranAssignedHead K₀ X Y k) (cR k)
      (by
        rw [offTuranAssignedHead_eq_boolHead]
        exact hheadSub (offTuranAssignedBool K₀ k))
      (by
        rw [offTuranAssignedHead_eq_boolHead]
        exact hheadSig (offTuranAssignedBool K₀ k))
      (hC (cR k))
      (fun h => huni _ _ h)
      (by simpa [rightThreshold, offTuranRightThreshold] using! hpos)
    have hscale :
        ((C (cR k)).card : ℝ) ≤ RD.scale := by
      exact_mod_cast RD.part_size_upper (cR k)
    exact hremoved.le.trans
      ((mul_le_mul_of_nonneg_left hscale hε0.le).trans hretainedLoss)
  · intro k
    exact hcap (cL k)
  · intro k
    exact hcap (cR k)
  · exact herr0
  · exact herr
  · exact hrootFromRoom
  · exact hrootMargin
  · exact hlocalMargin
  · intro k
    exact hleftCap k
  · intro k
    exact hrightCap k
  · intro b u hu hroutePos
    exact (hGoodBundle b u hu hroutePos).2

end Erdos550
