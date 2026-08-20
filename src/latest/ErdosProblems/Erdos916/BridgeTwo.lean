/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreTT

/-!
# The two-vertex bridge case for Erdős Problem 916

This file closes the smallest complementary-bridge case in the
Thomassen--Toft maximum-cycle analysis.  If the unique bridge of a maximum
chordless cycle has two vertices, minimum degree three and the absence of a
wheel force the rim to have length four.  The two bridge vertices then attach
to opposite pairs of rim vertices.  The opposite rim pair, the other opposite
pair, and one bridge vertex induce the required `K₂,₃`; all four rim
vertices have ambient degree three.
-/

namespace Erdos916

open SimpleGraph
open Erdos751.BV

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace TwoVertexBridgeData

variable {M : MaxCycleCertificate G} (D : TwoVertexBridgeData G M)

/-- A rim vertex which is not adjacent to `y` has no off-rim neighbour other
than `x`.  Chordlessness and minimum degree three therefore force its ambient
degree to be exactly three. -/
theorem degree_eq_three_of_mem_x_not_mem_y
    (hmin : ∀ v : V, 3 ≤ G.degree v) {c : V}
    (hc : c ∈ M.cycle.verts (G := G))
    (hcy : c ∉ G.neighborFinset D.y ∩ M.cycle.verts (G := G)) :
    G.degree c = 3 := by
  classical
  have hOffSub :
      G.neighborFinset c \ M.cycle.verts (G := G) ⊆ {D.x} := by
    intro z hz
    have hz' := Finset.mem_sdiff.mp hz
    have hcz : G.Adj c z := by
      simpa only [SimpleGraph.mem_neighborFinset] using hz'.1
    have hzout : z ∉ M.cycle.vSet (G := G) := by
      simpa only [M.cycle.mem_vSet_iff] using hz'.2
    have hzB : z ∈ bridgeSet (G := G) M.cycle M.bridge :=
      (M.mem_bridge_iff_not_mem_cycle G z).2 hzout
    have hzPair : z = D.x ∨ z = D.y := by
      have : z ∈ ({D.x, D.y} : Set V) := by
        rw [← D.bridge_eq]
        exact hzB
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hzPair with rfl | rfl
    · simp
    · exfalso
      apply hcy
      exact Finset.mem_inter.mpr ⟨by simpa using hcz.symm, hc⟩
  have hOffCard :
      (G.neighborFinset c \ M.cycle.verts (G := G)).card ≤ 1 := by
    simpa using Finset.card_le_card hOffSub
  have hcSet : c ∈ M.cycle.vSet (G := G) :=
    M.cycle.mem_vSet_iff.mpr hc
  have hdegree :=
    card_neighbors_off_chordless_cycle G M.cycle M.chordless hcSet
  have hminc := hmin c
  omega

/-- Symmetric form of `degree_eq_three_of_mem_x_not_mem_y`. -/
theorem degree_eq_three_of_mem_y_not_mem_x
    (hmin : ∀ v : V, 3 ≤ G.degree v) {c : V}
    (hc : c ∈ M.cycle.verts (G := G))
    (hcx : c ∉ G.neighborFinset D.x ∩ M.cycle.verts (G := G)) :
    G.degree c = 3 := by
  let D' : TwoVertexBridgeData G M :=
    { x := D.y
      y := D.x
      ne := D.ne.symm
      x_mem := D.y_mem
      y_mem := D.x_mem
      bridge_eq := by simpa [Set.pair_comm] using D.bridge_eq
      adj := D.adj.symm
      degree_x := D.degree_y
      degree_y := D.degree_x
      card_cycle_neighbors_x := D.card_cycle_neighbors_y
      card_cycle_neighbors_y := D.card_cycle_neighbors_x
      cover := by
        simpa only [Finset.union_comm] using D.cover }
  exact D'.degree_eq_three_of_mem_x_not_mem_y hmin hc hcx

end TwoVertexBridgeData

namespace MaxCycleCertificate

variable (M : MaxCycleCertificate G)

/-- In the four-rim case, the two two-element attachment sets partition the
rim. -/
private theorem attachment_sets_disjoint_of_length_four
    (D : TwoVertexBridgeData G M)
    (hlen : M.cycle.length (G := G) = 4) :
    Disjoint
      (G.neighborFinset D.x ∩ M.cycle.verts (G := G))
      (G.neighborFinset D.y ∩ M.cycle.verts (G := G)) := by
  classical
  let NX := G.neighborFinset D.x ∩ M.cycle.verts (G := G)
  let NY := G.neighborFinset D.y ∩ M.cycle.verts (G := G)
  have hCcard : (M.cycle.verts (G := G)).card = 4 := by
    rw [card_cycle_verts_eq_length G M.cycle]
    exact hlen
  have hNX : NX.card = 2 := by
    simpa only [NX] using D.card_cycle_neighbors_x
  have hNY : NY.card = 2 := by
    simpa only [NY] using D.card_cycle_neighbors_y
  have hsub : NX ∪ NY ⊆ M.cycle.verts (G := G) :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have heq : NX ∪ NY = M.cycle.verts (G := G) :=
    Finset.Subset.antisymm hsub (by simpa only [NX, NY] using D.cover)
  have hinter : (NX ∩ NY).card = 0 := by
    have hcard := Finset.card_union_add_card_inter NX NY
    rw [heq, hCcard, hNX, hNY] at hcard
    omega
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.card_eq_zero.mp
  simpa only [NX, NY] using hinter

/-- If the unique complementary bridge has two vertices and the rim has
length four, then the graph already has a wheel or the exact induced `K₂,₃`
reduction used by the density induction. -/
theorem wheel_or_reduction_of_bridge_two_cycle_four
    (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hBcard : (bridgeSet (G := G) M.cycle M.bridge).ncard = 2)
    (hlen : M.cycle.length (G := G) = 4) :
    HasWheelWitness G ∨ Nonempty (K23Reduction G) := by
  classical
  obtain ⟨D⟩ := M.exists_twoVertexBridgeData G hno hmin hBcard
  obtain ⟨F⟩ :=
    Erdos916.Cycle.fourCycleDisplay_of_length_eq_four G M.cycle hlen
  let C := M.cycle.verts (G := G)
  let NX := G.neighborFinset D.x ∩ C
  let NY := G.neighborFinset D.y ∩ C
  have hdis : Disjoint NX NY := by
    simpa only [NX, NY, C] using
      M.attachment_sets_disjoint_of_length_four D hlen
  have hcover : C ⊆ NX ∪ NY := by
    simpa only [C, NX, NY] using D.cover
  have hNXcard : NX.card = 2 := by
    simpa only [NX, C] using D.card_cycle_neighbors_x
  have hNYcard : NY.card = 2 := by
    simpa only [NY, C] using D.card_cycle_neighbors_y
  have hr0C : F.r0 ∈ C := by
    change F.r0 ∈ M.cycle.verts (G := G)
    rw [F.verts_eq]
    simp
  have hr1C : F.r1 ∈ C := by
    change F.r1 ∈ M.cycle.verts (G := G)
    rw [F.verts_eq]
    simp
  have hr2C : F.r2 ∈ C := by
    change F.r2 ∈ M.cycle.verts (G := G)
    rw [F.verts_eq]
    simp
  have hr3C : F.r3 ∈ C := by
    change F.r3 ∈ M.cycle.verts (G := G)
    rw [F.verts_eq]
    simp
  have hbelongs (r : V) (hr : r ∈ C) : r ∈ NX ∨ r ∈ NY := by
    simpa only [Finset.mem_union] using hcover hr
  have hnotY_of_X {r : V} (hr : r ∈ NX) : r ∉ NY := by
    exact Finset.disjoint_left.mp hdis hr
  have hnotX_of_Y {r : V} (hr : r ∈ NY) : r ∉ NX := by
    exact Finset.disjoint_right.mp hdis hr
  have hxout : D.x ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge D.x_mem
  have hyout : D.y ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge D.y_mem
  have hx_ne (z : V) (hz : z ∈ C) : D.x ≠ z := by
    intro h
    apply hxout
    exact h.symm ▸ M.cycle.mem_vSet_iff.mpr (by simpa only [C] using hz)
  have hy_ne (z : V) (hz : z ∈ C) : D.y ≠ z := by
    intro h
    apply hyout
    exact h.symm ▸ M.cycle.mem_vSet_iff.mpr (by simpa only [C] using hz)
  have adj_x {r : V} (hr : r ∈ NX) : G.Adj D.x r := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hr).1
  have adj_y {r : V} (hr : r ∈ NY) : G.Adj D.y r := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hr).1
  /- The labels of the display may be reflected.  Normalize them so that
  `r0` belongs to the attachment set of `x`. -/
  let D0 : TwoVertexBridgeData G M := if F.r0 ∈ NX then D else
    { x := D.y
      y := D.x
      ne := D.ne.symm
      x_mem := D.y_mem
      y_mem := D.x_mem
      bridge_eq := by simpa [Set.pair_comm] using D.bridge_eq
      adj := D.adj.symm
      degree_x := D.degree_y
      degree_y := D.degree_x
      card_cycle_neighbors_x := D.card_cycle_neighbors_y
      card_cycle_neighbors_y := D.card_cycle_neighbors_x
      cover := by simpa only [Finset.union_comm] using D.cover }
  let NX0 := G.neighborFinset D0.x ∩ C
  let NY0 := G.neighborFinset D0.y ∩ C
  have hr0X0 : F.r0 ∈ NX0 := by
    by_cases hr0X : F.r0 ∈ NX
    · have hD0x : D0.x = D.x := by simp [D0, hr0X]
      change F.r0 ∈ G.neighborFinset D0.x ∩ C
      rw [hD0x]
      exact hr0X
    · have hr0Y : F.r0 ∈ NY := (hbelongs F.r0 hr0C).resolve_left hr0X
      have hD0x : D0.x = D.y := by simp [D0, hr0X]
      change F.r0 ∈ G.neighborFinset D0.x ∩ C
      rw [hD0x]
      exact hr0Y
  have hdis0 : Disjoint NX0 NY0 := by
    simpa only [NX0, NY0, C] using
      M.attachment_sets_disjoint_of_length_four D0 hlen
  have hcover0 : C ⊆ NX0 ∪ NY0 := by
    simpa only [NX0, NY0, C] using D0.cover
  have hNX0card : NX0.card = 2 := by
    simpa only [NX0, C] using D0.card_cycle_neighbors_x
  have hNY0card : NY0.card = 2 := by
    simpa only [NY0, C] using D0.card_cycle_neighbors_y
  have belongs0 (r : V) (hr : r ∈ C) : r ∈ NX0 ∨ r ∈ NY0 := by
    simpa only [Finset.mem_union] using hcover0 hr
  have notY0_of_X0 {r : V} (hr : r ∈ NX0) : r ∉ NY0 :=
    Finset.disjoint_left.mp hdis0 hr
  have notX0_of_Y0 {r : V} (hr : r ∈ NY0) : r ∉ NX0 :=
    Finset.disjoint_right.mp hdis0 hr
  have adj_x0 {r : V} (hr : r ∈ NX0) : G.Adj D0.x r := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hr).1
  have adj_y0 {r : V} (hr : r ∈ NY0) : G.Adj D0.y r := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hr).1
  have hx0_ne (z : V) (hz : z ∈ C) : D0.x ≠ z := by
    have hout : D0.x ∉ M.cycle.vSet (G := G) :=
      mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge D0.x_mem
    intro h
    apply hout
    exact h.symm ▸ M.cycle.mem_vSet_iff.mpr (by simpa only [C] using hz)
  have hy0_ne (z : V) (hz : z ∈ C) : D0.y ≠ z := by
    have hout : D0.y ∉ M.cycle.vSet (G := G) :=
      mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge D0.y_mem
    intro h
    apply hout
    exact h.symm ▸ M.cycle.mem_vSet_iff.mpr (by simpa only [C] using hz)
  have hr2X0 : F.r2 ∈ NX0 := by
    by_contra hr2X
    have hr2Y : F.r2 ∈ NY0 := (belongs0 F.r2 hr2C).resolve_left hr2X
    by_cases hr1X : F.r1 ∈ NX0
    · have hr3Y : F.r3 ∈ NY0 := by
        have hr3 := belongs0 F.r3 hr3C
        rcases hr3 with hr3X | hr3Y
        · have hthree : 2 < NX0.card :=
            Finset.two_lt_card_iff.mpr
              ⟨F.r0, F.r1, F.r3, hr0X0, hr1X, hr3X,
                F.ne01, F.ne03, F.ne13⟩
          omega
        · exact hr3Y
      have hW := hasWheelWitness_of_fiveCycle_threeSpokes G
        D0.adj.symm (adj_x0 hr0X0) F.adj01 F.adj12 (adj_y0 hr2Y).symm
        (adj_y0 hr3Y).symm F.adj30 F.adj23.symm
        D0.ne.symm (hy0_ne F.r0 hr0C) (hy0_ne F.r1 hr1C)
        (hy0_ne F.r2 hr2C) (hx0_ne F.r0 hr0C)
        (hx0_ne F.r1 hr1C) (hx0_ne F.r2 hr2C) F.ne01 F.ne02 F.ne12
        (hy0_ne F.r3 hr3C).symm (hx0_ne F.r3 hr3C).symm
        F.ne03.symm F.ne13.symm F.ne23.symm
      exact hno hW
    · have hr1Y : F.r1 ∈ NY0 := (belongs0 F.r1 hr1C).resolve_left hr1X
      have hr3X : F.r3 ∈ NX0 := by
        have hr3 := belongs0 F.r3 hr3C
        rcases hr3 with hr3X | hr3Y
        · exact hr3X
        · have hthree : 2 < NY0.card :=
            Finset.two_lt_card_iff.mpr
              ⟨F.r1, F.r2, F.r3, hr1Y, hr2Y, hr3Y,
                F.ne12, F.ne13, F.ne23⟩
          omega
      have hW := hasWheelWitness_of_fiveCycle_threeSpokes G
        D0.adj.symm (adj_x0 hr0X0) F.adj30.symm F.adj23.symm
          (adj_y0 hr2Y).symm
        (adj_y0 hr1Y).symm F.adj01.symm F.adj12
        D0.ne.symm (hy0_ne F.r0 hr0C) (hy0_ne F.r3 hr3C)
        (hy0_ne F.r2 hr2C) (hx0_ne F.r0 hr0C)
        (hx0_ne F.r3 hr3C) (hx0_ne F.r2 hr2C)
        F.ne03 F.ne02 F.ne23.symm
        (hy0_ne F.r1 hr1C).symm (hx0_ne F.r1 hr1C).symm
        F.ne01.symm F.ne13 F.ne12
      exact hno hW
  have hr0Y0 : F.r0 ∉ NY0 := notY0_of_X0 hr0X0
  have hr2Y0 : F.r2 ∉ NY0 := notY0_of_X0 hr2X0
  have hr1Y0 : F.r1 ∈ NY0 := by
    have hr1 := belongs0 F.r1 hr1C
    rcases hr1 with hr1X | hr1Y
    · have hthree : 2 < NX0.card :=
        Finset.two_lt_card_iff.mpr
          ⟨F.r0, F.r1, F.r2, hr0X0, hr1X, hr2X0,
            F.ne01, F.ne02, F.ne12⟩
      omega
    · exact hr1Y
  have hr3Y0 : F.r3 ∈ NY0 := by
    have hr3 := belongs0 F.r3 hr3C
    rcases hr3 with hr3X | hr3Y
    · have hthree : 2 < NX0.card :=
        Finset.two_lt_card_iff.mpr
          ⟨F.r0, F.r2, F.r3, hr0X0, hr2X0, hr3X,
            F.ne02, F.ne03, F.ne23⟩
      omega
    · exact hr3Y
  have hr1X0 : F.r1 ∉ NX0 := notX0_of_Y0 hr1Y0
  have hr3X0 : F.r3 ∉ NX0 := notX0_of_Y0 hr3Y0
  have hdeg0 : G.degree F.r0 = 3 :=
    D0.degree_eq_three_of_mem_x_not_mem_y hmin hr0C (by simpa only [NY0, C] using hr0Y0)
  have hdeg2 : G.degree F.r2 = 3 :=
    D0.degree_eq_three_of_mem_x_not_mem_y hmin hr2C (by simpa only [NY0, C] using hr2Y0)
  have hdeg1 : G.degree F.r1 = 3 :=
    D0.degree_eq_three_of_mem_y_not_mem_x hmin hr1C (by simpa only [NX0, C] using hr1X0)
  have hdeg3 : G.degree F.r3 = 3 :=
    D0.degree_eq_three_of_mem_y_not_mem_x hmin hr3C (by simpa only [NX0, C] using hr3X0)
  have hN0 : G.neighborFinset F.r0 = {F.r1, F.r3, D0.x} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simpa using F.adj01
      · simpa using F.adj30.symm
      · simpa using (adj_x0 hr0X0).symm
    · rw [G.card_neighborFinset_eq_degree, hdeg0]
      simp [F.ne13, (hx0_ne F.r1 hr1C).symm,
        (hx0_ne F.r3 hr3C).symm]
  have hN2 : G.neighborFinset F.r2 = {F.r1, F.r3, D0.x} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simpa using F.adj12.symm
      · simpa using F.adj23
      · simpa using (adj_x0 hr2X0).symm
    · rw [G.card_neighborFinset_eq_degree, hdeg2]
      simp [F.ne13, (hx0_ne F.r1 hr1C).symm,
        (hx0_ne F.r3 hr3C).symm]
  let T : TwinTriple G :=
    { u := F.r0
      v := F.r2
      a := F.r1
      b := F.r3
      c := D0.x
      huv := F.ne02
      hab := F.ne13
      hac := (hx0_ne F.r1 hr1C).symm
      hbc := (hx0_ne F.r3 hr3C).symm
      neighbors_u := hN0
      neighbors_v := hN2
      degree_u := hdeg0
      degree_v := hdeg2
      degree_a := hdeg1
      degree_b := hdeg3 }
  exact T.wheel_or_reduction

/-- Complete unconditional classification of the two-vertex bridge case. -/
theorem wheel_or_reduction_of_bridge_ncard_eq_two
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hBcard : (bridgeSet (G := G) M.cycle M.bridge).ncard = 2) :
    HasWheelWitness G ∨ Nonempty (K23Reduction G) := by
  by_cases hW : HasWheelWitness G
  · exact Or.inl hW
  have hle := M.cycle_length_le_four_of_bridge_ncard_eq_two G hW hmin hBcard
  have hge : 3 ≤ M.cycle.length (G := G) := M.cycle.len_ge_three
  have hcases : M.cycle.length (G := G) = 3 ∨ M.cycle.length (G := G) = 4 := by
    omega
  rcases hcases with hthree | hfour
  · exact Or.inl (M.hasWheelWitness_of_bridge_two_cycle_three G hW hmin hBcard hthree)
  · exact M.wheel_or_reduction_of_bridge_two_cycle_four hW hmin hBcard hfour

end MaxCycleCertificate

end Erdos916
