/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreTT

/-!
# The single-block case of the Thomassen--Toft cycle analysis

This file closes the case in which the connected complement of the selected
induced cycle is itself vertex-two-connected.  The attachment-alternation
lemma from `CoreTT` forces a wheel on every rim of length at least five and is
inconsistent on a triangular rim.  On the remaining four-cycle, opposite rim
vertices are degree-three false twins and the AHT converter gives exactly the
required `K23Reduction`.
-/

namespace Erdos916

open SimpleGraph
open Erdos751.BV

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem getVert_mem_cycle
    (C : Cycle (G := G)) (i : Nat) :
    C.walk.getVert i ∈ C.vSet (G := G) := by
  exact (mem_cycle_vSet_iff_mem_support G C _).2
    (C.walk.getVert_mem_support (i := i))

/-- In the no-wheel branch, attachment alternation rules out five distinct
successive vertices of the selected cycle. -/
theorem MaxCycleCertificate.cycle_length_le_four_of_complement_twoConnected
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hdelete : ∀ d : {v : V // v ∉ M.cycle.vSet (G := G)},
      ((G.induce (M.cycle.vSet (G := G))ᶜ).induce
        (fun w => w ≠ d)).Connected) :
    M.cycle.length (G := G) ≤ 4 := by
  classical
  by_contra hnot
  have hlen : 5 ≤ M.cycle.walk.length := by
    change ¬M.cycle.walk.length ≤ 4 at hnot
    omega
  let r0 := M.cycle.walk.getVert 0
  let r1 := M.cycle.walk.getVert 1
  let r2 := M.cycle.walk.getVert 2
  let r3 := M.cycle.walk.getVert 3
  let r4 := M.cycle.walk.getVert 4
  have hr0 : r0 ∈ M.cycle.vSet (G := G) := getVert_mem_cycle G M.cycle 0
  have hr1 : r1 ∈ M.cycle.vSet (G := G) := getVert_mem_cycle G M.cycle 1
  have hr2 : r2 ∈ M.cycle.vSet (G := G) := getVert_mem_cycle G M.cycle 2
  have hr3 : r3 ∈ M.cycle.vSet (G := G) := getVert_mem_cycle G M.cycle 3
  have hr4 : r4 ∈ M.cycle.vSet (G := G) := getVert_mem_cycle G M.cycle 4
  have hadj01 : G.Adj r0 r1 := by
    simpa only [r0, r1] using
      M.cycle.walk.adj_getVert_succ (i := 0) (by omega)
  have hadj12 : G.Adj r1 r2 := by
    simpa only [r1, r2] using
      M.cycle.walk.adj_getVert_succ (i := 1) (by omega)
  have hadj23 : G.Adj r2 r3 := by
    simpa only [r2, r3] using
      M.cycle.walk.adj_getVert_succ (i := 2) (by omega)
  have hadj34 : G.Adj r3 r4 := by
    simpa only [r3, r4] using
      M.cycle.walk.adj_getVert_succ (i := 3) (by omega)
  have hne (i j : Nat) (hi : i ≤ 4) (hj : j ≤ 4) (hij : i ≠ j) :
      M.cycle.walk.getVert i ≠ M.cycle.walk.getVert j := by
    intro heq
    have heqIdx := M.cycle.isCycle.getVert_injOn'
      (show i ≤ M.cycle.walk.length - 1 by omega)
      (show j ≤ M.cycle.walk.length - 1 by omega) heq
    exact hij heqIdx
  have hne02 : r0 ≠ r2 := hne 0 2 (by omega) (by omega) (by omega)
  have hne10 : r1 ≠ r0 := hne 1 0 (by omega) (by omega) (by omega)
  have hne12 : r1 ≠ r2 := hne 1 2 (by omega) (by omega) (by omega)
  have hne13 : r1 ≠ r3 := hne 1 3 (by omega) (by omega) (by omega)
  have hne32 : r3 ≠ r2 := hne 3 2 (by omega) (by omega) (by omega)
  have hne34 : r3 ≠ r4 := hne 3 4 (by omega) (by omega) (by omega)
  have hne24 : r2 ≠ r4 := hne 2 4 (by omega) (by omega) (by omega)
  obtain ⟨a0, ha0B, hr0a0⟩ := M.exists_adj_bridge G hr0
  obtain ⟨a1, ha1B, hr1a1⟩ := M.exists_adj_bridge G hr1
  obtain ⟨a2, ha2B, hr2a2⟩ := M.exists_adj_bridge G hr2
  obtain ⟨a3, ha3B, hr3a3⟩ := M.exists_adj_bridge G hr3
  obtain ⟨a4, ha4B, hr4a4⟩ := M.exists_adj_bridge G hr4
  have h02 := M.attachment_alternation_of_complement_twoConnected G hno
    hr0 hr1 hr2 hadj01.symm hadj12 hr0a0 hr1a1 hr2a2.symm
    ha0B ha1B ha2B hne02 hne10 hne12 hdelete
  have h24 := M.attachment_alternation_of_complement_twoConnected G hno
    hr2 hr3 hr4 hadj23.symm hadj34 hr2a2 hr3a3 hr4a4.symm
    ha2B ha3B ha4B hne24 hne32 hne34 hdelete
  have hr0N : r0 ∈ G.neighborFinset a2 ∩ M.cycle.verts (G := G) := by
    refine Finset.mem_inter.mpr ⟨?_, (M.cycle.mem_vSet_iff (G := G)).1 hr0⟩
    simpa only [SimpleGraph.mem_neighborFinset, h02.1] using hr0a0.symm
  have hr2N : r2 ∈ G.neighborFinset a2 ∩ M.cycle.verts (G := G) := by
    exact Finset.mem_inter.mpr ⟨by simpa using hr2a2.symm,
      (M.cycle.mem_vSet_iff (G := G)).1 hr2⟩
  have hr4N : r4 ∈ G.neighborFinset a2 ∩ M.cycle.verts (G := G) := by
    refine Finset.mem_inter.mpr ⟨?_, (M.cycle.mem_vSet_iff (G := G)).1 hr4⟩
    have ha24 : a2 = a4 := h24.1
    simpa only [SimpleGraph.mem_neighborFinset, ha24] using hr4a4.symm
  have hthree : 3 ≤
      (G.neighborFinset a2 ∩ M.cycle.verts (G := G)).card := by
    have := Finset.two_lt_card_iff.mpr
      ⟨r0, r2, r4, hr0N, hr2N, hr4N, hne02, hne 0 4 (by omega)
        (by omega) (by omega), hne24⟩
    omega
  exact hno (M.hasWheelWitness_of_three_neighbors G a2 ha2B hthree)

/-- On a triangular rim, the three cyclic applications of attachment
alternation contradict each other. -/
theorem MaxCycleCertificate.cycle_length_ne_three_of_complement_twoConnected
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hdelete : ∀ d : {v : V // v ∉ M.cycle.vSet (G := G)},
      ((G.induce (M.cycle.vSet (G := G))ᶜ).induce
        (fun w => w ≠ d)).Connected) :
    M.cycle.length (G := G) ≠ 3 := by
  classical
  intro hlen
  obtain ⟨T⟩ := Erdos916.Cycle.triangleDisplay_of_length_eq_three G M.cycle hlen
  obtain ⟨a0, ha0B, h0a0⟩ := M.exists_adj_bridge G (c := T.r0)
    ((M.cycle.mem_vSet_iff (G := G)).2 (by rw [T.verts_eq]; simp))
  obtain ⟨a1, ha1B, h1a1⟩ := M.exists_adj_bridge G (c := T.r1)
    ((M.cycle.mem_vSet_iff (G := G)).2 (by rw [T.verts_eq]; simp))
  obtain ⟨a2, ha2B, h2a2⟩ := M.exists_adj_bridge G (c := T.r2)
    ((M.cycle.mem_vSet_iff (G := G)).2 (by rw [T.verts_eq]; simp))
  have hr0 : T.r0 ∈ M.cycle.vSet (G := G) :=
    (M.cycle.mem_vSet_iff (G := G)).2 (by rw [T.verts_eq]; simp)
  have hr1 : T.r1 ∈ M.cycle.vSet (G := G) :=
    (M.cycle.mem_vSet_iff (G := G)).2 (by rw [T.verts_eq]; simp)
  have hr2 : T.r2 ∈ M.cycle.vSet (G := G) :=
    (M.cycle.mem_vSet_iff (G := G)).2 (by rw [T.verts_eq]; simp)
  have h012 := M.attachment_alternation_of_complement_twoConnected G hno
    hr0 hr1 hr2 T.adj01.symm T.adj12 h0a0 h1a1 h2a2.symm
    ha0B ha1B ha2B T.ne02 T.ne01.symm T.ne12 hdelete
  have h120 := M.attachment_alternation_of_complement_twoConnected G hno
    hr1 hr2 hr0 T.adj12.symm T.adj20 h1a1 h2a2 h0a0.symm
    ha1B ha2B ha0B T.ne01.symm T.ne12.symm T.ne02.symm hdelete
  exact h012.2 h120.1

/-- The complete single-block alternative.  Here "single block" is used in
the strong form needed by the local path lemma: deleting any vertex of the
cycle complement leaves that complement connected. -/
theorem MaxCycleCertificate.wheel_or_reduction_of_complement_twoConnected
    (M : MaxCycleCertificate G)
    (hdelete : ∀ d : {v : V // v ∉ M.cycle.vSet (G := G)},
      ((G.induce (M.cycle.vSet (G := G))ᶜ).induce
        (fun w => w ≠ d)).Connected) :
    HasWheelWitness G ∨ Nonempty (K23Reduction G) := by
  classical
  by_cases hW : HasWheelWitness G
  · exact Or.inl hW
  have hle := M.cycle_length_le_four_of_complement_twoConnected G hW hdelete
  have hne3 := M.cycle_length_ne_three_of_complement_twoConnected G hW hdelete
  have hlen : M.cycle.length (G := G) = 4 := by
    have hthree := M.cycle.len_ge_three
    change 3 ≤ M.cycle.length (G := G) at hthree
    omega
  obtain ⟨F⟩ := Erdos916.Cycle.fourCycleDisplay_of_length_eq_four G M.cycle hlen
  have hr0 : F.r0 ∈ M.cycle.vSet (G := G) :=
    (M.cycle.mem_vSet_iff (G := G)).2 (by rw [F.verts_eq]; simp)
  have hr1 : F.r1 ∈ M.cycle.vSet (G := G) :=
    (M.cycle.mem_vSet_iff (G := G)).2 (by rw [F.verts_eq]; simp)
  have hr2 : F.r2 ∈ M.cycle.vSet (G := G) :=
    (M.cycle.mem_vSet_iff (G := G)).2 (by rw [F.verts_eq]; simp)
  have hr3 : F.r3 ∈ M.cycle.vSet (G := G) :=
    (M.cycle.mem_vSet_iff (G := G)).2 (by rw [F.verts_eq]; simp)
  obtain ⟨a0, ha0B, h0a0⟩ := M.exists_adj_bridge G (c := F.r0) hr0
  obtain ⟨a1, ha1B, h1a1⟩ := M.exists_adj_bridge G (c := F.r1) hr1
  obtain ⟨a2, ha2B, h2a2⟩ := M.exists_adj_bridge G (c := F.r2) hr2
  obtain ⟨a3, ha3B, h3a3⟩ := M.exists_adj_bridge G (c := F.r3) hr3
  have h012 := M.attachment_alternation_of_complement_twoConnected G hW
    hr0 hr1 hr2 F.adj01.symm F.adj12 h0a0 h1a1 h2a2.symm
    ha0B ha1B ha2B F.ne02 F.ne01.symm F.ne12 hdelete
  have h123 := M.attachment_alternation_of_complement_twoConnected G hW
    hr1 hr2 hr3 F.adj12.symm F.adj23 h1a1 h2a2 h3a3.symm
    ha1B ha2B ha3B F.ne13 F.ne12.symm F.ne23 hdelete
  have hoff0 :
      G.neighborFinset F.r0 \ M.cycle.verts (G := G) = {a0} := by
    ext w
    constructor
    · intro hw
      have hw' := Finset.mem_sdiff.mp hw
      have hwB : w ∈ bridgeSet (G := G) M.cycle M.bridge :=
        (M.mem_bridge_iff_not_mem_cycle G w).2
          (fun hwC => hw'.2 ((M.cycle.mem_vSet_iff (G := G)).1 hwC))
      have halt := M.attachment_alternation_of_complement_twoConnected G hW
        hr0 hr1 hr2 F.adj01.symm F.adj12
        (by simpa only [SimpleGraph.mem_neighborFinset] using hw'.1)
        h1a1 h2a2.symm hwB ha1B ha2B
        F.ne02 F.ne01.symm F.ne12 hdelete
      simpa only [Finset.mem_singleton] using halt.1.trans h012.1.symm
    · intro hw
      have hwa : w = a0 := by simpa only [Finset.mem_singleton] using hw
      subst w
      exact Finset.mem_sdiff.mpr ⟨by simpa using h0a0,
        fun ha0C => (mem_bridge_imp_not_mem_cycle
          (G := G) M.cycle M.bridge ha0B)
            ((M.cycle.mem_vSet_iff (G := G)).2 ha0C)⟩
  have hoff2 :
      G.neighborFinset F.r2 \ M.cycle.verts (G := G) = {a0} := by
    ext w
    constructor
    · intro hw
      have hw' := Finset.mem_sdiff.mp hw
      have hwB : w ∈ bridgeSet (G := G) M.cycle M.bridge :=
        (M.mem_bridge_iff_not_mem_cycle G w).2
          (fun hwC => hw'.2 ((M.cycle.mem_vSet_iff (G := G)).1 hwC))
      have halt := M.attachment_alternation_of_complement_twoConnected G hW
        hr0 hr1 hr2 F.adj01.symm F.adj12 h0a0 h1a1
        (by
          have hadj : G.Adj F.r2 w := by
            simpa only [SimpleGraph.mem_neighborFinset] using hw'.1
          exact hadj.symm)
        ha0B ha1B hwB F.ne02 F.ne01.symm F.ne12 hdelete
      simpa only [Finset.mem_singleton] using halt.1.symm
    · intro hw
      have hwa : w = a0 := by simpa only [Finset.mem_singleton] using hw
      subst w
      exact Finset.mem_sdiff.mpr ⟨by
        have hadj : G.Adj F.r2 a0 := by simpa only [h012.1] using h2a2
        simpa using hadj,
        fun ha0C => (mem_bridge_imp_not_mem_cycle
          (G := G) M.cycle M.bridge ha0B)
            ((M.cycle.mem_vSet_iff (G := G)).2 ha0C)⟩
  have hoff1 :
      G.neighborFinset F.r1 \ M.cycle.verts (G := G) = {a1} := by
    ext w
    constructor
    · intro hw
      have hw' := Finset.mem_sdiff.mp hw
      have hwB : w ∈ bridgeSet (G := G) M.cycle M.bridge :=
        (M.mem_bridge_iff_not_mem_cycle G w).2
          (fun hwC => hw'.2 ((M.cycle.mem_vSet_iff (G := G)).1 hwC))
      have halt := M.attachment_alternation_of_complement_twoConnected G hW
        hr1 hr2 hr3 F.adj12.symm F.adj23
        (by simpa only [SimpleGraph.mem_neighborFinset] using hw'.1)
        h2a2 h3a3.symm hwB ha2B ha3B
        F.ne13 F.ne12.symm F.ne23 hdelete
      simpa only [Finset.mem_singleton] using halt.1.trans h123.1.symm
    · intro hw
      have hwa : w = a1 := by simpa only [Finset.mem_singleton] using hw
      subst w
      exact Finset.mem_sdiff.mpr ⟨by simpa using h1a1,
        fun ha1C => (mem_bridge_imp_not_mem_cycle
          (G := G) M.cycle M.bridge ha1B)
            ((M.cycle.mem_vSet_iff (G := G)).2 ha1C)⟩
  have hoff3 :
      G.neighborFinset F.r3 \ M.cycle.verts (G := G) = {a1} := by
    ext w
    constructor
    · intro hw
      have hw' := Finset.mem_sdiff.mp hw
      have hwB : w ∈ bridgeSet (G := G) M.cycle M.bridge :=
        (M.mem_bridge_iff_not_mem_cycle G w).2
          (fun hwC => hw'.2 ((M.cycle.mem_vSet_iff (G := G)).1 hwC))
      have halt := M.attachment_alternation_of_complement_twoConnected G hW
        hr1 hr2 hr3 F.adj12.symm F.adj23 h1a1 h2a2
        (by
          have hadj : G.Adj F.r3 w := by
            simpa only [SimpleGraph.mem_neighborFinset] using hw'.1
          exact hadj.symm)
        ha1B ha2B hwB F.ne13 F.ne12.symm F.ne23 hdelete
      simpa only [Finset.mem_singleton] using halt.1.symm
    · intro hw
      have hwa : w = a1 := by simpa only [Finset.mem_singleton] using hw
      subst w
      exact Finset.mem_sdiff.mpr ⟨by
        have hadj : G.Adj F.r3 a1 := by simpa only [h123.1] using h3a3
        simpa using hadj,
        fun ha1C => (mem_bridge_imp_not_mem_cycle
          (G := G) M.cycle M.bridge ha1B)
            ((M.cycle.mem_vSet_iff (G := G)).2 ha1C)⟩
  have hdeg0 : G.degree F.r0 = 3 := by
    have h := card_neighbors_off_chordless_cycle G M.cycle M.chordless hr0
    rw [hoff0] at h
    simpa using h.symm
  have hdeg1 : G.degree F.r1 = 3 := by
    have h := card_neighbors_off_chordless_cycle G M.cycle M.chordless hr1
    rw [hoff1] at h
    simpa using h.symm
  have hdeg3 : G.degree F.r3 = 3 := by
    have h := card_neighbors_off_chordless_cycle G M.cycle M.chordless hr3
    rw [hoff3] at h
    simpa using h.symm
  have hN0 :
      G.neighborFinset F.r0 ∩ M.cycle.verts (G := G) = {F.r1, F.r3} := by
    have hsub : ({F.r1, F.r3} : Finset V) ⊆
        G.neighborFinset F.r0 ∩ M.cycle.verts (G := G) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨by simpa using F.adj01,
          (M.cycle.mem_vSet_iff (G := G)).1 hr1⟩
      · exact Finset.mem_inter.mpr ⟨by simpa using F.adj30.symm,
          (M.cycle.mem_vSet_iff (G := G)).1 hr3⟩
    have hcard := card_neighbors_on_chordless_cycle_eq_two
      G M.cycle M.chordless hr0
    have heq : ({F.r1, F.r3} : Finset V) =
        G.neighborFinset F.r0 ∩ M.cycle.verts (G := G) :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [F.ne13] using hcard.le)
    exact heq.symm
  have hN2 :
      G.neighborFinset F.r2 ∩ M.cycle.verts (G := G) = {F.r1, F.r3} := by
    have hsub : ({F.r1, F.r3} : Finset V) ⊆
        G.neighborFinset F.r2 ∩ M.cycle.verts (G := G) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨by simpa using F.adj12.symm,
          (M.cycle.mem_vSet_iff (G := G)).1 hr1⟩
      · exact Finset.mem_inter.mpr ⟨by simpa using F.adj23,
          (M.cycle.mem_vSet_iff (G := G)).1 hr3⟩
    have hcard := card_neighbors_on_chordless_cycle_eq_two
      G M.cycle M.chordless hr2
    have heq : ({F.r1, F.r3} : Finset V) =
        G.neighborFinset F.r2 ∩ M.cycle.verts (G := G) :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [F.ne13] using hcard.le)
    exact heq.symm
  have htwin : AreFalseTwins G F.r0 F.r2 := by
    refine ⟨F.ne02, ?_⟩
    ext w
    simp only [SimpleGraph.mem_neighborSet]
    constructor
    · intro h0w
      by_cases hwC : w ∈ M.cycle.verts (G := G)
      · have hw : w ∈ G.neighborFinset F.r0 ∩ M.cycle.verts (G := G) :=
          Finset.mem_inter.mpr ⟨by simpa using h0w, hwC⟩
        rw [hN0] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact F.adj12.symm
        · exact F.adj23
      · have hw : w ∈ G.neighborFinset F.r0 \ M.cycle.verts (G := G) :=
          Finset.mem_sdiff.mpr ⟨by simpa using h0w, hwC⟩
        rw [hoff0] at hw
        have hwa : w = a0 := by simpa only [Finset.mem_singleton] using hw
        subst w
        simpa only [h012.1] using h2a2
    · intro h2w
      by_cases hwC : w ∈ M.cycle.verts (G := G)
      · have hw : w ∈ G.neighborFinset F.r2 ∩ M.cycle.verts (G := G) :=
          Finset.mem_inter.mpr ⟨by simpa using h2w, hwC⟩
        rw [hN2] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact F.adj01
        · exact F.adj30.symm
      · have hw : w ∈ G.neighborFinset F.r2 \ M.cycle.verts (G := G) :=
          Finset.mem_sdiff.mpr ⟨by simpa using h2w, hwC⟩
        rw [hoff2] at hw
        have hwa : w = a0 := by simpa only [Finset.mem_singleton] using hw
        subst w
        exact h0a0
  exact wheel_or_reduction_of_falseTwins htwin hdeg0
    F.adj01 F.adj30.symm F.ne13 hdeg1 hdeg3

/-- Circuit-proof interface to the same single-block analysis. -/
theorem MaxCycleCertificate.wheel_or_degreeThreeFalseTwins_of_complement_twoConnected
    (M : MaxCycleCertificate G)
    (hdelete : ∀ d : {v : V // v ∉ M.cycle.vSet (G := G)},
      ((G.induce (M.cycle.vSet (G := G))ᶜ).induce
        (fun w => w ≠ d)).Connected) :
    HasWheelWitness G ∨
      ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  rcases M.wheel_or_reduction_of_complement_twoConnected G hdelete with
    hW | hR
  · exact Or.inl hW
  · obtain ⟨R⟩ := hR
    obtain ⟨u, v, htwin, hdeg, -⟩ := hasRichFalseTwins_of_k23Reduction R
    exact Or.inr ⟨u, v, htwin, hdeg⟩

end Erdos916
