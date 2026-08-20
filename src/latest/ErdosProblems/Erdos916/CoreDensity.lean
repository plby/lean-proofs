/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreRigidity
import ErdosProblems.Erdos916.Connectivity
import ErdosProblems.Erdos916.Torso
import ErdosProblems.Erdos751

/-!
# Density circuits are vertex-two-connected

This file records the connectivity consequence of the vertex-minimal
`(2,3)`-circuit reduction.  It is useful for a density-aware approach to
Erdős Problem 916: disconnectedness would put the same forbidden density in
one connected component, while a cut vertex would put it in one of the two
proper induced cut pieces.  Both conclusions contradict circuit sparsity.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Is23Circuit

noncomputable local instance componentFintype
    (C : G.ConnectedComponent) : Fintype C := Fintype.ofFinite C

noncomputable local instance componentAdjDecidable
    (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj :=
  Classical.decRel _

/-- A component graph is graph-isomorphic to the induced graph on its
ambient support. -/
noncomputable def componentIsoInduce (C : G.ConnectedComponent) :
    C.toSimpleGraph ≃g G.induce C.supp where
  toEquiv := Equiv.refl C
  map_rel_iff' := Iff.rfl

/-- The component carrier is equivalent to the finite support obtained by
turning that support into a finset. -/
noncomputable def componentEquivSupportFinset (C : G.ConnectedComponent) :
    C ≃ C.supp.toFinset where
  toFun x := ⟨x.1, by
    rw [Set.mem_toFinset]
    change G.connectedComponentMk x.1 = C
    have hx := x.2
    change G.connectedComponentMk x.1 = C at hx
    exact hx⟩
  invFun x := ⟨x.1, by
    change G.connectedComponentMk x.1 = C
    have hx := x.2
    rw [Set.mem_toFinset] at hx
    change G.connectedComponentMk x.1 = C at hx
    exact hx⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- A `(2,3)`-circuit on at least four vertices is connected. -/
theorem connected (hcircuit : Is23Circuit G)
    (hcard : 4 ≤ Fintype.card V) : G.Connected := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hconn
  have hnpre : ¬G.Preconnected := by
    intro hp
    exact hconn (SimpleGraph.Connected.mk hp)
  have hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2 := by
    have hcount := hcircuit.1
    dsimp [Has23CircuitCount] at hcount
    omega
  obtain ⟨C, hCdense⟩ :=
    exists_dense_connectedComponent G inferInstance hdense
  let S : Finset V := C.supp.toFinset
  have hScard : S.card = Fintype.card C := by
    calc
      S.card = Fintype.card S := by simp
      _ = Fintype.card C :=
        Fintype.card_congr (componentEquivSupportFinset (G := G) C).symm
  have hClt : Fintype.card C < Fintype.card V :=
    connectedComponent_card_lt_of_not_preconnected G hnpre C
  have hSne : S ≠ Finset.univ := by
    intro h
    have : S.card = Fintype.card V := by rw [h]; simp
    omega
  obtain ⟨v, hv⟩ := C.nonempty_supp
  let vC : C := ⟨v, hv⟩
  have hdegC : 3 ≤ C.toSimpleGraph.degree vC := by
    rw [degree_connectedComponent G C vC]
    exact hcircuit.degree_three_le hcard v
  have hC4 : 4 ≤ Fintype.card C := by
    have hlt := C.toSimpleGraph.degree_lt_card_verts vC
    omega
  have hS2 : 2 ≤ S.card := by omega
  have hsparse := hcircuit.2 S hS2 hSne
  have hedgeEq :
      C.toSimpleGraph.edgeFinset.card =
        (G.induce (S : Set V)).edgeFinset.card := by
    let e : C.toSimpleGraph ≃g G.induce (S : Set V) :=
      { toEquiv := componentEquivSupportFinset (G := G) C
        map_rel_iff' := Iff.rfl }
    exact e.card_edgeFinset_eq
  rw [← hedgeEq, hScard] at hsparse
  omega

/-- A `(2,3)`-circuit on at least four vertices stays connected after any
single vertex is deleted. -/
theorem connected_delete (hcircuit : Is23Circuit G)
    (hcard : 4 ≤ Fintype.card V) (c : V) :
    (G.induce (fun w : V ↦ w ≠ c)).Connected := by
  classical
  have hGconn : G.Connected := hcircuit.connected hcard
  have hneNe : Nonempty {w : V // w ≠ c} := by
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
    by_cases hac : a ≠ c
    · exact ⟨⟨a, hac⟩⟩
    · exact ⟨⟨b, fun hbc ↦ hab ((not_ne_iff.mp hac).trans hbc.symm)⟩⟩
  letI : Nonempty {w : V // w ≠ c} := hneNe
  have hneComp : Nonempty {w : V // w ∈ ({c}ᶜ : Set V)} := by
    obtain ⟨w⟩ := hneNe
    exact ⟨⟨w.1, by simpa using w.2⟩⟩
  letI : Nonempty {w : V // w ∈ ({c}ᶜ : Set V)} := hneComp
  by_contra hdelete
  have hcut : IsCutVertex G c := by
    change ¬(G.induce (fun w : V ↦ w ≠ c)).Preconnected
    intro hp
    apply hdelete
    exact { preconnected := hp, nonempty := hneNe }
  let K : (deleteVertex G c).ConnectedComponent :=
    (deleteVertex G c).connectedComponentMk
      (Classical.choice hneNe)
  have hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2 := by
    have hcount := hcircuit.1
    dsimp [Has23CircuitCount] at hcount
    omega
  obtain ⟨hpieceProper, hremProper, hdensePiece | hdenseRem⟩ :=
    CutDensity.cut_dense_piece (G := G) hGconn hcut K hdense
  · let S : Finset V := CutDensity.piece G c K
    obtain ⟨v, hvside⟩ := ComponentEndBlock.side_nonempty (G := G) c K
    have hvc : v ≠ c := by
      intro h
      subst v
      exact ComponentEndBlock.cut_not_mem_side (G := G) c K hvside
    have hcS : c ∈ S := CutDensity.cut_mem_piece (G := G) c K
    have hvS : v ∈ S :=
      (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hvside)
    have hS2 : 2 ≤ S.card := by
      rw [show (2 : ℕ) = 1 + 1 by omega]
      exact Finset.one_lt_card_iff.mpr ⟨c, v, hcS, hvS, hvc.symm⟩
    have hsparse := hcircuit.2 S hS2 hpieceProper
    have hdenseS :
        2 * S.card ≤ (G.induce (S : Set V)).edgeFinset.card + 2 := by
      simpa only [Fintype.card_coe] using hdensePiece
    omega
  · let S : Finset V := CutDensity.remainder G c K
    have hex : ∃ v : V, v ∉ CutDensity.piece G c K := by
      by_contra h
      push Not at h
      exact hpieceProper (Finset.eq_univ_of_forall h)
    obtain ⟨v, hvpiece⟩ := hex
    have hvc : v ≠ c := by
      intro h
      subst v
      exact hvpiece (CutDensity.cut_mem_piece (G := G) c K)
    have hvside : v ∉ ComponentEndBlock.side c K := by
      intro hv
      exact hvpiece ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hv))
    have hcS : c ∈ S := CutDensity.cut_mem_remainder (G := G) c K
    have hvS : v ∈ S :=
      (CutDensity.mem_remainder_iff (G := G)).mpr hvside
    have hS2 : 2 ≤ S.card := by
      rw [show (2 : ℕ) = 1 + 1 by omega]
      exact Finset.one_lt_card_iff.mpr ⟨c, v, hcS, hvS, hvc.symm⟩
    have hsparse := hcircuit.2 S hS2 hremProper
    have hdenseS :
        2 * S.card ≤ (G.induce (S : Set V)).edgeFinset.card + 2 := by
      simpa only [Fintype.card_coe] using hdenseRem
    omega

/-- Circuit sparsity supplies exactly the Bondy--Vince vertex-two-connected
hypothesis used by the maximum-chordless-cycle machinery. -/
theorem vertexTwoConnected (hcircuit : Is23Circuit G)
    (hcard : 4 ≤ Fintype.card V) : Erdos751.BV.VertexTwoConnected (G := G) := by
  refine ⟨hcircuit.connected hcard, ?_⟩
  exact hcircuit.connected_delete hcard

end Is23Circuit

end Erdos916
