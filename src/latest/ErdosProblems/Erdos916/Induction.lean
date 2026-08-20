/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.Density
import ErdosProblems.Erdos916.Connectivity
import ErdosProblems.Erdos916.Torso

/-!
# The density induction for Erdős Problem 916

This file reduces the theorem to its genuinely two-connected, minimum-degree-three
structural core.  Disconnected graphs are reduced to a dense connected component; a
cut vertex partitions both vertices and edges into two proper induced pieces; vertices
of degree at most two are deleted; and the exceptional induced `K₂,₃` deletes four
degree-three vertices and exactly eight edges.
-/

namespace Erdos916

open SimpleGraph

universe u

/-- The only structural input needed by the density induction. -/
def VertexTwoConnectedReductionPrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
      4 ≤ Fintype.card W →
      H.Connected →
      (∀ c : W, (H.induce (fun w : W => w ≠ c)).Connected) →
      (∀ w : W, 3 ≤ H.degree w) →
      HasWheelWitness H ∨ Nonempty (K23Reduction H)

/-- A vertex of degree at least three whose entire neighbourhood lies in `S` proves
that the induced graph on `S` has at least four vertices. -/
theorem four_le_card_induce_of_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S)
    (hclosed : G.neighborSet v ⊆ (S : Set V)) (hdeg : 3 ≤ G.degree v) :
    4 ≤ S.card := by
  classical
  have hnsub : G.neighborFinset v ⊆ S := by
    intro w hw
    apply hclosed
    simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hw
  have hins : insert v (G.neighborFinset v) ⊆ S := by
    simpa only [Finset.insert_subset_iff] using ⟨hv, hnsub⟩
  have hlt := Finset.card_le_card hins
  rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
    G.card_neighborFinset_eq_degree] at hlt
  omega

/-- The full density theorem follows from the two-connected structural alternative. -/
theorem dense_hasWheel_of_vertexTwoConnectedReduction
    (hcore : VertexTwoConnectedReductionPrinciple.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    HasWheelWitness G := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn4 : n = 4
      · have htop : G = ⊤ :=
          eq_top_of_card_four_of_dense G (by omega) (by simpa [hn] using hdense)
        have hle : (⊤ : SimpleGraph V) ≤ G := by rw [htop]
        exact HasWheelWitness.mono hle
          (hasWheelWitness_top (by simpa [hn] using hcard))
      · have hn5 : 5 ≤ n := by omega
        by_cases hmin : ∀ v : V, 3 ≤ G.degree v
        · letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
          by_cases hconn : G.Connected
          · by_cases hcut : ∃ c : V, IsCutVertex G c
            · obtain ⟨c, hc⟩ := hcut
              let U : Type u := {w : V // w ≠ c}
              letI : Nonempty U := by
                obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
                by_cases hac : a ≠ c
                · exact ⟨⟨a, hac⟩⟩
                · exact ⟨⟨b, fun hbc => hab ((not_ne_iff.mp hac).trans hbc.symm)⟩⟩
              let K : (deleteVertex G c).ConnectedComponent :=
                (deleteVertex G c).connectedComponentMk (Classical.choice (inferInstance : Nonempty U))
              obtain ⟨hpieceProper, hremProper, hdensePiece | hdenseRem⟩ :=
                CutDensity.cut_dense_piece (G := G) hconn hc K hdense
              · let S : Finset V := CutDensity.piece G c K
                let T : Type u := {x : V // x ∈ (S : Set V)}
                have hcardT : Fintype.card T = S.card := by simp [T]
                have hlt : Fintype.card T < n := by
                  rw [← hn]
                  rw [hcardT]
                  exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hpieceProper)
                obtain ⟨v, hvside⟩ := ComponentEndBlock.side_nonempty (G := G) c K
                have hvS : v ∈ S := by
                  exact (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hvside)
                have hclosed : G.neighborSet v ⊆ (S : Set V) := by
                  intro w hvw
                  have hw := ComponentEndBlock.neighborSet_subset_verts (G := G) K hvside hvw
                  simpa [S, CutDensity.coe_piece] using hw
                have hcardS : 4 ≤ S.card :=
                  four_le_card_induce_of_degree_three G S v hvS hclosed (hmin v)
                have hcardT4 : 4 ≤ Fintype.card T := by omega
                have hdenseT :
                    2 * Fintype.card T ≤ (G.induce (S : Set V)).edgeFinset.card + 2 := by
                  rw [hcardT]
                  have hpieceCard : Fintype.card (CutDensity.piece G c K) =
                      (CutDensity.piece G c K).card := Fintype.card_coe _
                  rw [hpieceCard] at hdensePiece
                  simpa only [S] using hdensePiece
                have hWS : HasWheelWitness (G.induce (S : Set V)) :=
                  ih _ hlt (G.induce (S : Set V)) hcardT4 hdenseT rfl
                have hWS' : HasWheelWitness
                    (G.induce (CutDensity.piece G c K : Set V)) := by
                  apply (HasWheelWitness.decidableRel_iff _ _ _).mp
                  simpa only [S] using hWS
                exact HasWheelWitness.mapEmbedding
                  (SimpleGraph.Embedding.induce (CutDensity.piece G c K : Set V)) hWS'
              · let S : Finset V := CutDensity.remainder G c K
                let T : Type u := {x : V // x ∈ (S : Set V)}
                have hcardT : Fintype.card T = S.card := by simp [T]
                have hlt : Fintype.card T < n := by
                  rw [← hn]
                  rw [hcardT]
                  exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hremProper)
                have hex : ∃ v : V, v ∉ CutDensity.piece G c K := by
                  by_contra h
                  push Not at h
                  exact hpieceProper (Finset.eq_univ_of_forall h)
                obtain ⟨v, hvpiece⟩ := hex
                have hvside : v ∉ ComponentEndBlock.side c K := by
                  intro hv
                  exact hvpiece ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hv))
                have hvS : v ∈ S := by
                  simpa [S, CutDensity.mem_remainder_iff] using hvside
                have hclosed : G.neighborSet v ⊆ (S : Set V) := by
                  intro w hvw
                  have hwside : w ∉ ComponentEndBlock.side c K := by
                    intro hw
                    have hvverts :=
                      ComponentEndBlock.neighborSet_subset_verts (G := G) K hw hvw.symm
                    rw [ComponentEndBlock.verts] at hvverts
                    rcases hvverts with hvc | hv
                    · exact hvpiece ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inl hvc))
                    · exact hvside hv
                  simpa [S, CutDensity.mem_remainder_iff] using hwside
                have hcardS : 4 ≤ S.card :=
                  four_le_card_induce_of_degree_three G S v hvS hclosed (hmin v)
                have hcardT4 : 4 ≤ Fintype.card T := by omega
                have hdenseT :
                    2 * Fintype.card T ≤ (G.induce (S : Set V)).edgeFinset.card + 2 := by
                  rw [hcardT]
                  have hremCard : Fintype.card (CutDensity.remainder G c K) =
                      (CutDensity.remainder G c K).card := Fintype.card_coe _
                  rw [hremCard] at hdenseRem
                  simpa only [S] using hdenseRem
                have hWS : HasWheelWitness (G.induce (S : Set V)) :=
                  ih _ hlt (G.induce (S : Set V)) hcardT4 hdenseT rfl
                have hWS' : HasWheelWitness
                    (G.induce (CutDensity.remainder G c K : Set V)) := by
                  apply (HasWheelWitness.decidableRel_iff _ _ _).mp
                  simpa only [S] using hWS
                exact HasWheelWitness.mapEmbedding
                  (SimpleGraph.Embedding.induce (CutDensity.remainder G c K : Set V)) hWS'
            · have hdel : ∀ c : V,
                  (G.induce (fun w : V => w ≠ c)).Connected := by
                intro c
                have hncut : ¬IsCutVertex G c := (not_exists.mp hcut) c
                have hpre : (deleteVertex G c).Preconnected := not_not.mp hncut
                letI : Nonempty {w : V // w ≠ c} := by
                  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
                  by_cases hac : a ≠ c
                  · exact ⟨⟨a, hac⟩⟩
                  · exact ⟨⟨b, fun hbc => hab ((not_ne_iff.mp hac).trans hbc.symm)⟩⟩
                change (deleteVertex G c).Connected
                exact SimpleGraph.Connected.mk hpre
              rcases @hcore V _ _ G _ (by simpa [hn] using hcard) hconn hdel hmin with hW | hR
              · exact hW
              · obtain ⟨R⟩ := hR
                have hn6 : 6 ≤ n := by rw [← hn]; exact R.six_le_card
                by_cases hn8 : 8 ≤ n
                · let W : Type u := {v : V // v ∉ R.deletedFour}
                  letI : Fintype R.remaining.edgeSet := R.remaining.fintypeEdgeSet
                  have hWcard : Fintype.card W = n - 4 := by
                    simpa [W, hn] using R.card_remaining_vertices
                  have hWcard4 : 4 ≤ Fintype.card W := by omega
                  have hWlt : Fintype.card W < n := by omega
                  have hWedges : R.remaining.edgeFinset.card + 8 = G.edgeFinset.card := by
                    change R.remaining.edgeSet.toFinset.card + 8 = G.edgeSet.toFinset.card
                    rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
                    exact R.ncard_remaining_add_eight
                  have hWdense :
                      2 * Fintype.card W ≤ R.remaining.edgeFinset.card + 2 := by omega
                  have hWH : HasWheelWitness R.remaining :=
                    ih _ hWlt R.remaining hWcard4 hWdense rfl
                  exact R.wheel_of_remaining hWH
                · have hn67 : n = 6 ∨ n = 7 := by omega
                  rcases hn67 with hn6eq | hn7eq
                  · have hedge := R.edge_card_le_nine_of_card_eq_six (hn.trans hn6eq)
                    omega
                  · have hedge := R.edge_card_le_eleven_of_card_eq_seven (hn.trans hn7eq)
                    omega
          · have hnpre : ¬G.Preconnected := by
              intro hp
              exact hconn (SimpleGraph.Connected.mk hp)
            obtain ⟨C, hCdense⟩ := exists_dense_connectedComponent G inferInstance hdense
            letI : Fintype C := Fintype.ofFinite C
            letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
            have hClt : Fintype.card C < n := by
              rw [← hn]
              exact connectedComponent_card_lt_of_not_preconnected G hnpre C
            obtain ⟨u, hu⟩ := C.nonempty_supp
            let uC : C := ⟨u, hu⟩
            have hdegC : 3 ≤ C.toSimpleGraph.degree uC := by
              rw [degree_connectedComponent G C uC]
              exact hmin u
            have hcardC : 4 ≤ Fintype.card C := by
              have hlt := C.toSimpleGraph.degree_lt_card_verts uC
              omega
            have hCW : HasWheelWitness C.toSimpleGraph :=
              ih _ hClt C.toSimpleGraph hcardC hCdense rfl
            let f : C.toSimpleGraph ↪g G :=
              { toFun := fun v => v.1
                inj' := Subtype.val_injective
                map_rel_iff' := Iff.rfl }
            exact HasWheelWitness.mapEmbedding f hCW
        · push Not at hmin
          obtain ⟨v, hv⟩ := hmin
          have hv2 : G.degree v ≤ 2 := by omega
          let W : Type u := {x : V // x ∈ ({v}ᶜ : Set V)}
          let H : SimpleGraph W := G.induce ({v}ᶜ : Set V)
          have hcardW : Fintype.card W = n - 1 := by
            dsimp [W]
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            rw [Fintype.card_subtype_compl]
            simp [hn]
          have hcardW4 : 4 ≤ Fintype.card W := by omega
          have hcardWlt : Fintype.card W < n := by omega
          have hedgeInd := G.card_edgeFinset_induce_compl_singleton v
          have hedgeDel := G.card_edgeFinset_deleteIncidenceSet v
          have hHedges : H.edgeFinset.card = G.edgeFinset.card - G.degree v :=
            hedgeInd.trans hedgeDel
          have hHdense : 2 * Fintype.card W ≤ H.edgeFinset.card + 2 := by omega
          have hHW : HasWheelWitness H :=
            ih _ hcardWlt H hcardW4 hHdense rfl
          exact HasWheelWitness.induce ({v}ᶜ : Set V) hHW

end Erdos916
