/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreAHT
import ErdosProblems.Erdos916.StructuralCore
import ErdosProblems.Erdos916.AHTConnectivity

/-!
# The low-connectivity step of the AHT false-twin theorem

This file proves the cut-vertex part of the induction behind
Aboulker--Havet--Trotignon's degree-three false-twin theorem.  It does not
assume the remaining two-connected theorem as a principle: starting with any
connected pointed graph of minimum degree three away from its distinguished
vertex, it either finds the desired false twins or produces a genuine
vertex-two-connected pointed obstruction.  The latter may live in a proper
component end piece.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace AHTSection7

/-- A degree-three false-twin pair avoiding one distinguished vertex. -/
def HasFalseTwinsAway
    (G : SimpleGraph V) [DecidableRel G.Adj] (x₀ : V) : Prop :=
  ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 ∧
    u ≠ x₀ ∧ v ≠ x₀

/-! ## Boundary avoidance for the two-pair output of AHT Section 6 -/

/-- Of two vertex-disjoint false-twin pairs, one avoids any one prescribed
vertex.  This is the direct three-connected terminal step in the pointed
induction. -/
theorem hasFalseTwinsAway_of_twoDisjointPairs
    (T : TwoDisjointFalseTwinPairs G) (x₀ : V) :
    HasFalseTwinsAway G x₀ := by
  by_cases hfirst : T.u ≠ x₀ ∧ T.v ≠ x₀
  · exact ⟨T.u, T.v, T.twins_uv, T.degree_u, hfirst⟩
  · have hxFirst : x₀ ∈ ({T.u, T.v} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hu : T.u = x₀
      · exact Or.inl hu.symm
      · exact Or.inr (not_ne_iff.mp (fun hv ↦ hfirst ⟨hu, hv⟩)).symm
    have hsecond : T.x ≠ x₀ ∧ T.y ≠ x₀ := by
      constructor
      · intro hx
        have hxSecond : x₀ ∈ ({T.x, T.y} : Finset V) := by simp [← hx]
        exact Finset.disjoint_left.mp T.disjoint hxFirst hxSecond
      · intro hy
        have hySecond : x₀ ∈ ({T.x, T.y} : Finset V) := by simp [← hy]
        exact Finset.disjoint_left.mp T.disjoint hxFirst hySecond
    exact ⟨T.x, T.y, T.twins_xy, T.degree_x, hsecond⟩

/-- Among the two parts of `K₃,₃`, some part contains two vertices avoiding
any two prescribed vertices. -/
private theorem exists_samePart_pair_avoiding
    (a b : Fin 3 ⊕ Fin 3) :
    (∃ i j : Fin 3, i ≠ j ∧
      (Sum.inl i : Fin 3 ⊕ Fin 3) ≠ a ∧ Sum.inl i ≠ b ∧
      Sum.inl j ≠ a ∧ Sum.inl j ≠ b) ∨
    (∃ i j : Fin 3, i ≠ j ∧
      (Sum.inr i : Fin 3 ⊕ Fin 3) ≠ a ∧ Sum.inr i ≠ b ∧
      Sum.inr j ≠ a ∧ Sum.inr j ≠ b) := by
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;> decide

/-- The elementary `K₃,₃` resolution of the crossing-boundary case.  In a
graph isomorphic to `K₃,₃`, after excluding two attachment vertices there
remain two degree-three false twins in one bipartition class. -/
theorem exists_falseTwins_avoiding_two_of_k33_iso
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : completeBipartiteGraph (Fin 3) (Fin 3) ≃g H)
    (a b : W) :
    ∃ p q : W, AreFalseTwins H p q ∧ H.degree p = 3 ∧
      p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b := by
  classical
  let za : Fin 3 ⊕ Fin 3 := e.symm a
  let zb : Fin 3 ⊕ Fin 3 := e.symm b
  have avoid_image {z : Fin 3 ⊕ Fin 3} (hza : z ≠ za) (hzb : z ≠ zb) :
      e z ≠ a ∧ e z ≠ b := by
    constructor
    · intro h
      apply hza
      simpa [za] using congrArg e.symm h
    · intro h
      apply hzb
      simpa [zb] using congrArg e.symm h
  have twins_left {i j : Fin 3} (hij : i ≠ j) :
      AreFalseTwins H (e (.inl i)) (e (.inl j)) := by
    refine ⟨e.injective.ne (by simpa using hij), ?_⟩
    rw [← e.image_neighborSet, ← e.image_neighborSet]
    congr 1
  have twins_right {i j : Fin 3} (hij : i ≠ j) :
      AreFalseTwins H (e (.inr i)) (e (.inr j)) := by
    refine ⟨e.injective.ne (by simpa using hij), ?_⟩
    rw [← e.image_neighborSet, ← e.image_neighborSet]
    congr 1
  have degree_image_left (i : Fin 3) : H.degree (e (.inl i)) = 3 := by
    rw [e.degree_eq]
    rw [← (completeBipartiteGraph (Fin 3) (Fin 3)).card_neighborSet_eq_degree]
    let f : (completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet (.inl i) ≃
        Fin 3 :=
      { toFun := fun
          | ⟨.inl k, hk⟩ => False.elim (by simpa using hk)
          | ⟨.inr k, _⟩ => k
        invFun := fun k ↦ ⟨.inr k, by simp⟩
        left_inv := by
          rintro ⟨k | k, hk⟩
          · simp at hk
          · rfl
        right_inv := by intro k; rfl }
    rw [Fintype.card_congr f]
    simp
  have degree_image_right (i : Fin 3) : H.degree (e (.inr i)) = 3 := by
    rw [e.degree_eq]
    rw [← (completeBipartiteGraph (Fin 3) (Fin 3)).card_neighborSet_eq_degree]
    let f : (completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet (.inr i) ≃
        Fin 3 :=
      { toFun := fun
          | ⟨.inl k, _⟩ => k
          | ⟨.inr k, hk⟩ => False.elim (by simpa using hk)
        invFun := fun k ↦ ⟨.inl k, by simp⟩
        left_inv := by
          rintro ⟨k | k, hk⟩
          · rfl
          · simp at hk
        right_inv := by intro k; rfl }
    rw [Fintype.card_congr f]
    simp
  rcases exists_samePart_pair_avoiding za zb with hleft | hright
  · obtain ⟨i, j, hij, hia, hib, hja, hjb⟩ := hleft
    obtain ⟨hipa, hipb⟩ := avoid_image hia hib
    obtain ⟨hjpa, hjpb⟩ := avoid_image hja hjb
    exact ⟨e (.inl i), e (.inl j), twins_left hij,
      degree_image_left i, hipa, hipb, hjpa, hjpb⟩
  · obtain ⟨i, j, hij, hia, hib, hja, hjb⟩ := hright
    obtain ⟨hipa, hipb⟩ := avoid_image hia hib
    obtain ⟨hjpa, hjpb⟩ := avoid_image hja hjb
    exact ⟨e (.inr i), e (.inr j), twins_right hij,
      degree_image_right i, hipa, hipb, hjpa, hjpb⟩

namespace EndPieceLift

variable {c x₀ : V} (K : (deleteVertex G c).ConnectedComponent)

private theorem mem_side_of_mem_verts_ne_cut {v : V}
    (hv : v ∈ ComponentEndBlock.verts c K) (hvc : v ≠ c) :
    v ∈ ComponentEndBlock.side c K := by
  simpa [ComponentEndBlock.verts, hvc] using hv

/-- False twins on the component side of an induced end piece lift to the
ambient graph. -/
theorem falseTwins_lift
    {u v : {w : V // w ∈ ComponentEndBlock.verts c K}}
    (hu : u.1 ∈ ComponentEndBlock.side c K)
    (hv : v.1 ∈ ComponentEndBlock.side c K)
    (htwin : AreFalseTwins
      (G.induce (ComponentEndBlock.verts c K)) u v) :
    AreFalseTwins G u.1 v.1 := by
  refine ⟨fun huv ↦ htwin.1 (Subtype.ext huv), ?_⟩
  ext w
  constructor
  · intro huw
    have hw : w ∈ ComponentEndBlock.verts c K :=
      ComponentEndBlock.neighborSet_subset_verts (G := G) K hu huw
    have hi : (G.induce (ComponentEndBlock.verts c K)).Adj u ⟨w, hw⟩ := huw
    exact (htwin.adj_iff ⟨w, hw⟩).mp hi
  · intro hvw
    have hw : w ∈ ComponentEndBlock.verts c K :=
      ComponentEndBlock.neighborSet_subset_verts (G := G) K hv hvw
    have hi : (G.induce (ComponentEndBlock.verts c K)).Adj v ⟨w, hw⟩ := hvw
    exact (htwin.adj_iff ⟨w, hw⟩).mpr hi

/-- A false-twin pair avoiding the cut vertex lifts from a component end
piece and avoids the original exceptional vertex. -/
theorem falseTwinsAway_lift
    (hsideAvoid : x₀ = c ∨ x₀ ∉ ComponentEndBlock.side c K)
    (hpair : HasFalseTwinsAway
      (G.induce (ComponentEndBlock.verts c K))
        ⟨c, by simp [ComponentEndBlock.verts]⟩) :
    HasFalseTwinsAway G x₀ := by
  obtain ⟨u, v, htwin, hdegu, huc, hvc⟩ := hpair
  have hune : u.1 ≠ c := by
    intro h
    exact huc (Subtype.ext h)
  have hvne : v.1 ≠ c := by
    intro h
    exact hvc (Subtype.ext h)
  have huside : u.1 ∈ ComponentEndBlock.side c K :=
    mem_side_of_mem_verts_ne_cut K u.2 hune
  have hvside : v.1 ∈ ComponentEndBlock.side c K :=
    mem_side_of_mem_verts_ne_cut K v.2 hvne
  have hdegu' : G.degree u.1 = 3 := by
    rw [← ComponentEndBlock.degree_induce_verts (G := G) K huside]
    exact hdegu
  have huAvoid : u.1 ≠ x₀ := by
    rcases hsideAvoid with rfl | hx
    · exact hune
    · intro h
      exact hx (h ▸ huside)
  have hvAvoid : v.1 ≠ x₀ := by
    rcases hsideAvoid with rfl | hx
    · exact hvne
    · intro h
      exact hx (h ▸ hvside)
  exact ⟨u.1, v.1, falseTwins_lift K huside hvside htwin,
    hdegu', huAvoid, hvAvoid⟩

end EndPieceLift

namespace ComponentLift

/-- False twins in a connected component lift to the ambient graph. -/
theorem falseTwins_lift (C : G.ConnectedComponent) {u v : C}
    (htwin : AreFalseTwins C.toSimpleGraph u v) :
    AreFalseTwins G u.1 v.1 := by
  refine ⟨fun huv ↦ htwin.1 (Subtype.ext huv), ?_⟩
  ext w
  constructor
  · intro huw
    have hwC : w ∈ C.supp := C.mem_supp_of_adj_mem_supp u.2 huw
    have hi : C.toSimpleGraph.Adj u ⟨w, hwC⟩ := huw
    exact (htwin.adj_iff ⟨w, hwC⟩).mp hi
  · intro hvw
    have hwC : w ∈ C.supp := C.mem_supp_of_adj_mem_supp v.2 hvw
    have hi : C.toSimpleGraph.Adj v ⟨w, hwC⟩ := hvw
    exact (htwin.adj_iff ⟨w, hwC⟩).mpr hi

end ComponentLift

/-! ## Minimal pointed counterexamples have no cut vertex -/

/-- The induction hypothesis associated with a vertex-minimal pointed
counterexample.  This is deliberately a hypothesis about *strictly smaller
graphs*, rather than an assumed structural principle. -/
def SmallerPointedInstancesHaveFalseTwins
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (x₀ : W),
      Fintype.card W < Fintype.card V →
      2 ≤ Fintype.card W →
      H.Connected →
      MinDegreeThreeExcept H x₀ →
      ¬HasWheelWitness H →
      HasFalseTwinsAway H x₀

/-- A vertex-minimal connected, wheel-free pointed counterexample to the AHT
false-twin conclusion is vertex-two-connected.  This is the complete
cut-vertex step of the AHT induction: a cut vertex supplies a proper component
end piece, all non-cut vertices retain their degrees and neighbourhoods, and a
false-twin pair in the smaller piece lifts to the original graph. -/
theorem vertexTwoConnected_of_minimal_pointed_counterexample
    (x₀ : V) (hcard : 2 ≤ Fintype.card V)
    (hconn : G.Connected) (hdeg : MinDegreeThreeExcept G x₀)
    (hnoWheel : ¬HasWheelWitness G)
    (hnoTwins : ¬HasFalseTwinsAway G x₀)
    (hminimal : SmallerPointedInstancesHaveFalseTwins G) :
    G.Connected ∧
      ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected := by
  classical
  have hncut : ∀ c : V, ¬IsCutVertex G c := by
    intro c hc
    obtain ⟨K, havoidSide, hproper, hpieceConn, -⟩ :=
      ComponentEndBlock.endblock_reduction_N1 hconn c x₀ hc
    let S : Set V := ComponentEndBlock.verts c K
    let J : SimpleGraph S := G.induce S
    let c' : S := ⟨c, by simp [S, ComponentEndBlock.verts]⟩
    have hcardJ : 2 ≤ Fintype.card S := by
      obtain ⟨v, hv⟩ := ComponentEndBlock.side_nonempty (G := G) c K
      have hvc : v ≠ c := by
        intro hvc
        subst v
        exact ComponentEndBlock.cut_not_mem_side (G := G) c K hv
      have hne : (⟨v, by simp [S, ComponentEndBlock.verts, hv]⟩ : S) ≠ c' := by
        intro heq
        exact hvc (congrArg Subtype.val heq)
      rw [show (2 : ℕ) = 1 + 1 by omega]
      exact Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩
    have hcard_lt : Fintype.card S < Fintype.card V :=
      ComponentEndBlock.card_verts_lt (G := G) K hproper
    have hdegJ : MinDegreeThreeExcept J c' := by
      intro v hvcut
      have hvne : v.1 ≠ c := by
        intro heq
        apply hvcut
        apply Subtype.ext
        exact heq
      have hvside : v.1 ∈ ComponentEndBlock.side c K := by
        have hvverts : v.1 ∈ ComponentEndBlock.verts c K := by
          simpa [S] using v.2
        simpa [ComponentEndBlock.verts, hvne] using hvverts
      have hvx₀ : v.1 ≠ x₀ := by
        rcases havoidSide with rfl | hx₀side
        · exact hvne
        · intro hvx
          exact hx₀side (hvx ▸ hvside)
      rw [show J.degree v = G.degree v.1 by
        simpa [J, S] using
          ComponentEndBlock.degree_induce_verts (G := G) K hvside]
      exact hdeg v.1 hvx₀
    have hpair : HasFalseTwinsAway J c' :=
      hminimal S J c' hcard_lt hcardJ
        (by simpa [J, S] using hpieceConn) hdegJ
        (by
          intro hW
          exact hnoWheel (HasWheelWitness.induce S hW))
    exact hnoTwins
      (EndPieceLift.falseTwinsAway_lift K havoidSide hpair)
  refine ⟨hconn, ?_⟩
  intro c
  have hnonempty : Nonempty {w : V // w ≠ c} := by
    obtain ⟨a, b, hab⟩ :=
      Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
    by_cases hac : a ≠ c
    · exact ⟨⟨a, hac⟩⟩
    · have hbc : b ≠ c := by
        intro hbc
        apply hab
        exact (not_ne_iff.mp hac).trans hbc.symm
      exact ⟨⟨b, hbc⟩⟩
  change (deleteVertex G c).Connected
  let : Nonempty {w : V // w ≠ c} := hnonempty
  exact SimpleGraph.Connected.mk (not_not.mp (hncut c))

/-! ## An unconditional obstruction reduction -/

/-- The exact pointed counterexamples occurring in the cut-vertex induction.
The distinguished vertex is allowed to have small degree; the desired
degree-three false twins must avoid it. -/
def IsPointedFalseTwinCounterexample
    (G : SimpleGraph V) [DecidableRel G.Adj] (x₀ : V) : Prop :=
  2 ≤ Fintype.card V ∧
    G.Connected ∧
    MinDegreeThreeExcept G x₀ ∧
    ¬HasWheelWitness G ∧
    ¬HasFalseTwinsAway G x₀

/-- If a pointed wheel-free counterexample exists, then one exists which is
vertex-two-connected.  This theorem discharges the entire cut-vertex part of
AHT Section 7 without taking any false-twin principle as an argument.

The explicit `Fintype`, equality, and adjacency-decision data in the
conclusion merely package a possibly smaller vertex type in the same
universe. -/
theorem exists_vertexTwoConnected_pointed_counterexample
    (x₀ : V) (hbad : IsPointedFalseTwinCounterexample G x₀) :
    ∃ (W : Type u) (fW : Fintype W) (deqW : DecidableEq W)
      (H : SimpleGraph W) (dAdj : DecidableRel H.Adj) (y₀ : W),
      @IsPointedFalseTwinCounterexample W fW deqW H dAdj y₀ ∧
        (H.Connected ∧
          ∀ c : W, (H.induce (fun w : W ↦ w ≠ c)).Connected) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ (W : Type u) (fW : Fintype W) (deqW : DecidableEq W)
      (H : SimpleGraph W) (dAdj : DecidableRel H.Adj) (y₀ : W),
      @Fintype.card W fW = n ∧
        @IsPointedFalseTwinCounterexample W fW deqW H dAdj y₀
  have hP : ∃ n, P n := by
    refine ⟨Fintype.card V, V, inferInstance, inferInstance, G,
      inferInstance, x₀, rfl, hbad⟩
  let n : ℕ := Nat.find hP
  obtain ⟨W, fW, deqW, H, dAdj, y₀, hcardW, hbadW⟩ :=
    Nat.find_spec hP
  let : Fintype W := fW
  let : DecidableEq W := deqW
  let : DecidableRel H.Adj := dAdj
  have hsmall : SmallerPointedInstancesHaveFalseTwins H := by
    intro Z instF instDE K instAdj z₀ hlt hcardZ hconnZ hdegZ hnoWheelZ
    by_contra hnoTwinsZ
    have hPZ : P (Fintype.card Z) := by
      refine ⟨Z, instF, instDE, K, instAdj, z₀, rfl, ?_⟩
      exact ⟨hcardZ, hconnZ, hdegZ, hnoWheelZ, hnoTwinsZ⟩
    have hltN : Fintype.card Z < n := by
      simpa [n, hcardW] using hlt
    exact (Nat.find_min hP hltN) hPZ
  have hbadW' := hbadW
  obtain ⟨hcard2, hconn, hdeg, hnoWheel, hnoTwins⟩ := hbadW'
  have htwo := vertexTwoConnected_of_minimal_pointed_counterexample
    y₀ hcard2 hconn hdeg hnoWheel hnoTwins hsmall
  exact ⟨W, fW, deqW, H, dAdj, y₀, hbadW, htwo⟩

/-- Direct low-connectivity alternative.  Every connected wheel-free pointed
instance with minimum degree three away from its distinguished vertex either
already contains the required false twins, or has a (possibly smaller)
vertex-two-connected pointed counterexample. -/
theorem falseTwins_or_vertexTwoConnected_pointed_counterexample
    (x₀ : V) (hcard : 2 ≤ Fintype.card V)
    (hconn : G.Connected) (hdeg : MinDegreeThreeExcept G x₀)
    (hnoWheel : ¬HasWheelWitness G) :
    HasFalseTwinsAway G x₀ ∨
      ∃ (W : Type u) (fW : Fintype W) (deqW : DecidableEq W)
        (H : SimpleGraph W) (dAdj : DecidableRel H.Adj) (y₀ : W),
        @IsPointedFalseTwinCounterexample W fW deqW H dAdj y₀ ∧
          (H.Connected ∧
            ∀ c : W, (H.induce (fun w : W ↦ w ≠ c)).Connected) := by
  by_cases htwins : HasFalseTwinsAway G x₀
  · exact Or.inl htwins
  · exact Or.inr <| exists_vertexTwoConnected_pointed_counterexample x₀
      ⟨hcard, hconn, hdeg, hnoWheel, htwins⟩

/-! ## Component reduction for the ordinary AHT statement -/

/-- The complete component-and-cut-vertex reduction for the ordinary AHT
false-twin theorem.  A nonempty wheel-free graph of minimum degree three
either has degree-three false twins, or there is a vertex-two-connected
pointed counterexample in the same universe.  Consequently the only
remaining source theorem is the genuinely two-connected pointed case. -/
theorem falseTwins_or_vertexTwoConnected_counterexample
    [Nonempty V] (hdeg : ∀ w : V, 3 ≤ G.degree w)
    (hnoWheel : ¬HasWheelWitness G) :
    (∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3) ∨
      ∃ (W : Type u) (fW : Fintype W) (deqW : DecidableEq W)
        (H : SimpleGraph W) (dAdj : DecidableRel H.Adj) (y₀ : W),
        @IsPointedFalseTwinCounterexample W fW deqW H dAdj y₀ ∧
          (H.Connected ∧
            ∀ c : W, (H.induce (fun w : W ↦ w ≠ c)).Connected) := by
  classical
  let C : G.ConnectedComponent :=
    G.connectedComponentMk (Classical.choice inferInstance)
  let : Fintype C := Fintype.ofFinite C
  let : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨x, hx⟩ := C.nonempty_supp
  let x₀ : C := ⟨x, hx⟩
  have hcardC : 2 ≤ Fintype.card C := by
    have hthree : 3 ≤ C.toSimpleGraph.degree x₀ := by
      rw [Erdos916.ConnectedComponent.degree_toSimpleGraph C x₀]
      exact hdeg x
    have hlt := C.toSimpleGraph.degree_lt_card_verts x₀
    omega
  have hdegC : MinDegreeThreeExcept C.toSimpleGraph x₀ := by
    intro v _
    rw [Erdos916.ConnectedComponent.degree_toSimpleGraph C v]
    exact hdeg v.1
  have hnoWheelC : ¬HasWheelWitness C.toSimpleGraph := by
    intro hW
    let e : C.toSimpleGraph ↪g G :=
      { toFun := fun v ↦ v.1
        inj' := Subtype.val_injective
        map_rel_iff' := by intro _ _; rfl }
    exact hnoWheel (HasWheelWitness.mapEmbedding e hW)
  rcases falseTwins_or_vertexTwoConnected_pointed_counterexample
      x₀ hcardC C.connected_toSimpleGraph hdegC hnoWheelC with hpair | hobs
  · obtain ⟨u, v, htwin, hdegu, -, -⟩ := hpair
    refine Or.inl ⟨u.1, v.1,
      ComponentLift.falseTwins_lift C htwin, ?_⟩
    rw [← Erdos916.ConnectedComponent.degree_toSimpleGraph C u]
    exact hdegu
  · exact Or.inr hobs

end AHTSection7

end Erdos916
