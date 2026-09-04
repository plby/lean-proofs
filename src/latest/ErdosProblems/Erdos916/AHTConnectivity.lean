/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreAHT
import ErdosProblems.Erdos916.StructuralCore

/-!
# Connectivity reductions for the AHT false-twin theorem

This file isolates the part of Aboulker--Havet--Trotignon's proof which does
not use the three-connected theorem.  The useful induction statement is
pointed: one vertex is allowed to have small degree, and the false-twin pair
must avoid that vertex.  At a cut vertex we pass to a component end piece and
use its cut vertex as the new exceptional vertex.  All vertices in the
resulting pair lie on the component side, so both their degrees and their open
neighbourhoods are unchanged when the pair is lifted.

The remaining two-separation step is deliberately represented by the exact
vertex-two-connected interface below.  It is stronger than an unpointed
statement and is the interface supplied by the AHT end/torso argument.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A degree-three false-twin pair, with neither member equal to a specified
exceptional vertex. -/
def HasDegreeThreeFalseTwinsAway
    (G : SimpleGraph V) [DecidableRel G.Adj] (x₀ : V) : Prop :=
  ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 ∧
    u ≠ x₀ ∧ v ≠ x₀

/-- The exact pointed, vertex-two-connected interface needed by the
cut-vertex induction. -/
def VertexTwoConnectedFalseTwinPrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (x₀ : W),
      2 ≤ Fintype.card W →
      (H.Connected ∧
        ∀ c : W, (H.induce (fun w : W ↦ w ≠ c)).Connected) →
      MinDegreeThreeExcept H x₀ →
      ¬HasWheelWitness H →
      HasDegreeThreeFalseTwinsAway H x₀

/-! ## Exact signature of the AHT three-connected input -/

/-- The centre-specific form of the witness used to define "almost
wheel-free". -/
def HasWheelCenteredAt
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Prop :=
  ∃ a : V, ∃ p : G.Walk a a,
    p.IsCycle ∧ x ∉ p.support ∧
      3 ≤ (G.neighborFinset x ∩ p.support.toFinset).card

theorem hasWheelWitness_iff_exists_center :
    HasWheelWitness G ↔ ∃ x : V, HasWheelCenteredAt G x := by
  constructor
  · rintro ⟨a, p, x, hp, hx, hthree⟩
    exact ⟨x, a, p, hp, hx, hthree⟩
  · rintro ⟨x, a, p, hp, hx, hthree⟩
    exact ⟨a, p, x, hp, hx, hthree⟩

/-- Vertex-three-connectivity in the finite setting used here: the graph has
at least four vertices, is connected, and remains connected after deletion of
any two distinct vertices. -/
def VertexThreeConnected
    (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧ G.Connected ∧
    ∀ a b : V, a ≠ b →
      (G.induce (fun w : V ↦ w ≠ a ∧ w ≠ b)).Connected

/-- All wheel centres of `G` (if any) belong to the displayed two-set.  This
is the centre-containment part of the end-torso argument. -/
def AlmostWheelFreeAt
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : Prop :=
  ∀ x : V, x ≠ a → x ≠ b → ¬HasWheelCenteredAt G x

/-- AHT's source-exact definition of an almost wheel-free graph: there are no
wheel centres; or there is one, of degree three; or there are two, both of
degree three and adjacent. -/
def AlmostWheelFree
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ x : V, ¬HasWheelCenteredAt G x) ∨
  (∃ a : V, G.degree a = 3 ∧
    ∀ x : V, HasWheelCenteredAt G x → x = a) ∨
  (∃ a b : V, G.Adj a b ∧ G.degree a = 3 ∧ G.degree b = 3 ∧
    ∀ x : V, HasWheelCenteredAt G x → x = a ∨ x = b)

theorem almostWheelFree_of_noWheel (hnoWheel : ¬HasWheelWitness G) :
    AlmostWheelFree G := by
  left
  intro x hx
  exact hnoWheel (hasWheelWitness_iff_exists_center.mpr ⟨x, hx⟩)

/-- The endpoint form used after adding a virtual edge to a two-separation
torso. -/
theorem almostWheelFree_of_at_of_adj_of_degree_three
    {a b : V} (hcentres : AlmostWheelFreeAt G a b)
    (hab : G.Adj a b) (hdega : G.degree a = 3) (hdegb : G.degree b = 3) :
    AlmostWheelFree G := by
  right
  right
  exact ⟨a, b, hab, hdega, hdegb, fun x hx ↦ by
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr hxb
    exact False.elim (hcentres x hxa hxb hx)⟩

/-- The conclusion of AHT Theorem 6.6: two vertex-disjoint degree-three
false-twin pairs. -/
structure TwoDisjointFalseTwinPairs
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  v : V
  x : V
  y : V
  twins_uv : AreFalseTwins G u v
  twins_xy : AreFalseTwins G x y
  degree_u : G.degree u = 3
  degree_x : G.degree x = 3
  disjoint : Disjoint ({u, v} : Finset V) {x, y}

/-- The sole genuinely three-connected theorem used by AHT's connectivity
induction.  The two-pair conclusion is essential: an end torso has two
attachment vertices, so one whole pair avoids the attachment set. -/
def ThreeConnectedAlmostWheelFreeFalseTwinPrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
      VertexThreeConnected H → AlmostWheelFree H →
      Nonempty (TwoDisjointFalseTwinPairs H)

/-- The almost-wheel-free two-pair theorem contains the ordinary
three-connected wheel-free false-twin theorem as an immediate special case. -/
theorem threeConnected_falseTwins_of_almostWheelFreePrinciple
    (hcore : ThreeConnectedAlmostWheelFreeFalseTwinPrinciple.{u})
    (hthree : VertexThreeConnected G) (hnoWheel : ¬HasWheelWitness G) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  have halmost : AlmostWheelFree G := almostWheelFree_of_noWheel hnoWheel
  obtain ⟨T⟩ := hcore V G hthree halmost
  exact ⟨T.u, T.v, T.twins_uv, T.degree_u⟩

/-! ## Virtual-edge torso bookkeeping -/

namespace AHTTorso

/-- The usual torso of an induced vertex set, with one (possibly already
present) edge added between its two attachment vertices. -/
def torsoOn (G : SimpleGraph V) (S : Set V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) : SimpleGraph S :=
  G.induce S ⊔ SimpleGraph.edge ⟨a, ha⟩ ⟨b, hb⟩

/-- The virtual attachment edge changes no adjacency incident with an
interior vertex. -/
theorem torsoOn_adj_iff_of_ne_boundary
    {S : Set V} {a b : V} {ha : a ∈ S} {hb : b ∈ S}
    {u w : S} (hua : u.1 ≠ a) (hub : u.1 ≠ b) :
    (torsoOn G S a b ha hb).Adj u w ↔ G.Adj u.1 w.1 := by
  simp only [torsoOn, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro (h | h)
    · exact h
    · rcases h.1 with ⟨hu, -⟩ | ⟨hu, -⟩
      · exact False.elim (hua (congrArg Subtype.val hu))
      · exact False.elim (hub (congrArg Subtype.val hu))
  · exact Or.inl

/-- A false-twin pair wholly in the interior of a torso lifts to the ambient
graph when the two vertices have no neighbours outside the torso set. -/
theorem falseTwins_lift
    {S : Set V} {a b : V} {ha : a ∈ S} {hb : b ∈ S}
    {u v : S}
    (hua : u.1 ≠ a) (hub : u.1 ≠ b)
    (hva : v.1 ≠ a) (hvb : v.1 ≠ b)
    (hNu : G.neighborSet u.1 ⊆ S)
    (hNv : G.neighborSet v.1 ⊆ S)
    (htwin : AreFalseTwins (torsoOn G S a b ha hb) u v) :
    AreFalseTwins G u.1 v.1 := by
  refine ⟨fun huv ↦ htwin.1 (Subtype.ext huv), ?_⟩
  ext w
  constructor
  · intro huw
    have hwS : w ∈ S := hNu huw
    have htorso : (torsoOn G S a b ha hb).Adj u ⟨w, hwS⟩ :=
      (torsoOn_adj_iff_of_ne_boundary hua hub).mpr huw
    have htorso' : (torsoOn G S a b ha hb).Adj v ⟨w, hwS⟩ :=
      (htwin.adj_iff ⟨w, hwS⟩).mp htorso
    exact (torsoOn_adj_iff_of_ne_boundary hva hvb).mp htorso'
  · intro hvw
    have hwS : w ∈ S := hNv hvw
    have htorso : (torsoOn G S a b ha hb).Adj v ⟨w, hwS⟩ :=
      (torsoOn_adj_iff_of_ne_boundary hva hvb).mpr hvw
    have htorso' : (torsoOn G S a b ha hb).Adj u ⟨w, hwS⟩ :=
      (htwin.adj_iff ⟨w, hwS⟩).mpr htorso
    exact (torsoOn_adj_iff_of_ne_boundary hua hub).mp htorso'

/-- An interior torso vertex has the same degree in the torso as in the
ambient graph whenever all its ambient neighbours lie in the torso set. -/
theorem degree_torsoOn_eq
    {S : Set V} {a b : V} {ha : a ∈ S} {hb : b ∈ S}
    {u : S} (hua : u.1 ≠ a) (hub : u.1 ≠ b)
    (hNu : G.neighborSet u.1 ⊆ S) :
    (torsoOn G S a b ha hb).degree u = G.degree u.1 := by
  classical
  rw [← (torsoOn G S a b ha hb).card_neighborFinset_eq_degree,
    ← G.card_neighborFinset_eq_degree]
  let e : (torsoOn G S a b ha hb).neighborFinset u →
      G.neighborFinset u.1 := fun w ↦
    ⟨w.1.1, by
      rw [SimpleGraph.mem_neighborFinset]
      have hwAdj := w.2
      rw [SimpleGraph.mem_neighborFinset] at hwAdj
      exact (torsoOn_adj_iff_of_ne_boundary hua hub).mp
        hwAdj⟩
  have heinj : Function.Injective e := by
    intro x y hxy
    have hval : x.1.1 = y.1.1 :=
      congrArg (fun z : G.neighborFinset u.1 ↦ z.1) hxy
    exact Subtype.ext (Subtype.ext hval)
  have hesurj : Function.Surjective e := by
    rintro ⟨w, huw⟩
    have hwS : w ∈ S := hNu (by simpa using huw)
    let wS : S := ⟨w, hwS⟩
    have htorso : (torsoOn G S a b ha hb).Adj u wS :=
      (torsoOn_adj_iff_of_ne_boundary hua hub).mpr (by simpa using huw)
    refine ⟨⟨wS, by simpa using htorso⟩, ?_⟩
    rfl
  have hcard := Fintype.card_congr (Equiv.ofBijective e ⟨heinj, hesurj⟩)
  simpa only [Fintype.card_coe] using hcard

end AHTTorso

namespace ComponentEndBlock

variable {c x₀ : V} (K : (deleteVertex G c).ConnectedComponent)

private theorem mem_side_of_mem_verts_ne_cut {v : V}
    (hv : v ∈ verts c K) (hvc : v ≠ c) : v ∈ side c K := by
  simpa [verts, hvc] using hv

/-- False twins in an induced component end piece lift when both members lie
on the component side.  This records the neighbourhood part of the lift;
the degree equalities are added in `liftFalseTwinsAway`. -/
theorem falseTwins_induce_verts_lift
    {u v : {w : V // w ∈ verts c K}}
    (hu : u.1 ∈ side c K) (hv : v.1 ∈ side c K)
    (htwin : AreFalseTwins (G.induce (verts c K)) u v) :
    AreFalseTwins G u.1 v.1 := by
  refine ⟨fun huv ↦ htwin.1 (Subtype.ext huv), ?_⟩
  ext w
  constructor
  · intro huw
    have hw : w ∈ verts c K :=
      neighborSet_subset_verts (G := G) K hu huw
    have hi : (G.induce (verts c K)).Adj u ⟨w, hw⟩ := huw
    have hj : (G.induce (verts c K)).Adj v ⟨w, hw⟩ :=
      (htwin.adj_iff ⟨w, hw⟩).mp hi
    exact hj
  · intro hvw
    have hw : w ∈ verts c K :=
      neighborSet_subset_verts (G := G) K hv hvw
    have hi : (G.induce (verts c K)).Adj v ⟨w, hw⟩ := hvw
    have hj : (G.induce (verts c K)).Adj u ⟨w, hw⟩ :=
      (htwin.adj_iff ⟨w, hw⟩).mpr hi
    exact hj

/-- A pointed false-twin pair in a component end piece lifts to the ambient
graph and avoids the original exceptional vertex whenever the chosen side
does. -/
theorem liftFalseTwinsAway
    (hsideAvoid : x₀ = c ∨ x₀ ∉ side c K)
    (hpair : HasDegreeThreeFalseTwinsAway
      (G.induce (verts c K)) ⟨c, by simp [verts]⟩) :
    HasDegreeThreeFalseTwinsAway G x₀ := by
  obtain ⟨u, v, htwin, hdegu, huc, hvc⟩ := hpair
  have hune : u.1 ≠ c := by
    intro h
    exact huc (Subtype.ext h)
  have hvne : v.1 ≠ c := by
    intro h
    exact hvc (Subtype.ext h)
  have huside : u.1 ∈ side c K :=
    mem_side_of_mem_verts_ne_cut K u.2 hune
  have hvside : v.1 ∈ side c K :=
    mem_side_of_mem_verts_ne_cut K v.2 hvne
  have hdegu' : G.degree u.1 = 3 := by
    rw [← degree_induce_verts (G := G) K huside]
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
  exact ⟨u.1, v.1, falseTwins_induce_verts_lift K huside hvside htwin,
    hdegu', huAvoid, hvAvoid⟩

end ComponentEndBlock

/-! ## The cut-vertex induction -/

/-- Assuming only the pointed vertex-two-connected interface, every connected
graph with minimum degree three away from one vertex has a degree-three
false-twin pair avoiding that vertex. -/
theorem connected_falseTwins_of_vertexTwoConnected
    (hcore : VertexTwoConnectedFalseTwinPrinciple.{u})
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (x₀ : W) (hcard : 2 ≤ Fintype.card W)
    (hconn : H.Connected) (hdeg : MinDegreeThreeExcept H x₀)
    (hnoWheel : ¬HasWheelWitness H) :
    HasDegreeThreeFalseTwinsAway H x₀ := by
  classical
  induction hn : Fintype.card W using Nat.strong_induction_on generalizing W with
  | h n ih =>
      by_cases hcut : ∃ c : W, IsCutVertex H c
      · obtain ⟨c, hc⟩ := hcut
        obtain ⟨K, havoidSide, hproper, hpieceConn, -⟩ :=
          ComponentEndBlock.endblock_reduction_N1 hconn c x₀ hc
        let S : Set W := ComponentEndBlock.verts c K
        let J : SimpleGraph S := H.induce S
        let c' : S := ⟨c, by simp [S, ComponentEndBlock.verts]⟩
        have hcardJ : 2 ≤ Fintype.card S := by
          obtain ⟨v, hv⟩ := ComponentEndBlock.side_nonempty (G := H) c K
          have hvc : v ≠ c := by
            intro hvc
            subst v
            exact ComponentEndBlock.cut_not_mem_side (G := H) c K hv
          have hne : (⟨v, by simp [S, ComponentEndBlock.verts, hv]⟩ : S) ≠ c' := by
            intro heq
            exact hvc (congrArg Subtype.val heq)
          rw [show (2 : ℕ) = 1 + 1 by omega]
          exact Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩
        have hcard_lt : Fintype.card S < n := by
          rw [← hn]
          exact ComponentEndBlock.card_verts_lt (G := H) K hproper
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
          rw [show J.degree v = H.degree v.1 by
            simpa [J, S] using
              ComponentEndBlock.degree_induce_verts (G := H) K hvside]
          exact hdeg v.1 hvx₀
        have hrec : HasDegreeThreeFalseTwinsAway J c' :=
          ih (Fintype.card S) hcard_lt J c' hcardJ
            (by simpa [J, S] using hpieceConn) hdegJ
            (by
              intro hW
              exact hnoWheel (HasWheelWitness.induce S hW)) rfl
        exact ComponentEndBlock.liftFalseTwinsAway K havoidSide hrec
      · have hncut : ∀ c : W, ¬IsCutVertex H c := by
          simpa only [not_exists] using hcut
        have htwo : H.Connected ∧
            ∀ c : W, (H.induce (fun w : W ↦ w ≠ c)).Connected := by
          refine ⟨hconn, ?_⟩
          intro c
          have hnonempty : Nonempty {w : W // w ≠ c} := by
            obtain ⟨a, b, hab⟩ :=
              Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
            by_cases hac : a ≠ c
            · exact ⟨⟨a, hac⟩⟩
            · have hbc : b ≠ c := by
                intro hbc
                apply hab
                exact (not_ne_iff.mp hac).trans hbc.symm
              exact ⟨⟨b, hbc⟩⟩
          change (deleteVertex H c).Connected
          let : Nonempty {w : W // w ≠ c} := hnonempty
          exact SimpleGraph.Connected.mk (not_not.mp (hncut c))
        exact @hcore W _ _ H _ x₀ hcard htwo hdeg hnoWheel

/-! ## Passage from a component to the ambient graph -/

namespace ConnectedComponent

noncomputable local instance ahtComponentFintype
    (C : G.ConnectedComponent) : Fintype C := Fintype.ofFinite C

noncomputable local instance ahtComponentAdjDecidable
    (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj :=
  Classical.decRel _

/-- False twins in a connected component are false twins in the ambient
graph, because components contain every neighbour of each of their vertices. -/
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

end ConnectedComponent

/-- The full component/cut-vertex reduction.  Thus the only remaining
connectivity work is the pointed two-separation theorem represented by
`VertexTwoConnectedFalseTwinPrinciple`. -/
theorem falseTwins_of_vertexTwoConnected
    (hcore : VertexTwoConnectedFalseTwinPrinciple.{u})
    {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hdeg : ∀ w : W, 3 ≤ H.degree w)
    (hnoWheel : ¬HasWheelWitness H) :
    ∃ u v : W, AreFalseTwins H u v ∧ H.degree u = 3 := by
  classical
  let C : H.ConnectedComponent :=
    H.connectedComponentMk (Classical.choice inferInstance)
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
    let f : C.toSimpleGraph ↪g H :=
      { toFun := fun v ↦ v.1
        inj' := Subtype.val_injective
        map_rel_iff' := Iff.rfl }
    exact hnoWheel (HasWheelWitness.mapEmbedding f hW)
  obtain ⟨u, v, htwin, hdegu, -, -⟩ :=
    connected_falseTwins_of_vertexTwoConnected hcore C.toSimpleGraph x₀
      hcardC C.connected_toSimpleGraph hdegC hnoWheelC
  refine ⟨u.1, v.1, ConnectedComponent.falseTwins_lift C htwin, ?_⟩
  rw [← Erdos916.ConnectedComponent.degree_toSimpleGraph C u]
  exact hdegu

end Erdos916
