/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTPairBridge
import ErdosProblems.Erdos916.AHTMinimalThreeConnected
import ErdosProblems.Erdos916.AHTSourceTheorem66Case1
import ErdosProblems.Erdos916.AHTSourceTheorem66Case2
import ErdosProblems.Erdos916.AHTSourceTheorem66Case3CardDeleted
import ErdosProblems.Erdos916.AHTSourceTheorem66Case4
import ErdosProblems.Erdos916.AHTSourceTheorem66Case5Deleted
import ErdosProblems.Erdos916.AHTWatkinsMesnerSplitter
import ErdosProblems.Erdos916.AHTSourceTheorem66Adapters
import ErdosProblems.Erdos916.AHTSourceTheorem66ComponentAdapters
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

set_option relaxedAutoImplicit true

attribute [local instance] Classical.propDecidable

/-!
# Assembly of AHT Theorem 6.6

This module is the source-level assembly point for the theorem that every
finite three-connected almost-wheel-free graph contains two vertex-disjoint
pairs of degree-three false twins.  It imports only the corrected
centre-deleted versions of claims (3) and (5).  In particular, the
uninhabited ambient-splitter certificates from the earlier exploratory
modules are not part of this assembly API.

There is deliberately no theorem-principle parameter and no conditional
replacement for AHT Theorem 6.6 here.  The declarations below discharge the
first unconditional steps of the minimal-counterexample proof.  The exact
remaining constructive inputs are recorded at the end of the file so that
each can be proved as an ordinary theorem.
-/

namespace Erdos916

open _root_.SimpleGraph
open AHTClaim3CardinalityCertificateDeleted

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## The universe-polymorphic induction predicate -/

/-- The source theorem restricted to graphs with exactly `n` vertices.
The vertex type remains quantified in the current universe, so recursive
fragment replacements may change the type. -/
def AHTTheorem66AtCard (n : Nat) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W],
    ∀ (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = n → IsThreeConnected H → AlmostWheelFree H →
        Nonempty (TwoDisjointDegreeThreeFalseTwinPairs H)

/-- The strong-induction hypothesis below a strict vertex bound. -/
def AHTTheorem66Below (n : Nat) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W],
    ∀ (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W < n → IsThreeConnected H → AlmostWheelFree H →
        Nonempty (TwoDisjointDegreeThreeFalseTwinPairs H)

theorem ahtTheorem66Below_of_strongInduction
    {n : Nat} (ih : ∀ m < n, AHTTheorem66AtCard.{u} m) :
    AHTTheorem66Below.{u} n := by
  intro W _ _ H _ hcard hthree halmost
  exact ih (Fintype.card W) hcard W H rfl hthree halmost

/-! ## Choosing the source vertex -/

/-- In a counterexample to the two-pair conclusion, AHT Lemma 6.5 supplies
a degree-three vertex which is neither a wheel centre nor close to a source
twin pair.  This is the precise starting point of the minimal-counterexample
proof of AHT Theorem 6.6. -/
theorem exists_degreeThree_not_center_not_close_of_no_twoPairs
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G)) :
    ∃ center : V,
      G.degree center = 3 ∧
      ¬HasWheelCenteredAt G center ∧
      ¬IsCloseToAHTTwin G center := by
  by_cases hex : ∃ center : V,
      G.degree center = 3 ∧
      ¬HasWheelCenteredAt G center ∧
      ¬IsCloseToAHTTwin G center
  · exact hex
  · have hclose : ∀ center : V, G.degree center = 3 →
        ¬HasWheelCenteredAt G center → IsCloseToAHTTwin G center := by
      intro center hdeg hnotCenter
      by_contra hnotClose
      exact hex ⟨center, hdeg, hnotCenter, hnotClose⟩
    exact (hno (aht_lemma65 hthree halmost hclose)).elim

/-! ## Passing the cycle obstruction to the centre-deleted graph -/

/-- A common cycle through the three neighbours in `G - center` would map
to an ambient rim witnessing a wheel centred at `center`.  This is the
type-safe bridge from the source choice of `center` to the Watkins--Mesner
input on the deletion subtype. -/
theorem not_hasCycleThroughThree_deleteVertex_of_not_wheelCenter
    {center : V} {x y z : {w : V // w ≠ center}}
    (hxy : x.1 ≠ y.1) (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hnotCenter : ¬HasWheelCenteredAt G center) :
    ¬HasCycleThroughThree (deleteVertex G center) x y z := by
  rintro ⟨r, C, hC, hxC, hyC, hzC⟩
  apply hnotCenter
  let inc : deleteVertex G center →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := fun w : V ↦ w ≠ center)).toHom
  let rim : G.Walk r.1 r.1 := C.map inc
  have hinc : Function.Injective inc := by
    intro p q hpq
    exact Subtype.ext hpq
  have hrim : rim.IsCycle := hC.map hinc
  have hcenterNotRim : center ∉ rim.support := by
    intro hcenter
    change center ∈ (C.map inc).support at hcenter
    rw [Walk.support_map] at hcenter
    obtain ⟨q, -, hq⟩ := List.mem_map.mp hcenter
    exact q.2 hq
  have map_mem (q : {w : V // w ≠ center})
      (hq : q ∈ C.support) : q.1 ∈ rim.support := by
    change q.1 ∈ (C.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  exact AHTMinimalThreeConnected.hasWheelCenteredAt_of_cycle_three_neighbors
    rim hrim hcenterNotRim hcx hcy hcz
    (map_mem x hxC) (map_mem y hyC) (map_mem z hzC)
    hxy hxz hyz

/-! ## The source data at a minimal-counterexample vertex -/

/-- The completely concrete data obtained after choosing the degree-three
source vertex and enumerating its neighbourhood.  The terminal vertices
remain ambient here; the three subtype vertices used by Watkins--Mesner are
defined below. -/
structure AHTTheorem66SourceData
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  center : V
  x : V
  y : V
  z : V
  degree_center : G.degree center = 3
  xy : x ≠ y
  xz : x ≠ z
  yz : y ≠ z
  neighbor_eq : G.neighborFinset center = {x, y, z}
  not_center : ¬HasWheelCenteredAt G center
  not_close : ¬IsCloseToAHTTwin G center

/-- The source vertex theorem together with a normalized enumeration of its
three neighbours. -/
theorem exists_ahtTheorem66SourceData
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G)) :
    Nonempty (AHTTheorem66SourceData G) := by
  obtain ⟨center, hdegree, hnotCenter, hnotClose⟩ :=
    exists_degreeThree_not_center_not_close_of_no_twoPairs
      hthree halmost hno
  obtain ⟨x, y, z, hxy, hxz, hyz, hneighbors⟩ :=
    exists_three_neighbors_of_degree_eq_three hdegree
  exact ⟨{
    center := center
    x := x
    y := y
    z := z
    degree_center := hdegree
    xy := hxy
    xz := hxz
    yz := hyz
    neighbor_eq := hneighbors
    not_center := hnotCenter
    not_close := hnotClose }⟩

namespace AHTTheorem66SourceData

variable (D : AHTTheorem66SourceData G)

theorem center_adj_x : G.Adj D.center D.x := by
  rw [← SimpleGraph.mem_neighborFinset, D.neighbor_eq]
  simp

theorem center_adj_y : G.Adj D.center D.y := by
  rw [← SimpleGraph.mem_neighborFinset, D.neighbor_eq]
  simp

theorem center_adj_z : G.Adj D.center D.z := by
  rw [← SimpleGraph.mem_neighborFinset, D.neighbor_eq]
  simp

theorem center_ne_x : D.center ≠ D.x := D.center_adj_x.ne

theorem center_ne_y : D.center ≠ D.y := D.center_adj_y.ne

theorem center_ne_z : D.center ≠ D.z := D.center_adj_z.ne

/-- The three terminals as vertices of the centre-deleted graph. -/
def xDeleted : {w : V // w ≠ D.center} := ⟨D.x, D.center_ne_x.symm⟩

def yDeleted : {w : V // w ≠ D.center} := ⟨D.y, D.center_ne_y.symm⟩

def zDeleted : {w : V // w ≠ D.center} := ⟨D.z, D.center_ne_z.symm⟩

@[simp] theorem xDeleted_val : D.xDeleted.1 = D.x := rfl

@[simp] theorem yDeleted_val : D.yDeleted.1 = D.y := rfl

@[simp] theorem zDeleted_val : D.zDeleted.1 = D.z := rfl

theorem center_neighbor_location {q : V} (hq : G.Adj D.center q) :
    q = D.x ∨ q = D.y ∨ q = D.z := by
  have hmem : q ∈ G.neighborFinset D.center :=
    (G.mem_neighborFinset D.center q).mpr hq
  rw [D.neighbor_eq] at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

/-- Three-connectivity of the ambient graph gives exactly the connectivity
hypotheses used by the Watkins--Mesner theorem on `G - center`. -/
theorem deleted_vertexTwoConnected (hthree : IsThreeConnected G) :
    (deleteVertex G D.center).Connected ∧
      ∀ d : {w : V // w ≠ D.center},
        ((deleteVertex G D.center).induce
          fun w : {w : V // w ≠ D.center} ↦ w ≠ d).Connected := by
  exact vertexTwoConnected_delete_of_isThreeConnected hthree D.center

/-- The chosen source data supplies the complete common-cycle obstruction
for its three terminals in the centre-deleted graph. -/
theorem deleted_no_common_cycle :
    ¬HasCycleThroughThree (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted := by
  exact not_hasCycleThroughThree_deleteVertex_of_not_wheelCenter
    D.xy D.xz D.yz D.center_adj_x D.center_adj_y D.center_adj_z
      D.not_center

end AHTTheorem66SourceData

/-! ## The concrete `X` recursive call -/

namespace WatkinsMesnerSplitter

/-- Interchange the two splitter sides without changing any terminal part.
This is the source `A/B` symmetry used to orient each concrete recursive
call independently. -/
def swapSides {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) :
    WatkinsMesnerSplitter H x y z where
  aSet := S.bSet
  bSet := S.aSet
  xPart := S.xPart
  yPart := S.yPart
  zPart := S.zPart
  xA := S.xB
  yA := S.yB
  zA := S.zB
  xB := S.xA
  yB := S.yA
  zB := S.zA
  A_nonempty := S.B_nonempty
  B_nonempty := S.A_nonempty
  A_disjoint_B := S.A_disjoint_B.symm
  X_component := by
    simpa [Finset.union_comm] using S.X_component
  Y_component := by
    simpa [Finset.union_comm] using S.Y_component
  Z_component := by
    simpa [Finset.union_comm] using S.Z_component
  X_disjoint_Y := S.X_disjoint_Y
  X_disjoint_Z := S.X_disjoint_Z
  Y_disjoint_Z := S.Y_disjoint_Z
  x_mem_X := S.x_mem_X
  y_mem_Y := S.y_mem_Y
  z_mem_Z := S.z_mem_Z
  X_A_attachment := S.X_B_attachment
  Y_A_attachment := S.Y_B_attachment
  Z_A_attachment := S.Z_B_attachment
  X_B_attachment := S.X_A_attachment
  Y_B_attachment := S.Y_A_attachment
  Z_B_attachment := S.Z_A_attachment
  A_eq := S.B_eq
  B_eq := S.A_eq
  A_card := S.B_card
  B_card := S.A_card
  twoConnected_compl_X := S.twoConnected_compl_X
  twoConnected_compl_Y := S.twoConnected_compl_Y
  twoConnected_compl_Z := S.twoConnected_compl_Z
  matched_edges_of_both_triples := by
    intro hA hB a ha b hb hab
    rcases S.matched_edges_of_both_triples hB hA b hb a ha hab.symm with
      hX | hY | hZ
    · exact Or.inl ⟨hX.2, hX.1⟩
    · exact Or.inr (Or.inl ⟨hY.2, hY.1⟩)
    · exact Or.inr (Or.inr ⟨hZ.2, hZ.1⟩)
  component_boundary_of_both_triples := by
    intro hA hB D hD
    have hD' : IsComponentAfterDeleting H (S.aSet ∪ S.bSet) D := by
      simpa [Finset.union_comm] using hD
    rcases S.component_boundary_of_both_triples hB hA D hD' with
      hOldA | hOldB | hX | hY | hZ
    · exact Or.inr (Or.inl hOldA)
    · exact Or.inl hOldB
    · exact Or.inr (Or.inr (Or.inl (by
        simpa [Finset.pair_comm] using hX)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        simpa [Finset.pair_comm] using hY))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        simpa [Finset.pair_comm] using hZ))))

@[simp] theorem swapSides_xPart {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) : S.swapSides.xPart = S.xPart := rfl

/-- Cyclically relabel `x,y,z` (and their component and attachment data)
without changing either splitter side. -/
def cycleLeft {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) :
    WatkinsMesnerSplitter H y z x where
  aSet := S.aSet
  bSet := S.bSet
  xPart := S.yPart
  yPart := S.zPart
  zPart := S.xPart
  xA := S.yA
  yA := S.zA
  zA := S.xA
  xB := S.yB
  yB := S.zB
  zB := S.xB
  A_nonempty := S.A_nonempty
  B_nonempty := S.B_nonempty
  A_disjoint_B := S.A_disjoint_B
  X_component := S.Y_component
  Y_component := S.Z_component
  Z_component := S.X_component
  X_disjoint_Y := S.Y_disjoint_Z
  X_disjoint_Z := S.X_disjoint_Y.symm
  Y_disjoint_Z := S.X_disjoint_Z.symm
  x_mem_X := S.y_mem_Y
  y_mem_Y := S.z_mem_Z
  z_mem_Z := S.x_mem_X
  X_A_attachment := S.Y_A_attachment
  Y_A_attachment := S.Z_A_attachment
  Z_A_attachment := S.X_A_attachment
  X_B_attachment := S.Y_B_attachment
  Y_B_attachment := S.Z_B_attachment
  Z_B_attachment := S.X_B_attachment
  A_eq := by
    rw [S.A_eq]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hX | hY | hZ)
      · exact Or.inr (Or.inr hX)
      · exact Or.inl hY
      · exact Or.inr (Or.inl hZ)
    · rintro (hY | hZ | hX)
      · exact Or.inr (Or.inl hY)
      · exact Or.inr (Or.inr hZ)
      · exact Or.inl hX
  B_eq := by
    rw [S.B_eq]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hX | hY | hZ)
      · exact Or.inr (Or.inr hX)
      · exact Or.inl hY
      · exact Or.inr (Or.inl hZ)
    · rintro (hY | hZ | hX)
      · exact Or.inr (Or.inl hY)
      · exact Or.inr (Or.inr hZ)
      · exact Or.inl hX
  A_card := S.A_card
  B_card := S.B_card
  twoConnected_compl_X := S.twoConnected_compl_Y
  twoConnected_compl_Y := S.twoConnected_compl_Z
  twoConnected_compl_Z := S.twoConnected_compl_X
  matched_edges_of_both_triples := by
    intro hA hB a ha b hb hab
    rcases S.matched_edges_of_both_triples hA hB a ha b hb hab with
      hX | hY | hZ
    · exact Or.inr (Or.inr hX)
    · exact Or.inl hY
    · exact Or.inr (Or.inl hZ)
  component_boundary_of_both_triples := by
    intro hA hB D hD
    rcases S.component_boundary_of_both_triples hA hB D hD with
      hA' | hB' | hX | hY | hZ
    · exact Or.inl hA'
    · exact Or.inr (Or.inl hB')
    · exact Or.inr (Or.inr (Or.inr (Or.inr hX)))
    · exact Or.inr (Or.inr (Or.inl hY))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hZ)))

@[simp] theorem cycleLeft_xPart {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) : S.cycleLeft.xPart = S.yPart := rfl

@[simp] theorem cycleLeft_yPart {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) : S.cycleLeft.yPart = S.zPart := rfl

@[simp] theorem cycleLeft_zPart {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) : S.cycleLeft.zPart = S.xPart := rfl

/-- Swap the last two terminals, their components, and their named
attachments while leaving `x` and both splitter sides fixed. -/
def swapLast {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) :
    WatkinsMesnerSplitter H x z y where
  aSet := S.aSet
  bSet := S.bSet
  xPart := S.xPart
  yPart := S.zPart
  zPart := S.yPart
  xA := S.xA
  yA := S.zA
  zA := S.yA
  xB := S.xB
  yB := S.zB
  zB := S.yB
  A_nonempty := S.A_nonempty
  B_nonempty := S.B_nonempty
  A_disjoint_B := S.A_disjoint_B
  X_component := S.X_component
  Y_component := S.Z_component
  Z_component := S.Y_component
  X_disjoint_Y := S.X_disjoint_Z
  X_disjoint_Z := S.X_disjoint_Y
  Y_disjoint_Z := S.Y_disjoint_Z.symm
  x_mem_X := S.x_mem_X
  y_mem_Y := S.z_mem_Z
  z_mem_Z := S.y_mem_Y
  X_A_attachment := S.X_A_attachment
  Y_A_attachment := S.Z_A_attachment
  Z_A_attachment := S.Y_A_attachment
  X_B_attachment := S.X_B_attachment
  Y_B_attachment := S.Z_B_attachment
  Z_B_attachment := S.Y_B_attachment
  A_eq := by
    rw [S.A_eq]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  B_eq := by
    rw [S.B_eq]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  A_card := S.A_card
  B_card := S.B_card
  twoConnected_compl_X := S.twoConnected_compl_X
  twoConnected_compl_Y := S.twoConnected_compl_Z
  twoConnected_compl_Z := S.twoConnected_compl_Y
  matched_edges_of_both_triples := by
    intro hA hB a ha b hb hab
    rcases S.matched_edges_of_both_triples hA hB a ha b hb hab with
      hX | hY | hZ
    · exact Or.inl hX
    · exact Or.inr (Or.inr hY)
    · exact Or.inr (Or.inl hZ)
  component_boundary_of_both_triples := by
    intro hA hB D hD
    rcases S.component_boundary_of_both_triples hA hB D hD with
      hA' | hB' | hX | hY | hZ
    · exact Or.inl hA'
    · exact Or.inr (Or.inl hB')
    · exact Or.inr (Or.inr (Or.inl hX))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hY)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hZ)))

@[simp] theorem swapLast_xPart {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) : S.swapLast.xPart = S.xPart := rfl

@[simp] theorem swapLast_yPart {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) : S.swapLast.yPart = S.zPart := rfl

@[simp] theorem swapLast_zPart {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {x y z : W}
    (S : WatkinsMesnerSplitter H x y z) : S.swapLast.zPart = S.yPart := rfl

/-- The actual strong-induction call for the concrete source graph `G_X`.
The strict inequality is the corrected deleted-centre claim (3), while
three-connectivity and almost-wheel-freeness are the two conclusions of AHT
Lemma 6.4.  Claim (7) then returns the source alternative for `X`. -/
theorem xPart_singleton_or_ambientTwinPair_of_below
    {center : V} {x y z : {w : V // w ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center)
    (horiented : S.yA = S.zA → S.yB = S.zB)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    S.xPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.xPart,
        ∃ q ∈ ahtDeletedFinsetVal S.xPart, AHTTwinPair G p q := by
  let F := S.xThreeFragment hcx
  have hcard : Fintype.card (ConcreteGX.RawVertex S hcx) <
      Fintype.card V :=
    ConcreteGX.replacement_card_lt S hcx hcy hcz hcenterNeighbors
      hnotClose horiented hthree halmost
  have hreplacementThree : IsThreeConnected F.replacementGraph :=
    F.replacementGraph_isThreeConnected hthree
  have hreplacementAlmost : AlmostWheelFree F.replacementGraph :=
    F.replacementGraph_almostWheelFree hthree halmost
  have hrecursive : Nonempty
      (TwoDisjointDegreeThreeFalseTwinPairs F.replacementGraph) :=
    ih (ConcreteGX.RawVertex S hcx) F.replacementGraph hcard
      hreplacementThree hreplacementAlmost
  obtain ⟨T⟩ := hrecursive
  exact S.xThreeFragment_singleton_or_twinPair
    hcx T hreplacementThree

/-- The source `A/B` symmetry makes the concrete `X` recursion unconditional:
if the displayed implication is not already true, its premise is true and
becomes the conclusion after swapping the two splitter sides. -/
theorem xPart_singleton_or_ambientTwinPair_of_below_unoriented
    {center : V} {x y z : {w : V // w ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    S.xPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.xPart,
        ∃ q ∈ ahtDeletedFinsetVal S.xPart, AHTTwinPair G p q := by
  by_cases horiented : S.yA = S.zA → S.yB = S.zB
  · exact S.xPart_singleton_or_ambientTwinPair_of_below
      hcx hcy hcz hcenterNeighbors hnotClose horiented hthree halmost ih
  · have hA : S.yA = S.zA := by
      by_contra hne
      apply horiented
      intro heq
      exact (hne heq).elim
    have hswapped :
        S.swapSides.yA = S.swapSides.zA →
          S.swapSides.yB = S.swapSides.zB := by
      intro _
      exact hA
    simpa only [swapSides_xPart] using
      S.swapSides.xPart_singleton_or_ambientTwinPair_of_below
        hcx hcy hcz hcenterNeighbors hnotClose hswapped
          hthree halmost ih

/-- The cyclic `Y` instance of the same concrete recursive call. -/
theorem yPart_singleton_or_ambientTwinPair_of_below_unoriented
    {center : V} {x y z : {w : V // w ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    S.yPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.yPart,
        ∃ q ∈ ahtDeletedFinsetVal S.yPart, AHTTwinPair G p q := by
  have hcenterNeighbors' : ∀ ⦃q : V⦄, G.Adj center q →
      q = y.1 ∨ q = z.1 ∨ q = x.1 := by
    intro q hq
    rcases hcenterNeighbors hq with hx | hy | hz
    · exact Or.inr (Or.inr hx)
    · exact Or.inl hy
    · exact Or.inr (Or.inl hz)
  simpa only [cycleLeft_xPart] using
    S.cycleLeft.xPart_singleton_or_ambientTwinPair_of_below_unoriented
      hcy hcz hcx hcenterNeighbors' hnotClose hthree halmost ih

/-- The cyclic `Z` instance of the same concrete recursive call. -/
theorem zPart_singleton_or_ambientTwinPair_of_below_unoriented
    {center : V} {x y z : {w : V // w ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    S.zPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.zPart,
        ∃ q ∈ ahtDeletedFinsetVal S.zPart, AHTTwinPair G p q := by
  have hcenterNeighbors' : ∀ ⦃q : V⦄, G.Adj center q →
      q = z.1 ∨ q = x.1 ∨ q = y.1 := by
    intro q hq
    rcases hcenterNeighbors hq with hx | hy | hz
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hy)
    · exact Or.inl hz
  simpa only [cycleLeft_xPart, cycleLeft_yPart] using
    (S.cycleLeft.cycleLeft).xPart_singleton_or_ambientTwinPair_of_below_unoriented
      hcz hcx hcy hcenterNeighbors' hnotClose hthree halmost ih

end WatkinsMesnerSplitter

/-- Two terminal twin pairs contained in disjoint splitter components
already form the forbidden source two-pair certificate. -/
theorem false_of_twinPairs_in_disjoint_parts
    {P Q : Finset V} (hPQ : Disjoint P Q)
    {p q r s : V} (hp : p ∈ P) (hq : q ∈ P)
    (hr : r ∈ Q) (hs : s ∈ Q)
    (hpq : AHTTwinPair G p q) (hrs : AHTTwinPair G r s)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G)) : False := by
  have hpairs : Disjoint ({p, q} : Finset V) ({r, s} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro w hwP hwQ
    have hwPartP : w ∈ P := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwP
      rcases hwP with rfl | rfl
      · exact hp
      · exact hq
    have hwPartQ : w ∈ Q := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwQ
      rcases hwQ with rfl | rfl
      · exact hr
      · exact hs
    exact Finset.disjoint_left.mp hPQ hwPartP hwPartQ
  apply hno
  exact ⟨{
    u := p
    v := q
    x := r
    y := s
    twin_uv := hpq.falseTwins
    twin_xy := hrs.falseTwins
    degree_u := hpq.degree_left
    degree_x := hrs.degree_left
    disjoint := hpairs }⟩

namespace AHTTheorem66SourceData

/-- The concrete `X` recursion specialized all the way to the source data
chosen above.  After a deleted-centre splitter has been constructed, this
branch needs no further geometric or orientation input. -/
theorem xPart_singleton_or_ambientTwinPair_of_below
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    S.xPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.xPart,
        ∃ q ∈ ahtDeletedFinsetVal S.xPart, AHTTwinPair G p q := by
  apply WatkinsMesnerSplitter.xPart_singleton_or_ambientTwinPair_of_below_unoriented
    S D.center_adj_x D.center_adj_y D.center_adj_z
      (fun _ hq ↦ D.center_neighbor_location hq) D.not_close hthree halmost ih

theorem yPart_singleton_or_ambientTwinPair_of_below
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    S.yPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.yPart,
        ∃ q ∈ ahtDeletedFinsetVal S.yPart, AHTTwinPair G p q := by
  apply WatkinsMesnerSplitter.yPart_singleton_or_ambientTwinPair_of_below_unoriented
    S D.center_adj_x D.center_adj_y D.center_adj_z
      (fun _ hq ↦ D.center_neighbor_location hq) D.not_close hthree halmost ih

theorem zPart_singleton_or_ambientTwinPair_of_below
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    S.zPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.zPart,
        ∃ q ∈ ahtDeletedFinsetVal S.zPart, AHTTwinPair G p q := by
  apply WatkinsMesnerSplitter.zPart_singleton_or_ambientTwinPair_of_below_unoriented
    S D.center_adj_x D.center_adj_y D.center_adj_z
      (fun _ hq ↦ D.center_neighbor_location hq) D.not_close hthree halmost ih

/-- All three concrete Claim-(7) alternatives, with both splitter-side and
terminal-label symmetries already discharged. -/
theorem all_terminalParts_singleton_or_ambientTwinPair_of_below
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    (S.xPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.xPart,
        ∃ q ∈ ahtDeletedFinsetVal S.xPart, AHTTwinPair G p q) ∧
    (S.yPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.yPart,
        ∃ q ∈ ahtDeletedFinsetVal S.yPart, AHTTwinPair G p q) ∧
    (S.zPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.zPart,
        ∃ q ∈ ahtDeletedFinsetVal S.zPart, AHTTwinPair G p q) := by
  exact ⟨D.xPart_singleton_or_ambientTwinPair_of_below
      S hthree halmost ih,
    D.yPart_singleton_or_ambientTwinPair_of_below S hthree halmost ih,
    D.zPart_singleton_or_ambientTwinPair_of_below S hthree halmost ih⟩

/-- Once `X` contains a twin pair, the other two terminal components must
take their singleton alternatives: a second terminal twin pair would be
vertex-disjoint from the first and would already contradict the assumed
absence of the source two-pair certificate. -/
theorem yzParts_singleton_of_xPart_twinPair_below
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) :
    S.yPart.card = 1 ∧ S.zPart.card = 1 := by
  constructor
  · rcases D.yPart_singleton_or_ambientTwinPair_of_below
        S hthree halmost ih with hy | ⟨r, hr, s, hs, hrs⟩
    · exact hy
    · exact False.elim (false_of_twinPairs_in_disjoint_parts
        (disjoint_ahtDeletedFinsetVal S.X_disjoint_Y)
        hp hq hr hs hpq hrs hno)
  · rcases D.zPart_singleton_or_ambientTwinPair_of_below
        S hthree halmost ih with hz | ⟨r, hr, s, hs, hrs⟩
    · exact hz
    · exact False.elim (false_of_twinPairs_in_disjoint_parts
        (disjoint_ahtDeletedFinsetVal S.X_disjoint_Z)
        hp hq hr hs hpq hrs hno)

/-- The all-singleton branch is exactly the corrected deleted-centre input
to source claim (5); hence both splitter sides are triples. -/
theorem splitter_side_cards_eq_three_of_terminalParts_singleton
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G) :
    S.aSet.card = 3 ∧ S.bSet.card = 3 := by
  obtain ⟨x0, hxPart⟩ := Finset.card_eq_one.mp hx
  obtain ⟨y0, hyPart⟩ := Finset.card_eq_one.mp hy
  obtain ⟨z0, hzPart⟩ := Finset.card_eq_one.mp hz
  have hxx0 : D.xDeleted = x0 := by
    simpa [hxPart] using S.x_mem_X
  have hyy0 : D.yDeleted = y0 := by
    simpa [hyPart] using S.y_mem_Y
  have hzz0 : D.zDeleted = z0 := by
    simpa [hzPart] using S.z_mem_Z
  let C : AHTClaim5DeletedSplitter G D.center
      D.xDeleted D.yDeleted D.zDeleted :=
    { splitter := S
      xPart_eq := by simpa [hxx0] using hxPart
      yPart_eq := by simpa [hyy0] using hyPart
      zPart_eq := by simpa [hzz0] using hzPart
      center_adj_x := D.center_adj_x
      center_adj_y := D.center_adj_y
      center_adj_z := D.center_adj_z
      center_not_close := D.not_close }
  exact aht_theorem66_claim5_of_deletedSplitter hthree halmost C

end AHTTheorem66SourceData

/-! ## The component-side Claim-(6) reduction -/

namespace AHTTerminalComponentLocal

/-- If a mapped terminal component already contains the ambient twin pair
returned by Claim (7), its Claim-(6) singleton branch is impossible.  The
component is therefore either large or the explicit exceptional triple. -/
theorem large_or_exceptional_of_twinPair
    (C : AHTTerminalComponentLocal G) {p q : V}
    (hp : p ∈ C.part) (hq : q ∈ C.part) (hpq : AHTTwinPair G p q)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G) :
    4 ≤ C.part.card ∨ AHTTerminalExceptionalTriple C := by
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hmin : ∀ w : V, 3 ≤ G.degree w := fun w ↦ hthree.degree_ge w
  rcases aht_theorem66_claim6_terminal_component C htri hmin with
    hone | hlarge | hexceptional
  · obtain ⟨w, hpart⟩ := Finset.card_eq_one.mp hone
    have hpw : p = w := by simpa [hpart] using hp
    have hqw : q = w := by simpa [hpart] using hq
    exact (hpq.falseTwins.1 (hpw.trans hqw.symm)).elim
  · exact Or.inl hlarge
  · exact Or.inr hexceptional

end AHTTerminalComponentLocal

/-! ## Converting a Claim-One certificate to the opposite fragment -/

/-- A Claim-One certificate, oriented so that its `opposite` side is the
retained three-fragment and its six-vertex `fragment` side is discarded.
The equalities make the later cardinality and complementary-twin arguments
literal rewrites rather than additional set-theoretic assumptions. -/
structure AHTClaimOneOppositeFragment
    (C : AHTClaimOneFragmentCertificate G) where
  fragment : AHTThreeFragment G
  verts_eq : fragment.verts = C.opposite
  boundary_eq : fragment.boundaryFinset = C.boundary
  outside_eq :
    Finset.univ \ (fragment.verts ∪
      ({fragment.a, fragment.b, fragment.c} : Finset V)) = C.fragment

namespace AHTClaimOneFragmentCertificate

/-- The complementary side of every Claim-One certificate is a genuine
`AHTThreeFragment`.  Exactness of its boundary uses both directions stored
in the certificate: no edge leaves `opposite` away from `boundary`, and
each boundary vertex has a neighbour in `opposite`. -/
theorem exists_oppositeFragment (C : AHTClaimOneFragmentCertificate G) :
    Nonempty (AHTClaimOneOppositeFragment C) := by
  obtain ⟨a, b, c, hab, hac, hbc, hboundary⟩ :=
    Finset.card_eq_three.mp C.boundary_card
  have hoppositeNonempty : C.opposite.Nonempty := by
    apply Finset.card_pos.mp
    have h := C.two_le_opposite
    omega
  have hfragmentNonempty : C.fragment.Nonempty := by
    apply Finset.card_pos.mp
    have h := C.six_le_fragment
    omega
  have houtside :
      Finset.univ \ (C.opposite ∪ ({a, b, c} : Finset V)) =
        C.fragment := by
    ext q
    constructor
    · intro hq
      have hq' := Finset.mem_sdiff.mp hq
      have hparts : q ∈ C.fragment ∪ C.boundary ∪ C.opposite := by
        rw [C.partition]
        exact Finset.mem_univ q
      rcases Finset.mem_union.mp hparts with hside | hopposite
      · rcases Finset.mem_union.mp hside with hfragment | hboundaryMem
        · exact hfragment
        · have hboundaryMem' : q ∈ ({a, b, c} : Finset V) :=
            hboundary ▸ hboundaryMem
          exact (hq'.2 (Finset.mem_union_right _ hboundaryMem')).elim
      · exact (hq'.2 (Finset.mem_union_left _ hopposite)).elim
    · intro hq
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, ?_⟩
      intro hunion
      rcases Finset.mem_union.mp hunion with hopposite | hboundaryMem
      · exact Finset.disjoint_left.mp C.fragment_disjoint_opposite
          hq hopposite
      · have hboundaryMem' : q ∈ C.boundary :=
          hboundary.symm ▸ hboundaryMem
        exact Finset.disjoint_left.mp C.fragment_disjoint_boundary
          hq hboundaryMem'
  let F : AHTThreeFragment G :=
    { verts := C.opposite
      a := a
      b := b
      c := c
      ab := hab
      ac := hac
      bc := hbc
      boundary_disjoint := by
        rw [← hboundary]
        exact C.opposite_disjoint_boundary
      nonempty := hoppositeNonempty
      outside_nonempty := by
        rw [houtside]
        exact hfragmentNonempty
      boundary_exact := by
        intro q hq
        constructor
        · rintro ⟨p, hp, hqp⟩
          have hqBoundary : q ∈ C.boundary :=
            C.opposite_boundary p hp q hqp.symm hq
          have hqBoundary' : q ∈ ({a, b, c} : Finset V) :=
            hboundary ▸ hqBoundary
          simpa only [Finset.mem_insert, Finset.mem_singleton] using
            hqBoundary'
        · intro hqBoundary
          have hqBoundary' : q ∈ C.boundary := by
            rw [hboundary]
            simpa only [Finset.mem_insert, Finset.mem_singleton] using
              hqBoundary
          obtain ⟨p, hp, hpq⟩ :=
            C.opposite_meets_boundary q hqBoundary'
          exact ⟨p, hp, hpq.symm⟩ }
  exact ⟨{
    fragment := F
    verts_eq := rfl
    boundary_eq := by
      simpa [F, AHTThreeFragment.boundaryFinset] using hboundary.symm
    outside_eq := by
      simpa [F] using houtside }⟩

/-- Claim (1), with the recursive pair supplied by the actual strong
induction hypothesis.  Thus a Claim-One certificate cannot occur in a
minimal counterexample once the strict-below theorem is available. -/
theorem false_of_below
    (C : AHTClaimOneFragmentCertificate G)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) : False := by
  obtain ⟨P⟩ := C.exists_oppositeFragment
  let F := P.fragment
  have houtside : 6 ≤
      (Finset.univ \ (F.verts ∪
        ({F.a, F.b, F.c} : Finset V))).card := by
    rw [P.outside_eq]
    exact C.six_le_fragment
  have hcard : Fintype.card (F.PreparedVertex ⊕ Fin 2) <
      Fintype.card V :=
    F.replacement_card_lt_of_six_le_outside houtside
  have hreplacementThree : IsThreeConnected F.replacementGraph :=
    F.replacementGraph_isThreeConnected hthree
  have hreplacementAlmost : AlmostWheelFree F.replacementGraph :=
    F.replacementGraph_almostWheelFree hthree halmost
  have hrecursive : Nonempty
      (TwoDisjointDegreeThreeFalseTwinPairs F.replacementGraph) :=
    ih (F.PreparedVertex ⊕ Fin 2) F.replacementGraph hcard
      hreplacementThree hreplacementAlmost
  obtain ⟨T⟩ := hrecursive
  have htwinLeftOutside : C.twinLeft ∉ F.verts := by
    rw [P.verts_eq]
    exact fun hmem ↦ Finset.disjoint_left.mp
      C.fragment_disjoint_opposite C.twinLeft_mem hmem
  have htwinRightOutside : C.twinRight ∉ F.verts := by
    rw [P.verts_eq]
    exact fun hmem ↦ Finset.disjoint_left.mp
      C.fragment_disjoint_opposite C.twinRight_mem hmem
  have hnotTwo : ¬2 ≤ F.verts.card :=
    F.not_two_le_card_of_replacement_twoPairs T hreplacementThree hno
      C.twins htwinLeftOutside htwinRightOutside
  apply hnotTwo
  rw [P.verts_eq]
  exact C.two_le_opposite

end AHTClaimOneFragmentCertificate

namespace AHTRelevantTripleSideLocal

/-- The both-triples terminal-twin branch, once condition (vii) has been
packaged as the relevant same-side component union.  The local
triangle-free/minimum-degree argument supplies the two vertices on that
side, `ahtClaimOneFragmentCertificate_of_relevantTripleSide` turns the
opposite large side and its terminal twin pair into Claim (1), and the
actual strict-below hypothesis closes the branch. -/
theorem false_of_opposite_twinPair_below
    (S : AHTRelevantTripleSideLocal G) {p q : V}
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hpq : AHTTwinPair G p q)
    (hp : p ∈ Finset.univ \ (S.carrier ∪ S.boundary))
    (hq : q ∈ Finset.univ \ (S.carrier ∪ S.boundary))
    (hlarge : 6 ≤
      (Finset.univ \ (S.carrier ∪ S.boundary)).card) : False := by
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hmin : ∀ z : V, 3 ≤ G.degree z := fun z ↦ hthree.degree_ge z
  obtain ⟨C⟩ := ahtClaimOneFragmentCertificate_of_relevantTripleSide
    S hthree htri hmin hpq hp hq hlarge
  exact C.false_of_below hthree halmost hno ih

end AHTRelevantTripleSideLocal

namespace WatkinsMesnerSplitter

/-- Source Claim (8), both-triples branch, for a twin pair in `X` while
the other two terminal components are singletons.  The actual component
union is packaged as `AHTRelevantTripleSideLocal`; the twin pair and the
three vertices of the opposite splitter side provide the six vertices on
the large side of Claim (1). -/
theorem false_of_xPart_twinPair_both_triples_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) : False := by
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hmin : ∀ r : V, 3 ≤ G.degree r := fun r ↦ hthree.degree_ge r
  let R : AHTRelevantTripleSideLocal G :=
    S.relevantLeftSideLocal_of_both_triples
      hthree htri hmin hAcard hBcard hy hz hcenterNeighbors
  have hp' : p ∈ Finset.univ \ (R.carrier ∪ R.boundary) := by
    change p ∈ Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet)
    exact S.xPart_mem_complement_leftCarrier hcx hcy hcz hp
  have hq' : q ∈ Finset.univ \ (R.carrier ∪ R.boundary) := by
    change q ∈ Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet)
    exact S.xPart_mem_complement_leftCarrier hcx hcy hcz hq
  have hlarge : 6 ≤
      (Finset.univ \ (R.carrier ∪ R.boundary)).card := by
    change 6 ≤ (Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet)).card
    exact S.six_le_complement_leftCarrier_of_xTwinPair
      hcx hcy hcz hBcard hp hq hpq
  exact R.false_of_opposite_twinPair_below
    hthree halmost hno ih hpq hp' hq' hlarge

/-- Source Claim (5) in the normalized mixed `|A|=3, |B|=1` branch:
the union `C_A` of residual components whose external boundary lies in `A`
has at most one vertex.  If it had two, the terminal twin pair and the four
displayed vertices `y,z,x_B,center` give the required six-vertex opposite
side of the forbidden three-fragment. -/
theorem ambientLeftCarrier_card_le_one_of_xTwinPair_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1) (hAcard : S.aSet.card = 3)
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) :
    S.ambientLeftCarrier.card ≤ 1 := by
  by_contra hcard
  have htwo : 2 ≤ S.ambientLeftCarrier.card := by omega
  have hp' : p ∈ Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet) :=
    S.xPart_mem_complement_leftCarrier hcx hcy hcz hp
  have hq' : q ∈ Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet) :=
    S.xPart_mem_complement_leftCarrier hcx hcy hcz hq
  have hlarge : 6 ≤ (Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet)).card :=
    S.six_le_complement_leftCarrier_of_xTwinPair_mixed
      hcx hcy hcz hp hq hpq
  obtain ⟨C⟩ := ahtClaimOneFragmentCertificate_of_threeBoundarySide
    S.ambientLeftCarrier (ahtDeletedFinsetVal S.aSet)
      hthree S.ambientLeftCarrier_disjoint
      S.ambientLeftCarrier_externalBoundary (by simpa using hAcard)
      htwo hpq hp' hq' hlarge
  exact C.false_of_below hthree halmost hno ih

end WatkinsMesnerSplitter

namespace AHTTheorem66SourceData

/-- After the completed both-triples and both-singletons branches of source
Claim (8), an `X`-terminal twin pair can survive only in one of the two
mixed splitter-side cardinality configurations.  These are precisely the
two fan/wheel branches remaining from the paper. -/
theorem mixed_side_cards_of_xPart_twinPair_below
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) :
    (S.aSet.card = 1 ∧ S.bSet.card = 3) ∨
      (S.aSet.card = 3 ∧ S.bSet.card = 1) := by
  obtain ⟨hy, hz⟩ := D.yzParts_singleton_of_xPart_twinPair_below
    S hthree halmost hno ih hp hq hpq
  rcases S.A_card with hAone | hAthree
  · rcases S.B_card with hBone | hBthree
    · exact False.elim
        (S.false_of_yz_singletons_both_sides_singletons
          hthree D.not_close D.center_adj_y D.center_adj_z
          (fun _ h ↦ D.center_neighbor_location h)
          hy hz hAone hBone)
    · exact Or.inl ⟨hAone, hBthree⟩
  · rcases S.B_card with hBone | hBthree
    · exact Or.inr ⟨hAthree, hBone⟩
    · exact False.elim
        (S.false_of_xPart_twinPair_both_triples_below
          hthree halmost hno ih
          D.center_adj_x D.center_adj_y D.center_adj_z
          (fun _ h ↦ D.center_neighbor_location h)
          hAthree hBthree hy hz hp hq hpq)

end AHTTheorem66SourceData

/-! ## The two source fans in the mixed splitter-side branch -/

/-- An ambient path obtained from a two-fan in `G - deleted`, normalized so
that its only vertices in the displayed three-set are its two endpoints.
The root lies on the path and the deleted vertex does not.  This is the
literal path datum used twice in the mixed `3/1` branch of source Claim
(8). -/
structure AHTMixedTripleFan (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted root a b c : V) where
  start : V
  finish : V
  path : G.Walk start finish
  isPath : path.IsPath
  root_mem : root ∈ path.support
  deleted_not_mem : deleted ∉ path.support
  start_target : start = a ∨ start = b ∨ start = c
  finish_target : finish = a ∨ finish = b ∨ finish = c
  start_ne_finish : start ≠ finish
  target_only_endpoints :
    ∀ w, w ∈ path.support →
      (w = a ∨ w = b ∨ w = c) → w = start ∨ w = finish

namespace AHTMixedTripleFan

/-- Reverse the target-clean path without changing its deleted vertex,
root, or target triple. -/
def reverse (F : AHTMixedTripleFan G deleted root a b c) :
    AHTMixedTripleFan G deleted root a b c where
  start := F.finish
  finish := F.start
  path := F.path.reverse
  isPath := F.isPath.reverse
  root_mem := by
    simpa only [Walk.support_reverse, List.mem_reverse] using F.root_mem
  deleted_not_mem := by
    simpa only [Walk.support_reverse, List.mem_reverse] using F.deleted_not_mem
  start_target := F.finish_target
  finish_target := F.start_target
  start_ne_finish := F.start_ne_finish.symm
  target_only_endpoints := by
    intro w hw hwTarget
    have hw' : w ∈ F.path.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hw
    rcases F.target_only_endpoints w hw' hwTarget with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Reorder the last two names of the target triple without changing the
underlying fan path. -/
def swapLastTargets (F : AHTMixedTripleFan G deleted root a b c) :
    AHTMixedTripleFan G deleted root a c b where
  start := F.start
  finish := F.finish
  path := F.path
  isPath := F.isPath
  root_mem := F.root_mem
  deleted_not_mem := F.deleted_not_mem
  start_target := by
    rcases F.start_target with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  finish_target := by
    rcases F.finish_target with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  start_ne_finish := F.start_ne_finish
  target_only_endpoints := by
    intro w hw hwT
    apply F.target_only_endpoints w hw
    rcases hwT with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- The normalized fan endpoints are one of the three unordered pairs in
the target triple.  Keeping both orientations explicit makes the later
`Walk.copy`/`Walk.reverse` normalization definitional. -/
theorem endpoint_pair_cases
    (F : AHTMixedTripleFan G deleted root a b c) :
    (F.start = a ∧ F.finish = b) ∨
      (F.start = b ∧ F.finish = a) ∨
      (F.start = a ∧ F.finish = c) ∨
      (F.start = c ∧ F.finish = a) ∨
      (F.start = b ∧ F.finish = c) ∨
      (F.start = c ∧ F.finish = b) := by
  rcases F.start_target with hs | hs | hs <;>
    rcases F.finish_target with ht | ht | ht
  · exact False.elim (F.start_ne_finish (hs.trans ht.symm))
  · exact Or.inl ⟨hs, ht⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hs, ht⟩))
  · exact Or.inr (Or.inl ⟨hs, ht⟩)
  · exact False.elim (F.start_ne_finish (hs.trans ht.symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, ht⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, ht⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, ht⟩))))
  · exact False.elim (F.start_ne_finish (hs.trans ht.symm))

end AHTMixedTripleFan

/-- The second mixed-branch two-fan, represented by its target-minimal path
between a displayed pair. -/
structure AHTMixedPairFan (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted root a b : V) where
  start : V
  finish : V
  path : G.Walk start finish
  isPath : path.IsPath
  root_mem : root ∈ path.support
  deleted_not_mem : deleted ∉ path.support
  start_target : start = a ∨ start = b
  finish_target : finish = a ∨ finish = b
  start_ne_finish : start ≠ finish
  target_only_endpoints :
    ∀ w, w ∈ path.support → (w = a ∨ w = b) →
      w = start ∨ w = finish

namespace AHTMixedPairFan

def reverse (F : AHTMixedPairFan G deleted root a b) :
    AHTMixedPairFan G deleted root a b where
  start := F.finish
  finish := F.start
  path := F.path.reverse
  isPath := F.isPath.reverse
  root_mem := by
    simpa only [Walk.support_reverse, List.mem_reverse] using F.root_mem
  deleted_not_mem := by
    simpa only [Walk.support_reverse, List.mem_reverse] using F.deleted_not_mem
  start_target := F.finish_target
  finish_target := F.start_target
  start_ne_finish := F.start_ne_finish.symm
  target_only_endpoints := by
    intro w hw hwT
    have hw' : w ∈ F.path.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hw
    rcases F.target_only_endpoints w hw' hwT with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem endpoints (F : AHTMixedPairFan G deleted root a b) :
    (F.start = a ∧ F.finish = b) ∨
      (F.start = b ∧ F.finish = a) := by
  rcases F.start_target with hs | hs <;>
    rcases F.finish_target with ht | ht
  · exact False.elim (F.start_ne_finish (hs.trans ht.symm))
  · exact Or.inl ⟨hs, ht⟩
  · exact Or.inr ⟨hs, ht⟩
  · exact False.elim (F.start_ne_finish (hs.trans ht.symm))

end AHTMixedPairFan

/-- The target-minimal pair fan in `G - deleted`. -/
theorem exists_ahtMixedPairFan
    (hthree : IsThreeConnected G) {deleted root a b : V}
    (hrd : root ≠ deleted) (had : a ≠ deleted)
    (hbd : b ≠ deleted) (hra : root ≠ a) (hrb : root ≠ b)
    (hab : a ≠ b) : Nonempty (AHTMixedPairFan G deleted root a b) := by
  classical
  let aD : {w : V // w ≠ deleted} := ⟨a, had⟩
  let bD : {w : V // w ≠ deleted} := ⟨b, hbd⟩
  let rootD : {w : V // w ≠ deleted} := ⟨root, hrd⟩
  let targets : Finset {w : V // w ≠ deleted} := {aD, bD}
  have hrootTargets : rootD ∉ targets := by
    simp only [targets, Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h
    · exact hra (congrArg Subtype.val h)
    · exact hrb (congrArg Subtype.val h)
  have habD : aD ≠ bD := fun h ↦ hab (congrArg Subtype.val h)
  have htargetsCard : 2 ≤ targets.card := by simp [targets, habD]
  obtain ⟨hconn, hdelete⟩ :=
    vertexTwoConnected_delete_of_isThreeConnected hthree deleted
  obtain ⟨s, t, hs, ht, hst, p, hp, hroot, htarget⟩ :=
    exists_targetPath_through_of_vertexTwoConnected
      targets hrootTargets htargetsCard hconn hdelete
  let inc : (G.induce fun w : V ↦ w ≠ deleted) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := fun w : V ↦ w ≠ deleted)).toHom
  let pG : G.Walk s.1 t.1 := p.map inc
  have hpG : pG.IsPath := hp.map Subtype.val_injective
  have hrootG : root ∈ pG.support := by
    change root ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨rootD, hroot, rfl⟩
  have hdeletedG : deleted ∉ pG.support := by
    change deleted ∉ (p.map inc).support
    rw [Walk.support_map]
    intro h
    obtain ⟨w, -, hw⟩ := List.mem_map.mp h
    change w.1 = deleted at hw
    exact w.2 hw
  have endpointTarget (w : {q : V // q ≠ deleted}) (hw : w ∈ targets) :
      w.1 = a ∨ w.1 = b := by
    have hw' : w = aD ∨ w = bD := by simpa [targets] using hw
    rcases hw' with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have htargetG : ∀ w, w ∈ pG.support →
      (w = a ∨ w = b) → w = s.1 ∨ w = t.1 := by
    intro w hwp hwT
    change w ∈ (p.map inc).support at hwp
    rw [Walk.support_map] at hwp
    obtain ⟨wD, hwDp, hwD⟩ := List.mem_map.mp hwp
    change wD.1 = w at hwD
    have hwD' : wD.1 = w := hwD
    have hwTargets : wD ∈ targets := by
      simp only [targets, Finset.mem_insert, Finset.mem_singleton]
      rcases hwT with rfl | rfl
      · exact Or.inl (Subtype.ext hwD')
      · exact Or.inr (Subtype.ext hwD')
    rcases htarget wD hwDp hwTargets with h | h
    · exact Or.inl (hwD'.symm.trans (congrArg Subtype.val h))
    · exact Or.inr (hwD'.symm.trans (congrArg Subtype.val h))
  exact ⟨{
    start := s.1
    finish := t.1
    path := pG
    isPath := hpG
    root_mem := hrootG
    deleted_not_mem := hdeletedG
    start_target := endpointTarget s hs
    finish_target := endpointTarget t ht
    start_ne_finish := fun h ↦ hst (Subtype.ext h)
    target_only_endpoints := htargetG }⟩

/-- Three-connectivity supplies the normalized mixed-branch fan after
deleting its future wheel centre. -/
theorem exists_ahtMixedTripleFan
    (hthree : IsThreeConnected G) {deleted root a b c : V}
    (hrd : root ≠ deleted) (had : a ≠ deleted)
    (hbd : b ≠ deleted) (hcd : c ≠ deleted)
    (hra : root ≠ a) (hrb : root ≠ b) (hrc : root ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Nonempty (AHTMixedTripleFan G deleted root a b c) := by
  classical
  let aD : {w : V // w ≠ deleted} := ⟨a, had⟩
  let bD : {w : V // w ≠ deleted} := ⟨b, hbd⟩
  let cD : {w : V // w ≠ deleted} := ⟨c, hcd⟩
  let rootD : {w : V // w ≠ deleted} := ⟨root, hrd⟩
  let targets : Finset {w : V // w ≠ deleted} := {aD, bD, cD}
  have hrootTargets : rootD ∉ targets := by
    simp only [targets, Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h | h
    · exact hra (congrArg Subtype.val h)
    · exact hrb (congrArg Subtype.val h)
    · exact hrc (congrArg Subtype.val h)
  have haDbD : aD ≠ bD := by
    intro h
    exact hab (congrArg Subtype.val h)
  have htargetsCard : 2 ≤ targets.card := by
    have hpair : ({aD, bD} : Finset {w : V // w ≠ deleted}).card = 2 := by
      simp [haDbD]
    rw [← hpair]
    exact Finset.card_le_card (by simp [targets])
  obtain ⟨hconn, hdelete⟩ :=
    vertexTwoConnected_delete_of_isThreeConnected hthree deleted
  obtain ⟨s, t, hs, ht, hst, p, hp, hroot, htarget⟩ :=
    exists_targetPath_through_of_vertexTwoConnected
      targets hrootTargets htargetsCard hconn hdelete
  let inc : (G.induce fun w : V ↦ w ≠ deleted) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := fun w : V ↦ w ≠ deleted)).toHom
  let pG : G.Walk s.1 t.1 := p.map inc
  have hpG : pG.IsPath := hp.map Subtype.val_injective
  have hrootG : root ∈ pG.support := by
    change root ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨rootD, hroot, rfl⟩
  have hdeletedG : deleted ∉ pG.support := by
    change deleted ∉ (p.map inc).support
    rw [Walk.support_map]
    intro h
    obtain ⟨w, -, hw⟩ := List.mem_map.mp h
    change w.1 = deleted at hw
    exact w.2 hw
  have endpointTarget
      (w : {q : V // q ≠ deleted}) (hw : w ∈ targets) :
      w.1 = a ∨ w.1 = b ∨ w.1 = c := by
    have hw' : w = aD ∨ w = bD ∨ w = cD := by
      simpa only [targets, Finset.mem_insert, Finset.mem_singleton] using hw
    rcases hw' with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have htargetG : ∀ w, w ∈ pG.support →
      (w = a ∨ w = b ∨ w = c) → w = s.1 ∨ w = t.1 := by
    intro w hwp hwTarget
    change w ∈ (p.map inc).support at hwp
    rw [Walk.support_map] at hwp
    obtain ⟨wD, hwDp, hwD⟩ := List.mem_map.mp hwp
    change wD.1 = w at hwD
    have hwD' : wD.1 = w := hwD
    have hwDTargets : wD ∈ targets := by
      simp only [targets, Finset.mem_insert, Finset.mem_singleton]
      rcases hwTarget with rfl | rfl | rfl
      · exact Or.inl (Subtype.ext hwD')
      · exact Or.inr (Or.inl (Subtype.ext hwD'))
      · exact Or.inr (Or.inr (Subtype.ext hwD'))
    rcases htarget wD hwDp hwDTargets with h | h
    · exact Or.inl (hwD'.symm.trans (congrArg Subtype.val h))
    · exact Or.inr (hwD'.symm.trans (congrArg Subtype.val h))
  exact ⟨{
    start := s.1
    finish := t.1
    path := pG
    isPath := hpG
    root_mem := hrootG
    deleted_not_mem := hdeletedG
    start_target := endpointTarget s hs
    finish_target := endpointTarget t ht
    start_ne_finish := fun h ↦ hst (Subtype.ext h)
    target_only_endpoints := htargetG }⟩

namespace WatkinsMesnerSplitter

/-- Support-aware version of the elementary edge-boundary crossing lemma,
placed before the mixed-fan consumers that use it. -/
theorem _root_.SimpleGraph.Walk.exists_boundary_edge_on_support
    {a b : V} (p : G.Walk a b) (C : Finset V)
    (ha : a ∈ C) (hb : b ∉ C) :
    ∃ u ∈ C, ∃ v ∉ C,
      u ∈ p.support ∧ v ∈ p.support ∧ G.Adj u v := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons a c b hac p ih =>
      by_cases hc : c ∈ C
      · obtain ⟨u, huC, v, hvC, hup, hvp, huv⟩ := ih hc hb
        exact ⟨u, huC, v, hvC, by simp [hup], by simp [hvp], huv⟩
      · exact ⟨a, ha, c, hc, by simp, by simp, hac⟩

/-- The second fan stays in `X` except for its two target endpoints. -/
theorem mixedSecondFan_support_location
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    {xPrime : V} (hxPrime : xPrime ∈ ahtDeletedFinsetVal S.xPart)
    (F : AHTMixedPairFan G S.xB.1 xPrime center S.xA.1) :
    ∀ w, w ∈ F.path.support →
      w ∈ ahtDeletedFinsetVal S.xPart ∨
        w = center ∨ w = S.xA.1 := by
  have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
  rw [ahtDeletedFinsetVal_union] at hXsep
  have hxPrimeCenter : xPrime ≠ center := by
    intro h
    exact center_not_mem_ahtDeletedFinsetVal S.xPart (h ▸ hxPrime)
  have hxPrimeA : xPrime ≠ S.xA.1 := by
    intro h
    exact Finset.disjoint_left.mp hXsep hxPrime
      (Finset.mem_union_left _
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_A_attachment.1))
  have hxPrimeStart : xPrime ≠ F.start := by
    rcases F.start_target with h | h
    · exact fun h' ↦ hxPrimeCenter (h'.trans h)
    · exact fun h' ↦ hxPrimeA (h'.trans h)
  have hxPrimeFinish : xPrime ≠ F.finish := by
    rcases F.finish_target with h | h
    · exact fun h' ↦ hxPrimeCenter (h'.trans h)
    · exact fun h' ↦ hxPrimeA (h'.trans h)
  have hXambient : IsComponentAfterDeleting G
      (ahtDeletedFinsetVal S.aSet ∪
        ahtDeletedFinsetVal S.bSet ∪ {center})
      (ahtDeletedFinsetVal S.xPart) := by
    simpa using S.X_component.ambient_of_deleteVertex (G := G)
  intro w hwPath
  by_cases hwStart : w = F.start
  · rcases F.start_target with h | h
    · exact Or.inr (Or.inl (hwStart.trans h))
    · exact Or.inr (Or.inr (hwStart.trans h))
  by_cases hwFinish : w = F.finish
  · rcases F.finish_target with h | h
    · exact Or.inr (Or.inl (hwFinish.trans h))
    · exact Or.inr (Or.inr (hwFinish.trans h))
  by_cases hwX : w ∈ ahtDeletedFinsetVal S.xPart
  · exact Or.inl hwX
  obtain ⟨r, -, hrSub, hrEnds⟩ := F.isPath.exists_internal_interval
    F.root_mem hwPath hxPrimeStart hxPrimeFinish hwStart hwFinish
  obtain ⟨u, huX, v, hvX, hur, hvr, huv⟩ :=
    r.exists_boundary_edge_on_support (ahtDeletedFinsetVal S.xPart)
      hxPrime hwX
  have hvDelete : v ∈ ahtDeletedFinsetVal S.aSet ∪
      ahtDeletedFinsetVal S.bSet ∪ {center} := by
    by_contra hv
    exact hvX (hXambient.2.2.2 u huX v hv huv)
  rcases Finset.mem_union.mp hvDelete with hvAB | hvCenter
  · rcases Finset.mem_union.mp hvAB with hvA | hvB
    · obtain ⟨u', hu'X, hu'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal huX
      obtain ⟨v', hv'A, hv'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hvA
      have huvDel : (deleteVertex G center).Adj u' v' :=
        (deleteVertex_adj (G := G)).mpr (by
          simpa [hu'val, hv'val] using huv)
      have hvEq' := S.X_A_attachment.2.2
        u' hu'X v' hv'A huvDel
      have hvEq : v = S.xA.1 :=
        hv'val.symm.trans (congrArg Subtype.val hvEq')
      rcases F.target_only_endpoints v (hrSub v hvr)
          (Or.inr hvEq) with h | h
      · exact False.elim ((hrEnds v hvr).1 h)
      · exact False.elim ((hrEnds v hvr).2 h)
    · obtain ⟨u', hu'X, hu'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal huX
      obtain ⟨v', hv'B, hv'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hvB
      have huvDel : (deleteVertex G center).Adj u' v' :=
        (deleteVertex_adj (G := G)).mpr (by
          simpa [hu'val, hv'val] using huv)
      have hvEq' := S.X_B_attachment.2.2
        u' hu'X v' hv'B huvDel
      have hvEq : v = S.xB.1 :=
        hv'val.symm.trans (congrArg Subtype.val hvEq')
      exact False.elim (F.deleted_not_mem (hvEq ▸ hrSub v hvr))
  · have hvEq : v = center := by simpa using hvCenter
    rcases F.target_only_endpoints v (hrSub v hvr)
        (Or.inl hvEq) with h | h
    · exact False.elim ((hrEnds v hvr).1 h)
    · exact False.elim ((hrEnds v hvr).2 h)

end WatkinsMesnerSplitter

namespace WatkinsMesnerSplitter.MixedResidualComponent

/-- Transport the same residual component through the `y/z` relabelling.
-/
def swapLast
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent) : S.swapLast.MixedResidualComponent where
  carrier := R.carrier
  component := R.component
  disjoint_xPart := R.disjoint_xPart
  disjoint_yPart := R.disjoint_zPart
  disjoint_zPart := R.disjoint_yPart
  xBPrime := R.xBPrime
  xBPrime_mem := R.xBPrime_mem
  adj_xBPrime_xB := R.adj_xBPrime_xB

/-- The residual witness supplies the first fan of the normalized mixed
branch, through `x'_B` and between two distinct vertices of `A`, in the
ambient graph with `x_B` deleted. -/
theorem exists_firstFan
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent)
    (hthree : IsThreeConnected G) (hAcard : S.aSet.card = 3) :
    Nonempty (AHTMixedTripleFan G S.xB.1 R.xBPrime
      S.xA.1 S.yA.1 S.zA.1) := by
  have hneA := S.a_attachments_pairwise_ne_of_card_three hAcard
  have hxAxB : S.xA.1 ≠ S.xB.1 := by
    intro h
    exact Finset.disjoint_left.mp S.A_disjoint_B S.X_A_attachment.1
      ((Subtype.ext h) ▸ S.X_B_attachment.1)
  have hyAxB : S.yA.1 ≠ S.xB.1 := by
    intro h
    exact Finset.disjoint_left.mp S.A_disjoint_B S.Y_A_attachment.1
      ((Subtype.ext h) ▸ S.X_B_attachment.1)
  have hzAxB : S.zA.1 ≠ S.xB.1 := by
    intro h
    exact Finset.disjoint_left.mp S.A_disjoint_B S.Z_A_attachment.1
      ((Subtype.ext h) ▸ S.X_B_attachment.1)
  exact exists_ahtMixedTripleFan hthree
    (xBPrime_ne_xB S R) hxAxB hyAxB hzAxB
      (xBPrime_ne_xA S R) (xBPrime_ne_yA S R) (xBPrime_ne_zA S R)
      (fun h ↦ hneA.1 (Subtype.ext h))
      (fun h ↦ hneA.2.1 (Subtype.ext h))
      (fun h ↦ hneA.2.2 (Subtype.ext h))

/-- Every internal vertex of the first fan remains in `D'`.  The only
possible exits from the residual component are through `A`, the singleton
`x_B`, or `center`; target-minimality excludes `A`, the fan deletion
excludes `x_B`, and the prescribed centre neighbourhood excludes `center`.
-/
theorem firstFan_support_location
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent)
    (F : AHTMixedTripleFan G S.xB.1 R.xBPrime
      S.xA.1 S.yA.1 S.zA.1)
    (hBcard : S.bSet.card = 1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    ∀ w, w ∈ F.path.support →
      w ∈ R.carrier ∨ w ∈ ahtDeletedFinsetVal S.aSet := by
  have hAval : ahtDeletedFinsetVal S.aSet =
      {S.xA.1, S.yA.1, S.zA.1} := by simp [S.A_eq]
  obtain ⟨hxByB, hxBzB⟩ := S.b_attachments_eq_of_card_one hBcard
  have hxByBval : S.xB.1 = S.yB.1 := congrArg Subtype.val hxByB
  have hxBzBval : S.xB.1 = S.zB.1 := congrArg Subtype.val hxBzB
  have hzByBval : S.zB.1 = S.yB.1 := hxBzBval.symm.trans hxByBval
  have hBval : ahtDeletedFinsetVal S.bSet = {S.xB.1} := by
    simp [S.B_eq, hxByBval, hzByBval]
  have hrootStart : R.xBPrime ≠ F.start := by
    rcases F.start_target with h | h | h
    · intro heq
      exact xBPrime_ne_xA S R (heq.trans h)
    · intro heq
      exact xBPrime_ne_yA S R (heq.trans h)
    · intro heq
      exact xBPrime_ne_zA S R (heq.trans h)
  have hrootFinish : R.xBPrime ≠ F.finish := by
    rcases F.finish_target with h | h | h
    · intro heq
      exact xBPrime_ne_xA S R (heq.trans h)
    · intro heq
      exact xBPrime_ne_yA S R (heq.trans h)
    · intro heq
      exact xBPrime_ne_zA S R (heq.trans h)
  have endpoint_mem_A {w : V}
      (hw : w = F.start ∨ w = F.finish) :
      w ∈ ahtDeletedFinsetVal S.aSet := by
    rw [hAval]
    rcases hw with rfl | rfl
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using
        F.start_target
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using
        F.finish_target
  have interval_avoids_deletion
      {w : V} (hwPath : w ∈ F.path.support)
      (hwStart : w ≠ F.start) (hwFinish : w ≠ F.finish)
      (hcenterAvoid : center ∉ F.path.support) :
      ∃ r : G.Walk R.xBPrime w, r.IsPath ∧
        (∀ t, t ∈ r.support → t ∈ F.path.support) ∧
        ∀ t, t ∈ r.support →
          t ∉ ahtDeletedFinsetVal S.aSet ∪
            ahtDeletedFinsetVal S.bSet ∪ {center} := by
    obtain ⟨r, hr, hrSub, hrEnds⟩ := F.isPath.exists_internal_interval
      F.root_mem hwPath hrootStart hrootFinish hwStart hwFinish
    refine ⟨r, hr, hrSub, ?_⟩
    intro t htr htDelete
    rcases Finset.mem_union.mp htDelete with htAB | htCenter
    · rcases Finset.mem_union.mp htAB with htA | htB
      · have htTarget : t = S.xA.1 ∨ t = S.yA.1 ∨ t = S.zA.1 := by
          simpa only [hAval, Finset.mem_insert, Finset.mem_singleton] using htA
        rcases F.target_only_endpoints t (hrSub t htr) htTarget with h | h
        · exact (hrEnds t htr).1 h
        · exact (hrEnds t htr).2 h
      · have htxB : t = S.xB.1 := by simpa [hBval] using htB
        exact F.deleted_not_mem (htxB ▸ hrSub t htr)
    · have htc : t = center := by simpa using htCenter
      exact hcenterAvoid (htc ▸ hrSub t htr)
  have hcenterNotPath : center ∉ F.path.support := by
    intro hcPath
    have hcStart : center ≠ F.start := by
      intro h
      exact center_not_mem_ahtDeletedFinsetVal S.aSet
        (endpoint_mem_A (Or.inl h))
    have hcFinish : center ≠ F.finish := by
      intro h
      exact center_not_mem_ahtDeletedFinsetVal S.aSet
        (endpoint_mem_A (Or.inr h))
    obtain ⟨r, hr, hrSub, hrEnds⟩ := F.isPath.exists_internal_interval
      F.root_mem hcPath hrootStart hrootFinish hcStart hcFinish
    have hrNonNil : ¬r.Nil := by
      intro hnil
      exact xBPrime_ne_center S R hnil.eq
    have huSupport : r.penultimate ∈ r.dropLast.support := by
      rw [r.support_dropLast hrNonNil]
      exact r.penultimate_mem_dropLast_support hrNonNil
    have huD : r.penultimate ∈ R.carrier := by
      apply R.component.walk_end_mem r.dropLast R.xBPrime_mem
      intro t htDrop htDelete
      have htr : t ∈ r.support := by
        rw [r.support_dropLast hrNonNil] at htDrop
        exact List.mem_of_mem_dropLast htDrop
      rcases Finset.mem_union.mp htDelete with htAB | htCenter
      · rcases Finset.mem_union.mp htAB with htA | htB
        · rw [hAval] at htA
          have htTarget : t = S.xA.1 ∨ t = S.yA.1 ∨ t = S.zA.1 := by
            simpa only [Finset.mem_insert, Finset.mem_singleton] using htA
          rcases F.target_only_endpoints t (hrSub t htr) htTarget with h | h
          · exact (hrEnds t htr).1 h
          · exact (hrEnds t htr).2 h
        · have htxB : t = S.xB.1 := by simpa [hBval] using htB
          exact F.deleted_not_mem (htxB ▸ hrSub t htr)
      · have htc : t = center := by simpa using htCenter
        have hnd := hr.support_nodup
        rw [← r.support_dropLast_concat hrNonNil] at hnd
        exact (List.nodup_append.mp hnd).2.2 center
          (htc ▸ htDrop) center (by simp) rfl
    rcases hcenterNeighbors (r.adj_penultimate hrNonNil).symm with
      hux | huy | huz
    · exact Finset.disjoint_left.mp R.disjoint_xPart huD
        (hux ▸ val_mem_ahtDeletedFinsetVal.mpr S.x_mem_X)
    · exact Finset.disjoint_left.mp R.disjoint_yPart huD
        (huy ▸ val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
    · exact Finset.disjoint_left.mp R.disjoint_zPart huD
        (huz ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
  intro w hwPath
  by_cases hwStart : w = F.start
  · exact Or.inr (endpoint_mem_A (Or.inl hwStart))
  by_cases hwFinish : w = F.finish
  · exact Or.inr (endpoint_mem_A (Or.inr hwFinish))
  obtain ⟨r, -, -, hrAvoid⟩ := interval_avoids_deletion
    hwPath hwStart hwFinish hcenterNotPath
  exact Or.inl (R.component.walk_end_mem r R.xBPrime_mem hrAvoid)

/-- If the first mixed fan joins `y_A` to `z_A`, its component-confined
path closes through `z-center-y` to a wheel centred at `x_B`.  The
neighbours `y,z`, one vertex of `X`, and `x'_B` then force degree at least
four, contradicting almost-wheel-freeness. -/
theorem false_of_firstFan_yA_zA
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent)
    (F : AHTMixedTripleFan G S.xB.1 R.xBPrime
      S.xA.1 S.yA.1 S.zA.1)
    (halmost : AlmostWheelFree G)
    (hcy : G.Adj center y.1) (hcz : G.Adj center z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hs : F.start = S.yA.1) (ht : F.finish = S.zA.1)
    (hlocation : ∀ w, w ∈ F.path.support →
      w ∈ R.carrier ∨ w ∈ ahtDeletedFinsetVal S.aSet) : False := by
  have hneA := S.a_attachments_pairwise_ne_of_card_three hAcard
  obtain ⟨hxByB, hxBzB⟩ := S.b_attachments_eq_of_card_one hBcard
  have hyA : G.Adj y.1 S.yA.1 := S.adj_y_yA_of_yPart_card_one hy
  have hzA : G.Adj z.1 S.zA.1 := S.adj_z_zA_of_zPart_card_one hz
  have hyB : G.Adj y.1 S.xB.1 := by
    simpa [hxByB] using S.adj_y_yB_of_yPart_card_one hy
  have hzB : G.Adj z.1 S.xB.1 := by
    simpa [hxBzB] using S.adj_z_zB_of_zPart_card_one hz
  let p : G.Walk S.yA.1 S.zA.1 := F.path.copy hs ht
  have hp : p.IsPath := (Walk.isPath_copy F.path hs ht).2 F.isPath
  have hrootP : R.xBPrime ∈ p.support := by
    simpa only [p, Walk.support_copy] using F.root_mem
  have hxBP : S.xB.1 ∉ p.support := by
    simpa only [p, Walk.support_copy] using F.deleted_not_mem
  have support_location : ∀ w, w ∈ p.support →
      w ∈ R.carrier ∨ w ∈ ahtDeletedFinsetVal S.aSet := by
    intro w hw
    apply hlocation w
    simpa only [p, Walk.support_copy] using hw
  have hyNotP : y.1 ∉ p.support := by
    intro hyp
    rcases support_location y.1 hyp with hyD | hyAset
    · exact Finset.disjoint_left.mp R.disjoint_yPart hyD
        (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
    · have hYsep := disjoint_ahtDeletedFinsetVal S.Y_component.2.1
      rw [ahtDeletedFinsetVal_union] at hYsep
      exact Finset.disjoint_left.mp hYsep
        (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
        (Finset.mem_union_left _ hyAset)
  have hzNotP : z.1 ∉ p.support := by
    intro hzp
    rcases support_location z.1 hzp with hzD | hzAset
    · exact Finset.disjoint_left.mp R.disjoint_zPart hzD
        (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
    · have hZsep := disjoint_ahtDeletedFinsetVal S.Z_component.2.1
      rw [ahtDeletedFinsetVal_union] at hZsep
      exact Finset.disjoint_left.mp hZsep
        (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
        (Finset.mem_union_left _ hzAset)
  have hcenterNotP : center ∉ p.support := by
    intro hcp
    rcases support_location center hcp with hcD | hcA
    · exact Finset.disjoint_left.mp R.component.2.1 hcD
        (Finset.mem_union_right _ (by simp))
    · exact center_not_mem_ahtDeletedFinsetVal S.aSet hcA
  have hyz : y.1 ≠ z.1 := by
    intro h
    exact Finset.disjoint_left.mp
      (disjoint_ahtDeletedFinsetVal S.Y_disjoint_Z)
      (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
  have hyAy : S.yA.1 ≠ y.1 := hyA.ne.symm
  have hzAz : S.zA.1 ≠ z.1 := hzA.ne.symm
  have hyAz : S.yA.1 ≠ z.1 := by
    intro h
    have hZsep := disjoint_ahtDeletedFinsetVal S.Z_component.2.1
    rw [ahtDeletedFinsetVal_union] at hZsep
    exact Finset.disjoint_left.mp hZsep
      (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
      (Finset.mem_union_left _
        (h.symm ▸ val_mem_ahtDeletedFinsetVal.mpr S.Y_A_attachment.1))
  have hzAy : S.zA.1 ≠ y.1 := by
    intro h
    have hYsep := disjoint_ahtDeletedFinsetVal S.Y_component.2.1
    rw [ahtDeletedFinsetVal_union] at hYsep
    exact Finset.disjoint_left.mp hYsep
      (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
      (Finset.mem_union_left _
        (h.symm ▸ val_mem_ahtDeletedFinsetVal.mpr S.Z_A_attachment.1))
  let q : G.Walk S.zA.1 S.yA.1 :=
    (((hzA.symm.toWalk.concat hcz.symm).concat hcy).concat hyA)
  have hq : q.IsPath := by
    have h1 : hzA.symm.toWalk.IsPath := Walk.IsPath.of_adj hzA.symm
    have h2 := h1.concat (by
      simp [SimpleGraph.Adj.support_toWalk, S.zA.2, S.zA.2.symm,
        z.2, z.2.symm]) hcz.symm
    have h3 := h2.concat (by
      simp [Walk.support_concat, SimpleGraph.Adj.support_toWalk,
        hzAy, hzAy.symm, hyz, y.2]) hcy
    have hyAzA : S.yA.1 ≠ S.zA.1 := by
      intro h
      exact hneA.2.2 (Subtype.ext h)
    have h4 := h3.concat (by
      simp [Walk.support_concat, SimpleGraph.Adj.support_toWalk,
        hyAzA, hyAz, S.yA.2, hyAy]) hyA
    exact h4
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    rw [List.disjoint_left]
    intro w hwp hwq
    have hwpFull : w ∈ p.support := List.mem_of_mem_tail hwp
    have hwqCases : w = z.1 ∨ w = center ∨ w = y.1 ∨ w = S.yA.1 := by
      simpa [q] using hwq
    rcases hwqCases with rfl | rfl | rfl | rfl
    · exact hzNotP hwpFull
    · exact hcenterNotP hwpFull
    · exact hyNotP hwpFull
    · have hnd := hp.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hwp
  have hxBQ : S.xB.1 ∉ q.support := by
    have hYsep := disjoint_ahtDeletedFinsetVal S.Y_component.2.1
    have hZsep := disjoint_ahtDeletedFinsetVal S.Z_component.2.1
    rw [ahtDeletedFinsetVal_union] at hYsep hZsep
    have hxBy : S.xB.1 ≠ y.1 := by
      intro h
      exact Finset.disjoint_left.mp hYsep
        (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
        (Finset.mem_union_right _
          (h.symm ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1))
    have hxBz : S.xB.1 ≠ z.1 := by
      intro h
      exact Finset.disjoint_left.mp hZsep
        (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
        (Finset.mem_union_right _
          (h.symm ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1))
    have hxByA : S.xB.1 ≠ S.yA.1 := by
      intro h
      have hyAmem : S.yA ∈ S.bSet := by
        rw [show S.yA = S.xB from Subtype.ext h.symm]
        exact S.X_B_attachment.1
      exact Finset.disjoint_left.mp S.A_disjoint_B S.Y_A_attachment.1
        hyAmem
    have hxBzA : S.xB.1 ≠ S.zA.1 := by
      intro h
      have hzAmem : S.zA ∈ S.bSet := by
        rw [show S.zA = S.xB from Subtype.ext h.symm]
        exact S.X_B_attachment.1
      exact Finset.disjoint_left.mp S.A_disjoint_B S.Z_A_attachment.1
        hzAmem
    simp [q, hxBy, hxBz, hxByA, hxBzA, S.xB.2]
  have hwheel : HasWheelCenteredAt G S.xB.1 :=
    hasWheelCenteredAt_of_path_append p q hp hq hdisj
      (Or.inr (by simp [q])) hxBP hxBQ
      hyB.symm hzB.symm R.adj_xBPrime_xB.symm
      (Or.inr (by simp [q])) (Or.inr (by simp [q]))
      (Or.inl hrootP) hyz (xBPrime_ne_y S R).symm
        (xBPrime_ne_z S R).symm
  obtain ⟨x', hx'X, hx'xB⟩ := S.X_B_attachment.2.1
  have hx'Adj : G.Adj S.xB.1 x'.1 :=
    ((deleteVertex_adj (G := G)).mp hx'xB).symm
  have hfour : 4 ≤ G.degree S.xB.1 := by
    rw [← G.card_neighborFinset_eq_degree]
    let N : Finset V := {y.1, z.1, x'.1, R.xBPrime}
    have hNcard : N.card = 4 := by
      have hx'Y : x'.1 ≠ y.1 := by
        intro h
        exact Finset.disjoint_left.mp
          (disjoint_ahtDeletedFinsetVal S.X_disjoint_Y)
          (val_mem_ahtDeletedFinsetVal.mpr hx'X)
          (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
      have hx'Z : x'.1 ≠ z.1 := by
        intro h
        exact Finset.disjoint_left.mp
          (disjoint_ahtDeletedFinsetVal S.X_disjoint_Z)
          (val_mem_ahtDeletedFinsetVal.mpr hx'X)
          (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
      have hx'R : x'.1 ≠ R.xBPrime :=
        (xBPrime_ne_xPart S R
          (val_mem_ahtDeletedFinsetVal.mpr hx'X)).symm
      simp [N, hyz, hyz.symm, hx'Y, hx'Y.symm, hx'Z, hx'Z.symm,
        hx'R, hx'R.symm, xBPrime_ne_y S R,
        (xBPrime_ne_y S R).symm, xBPrime_ne_z S R,
        (xBPrime_ne_z S R).symm]
    rw [← hNcard]
    apply Finset.card_le_card
    intro w hw
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · simpa using hyB.symm
    · simpa using hzB.symm
    · simpa using hx'Adj
    · simpa using R.adj_xBPrime_xB.symm
  have hdegree := halmost.degree_eq_three_of_center hwheel
  omega

/-- The first endpoint branch with component confinement discharged from
the residual certificate. -/
theorem false_of_firstFan_yA_zA_auto
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent)
    (F : AHTMixedTripleFan G S.xB.1 R.xBPrime
      S.xA.1 S.yA.1 S.zA.1)
    (halmost : AlmostWheelFree G)
    (hcy : G.Adj center y.1) (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hs : F.start = S.yA.1) (ht : F.finish = S.zA.1) : False := by
  exact R.false_of_firstFan_yA_zA F halmost hcy hcz hAcard hBcard hy hz
    hs ht (R.firstFan_support_location F hBcard hcenterNeighbors)

theorem false_of_firstFan_yA_zA_unordered
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent)
    (F : AHTMixedTripleFan G S.xB.1 R.xBPrime
      S.xA.1 S.yA.1 S.zA.1)
    (halmost : AlmostWheelFree G)
    (hcy : G.Adj center y.1) (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hends : (F.start = S.yA.1 ∧ F.finish = S.zA.1) ∨
      (F.start = S.zA.1 ∧ F.finish = S.yA.1)) : False := by
  rcases hends with h | h
  · exact R.false_of_firstFan_yA_zA_auto F halmost hcy hcz
      hcenterNeighbors hAcard hBcard hy hz h.1 h.2
  · exact R.false_of_firstFan_yA_zA_auto F.reverse halmost hcy hcz
      hcenterNeighbors hAcard hBcard hy hz h.2 h.1

/-- In the remaining endpoint branch, the first fan is an `x_A`--`y_A`
path through `x'_B`; the second fan is a `center`--`x_A` path through an
`X`-neighbour `x'` of `x_B`.  Their component locations make the paths
internally disjoint, and closing through `y` gives the second source wheel
centred at `x_B`. -/
theorem false_of_firstFan_xA_yA_and_secondFan
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent)
    (F : AHTMixedTripleFan G S.xB.1 R.xBPrime
      S.xA.1 S.yA.1 S.zA.1)
    {xPrime : V} (hxPrime : xPrime ∈ ahtDeletedFinsetVal S.xPart)
    (hxPrimeAdj : G.Adj S.xB.1 xPrime)
    (Q : AHTMixedPairFan G S.xB.1 xPrime center S.xA.1)
    (halmost : AlmostWheelFree G)
    (hcy : G.Adj center y.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hFs : F.start = S.xA.1) (hFt : F.finish = S.yA.1)
    (hQs : Q.start = center) (hQt : Q.finish = S.xA.1) : False := by
  obtain ⟨hxByB, hxBzB⟩ := S.b_attachments_eq_of_card_one hBcard
  have hyA : G.Adj y.1 S.yA.1 := S.adj_y_yA_of_yPart_card_one hy
  have hyB : G.Adj S.xB.1 y.1 := by
    simpa [hxByB] using (S.adj_y_yB_of_yPart_card_one hy).symm
  have hzB : G.Adj S.xB.1 z.1 := by
    simpa [hxBzB] using (S.adj_z_zB_of_zPart_card_one hz).symm
  let p : G.Walk S.xA.1 S.yA.1 := F.path.copy hFs hFt
  let q : G.Walk center S.xA.1 := Q.path.copy hQs hQt
  have hp : p.IsPath := (Walk.isPath_copy F.path hFs hFt).2 F.isPath
  have hq : q.IsPath := (Walk.isPath_copy Q.path hQs hQt).2 Q.isPath
  have hFLocation := R.firstFan_support_location F hBcard hcenterNeighbors
  have hQLocation := S.mixedSecondFan_support_location hxPrime Q
  have pLocation : ∀ w, w ∈ p.support →
      w ∈ R.carrier ∨ w ∈ ahtDeletedFinsetVal S.aSet := by
    intro w hw
    apply hFLocation w
    simpa only [p, Walk.support_copy] using hw
  have qLocation : ∀ w, w ∈ q.support →
      w ∈ ahtDeletedFinsetVal S.xPart ∨
        w = center ∨ w = S.xA.1 := by
    intro w hw
    apply hQLocation w
    simpa only [q, Walk.support_copy] using hw
  have hyNotP : y.1 ∉ p.support := by
    intro hyp
    rcases pLocation y.1 hyp with hyD | hySep
    · exact Finset.disjoint_left.mp R.disjoint_yPart hyD
        (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
    · have hYsep := disjoint_ahtDeletedFinsetVal S.Y_component.2.1
      rw [ahtDeletedFinsetVal_union] at hYsep
      exact Finset.disjoint_left.mp hYsep
        (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
        (Finset.mem_union_left _ hySep)
  have hcenterNotP : center ∉ p.support := by
    intro hcp
    rcases pLocation center hcp with hcD | hcA
    · exact Finset.disjoint_left.mp R.component.2.1 hcD
        (Finset.mem_union_right _ (by simp))
    · exact center_not_mem_ahtDeletedFinsetVal S.aSet hcA
  have hxBNotP : S.xB.1 ∉ p.support := by
    simpa only [p, Walk.support_copy] using F.deleted_not_mem
  have hxBNotQ : S.xB.1 ∉ q.support := by
    simpa only [q, Walk.support_copy] using Q.deleted_not_mem
  let r : G.Walk S.xA.1 center := (p.concat hyA.symm).concat hcy.symm
  have hr : r.IsPath := by
    have h1 := hp.concat hyNotP hyA.symm
    have hcenterNotFirst : center ∉ (p.concat hyA.symm).support := by
      simp [hcenterNotP, y.2.symm]
    exact h1.concat hcenterNotFirst hcy.symm
  have hrootR : R.xBPrime ∈ r.support := by
    have hrootP : R.xBPrime ∈ p.support := by
      simpa only [p, Walk.support_copy] using F.root_mem
    simp [r, hrootP]
  have hyR : y.1 ∈ r.support := by simp [r]
  have hxPrimeQ : xPrime ∈ q.support := by
    simpa only [q, Walk.support_copy] using Q.root_mem
  have hxBNotR : S.xB.1 ∉ r.support := by
    have hxBy : S.xB.1 ≠ y.1 := hyB.ne
    have hxBc : S.xB.1 ≠ center := S.xB.2
    simp [r, hxBNotP, hxBy, hxBc]
  have hdisj : q.support.tail.Disjoint r.support.tail := by
    rw [List.disjoint_left]
    intro w hwq hwr
    have hwqFull : w ∈ q.support := List.mem_of_mem_tail hwq
    rcases qLocation w hwqFull with hwX | rfl | rfl
    · have hwrCases : w ∈ p.support ∨ w = y.1 ∨ w = center := by
        simpa [r] using List.mem_of_mem_tail hwr
      rcases hwrCases with hwp | hwy | hwc
      · rcases pLocation w hwp with hwD | hwA
        · exact Finset.disjoint_left.mp R.disjoint_xPart hwD hwX
        · have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
          rw [ahtDeletedFinsetVal_union] at hXsep
          exact Finset.disjoint_left.mp hXsep hwX
            (Finset.mem_union_left _ hwA)
      · have hXY := disjoint_ahtDeletedFinsetVal S.X_disjoint_Y
        exact Finset.disjoint_left.mp hXY hwX
          (hwy ▸ val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
      · exact center_not_mem_ahtDeletedFinsetVal S.xPart (hwc ▸ hwX)
    · have hnd := hq.support_nodup
      rw [← q.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hwq
    · have hnd := hr.support_nodup
      rw [← r.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hwr
  have hwheel : HasWheelCenteredAt G S.xB.1 :=
    hasWheelCenteredAt_of_path_append q r hq hr hdisj
      (Or.inr (by simp [r])) hxBNotQ hxBNotR
      hyB hxPrimeAdj R.adj_xBPrime_xB.symm
      (Or.inr hyR) (Or.inl hxPrimeQ) (Or.inr hrootR)
      (by
        intro h
        have hXY := disjoint_ahtDeletedFinsetVal S.X_disjoint_Y
        exact Finset.disjoint_left.mp hXY hxPrime
          (h.symm ▸ val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y))
      (xBPrime_ne_y S R).symm
      (xBPrime_ne_xPart S R hxPrime).symm
  have hfour : 4 ≤ G.degree S.xB.1 := by
    rw [← G.card_neighborFinset_eq_degree]
    let N : Finset V := {y.1, z.1, xPrime, R.xBPrime}
    have hyz : y.1 ≠ z.1 := by
      intro h
      exact Finset.disjoint_left.mp
        (disjoint_ahtDeletedFinsetVal S.Y_disjoint_Z)
        (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
    have hxY : xPrime ≠ y.1 := by
      intro h
      exact Finset.disjoint_left.mp
        (disjoint_ahtDeletedFinsetVal S.X_disjoint_Y) hxPrime
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
    have hxZ : xPrime ≠ z.1 := by
      intro h
      exact Finset.disjoint_left.mp
        (disjoint_ahtDeletedFinsetVal S.X_disjoint_Z) hxPrime
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
    have hxR : xPrime ≠ R.xBPrime :=
      (xBPrime_ne_xPart S R hxPrime).symm
    have hNcard : N.card = 4 := by
      simp [N, hyz, hyz.symm, hxY, hxY.symm, hxZ, hxZ.symm,
        hxR, hxR.symm, xBPrime_ne_y S R,
        (xBPrime_ne_y S R).symm, xBPrime_ne_z S R,
        (xBPrime_ne_z S R).symm]
    rw [← hNcard]
    apply Finset.card_le_card
    intro w hw
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · simpa using hyB
    · simpa using hzB
    · simpa using hxPrimeAdj
    · simpa using R.adj_xBPrime_xB.symm
  have hdegree := halmost.degree_eq_three_of_center hwheel
  omega

theorem false_of_firstFan_xA_yA_and_secondFan_unordered
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent)
    (F : AHTMixedTripleFan G S.xB.1 R.xBPrime
      S.xA.1 S.yA.1 S.zA.1)
    {xPrime : V} (hxPrime : xPrime ∈ ahtDeletedFinsetVal S.xPart)
    (hxPrimeAdj : G.Adj S.xB.1 xPrime)
    (Q : AHTMixedPairFan G S.xB.1 xPrime center S.xA.1)
    (halmost : AlmostWheelFree G) (hcy : G.Adj center y.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hFends : (F.start = S.xA.1 ∧ F.finish = S.yA.1) ∨
      (F.start = S.yA.1 ∧ F.finish = S.xA.1)) : False := by
  rcases Q.endpoints with hQ | hQ
  · rcases hFends with hF | hF
    · exact R.false_of_firstFan_xA_yA_and_secondFan F hxPrime
        hxPrimeAdj Q halmost hcy hcenterNeighbors hBcard hy hz
        hF.1 hF.2 hQ.1 hQ.2
    · exact R.false_of_firstFan_xA_yA_and_secondFan F.reverse hxPrime
        hxPrimeAdj Q halmost hcy hcenterNeighbors hBcard hy hz
        hF.2 hF.1 hQ.1 hQ.2
  · rcases hFends with hF | hF
    · exact R.false_of_firstFan_xA_yA_and_secondFan F hxPrime
        hxPrimeAdj Q.reverse halmost hcy hcenterNeighbors hBcard hy hz
        hF.1 hF.2 hQ.2 hQ.1
    · exact R.false_of_firstFan_xA_yA_and_secondFan F.reverse hxPrime
        hxPrimeAdj Q.reverse halmost hcy hcenterNeighbors hBcard hy hz
        hF.2 hF.1 hQ.2 hQ.1

/-- The `x_A`--`z_A` endpoint pair is the preceding branch after swapping
the last two terminal labels. -/
theorem false_of_firstFan_xA_zA_and_secondFan_unordered
    {center : V} {x y z : {v : V // v ≠ center}}
    {S : WatkinsMesnerSplitter (deleteVertex G center) x y z}
    (R : S.MixedResidualComponent)
    (F : AHTMixedTripleFan G S.xB.1 R.xBPrime
      S.xA.1 S.yA.1 S.zA.1)
    {xPrime : V} (hxPrime : xPrime ∈ ahtDeletedFinsetVal S.xPart)
    (hxPrimeAdj : G.Adj S.xB.1 xPrime)
    (Q : AHTMixedPairFan G S.xB.1 xPrime center S.xA.1)
    (halmost : AlmostWheelFree G) (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hFends : (F.start = S.xA.1 ∧ F.finish = S.zA.1) ∨
      (F.start = S.zA.1 ∧ F.finish = S.xA.1)) : False := by
  have hcenterNeighbors' : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = z.1 ∨ q = y.1 := by
    intro q hq
    rcases hcenterNeighbors hq with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  exact R.swapLast.false_of_firstFan_xA_yA_and_secondFan_unordered
    F.swapLastTargets hxPrime hxPrimeAdj Q halmost hcz hcenterNeighbors'
      hBcard hz hy hFends

end WatkinsMesnerSplitter.MixedResidualComponent

namespace WatkinsMesnerSplitter

/-- Support-aware version of the elementary edge-boundary crossing lemma.
Both ends of the crossing edge are retained on the original walk. -/
theorem _root_.SimpleGraph.Walk.exists_boundary_edge_on_support_duplicate
    {a b : V} (p : G.Walk a b) (C : Finset V)
    (ha : a ∈ C) (hb : b ∉ C) :
    ∃ u ∈ C, ∃ v ∉ C,
      u ∈ p.support ∧ v ∈ p.support ∧ G.Adj u v := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons a c b hac p ih =>
      by_cases hc : c ∈ C
      · obtain ⟨u, huC, v, hvC, hup, hvp, huv⟩ := ih hc hb
        exact ⟨u, huC, v, hvC, by simp [hup], by simp [hvp], huv⟩
      · exact ⟨a, ha, c, hc, by simp, by simp, hac⟩

/-- Choose the source's `x' ∈ X` adjacent to `x_B` and take the second
target-minimal fan in `G-x_B` from that root to `{center,x_A}`. -/
theorem exists_mixedSecondFan
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) :
    ∃ xPrime : V,
      xPrime ∈ ahtDeletedFinsetVal S.xPart ∧
      G.Adj S.xB.1 xPrime ∧
      Nonempty (AHTMixedPairFan G S.xB.1 xPrime center S.xA.1) := by
  obtain ⟨x', hx'X, hx'xB⟩ := S.X_B_attachment.2.1
  have hx'Xval : x'.1 ∈ ahtDeletedFinsetVal S.xPart :=
    val_mem_ahtDeletedFinsetVal.mpr hx'X
  have hx'xBval : G.Adj S.xB.1 x'.1 :=
    ((deleteVertex_adj (G := G)).mp hx'xB).symm
  have hx'neB : x'.1 ≠ S.xB.1 := by
    intro h
    have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
    rw [ahtDeletedFinsetVal_union] at hXsep
    exact Finset.disjoint_left.mp hXsep hx'Xval
      (Finset.mem_union_right _
        (h.symm ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1))
  have hx'neA : x'.1 ≠ S.xA.1 := by
    intro h
    have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
    rw [ahtDeletedFinsetVal_union] at hXsep
    exact Finset.disjoint_left.mp hXsep hx'Xval
      (Finset.mem_union_left _
        (h.symm ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_A_attachment.1))
  refine ⟨x'.1, hx'Xval, hx'xBval, ?_⟩
  exact exists_ahtMixedPairFan hthree
    hx'neB S.xB.2.symm (by
      intro h
      have hxAmem : S.xA ∈ S.bSet := by
        rw [show S.xA = S.xB from Subtype.ext h]
        exact S.X_B_attachment.1
      exact Finset.disjoint_left.mp S.A_disjoint_B S.X_A_attachment.1
        hxAmem)
    x'.2 hx'neA S.xA.2.symm

/-- The complete fan/wheel contradiction once the mixed residual component
`D'` has been selected.  The three possible unordered endpoint pairs are
exactly the direct `y_Az_A` wheel and the two second-fan branches. -/
theorem MixedResidualComponent.false_of_mixedResidualComponent
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (R : S.MixedResidualComponent)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hcy : G.Adj center y.1) (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1) : False := by
  obtain ⟨F⟩ := R.exists_firstFan hthree hAcard
  rcases F.endpoint_pair_cases with hXY | hYX | hXZ | hZX | hYZ | hZY
  · obtain ⟨xPrime, hxPrime, hxPrimeAdj, Q⟩ :=
      S.exists_mixedSecondFan hthree
    obtain ⟨Q⟩ := Q
    exact R.false_of_firstFan_xA_yA_and_secondFan_unordered F hxPrime
      hxPrimeAdj Q halmost hcy hcenterNeighbors hBcard hy hz (Or.inl hXY)
  · obtain ⟨xPrime, hxPrime, hxPrimeAdj, Q⟩ :=
      S.exists_mixedSecondFan hthree
    obtain ⟨Q⟩ := Q
    exact R.false_of_firstFan_xA_yA_and_secondFan_unordered F hxPrime
      hxPrimeAdj Q halmost hcy hcenterNeighbors hBcard hy hz (Or.inr hYX)
  · obtain ⟨xPrime, hxPrime, hxPrimeAdj, Q⟩ :=
      S.exists_mixedSecondFan hthree
    obtain ⟨Q⟩ := Q
    exact R.false_of_firstFan_xA_zA_and_secondFan_unordered F hxPrime
      hxPrimeAdj Q halmost hcz hcenterNeighbors hBcard hy hz (Or.inl hXZ)
  · obtain ⟨xPrime, hxPrime, hxPrimeAdj, Q⟩ :=
      S.exists_mixedSecondFan hthree
    obtain ⟨Q⟩ := Q
    exact R.false_of_firstFan_xA_zA_and_secondFan_unordered F hxPrime
      hxPrimeAdj Q halmost hcz hcenterNeighbors hBcard hy hz (Or.inr hZX)
  · exact R.false_of_firstFan_yA_zA_unordered F halmost hcy hcz
      hcenterNeighbors hAcard hBcard hy hz (Or.inl hYZ)
  · exact R.false_of_firstFan_yA_zA_unordered F halmost hcy hcz
      hcenterNeighbors hAcard hBcard hy hz (Or.inr hZY)

/-- The second fan stays in `X` except for its two target endpoints.  If an
internal subpath first leaves `X`, component maximality puts the exit in
`A ∪ B ∪ {center}`; the unique-attachment fields then identify it as
`x_A`, `x_B`, or `center`, contradicting target-minimality/deletion. -/
theorem mixedSecondFan_support_location_duplicate
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    {xPrime : V} (hxPrime : xPrime ∈ ahtDeletedFinsetVal S.xPart)
    (F : AHTMixedPairFan G S.xB.1 xPrime center S.xA.1) :
    ∀ w, w ∈ F.path.support →
      w ∈ ahtDeletedFinsetVal S.xPart ∨
        w = center ∨ w = S.xA.1 := by
  have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
  rw [ahtDeletedFinsetVal_union] at hXsep
  have hxPrimeCenter : xPrime ≠ center := by
    intro h
    exact center_not_mem_ahtDeletedFinsetVal S.xPart (h ▸ hxPrime)
  have hxPrimeA : xPrime ≠ S.xA.1 := by
    intro h
    exact Finset.disjoint_left.mp hXsep hxPrime
      (Finset.mem_union_left _
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_A_attachment.1))
  have hxPrimeStart : xPrime ≠ F.start := by
    rcases F.start_target with h | h
    · exact fun h' ↦ hxPrimeCenter (h'.trans h)
    · exact fun h' ↦ hxPrimeA (h'.trans h)
  have hxPrimeFinish : xPrime ≠ F.finish := by
    rcases F.finish_target with h | h
    · exact fun h' ↦ hxPrimeCenter (h'.trans h)
    · exact fun h' ↦ hxPrimeA (h'.trans h)
  have hXambient : IsComponentAfterDeleting G
      (ahtDeletedFinsetVal S.aSet ∪
        ahtDeletedFinsetVal S.bSet ∪ {center})
      (ahtDeletedFinsetVal S.xPart) := by
    simpa using S.X_component.ambient_of_deleteVertex (G := G)
  intro w hwPath
  by_cases hwStart : w = F.start
  · rcases F.start_target with h | h
    · exact Or.inr (Or.inl (hwStart.trans h))
    · exact Or.inr (Or.inr (hwStart.trans h))
  by_cases hwFinish : w = F.finish
  · rcases F.finish_target with h | h
    · exact Or.inr (Or.inl (hwFinish.trans h))
    · exact Or.inr (Or.inr (hwFinish.trans h))
  by_cases hwX : w ∈ ahtDeletedFinsetVal S.xPart
  · exact Or.inl hwX
  obtain ⟨r, -, hrSub, hrEnds⟩ := F.isPath.exists_internal_interval
    F.root_mem hwPath hxPrimeStart hxPrimeFinish hwStart hwFinish
  obtain ⟨u, huX, v, hvX, hur, hvr, huv⟩ :=
    r.exists_boundary_edge_on_support (ahtDeletedFinsetVal S.xPart)
      hxPrime hwX
  have hvDelete : v ∈ ahtDeletedFinsetVal S.aSet ∪
      ahtDeletedFinsetVal S.bSet ∪ {center} := by
    by_contra hv
    exact hvX (hXambient.2.2.2 u huX v hv huv)
  rcases Finset.mem_union.mp hvDelete with hvAB | hvCenter
  · rcases Finset.mem_union.mp hvAB with hvA | hvB
    · obtain ⟨u', hu'X, hu'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal huX
      obtain ⟨v', hv'A, hv'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hvA
      have huvDel : (deleteVertex G center).Adj u' v' :=
        (deleteVertex_adj (G := G)).mpr (by
          simpa [hu'val, hv'val] using huv)
      have hvEq' := S.X_A_attachment.2.2
        u' hu'X v' hv'A huvDel
      have hvEq : v = S.xA.1 :=
        hv'val.symm.trans (congrArg Subtype.val hvEq')
      rcases F.target_only_endpoints v (hrSub v hvr)
          (Or.inr hvEq) with h | h
      · exact False.elim ((hrEnds v hvr).1 h)
      · exact False.elim ((hrEnds v hvr).2 h)
    · obtain ⟨u', hu'X, hu'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal huX
      obtain ⟨v', hv'B, hv'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hvB
      have huvDel : (deleteVertex G center).Adj u' v' :=
        (deleteVertex_adj (G := G)).mpr (by
          simpa [hu'val, hv'val] using huv)
      have hvEq' := S.X_B_attachment.2.2
        u' hu'X v' hv'B huvDel
      have hvEq : v = S.xB.1 :=
        hv'val.symm.trans (congrArg Subtype.val hvEq')
      exact False.elim (F.deleted_not_mem (hvEq ▸ hrSub v hvr))
  · have hvEq : v = center := by simpa using hvCenter
    rcases F.target_only_endpoints v (hrSub v hvr)
        (Or.inl hvEq) with h | h
    · exact False.elim ((hrEnds v hvr).1 h)
    · exact False.elim ((hrEnds v hvr).2 h)

end WatkinsMesnerSplitter

namespace WatkinsMesnerSplitter

/-- Source Claim (8), normalized mixed branch `|A|=3, |B|=1`.
Claim (5) bounds the `A`-side component union, the local degree argument
selects `D'`, and the two staged fans give the forbidden wheel. -/
theorem false_of_xPart_twinPair_mixed_left_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) : False := by
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hcard : S.ambientLeftCarrier.card ≤ 1 :=
    S.ambientLeftCarrier_card_le_one_of_xTwinPair_below
      hthree halmost hno ih hcx hcy hcz hAcard hp hq hpq
  obtain ⟨R⟩ := S.exists_mixedResidualComponent_of_leftCarrier_card_le_one
    hthree htri hcenterNeighbors hAcard hBcard hy hz hcard
  exact R.false_of_mixedResidualComponent S hthree halmost hcy hcz
    hcenterNeighbors hAcard hBcard hy hz

/-- The opposite mixed orientation, obtained by the literal splitter-side
involution.  Terminal components and the ambient twin pair are unchanged. -/
theorem false_of_xPart_twinPair_mixed_right_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 1) (hBcard : S.bSet.card = 3)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) : False := by
  have hAcard' : S.swapSides.aSet.card = 3 := by
    simpa [swapSides] using hBcard
  have hBcard' : S.swapSides.bSet.card = 1 := by
    simpa [swapSides] using hAcard
  exact S.swapSides.false_of_xPart_twinPair_mixed_left_below
    hthree halmost hno ih hcx hcy hcz hcenterNeighbors hAcard' hBcard'
      (by simpa [swapSides] using hy) (by simpa [swapSides] using hz)
      (by simpa [swapSides] using hp) (by simpa [swapSides] using hq) hpq

/-- Claim (8) for either mixed splitter-side cardinality orientation. -/
theorem false_of_xPart_twinPair_mixed_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q)
    (hmixed : (S.aSet.card = 3 ∧ S.bSet.card = 1) ∨
      (S.aSet.card = 1 ∧ S.bSet.card = 3)) : False := by
  rcases hmixed with h | h
  · exact S.false_of_xPart_twinPair_mixed_left_below hthree halmost
      hno ih hcx hcy hcz hcenterNeighbors h.1 h.2 hy hz hp hq hpq
  · exact S.false_of_xPart_twinPair_mixed_right_below hthree halmost
      hno ih hcx hcy hcz hcenterNeighbors h.1 h.2 hy hz hp hq hpq

/-! ## The final all-singleton, both-triples replacement -/

/-- In the final branch, the union `C_A ∪ A` has external boundary exactly
among the three singleton terminals.  A residual deleted component is
classified by condition (vii): an `A`-boundary component was already put
in `C_A`, while a `B`-boundary component cannot meet `A`. -/
theorem finalLeftVerts_externalBoundary
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (htri : AHTTriangleFree G)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1) :
    HasExternalBoundaryIn G S.finalLeftVerts ({x.1, y.1, z.1} : Finset V) := by
  classical
  have hnoAB := S.no_edges_between_sides_of_both_triples_singletons
    htri hAcard hBcard hx hy hz
  intro p hpF q hpq hqF
  change p ∈ S.ambientLeftCarrier ∪
    ahtDeletedFinsetVal S.aSet at hpF
  rcases Finset.mem_union.mp hpF with hpC | hpA
  · have hqC : q ∉ S.ambientLeftCarrier := by
      intro h
      exact hqF (Finset.mem_union_left _ h)
    have hqA := S.ambientLeftCarrier_externalBoundary p hpC q hpq hqC
    exact False.elim (hqF (Finset.mem_union_right _ hqA))
  · obtain ⟨p', hp'A, hp'val⟩ :=
      exists_subtype_of_mem_ahtDeletedFinsetVal hpA
    have hpNe := S.aSet_val_ne_terminals hp'A
    by_cases hqA : q ∈ ahtDeletedFinsetVal S.aSet
    · exact False.elim (hqF (Finset.mem_union_right _ hqA))
    by_cases hqB : q ∈ ahtDeletedFinsetVal S.bSet
    · obtain ⟨q', hq'B, hq'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hqB
      exact False.elim (hnoAB p' hp'A q' hq'B (by
        simpa [hp'val, hq'val] using hpq))
    by_cases hqc : q = center
    · have hcp : G.Adj center p'.1 := by
        simpa [hqc, hp'val] using hpq.symm
      rcases hcenterNeighbors hcp with h | h | h
      · exact False.elim (hpNe.1 h)
      · exact False.elim (hpNe.2.1 h)
      · exact False.elim (hpNe.2.2 h)
    let q' : {v : V // v ≠ center} := ⟨q, hqc⟩
    have hq'A : q' ∉ S.aSet := by
      intro h
      exact hqA (val_mem_ahtDeletedFinsetVal.mpr h)
    have hq'B : q' ∉ S.bSet := by
      intro h
      exact hqB (val_mem_ahtDeletedFinsetVal.mpr h)
    by_cases hqX : q' ∈ S.xPart
    · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hx
      have hqt : q' = t := by simpa [ht] using hqX
      have hxt : x = t := by simpa [ht] using S.x_mem_X
      have hqx : q = x.1 := congrArg Subtype.val (hqt.trans hxt.symm)
      simp [hqx]
    by_cases hqY : q' ∈ S.yPart
    · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hy
      have hqt : q' = t := by simpa [ht] using hqY
      have hyt : y = t := by simpa [ht] using S.y_mem_Y
      have hqy : q = y.1 := congrArg Subtype.val (hqt.trans hyt.symm)
      simp [hqy]
    by_cases hqZ : q' ∈ S.zPart
    · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hz
      have hqt : q' = t := by simpa [ht] using hqZ
      have hzt : z = t := by simpa [ht] using S.z_mem_Z
      have hqz : q = z.1 := congrArg Subtype.val (hqt.trans hzt.symm)
      simp [hqz]
    let K : Finset {v : V // v ≠ center} := S.aSet ∪ S.bSet
    have hqK : q' ∉ (K : Set {v : V // v ≠ center}) := by
      simpa only [K, Finset.mem_coe, Finset.mem_union, not_or] using
        And.intro hq'A hq'B
    let C : (deleteVertex G center).ComponentCompl (K : Set _) :=
      (deleteVertex G center).componentComplMk hqK
    let D : Finset {v : V // v ≠ center} := componentCarrier K C
    have hD : IsComponentAfterDeleting (deleteVertex G center) K D :=
      isComponentAfterDeleting_componentCarrier K C
    have hqD : q' ∈ D := by
      change q' ∈ componentCarrier K C
      rw [mem_componentCarrier]
      exact ⟨hqK, rfl⟩
    have hDX : Disjoint D S.xPart := by
      apply Finset.disjoint_left.mpr
      intro w hwD hwX
      exact hqX (S.X_component.mem_of_shared hD hwX hwD hqD)
    have hDY : Disjoint D S.yPart := by
      apply Finset.disjoint_left.mpr
      intro w hwD hwY
      exact hqY (S.Y_component.mem_of_shared hD hwY hwD hqD)
    have hDZ : Disjoint D S.zPart := by
      apply Finset.disjoint_left.mpr
      intro w hwD hwZ
      exact hqZ (S.Z_component.mem_of_shared hD hwZ hwD hqD)
    have hnoCenter := S.no_center_adj_of_disjoint_terminalParts
      hcenterNeighbors hDX hDY hDZ
    rcases S.ambient_component_boundary_left_or_right hthree hAcard hBcard
        hD hnoCenter with hleft | hright
    · have hqLeft : q ∈ S.ambientLeftCarrier :=
        S.mem_ambientLeftCarrier_of_component hD hnoCenter hleft
          (val_mem_ahtDeletedFinsetVal.mpr hqD)
      exact False.elim (hqF (Finset.mem_union_left _ hqLeft))
    · have hDambient := hD.ambient_of_deleteVertex (G := G)
      have hpD : p ∉ ahtDeletedFinsetVal D := by
        intro h
        have hpK : p ∈ ahtDeletedFinsetVal K := by
          simpa only [K, ahtDeletedFinsetVal_union] using
            (Finset.mem_union_left (ahtDeletedFinsetVal S.bSet) hpA)
        exact Finset.disjoint_left.mp hDambient.2.1 h
          (Finset.mem_union_left _ hpK)
      have hpB : p ∈ ahtDeletedFinsetVal S.bSet :=
        hright q (val_mem_ahtDeletedFinsetVal.mpr hqD) p hpq.symm hpD
      exact False.elim (Finset.disjoint_left.mp
        (disjoint_ahtDeletedFinsetVal S.A_disjoint_B) hpA hpB)

/-- The retained `A` side with boundary `x,y,z` as the literal
three-fragment consumed by Lemma 6.4. -/
noncomputable def finalLeftFragment
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (htri : AHTTriangleFree G)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hxy : x.1 ≠ y.1) (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1) : AHTThreeFragment G where
  verts := S.finalLeftVerts
  a := x.1
  b := y.1
  c := z.1
  ab := hxy
  ac := hxz
  bc := hyz
  boundary_disjoint :=
    S.finalLeftVerts_disjoint_terminals hcx hcy hcz
  nonempty := S.finalLeftVerts_nonempty
  outside_nonempty :=
    ⟨center, S.center_mem_complement_finalLeftVerts_terminals⟩
  boundary_exact := by
    have hboundary := S.finalLeftVerts_externalBoundary hthree htri
      hcenterNeighbors hAcard hBcard hx hy hz
    obtain ⟨hxMeet, hyMeet, hzMeet⟩ :=
      S.terminals_meet_finalLeftVerts hx hy hz
    intro q hq
    constructor
    · rintro ⟨p, hp, hqp⟩
      have hmem := hboundary p hp q hqp.symm hq
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    · intro hmem
      rcases hmem with rfl | rfl | rfl
      · exact hxMeet
      · exact hyMeet
      · exact hzMeet

/-- Each singleton terminal has exactly one possible neighbour in the
retained side, namely its `A` attachment.  A neighbour in a component of
`C_A` would put that terminal in a centre-free component, contradicting its
edge to `center`. -/
theorem finalLeft_insideNeighbor_subsets
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1) :
    G.neighborFinset x.1 ∩ S.finalLeftVerts ⊆ {S.xA.1} ∧
      G.neighborFinset y.1 ∩ S.finalLeftVerts ⊆ {S.yA.1} ∧
      G.neighborFinset z.1 ∩ S.finalLeftVerts ⊆ {S.zA.1} := by
  classical
  have one
      (terminal : {v : V // v ≠ center})
      (part : Finset {v : V // v ≠ center})
      (hpart : IsComponentAfterDeleting (deleteVertex G center)
        (S.aSet ∪ S.bSet) part)
      (ht : terminal ∈ part) (hct : G.Adj center terminal.1)
      (attachment : {v : V // v ≠ center})
      (ha : attachment ∈ S.aSet)
      (hunique : ∀ w ∈ part, ∀ a ∈ S.aSet,
        (deleteVertex G center).Adj w a → a = attachment) :
      G.neighborFinset terminal.1 ∩ S.finalLeftVerts ⊆ {attachment.1} := by
    intro q hq
    have htq : G.Adj terminal.1 q := by
      simpa using (Finset.mem_inter.mp hq).1
    have hqF := (Finset.mem_inter.mp hq).2
    change q ∈ S.ambientLeftCarrier ∪
      ahtDeletedFinsetVal S.aSet at hqF
    rcases Finset.mem_union.mp hqF with hqC | hqA
    · obtain ⟨C, hCfamily, hqCarrier⟩ := Finset.mem_biUnion.mp hqC
      obtain ⟨D, hD, hnoCenter, rfl, -⟩ :=
        (S.mem_ambientLeftComponents_iff C).mp hCfamily
      obtain ⟨q', hq'D, hq'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hqCarrier
      have htSep : terminal ∉ S.aSet ∪ S.bSet := by
        intro h
        exact Finset.disjoint_left.mp hpart.2.1 ht h
      have hdel : (deleteVertex G center).Adj q' terminal :=
        (deleteVertex_adj (G := G)).mpr (by
          simpa [hq'val] using htq.symm)
      have htD := hD.2.2.2 q' hq'D terminal htSep hdel
      exact False.elim (hnoCenter terminal.1
        (val_mem_ahtDeletedFinsetVal.mpr htD) hct.symm)
    · obtain ⟨q', hq'A, hq'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hqA
      have hdel : (deleteVertex G center).Adj terminal q' :=
        (deleteVertex_adj (G := G)).mpr (by simpa [hq'val] using htq)
      have heq := hunique terminal ht q' hq'A hdel
      exact Finset.mem_singleton.mpr
        (hq'val.symm.trans (congrArg Subtype.val heq))
  exact ⟨one x S.xPart S.X_component S.x_mem_X hcx S.xA
      S.X_A_attachment.1 S.X_A_attachment.2.2,
    one y S.yPart S.Y_component S.y_mem_Y hcy S.yA
      S.Y_A_attachment.1 S.Y_A_attachment.2.2,
    one z S.zPart S.Z_component S.z_mem_Z hcz S.zA
      S.Z_A_attachment.1 S.Z_A_attachment.2.2⟩

/-- No optional fresh boundary pin occurs in the final replacement: each
terminal sees at most its single `A` attachment in the retained side. -/
theorem finalLeftFragment_not_needsFreshPin
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (htri : AHTTriangleFree G)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hxy : x.1 ≠ y.1) (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1) (i : Fin 3) :
    ¬(S.finalLeftFragment hthree htri hcx hcy hcz hxy hxz hyz
      hcenterNeighbors hAcard hBcard hx hy hz).NeedsFreshPin i := by
  let F := S.finalLeftFragment hthree htri hcx hcy hcz hxy hxz hyz
    hcenterNeighbors hAcard hBcard hx hy hz
  have hsubs := S.finalLeft_insideNeighbor_subsets hcx hcy hcz
  have hsub : F.insideNeighborFinset i ⊆
      {![S.xA.1, S.yA.1, S.zA.1] i} := by
    fin_cases i
    · change G.neighborFinset x.1 ∩ S.finalLeftVerts ⊆ {S.xA.1}
      exact hsubs.1
    · change G.neighborFinset y.1 ∩ S.finalLeftVerts ⊆ {S.yA.1}
      exact hsubs.2.1
    · change G.neighborFinset z.1 ∩ S.finalLeftVerts ⊆ {S.zA.1}
      exact hsubs.2.2
  intro hneeds
  have hcard := Finset.card_le_card hsub
  have hle : (F.insideNeighborFinset i).card ≤ 1 := by
    simpa using hcard
  exact (by
    change 2 ≤ (F.insideNeighborFinset i).card at hneeds
    omega)

/-- The opposite splitter triple together with `center` gives four
exterior vertices for the final retained `A` side. -/
theorem four_le_complement_finalLeftVerts_terminals
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hBcard : S.bSet.card = 3) :
    4 ≤ (Finset.univ \
      (S.finalLeftVerts ∪ ({x.1, y.1, z.1} : Finset V))).card := by
  classical
  let B : Finset V := ahtDeletedFinsetVal S.bSet
  let T : Finset V := B ∪ {center}
  have hBcenter : Disjoint B ({center} : Finset V) := by
    apply Finset.disjoint_right.mpr
    intro r hrCenter hrB
    have hrc : r = center := by simpa using hrCenter
    change r ∈ ahtDeletedFinsetVal S.bSet at hrB
    exact center_not_mem_ahtDeletedFinsetVal S.bSet (hrc ▸ hrB)
  have hTcard : T.card = 4 := by
    change (B ∪ {center}).card = 4
    rw [Finset.card_union_of_disjoint hBcenter]
    simpa [B] using hBcard
  have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
  have hYsep := disjoint_ahtDeletedFinsetVal S.Y_component.2.1
  have hZsep := disjoint_ahtDeletedFinsetVal S.Z_component.2.1
  rw [ahtDeletedFinsetVal_union] at hXsep hYsep hZsep
  have hTsub : T ⊆ Finset.univ \
      (S.finalLeftVerts ∪ ({x.1, y.1, z.1} : Finset V)) := by
    intro r hrT
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, ?_⟩
    intro hrBad
    rcases Finset.mem_union.mp hrBad with hrLeft | hrTerminal
    · change r ∈ S.ambientLeftCarrier ∪
        ahtDeletedFinsetVal S.aSet at hrLeft
      rcases Finset.mem_union.mp hrT with hrB | hrCenter
      · rcases Finset.mem_union.mp hrLeft with hrCarrier | hrA
        · exact Finset.disjoint_left.mp
            S.ambientLeftCarrier_disjoint_right hrCarrier hrB
        · exact Finset.disjoint_left.mp
            (disjoint_ahtDeletedFinsetVal S.A_disjoint_B) hrA hrB
      · have hrc : r = center := by simpa using hrCenter
        subst r
        rcases Finset.mem_union.mp hrLeft with hrCarrier | hrA
        · exact S.center_not_mem_ambientLeftCarrier hrCarrier
        · exact center_not_mem_ahtDeletedFinsetVal S.aSet hrA
    · rcases Finset.mem_union.mp hrT with hrB | hrCenter
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hrTerminal
        rcases hrTerminal with rfl | rfl | rfl
        · exact Finset.disjoint_left.mp hXsep
            (val_mem_ahtDeletedFinsetVal.mpr S.x_mem_X)
            (Finset.mem_union_right _ hrB)
        · exact Finset.disjoint_left.mp hYsep
            (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
            (Finset.mem_union_right _ hrB)
        · exact Finset.disjoint_left.mp hZsep
            (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
            (Finset.mem_union_right _ hrB)
      · have hrc : r = center := by simpa using hrCenter
        subst r
        simp only [Finset.mem_insert, Finset.mem_singleton] at hrTerminal
        rcases hrTerminal with h | h | h
        · exact x.2 h.symm
        · exact y.2 h.symm
        · exact z.2 h.symm
  rw [← hTcard]
  exact Finset.card_le_card hTsub

end WatkinsMesnerSplitter

namespace AHTThreeFragment

/-- Sharpen the general six-vertex size comparison when no optional fresh
pin is present.  The replacement then adds only the deliberate double-pin
pair, so three exterior vertices already make it strictly smaller. -/
theorem replacement_card_lt_of_no_fresh_of_three_le_outside
    (F : AHTThreeFragment G)
    (hfresh : ∀ i : Fin 3, ¬F.NeedsFreshPin i)
    (hout : 3 ≤
      (Finset.univ \ (F.verts ∪ ({F.a, F.b, F.c} : Finset V))).card) :
    Fintype.card (F.PreparedVertex ⊕ Fin 2) < Fintype.card V := by
  let B : Finset V := F.verts ∪ ({F.a, F.b, F.c} : Finset V)
  have hboundary : ({F.a, F.b, F.c} : Finset V).card = 3 := by
    simp [F.ab, F.ac, F.bc]
  have hbase : Fintype.card F.BaseVertex = F.verts.card + 3 := by
    rw [Fintype.card_coe, Finset.card_union_of_disjoint F.boundary_disjoint,
      hboundary]
  have hfreshCard : Fintype.card F.FreshPin = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun i ↦ hfresh i.1 i.2⟩
  have hsplit :
      (Finset.univ \ B).card + B.card = Fintype.card V := by
    simpa [Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  have hBcard : B.card = F.verts.card + 3 := by
    simpa [B, Fintype.card_coe] using hbase
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [hbase, hfreshCard]
  rw [hBcard] at hsplit
  change 3 ≤ (Finset.univ \ B).card at hout
  omega

/-- A two-pair certificate in the replacement leaves an ambient twin pair
inside any non-singleton retained fragment.  The non-pin case lifts
directly; the pin case would force the fragment to have cardinality one. -/
theorem exists_ambient_twinPair_of_replacement_twoPairs_of_two_le
    (F : AHTThreeFragment G)
    (T : TwoDisjointDegreeThreeFalseTwinPairs F.replacementGraph)
    (hthree : IsThreeConnected F.replacementGraph)
    (htwo : 2 ≤ F.verts.card) :
    ∃ p ∈ F.verts, ∃ q ∈ F.verts, AHTTwinPair G p q := by
  obtain ⟨p, q, hpq, hclass⟩ :=
    ahtDoublePinReplacement_twoPairs_classification (T := T)
  rcases hclass with hnonpin | hpin
  · exact F.exists_ambient_twinPair_of_replacement_old_nonpin
      hpq hnonpin.1 hnonpin.2.1
  · have hpqNe : p ≠ q := fun heq ↦ hpq.falseTwins.1
      (congrArg Sum.inl heq)
    have hone : F.verts.card = 1 := by
      rcases hpin.1 with rfl | rfl | rfl <;>
        rcases hpin.2.1 with rfl | rfl | rfl
      · exact (hpqNe rfl).elim
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (2 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (1 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (2 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact (hpqNe rfl).elim
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (0 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (1 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (0 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact (hpqNe rfl).elim
    exact False.elim (by omega)

end AHTThreeFragment

namespace WatkinsMesnerSplitter

/-- Minimality applied to the final `A`-side replacement supplies an
ambient degree-three twin pair entirely inside `C_A ∪ A`. -/
theorem exists_twinPair_mem_finalLeftVerts_of_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hxy : x.1 ≠ y.1) (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1) :
    ∃ p ∈ S.finalLeftVerts, ∃ q ∈ S.finalLeftVerts,
      AHTTwinPair G p q := by
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  let F := S.finalLeftFragment hthree htri hcx hcy hcz hxy hxz hyz
    hcenterNeighbors hAcard hBcard hx hy hz
  have hfresh : ∀ i : Fin 3, ¬F.NeedsFreshPin i := by
    intro i
    exact S.finalLeftFragment_not_needsFreshPin hthree htri
      hcx hcy hcz hxy hxz hyz hcenterNeighbors hAcard hBcard hx hy hz i
  have hout : 3 ≤ (Finset.univ \
      (F.verts ∪ ({F.a, F.b, F.c} : Finset V))).card := by
    have hfour := S.four_le_complement_finalLeftVerts_terminals hBcard
    change 3 ≤ (Finset.univ \
      (S.finalLeftVerts ∪ ({x.1, y.1, z.1} : Finset V))).card
    omega
  have hcard : Fintype.card (F.PreparedVertex ⊕ Fin 2) < Fintype.card V :=
    F.replacement_card_lt_of_no_fresh_of_three_le_outside hfresh hout
  have hreplacementThree : IsThreeConnected F.replacementGraph :=
    F.replacementGraph_isThreeConnected hthree
  have hreplacementAlmost : AlmostWheelFree F.replacementGraph :=
    F.replacementGraph_almostWheelFree hthree halmost
  obtain ⟨T⟩ := ih (F.PreparedVertex ⊕ Fin 2) F.replacementGraph hcard
    hreplacementThree hreplacementAlmost
  have htwo : 2 ≤ F.verts.card := by
    have hsub : ahtDeletedFinsetVal S.aSet ⊆ S.finalLeftVerts :=
      Finset.subset_union_right
    have hle := Finset.card_le_card hsub
    have hAcard' : (ahtDeletedFinsetVal S.aSet).card = 3 := by
      simpa using hAcard
    change 2 ≤ S.finalLeftVerts.card
    omega
  exact F.exists_ambient_twinPair_of_replacement_twoPairs_of_two_le
    T hreplacementThree htwo

/-- The two final retained sides are vertex-disjoint.  The only nonliteral
case is a component selected by both side families; its external boundary
would then lie in the disjoint sets `A` and `B`, hence be empty, contradicting
ambient three-connectivity. -/
theorem finalLeftVerts_disjoint_swapSides
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) :
    Disjoint S.finalLeftVerts S.swapSides.finalLeftVerts := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hqLeft hqRight
  change q ∈ S.ambientLeftCarrier ∪
    ahtDeletedFinsetVal S.aSet at hqLeft
  change q ∈ S.swapSides.ambientLeftCarrier ∪
    ahtDeletedFinsetVal S.swapSides.aSet at hqRight
  rcases Finset.mem_union.mp hqLeft with hqCarrier | hqA
  · rcases Finset.mem_union.mp hqRight with hqCarrier' | hqB
    · obtain ⟨CL, hCL, hqCL⟩ := Finset.mem_biUnion.mp hqCarrier
      obtain ⟨D, hD, -, rfl, hleft⟩ :=
        (S.mem_ambientLeftComponents_iff CL).mp hCL
      obtain ⟨CR, hCR, hqCR⟩ := Finset.mem_biUnion.mp hqCarrier'
      obtain ⟨E, hEraw, -, rfl, hrightRaw⟩ :=
        (S.swapSides.mem_ambientLeftComponents_iff CR).mp hCR
      have hE : IsComponentAfterDeleting (deleteVertex G center)
          (S.aSet ∪ S.bSet) E := by
        simpa [swapSides, Finset.union_comm] using hEraw
      obtain ⟨qD, hqD, hqDval⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hqCL
      obtain ⟨qE, hqE, hqEval⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hqCR
      have hqDEq : qD = qE := Subtype.ext (hqDval.trans hqEval.symm)
      have hqE' : qD ∈ E := by simpa [hqDEq] using hqE
      have hDE : D = E := by
        ext w
        constructor
        · intro hwD
          exact hE.mem_of_shared hD hqE' hqD hwD
        · intro hwE
          exact hD.mem_of_shared hE hqD hqE' hwE
      subst E
      have hright : HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
          (ahtDeletedFinsetVal S.bSet) := by
        simpa [swapSides] using hrightRaw
      have hempty : HasExternalBoundaryIn G (ahtDeletedFinsetVal D) ∅ := by
        intro u huD v huv hvD
        have hvA := hleft u huD v huv hvD
        have hvB := hright u huD v huv hvD
        exact False.elim (Finset.disjoint_left.mp
          (disjoint_ahtDeletedFinsetVal S.A_disjoint_B) hvA hvB)
      have hthreeEmpty := three_le_card_of_externalBoundary hthree
        (ahtDeletedFinsetVal D) ∅ (by simp) hempty
        (ahtDeletedFinsetVal_nonempty.mpr hD.1)
        ⟨center, by simp [center_not_mem_ahtDeletedFinsetVal D]⟩
      simpa using hthreeEmpty
    · exact Finset.disjoint_left.mp S.ambientLeftCarrier_disjoint_right
        hqCarrier (by simpa [swapSides] using hqB)
  · rcases Finset.mem_union.mp hqRight with hqCarrier' | hqB
    · exact Finset.disjoint_left.mp
        S.swapSides.ambientLeftCarrier_disjoint_right hqCarrier'
          (by simpa [swapSides] using hqA)
    · exact Finset.disjoint_left.mp
        (disjoint_ahtDeletedFinsetVal S.A_disjoint_B) hqA
          (by simpa [swapSides] using hqB)

/-- The final all-singleton, both-triples branch contradicts the assumed
absence of two disjoint ambient twin pairs: recurse once on each retained
side and combine the resulting pairs using the preceding disjointness
theorem. -/
theorem false_of_terminalParts_singleton_both_triples_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hxy : x.1 ≠ y.1) (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1) : False := by
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    S.exists_twinPair_mem_finalLeftVerts_of_below hthree halmost ih
      hcx hcy hcz hxy hxz hyz hcenterNeighbors hAcard hBcard hx hy hz
  have hAcard' : S.swapSides.aSet.card = 3 := by
    simpa [swapSides] using hBcard
  have hBcard' : S.swapSides.bSet.card = 3 := by
    simpa [swapSides] using hAcard
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    S.swapSides.exists_twinPair_mem_finalLeftVerts_of_below
      hthree halmost ih hcx hcy hcz hxy hxz hyz hcenterNeighbors
        hAcard' hBcard' (by simpa [swapSides] using hx)
        (by simpa [swapSides] using hy) (by simpa [swapSides] using hz)
  exact false_of_twinPairs_in_disjoint_parts
    (S.finalLeftVerts_disjoint_swapSides hthree)
      hp hq hr hs hpq hrs hno

/-- Complete Claim-(8) elimination for a twin pair in the `X` terminal
component.  Disjoint terminal alternatives force `Y,Z` to be singletons;
the four side-cardinality cases are then respectively the singleton-twin,
both-triples Claim-One, and the two mixed fan/wheel contradictions. -/
theorem false_of_xPart_twinPair_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center)
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) : False := by
  have hy : S.yPart.card = 1 := by
    rcases S.yPart_singleton_or_ambientTwinPair_of_below_unoriented
        hcx hcy hcz hcenterNeighbors hnotClose hthree halmost ih with
      hy | ⟨r, hr, s, hs, hrs⟩
    · exact hy
    · exact False.elim (false_of_twinPairs_in_disjoint_parts
        (disjoint_ahtDeletedFinsetVal S.X_disjoint_Y)
          hp hq hr hs hpq hrs hno)
  have hz : S.zPart.card = 1 := by
    rcases S.zPart_singleton_or_ambientTwinPair_of_below_unoriented
        hcx hcy hcz hcenterNeighbors hnotClose hthree halmost ih with
      hz | ⟨r, hr, s, hs, hrs⟩
    · exact hz
    · exact False.elim (false_of_twinPairs_in_disjoint_parts
        (disjoint_ahtDeletedFinsetVal S.X_disjoint_Z)
          hp hq hr hs hpq hrs hno)
  rcases S.A_card with hAone | hAthree
  · rcases S.B_card with hBone | hBthree
    · exact S.false_of_yz_singletons_both_sides_singletons hthree
        hnotClose hcy hcz hcenterNeighbors hy hz hAone hBone
    · exact S.false_of_xPart_twinPair_mixed_below hthree halmost hno ih
        hcx hcy hcz hcenterNeighbors hy hz hp hq hpq
          (Or.inr ⟨hAone, hBthree⟩)
  · rcases S.B_card with hBone | hBthree
    · exact S.false_of_xPart_twinPair_mixed_below hthree halmost hno ih
        hcx hcy hcz hcenterNeighbors hy hz hp hq hpq
          (Or.inl ⟨hAthree, hBone⟩)
    · exact S.false_of_xPart_twinPair_both_triples_below hthree halmost
        hno ih hcx hcy hcz hcenterNeighbors hAthree hBthree hy hz
          hp hq hpq

/-- General deleted-centre form of corrected Claim (5), independent of the
packaged source-data record. -/
theorem side_cards_eq_three_of_terminalParts_singleton
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center)
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1) :
    S.aSet.card = 3 ∧ S.bSet.card = 3 := by
  obtain ⟨x0, hxPart⟩ := Finset.card_eq_one.mp hx
  obtain ⟨y0, hyPart⟩ := Finset.card_eq_one.mp hy
  obtain ⟨z0, hzPart⟩ := Finset.card_eq_one.mp hz
  have hxx0 : x = x0 := by simpa [hxPart] using S.x_mem_X
  have hyy0 : y = y0 := by simpa [hyPart] using S.y_mem_Y
  have hzz0 : z = z0 := by simpa [hzPart] using S.z_mem_Z
  let C : AHTClaim5DeletedSplitter G center x y z :=
    { splitter := S
      xPart_eq := by simpa [hxx0] using hxPart
      yPart_eq := by simpa [hyy0] using hyPart
      zPart_eq := by simpa [hzz0] using hzPart
      center_adj_x := hcx
      center_adj_y := hcy
      center_adj_z := hcz
      center_not_close := hnotClose }
  exact aht_theorem66_claim5_of_deletedSplitter hthree halmost C

/-- The entire terminal endgame for a fixed deleted-centre splitter.  Each
twin alternative is reduced cyclically to Claim (8); if all three terminal
parts are singletons, corrected Claim (5) and the two final side
replacements close the counterexample. -/
theorem false_of_below
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V))
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hxy : x.1 ≠ y.1) (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center) : False := by
  rcases S.xPart_singleton_or_ambientTwinPair_of_below_unoriented
      hcx hcy hcz hcenterNeighbors hnotClose hthree halmost ih with
    hx | ⟨p, hp, q, hq, hpq⟩
  · rcases S.yPart_singleton_or_ambientTwinPair_of_below_unoriented
        hcx hcy hcz hcenterNeighbors hnotClose hthree halmost ih with
      hy | ⟨p, hp, q, hq, hpq⟩
    · rcases S.zPart_singleton_or_ambientTwinPair_of_below_unoriented
          hcx hcy hcz hcenterNeighbors hnotClose hthree halmost ih with
        hz | ⟨p, hp, q, hq, hpq⟩
      · obtain ⟨hAcard, hBcard⟩ :=
          S.side_cards_eq_three_of_terminalParts_singleton hthree halmost
            hcx hcy hcz hnotClose hx hy hz
        exact S.false_of_terminalParts_singleton_both_triples_below
          hthree halmost hno ih hcx hcy hcz hxy hxz hyz
            hcenterNeighbors hAcard hBcard hx hy hz
      · have hcenterNeighbors' : ∀ ⦃r : V⦄, G.Adj center r →
            r = z.1 ∨ r = x.1 ∨ r = y.1 := by
          intro r hr
          rcases hcenterNeighbors hr with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
        exact (S.cycleLeft.cycleLeft).false_of_xPart_twinPair_below
          hthree halmost hno ih hcz hcx hcy hcenterNeighbors' hnotClose
            (by simpa only [cycleLeft_xPart, cycleLeft_yPart] using hp)
            (by simpa only [cycleLeft_xPart, cycleLeft_yPart] using hq) hpq
    · have hcenterNeighbors' : ∀ ⦃r : V⦄, G.Adj center r →
          r = y.1 ∨ r = z.1 ∨ r = x.1 := by
        intro r hr
        rcases hcenterNeighbors hr with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      exact S.cycleLeft.false_of_xPart_twinPair_below
        hthree halmost hno ih hcy hcz hcx hcenterNeighbors' hnotClose
          (by simpa only [cycleLeft_xPart] using hp)
          (by simpa only [cycleLeft_xPart] using hq) hpq
  · exact S.false_of_xPart_twinPair_below hthree halmost hno ih
      hcx hcy hcz hcenterNeighbors hnotClose hp hq hpq

end WatkinsMesnerSplitter

namespace AHTTheorem66SourceData

/-- The complete terminal endgame specialized to the concrete degree-three
source chosen at the start of the minimal-counterexample proof.  Thus, once
Watkins--Mesner supplies its splitter in the centre-deleted graph, no further
geometric input remains: all terminal, mixed-side, and final three-by-three
branches contradict the strict strong-induction hypothesis. -/
theorem false_of_splitter_below
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) : False := by
  exact S.false_of_below hthree halmost hno ih
    D.center_adj_x D.center_adj_y D.center_adj_z
    D.xy D.xz D.yz (fun _ hq ↦ D.center_neighbor_location hq) D.not_close

/-- Positive fixed-splitter form of Theorem 6.6.  This is the exact result
consumed by the outer strong-induction step after the Watkins--Mesner
construction has produced its deleted-centre splitter. -/
theorem twoPairs_of_splitter_below
    (D : AHTTheorem66SourceData G)
    (S : WatkinsMesnerSplitter (deleteVertex G D.center)
      D.xDeleted D.yDeleted D.zDeleted)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (ih : AHTTheorem66Below.{u} (Fintype.card V)) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  by_contra hno
  exact D.false_of_splitter_below S hthree halmost hno ih

end AHTTheorem66SourceData

/-!
## Unconditional assembly theorem

The final `aht_theorem66` uses the following constructive call graph.  Every
step is now an ordinary theorem: in particular, Watkins--Mesner splitter
existence is supplied by `exists_watkinsMesnerSplitter`, with no
`Prop`-valued principle or assumed function.

The induction must have the following (universe-polymorphic) shape.  For
`n : Nat`, its motive says that for every finite `W : Type u`, every
decidable simple graph `H` on `W` with `Fintype.card W = n`, three
connectivity and almost-wheel-freeness imply
`Nonempty (TwoDisjointDegreeThreeFalseTwinPairs H)`.  Strong induction on
`n` is essential: the two recursive graphs below have vertex types built
from subtypes, sums, and optional pins, rather than the ambient type `V`.
At the step for `G`, assume that the conclusion is false.  Claim (1), each
of the three applications in Claim (3), and the final `C_B`-side
replacement invoke the induction hypothesis only after an explicit strict
`Fintype.card` inequality has been established.

The source-exact call graph is:

* `exists_degreeThree_not_center_not_close_of_no_twoPairs` chooses `center`.
  `exists_three_neighbors_of_degree_eq_three` enumerates its neighbourhood
  as three distinct ambient vertices.  The three vertices are then put in
  the subtype `{w // w != center}` and
  `vertexTwoConnected_delete_of_isThreeConnected` supplies connectivity of
  `deleteVertex G center` and of all its one-vertex deletions.
* `not_hasCycleThroughThree_deleteVertex_of_not_wheelCenter` gives the
  common-cycle obstruction.  Watkins--Mesner supplies a splitter in the
  deleted graph, never in `G`.
* For each terminal component, map the subtype finset with
  `ahtDeletedFinsetVal`.  The ambient fragment for the `X` recursion is
  precisely mapped `X`, with boundary
  `{center, splitter.xA.1, splitter.xB.1}`.  Thus its recursive graph is the
  concrete `AHTThreeFragment.replacementGraph`; names `yPrime`, `zPrime`,
  `xAPrime`, and `xBPrime` in
  `AHTClaim3CardinalityCertificateDeleted` are the images of its two double
  pins and its two optional fresh boundary pins.
* `gx_card_lt` proves the strict inequality for that graph.  The induction
  hypothesis produces two replacement twin pairs.  The deliberately added
  pair consumes one pair; the other is classified by
  `ahtDoublePinReplacement_twoPairs_classification`.  Its non-pin branch
  lifts to a twin pair inside mapped `X`; its pin branch is the explicit
  two-vertex gate and forces `X.card = 1`.  Repeat cyclically for `Y,Z`.
* If one terminal component contains a twin pair, the both-triples branch
  builds the opposite three-fragment and contradicts Claim (1); the mixed
  one/triple splitter-side branch is ruled out by the two source fan/wheel
  arguments.  Therefore all three terminal components are singletons.
  `aht_theorem66_claim5_of_deletedSplitter` then forces both splitter sides
  to have cardinality three.
* In the final three-by-three branch, condition (vii) partitions every
  remaining component onto the `A` or `B` side.  The `B`-side union together
  with the three `B` attachments and `center` is a three-fragment with
  boundary `{x.1,y.1,z.1}`.  Its replacement has only the two double pins as
  new vertices, hence is strictly smaller.  Induction supplies a second
  replacement pair; after removing the deliberate double-pin pair it lifts
  to a pair on the disjoint `A` side.  Reversing the roles of `A,B` supplies
  another pair, contradicting the counterexample assumption.

1. **Watkins--Mesner splitter completion.**  Starting with the
   `WatkinsMesnerK32Source` and the maximal triple supplied by
   `exists_watkinsMesnerMaximalTriple`, eliminate the cardinality-two cases
   in `aSet_card_trichotomy` and `bSet_card_trichotomy`.  Then turn an
   unmatched edge or the `MismatchedBoundaryPath` produced by
   `exists_mismatchedBoundaryPath_of_boundary_failure` into a forbidden
   cycle through the three terminals.  These give the `hAcard`, `hBcard`,
   `hmatched`, and `hboundary` arguments of `toWatkinsMesnerSplitter`.

The terminal-twin, mixed one/triple, both-triples component-union, and final
`A/B` replacement branches are completed above.  In particular,
`AHTTheorem66SourceData.twoPairs_of_splitter_below` is the complete positive
strong-induction step.  The outer `Nat.strong_induction_on` only chooses the
source data, constructs its splitter, and applies that theorem.

The strong-induction motive quantifies over every finite vertex type in the
current universe and uses `Fintype.card` as its measure; both fragment
replacement and the concrete `G_X` change the vertex type.
-/

/-- AHT Theorem 6.6: every finite three-connected almost-wheel-free graph
contains two vertex-disjoint pairs of degree-three false twins. -/
theorem aht_theorem66 :
    ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      IsThreeConnected H → AlmostWheelFree H →
        Nonempty (TwoDisjointDegreeThreeFalseTwinPairs H) := by
  classical
  have hP : ∀ n : Nat, AHTTheorem66AtCard.{0} n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro W _ _ H _ hcardEq hthree halmost
        subst n
        by_contra hno
        obtain ⟨D⟩ := exists_ahtTheorem66SourceData hthree halmost hno
        obtain ⟨hconn, hdelete⟩ := D.deleted_vertexTwoConnected hthree
        obtain ⟨S⟩ := exists_watkinsMesnerSplitter
          (fun h ↦ D.xy (congrArg Subtype.val h))
          (fun h ↦ D.xz (congrArg Subtype.val h))
          (fun h ↦ D.yz (congrArg Subtype.val h))
          hconn hdelete D.deleted_no_common_cycle
        exact hno (D.twoPairs_of_splitter_below S hthree halmost
          (ahtTheorem66Below_of_strongInduction ih))
  intro W _ _ H _ hthree halmost
  exact hP (Fintype.card W) W H rfl hthree halmost

end Erdos916
