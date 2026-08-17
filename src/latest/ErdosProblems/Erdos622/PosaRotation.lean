/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.LongestCycle

/-!
# Pósa endpoint rotations

This file develops the finite rotation operation used in Pósa's
rotation--extension argument.  A path from `a` to `b` is split at a vertex
`y` adjacent to `b`; the initial segment is followed by the chord `y b`, and
the old final segment is traversed backwards.  Thus the initial endpoint is
fixed and the new final endpoint is the successor of `y` on the old path.
-/

open Finset
open scoped SimpleGraph

namespace Erdos622
namespace PosaRotation

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Rotate `p` using the chord from its terminal endpoint `b` to `y`.
The new terminal endpoint is the successor of `y` on `p`. -/
def rotateEndpoint {a b y : V} (p : G.Walk a b)
    (hy : y ∈ p.support) (hby : G.Adj b y) :
    G.Walk a ((p.dropUntil y hy).snd) :=
  ((p.takeUntil y hy).concat hby.symm).append
    ((p.dropUntil y hy).tail.reverse)

theorem rotateEndpoint_length {a b y : V} (p : G.Walk a b)
    (hy : y ∈ p.support) (hby : G.Adj b y) :
    (rotateEndpoint p hy hby).length = p.length := by
  simp only [rotateEndpoint, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.length_tail]
  have hsplit := congrArg SimpleGraph.Walk.length (p.take_spec hy)
  simp only [SimpleGraph.Walk.length_append] at hsplit
  have hdrop : ¬ (p.dropUntil y hy).Nil := by
    intro hnil
    have hyb : y = b := hnil.eq
    exact hby.ne hyb.symm
  have hpos : 0 < (p.dropUntil y hy).length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hdrop
  omega

/-- Rotation preserves the vertex set of the path.  This formulation by
membership is convenient when transporting Hamiltonicity and maximality. -/
theorem mem_rotateEndpoint_support_iff {a b y z : V} (p : G.Walk a b)
    (hy : y ∈ p.support) (hby : G.Adj b y) :
    z ∈ (rotateEndpoint p hy hby).support ↔ z ∈ p.support := by
  have hdrop : ¬ (p.dropUntil y hy).Nil := by
    intro hnil
    have hyb : y = b := hnil.eq
    exact hby.ne hyb.symm
  rw [rotateEndpoint, SimpleGraph.Walk.mem_support_append_iff]
  constructor
  · rintro (hz | hz)
    · rw [SimpleGraph.Walk.support_concat] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact p.support_takeUntil_subset_support hy hz
      · simp only [List.mem_singleton] at hz
        simpa [hz] using p.end_mem_support
    · have hz' : z ∈ (p.dropUntil y hy).tail.support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
      exact p.support_dropUntil_subset_support hy
        (List.tail_subset _ (by
          rwa [SimpleGraph.Walk.support_tail_of_not_nil _ hdrop] at hz'))
  · intro hz
    have hsplit :
        z ∈ (p.takeUntil y hy).support ∨ z ∈ (p.dropUntil y hy).support := by
      rw [← SimpleGraph.Walk.mem_support_append_iff, p.take_spec hy]
      exact hz
    rcases hsplit with hz | hz
    · exact Or.inl (by
        rw [SimpleGraph.Walk.support_concat]
        exact List.mem_append_left _ hz)
    · rw [SimpleGraph.Walk.mem_support_iff] at hz
      rcases hz with hzy | hz
      · subst z
        exact Or.inl (by
          rw [SimpleGraph.Walk.support_concat]
          exact List.mem_append_left _ (p.takeUntil y hy).end_mem_support)
      · exact Or.inr (by
          rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
            SimpleGraph.Walk.support_tail_of_not_nil _ hdrop]
          exact hz)

/-- A legal endpoint rotation of a path is again a path. -/
theorem rotateEndpoint_isPath {a b y : V} {p : G.Walk a b}
    (hp : p.IsPath) (hy : y ∈ p.support) (hby : G.Adj b y) :
    (rotateEndpoint p hy hby).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  change Multiset.Nodup (↑(rotateEndpoint p hy hby).support : Multiset V)
  rw [← Multiset.toFinset_card_eq_card_iff_nodup]
  change (rotateEndpoint p hy hby).support.toFinset.card =
    (rotateEndpoint p hy hby).support.length
  have hfinset : (rotateEndpoint p hy hby).support.toFinset =
      p.support.toFinset := by
    ext z
    simp only [List.mem_toFinset, mem_rotateEndpoint_support_iff]
  rw [hfinset, List.toFinset_card_of_nodup hp.support_nodup]
  rw [(rotateEndpoint p hy hby).length_support, p.length_support,
    rotateEndpoint_length]

/-! ## Rotation reachability with a fixed root -/

/-- A walk whose initial vertex is fixed, with its terminal vertex bundled
because rotations change that terminal vertex. -/
structure RootedWalk (G : SimpleGraph V) (a : V) where
  terminal : V
  walk : G.Walk a terminal

/-- The rooted walk obtained by one endpoint rotation. -/
def RootedWalk.rotate {a : V} (q : RootedWalk G a) (y : V)
    (hy : y ∈ q.walk.support) (h : G.Adj q.terminal y) : RootedWalk G a where
  terminal := (q.walk.dropUntil y hy).snd
  walk := rotateEndpoint q.walk hy h

/-- One legal Pósa endpoint rotation. -/
def OneStep {a : V} (q r : RootedWalk G a) : Prop :=
  ∃ (y : V) (hy : y ∈ q.walk.support) (h : G.Adj q.terminal y),
    r = q.rotate y hy h

/-- Reachability by a finite (possibly empty) sequence of endpoint
rotations, always fixing the root. -/
abbrev RotationReachable {a : V} (q r : RootedWalk G a) : Prop :=
  Relation.ReflTransGen (OneStep (G := G)) q r

theorem OneStep.isPath {a : V} {q r : RootedWalk G a}
    (hqr : OneStep q r) (hq : q.walk.IsPath) : r.walk.IsPath := by
  obtain ⟨y, hy, h, rfl⟩ := hqr
  exact rotateEndpoint_isPath hq hy h

theorem OneStep.length_eq {a : V} {q r : RootedWalk G a}
    (hqr : OneStep q r) : r.walk.length = q.walk.length := by
  obtain ⟨y, hy, h, rfl⟩ := hqr
  exact rotateEndpoint_length q.walk hy h

theorem OneStep.mem_support_iff {a : V} {q r : RootedWalk G a}
    (hqr : OneStep q r) (z : V) :
    z ∈ r.walk.support ↔ z ∈ q.walk.support := by
  obtain ⟨y, hy, h, rfl⟩ := hqr
  exact mem_rotateEndpoint_support_iff q.walk hy h

theorem RotationReachable.isPath {a : V} {q r : RootedWalk G a}
    (hqr : RotationReachable q r) (hq : q.walk.IsPath) : r.walk.IsPath := by
  induction hqr with
  | refl => exact hq
  | tail _ hst ih => exact hst.isPath ih

theorem RotationReachable.length_eq {a : V} {q r : RootedWalk G a}
    (hqr : RotationReachable q r) : r.walk.length = q.walk.length := by
  induction hqr with
  | refl => rfl
  | tail _ hst ih => exact hst.length_eq.trans ih

theorem RotationReachable.mem_support_iff {a : V} {q r : RootedWalk G a}
    (hqr : RotationReachable q r) (z : V) :
    z ∈ r.walk.support ↔ z ∈ q.walk.support := by
  induction hqr with
  | refl => rfl
  | tail _ hst ih => exact (hst.mem_support_iff z).trans ih

/-- Every path reached from a longest path is again longest. -/
theorem RotationReachable.isLongestPath {a : V} {q r : RootedWalk G a}
    (hqr : RotationReachable q r)
    (hq : LongestCycle.IsLongestPath q.walk) :
    LongestCycle.IsLongestPath r.walk := by
  refine ⟨hqr.isPath hq.1, ?_⟩
  intro u v p hp
  rw [hqr.length_eq]
  exact hq.2 p hp

/-- The finite set of endpoints reachable by Pósa rotations from `q`. -/
noncomputable def endpointSet {a : V} (q : RootedWalk G a) : Finset V :=
  Finset.univ.filter fun x ↦
    ∃ r : RootedWalk G a, RotationReachable q r ∧ r.terminal = x

theorem mem_endpointSet_iff {a x : V} {q : RootedWalk G a} :
    x ∈ endpointSet q ↔
      ∃ r : RootedWalk G a, RotationReachable q r ∧ r.terminal = x := by
  simp [endpointSet]

theorem terminal_mem_endpointSet {a : V} (q : RootedWalk G a) :
    q.terminal ∈ endpointSet q := by
  rw [mem_endpointSet_iff]
  exact ⟨q, Relation.ReflTransGen.refl, rfl⟩

/-- The endpoint set is closed under every legal rotation of every reached
path. -/
theorem endpoint_of_rotate_mem_endpointSet {a : V} {q r : RootedWalk G a}
    (hqr : RotationReachable q r) (y : V) (hy : y ∈ r.walk.support)
    (h : G.Adj r.terminal y) :
    (r.rotate y hy h).terminal ∈ endpointSet q := by
  rw [mem_endpointSet_iff]
  exact ⟨r.rotate y hy h, hqr.tail ⟨y, hy, h, rfl⟩, rfl⟩

/-! ## Shifting endpoint neighbours -/

/-- The successor of a vertex on an oriented path.  Off the support it is
defined to be the vertex itself; all applications below are on the support. -/
noncomputable def pathSuccessor {a b : V} (p : G.Walk a b) (y : V) : V :=
  if hy : y ∈ p.support then (p.dropUntil y hy).snd else y

/-- The predecessor of a vertex on an oriented path.  At the initial vertex
the truncated index is zero; that value is removed in `pathBoundary`. -/
noncomputable def pathPredecessor {a b : V} (p : G.Walk a b) (y : V) : V :=
  if hy : y ∈ p.support then p.getVert (p.support.idxOf y - 1) else y

theorem pathSuccessor_eq {a b y : V} (p : G.Walk a b)
    (hy : y ∈ p.support) :
    pathSuccessor p y = (p.dropUntil y hy).snd := by
  simp [pathSuccessor, hy]

theorem snd_dropUntil_eq_getVert_succ {a b y : V} (p : G.Walk a b)
    (hy : y ∈ p.support) :
    (p.dropUntil y hy).snd = p.getVert (p.support.idxOf y + 1) := by
  rw [SimpleGraph.Walk.dropUntil_eq_drop]
  simp only [SimpleGraph.Walk.snd, SimpleGraph.Walk.drop_getVert,
    SimpleGraph.Walk.getVert_copy]

theorem pathSuccessor_getVert {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {i : ℕ} (hi : i < p.length) :
    pathSuccessor p (p.getVert i) = p.getVert (i + 1) := by
  have hmem : p.getVert i ∈ p.support := p.getVert_mem_support i
  rw [pathSuccessor_eq p hmem, snd_dropUntil_eq_getVert_succ]
  have hidxle : p.support.idxOf (p.getVert i) ≤ p.length := by
    have hlt := List.idxOf_lt_length_of_mem hmem
    rw [p.length_support] at hlt
    omega
  have hidx : p.support.idxOf (p.getVert i) = i :=
    hp.getVert_injOn hidxle (show i ≤ p.length by omega)
      (p.getVert_support_idxOf hmem)
  rw [hidx]

theorem pathPredecessor_getVert_succ {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {i : ℕ} (hi : i < p.length) :
    pathPredecessor p (p.getVert (i + 1)) = p.getVert i := by
  have hmem : p.getVert (i + 1) ∈ p.support := p.getVert_mem_support (i + 1)
  rw [pathPredecessor, dif_pos hmem]
  have hidxle : p.support.idxOf (p.getVert (i + 1)) ≤ p.length := by
    have hlt := List.idxOf_lt_length_of_mem hmem
    rw [p.length_support] at hlt
    omega
  have hidx : p.support.idxOf (p.getVert (i + 1)) = i + 1 :=
    hp.getVert_injOn hidxle (show i + 1 ≤ p.length by omega)
      (p.getVert_support_idxOf hmem)
  rw [hidx]
  congr

/-- Vertices immediately before or after `S` in the fixed orientation of
`p`.  The missing successor of the terminal vertex and missing predecessor
of the initial vertex are explicitly erased. -/
noncomputable def pathBoundary {a b : V} (p : G.Walk a b)
    (S : Finset V) : Finset V :=
  (S.erase b).image (pathSuccessor p) ∪
    (S.erase a).image (pathPredecessor p)

/-- Every path edge from `S` ends in the path boundary of `S`. -/
theorem mem_pathBoundary_of_mem_edges {a b x y : V} {p : G.Walk a b}
    (hp : p.IsPath) {S : Finset V} (hx : x ∈ S)
    (hxy : s(x, y) ∈ p.edges) : y ∈ pathBoundary p S := by
  obtain ⟨i, hi, hedge⟩ :=
    (p.mk_mem_edges_iff_exists (u' := x) (v' := y)).mp hxy
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq] at hedge
  rcases hedge with hedge | hedge
  · have hix : p.getVert i = x := hedge.1
    have hiy : p.getVert (i + 1) = y := hedge.2
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_erase.mpr ⟨?_, hx⟩, ?_⟩
    · intro hxb
      have : i = p.length :=
        (hp.getVert_eq_end_iff (by omega)).mp (hix.trans hxb)
      omega
    · rw [← hiy, ← hix]
      exact pathSuccessor_getVert hp hi
  · have hedge' : (p.getVert i, p.getVert (i + 1)) = (y, x) := by
      simpa only [Prod.swap_prod_mk] using hedge
    have hiy : p.getVert i = y := congrArg Prod.fst hedge'
    have hix : p.getVert (i + 1) = x := congrArg Prod.snd hedge'
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_erase.mpr ⟨?_, hx⟩, ?_⟩
    · intro hxa
      have : i + 1 = 0 :=
        (hp.getVert_eq_start_iff (by omega)).mp (hix.trans hxa)
      omega
    · rw [← hiy, ← hix]
      exact pathPredecessor_getVert_succ hp hi

/-- The elementary `2|S|-1` count underlying Pósa's neighbourhood lemma. -/
theorem card_pathBoundary_le_two_mul_sub_one {a b : V} (p : G.Walk a b)
    (S : Finset V) (hb : b ∈ S) :
    (pathBoundary p S).card ≤ 2 * S.card - 1 := by
  have hunion := Finset.card_union_le
    ((S.erase b).image (pathSuccessor p))
    ((S.erase a).image (pathPredecessor p))
  have hsucc : ((S.erase b).image (pathSuccessor p)).card ≤
      (S.erase b).card := Finset.card_image_le
  have hpred : ((S.erase a).image (pathPredecessor p)).card ≤
      (S.erase a).card := Finset.card_image_le
  rw [Finset.card_erase_of_mem hb] at hsucc
  have herase : (S.erase a).card ≤ S.card := Finset.card_erase_le
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨b, hb⟩
  change ((S.erase b).image (pathSuccessor p) ∪
    (S.erase a).image (pathPredecessor p)).card ≤ 2 * S.card - 1
  omega

/-! ## The finite neighbourhood inequality -/

/-- The open neighbourhood of a finite vertex set.  A vertex belongs when
it is adjacent to at least one member of the set; it need not lie outside
the set. -/
noncomputable def openNeighborhood (G : SimpleGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter fun y ↦ ∃ x ∈ S, G.Adj x y

theorem mem_openNeighborhood_iff {S : Finset V} {y : V} :
    y ∈ openNeighborhood G S ↔ ∃ x ∈ S, G.Adj x y := by
  simp [openNeighborhood]

theorem neighborFinset_subset_openNeighborhood {S : Finset V} {x : V}
    (hx : x ∈ S) : G.neighborFinset x ⊆ openNeighborhood G S := by
  intro y hy
  rw [mem_openNeighborhood_iff]
  exact ⟨x, hx, (G.mem_neighborFinset x y).mp hy⟩

/-- A reusable exact form of Pósa's boundary argument.  Once every graph
edge leaving `S` is certified to be an edge of the fixed path, the open
neighbourhood is contained in the two shifted copies of `S`. -/
theorem openNeighborhood_subset_pathBoundary {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {S : Finset V}
    (hconfined : ∀ x ∈ S, ∀ y, G.Adj x y → s(x, y) ∈ p.edges) :
    openNeighborhood G S ⊆ pathBoundary p S := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_openNeighborhood_iff.mp hy
  exact mem_pathBoundary_of_mem_edges hp hx (hconfined x hx y hxy)

/-- Pósa's `2|S|-1` neighbourhood estimate, in a certificate form usable
by rotation inductions and longest-cycle arguments. -/
theorem card_openNeighborhood_le_two_mul_sub_one {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) {S : Finset V} (hb : b ∈ S)
    (hconfined : ∀ x ∈ S, ∀ y, G.Adj x y → s(x, y) ∈ p.edges) :
    (openNeighborhood G S).card ≤ 2 * S.card - 1 := by
  exact (Finset.card_le_card
    (openNeighborhood_subset_pathBoundary hp hconfined)).trans
      (card_pathBoundary_le_two_mul_sub_one p S hb)

/-- A minimum-degree consequence of the neighbourhood inequality. -/
theorem minDegree_le_two_mul_card_sub_one {k : ℕ}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) {S : Finset V}
    (hv : v ∈ S) (hDegree : ∀ x : V, k ≤ G.degree x)
    (hconfined : ∀ x ∈ S, ∀ y, G.Adj x y → s(x, y) ∈ p.edges) :
    k ≤ 2 * S.card - 1 := by
  have hdegree : G.degree v ≤ (openNeighborhood G S).card := by
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (neighborFinset_subset_openNeighborhood hv)
  exact (hDegree v).trans (hdegree.trans
    (card_openNeighborhood_le_two_mul_sub_one hp hv hconfined))

/-- Vertices outside `S` and its open neighbourhood. -/
noncomputable def outsideNeighborhood (G : SimpleGraph V) (S : Finset V) : Finset V :=
  (S ∪ openNeighborhood G S)ᶜ

theorem disjoint_outsideNeighborhood (S : Finset V) :
    Disjoint S (outsideNeighborhood G S) := by
  exact Finset.disjoint_left.mpr fun x hxS hxout ↦
    (Finset.mem_compl.mp hxout) (Finset.mem_union_left _ hxS)

/-- There are no edges from a set to the vertices outside its closed
neighbourhood. -/
theorem interedges_outsideNeighborhood_eq_empty (S : Finset V) :
    G.interedges S (outsideNeighborhood G S) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' : (e.1 ∈ S ∧ e.2 ∈ outsideNeighborhood G S) ∧
      G.Adj e.1 e.2 := by
    simpa [SimpleGraph.interedges_def] using he
  have hneigh : e.2 ∈ openNeighborhood G S :=
    mem_openNeighborhood_iff.mpr ⟨e.1, he'.1.1, he'.2⟩
  exact (Finset.mem_compl.mp he'.1.2)
    (Finset.mem_union_right S hneigh)

/-- If both sides have the requested sizes, the exterior of a Pósa set is
an exact zero-edge sparse-pair witness. -/
theorem hasSparsePairAt_of_outsideNeighborhood {k budget : ℕ}
    {S : Finset V} (hS : k ≤ S.card)
    (hout : k ≤ (outsideNeighborhood G S).card) :
    DiracStability.HasSparsePairAt G k budget := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact DiracStability.hasSparsePairAt_of_emptyCut G
    (disjoint_outsideNeighborhood S) hS hout
    (interedges_outsideNeighborhood_eq_empty S)

/-- On a simple path, shifting vertices other than the terminal endpoint to
their successors is injective. -/
theorem pathSuccessor_injOn {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    {S : Finset V} (hS : ∀ y ∈ S, y ∈ p.support ∧ y ≠ b) :
    Set.InjOn (pathSuccessor p) (S : Set V) := by
  intro y hyS z hzS heq
  have hy := (hS y hyS).1
  have hz := (hS z hzS).1
  rw [pathSuccessor_eq p hy, pathSuccessor_eq p hz,
    snd_dropUntil_eq_getVert_succ, snd_dropUntil_eq_getVert_succ] at heq
  have hylt : p.support.idxOf y < p.length := by
    simpa only [SimpleGraph.Walk.length_takeUntil] using
      p.length_takeUntil_lt_length hy (hS y hyS).2
  have hzlt : p.support.idxOf z < p.length := by
    simpa only [SimpleGraph.Walk.length_takeUntil] using
      p.length_takeUntil_lt_length hz (hS z hzS).2
  have hidx : p.support.idxOf y + 1 = p.support.idxOf z + 1 :=
    hp.getVert_injOn (show p.support.idxOf y + 1 ≤ p.length by omega)
      (show p.support.idxOf z + 1 ≤ p.length by omega) heq
  have hidx' : p.support.idxOf y = p.support.idxOf z := by omega
  exact (List.idxOf_inj hy).mp hidx'

/-- Every shifted neighbour of the endpoint of a reached longest path is
again a reachable endpoint. -/
theorem pathSuccessor_mem_endpointSet_of_neighbor
    {a : V} {q r : RootedWalk G a} (hqr : RotationReachable q r)
    (hq : LongestCycle.IsLongestPath q.walk) {y : V}
    (hy : y ∈ G.neighborFinset r.terminal) :
    pathSuccessor r.walk y ∈ endpointSet q := by
  have hr := hqr.isLongestPath hq
  have hadj : G.Adj r.terminal y := (G.mem_neighborFinset _ _).mp hy
  have hysupport : y ∈ r.walk.support := hr.end_neighbor_mem_support hadj
  rw [pathSuccessor_eq r.walk hysupport]
  exact endpoint_of_rotate_mem_endpointSet hqr y hysupport hadj

/-- The classical first numerical consequence of rotations: the reachable
endpoint set has at least the degree of every reached endpoint. -/
theorem degree_le_card_endpointSet {a : V} {q r : RootedWalk G a}
    (hqr : RotationReachable q r)
    (hq : LongestCycle.IsLongestPath q.walk) :
    G.degree r.terminal ≤ (endpointSet q).card := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (pathSuccessor r.walk)
  · intro y hy
    exact pathSuccessor_mem_endpointSet_of_neighbor hqr hq hy
  · apply pathSuccessor_injOn (hqr.isPath hq.1)
    intro y hy
    have hadj : G.Adj r.terminal y := (G.mem_neighborFinset _ _).mp hy
    exact ⟨(hqr.isLongestPath hq).end_neighbor_mem_support hadj, hadj.ne.symm⟩

/-- A minimum-degree lower bound for the entire reachable endpoint set. -/
theorem minDegree_le_card_endpointSet {a : V} {k : ℕ}
    {q : RootedWalk G a} (hq : LongestCycle.IsLongestPath q.walk)
    (hDegree : ∀ x : V, k ≤ G.degree x) :
    k ≤ (endpointSet q).card := by
  exact (hDegree q.terminal).trans
    (degree_le_card_endpointSet Relation.ReflTransGen.refl hq)

/-- In a connected non-Hamiltonian graph, no endpoint reached from a
longest path can be adjacent to the fixed root. -/
theorem not_adj_root_of_rotationReachable_of_not_isHamiltonian
    {a : V} {q r : RootedWalk G a}
    (hq : LongestCycle.IsLongestPath q.walk)
    (hqr : RotationReachable q r) (hconn : G.Connected)
    (hlen : 2 ≤ q.walk.length) (hnot : ¬ G.IsHamiltonian) :
    ¬ G.Adj r.terminal a := by
  intro hra
  have hr : LongestCycle.IsLongestPath r.walk := hqr.isLongestPath hq
  have hrlen : 2 ≤ r.walk.length := by rw [hqr.length_eq]; exact hlen
  have hrHam : r.walk.IsHamiltonian :=
    hr.isHamiltonian_of_connected_of_end_adj hconn hra hrlen
  obtain ⟨c, hc, _hcSupport, hcLength⟩ :=
    hr.exists_isCycle_of_end_adj hra hrlen
  apply hnot
  intro _hcard
  refine ⟨a, c, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨hc, ?_⟩
  rw [hcLength, hrHam.length_eq]
  letI : Nonempty V := ⟨a⟩
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos
  omega

/-- Equivalently, the fixed root is outside the open neighbourhood of the
reachable endpoint set. -/
theorem root_not_mem_openNeighborhood_endpointSet
    {a : V} {q : RootedWalk G a}
    (hq : LongestCycle.IsLongestPath q.walk) (hconn : G.Connected)
    (hlen : 2 ≤ q.walk.length) (hnot : ¬ G.IsHamiltonian) :
    a ∉ openNeighborhood G (endpointSet q) := by
  intro ha
  obtain ⟨x, hx, hxa⟩ := mem_openNeighborhood_iff.mp ha
  obtain ⟨r, hqr, hrx⟩ := mem_endpointSet_iff.mp hx
  subst x
  exact not_adj_root_of_rotationReachable_of_not_isHamiltonian
    hq hqr hconn hlen hnot hxa

end PosaRotation
end Erdos622
