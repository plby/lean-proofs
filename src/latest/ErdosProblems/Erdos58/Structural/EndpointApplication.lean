/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos58.EndpointCount
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Applying the endpoint count to an actual exterior path

`EndpointCount.endpoint_count` deliberately separates its finite sumset
argument from the graph-theoretic construction.  This file supplies the
missing graph side.  Starting with a longest odd cycle, a simple path outside
it, and *positions* at which the two endpoints are adjacent to the path and
cycle, we construct the shortcut routes, the two complementary cycle arcs,
and the short cycles cut off by the last path chord.

The position sets below are defined from `G.Adj`; the enumerations in
`EndpointConfiguration` are required to enumerate those derived sets.  Thus
the public application theorem does not take an `EndpointCountData`, a
`LengthBlock`, or any pre-certified family of cycles as an input.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.Structural.EndpointApplication

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace EC

abbrev LongestOddCycle {V : Type*} (G : SimpleGraph V) :=
  Erdos58.EndpointCount.LongestOddCycle G
abbrev EndpointGeometry {V : Type*} (G : SimpleGraph V) (p q : ℕ) :=
  Erdos58.EndpointCount.EndpointGeometry G p q
abbrev EndpointCountData {V : Type*} (G : SimpleGraph V) (p q : ℕ) :=
  Erdos58.EndpointCount.EndpointCountData G p q
abbrev LengthBlock {V : Type*} (G : SimpleGraph V) (a b c : ℕ) :=
  Erdos58.EndpointCount.LengthBlock G a b c

end EC

/-! ## Positions derived from adjacency -/

/-- Later path positions at which `x` is adjacent to a vertex of `p`.
Position `1` is omitted because it is the compulsory first path edge.  The
terminal position is included: when the path endpoints are adjacent, the
direct endpoint edge is one of Gyárfás' additional routes. -/
noncomputable def interiorChordPositions {x y : V} (p : G.Walk x y) : Finset ℕ := by
  classical
  exact Finset.Ioc 1 p.length |>.filter fun n => G.Adj x (p.getVert n)

/-- Positions on the chosen presentation of a closed walk adjacent to `x`.
The duplicated terminal occurrence of the base vertex is omitted. -/
noncomputable def cycleNeighborPositions {c : V} (w : G.Walk c c) (x : V) : Finset ℕ := by
  classical
  exact Finset.range w.length |>.filter fun n => G.Adj x (w.getVert n)

lemma mem_interiorChordPositions_iff {x y : V} {p : G.Walk x y} {n : ℕ} :
    n ∈ interiorChordPositions p ↔ 1 < n ∧ n ≤ p.length ∧ G.Adj x (p.getVert n) := by
  classical
  simp [interiorChordPositions, and_assoc]

lemma mem_cycleNeighborPositions_iff {c x : V} {w : G.Walk c c} {n : ℕ} :
    n ∈ cycleNeighborPositions w x ↔ n < w.length ∧ G.Adj x (w.getVert n) := by
  classical
  simp [cycleNeighborPositions]

/-! ## Concrete input -/

/--
The concrete endpoint configuration used in Gyárfás' Lemma 4.

The only indexed data are enumerations of adjacency-defined position
finsets.  All paths and cycles used by the counting argument are constructed
below.  The proof itself treats both possible parity orientations of the odd
cycle, so no compatibility certificate is part of this input.
-/
structure EndpointConfiguration (G : SimpleGraph V) (p q : ℕ) where
  longestCycle : EC.LongestOddCycle G
  aVertex : V
  bVertex : V
  path : G.Walk aVertex bVertex
  path_isPath : path.IsPath
  path_positive : 0 < path.length
  path_avoids_cycle :
    ∀ {v : V}, v ∈ path.support → v ∉ longestCycle.cycle.support
  chordPos : Fin q → ℕ
  chordPos_strictMono : StrictMono chordPos
  chordPos_enumerates :
    Finset.univ.image chordPos = interiorChordPositions path
  aPos : Fin p → ℕ
  aPos_strictMono : StrictMono aPos
  aPos_pos : ∀ i, 0 < aPos i
  bPos : ℕ
  aPos_lt_bPos : ∀ i, aPos i < bPos
  bPos_le : bPos ≤ longestCycle.cycle.length
  aPos_enumerates :
    Finset.univ.image aPos =
      (cycleNeighborPositions longestCycle.cycle aVertex).filter fun n =>
        0 < n ∧ n < bPos
  bPos_adj : G.Adj bVertex (longestCycle.cycle.getVert bPos)

namespace EndpointConfiguration

variable {p q : ℕ} (D : EndpointConfiguration G p q)

lemma chordPos_mem (i : Fin q) : D.chordPos i ∈ interiorChordPositions D.path := by
  rw [← D.chordPos_enumerates]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

lemma chordPos_one_lt (i : Fin q) : 1 < D.chordPos i :=
  mem_interiorChordPositions_iff.mp (D.chordPos_mem i) |>.1

lemma chordPos_le (i : Fin q) : D.chordPos i ≤ D.path.length :=
  mem_interiorChordPositions_iff.mp (D.chordPos_mem i) |>.2.1

lemma chord_adj (i : Fin q) :
    G.Adj D.aVertex (D.path.getVert (D.chordPos i)) :=
  mem_interiorChordPositions_iff.mp (D.chordPos_mem i) |>.2.2

lemma aPos_mem (i : Fin p) :
    D.aPos i ∈ cycleNeighborPositions D.longestCycle.cycle D.aVertex := by
  have hi : D.aPos i ∈
      (cycleNeighborPositions D.longestCycle.cycle D.aVertex).filter fun n =>
        0 < n ∧ n < D.bPos := by
    rw [← D.aPos_enumerates]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  exact (Finset.mem_filter.mp hi).1

lemma a_adj_cycle (i : Fin p) :
    G.Adj D.aVertex (D.longestCycle.cycle.getVert (D.aPos i)) :=
  mem_cycleNeighborPositions_iff.mp (D.aPos_mem i) |>.2

/-! ## The shortcut routes -/

/-- The shortcut beginning with the chord from `A` to position `z`. -/
def chordRoute (i : Fin q) : G.Walk D.aVertex D.bVertex :=
  (D.chord_adj i).toWalk.append (D.path.drop (D.chordPos i))

@[simp] lemma chordRoute_length (i : Fin q) :
    (D.chordRoute i).length = 1 + (D.path.length - D.chordPos i) := by
  simp [chordRoute]
  omega

lemma chordRoute_isPath (i : Fin q) : (D.chordRoute i).IsPath := by
  have hdrop := D.path_isPath.drop (D.chordPos i)
  have hA_not_drop : D.aVertex ∉ (D.path.drop (D.chordPos i)).support := by
    intro hA
    rw [SimpleGraph.Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left (D.chordPos_le i),
      ← D.path.cons_tail_support] at hA
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by
      have := D.chordPos_one_lt i
      omega : D.chordPos i ≠ 0)
    rw [hn] at hA
    simp only [List.drop_succ_cons] at hA
    have hnodup := D.path_isPath.support_nodup
    rw [← D.path.cons_tail_support] at hnodup
    exact hnodup.notMem (List.mem_of_mem_drop hA)
  change (SimpleGraph.Walk.cons (D.chord_adj i)
    (D.path.drop (D.chordPos i))).IsPath
  exact (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hdrop, hA_not_drop⟩

/-- Routes are ordered by increasing length: reverse the ordered chord list,
then put the original path last. -/
def route : Fin (q + 1) → G.Walk D.aVertex D.bVertex :=
  Fin.lastCases D.path (fun i : Fin q ↦ D.chordRoute i.rev)

lemma route_isPath (i : Fin (q + 1)) : (D.route i).IsPath := by
  refine Fin.lastCases ?_ (fun j : Fin q ↦ ?_) i
  · simpa [route] using D.path_isPath
  · simpa [route] using D.chordRoute_isPath j.rev

lemma route_avoids_cycle (i : Fin (q + 1)) {v : V}
    (hv : v ∈ (D.route i).support) : v ∉ D.longestCycle.cycle.support := by
  induction i using Fin.lastCases with
  | last =>
    simpa [route] using D.path_avoids_cycle (by simpa [route] using hv)
  | cast j =>
    simp only [route, Fin.lastCases_castSucc] at hv
    have hv' : v = D.aVertex ∨
        v ∈ (D.path.drop (D.chordPos j.rev)).support := by
      simpa [chordRoute, SimpleGraph.Walk.support_cons] using hv
    rcases hv' with rfl | hv'
    · exact D.path_avoids_cycle D.path.start_mem_support
    · exact D.path_avoids_cycle
        (by
          rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hv'
          exact List.mem_of_mem_drop hv')

lemma route_length_strictMono : StrictMono (fun i ↦ (D.route i).length) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last => exact (False.elim ((not_lt_of_ge (Fin.le_last j)) hij))
  | cast i' =>
    induction j using Fin.lastCases with
    | last =>
      simp only [route, Fin.lastCases_castSucc, Fin.lastCases_last,
        chordRoute_length]
      have hz := D.chordPos_one_lt i'.rev
      have hzl := D.chordPos_le i'.rev
      omega
    | cast j' =>
      simp only [route, Fin.lastCases_castSucc, chordRoute_length]
      have hij' : i' < j' := by simpa using hij
      have hrev : j'.rev < i'.rev := Fin.rev_lt_rev.mpr hij'
      have hz := D.chordPos_strictMono hrev
      have hi := D.chordPos_le i'.rev
      have hj := D.chordPos_le j'.rev
      omega

/-! ## Cycle arcs -/

/-- The forward arc between two positions in the chosen linear presentation
of the cycle. -/
def forwardArc (i : Fin p) :
    G.Walk (D.longestCycle.cycle.getVert (D.aPos i))
      (D.longestCycle.cycle.getVert D.bPos) :=
  (((D.longestCycle.cycle.drop (D.aPos i)).take
      (D.bPos - D.aPos i))).copy rfl (by
        rw [SimpleGraph.Walk.drop_getVert]
        have hab := D.aPos_lt_bPos i
        congr 1
        omega)

@[simp] lemma forwardArc_length (i : Fin p) :
    (D.forwardArc i).length = D.bPos - D.aPos i := by
  simp only [forwardArc, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
  have ha := D.aPos_lt_bPos i
  have hb := D.bPos_le
  omega

lemma forwardArc_isPath (i : Fin p) : (D.forwardArc i).IsPath := by
  rw [forwardArc, SimpleGraph.Walk.isPath_copy]
  apply (D.longestCycle.isCycle.isPath_drop (D.aPos_pos i)).take

/-- The complementary arc, with the same orientation of its endpoints. -/
def complementaryArc (i : Fin p) :
    G.Walk (D.longestCycle.cycle.getVert (D.aPos i))
      (D.longestCycle.cycle.getVert D.bPos) :=
  ((D.longestCycle.cycle.drop D.bPos).append
      (D.longestCycle.cycle.take (D.aPos i))).reverse

@[simp] lemma complementaryArc_length (i : Fin p) :
    (D.complementaryArc i).length =
      D.longestCycle.cycle.length - D.bPos + D.aPos i := by
  simp [complementaryArc,
    (D.aPos_lt_bPos i).le.trans D.bPos_le]
  omega

lemma path_endpoints_ne : D.aVertex ≠ D.bVertex := by
  intro hab
  have heq : D.path.getVert D.path.length = D.aVertex := by
    simp [hab]
  have hidx := (D.path_isPath.getVert_eq_start_iff (i := D.path.length)
    (by omega)).mp heq
  exact (Nat.ne_of_gt D.path_positive) hidx

lemma aVertex_not_cycle : D.aVertex ∉ D.longestCycle.cycle.support :=
  D.path_avoids_cycle D.path.start_mem_support

lemma bVertex_not_cycle : D.bVertex ∉ D.longestCycle.cycle.support :=
  D.path_avoids_cycle D.path.end_mem_support

lemma forwardArc_support_subset (i : Fin p) :
    ∀ {v : V}, v ∈ (D.forwardArc i).support →
      v ∈ D.longestCycle.cycle.support := by
  intro v hv
  rw [forwardArc, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_take] at hv
  have hvdrop : v ∈ (D.longestCycle.cycle.drop (D.aPos i)).support :=
    List.mem_of_mem_take hv
  rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hvdrop
  exact List.mem_of_mem_drop hvdrop

lemma complementaryArc_isPath (i : Fin p) : (D.complementaryArc i).IsPath := by
  rw [complementaryArc, SimpleGraph.Walk.isPath_reverse_iff,
    SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  have hdrop := D.longestCycle.isCycle.isPath_drop (by
    have := D.aPos_lt_bPos i
    omega : 0 < D.bPos)
  have htake := D.longestCycle.isCycle.isPath_take
    ((D.aPos_lt_bPos i).trans_le D.bPos_le)
  refine ⟨hdrop.support_nodup, htake.support_nodup.tail, ?_⟩
  intro v hvdrop hvtake
  obtain ⟨n, hnEq, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvdrop
  obtain ⟨m, hmEq, hmle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (List.mem_of_mem_tail hvtake)
  have hm0 : m ≠ 0 := by
    intro hm0
    subst m
    have hvstart : (D.longestCycle.cycle.take (D.aPos i)).getVert 0 ∈
        (D.longestCycle.cycle.take (D.aPos i)).support.tail := by
      simpa [hmEq] using hvtake
    have hn := htake.support_nodup
    rw [← (D.longestCycle.cycle.take (D.aPos i)).cons_tail_support] at hn
    exact hn.notMem (by simpa using hvstart)
  have hnBound : D.bPos + n ≤ D.longestCycle.cycle.length := by
    rw [SimpleGraph.Walk.drop_length] at hnle
    have hb := D.bPos_le
    omega
  have hmBound : m ≤ D.aPos i := by
    rw [SimpleGraph.Walk.take_length,
      Nat.min_eq_left ((D.aPos_lt_bPos i).le.trans D.bPos_le)] at hmle
    exact hmle
  have hget : D.longestCycle.cycle.getVert (D.bPos + n) =
      D.longestCycle.cycle.getVert m := by
    calc
      _ = (D.longestCycle.cycle.drop D.bPos).getVert n := by
        rw [SimpleGraph.Walk.drop_getVert]
      _ = v := hnEq
      _ = (D.longestCycle.cycle.take (D.aPos i)).getVert m := hmEq.symm
      _ = _ := by
        rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hmBound]
  have hindices := D.longestCycle.isCycle.getVert_injOn
    (by
      simp only [Set.mem_ofPred_eq]
      have hb : 0 < D.bPos := by have := D.aPos_lt_bPos i; omega
      exact ⟨by omega, hnBound⟩)
    (by
      simp only [Set.mem_ofPred_eq]
      exact ⟨Nat.one_le_iff_ne_zero.mpr hm0,
        hmBound.trans ((D.aPos_lt_bPos i).le.trans D.bPos_le)⟩) hget
  have hba := D.aPos_lt_bPos i
  omega

lemma complementaryArc_support_subset (i : Fin p) :
    ∀ {v : V}, v ∈ (D.complementaryArc i).support →
      v ∈ D.longestCycle.cycle.support := by
  intro v hv
  have hv' : v ∈ (D.longestCycle.cycle.take (D.aPos i)).support ∨
      v ∈ (D.longestCycle.cycle.drop D.bPos).support := by
    simpa [complementaryArc, SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.mem_support_append_iff] using hv
  rcases hv' with hv' | hv'
  · rw [SimpleGraph.Walk.support_take] at hv'
    exact List.mem_of_mem_take hv'
  · rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hv'
    exact List.mem_of_mem_drop hv'

/-! ## Gluing a route to a cycle arc -/

/-- Add the two endpoint edges to a cycle arc. -/
def attachmentPath (i : Fin p)
    (arc : G.Walk (D.longestCycle.cycle.getVert (D.aPos i))
      (D.longestCycle.cycle.getVert D.bPos)) :
    G.Walk D.aVertex D.bVertex :=
  (arc.cons (D.a_adj_cycle i)).concat D.bPos_adj.symm

@[simp] lemma attachmentPath_length (i : Fin p)
    (arc : G.Walk (D.longestCycle.cycle.getVert (D.aPos i))
      (D.longestCycle.cycle.getVert D.bPos)) :
    (D.attachmentPath i arc).length = arc.length + 2 := by
  simp [attachmentPath]

lemma attachmentPath_isPath (i : Fin p)
    (arc : G.Walk (D.longestCycle.cycle.getVert (D.aPos i))
      (D.longestCycle.cycle.getVert D.bPos))
    (harc : arc.IsPath)
    (hsub : ∀ {v : V}, v ∈ arc.support →
      v ∈ D.longestCycle.cycle.support) :
    (D.attachmentPath i arc).IsPath := by
  rw [attachmentPath, SimpleGraph.Walk.concat_isPath_iff,
    SimpleGraph.Walk.cons_isPath_iff]
  refine ⟨⟨harc, ?_⟩, ?_⟩
  · intro hA
    exact D.aVertex_not_cycle (hsub hA)
  · simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
    rintro (hBA | hB)
    · exact D.path_endpoints_ne hBA.symm
    · exact D.bVertex_not_cycle (hsub hB)

/-- Close an exterior route using an attachment arc through the cycle. -/
def gluedCycle (r : Fin (q + 1)) (i : Fin p)
    (arc : G.Walk (D.longestCycle.cycle.getVert (D.aPos i))
      (D.longestCycle.cycle.getVert D.bPos)) :
    G.Walk D.aVertex D.aVertex :=
  (D.attachmentPath i arc).append (D.route r).reverse

@[simp] lemma gluedCycle_length (r : Fin (q + 1)) (i : Fin p)
    (arc : G.Walk (D.longestCycle.cycle.getVert (D.aPos i))
      (D.longestCycle.cycle.getVert D.bPos)) :
    (D.gluedCycle r i arc).length = (D.route r).length + arc.length + 2 := by
  simp [gluedCycle, Nat.add_comm, Nat.add_left_comm]

lemma gluedCycle_isCycle (r : Fin (q + 1)) (i : Fin p)
    (arc : G.Walk (D.longestCycle.cycle.getVert (D.aPos i))
      (D.longestCycle.cycle.getVert D.bPos))
    (harc : arc.IsPath)
    (hsub : ∀ {v : V}, v ∈ arc.support →
      v ∈ D.longestCycle.cycle.support) :
    (D.gluedCycle r i arc).IsCycle := by
  have hatt := D.attachmentPath_isPath i arc harc hsub
  have hr := (D.route_isPath r).reverse
  apply hatt.isCycle_append hr
  · intro v hvatt hvr
    have hvr' : v ∈ (D.route r).support := by
      have : v ∈ (D.route r).reverse.support := List.mem_of_mem_tail hvr
      simpa [SimpleGraph.Walk.support_reverse] using this
    have hvattAll : v = D.aVertex ∨ v ∈ arc.support ∨ v = D.bVertex := by
      have : v ∈ (D.attachmentPath i arc).support := List.mem_of_mem_tail hvatt
      simpa [attachmentPath, SimpleGraph.Walk.support_concat,
        SimpleGraph.Walk.support_cons] using this
    have hvneA : v ≠ D.aVertex := by
      have hnodup := hatt.support_nodup
      rw [← (D.attachmentPath i arc).cons_tail_support] at hnodup
      exact fun h ↦ hnodup.notMem (h ▸ hvatt)
    have hvatt' : v ∈ arc.support ∨ v = D.bVertex := by
      rcases hvattAll with hA | hrest
      · exact (hvneA hA).elim
      · exact hrest
    rcases hvatt' with hvArc | rfl
    · exact D.route_avoids_cycle r hvr' (hsub hvArc)
    · have hnodup := (D.route_isPath r).reverse.support_nodup
      have hstart : D.bVertex ∉ (D.route r).reverse.support.tail := by
        rw [← (D.route r).reverse.cons_tail_support] at hnodup
        exact hnodup.notMem
      exact hstart hvr
  · left
    simp [attachmentPath]

lemma forwardGlued_isCycle (r : Fin (q + 1)) (i : Fin p) :
    (D.gluedCycle r i (D.forwardArc i)).IsCycle :=
  D.gluedCycle_isCycle r i _ (D.forwardArc_isPath i)
    (D.forwardArc_support_subset i)

lemma complementaryGlued_isCycle (r : Fin (q + 1)) (i : Fin p) :
    (D.gluedCycle r i (D.complementaryArc i)).IsCycle :=
  D.gluedCycle_isCycle r i _ (D.complementaryArc_isPath i)
    (D.complementaryArc_support_subset i)

/-! ## The concrete endpoint geometry -/

/-- Forget only the derivation of the routes, retaining exactly the geometry
consumed by `EndpointCountData`. -/
def toGeometry : EC.EndpointGeometry G p q where
  longestCycle := D.longestCycle
  aVertex := D.aVertex
  bVertex := D.bVertex
  path := D.path
  path_isPath := D.path_isPath
  path_positive := D.path_positive
  path_avoids_cycle := D.path_avoids_cycle
  chordPos := D.chordPos
  chordPos_strictMono := D.chordPos_strictMono
  chordPos_pos := fun i ↦ (D.chordPos_one_lt i).trans' Nat.zero_lt_one
  chordPos_le := D.chordPos_le
  chord_adj := D.chord_adj
  routes := D.route
  routes_isPath := D.route_isPath
  routes_avoid_cycle := D.route_avoids_cycle
  routes_length_strictMono := D.route_length_strictMono
  aPos := D.aPos
  aPos_strictMono := D.aPos_strictMono
  bPos := D.bPos
  aPos_lt_bPos := D.aPos_lt_bPos
  bPos_le := D.bPos_le
  a_adj_cycle := D.a_adj_cycle
  b_adj_cycle := D.bPos_adj

@[simp] lemma toGeometry_arcOffset (i : Fin p) :
    (D.toGeometry.arcOffset i) = D.bPos - D.aPos i + 2 := rfl

lemma toGeometry_arcOffset_injective :
    Function.Injective D.toGeometry.arcOffset := by
  intro i j hij
  have hi := D.aPos_lt_bPos i
  have hj := D.aPos_lt_bPos j
  simp only [toGeometry_arcOffset] at hij
  apply D.aPos_strictMono.injective
  omega

/-! ## A complete application when there are no path chords -/

/-- The larger of the two arc-parity classes, selected canonically. -/
def majorityArcSet (D : EndpointConfiguration G p q) : Finset (Fin p) := by
  classical
  exact if D.toGeometry.oddArcCount ≤ D.toGeometry.evenArcCount then
    Finset.univ.filter fun i ↦ Even (D.toGeometry.arcOffset i)
  else
    Finset.univ.filter fun i ↦ Odd (D.toGeometry.arcOffset i)

lemma card_majorityArcSet (D : EndpointConfiguration G p q) :
    D.majorityArcSet.card =
      max D.toGeometry.evenArcCount D.toGeometry.oddArcCount := by
  classical
  by_cases h : D.toGeometry.oddArcCount ≤ D.toGeometry.evenArcCount
  · simp only [majorityArcSet, if_pos h]
    change D.toGeometry.evenArcCount =
      max D.toGeometry.evenArcCount D.toGeometry.oddArcCount
    exact (max_eq_left h).symm
  · have h' : D.toGeometry.evenArcCount < D.toGeometry.oddArcCount :=
      Nat.lt_of_not_ge h
    simp only [majorityArcSet, if_neg h]
    change D.toGeometry.oddArcCount =
      max D.toGeometry.evenArcCount D.toGeometry.oddArcCount
    exact (max_eq_right h'.le).symm

/-- Ordered enumeration of the selected majority parity class. -/
def majorityArc (D : EndpointConfiguration G p q) :
    Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount) → Fin p :=
  fun i ↦ ↑(D.majorityArcSet.orderIsoOfFin D.card_majorityArcSet i)

lemma majorityArc_injective (D : EndpointConfiguration G p q) :
    Function.Injective D.majorityArc := by
  intro i j hij
  apply (D.majorityArcSet.orderIsoOfFin D.card_majorityArcSet).injective
  exact Subtype.ext hij

lemma majorityArc_mem (D : EndpointConfiguration G p q)
    (i : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    D.majorityArc i ∈ D.majorityArcSet :=
  (D.majorityArcSet.orderIsoOfFin D.card_majorityArcSet i).property

lemma majorityArc_odd_iff (D : EndpointConfiguration G p q)
    (i j : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    Odd (D.toGeometry.arcOffset (D.majorityArc i)) ↔
      Odd (D.toGeometry.arcOffset (D.majorityArc j)) := by
  classical
  have hi := D.majorityArc_mem i
  have hj := D.majorityArc_mem j
  by_cases h : D.toGeometry.oddArcCount ≤ D.toGeometry.evenArcCount
  · rw [majorityArcSet, if_pos h] at hi hj
    exact iff_of_false
      (Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hi).2)
      (Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hj).2)
  · rw [majorityArcSet, if_neg h] at hi hj
    exact iff_of_true (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

lemma complementaryOffset_odd_iff_not_arcOffset
    (D : EndpointConfiguration G p q) (i : Fin p) :
    Odd ((D.complementaryArc i).length + 2) ↔
      ¬ Odd (D.toGeometry.arcOffset i) := by
  have hsum :
      ((D.complementaryArc i).length + 2) + D.toGeometry.arcOffset i =
        D.longestCycle.cycle.length + 4 := by
    simp only [complementaryArc_length, toGeometry_arcOffset]
    have hi := D.aPos_lt_bPos i
    have hb := D.bPos_le
    omega
  have hodd : Odd (((D.complementaryArc i).length + 2) +
      D.toGeometry.arcOffset i) := by
    rw [hsum]
    obtain ⟨t, ht⟩ := D.longestCycle.odd_length
    exact ⟨t + 2, by omega⟩
  rw [Nat.odd_add] at hodd
  exact hodd.trans Nat.not_odd_iff_even.symm

/-- Orientation compatibility needed in the zero-chord application: the
selected majority arcs close the unique exterior route with odd length.
Reversing the odd cycle swaps its two arc-parity classes. -/
def MajorityCompatible (D : EndpointConfiguration G p 0) : Prop :=
  ∀ i ∈ D.majorityArcSet,
    Odd ((D.route (0 : Fin 1)).length + D.toGeometry.arcOffset i)

def noChordSplicingBlock (D : EndpointConfiguration G p 0)
    (hcompat : D.MajorityCompatible) :
    Erdos58.EndpointCount.SplicingBlock G D.longestCycle 0 1
      (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount) where
  small := Fin.elim0
  row := fun _ ↦ (D.route (0 : Fin 1)).length
  col := fun i ↦ D.toGeometry.arcOffset (D.majorityArc i)
  small_injective := fun i ↦ Fin.elim0 i
  row_injective := by intro i j _; exact Subsingleton.elim i j
  col_injective := D.toGeometry_arcOffset_injective.comp D.majorityArc_injective
  small_mem := fun i ↦ Fin.elim0 i
  sum_mem := by
    intro _ j
    have hodd := hcompat (D.majorityArc j) (D.majorityArc_mem j)
    refine ⟨hodd, D.aVertex,
      D.gluedCycle (0 : Fin 1) (D.majorityArc j)
        (D.forwardArc (D.majorityArc j)),
      D.forwardGlued_isCycle (0 : Fin 1) (D.majorityArc j), ?_⟩
    simp only [gluedCycle_length, forwardArc_length, toGeometry_arcOffset]
    omega
  complement := fun i ↦ Fin.elim0 i
  complement_mem := fun i ↦ Fin.elim0 i
  complement_long_of_not_lt := fun i ↦ Fin.elim0 i

def noChordEndpointCountData (D : EndpointConfiguration G p 0)
    (hcompat : D.MajorityCompatible) : EC.EndpointCountData G p 0 where
  toGeometry := D.toGeometry
  a := 0
  b := 1
  path_partition := by omega
  row_nonempty := by omega
  majoritySplicing := D.noChordSplicingBlock hcompat
  tailLength := 0
  smallRoute := Fin.elim0
  smallRoute_injective := fun i ↦ Fin.elim0 i
  rowRoute := fun _ ↦ 0
  rowRoute_injective := by intro i j _; exact Subsingleton.elim i j
  route_classes_disjoint := fun i ↦ Fin.elim0 i
  small_eq_route_cycle := fun i ↦ Fin.elim0 i
  row_eq_route_length := by intro i; fin_cases i; rfl
  majorityArc := D.majorityArc
  majorityArc_injective := D.majorityArc_injective
  majorityArc_parity := by
    intro i
    have hi := D.majorityArc_mem i
    constructor
    · intro hle
      rw [majorityArcSet, if_pos hle] at hi
      exact (Finset.mem_filter.mp hi).2
    · intro hlt
      have hnle : ¬ D.toGeometry.oddArcCount ≤ D.toGeometry.evenArcCount :=
        Nat.not_le.mpr hlt
      rw [majorityArcSet, if_neg hnle] at hi
      exact (Finset.mem_filter.mp hi).2
  col_eq_arc_offset := fun _ ↦ rfl

/-- Actual `endpoint_count` application for a longest exterior path whose
initial endpoint has no additional chord on that path. -/
theorem endpoint_count_no_path_chords [Finite V]
    (D : EndpointConfiguration G p 0) (hcompat : D.MajorityCompatible)
    (hp : 0 < p) :
    Erdos58.EndpointCount.ceilHalf p ≤ (oddCycleLengths G).ncard := by
  simpa using Erdos58.EndpointCount.endpoint_count
    (D.noChordEndpointCountData hcompat) hp

lemma complementaryGlued_odd_of_not_compatible
    (D : EndpointConfiguration G p 0) (hcompat : ¬ D.MajorityCompatible)
    (j : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    Odd (D.gluedCycle (0 : Fin 1) (D.majorityArc j)
      (D.complementaryArc (D.majorityArc j))).length := by
  classical
  rw [MajorityCompatible] at hcompat
  push Not at hcompat
  obtain ⟨i, hi, hnot⟩ := hcompat
  have hi' : i = D.majorityArc
      ((D.majorityArcSet.orderIsoOfFin D.card_majorityArcSet).symm ⟨i, hi⟩) := by
    exact congrArg Subtype.val
      ((D.majorityArcSet.orderIsoOfFin D.card_majorityArcSet).apply_symm_apply ⟨i, hi⟩).symm
  let i' := (D.majorityArcSet.orderIsoOfFin D.card_majorityArcSet).symm ⟨i, hi⟩
  have hsame :
      Odd (D.toGeometry.arcOffset i) ↔
        Odd (D.toGeometry.arcOffset (D.majorityArc j)) := by
    rw [hi']
    exact D.majorityArc_odd_iff i' j
  have hnotj : ¬ Odd ((D.route (0 : Fin 1)).length +
      D.toGeometry.arcOffset (D.majorityArc j)) := by
    intro hj
    apply hnot
    rw [Nat.odd_add] at hj ⊢
    have hei : Even (D.toGeometry.arcOffset i) ↔
        ¬ Odd (D.toGeometry.arcOffset i) := Nat.not_odd_iff_even.symm
    have hej : Even (D.toGeometry.arcOffset (D.majorityArc j)) ↔
        ¬ Odd (D.toGeometry.arcOffset (D.majorityArc j)) :=
      Nat.not_odd_iff_even.symm
    tauto
  have hopp := D.complementaryOffset_odd_iff_not_arcOffset (D.majorityArc j)
  rw [gluedCycle_length]
  have htarget : Odd ((D.route (0 : Fin 1)).length +
      ((D.complementaryArc (D.majorityArc j)).length + 2)) := by
    rw [Nat.odd_add] at hnotj ⊢
    have het : Even (D.toGeometry.arcOffset (D.majorityArc j)) ↔
        ¬ Odd (D.toGeometry.arcOffset (D.majorityArc j)) :=
      Nat.not_odd_iff_even.symm
    have hec : Even ((D.complementaryArc (D.majorityArc j)).length + 2) ↔
        ¬ Odd ((D.complementaryArc (D.majorityArc j)).length + 2) :=
      Nat.not_odd_iff_even.symm
    tauto
  simpa [Nat.add_assoc] using htarget

def noChordComplementBlock (D : EndpointConfiguration G p 0)
    (hcompat : ¬ D.MajorityCompatible) :
    EC.LengthBlock G 0 1
      (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount) where
  small := Fin.elim0
  row := fun _ ↦ (D.route (0 : Fin 1)).length
  col := fun i ↦ (D.complementaryArc (D.majorityArc i)).length + 2
  small_injective := fun i ↦ Fin.elim0 i
  row_injective := by intro i j _; exact Subsingleton.elim i j
  col_injective := by
    intro i j hij
    simp only [complementaryArc_length] at hij
    have hb := D.bPos_le
    have hai := D.aPos_lt_bPos (D.majorityArc i)
    have haj := D.aPos_lt_bPos (D.majorityArc j)
    apply D.majorityArc_injective
    apply D.aPos_strictMono.injective
    omega
  small_mem := fun i ↦ Fin.elim0 i
  sum_mem := by
    intro _ j
    have hodd : Odd ((D.route (0 : Fin 1)).length +
        ((D.complementaryArc (D.majorityArc j)).length + 2)) := by
      simpa [gluedCycle_length, Nat.add_assoc] using
        D.complementaryGlued_odd_of_not_compatible hcompat j
    refine ⟨hodd,
      D.aVertex,
      D.gluedCycle (0 : Fin 1) (D.majorityArc j)
        (D.complementaryArc (D.majorityArc j)),
      D.complementaryGlued_isCycle (0 : Fin 1) (D.majorityArc j), ?_⟩
    simp [gluedCycle_length, Nat.add_comm, Nat.add_left_comm]
  separated := fun i ↦ Fin.elim0 i

/-- The zero-path-chord endpoint bound with no orientation certificate.
If the displayed orientation is compatible, this is the genuine
`EndpointCountData` application above.  Otherwise the complementary arc at
every selected attachment is odd, and the corresponding actual glued cycles
give the same cardinality bound directly. -/
theorem endpoint_count_no_path_chords_unconditional [Finite V]
    (D : EndpointConfiguration G p 0) (hp : 0 < p) :
    Erdos58.EndpointCount.ceilHalf p ≤ (oddCycleLengths G).ncard := by
  classical
  by_cases hcompat : D.MajorityCompatible
  · exact D.endpoint_count_no_path_chords hcompat hp
  · have hc : 0 < max D.toGeometry.evenArcCount D.toGeometry.oddArcCount := by
      have hpart := D.toGeometry.evenArcCount_add_oddArcCount
      omega
    have hblock := Erdos58.EndpointCount.lengthBlock_lower_bound
      (D.noChordComplementBlock hcompat) (by omega) hc
    have hceil : Erdos58.EndpointCount.ceilHalf p ≤
        max D.toGeometry.evenArcCount D.toGeometry.oddArcCount := by
      have hpart := D.toGeometry.evenArcCount_add_oddArcCount
      simp only [Erdos58.EndpointCount.ceilHalf]
      omega
    omega

/-! ## Short cycles cut off by the last path chord (`q > 0`) -/

/-- The final chord position in path order. -/
def lastChord (_D : EndpointConfiguration G p q) (hq : 0 < q) : Fin q :=
  ⟨q - 1, by omega⟩

def tailLength (D : EndpointConfiguration G p q) (hq : 0 < q) : ℕ :=
  D.path.length - D.chordPos (D.lastChord hq)

lemma zero_rev_eq_lastChord (D : EndpointConfiguration G p q) (hq : 0 < q) :
    (⟨0, hq⟩ : Fin q).rev = D.lastChord hq := by
  ext
  simp [lastChord, Fin.rev]

/-- The path segment from a chord position to the final chord position. -/
def pathSegment (D : EndpointConfiguration G p q) (hq : 0 < q) (i : Fin q) :
    G.Walk (D.path.getVert (D.chordPos i))
      (D.path.getVert (D.chordPos (D.lastChord hq))) :=
  (((D.path.drop (D.chordPos i)).take
      (D.chordPos (D.lastChord hq) - D.chordPos i))).copy rfl (by
        rw [SimpleGraph.Walk.drop_getVert]
        have hi : i ≤ D.lastChord hq := by
          simp only [Fin.le_iff_val_le_val, lastChord]
          omega
        have hz := D.chordPos_strictMono.monotone hi
        congr 1
        omega)

@[simp] lemma pathSegment_length (D : EndpointConfiguration G p q)
    (hq : 0 < q) (i : Fin q) :
    (D.pathSegment hq i).length =
      D.chordPos (D.lastChord hq) - D.chordPos i := by
  simp only [pathSegment, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
  have hi : i ≤ D.lastChord hq := by
    simp only [Fin.le_iff_val_le_val, lastChord]
    omega
  have hz := D.chordPos_strictMono.monotone hi
  have hlast := D.chordPos_le (D.lastChord hq)
  have hzlen := D.chordPos_le i
  omega

lemma pathSegment_isPath (D : EndpointConfiguration G p q)
    (hq : 0 < q) (i : Fin q) : (D.pathSegment hq i).IsPath := by
  rw [pathSegment, SimpleGraph.Walk.isPath_copy]
  exact (D.path_isPath.drop (D.chordPos i)).take _

lemma aVertex_not_mem_path_drop (D : EndpointConfiguration G p q) (i : Fin q) :
    D.aVertex ∉ (D.path.drop (D.chordPos i)).support := by
  intro hA
  rw [SimpleGraph.Walk.drop_support_eq_support_drop_min,
    Nat.min_eq_left (D.chordPos_le i), ← D.path.cons_tail_support] at hA
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by
    have := D.chordPos_one_lt i
    omega : D.chordPos i ≠ 0)
  rw [hn] at hA
  simp only [List.drop_succ_cons] at hA
  have hnodup := D.path_isPath.support_nodup
  rw [← D.path.cons_tail_support] at hnodup
  exact hnodup.notMem (List.mem_of_mem_drop hA)

/-- The `A`--last-chord prefix determined by a route.  For the original
route this is the ordinary path prefix; for a chord route it starts with the
chord and continues along the corresponding path segment. -/
def shortPrefix (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Fin (q + 1) → G.Walk D.aVertex
      (D.path.getVert (D.chordPos (D.lastChord hq))) :=
  Fin.lastCases (D.path.take (D.chordPos (D.lastChord hq)))
    (fun i : Fin q ↦ (D.pathSegment hq i.rev).cons (D.chord_adj i.rev))

lemma shortPrefix_isPath (D : EndpointConfiguration G p q) (hq : 0 < q)
    (r : Fin (q + 1)) : (D.shortPrefix hq r).IsPath := by
  induction r using Fin.lastCases with
  | last =>
    simp only [shortPrefix, Fin.lastCases_last]
    exact D.path_isPath.take _
  | cast i =>
    simp only [shortPrefix, Fin.lastCases_castSucc]
    apply (SimpleGraph.Walk.cons_isPath_iff _ _).mpr
    refine ⟨D.pathSegment_isPath hq i.rev, ?_⟩
    intro hA
    rw [pathSegment, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_take] at hA
    exact D.aVertex_not_mem_path_drop i.rev (List.mem_of_mem_take hA)

@[simp] lemma shortPrefix_length (D : EndpointConfiguration G p q)
    (hq : 0 < q) (r : Fin (q + 1)) :
    (D.shortPrefix hq r).length =
      (D.route r).length - D.tailLength hq := by
  induction r using Fin.lastCases with
  | last =>
    simp only [shortPrefix, route, Fin.lastCases_last,
      SimpleGraph.Walk.take_length, tailLength]
    have hz := D.chordPos_le (D.lastChord hq)
    omega
  | cast i =>
    simp only [shortPrefix, route, Fin.lastCases_castSucc,
      SimpleGraph.Walk.length_cons, pathSegment_length, chordRoute_length,
      tailLength]
    have hi : i.rev ≤ D.lastChord hq := by
      simp only [Fin.le_iff_val_le_val, lastChord]
      omega
    have hz := D.chordPos_strictMono.monotone hi
    have hil := D.chordPos_le i.rev
    have hlast := D.chordPos_le (D.lastChord hq)
    omega

/-- Close a short prefix with the final chord. -/
def shortCycle (D : EndpointConfiguration G p q) (hq : 0 < q)
    (r : Fin (q + 1)) : G.Walk D.aVertex D.aVertex :=
  SimpleGraph.Walk.cons (D.chord_adj (D.lastChord hq))
    (D.shortPrefix hq r).reverse

@[simp] lemma shortCycle_length (D : EndpointConfiguration G p q)
    (hq : 0 < q) (r : Fin (q + 1)) :
    (D.shortCycle hq r).length =
      (D.route r).length - D.tailLength hq + 1 := by
  simp [shortCycle, shortPrefix_length]

lemma route_zero_length (D : EndpointConfiguration G p q) (hq : 0 < q) :
    (D.route (0 : Fin (q + 1))).length = D.tailLength hq + 1 := by
  have hcast : (0 : Fin (q + 1)) = (⟨0, hq⟩ : Fin q).castSucc := rfl
  rw [hcast]
  simp only [route, Fin.lastCases_castSucc, chordRoute_length, tailLength,
    D.zero_rev_eq_lastChord hq]
  have hz := D.chordPos_le (D.lastChord hq)
  omega

lemma two_le_shortCycle_length (D : EndpointConfiguration G p q) (hq : 0 < q)
    (r : Fin (q + 1)) : 2 ≤ (D.shortCycle hq r).length := by
  rw [shortCycle_length]
  have hmono := D.route_length_strictMono.monotone (Fin.zero_le r)
  rw [D.route_zero_length hq] at hmono
  omega

lemma closePath_isCycle {a z : V} (P : G.Walk a z) (hP : P.IsPath)
    (h : G.Adj a z) (hlen : 1 < P.length) :
    (SimpleGraph.Walk.cons h P.reverse).IsCycle := by
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨hP.reverse, ?_⟩
  intro he
  have he' : s(a, z) ∈ P.edges := by
    simpa [SimpleGraph.Walk.edges_reverse] using he
  exact (Nat.ne_of_gt hlen) (hP.length_eq_one_of_mem_edges he')

lemma shortCycle_isCycle_of_odd (D : EndpointConfiguration G p q) (hq : 0 < q)
    (r : Fin (q + 1)) (hodd : Odd (D.shortCycle hq r).length) :
    (D.shortCycle hq r).IsCycle := by
  apply closePath_isCycle (D.shortPrefix hq r) (D.shortPrefix_isPath hq r)
    (D.chord_adj (D.lastChord hq))
  have htwo := D.two_le_shortCycle_length hq r
  have hthree : 3 ≤ (D.shortCycle hq r).length := by
    rcases hodd with ⟨t, ht⟩
    omega
  rw [shortCycle, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_reverse] at hthree
  omega

@[simp] lemma shortCycle_zero_length (D : EndpointConfiguration G p q)
    (hq : 0 < q) :
    (D.shortCycle hq (0 : Fin (q + 1))).length = 2 := by
  rw [shortCycle_length, D.route_zero_length hq]
  omega

lemma shortCycle_length_strictMono (D : EndpointConfiguration G p q)
    (hq : 0 < q) : StrictMono fun r : Fin (q + 1) ↦
      (D.shortCycle hq r).length := by
  intro i j hij
  dsimp
  rw [shortCycle_length, shortCycle_length]
  have hroute := D.route_length_strictMono hij
  have hi := D.route_length_strictMono.monotone (Fin.zero_le i)
  have hj := D.route_length_strictMono.monotone (Fin.zero_le j)
  change (D.route (0 : Fin (q + 1))).length ≤ (D.route i).length at hi
  change (D.route (0 : Fin (q + 1))).length ≤ (D.route j).length at hj
  rw [D.route_zero_length hq] at hi hj
  have htail : D.tailLength hq ≤ (D.route i).length := by omega
  exact Nat.add_lt_add_right (Nat.sub_lt_sub_right htail hroute) 1

/-- Routes whose last-chord short cycle has odd length. -/
def smallRouteSet (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Finset (Fin (q + 1)) := by
  classical
  exact Finset.univ.filter fun r ↦ Odd (D.shortCycle hq r).length

/-- The complementary (even-short-cycle) route class. -/
def rowRouteSet (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Finset (Fin (q + 1)) := by
  classical
  exact Finset.univ.filter fun r ↦ ¬ Odd (D.shortCycle hq r).length

lemma card_smallRouteSet_add_card_rowRouteSet
    (D : EndpointConfiguration G p q) (hq : 0 < q) :
    (D.smallRouteSet hq).card + (D.rowRouteSet hq).card = q + 1 := by
  classical
  simpa [smallRouteSet, rowRouteSet] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (q + 1))))
      (fun r ↦ Odd (D.shortCycle hq r).length))

def smallRoute (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Fin (D.smallRouteSet hq).card → Fin (q + 1) :=
  fun i ↦ ↑((D.smallRouteSet hq).orderIsoOfFin rfl i)

def rowRoute (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Fin (D.rowRouteSet hq).card → Fin (q + 1) :=
  fun i ↦ ↑((D.rowRouteSet hq).orderIsoOfFin rfl i)

lemma smallRoute_injective (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Function.Injective (D.smallRoute hq) := by
  intro i j hij
  apply ((D.smallRouteSet hq).orderIsoOfFin rfl).injective
  exact Subtype.ext hij

lemma rowRoute_injective (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Function.Injective (D.rowRoute hq) := by
  intro i j hij
  apply ((D.rowRouteSet hq).orderIsoOfFin rfl).injective
  exact Subtype.ext hij

lemma smallRoute_mem (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i : Fin (D.smallRouteSet hq).card) :
    D.smallRoute hq i ∈ D.smallRouteSet hq :=
  ((D.smallRouteSet hq).orderIsoOfFin rfl i).property

lemma rowRoute_mem (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i : Fin (D.rowRouteSet hq).card) :
    D.rowRoute hq i ∈ D.rowRouteSet hq :=
  ((D.rowRouteSet hq).orderIsoOfFin rfl i).property

lemma smallRoute_odd (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i : Fin (D.smallRouteSet hq).card) :
    Odd (D.shortCycle hq (D.smallRoute hq i)).length := by
  classical
  exact (Finset.mem_filter.mp (D.smallRoute_mem hq i)).2

lemma rowRoute_not_odd (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i : Fin (D.rowRouteSet hq).card) :
    ¬ Odd (D.shortCycle hq (D.rowRoute hq i)).length := by
  classical
  exact (Finset.mem_filter.mp (D.rowRoute_mem hq i)).2

lemma rowRouteSet_nonempty (D : EndpointConfiguration G p q) (hq : 0 < q) :
    (D.rowRouteSet hq).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp only [rowRouteSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [D.shortCycle_zero_length hq]
  exact Nat.not_odd_iff_even.mpr even_two

lemma rowRoute_card_pos (D : EndpointConfiguration G p q) (hq : 0 < q) :
    0 < (D.rowRouteSet hq).card :=
  Finset.card_pos.mpr (D.rowRouteSet_nonempty hq)

lemma route_classes_disjoint (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i : Fin (D.smallRouteSet hq).card)
    (j : Fin (D.rowRouteSet hq).card) :
    D.smallRoute hq i ≠ D.rowRoute hq j := by
  intro hij
  have hs := D.smallRoute_odd hq i
  have hr := D.rowRoute_not_odd hq j
  exact hr (hij ▸ hs)

lemma smallLength_injective (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Function.Injective (fun i : Fin (D.smallRouteSet hq).card ↦
      (D.shortCycle hq (D.smallRoute hq i)).length) :=
  (D.shortCycle_length_strictMono hq).injective.comp (D.smallRoute_injective hq)

lemma rowLength_injective (D : EndpointConfiguration G p q) (hq : 0 < q) :
    Function.Injective (fun i : Fin (D.rowRouteSet hq).card ↦
      (D.route (D.rowRoute hq i)).length) :=
  D.route_length_strictMono.injective.comp (D.rowRoute_injective hq)

lemma smallLength_mem (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i : Fin (D.smallRouteSet hq).card) :
    (D.shortCycle hq (D.smallRoute hq i)).length ∈ oddCycleLengths G := by
  exact ⟨D.smallRoute_odd hq i, D.aVertex,
    D.shortCycle hq (D.smallRoute hq i),
    D.shortCycle_isCycle_of_odd hq _ (D.smallRoute_odd hq i), rfl⟩

lemma shortCycle_add_tail (D : EndpointConfiguration G p q) (hq : 0 < q)
    (r : Fin (q + 1)) :
    (D.shortCycle hq r).length + D.tailLength hq =
      (D.route r).length + 1 := by
  rw [shortCycle_length]
  have hr := D.route_length_strictMono.monotone (Fin.zero_le r)
  change (D.route (0 : Fin (q + 1))).length ≤ (D.route r).length at hr
  rw [D.route_zero_length hq] at hr
  omega

lemma rowRoute_odd_iff (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i j : Fin (D.rowRouteSet hq).card) :
    Odd (D.route (D.rowRoute hq i)).length ↔
      Odd (D.route (D.rowRoute hq j)).length := by
  have hei : Even (D.shortCycle hq (D.rowRoute hq i)).length :=
    Nat.not_odd_iff_even.mp (D.rowRoute_not_odd hq i)
  have hej : Even (D.shortCycle hq (D.rowRoute hq j)).length :=
    Nat.not_odd_iff_even.mp (D.rowRoute_not_odd hq j)
  have hi := D.shortCycle_add_tail hq (D.rowRoute hq i)
  have hj := D.shortCycle_add_tail hq (D.rowRoute hq j)
  constructor
  · intro hoi
    by_contra hnoj
    have hoj : Even (D.route (D.rowRoute hq j)).length :=
      Nat.not_odd_iff_even.mp hnoj
    rcases hei with ⟨ei, hei⟩
    rcases hej with ⟨ej, hej⟩
    rcases hoi with ⟨oi, hoi⟩
    rcases hoj with ⟨oj, hoj⟩
    omega
  · intro hoj
    by_contra hnoi
    have hoi : Even (D.route (D.rowRoute hq i)).length :=
      Nat.not_odd_iff_even.mp hnoi
    rcases hei with ⟨ei, hei⟩
    rcases hej with ⟨ej, hej⟩
    rcases hoi with ⟨oi, hoi⟩
    rcases hoj with ⟨oj, hoj⟩
    omega

lemma smallRoute_odd_iff_not_rowRoute_odd
    (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i : Fin (D.smallRouteSet hq).card)
    (j : Fin (D.rowRouteSet hq).card) :
    Odd (D.route (D.smallRoute hq i)).length ↔
      ¬ Odd (D.route (D.rowRoute hq j)).length := by
  have hsi := D.smallRoute_odd hq i
  have hrj : Even (D.shortCycle hq (D.rowRoute hq j)).length :=
    Nat.not_odd_iff_even.mp (D.rowRoute_not_odd hq j)
  have hi := D.shortCycle_add_tail hq (D.smallRoute hq i)
  have hj := D.shortCycle_add_tail hq (D.rowRoute hq j)
  constructor
  · intro hoi hoj
    rcases hsi with ⟨si, hsi⟩
    rcases hrj with ⟨sj, hrj⟩
    rcases hoi with ⟨oi, hoi⟩
    rcases hoj with ⟨oj, hoj⟩
    omega
  · intro hnoj
    by_contra hnoi
    have hoi : Even (D.route (D.smallRoute hq i)).length :=
      Nat.not_odd_iff_even.mp hnoi
    have hoj : Even (D.route (D.rowRoute hq j)).length :=
      Nat.not_odd_iff_even.mp hnoj
    rcases hsi with ⟨si, hsi⟩
    rcases hrj with ⟨sj, hrj⟩
    rcases hoi with ⟨oi, hoi⟩
    rcases hoj with ⟨oj, hoj⟩
    omega

def GeneralCompatible (D : EndpointConfiguration G p q) (hq : 0 < q) : Prop :=
  ∀ i : Fin (D.rowRouteSet hq).card,
    ∀ j : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount),
      Odd ((D.route (D.rowRoute hq i)).length +
        D.toGeometry.arcOffset (D.majorityArc j))

private lemma odd_add_iff_not_odd_add_of_odd_iff_not_odd
    {a b c : ℕ} (h : Odd a ↔ ¬ Odd b) :
    Odd (a + c) ↔ ¬ Odd (b + c) := by
  rw [Nat.odd_add, Nat.odd_add]
  have hea : Even a ↔ ¬ Odd a := Nat.not_odd_iff_even.symm
  have heb : Even b ↔ ¬ Odd b := Nat.not_odd_iff_even.symm
  have hec : Even c ↔ ¬ Odd c := Nat.not_odd_iff_even.symm
  tauto

private lemma odd_add_iff_odd_add_of_odd_iff_of_odd_iff
    {a b c d : ℕ} (hab : Odd a ↔ Odd b) (hcd : Odd c ↔ Odd d) :
    Odd (a + c) ↔ Odd (b + d) := by
  rw [Nat.odd_add, Nat.odd_add]
  have hea : Even a ↔ ¬ Odd a := Nat.not_odd_iff_even.symm
  have heb : Even b ↔ ¬ Odd b := Nat.not_odd_iff_even.symm
  have hec : Even c ↔ ¬ Odd c := Nat.not_odd_iff_even.symm
  have hed : Even d ↔ ¬ Odd d := Nat.not_odd_iff_even.symm
  tauto

lemma forwardSmall_not_odd_of_compatible
    (D : EndpointConfiguration G p q) (hq : 0 < q)
    (hcompat : D.GeneralCompatible hq)
    (i : Fin (D.smallRouteSet hq).card)
    (k : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    ¬ Odd ((D.route (D.smallRoute hq i)).length +
      D.toGeometry.arcOffset (D.majorityArc k)) := by
  let j : Fin (D.rowRouteSet hq).card := ⟨0, D.rowRoute_card_pos hq⟩
  have hrow := hcompat j k
  have hopp := D.smallRoute_odd_iff_not_rowRoute_odd hq i j
  intro hs
  exact (odd_add_iff_not_odd_add_of_odd_iff_not_odd hopp).mp hs hrow

lemma complementarySmall_odd_of_compatible
    (D : EndpointConfiguration G p q) (hq : 0 < q)
    (hcompat : D.GeneralCompatible hq)
    (i : Fin (D.smallRouteSet hq).card)
    (k : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    Odd ((D.route (D.smallRoute hq i)).length +
      ((D.complementaryArc (D.majorityArc k)).length + 2)) := by
  have hf := D.forwardSmall_not_odd_of_compatible hq hcompat i k
  have hc := D.complementaryOffset_odd_iff_not_arcOffset (D.majorityArc k)
  have h := odd_add_iff_not_odd_add_of_odd_iff_not_odd
    (c := (D.route (D.smallRoute hq i)).length) hc
  apply (by simpa [Nat.add_comm] using h :
    Odd ((D.route (D.smallRoute hq i)).length +
      ((D.complementaryArc (D.majorityArc k)).length + 2)) ↔
      ¬ Odd ((D.route (D.smallRoute hq i)).length +
        D.toGeometry.arcOffset (D.majorityArc k))).mpr
  exact hf

lemma arcOffset_add_complementaryOffset (D : EndpointConfiguration G p q)
    (i : Fin p) :
    D.toGeometry.arcOffset i + ((D.complementaryArc i).length + 2) =
      D.longestCycle.cycle.length + 4 := by
  simp only [toGeometry_arcOffset, complementaryArc_length]
  have hi := D.aPos_lt_bPos i
  have hb := D.bPos_le
  omega

def generalSplicingBlock (D : EndpointConfiguration G p q) (hq : 0 < q)
    (hcompat : D.GeneralCompatible hq) :
    Erdos58.EndpointCount.SplicingBlock G D.longestCycle
      (D.smallRouteSet hq).card (D.rowRouteSet hq).card
      (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount) where
  small := fun i ↦ (D.shortCycle hq (D.smallRoute hq i)).length
  row := fun i ↦ (D.route (D.rowRoute hq i)).length
  col := fun k ↦ D.toGeometry.arcOffset (D.majorityArc k)
  small_injective := D.smallLength_injective hq
  row_injective := D.rowLength_injective hq
  col_injective := D.toGeometry_arcOffset_injective.comp D.majorityArc_injective
  small_mem := D.smallLength_mem hq
  sum_mem := by
    intro i k
    refine ⟨hcompat i k, D.aVertex,
      D.gluedCycle (D.rowRoute hq i) (D.majorityArc k)
        (D.forwardArc (D.majorityArc k)),
      D.forwardGlued_isCycle (D.rowRoute hq i) (D.majorityArc k), ?_⟩
    simp only [gluedCycle_length, forwardArc_length, toGeometry_arcOffset]
    omega
  complement := fun i _ k ↦
    (D.gluedCycle (D.smallRoute hq i) (D.majorityArc k)
      (D.complementaryArc (D.majorityArc k))).length
  complement_mem := by
    intro i _ k
    refine ⟨?_, D.aVertex,
      D.gluedCycle (D.smallRoute hq i) (D.majorityArc k)
        (D.complementaryArc (D.majorityArc k)),
      D.complementaryGlued_isCycle (D.smallRoute hq i) (D.majorityArc k), rfl⟩
    rw [gluedCycle_length]
    simpa [Nat.add_assoc] using D.complementarySmall_odd_of_compatible hq hcompat i k
  complement_long_of_not_lt := by
    intro i j k hnot
    have hs := D.shortCycle_add_tail hq (D.smallRoute hq i)
    have hr := D.route_length_strictMono.monotone
      (Fin.zero_le (D.rowRoute hq j))
    change (D.route (0 : Fin (q + 1))).length ≤
      (D.route (D.rowRoute hq j)).length at hr
    rw [D.route_zero_length hq] at hr
    have hsum := D.arcOffset_add_complementaryOffset (D.majorityArc k)
    simp only [gluedCycle_length]
    omega

def generalEndpointCountData (D : EndpointConfiguration G p q) (hq : 0 < q)
    (hcompat : D.GeneralCompatible hq) : EC.EndpointCountData G p q where
  toGeometry := D.toGeometry
  a := (D.smallRouteSet hq).card
  b := (D.rowRouteSet hq).card
  path_partition := D.card_smallRouteSet_add_card_rowRouteSet hq
  row_nonempty := D.rowRoute_card_pos hq
  majoritySplicing := D.generalSplicingBlock hq hcompat
  tailLength := D.tailLength hq
  smallRoute := D.smallRoute hq
  smallRoute_injective := D.smallRoute_injective hq
  rowRoute := D.rowRoute hq
  rowRoute_injective := D.rowRoute_injective hq
  route_classes_disjoint := D.route_classes_disjoint hq
  small_eq_route_cycle := by
    intro i
    simp [generalSplicingBlock, shortCycle_length, toGeometry]
  row_eq_route_length := by
    intro i
    rfl
  majorityArc := D.majorityArc
  majorityArc_injective := D.majorityArc_injective
  majorityArc_parity := by
    intro i
    have hi := D.majorityArc_mem i
    constructor
    · intro hle
      rw [majorityArcSet, if_pos hle] at hi
      exact (Finset.mem_filter.mp hi).2
    · intro hlt
      have hnle : ¬ D.toGeometry.oddArcCount ≤ D.toGeometry.evenArcCount :=
        Nat.not_le.mpr hlt
      rw [majorityArcSet, if_neg hnle] at hi
      exact (Finset.mem_filter.mp hi).2
  col_eq_arc_offset := fun _ ↦ rfl

theorem endpoint_count_positive_path_chords [Finite V]
    (D : EndpointConfiguration G p q) (hq : 0 < q)
    (hcompat : D.GeneralCompatible hq) (hp : 0 < p) :
    Erdos58.EndpointCount.ceilHalf p + q ≤ (oddCycleLengths G).ncard := by
  rw [Erdos58.EndpointCount.ceilHalf_eq_ceilDiv]
  exact Erdos58.EndpointCount.endpoint_count
    (D.generalEndpointCountData hq hcompat) hp

lemma forwardRow_odd_iff (D : EndpointConfiguration G p q) (hq : 0 < q)
    (i j : Fin (D.rowRouteSet hq).card)
    (k l : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    Odd ((D.route (D.rowRoute hq i)).length +
      D.toGeometry.arcOffset (D.majorityArc k)) ↔
    Odd ((D.route (D.rowRoute hq j)).length +
      D.toGeometry.arcOffset (D.majorityArc l)) :=
  odd_add_iff_odd_add_of_odd_iff_of_odd_iff
    (D.rowRoute_odd_iff hq i j) (D.majorityArc_odd_iff k l)

lemma forwardRow_not_odd_of_not_compatible
    (D : EndpointConfiguration G p q) (hq : 0 < q)
    (hcompat : ¬ D.GeneralCompatible hq)
    (i : Fin (D.rowRouteSet hq).card)
    (k : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    ¬ Odd ((D.route (D.rowRoute hq i)).length +
      D.toGeometry.arcOffset (D.majorityArc k)) := by
  classical
  rw [GeneralCompatible] at hcompat
  push Not at hcompat
  obtain ⟨j, l, hnot⟩ := hcompat
  intro hodd
  exact hnot ((D.forwardRow_odd_iff hq i j k l).mp hodd)

lemma complementaryRow_odd_of_not_compatible
    (D : EndpointConfiguration G p q) (hq : 0 < q)
    (hcompat : ¬ D.GeneralCompatible hq)
    (i : Fin (D.rowRouteSet hq).card)
    (k : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    Odd ((D.route (D.rowRoute hq i)).length +
      ((D.complementaryArc (D.majorityArc k)).length + 2)) := by
  have hf := D.forwardRow_not_odd_of_not_compatible hq hcompat i k
  have hc := D.complementaryOffset_odd_iff_not_arcOffset (D.majorityArc k)
  have h := odd_add_iff_not_odd_add_of_odd_iff_not_odd
    (c := (D.route (D.rowRoute hq i)).length) hc
  apply (by simpa [Nat.add_comm] using h :
    Odd ((D.route (D.rowRoute hq i)).length +
      ((D.complementaryArc (D.majorityArc k)).length + 2)) ↔
      ¬ Odd ((D.route (D.rowRoute hq i)).length +
        D.toGeometry.arcOffset (D.majorityArc k))).mpr
  exact hf

lemma forwardSmall_odd_of_not_compatible
    (D : EndpointConfiguration G p q) (hq : 0 < q)
    (hcompat : ¬ D.GeneralCompatible hq)
    (i : Fin (D.smallRouteSet hq).card)
    (k : Fin (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount)) :
    Odd ((D.route (D.smallRoute hq i)).length +
      D.toGeometry.arcOffset (D.majorityArc k)) := by
  let j : Fin (D.rowRouteSet hq).card := ⟨0, D.rowRoute_card_pos hq⟩
  have hrow := D.forwardRow_not_odd_of_not_compatible hq hcompat j k
  have hopp := D.smallRoute_odd_iff_not_rowRoute_odd hq i j
  exact (odd_add_iff_not_odd_add_of_odd_iff_not_odd hopp).mpr hrow

def generalComplementSplicingBlock (D : EndpointConfiguration G p q)
    (hq : 0 < q) (hcompat : ¬ D.GeneralCompatible hq) :
    Erdos58.EndpointCount.SplicingBlock G D.longestCycle
      (D.smallRouteSet hq).card (D.rowRouteSet hq).card
      (max D.toGeometry.evenArcCount D.toGeometry.oddArcCount) where
  small := fun i ↦ (D.shortCycle hq (D.smallRoute hq i)).length
  row := fun i ↦ (D.route (D.rowRoute hq i)).length
  col := fun k ↦ (D.complementaryArc (D.majorityArc k)).length + 2
  small_injective := D.smallLength_injective hq
  row_injective := D.rowLength_injective hq
  col_injective := by
    intro i j hij
    simp only [complementaryArc_length] at hij
    have hb := D.bPos_le
    have hai := D.aPos_lt_bPos (D.majorityArc i)
    have haj := D.aPos_lt_bPos (D.majorityArc j)
    apply D.majorityArc_injective
    apply D.aPos_strictMono.injective
    omega
  small_mem := D.smallLength_mem hq
  sum_mem := by
    intro i k
    refine ⟨D.complementaryRow_odd_of_not_compatible hq hcompat i k,
      D.aVertex,
      D.gluedCycle (D.rowRoute hq i) (D.majorityArc k)
        (D.complementaryArc (D.majorityArc k)),
      D.complementaryGlued_isCycle (D.rowRoute hq i) (D.majorityArc k), ?_⟩
    simp [gluedCycle_length, Nat.add_comm, Nat.add_left_comm]
  complement := fun i _ k ↦
    (D.gluedCycle (D.smallRoute hq i) (D.majorityArc k)
      (D.forwardArc (D.majorityArc k))).length
  complement_mem := by
    intro i _ k
    refine ⟨?_, D.aVertex,
      D.gluedCycle (D.smallRoute hq i) (D.majorityArc k)
        (D.forwardArc (D.majorityArc k)),
      D.forwardGlued_isCycle (D.smallRoute hq i) (D.majorityArc k), rfl⟩
    rw [gluedCycle_length]
    simpa [forwardArc_length, toGeometry_arcOffset, Nat.add_assoc] using
      D.forwardSmall_odd_of_not_compatible hq hcompat i k
  complement_long_of_not_lt := by
    intro i j k hnot
    have hs := D.shortCycle_add_tail hq (D.smallRoute hq i)
    have hr := D.route_length_strictMono.monotone
      (Fin.zero_le (D.rowRoute hq j))
    change (D.route (0 : Fin (q + 1))).length ≤
      (D.route (D.rowRoute hq j)).length at hr
    rw [D.route_zero_length hq] at hr
    have hsum := D.arcOffset_add_complementaryOffset (D.majorityArc k)
    have hfwd : (D.forwardArc (D.majorityArc k)).length + 2 =
        D.toGeometry.arcOffset (D.majorityArc k) := by
      simp only [forwardArc_length, toGeometry_arcOffset]
    simp only [gluedCycle_length]
    omega

/-- The full positive-chord endpoint estimate from the raw configuration.
The two branches correspond to the two orientations of the longest odd
cycle.  The compatible branch is an actual `EndpointCountData` application;
the other branch uses the complementary arcs and the same cancellation
argument directly. -/
theorem endpoint_count_positive_path_chords_unconditional [Finite V]
    (D : EndpointConfiguration G p q) (hq : 0 < q) (hp : 0 < p) :
    Erdos58.EndpointCount.ceilHalf p + q ≤ (oddCycleLengths G).ncard := by
  classical
  by_cases hcompat : D.GeneralCompatible hq
  · exact D.endpoint_count_positive_path_chords hq hcompat hp
  · have hc : 0 < max D.toGeometry.evenArcCount D.toGeometry.oddArcCount := by
      have hpart := D.toGeometry.evenArcCount_add_oddArcCount
      omega
    have hblock := Erdos58.EndpointCount.lengthBlock_lower_bound
      (D.generalComplementSplicingBlock hq hcompat).toLengthBlock
      (D.rowRoute_card_pos hq) hc
    have hpath := D.card_smallRouteSet_add_card_rowRouteSet hq
    have hceil : Erdos58.EndpointCount.ceilHalf p ≤
        max D.toGeometry.evenArcCount D.toGeometry.oddArcCount := by
      have hpart := D.toGeometry.evenArcCount_add_oddArcCount
      simp only [Erdos58.EndpointCount.ceilHalf]
      omega
    omega

/-- Unconditional concrete endpoint counting, for any number of path
chords.  No `EndpointCountData`, parity/orientation certificate, or family
of cycles is an input: every odd cycle used in the proof is built above from
the supplied graph walks and adjacency-derived position enumerations. -/
theorem endpoint_count_from_configuration [Finite V]
    (D : EndpointConfiguration G p q) (hp : 0 < p) :
    Erdos58.EndpointCount.ceilHalf p + q ≤ (oddCycleLengths G).ncard := by
  cases q with
  | zero =>
      simpa using D.endpoint_count_no_path_chords_unconditional hp
  | succ q =>
      exact D.endpoint_count_positive_path_chords_unconditional (by omega) hp

end EndpointConfiguration

end

end Erdos58.Structural.EndpointApplication

#print axioms Erdos58.Structural.EndpointApplication.EndpointConfiguration.endpoint_count_from_configuration
