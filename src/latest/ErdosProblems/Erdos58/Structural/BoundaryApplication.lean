/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos58.Boundary
import ErdosProblems.Erdos58.EndpointCount
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Applying the boundary count to an actual longest cycle and exterior path

`Boundary.lean` deliberately separates the finite length count from the
walk-splicing argument.  This file begins the other half of that interface.
The cycle-neighbour sets below are not abstract sets of natural numbers:
they are the positions on an actual longest odd cycle whose vertices are
adjacent to an endpoint of an actual exterior path.

The theorem `sameNeighborhoodNoChordBoundary` proves the full concrete
equal-neighbour case.  It selects `2 * j` common cycle-neighbour positions,
uses a parity-majority argument on the actual oriented cycle arcs, constructs
the short and exterior-path cycles from those arcs and their complements,
and feeds the resulting certificate to `sameNeighborhoodBoundary`.  The
earlier theorem `sameNeighborhoodBoundary_one_of_exteriorPath` retains a
fully expanded `j = 1` construction.
-/

namespace Erdos58.Structural

open SimpleGraph

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- An actual positive simple path whose entire support is outside a chosen
longest odd cycle.  In particular both endpoints are outside the cycle. -/
structure ExteriorPath (C : EndpointCount.LongestOddCycle G) where
  left : V
  right : V
  walk : G.Walk left right
  isPath : walk.IsPath
  positive : 0 < walk.length
  avoids_cycle : ∀ {v : V}, v ∈ walk.support → v ∉ C.cycle.support

/-- The positions on `C` adjacent to `v`.  The use of positions, rather than
vertices, retains the canonical cyclic order and is harmless because a
simple cycle visits its proper positions injectively. -/
def cycleNeighborPositions (C : EndpointCount.LongestOddCycle G) (v : V) :
    Finset (Fin C.cycle.length) := by
  classical
  exact Finset.univ.filter fun i ↦ G.Adj v (C.cycle.getVert i)

@[simp] lemma mem_cycleNeighborPositions
    (C : EndpointCount.LongestOddCycle G) (v : V)
    (i : Fin C.cycle.length) :
    i ∈ cycleNeighborPositions C v ↔ G.Adj v (C.cycle.getVert i) := by
  classical
  simp [cycleNeighborPositions]

/-- Chords from the left endpoint to later vertices of its path.  Position
`1` is the ordinary first path edge and is therefore excluded.  The final
position is deliberately included: when the path has length greater than
one, a direct edge from its left to its right endpoint is an endpoint chord.
-/
def leftChordPositions {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C) : Finset (Fin (S.walk.length + 1)) := by
  classical
  exact Finset.univ.filter fun i ↦
    1 < (i : ℕ) ∧ G.Adj S.left (S.walk.getVert i)

@[simp] lemma mem_leftChordPositions
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i : Fin (S.walk.length + 1)) :
    i ∈ leftChordPositions S ↔
      1 < (i : ℕ) ∧ G.Adj S.left (S.walk.getVert i) := by
  classical
  simp [leftChordPositions]

/-- Chords from the right endpoint to the interior of its path.  The
ordinary last path edge is excluded. -/
def rightChordPositions {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C) : Finset (Fin (S.walk.length + 1)) := by
  classical
  exact Finset.univ.filter fun i ↦
    (i : ℕ) + 1 < S.walk.length ∧
      G.Adj S.right (S.walk.getVert i)

@[simp] lemma mem_rightChordPositions
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i : Fin (S.walk.length + 1)) :
    i ∈ rightChordPositions S ↔
      (i : ℕ) + 1 < S.walk.length ∧
        G.Adj S.right (S.walk.getVert i) := by
  classical
  simp [rightChordPositions]

/-- The actual graph configuration left by the endpoint count when the
oriented left endpoint has one path chord, the right endpoint has a chord
that can be selected, and the endpoints have the same `2*j-1` cycle
neighbours.  Extra right-endpoint chords are harmless and are not excluded.
-/
structure OneChordEachConfiguration
    (C : EndpointCount.LongestOddCycle G) (j : ℕ) where
  exterior : ExteriorPath C
  same_neighbors :
    cycleNeighborPositions C exterior.left =
      cycleNeighborPositions C exterior.right
  cycle_neighbor_card :
    (cycleNeighborPositions C exterior.left).card = 2 * j - 1
  left_chord_card : (leftChordPositions exterior).card = 1
  right_chord_nonempty : (rightChordPositions exterior).Nonempty

/-- A second simple route between the endpoints of an exterior path, still
entirely outside the longest cycle.  Endpoint chords produce routes of this
form by replacing an initial or final segment of the original path. -/
structure EndpointRoute {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C) where
  walk : G.Walk S.left S.right
  isPath : walk.IsPath
  positive : 0 < walk.length
  avoids_cycle : ∀ {v : V}, v ∈ walk.support → v ∉ C.cycle.support

/-- Regard an endpoint route as another exterior path with the same ordered
endpoints. -/
def EndpointRoute.toExteriorPath {C : EndpointCount.LongestOddCycle G}
    {S : ExteriorPath C} (R : EndpointRoute S) : ExteriorPath C where
  left := S.left
  right := S.right
  walk := R.walk
  isPath := R.isPath
  positive := R.positive
  avoids_cycle := R.avoids_cycle

/-- The original exterior path is itself an endpoint route. -/
def ExteriorPath.toEndpointRoute {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C) : EndpointRoute S where
  walk := S.walk
  isPath := S.isPath
  positive := S.positive
  avoids_cycle := S.avoids_cycle

/-- The endpoint route obtained by taking a left-endpoint chord and then
following the remaining suffix of the original exterior path. -/
def ExteriorPath.leftChordRoute {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C) (a : Fin (S.walk.length + 1))
    (ha : a ∈ leftChordPositions S) : EndpointRoute S := by
  classical
  have hapos : 1 < (a : ℕ) := (mem_leftChordPositions S a).mp ha |>.1
  have hadj : G.Adj S.left (S.walk.getVert a) :=
    (mem_leftChordPositions S a).mp ha |>.2
  have hale : (a : ℕ) ≤ S.walk.length := by omega
  let w : G.Walk S.left S.right := hadj.toWalk.append (S.walk.drop a)
  have hleft_not_drop : S.left ∉ (S.walk.drop a).support := by
    intro hleft
    rw [Walk.drop_support_eq_support_drop_min, Nat.min_eq_left hale,
      ← S.walk.cons_tail_support] at hleft
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (a : ℕ) ≠ 0)
    rw [hn] at hleft
    simp only [List.drop_succ_cons] at hleft
    have hn := S.isPath.support_nodup
    rw [← S.walk.cons_tail_support] at hn
    exact hn.notMem (List.mem_of_mem_drop hleft)
  refine {
    walk := w
    isPath := ?_
    positive := ?_
    avoids_cycle := ?_ }
  · change (hadj.toWalk.append (S.walk.drop a)).IsPath
    rw [Walk.isPath_def, Walk.support_append]
    exact hadj.isPath_toWalk.support_nodup.append
      (S.isPath.drop a).support_nodup.tail (by
        intro v hvEdge hvDrop
        simp only [hadj.support_toWalk, List.mem_cons, List.not_mem_nil,
          or_false] at hvEdge
        rcases hvEdge with rfl | rfl
        · exact hleft_not_drop (List.mem_of_mem_tail hvDrop)
        · have hn := (S.isPath.drop a).support_nodup
          rw [← (S.walk.drop a).cons_tail_support] at hn
          exact (List.nodup_cons.mp hn).1 hvDrop)
  · simp [w]
  · intro v hv hcycle
    apply S.avoids_cycle ?_ hcycle
    simp only [w, Walk.support_append, hadj.support_toWalk,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl) | hv
    · exact S.walk.start_mem_support
    · exact S.walk.getVert_mem_support a
    · have hv' : v ∈ (S.walk.drop a).support := List.mem_of_mem_tail hv
      rw [Walk.drop_support_eq_support_drop_min] at hv'
      exact List.mem_of_mem_drop hv'

@[simp] lemma ExteriorPath.leftChordRoute_length
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (a : Fin (S.walk.length + 1)) (ha : a ∈ leftChordPositions S) :
    (S.leftChordRoute a ha).walk.length = S.walk.length - a + 1 := by
  classical
  simp [ExteriorPath.leftChordRoute]

/-- The symmetric shortcut obtained by following the initial segment of the
exterior path and then taking a selected right-endpoint chord. -/
def ExteriorPath.rightChordRoute {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C) (b : Fin (S.walk.length + 1))
    (hb : b ∈ rightChordPositions S) : EndpointRoute S := by
  classical
  have hbpos : (b : ℕ) + 1 < S.walk.length :=
    (mem_rightChordPositions S b).mp hb |>.1
  have hadj : G.Adj S.right (S.walk.getVert b) :=
    (mem_rightChordPositions S b).mp hb |>.2
  let p : G.Walk S.left (S.walk.getVert b) := S.walk.take b
  have hright_not : S.right ∉ p.support := by
    intro hright
    have hpref : p.support <+: S.walk.support := by
      change (S.walk.take b).support <+: S.walk.support
      rw [Walk.support_take]
      exact List.take_prefix _ _
    have hlastmem : S.walk.support.getLast S.walk.support_ne_nil ∈ p.support := by
      simpa using hright
    have heq : p.support = S.walk.support :=
      List.Nodup.eq_of_getLast_mem_of_prefix hpref hlastmem S.isPath.support_nodup
    have hlen := congrArg List.length heq
    simp [p, Walk.support_take] at hlen
    omega
  let w : G.Walk S.left S.right := p.concat hadj.symm
  refine {
    walk := w
    isPath := (S.isPath.take b).concat hright_not hadj.symm
    positive := by simp [w, p]
    avoids_cycle := ?_ }
  intro v hv hcycle
  apply S.avoids_cycle ?_ hcycle
  simp only [w, Walk.support_concat, List.mem_append,
    List.mem_singleton] at hv
  rcases hv with hv | rfl
  · change v ∈ (S.walk.take b).support at hv
    rw [Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  · exact S.walk.end_mem_support

@[simp] lemma ExteriorPath.rightChordRoute_length
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (b : Fin (S.walk.length + 1)) (hb : b ∈ rightChordPositions S) :
    (S.rightChordRoute b hb).walk.length = (b : ℕ) + 1 := by
  classical
  have hble : (b : ℕ) ≤ S.walk.length := by omega
  simp [ExteriorPath.rightChordRoute, hble]

/-- The actual subpath between two ordered positions of an exterior path. -/
def ExteriorPath.segment {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j) :
    G.Walk (S.walk.getVert i) (S.walk.getVert j) :=
  (((S.walk.drop i).take (j - i))).copy (by simp) (by
    rw [Walk.drop_getVert]
    congr 1
    omega)

@[simp] lemma ExteriorPath.segment_length
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j) :
    (S.segment i j hij).length = (j : ℕ) - i := by
  simp only [ExteriorPath.segment, Walk.length_copy,
    Walk.take_length, Walk.drop_length]
  have hi : (i : ℕ) ≤ S.walk.length := by omega
  have hj : (j : ℕ) ≤ S.walk.length := by omega
  omega

lemma ExteriorPath.segment_isPath
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j) :
    (S.segment i j hij).IsPath := by
  rw [ExteriorPath.segment, Walk.isPath_copy]
  exact (S.isPath.drop i).take _

lemma ExteriorPath.segment_support_subset
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j) :
    ∀ v ∈ (S.segment i j hij).support, v ∈ S.walk.support := by
  intro v hv
  rw [ExteriorPath.segment, Walk.support_copy, Walk.support_take] at hv
  have hvdrop : v ∈ (S.walk.drop i).support := List.mem_of_mem_take hv
  rw [Walk.drop_support_eq_support_drop_min] at hvdrop
  exact List.mem_of_mem_drop hvdrop

private lemma ExteriorPath.left_not_mem_segment_of_pos
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j) (hi : 0 < (i : ℕ)) :
    S.left ∉ (S.segment i j hij).support := by
  intro hleft
  rw [ExteriorPath.segment, Walk.support_copy, Walk.support_take] at hleft
  have hdrop : S.left ∈ (S.walk.drop i).support :=
    List.mem_of_mem_take hleft
  have hi_le : (i : ℕ) ≤ S.walk.length := by omega
  rw [Walk.drop_support_eq_support_drop_min,
    Nat.min_eq_left hi_le, ← S.walk.cons_tail_support] at hdrop
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (i : ℕ) ≠ 0)
  rw [hn] at hdrop
  simp only [List.drop_succ_cons] at hdrop
  have hnodup := S.isPath.support_nodup
  rw [← S.walk.cons_tail_support] at hnodup
  exact hnodup.notMem (List.mem_of_mem_drop hdrop)

private lemma ExteriorPath.right_not_mem_segment_of_lt
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j)
    (hj : (j : ℕ) < S.walk.length) :
    S.right ∉ (S.segment i j hij).support := by
  intro hright
  obtain ⟨k, hkvert, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hright
  have hseglen := S.segment_length i j hij
  have hkbound : k ≤ (j : ℕ) - i := by omega
  have hik : (i : ℕ) + k ≤ S.walk.length := by omega
  have hget : S.walk.getVert ((i : ℕ) + k) = S.right := by
    simpa [ExteriorPath.segment, Walk.getVert_copy, Walk.take_getVert,
      Walk.drop_getVert, Nat.min_eq_right hkbound] using hkvert
  have hend := (S.isPath.getVert_eq_end_iff hik).mp hget
  omega

/-- The route using both selected endpoint chords and the subpath between
their marked positions.  The hypotheses say that this subpath is genuinely
internal, preventing either exterior endpoint from being repeated. -/
def ExteriorPath.bothChordRoute {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C)
    (a b : Fin (S.walk.length + 1))
    (ha : a ∈ leftChordPositions S) (hb : b ∈ rightChordPositions S)
    (hmin : 0 < min (a : ℕ) b)
    (hmax : max (a : ℕ) b < S.walk.length) : EndpointRoute S := by
  classical
  have hadjA : G.Adj S.left (S.walk.getVert a) :=
    (mem_leftChordPositions S a).mp ha |>.2
  have hadjB : G.Adj S.right (S.walk.getVert b) :=
    (mem_rightChordPositions S b).mp hb |>.2
  have hLR : S.left ≠ S.right := by
    intro h
    exact (Nat.ne_of_gt S.positive)
      (S.isPath.nil_iff_eq.mpr h).length_eq_zero
  by_cases hab : a ≤ b
  · let p := S.segment a b hab
    have hp : p.IsPath := S.segment_isPath a b hab
    have hleft : S.left ∉ p.support := by
      apply S.left_not_mem_segment_of_pos a b hab
      omega
    have hright : S.right ∉ p.support := by
      apply S.right_not_mem_segment_of_lt a b hab
      omega
    let q : G.Walk S.left (S.walk.getVert b) := Walk.cons hadjA p
    have hq : q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hleft⟩
    have hrightq : S.right ∉ q.support := by
      intro h
      simp only [q, Walk.support_cons, List.mem_cons] at h
      rcases h with h | h
      · exact hLR h.symm
      · exact hright h
    let w : G.Walk S.left S.right := q.concat hadjB.symm
    refine {
      walk := w
      isPath := hq.concat hrightq hadjB.symm
      positive := by simp [w, q, p]
      avoids_cycle := ?_ }
    intro v hv hcycle
    apply S.avoids_cycle ?_ hcycle
    have hv' : v ∈ q.support ∨ v = S.right := by
      simpa [w, Walk.support_concat] using hv
    rcases hv' with hvq | rfl
    · have hvq' : v = S.left ∨ v ∈ p.support := by
        simpa [q, Walk.support_cons] using hvq
      rcases hvq' with rfl | hvp
      · exact S.walk.start_mem_support
      · exact S.segment_support_subset a b hab v hvp
    · exact S.walk.end_mem_support
  · have hba : b ≤ a := by omega
    let p := (S.segment b a hba).reverse
    have hp : p.IsPath := (S.segment_isPath b a hba).reverse
    have hleft : S.left ∉ p.support := by
      simpa [p, Walk.support_reverse] using
        S.left_not_mem_segment_of_pos b a hba (by omega)
    have hright : S.right ∉ p.support := by
      simpa [p, Walk.support_reverse] using
        S.right_not_mem_segment_of_lt b a hba (by omega)
    let q : G.Walk S.left (S.walk.getVert b) := Walk.cons hadjA p
    have hq : q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hleft⟩
    have hrightq : S.right ∉ q.support := by
      intro h
      simp only [q, Walk.support_cons, List.mem_cons] at h
      rcases h with h | h
      · exact hLR h.symm
      · exact hright h
    let w : G.Walk S.left S.right := q.concat hadjB.symm
    refine {
      walk := w
      isPath := hq.concat hrightq hadjB.symm
      positive := by simp [w, q, p]
      avoids_cycle := ?_ }
    intro v hv hcycle
    apply S.avoids_cycle ?_ hcycle
    have hv' : v ∈ q.support ∨ v = S.right := by
      simpa [w, Walk.support_concat] using hv
    rcases hv' with hvq | rfl
    · have hvq' : v = S.left ∨ v ∈ p.support := by
        simpa [q, Walk.support_cons] using hvq
      rcases hvq' with rfl | hvp
      · exact S.walk.start_mem_support
      · apply S.segment_support_subset b a hba v
        simpa [p, Walk.support_reverse] using hvp
    · exact S.walk.end_mem_support

@[simp] lemma ExteriorPath.bothChordRoute_length
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (a b : Fin (S.walk.length + 1))
    (ha : a ∈ leftChordPositions S) (hb : b ∈ rightChordPositions S)
    (hmin : 0 < min (a : ℕ) b)
    (hmax : max (a : ℕ) b < S.walk.length) :
    (S.bothChordRoute a b ha hb hmin hmax).walk.length =
      Nat.dist (a : ℕ) b + 2 := by
  classical
  simp only [ExteriorPath.bothChordRoute]
  split
  · rename_i hab
    rw [Nat.dist_eq_sub_of_le (Fin.le_iff_val_le_val.mp hab)]
    simp [ExteriorPath.segment_length]
  · rename_i hab
    have hba : (b : ℕ) ≤ a := by omega
    rw [Nat.dist_eq_sub_of_le_right hba]
    simp [ExteriorPath.segment_length]

/-- The actual no-chord/equal-cycle-neighbour boundary configuration.  The
inequality permits the paper's `2*j+1` invocation; its proof selects any
`2*j` of the common neighbours. -/
structure SameNeighborhoodNoChordConfiguration
    (C : EndpointCount.LongestOddCycle G) (j : ℕ) where
  exterior : ExteriorPath C
  no_left_chord : leftChordPositions exterior = ∅
  same_neighbors :
    cycleNeighborPositions C exterior.left =
      cycleNeighborPositions C exterior.right
  many_neighbors :
    2 * j ≤ (cycleNeighborPositions C exterior.left).card

/-- The actual no-chord/different-cycle-neighbour boundary configuration.
The asymmetric orientation records the `2*j` selected neighbours of the
left endpoint and the extra right-endpoint neighbour used as the base of the
cyclic prefix sums. -/
structure DifferentNeighborhoodNoChordConfiguration
    (C : EndpointCount.LongestOddCycle G) (j : ℕ) where
  exterior : ExteriorPath C
  no_left_chord : leftChordPositions exterior = ∅
  many_left_neighbors :
    2 * j ≤ (cycleNeighborPositions C exterior.left).card
  /-- This is the orientation chosen in the source before the endpoint
  count: swap the two ends if necessary so that the left cycle-neighbour
  set is no larger than the right one.  It is essential here.  Without it,
  the raw configuration is false already for `j = 1` (a `C₇` with a
  length-four exterior ear attached twice at its left end and once at its
  right end). -/
  left_card_le_right_card :
    (cycleNeighborPositions C exterior.left).card ≤
      (cycleNeighborPositions C exterior.right).card
  extra_right_neighbor :
    (cycleNeighborPositions C exterior.right \
      cycleNeighborPositions C exterior.left).Nonempty

/-- The oriented arc of `C` from position `i` to position `j`.  It is
obtained by rotating the actual cycle at `i` and taking the initial segment
ending at `j`. -/
def cycleArc (C : EndpointCount.LongestOddCycle G)
    (i j : Fin C.cycle.length) :
    G.Walk (C.cycle.getVert i) (C.cycle.getVert j) := by
  classical
  let x := C.cycle.getVert i
  have hx : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  let c := C.cycle.rotate x hx
  have hy : C.cycle.getVert j ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hx).mpr
      (C.cycle.getVert_mem_support j)
  exact c.takeUntil (C.cycle.getVert j) hy

lemma cycleArc_isPath (C : EndpointCount.LongestOddCycle G)
    (i j : Fin C.cycle.length) : (cycleArc C i j).IsPath := by
  classical
  simp only [cycleArc]
  exact (C.isCycle.rotate (C.cycle.getVert_mem_support i)).isPath_takeUntil _

lemma cycleArc_support_subset_cycle (C : EndpointCount.LongestOddCycle G)
    (i j : Fin C.cycle.length) :
    ∀ z ∈ (cycleArc C i j).support, z ∈ C.cycle.support := by
  classical
  intro z hz
  simp only [cycleArc] at hz
  exact (C.cycle.mem_support_rotate_iff _ _).mp
    (Walk.support_takeUntil_subset_support _ _ hz)

lemma cycleArc_length_injective (C : EndpointCount.LongestOddCycle G)
    (i : Fin C.cycle.length) :
    Function.Injective fun j : Fin C.cycle.length ↦ (cycleArc C i j).length := by
  classical
  intro j k hlen
  let x := C.cycle.getVert i
  have hx : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  let c := C.cycle.rotate x hx
  have hj : C.cycle.getVert j ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hx).mpr
      (C.cycle.getVert_mem_support j)
  have hk : C.cycle.getVert k ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hx).mpr
      (C.cycle.getVert_mem_support k)
  change (c.takeUntil (C.cycle.getVert j) hj).length =
    (c.takeUntil (C.cycle.getVert k) hk).length at hlen
  apply Fin.ext
  apply C.isCycle.getVert_injOn' (by simp; omega) (by simp; omega)
  rw [← c.getVert_length_takeUntil hj,
    ← c.getVert_length_takeUntil hk, hlen]

/-- The complementary oriented arc in the same split used by `cycleArc`. -/
def cycleCoarc (C : EndpointCount.LongestOddCycle G)
    (i j : Fin C.cycle.length) :
    G.Walk (C.cycle.getVert j) (C.cycle.getVert i) := by
  classical
  let x := C.cycle.getVert i
  have hx : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  let c := C.cycle.rotate x hx
  have hy : C.cycle.getVert j ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hx).mpr
      (C.cycle.getVert_mem_support j)
  exact c.dropUntil (C.cycle.getVert j) hy

lemma cycleCoarc_isPath (C : EndpointCount.LongestOddCycle G)
    {i j : Fin C.cycle.length} (hij : i ≠ j) :
    (cycleCoarc C i j).IsPath := by
  classical
  let x := C.cycle.getVert i
  have hx : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  let c := C.cycle.rotate x hx
  have hy : C.cycle.getVert j ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hx).mpr
      (C.cycle.getVert_mem_support j)
  have hxy : x ≠ C.cycle.getVert j := by
    intro h
    apply hij
    apply Fin.ext
    exact C.isCycle.getVert_injOn' (by simp; omega) (by simp; omega) h
  have htake : ¬(c.takeUntil (C.cycle.getVert j) hy).Nil := by
    intro hnil
    exact hxy ((c.nil_takeUntil hy).mp hnil)
  change (c.dropUntil (C.cycle.getVert j) hy).IsPath
  exact Walk.IsCycle.isPath_of_append_right htake (by
    simpa only [c.take_spec hy] using C.isCycle.rotate hx)

lemma cycleCoarc_support_subset_cycle (C : EndpointCount.LongestOddCycle G)
    (i j : Fin C.cycle.length) :
    ∀ z ∈ (cycleCoarc C i j).support, z ∈ C.cycle.support := by
  classical
  intro z hz
  simp only [cycleCoarc] at hz
  exact (C.cycle.mem_support_rotate_iff _ _).mp
    (Walk.support_dropUntil_subset_support _ _ hz)

lemma cycleArc_add_cycleCoarc_length (C : EndpointCount.LongestOddCycle G)
    (i j : Fin C.cycle.length) :
    (cycleArc C i j).length + (cycleCoarc C i j).length = C.cycle.length := by
  classical
  let x := C.cycle.getVert i
  have hx : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  let c := C.cycle.rotate x hx
  have hy : C.cycle.getVert j ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hx).mpr
      (C.cycle.getVert_mem_support j)
  change (c.takeUntil (C.cycle.getVert j) hy).length +
      (c.dropUntil (C.cycle.getVert j) hy).length = C.cycle.length
  rw [← Walk.length_append, c.take_spec]
  simp [c]

lemma cycleCoarc_length_injective (C : EndpointCount.LongestOddCycle G)
    (i : Fin C.cycle.length) :
    Function.Injective fun j : Fin C.cycle.length ↦ (cycleCoarc C i j).length := by
  intro j k h
  apply cycleArc_length_injective C i
  change (cycleArc C i j).length = (cycleArc C i k).length
  have hj := cycleArc_add_cycleCoarc_length C i j
  have hk := cycleArc_add_cycleCoarc_length C i k
  change (cycleCoarc C i j).length = (cycleCoarc C i k).length at h
  omega

lemma odd_cycleArc_iff_even_cycleCoarc
    (C : EndpointCount.LongestOddCycle G) (i j : Fin C.cycle.length) :
    Odd (cycleArc C i j).length ↔ Even (cycleCoarc C i j).length := by
  apply Nat.odd_add.mp
  rw [cycleArc_add_cycleCoarc_length]
  exact C.odd_length

lemma even_cycleArc_iff_odd_cycleCoarc
    (C : EndpointCount.LongestOddCycle G) (i j : Fin C.cycle.length) :
    Even (cycleArc C i j).length ↔ Odd (cycleCoarc C i j).length := by
  exact (Nat.odd_add'.mp (by
    rw [cycleArc_add_cycleCoarc_length]
    exact C.odd_length)).symm

/-- Concrete cyclic-position data used by the general equal-neighbour
boundary application.  The only additional information beyond
`SameNeighborhoodNoChordConfiguration` is the outcome of the elementary
parity selection on the actual oriented cycle arcs: one base with `j` odd
arcs and one (possibly different) base with `j` even arcs.  No closed walk
or `CycleAtLength` witness is assumed. -/
structure SameNeighborhoodSelectedConfiguration
    (C : EndpointCount.LongestOddCycle G) (j : ℕ)
    extends SameNeighborhoodNoChordConfiguration C j where
  oddBase : Fin C.cycle.length
  oddTargets : Finset (Fin C.cycle.length)
  oddBase_mem : oddBase ∈ cycleNeighborPositions C exterior.left
  oddTargets_subset : oddTargets ⊆ cycleNeighborPositions C exterior.left
  oddBase_not_mem : oddBase ∉ oddTargets
  oddTargets_card : oddTargets.card = j
  odd_arcs : ∀ t ∈ oddTargets, Odd (cycleArc C oddBase t).length
  evenBase : Fin C.cycle.length
  evenTargets : Finset (Fin C.cycle.length)
  evenBase_mem : evenBase ∈ cycleNeighborPositions C exterior.left
  evenTargets_subset : evenTargets ⊆ cycleNeighborPositions C exterior.left
  evenBase_not_mem : evenBase ∉ evenTargets
  evenTargets_card : evenTargets.card = j
  even_arcs : ∀ t ∈ evenTargets, Even (cycleArc C evenBase t).length

/-- The concrete `p = 2`, `q = 0`, equal-neighbour boundary configuration.
No cycle-family or length certificate occurs in this structure. -/
structure SameNeighborhoodTwoConfiguration
    (C : EndpointCount.LongestOddCycle G) where
  exterior : ExteriorPath C
  same_neighbors :
    cycleNeighborPositions C exterior.left =
      cycleNeighborPositions C exterior.right
  two_neighbors : (cycleNeighborPositions C exterior.left).card = 2

private theorem cycleAtLength_of_append
    {x y : V} (p : G.Walk x y) (q : G.Walk y x)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : p.support.tail.Disjoint q.support.tail)
    (hlong : 1 < p.length ∨ 1 < q.length) :
    CycleAtLength G (p.length + q.length) := by
  exact ⟨x, p.append q, hp.isCycle_append hq hdisj hlong,
    Walk.length_append p q⟩

private lemma getVert_ne_of_fin_ne
    (C : EndpointCount.LongestOddCycle G)
    {i j : Fin C.cycle.length} (hij : i ≠ j) :
    C.cycle.getVert i ≠ C.cycle.getVert j := by
  intro h
  apply hij
  apply Fin.ext
  exact C.isCycle.getVert_injOn'
    (by simp; omega) (by simp; omega) h

private lemma mem_cycle_of_mem_rotated
    [DecidableEq V] (C : EndpointCount.LongestOddCycle G)
    {x z : V} (hx : x ∈ C.cycle.support)
    (hz : z ∈ (C.cycle.rotate x hx).support) :
    z ∈ C.cycle.support := by
  classical
  exact ((C.cycle.mem_support_rotate_iff x hx)).mp hz

private lemma start_not_mem_tail_of_isPath {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) : x ∉ p.support.tail := by
  have hnodup := hp.support_nodup
  rw [← p.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

/-- Close one actual oriented arc of the longest cycle using, respectively,
the two-edge route through the left endpoint and the long route through the
exterior path. -/
private theorem commonNeighborPathCycles
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i j : Fin C.cycle.length) (hij : i ≠ j)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (hjL : j ∈ cycleNeighborPositions C S.left)
    (hjR : j ∈ cycleNeighborPositions C S.right)
    (P : G.Walk (C.cycle.getVert i) (C.cycle.getVert j))
    (hP : P.IsPath)
    (hPsub : ∀ z ∈ P.support, z ∈ C.cycle.support) :
    CycleAtLength G (P.length + 2) ∧
      CycleAtLength G (P.length + S.walk.length + 2) := by
  classical
  let x := C.cycle.getVert i
  let y := C.cycle.getVert j
  have hxy : x ≠ y := getVert_ne_of_fin_ne C hij
  have hxC : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  have hyC : y ∈ C.cycle.support := C.cycle.getVert_mem_support j
  have hLx : G.Adj S.left x := (mem_cycleNeighborPositions C S.left i).mp hiL
  have hRx : G.Adj S.right x := (mem_cycleNeighborPositions C S.right i).mp hiR
  have hLy : G.Adj S.left y := (mem_cycleNeighborPositions C S.left j).mp hjL
  have hRy : G.Adj S.right y := (mem_cycleNeighborPositions C S.right j).mp hjR
  have hxOutside : x ∉ S.walk.support := fun hx ↦ S.avoids_cycle hx hxC
  have hyOutside : y ∉ S.walk.support := fun hy ↦ S.avoids_cycle hy hyC
  have hleftOutsideCycle : S.left ∉ C.cycle.support :=
    S.avoids_cycle S.walk.start_mem_support
  have hrightOutsideCycle : S.right ∉ C.cycle.support :=
    S.avoids_cycle S.walk.end_mem_support
  have hLy_ne : S.left ≠ y := fun h ↦ hleftOutsideCycle (h.symm ▸ hyC)
  have hRy_ne : S.right ≠ y := fun h ↦ hrightOutsideCycle (h.symm ▸ hyC)
  let shortYX : G.Walk y x := Walk.cons hLy.symm hLx.toWalk
  let longYX : G.Walk y x := Walk.cons hRy.symm (S.walk.reverse.concat hLx)
  have hshort : shortYX.IsPath := by
    dsimp [shortYX]
    rw [Walk.cons_isPath_iff]
    exact ⟨hLx.isPath_toWalk, by
      simp only [hLx.support_toWalk, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      exact ⟨hLy_ne.symm, hxy.symm⟩⟩
  have hlong : longYX.IsPath := by
    dsimp [longYX]
    rw [Walk.cons_isPath_iff]
    constructor
    · exact S.isPath.reverse.concat
        (by simpa [Walk.support_reverse] using hxOutside) hLx
    · simp only [Walk.support_concat, List.mem_append, List.mem_singleton,
        Walk.support_reverse, List.mem_reverse]
      exact fun h ↦ h.elim hyOutside hxy.symm
  have hshort_inter :
      ∀ z ∈ shortYX.support, z ∈ C.cycle.support → z = y ∨ z = x := by
    intro z hz hzC
    simp only [shortYX, Walk.support_cons, hLx.support_toWalk,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (S.avoids_cycle S.walk.start_mem_support hzC)
    · exact Or.inr rfl
  have hlong_inter :
      ∀ z ∈ longYX.support, z ∈ C.cycle.support → z = y ∨ z = x := by
    intro z hz hzC
    simp only [longYX, Walk.support_cons, Walk.support_concat,
      Walk.support_reverse, List.mem_cons, List.mem_append, List.mem_reverse,
      List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact Or.inl rfl
    · exact False.elim (S.avoids_cycle hz hzC)
    · exact Or.inr rfl
  have hP_short : P.support.tail.Disjoint shortYX.support.tail := by
    intro z hzP hzS
    have hzPin : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzSin : z ∈ shortYX.support := List.mem_of_mem_tail hzS
    rcases hshort_inter z hzSin (hPsub z hzPin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath hshort hzS
    · exact start_not_mem_tail_of_isPath hP hzP
  have hP_long : P.support.tail.Disjoint longYX.support.tail := by
    intro z hzP hzS
    have hzPin : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzSin : z ∈ longYX.support := List.mem_of_mem_tail hzS
    rcases hlong_inter z hzSin (hPsub z hzPin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath hlong hzS
    · exact start_not_mem_tail_of_isPath hP hzP
  constructor
  · convert cycleAtLength_of_append P shortYX hP hshort hP_short
      (Or.inr (by simp [shortYX])) using 1 <;> simp [shortYX]
  · convert cycleAtLength_of_append P longYX hP hlong hP_long
      (Or.inr (by simp [longYX])) using 1 <;>
      simp [longYX] <;> omega

private theorem commonNeighborArcCycles
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i j : Fin C.cycle.length) (hij : i ≠ j)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (hjL : j ∈ cycleNeighborPositions C S.left)
    (hjR : j ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G ((cycleArc C i j).length + 2) ∧
      CycleAtLength G ((cycleArc C i j).length + S.walk.length + 2) :=
  commonNeighborPathCycles C S i j hij hiL hiR hjL hjR
    (cycleArc C i j) (cycleArc_isPath C i j)
    (cycleArc_support_subset_cycle C i j)

private theorem commonNeighborCoarcCycles
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i j : Fin C.cycle.length) (hij : i ≠ j)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (hjL : j ∈ cycleNeighborPositions C S.left)
    (hjR : j ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G ((cycleCoarc C i j).length + 2) ∧
      CycleAtLength G ((cycleCoarc C i j).length + S.walk.length + 2) := by
  classical
  have hp : (cycleCoarc C i j).reverse.IsPath :=
    (cycleCoarc_isPath C hij).reverse
  have hsub : ∀ z ∈ (cycleCoarc C i j).reverse.support,
      z ∈ C.cycle.support := by
    intro z hz
    apply cycleCoarc_support_subset_cycle C i j z
    simpa [Walk.support_reverse] using hz
  simpa using commonNeighborPathCycles C S i j hij hiL hiR hjL hjR
    (cycleCoarc C i j).reverse hp hsub

/-- A common neighbour of both exterior endpoints closes the exterior path
to a simple cycle of length `S.length + 2`. -/
private theorem commonNeighborBaseCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i : Fin C.cycle.length)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hiR : i ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G (S.walk.length + 2) := by
  classical
  let x := C.cycle.getVert i
  have hxC : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  have hLx : G.Adj S.left x := (mem_cycleNeighborPositions C S.left i).mp hiL
  have hRx : G.Adj S.right x := (mem_cycleNeighborPositions C S.right i).mp hiR
  have hxOutside : x ∉ S.walk.support := fun hx ↦ S.avoids_cycle hx hxC
  have hLR : S.left ≠ S.right := by
    intro h
    have hnil : S.walk.Nil := S.isPath.nil_iff_eq.mpr h
    exact (Nat.ne_of_gt S.positive) hnil.length_eq_zero
  have hRx_ne : S.right ≠ x := fun h ↦
    S.avoids_cycle S.walk.end_mem_support (h ▸ hxC)
  let base : G.Walk x x := Walk.cons hLx.symm (S.walk.concat hRx)
  have hbase : base.IsCycle := by
    dsimp [base]
    rw [Walk.cons_isCycle_iff]
    constructor
    · exact S.isPath.concat hxOutside hRx
    · intro he
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
      simp only [List.mem_singleton] at he
      rcases he with he | he
      · exact hxOutside (S.walk.fst_mem_support_of_mem_edges he)
      · rw [Sym2.eq_iff] at he
        rcases he with ⟨hxr, -⟩ | ⟨-, hLR'⟩
        · exact hRx_ne hxr.symm
        · exact hLR hLR'
  exact ⟨x, base, hbase, by simp [base]⟩

/-- The short two-spoke cycle and the cycle using an arbitrary actual
endpoint route.  This is the route-parametric form used in the one-chord
boundary case. -/
theorem EndpointRoute.arcCycles
    (C : EndpointCount.LongestOddCycle G) {S : ExteriorPath C}
    (R : EndpointRoute S)
    (i j : Fin C.cycle.length) (hij : i ≠ j)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (hjL : j ∈ cycleNeighborPositions C S.left)
    (hjR : j ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G ((cycleArc C i j).length + 2) ∧
      CycleAtLength G ((cycleArc C i j).length + R.walk.length + 2) := by
  exact commonNeighborArcCycles C R.toExteriorPath i j hij
    hiL hiR hjL hjR

/-- Complementary-arc version of `EndpointRoute.arcCycles`. -/
theorem EndpointRoute.coarcCycles
    (C : EndpointCount.LongestOddCycle G) {S : ExteriorPath C}
    (R : EndpointRoute S)
    (i j : Fin C.cycle.length) (hij : i ≠ j)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (hjL : j ∈ cycleNeighborPositions C S.left)
    (hjR : j ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G ((cycleCoarc C i j).length + 2) ∧
      CycleAtLength G ((cycleCoarc C i j).length + R.walk.length + 2) := by
  exact commonNeighborCoarcCycles C R.toExteriorPath i j hij
    hiL hiR hjL hjR

/-- A common cycle neighbour closes any actual endpoint route. -/
theorem EndpointRoute.baseCycle
    (C : EndpointCount.LongestOddCycle G) {S : ExteriorPath C}
    (R : EndpointRoute S) (i : Fin C.cycle.length)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hiR : i ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G (R.walk.length + 2) := by
  exact commonNeighborBaseCycle C R.toExteriorPath i hiL hiR

private theorem append_left_cancel_walk
    {u v w : V} (p : G.Walk u v) {q r : G.Walk v w}
    (h : p.append q = p.append r) : q = r := by
  induction p with
  | nil => simpa using h
  | cons hadj p ih =>
      apply ih
      exact eq_of_heq ((by
        simpa only [Walk.cons_append, Walk.cons.injEq] using h :
          True ∧ p.append q ≍ p.append r)).2

/-- If `i` occurs before `z` after rotating the cycle to start at `y`, the
suffix after `z` followed by the prefix through `i` is the complementary
simple path from `z` to `i`. -/
private theorem exists_cycleSupported_wrapPath
    (C : EndpointCount.LongestOddCycle G)
    (y i z : Fin C.cycle.length)
    (hlt : (cycleArc C y i).length < (cycleArc C y z).length) :
    ∃ P : G.Walk (C.cycle.getVert z) (C.cycle.getVert i),
      P.IsPath ∧
      (∀ x ∈ P.support, x ∈ C.cycle.support) ∧
      P.length = C.cycle.length - (cycleArc C y z).length +
        (cycleArc C y i).length := by
  classical
  let vy := C.cycle.getVert y
  let vi := C.cycle.getVert i
  let vz := C.cycle.getVert z
  have hy : vy ∈ C.cycle.support := C.cycle.getVert_mem_support y
  let c := C.cycle.rotate vy hy
  have hi : vi ∈ c.support :=
    (C.cycle.mem_support_rotate_iff vy hy).mpr
      (C.cycle.getVert_mem_support i)
  have hz : vz ∈ c.support :=
    (C.cycle.mem_support_rotate_iff vy hy).mpr
      (C.cycle.getVert_mem_support z)
  let pi := c.takeUntil vi hi
  let pz := c.takeUntil vz hz
  have hlt' : pi.length < pz.length := by
    simpa only [cycleArc, vy, vi, vz, c] using hlt
  have hiPz : vi ∈ pz.support := by
    have hgeti : c.getVert pi.length = vi := c.getVert_length_takeUntil hi
    have hgetpz : pz.getVert pi.length = c.getVert pi.length :=
      c.getVert_takeUntil hz hlt'.le
    have hmem := pz.getVert_mem_support pi.length
    rw [hgetpz, hgeti] at hmem
    exact hmem
  let q := pz.dropUntil vi hiPz
  let suffix := c.dropUntil vz hz
  let P := suffix.append pi
  have hnested : pz.takeUntil vi hiPz = pi := by
    simpa only [pi, pz] using c.takeUntil_takeUntil hz hiPz
  have hpiq : pi.append q = pz := by
    calc
      pi.append q =
          (pz.takeUntil vi hiPz).append (pz.dropUntil vi hiPz) := by
            simp only [q, hnested]
      _ = pz := pz.take_spec hiPz
  have hpzsuffix : pz.append suffix = c := c.take_spec hz
  have hpicsuffix : pi.append (q.append suffix) = c := by
    rw [Walk.append_assoc, hpiq, hpzsuffix]
  have hpicdrop : pi.append (c.dropUntil vi hi) = c := c.take_spec hi
  have hq_suffix : q.append suffix = c.dropUntil vi hi := by
    apply append_left_cancel_walk pi
    rw [hpicsuffix, hpicdrop]
  have hrotate : q.append P = c.rotate vi hi := by
    simp only [P, Walk.rotate]
    rw [Walk.append_assoc, hq_suffix]
  have hqpos : 0 < q.length := by
    have hlen := congrArg Walk.length hpiq
    simp only [Walk.length_append] at hlen
    omega
  have hPpath : P.IsPath := by
    have hcycle : (q.append P).IsCycle := by
      rw [hrotate]
      exact (C.isCycle.rotate hy).rotate hi
    exact hcycle.isPath_of_append_right
      (Walk.not_nil_iff_lt_length.mpr hqpos)
  have hPsub : ∀ x ∈ P.support, x ∈ C.cycle.support := by
    intro x hx
    change x ∈ (suffix.append pi).support at hx
    rw [Walk.mem_support_append_iff] at hx
    apply (C.cycle.mem_support_rotate_iff vy hy).mp
    rcases hx with hx | hx
    · exact c.support_dropUntil_subset_support hz hx
    · exact c.support_takeUntil_subset_support hi hx
  have hsplitz : pz.length + suffix.length = c.length := by
    have hlen := congrArg Walk.length hpzsuffix
    simpa only [Walk.length_append] using hlen
  have hc_length : c.length = C.cycle.length := by simp [c]
  have hP_length : P.length = C.cycle.length - pz.length + pi.length := by
    simp only [P, Walk.length_append]
    omega
  refine ⟨P, hPpath, hPsub, ?_⟩
  simpa only [cycleArc, vy, vi, vz, c, pi, pz] using hP_length

/-- Close a cycle-supported path from a right-endpoint attachment to a
left-endpoint attachment through the actual exterior path. -/
private theorem mixedEndpointPathCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (r t : Fin C.cycle.length) (hrt : r ≠ t)
    (hrR : r ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left)
    (P : G.Walk (C.cycle.getVert r) (C.cycle.getVert t))
    (hP : P.IsPath)
    (hPsub : ∀ z ∈ P.support, z ∈ C.cycle.support) :
    CycleAtLength G (P.length + S.walk.length + 2) := by
  classical
  let x := C.cycle.getVert r
  let y := C.cycle.getVert t
  have hxy : x ≠ y := getVert_ne_of_fin_ne C hrt
  have hxC : x ∈ C.cycle.support := C.cycle.getVert_mem_support r
  have hyC : y ∈ C.cycle.support := C.cycle.getVert_mem_support t
  have hRx : G.Adj S.right x :=
    (mem_cycleNeighborPositions C S.right r).mp hrR
  have hLy : G.Adj S.left y :=
    (mem_cycleNeighborPositions C S.left t).mp htL
  have hxOutside : x ∉ S.walk.support := fun hx ↦ S.avoids_cycle hx hxC
  have hyOutside : y ∉ S.walk.support := fun hy ↦ S.avoids_cycle hy hyC
  let closeYX : G.Walk y x := Walk.cons hLy.symm (S.walk.concat hRx)
  have hclose : closeYX.IsPath := by
    dsimp [closeYX]
    rw [Walk.cons_isPath_iff]
    constructor
    · exact S.isPath.concat hxOutside hRx
    · simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
      exact fun h ↦ h.elim hyOutside hxy.symm
  have hclose_inter :
      ∀ z ∈ closeYX.support, z ∈ C.cycle.support → z = y ∨ z = x := by
    intro z hz hzC
    simp only [closeYX, Walk.support_cons, Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact Or.inl rfl
    · exact False.elim (S.avoids_cycle hz hzC)
    · exact Or.inr rfl
  have hdisj : P.support.tail.Disjoint closeYX.support.tail := by
    intro z hzP hzQ
    have hzPin : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzQin : z ∈ closeYX.support := List.mem_of_mem_tail hzQ
    rcases hclose_inter z hzQin (hPsub z hzPin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath hclose hzQ
    · exact start_not_mem_tail_of_isPath hP hzP
  convert cycleAtLength_of_append P closeYX hP hclose hdisj
    (Or.inr (by simp [closeYX])) using 1 <;>
    simp [closeYX] <;> omega

private theorem mixedEndpointArcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (r t : Fin C.cycle.length) (hrt : r ≠ t)
    (hrR : r ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left) :
    CycleAtLength G
      ((cycleArc C r t).length + S.walk.length + 2) :=
  mixedEndpointPathCycle C S r t hrt hrR htL
    (cycleArc C r t) (cycleArc_isPath C r t)
    (cycleArc_support_subset_cycle C r t)

private theorem mixedEndpointCoarcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (r t : Fin C.cycle.length) (hrt : r ≠ t)
    (hrR : r ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left) :
    CycleAtLength G
      ((cycleCoarc C r t).length + S.walk.length + 2) := by
  classical
  have hp : (cycleCoarc C r t).reverse.IsPath :=
    (cycleCoarc_isPath C hrt).reverse
  have hsub : ∀ z ∈ (cycleCoarc C r t).reverse.support,
      z ∈ C.cycle.support := by
    intro z hz
    apply cycleCoarc_support_subset_cycle C r t z
    simpa [Walk.support_reverse] using hz
  simpa using mixedEndpointPathCycle C S r t hrt hrR htL
    (cycleCoarc C r t).reverse hp hsub

/-- Close a cycle-supported path between two right-endpoint attachments
through their common endpoint. -/
private theorem rightEndpointPathCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (htR : t ∈ cycleNeighborPositions C S.right)
    (P : G.Walk (C.cycle.getVert i) (C.cycle.getVert t))
    (hP : P.IsPath)
    (hPsub : ∀ z ∈ P.support, z ∈ C.cycle.support) :
    CycleAtLength G (P.length + 2) := by
  classical
  let x := C.cycle.getVert i
  let y := C.cycle.getVert t
  have hxy : x ≠ y := getVert_ne_of_fin_ne C hit
  have hRx : G.Adj S.right x :=
    (mem_cycleNeighborPositions C S.right i).mp hiR
  have hRy : G.Adj S.right y :=
    (mem_cycleNeighborPositions C S.right t).mp htR
  have hrightOutsideCycle : S.right ∉ C.cycle.support :=
    S.avoids_cycle S.walk.end_mem_support
  have hRy_ne : S.right ≠ y := fun h ↦
    hrightOutsideCycle (h.symm ▸ C.cycle.getVert_mem_support t)
  let closeYX : G.Walk y x := Walk.cons hRy.symm hRx.toWalk
  have hclose : closeYX.IsPath := by
    dsimp [closeYX]
    rw [Walk.cons_isPath_iff]
    exact ⟨hRx.isPath_toWalk, by
      simp only [hRx.support_toWalk, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      exact ⟨hRy_ne.symm, hxy.symm⟩⟩
  have hclose_inter :
      ∀ z ∈ closeYX.support, z ∈ C.cycle.support → z = y ∨ z = x := by
    intro z hz hzC
    simp only [closeYX, Walk.support_cons, hRx.support_toWalk,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim
        (S.avoids_cycle S.walk.end_mem_support hzC)
    · exact Or.inr rfl
  have hdisj : P.support.tail.Disjoint closeYX.support.tail := by
    intro z hzP hzQ
    have hzPin : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzQin : z ∈ closeYX.support := List.mem_of_mem_tail hzQ
    rcases hclose_inter z hzQin (hPsub z hzPin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath hclose hzQ
    · exact start_not_mem_tail_of_isPath hP hzP
  convert cycleAtLength_of_append P closeYX hP hclose hdisj
    (Or.inr (by simp [closeYX])) using 1 <;> simp [closeYX]

private theorem rightEndpointArcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (htR : t ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G ((cycleArc C i t).length + 2) :=
  rightEndpointPathCycle C S i t hit hiR htR
    (cycleArc C i t) (cycleArc_isPath C i t)
    (cycleArc_support_subset_cycle C i t)

private theorem rightEndpointCoarcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (htR : t ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G ((cycleCoarc C i t).length + 2) := by
  classical
  have hp : (cycleCoarc C i t).reverse.IsPath :=
    (cycleCoarc_isPath C hit).reverse
  have hsub : ∀ z ∈ (cycleCoarc C i t).reverse.support,
      z ∈ C.cycle.support := by
    intro z hz
    apply cycleCoarc_support_subset_cycle C i t z
    simpa [Walk.support_reverse] using hz
  simpa using rightEndpointPathCycle C S i t hit hiR htR
    (cycleCoarc C i t).reverse hp hsub

/-- If two attachments seen from a fixed cycle position are separated by
exactly the exterior-path length, the complementary wrap path closes through
the exterior path to an odd cycle two edges longer than the designated
longest odd cycle. -/
private theorem mixedWrapContradiction_of_arc_eq
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (y z i : Fin C.cycle.length)
    (hzR : z ∈ cycleNeighborPositions C S.right)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (heq : (cycleArc C y z).length =
      (cycleArc C y i).length + S.walk.length) : False := by
  have hlt : (cycleArc C y i).length < (cycleArc C y z).length := by
    have := S.positive
    omega
  obtain ⟨P, hPpath, hPsub, hPlen⟩ :=
    exists_cycleSupported_wrapPath C y i z hlt
  have hzi : z ≠ i := by
    intro h
    subst z
    have := S.positive
    omega
  have hcycle : CycleAtLength G (C.cycle.length + 2) := by
    have hraw := mixedEndpointPathCycle C S z i hzi hzR hiL P hPpath hPsub
    convert hraw using 1
    have hsum := cycleArc_add_cycleCoarc_length C y z
    omega
  have hodd : Odd (C.cycle.length + 2) := by
    rcases C.odd_length with ⟨q, hq⟩
    exact ⟨q + 1, by omega⟩
  have hle := C.longest (hcycle.mem_oddCycleLengths hodd)
  omega

private theorem mixedWrapContradiction_of_left_arc_eq
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (y z t : Fin C.cycle.length)
    (hzR : z ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left)
    (heq : (cycleArc C y t).length =
      (cycleArc C y z).length + S.walk.length) : False := by
  have hlt : (cycleArc C y z).length < (cycleArc C y t).length := by
    have := S.positive
    omega
  obtain ⟨P, hPpath, hPsub, hPlen⟩ :=
    exists_cycleSupported_wrapPath C y z t hlt
  have hzt : z ≠ t := by
    intro h
    subst t
    have := S.positive
    omega
  have hPsub' : ∀ x ∈ P.reverse.support, x ∈ C.cycle.support := by
    intro x hx
    apply hPsub x
    simpa [Walk.support_reverse] using hx
  have hcycle : CycleAtLength G (C.cycle.length + 2) := by
    have hsum := cycleArc_add_cycleCoarc_length C y t
    have hlength : P.reverse.length + S.walk.length + 2 =
        C.cycle.length + 2 := by
      simp only [Walk.length_reverse]
      omega
    rw [← hlength]
    exact mixedEndpointPathCycle C S z t hzt hzR htL
      P.reverse hPpath.reverse hPsub'
  have hodd : Odd (C.cycle.length + 2) := by
    rcases C.odd_length with ⟨q, hq⟩
    exact ⟨q + 1, by omega⟩
  have hle := C.longest (hcycle.mem_oddCycleLengths hodd)
  omega

private theorem mixedWrapContradiction_of_coarc_eq
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (y z i t : Fin C.cycle.length)
    (hzR : z ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left)
    (heq : (cycleCoarc C y z).length =
      (cycleArc C y i).length + S.walk.length)
    (hreflect : (cycleArc C y t).length =
      (cycleCoarc C y i).length) : False := by
  apply mixedWrapContradiction_of_left_arc_eq C S y z t hzR htL
  have hzsum := cycleArc_add_cycleCoarc_length C y z
  have hisum := cycleArc_add_cycleCoarc_length C y i
  omega

private noncomputable def sameNeighborhoodCertificate_of_odd_forward_family
    (C : EndpointCount.LongestOddCycle G) (j : ℕ)
    (S : ExteriorPath C)
    (base : Fin C.cycle.length) (M : Finset (Fin C.cycle.length))
    (hMcard : M.card = j)
    (hbaseL : base ∈ cycleNeighborPositions C S.left)
    (hbaseR : base ∈ cycleNeighborPositions C S.right)
    (hML : M ⊆ cycleNeighborPositions C S.left)
    (hMR : M ⊆ cycleNeighborPositions C S.right)
    (hbaseNot : base ∉ M)
    (hodd : ∀ t ∈ M, Odd (cycleArc C base t).length)
    (hj : 0 < j) :
    SameNeighborhoodCertificate G j S.walk.length := by
  classical
  let oddPrefixes : Finset ℕ :=
    M.image fun t ↦ (cycleArc C base t).length
  let evenPrefixes : Finset ℕ :=
    M.image fun t ↦ (cycleCoarc C base t).length
  have hoddCard : oddPrefixes.card = j := by
    change (M.image fun t ↦ (cycleArc C base t).length).card = j
    rw [Finset.card_image_of_injective _
      (cycleArc_length_injective C base), hMcard]
  have hevenCard : evenPrefixes.card = j := by
    change (M.image fun t ↦ (cycleCoarc C base t).length).card = j
    rw [Finset.card_image_of_injective _
      (cycleCoarc_length_injective C base), hMcard]
  have hoddNonempty : oddPrefixes.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hoddCard
    simp at hoddCard
    omega
  let oddMax := oddPrefixes.max' hoddNonempty
  have htargetL {t : Fin C.cycle.length} (ht : t ∈ M) :
      t ∈ cycleNeighborPositions C S.left := hML ht
  have htargetR {t : Fin C.cycle.length} (ht : t ∈ M) :
      t ∈ cycleNeighborPositions C S.right := hMR ht
  have hbase_ne {t : Fin C.cycle.length} (ht : t ∈ M) : base ≠ t := by
    intro h
    apply hbaseNot
    simpa [h] using ht
  have hbaseCycle : CycleAtLength G (S.walk.length + 2) :=
    commonNeighborBaseCycle C S base hbaseL hbaseR
  refine {
    path_pos := S.positive
    oddPrefixes := oddPrefixes
    oddPrefixMax := oddMax
    evenPrefixes := evenPrefixes
    odd_card := hoddCard
    even_card := hevenCard
    odd_values := ?_
    even_values := ?_
    oddPrefixMax_mem := Finset.max'_mem oddPrefixes hoddNonempty
    oddPrefix_le_max := fun b hb ↦ Finset.le_max' oddPrefixes b hb
    even_pos := ?_
    short_cycles := ?_
    even_path_long_cycle := ?_
    odd_path_base_cycle := hbaseCycle
    odd_path_long_cycles := ?_
  }
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact hodd t ht
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact (odd_cycleArc_iff_even_cycleCoarc C base t).mp (hodd t ht)
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    apply Nat.pos_of_ne_zero
    intro hzero
    have hverts := Walk.eq_of_length_eq_zero hzero
    exact (getVert_ne_of_fin_ne C (hbase_ne ht)) hverts.symm
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact (commonNeighborArcCycles C S base t (hbase_ne ht)
      hbaseL hbaseR (htargetL ht) (htargetR ht)).1
  · have hmem : oddMax ∈ oddPrefixes :=
      Finset.max'_mem oddPrefixes hoddNonempty
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
    rw [← heq]
    exact (commonNeighborArcCycles C S base t (hbase_ne ht)
      hbaseL hbaseR (htargetL ht) (htargetR ht)).2
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact (commonNeighborCoarcCycles C S base t (hbase_ne ht)
      hbaseL hbaseR (htargetL ht) (htargetR ht)).2

private noncomputable def sameNeighborhoodCertificate_of_even_forward_family
    (C : EndpointCount.LongestOddCycle G) (j : ℕ)
    (S : ExteriorPath C)
    (base : Fin C.cycle.length) (M : Finset (Fin C.cycle.length))
    (hMcard : M.card = j)
    (hbaseL : base ∈ cycleNeighborPositions C S.left)
    (hbaseR : base ∈ cycleNeighborPositions C S.right)
    (hML : M ⊆ cycleNeighborPositions C S.left)
    (hMR : M ⊆ cycleNeighborPositions C S.right)
    (hbaseNot : base ∉ M)
    (heven : ∀ t ∈ M, Even (cycleArc C base t).length)
    (hj : 0 < j) :
    SameNeighborhoodCertificate G j S.walk.length := by
  classical
  let oddPrefixes : Finset ℕ :=
    M.image fun t ↦ (cycleCoarc C base t).length
  let evenPrefixes : Finset ℕ :=
    M.image fun t ↦ (cycleArc C base t).length
  have hoddCard : oddPrefixes.card = j := by
    change (M.image fun t ↦ (cycleCoarc C base t).length).card = j
    rw [Finset.card_image_of_injective _
      (cycleCoarc_length_injective C base), hMcard]
  have hevenCard : evenPrefixes.card = j := by
    change (M.image fun t ↦ (cycleArc C base t).length).card = j
    rw [Finset.card_image_of_injective _
      (cycleArc_length_injective C base), hMcard]
  have hoddNonempty : oddPrefixes.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hoddCard
    simp at hoddCard
    omega
  let oddMax := oddPrefixes.max' hoddNonempty
  have htargetL {t : Fin C.cycle.length} (ht : t ∈ M) :
      t ∈ cycleNeighborPositions C S.left := hML ht
  have htargetR {t : Fin C.cycle.length} (ht : t ∈ M) :
      t ∈ cycleNeighborPositions C S.right := hMR ht
  have hbase_ne {t : Fin C.cycle.length} (ht : t ∈ M) : base ≠ t := by
    intro h
    apply hbaseNot
    simpa [h] using ht
  have hbaseCycle : CycleAtLength G (S.walk.length + 2) :=
    commonNeighborBaseCycle C S base hbaseL hbaseR
  refine {
    path_pos := S.positive
    oddPrefixes := oddPrefixes
    oddPrefixMax := oddMax
    evenPrefixes := evenPrefixes
    odd_card := hoddCard
    even_card := hevenCard
    odd_values := ?_
    even_values := ?_
    oddPrefixMax_mem := Finset.max'_mem oddPrefixes hoddNonempty
    oddPrefix_le_max := fun b hb ↦ Finset.le_max' oddPrefixes b hb
    even_pos := ?_
    short_cycles := ?_
    even_path_long_cycle := ?_
    odd_path_base_cycle := hbaseCycle
    odd_path_long_cycles := ?_
  }
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact (even_cycleArc_iff_odd_cycleCoarc C base t).mp (heven t ht)
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact heven t ht
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    apply Nat.pos_of_ne_zero
    intro hzero
    have hverts := Walk.eq_of_length_eq_zero hzero
    exact (getVert_ne_of_fin_ne C (hbase_ne ht)) hverts
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact (commonNeighborCoarcCycles C S base t (hbase_ne ht)
      hbaseL hbaseR (htargetL ht) (htargetR ht)).1
  · have hmem : oddMax ∈ oddPrefixes :=
      Finset.max'_mem oddPrefixes hoddNonempty
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
    rw [← heq]
    exact (commonNeighborCoarcCycles C S base t (hbase_ne ht)
      hbaseL hbaseR (htargetL ht) (htargetR ht)).2
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact (commonNeighborArcCycles C S base t (hbase_ne ht)
      hbaseL hbaseR (htargetL ht) (htargetR ht)).2

/-- Any explicitly selected set of `2 * j` positions adjacent to both
endpoints of the exterior path already realizes `j + 1` odd cycle lengths.
This is the subset form of the equal-neighbour boundary argument; the full
endpoint-neighbour finsets need not be equal. -/
theorem commonNeighborSubsetBoundary [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 0 < j)
    (S : ExteriorPath C) (X : Finset (Fin C.cycle.length))
    (hXcard : X.card = 2 * j)
    (hXL : X ⊆ cycleNeighborPositions C S.left)
    (hXR : X ⊆ cycleNeighborPositions C S.right) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  have hXnonempty : X.Nonempty := Finset.card_pos.mp (by omega)
  let base : Fin C.cycle.length := X.min' hXnonempty
  have hbaseX : base ∈ X := Finset.min'_mem X hXnonempty
  let T : Finset (Fin C.cycle.length) := X.erase base
  have hTcard : T.card = 2 * j - 1 := by
    change (X.erase base).card = 2 * j - 1
    rw [Finset.card_erase_of_mem hbaseX, hXcard]
  let oddT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Odd (cycleArc C base t).length
  let evenT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Even (cycleArc C base t).length
  have hpartition : evenT.card + oddT.card = T.card := by
    simpa [evenT, oddT, Nat.not_even_iff_odd] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (fun t ↦ Even (cycleArc C base t).length))
  have hmajority : j ≤ oddT.card ∨ j ≤ evenT.card := by omega
  have hbaseL : base ∈ cycleNeighborPositions C S.left := hXL hbaseX
  have hbaseR : base ∈ cycleNeighborPositions C S.right := hXR hbaseX
  rcases hmajority with hoddMajority | hevenMajority
  · obtain ⟨M, hMsub, hMcard⟩ :=
      Finset.exists_subset_card_eq hoddMajority
    have hMX : M ⊆ X := by
      intro t ht
      exact (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).2
    have hbaseNot : base ∉ M := by
      intro hb
      have htT : base ∈ T := (Finset.mem_filter.mp (hMsub hb)).1
      change base ∈ X.erase base at htT
      exact (Finset.mem_erase.mp htT).1 rfl
    have hodd : ∀ t ∈ M, Odd (cycleArc C base t).length := by
      intro t ht
      exact (Finset.mem_filter.mp (hMsub ht)).2
    exact sameNeighborhoodBoundary
      (sameNeighborhoodCertificate_of_odd_forward_family C j S base M
        hMcard hbaseL hbaseR (hMX.trans hXL) (hMX.trans hXR)
        hbaseNot hodd hj)
  · obtain ⟨M, hMsub, hMcard⟩ :=
      Finset.exists_subset_card_eq hevenMajority
    have hMX : M ⊆ X := by
      intro t ht
      exact (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).2
    have hbaseNot : base ∉ M := by
      intro hb
      have htT : base ∈ T := (Finset.mem_filter.mp (hMsub hb)).1
      change base ∈ X.erase base at htT
      exact (Finset.mem_erase.mp htT).1 rfl
    have heven : ∀ t ∈ M, Even (cycleArc C base t).length := by
      intro t ht
      exact (Finset.mem_filter.mp (hMsub ht)).2
    exact sameNeighborhoodBoundary
      (sameNeighborhoodCertificate_of_even_forward_family C j S base M
        hMcard hbaseL hbaseR (hMX.trans hXL) (hMX.trans hXR)
      hbaseNot heven hj)

/-! ## Two actual endpoint routes in the one-chord case -/

/-- Counting core when two ordered endpoint routes have even lengths.  The
`j - 1` odd cycle-path lengths give the ordinary two-spoke cycles.  Closing
the largest one through each route supplies two new, strictly ordered
lengths. -/
private theorem oneChordBoundary_of_even_routes [Finite V]
    {j r₁ r₂ bMax : ℕ} (hj : 2 ≤ j)
    (B : Finset ℕ) (hcard : B.card = j - 1)
    (hbMax : bMax ∈ B) (hmax : ∀ b ∈ B, b ≤ bMax)
    (hBodd : ∀ b ∈ B, Odd b)
    (hr₁pos : 0 < r₁) (hrlt : r₁ < r₂)
    (hr₁even : Even r₁) (hr₂even : Even r₂)
    (hshort : ∀ b ∈ B, CycleAtLength G (b + 2))
    (hlong₁ : CycleAtLength G (bMax + r₁ + 2))
    (hlong₂ : CycleAtLength G (bMax + r₂ + 2)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  have hnew : bMax + r₁ ∉ B := by
    intro hmem
    have := hmax _ hmem
    omega
  let P : Finset ℕ := insert (bMax + r₁) B
  have hPcard : P.card = j := by
    simp [P, hnew, hcard]
    omega
  have hoddMax : Odd bMax := hBodd bMax hbMax
  apply oneChordBoundary hj
  refine {
    prefixes := P
    prefixMax := bMax + r₁
    offset₁ := 2
    offset₂ := r₂ - r₁ + 2
    card_prefixes := hPcard
    prefixMax_mem := by simp [P]
    prefix_le_max := ?_
    offset_lt := by omega
    first_odd := ?_
    last_odd := ?_
    first_cycles := ?_
    last_cycle := ?_ }
  · intro b hb
    simp only [P, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact le_rfl
    · have := hmax b hb
      omega
  · intro b hb
    simp only [P, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · grind
    · simpa only [Nat.add_assoc] using (hBodd b hb).add_even (by decide : Even 2)
  · grind
  · intro b hb
    simp only [P, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · simpa [Nat.add_assoc] using hlong₁
    · exact hshort b hb
  · convert hlong₂ using 1 <;> omega

/-- Counting core when two ordered endpoint routes have odd lengths.  Their
base cycles give two lengths below the `j - 1` positive even-prefix cycles
closed through the longer route. -/
private theorem oneChordBoundary_of_odd_routes [Finite V]
    {j r₁ r₂ bMax : ℕ} (hj : 2 ≤ j)
    (B : Finset ℕ) (hcard : B.card = j - 1)
    (hbMax : bMax ∈ B) (hmax : ∀ b ∈ B, b ≤ bMax)
    (hBpos : ∀ b ∈ B, 0 < b) (hBeven : ∀ b ∈ B, Even b)
    (hrlt : r₁ < r₂) (hr₁odd : Odd r₁) (hr₂odd : Odd r₂)
    (hbase₁ : CycleAtLength G (r₁ + 2))
    (hlong₁ : ∀ b ∈ B, CycleAtLength G (b + r₁ + 2))
    (hlong₂ : CycleAtLength G (bMax + r₂ + 2)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  have hzero : 0 ∉ B := fun h ↦ (Nat.lt_irrefl 0) (hBpos 0 h)
  let P : Finset ℕ := insert 0 B
  have hPcard : P.card = j := by
    simp [P, hzero, hcard]
    omega
  apply oneChordBoundary hj
  refine {
    prefixes := P
    prefixMax := bMax
    offset₁ := r₁ + 2
    offset₂ := r₂ + 2
    card_prefixes := hPcard
    prefixMax_mem := by simp [P, hbMax]
    prefix_le_max := ?_
    offset_lt := by omega
    first_odd := ?_
    last_odd := ?_
    first_cycles := ?_
    last_cycle := hlong₂ }
  · intro b hb
    simp only [P, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact Nat.zero_le _
    · exact hmax b hb
  · intro b hb
    simp only [P, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · simpa using hr₁odd.add_even (by decide : Even 2)
    · grind
  · grind
  · intro b hb
    simp only [P, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · simpa using hbase₁
    · exact hlong₁ b hb

private theorem oneChordBoundary_of_even_routes_indexed [Finite V]
    {ι : Type*} {j r₁ r₂ : ℕ} (hj : 2 ≤ j)
    (M : Finset ι) (hMcard : M.card = j - 1) (len : ι → ℕ)
    (hinj : Set.InjOn len M) (hodd : ∀ i ∈ M, Odd (len i))
    (hr₁pos : 0 < r₁) (hrlt : r₁ < r₂)
    (hr₁even : Even r₁) (hr₂even : Even r₂)
    (hshort : ∀ i ∈ M, CycleAtLength G (len i + 2))
    (hlong₁ : ∀ i ∈ M, CycleAtLength G (len i + r₁ + 2))
    (hlong₂ : ∀ i ∈ M, CycleAtLength G (len i + r₂ + 2)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let B : Finset ℕ := M.image len
  have hBcard : B.card = j - 1 := by
    rw [show B = M.image len by rfl, Finset.card_image_iff.mpr hinj,
      hMcard]
  have hBnonempty : B.Nonempty := Finset.card_pos.mp (by omega)
  let bMax := B.max' hBnonempty
  have hbMax : bMax ∈ B := Finset.max'_mem B hBnonempty
  obtain ⟨iMax, hiMax, hiMaxEq⟩ := Finset.mem_image.mp hbMax
  apply oneChordBoundary_of_even_routes hj B hBcard hbMax
      (fun b hb ↦ Finset.le_max' B b hb)
      (by
        intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact hodd i hi)
      hr₁pos hrlt hr₁even hr₂even
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact hshort i hi
  · rw [← hiMaxEq]
    exact hlong₁ iMax hiMax
  · rw [← hiMaxEq]
    exact hlong₂ iMax hiMax

private theorem oneChordBoundary_of_odd_routes_indexed [Finite V]
    {ι : Type*} {j r₁ r₂ : ℕ} (hj : 2 ≤ j)
    (M : Finset ι) (hMcard : M.card = j - 1) (len : ι → ℕ)
    (hinj : Set.InjOn len M) (hpos : ∀ i ∈ M, 0 < len i)
    (heven : ∀ i ∈ M, Even (len i))
    (hrlt : r₁ < r₂) (hr₁odd : Odd r₁) (hr₂odd : Odd r₂)
    (hbase₁ : CycleAtLength G (r₁ + 2))
    (hlong₁ : ∀ i ∈ M, CycleAtLength G (len i + r₁ + 2))
    (hlong₂ : ∀ i ∈ M, CycleAtLength G (len i + r₂ + 2)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let B : Finset ℕ := M.image len
  have hBcard : B.card = j - 1 := by
    rw [show B = M.image len by rfl, Finset.card_image_iff.mpr hinj,
      hMcard]
  have hBnonempty : B.Nonempty := Finset.card_pos.mp (by omega)
  let bMax := B.max' hBnonempty
  have hbMax : bMax ∈ B := Finset.max'_mem B hBnonempty
  obtain ⟨iMax, hiMax, hiMaxEq⟩ := Finset.mem_image.mp hbMax
  apply oneChordBoundary_of_odd_routes hj B hBcard hbMax
      (fun b hb ↦ Finset.le_max' B b hb)
      (by
        intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact hpos i hi)
      (by
        intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact heven i hi)
      hrlt hr₁odd hr₂odd hbase₁
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact hlong₁ i hi
  · rw [← hiMaxEq]
    exact hlong₂ iMax hiMax

/-- A direct two-spoke connection (formal route length zero) and one
positive even endpoint route.  Here the selected odd cycle-path family
already has cardinality `j`, so the two offsets give the final extra
length. -/
private theorem oneChordBoundary_of_direct_even_route_indexed [Finite V]
    {ι : Type*} {j r : ℕ} (hj : 2 ≤ j)
    (M : Finset ι) (hMcard : M.card = j) (len : ι → ℕ)
    (hinj : Set.InjOn len M) (hodd : ∀ i ∈ M, Odd (len i))
    (hrpos : 0 < r) (hreven : Even r)
    (hshort : ∀ i ∈ M, CycleAtLength G (len i + 2))
    (hlong : ∀ i ∈ M, CycleAtLength G (len i + r + 2)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let B : Finset ℕ := M.image len
  have hBcard : B.card = j := by
    rw [show B = M.image len by rfl, Finset.card_image_iff.mpr hinj,
      hMcard]
  have hBnonempty : B.Nonempty := Finset.card_pos.mp (by omega)
  let bMax := B.max' hBnonempty
  have hbMax : bMax ∈ B := Finset.max'_mem B hBnonempty
  obtain ⟨iMax, hiMax, hiMaxEq⟩ := Finset.mem_image.mp hbMax
  apply oneChordBoundary hj
  refine {
    prefixes := B
    prefixMax := bMax
    offset₁ := 2
    offset₂ := r + 2
    card_prefixes := hBcard
    prefixMax_mem := hbMax
    prefix_le_max := fun b hb ↦ Finset.le_max' B b hb
    offset_lt := by omega
    first_odd := ?_
    last_odd := ?_
    first_cycles := ?_
    last_cycle := ?_ }
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact (hodd i hi).add_even (by decide : Even 2)
  · rw [← hiMaxEq]
    exact (hodd iMax hiMax).add_even hreven |>.add_even (by decide : Even 2)
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact hshort i hi
  · rw [← hiMaxEq]
    exact hlong iMax hiMax

/-- Balanced parity subcase for a genuine endpoint edge and a positive even
endpoint route.  The extra prefix `1` is realized by the triangle through the
endpoint edge; the hypothesis `1 < len i` keeps it below all selected cyclic
prefixes. -/
private theorem oneChordBoundary_of_edge_even_route_indexed [Finite V]
    {ι : Type*} {j r : ℕ} (hj : 2 ≤ j)
    (M : Finset ι) (hMcard : M.card = j - 1) (len : ι → ℕ)
    (hinj : Set.InjOn len M) (hodd : ∀ i ∈ M, Odd (len i))
    (hlen : ∀ i ∈ M, 1 < len i)
    (hrpos : 0 < r) (hreven : Even r)
    (hedge : CycleAtLength G 3)
    (hshort : ∀ i ∈ M, CycleAtLength G (len i + 2))
    (hlong : ∀ i ∈ M, CycleAtLength G (len i + r + 2)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let B : Finset ℕ := M.image len
  have hBcard : B.card = j - 1 := by
    rw [show B = M.image len by rfl, Finset.card_image_iff.mpr hinj,
      hMcard]
  have hBnonempty : B.Nonempty := Finset.card_pos.mp (by omega)
  let bMax := B.max' hBnonempty
  have hbMax : bMax ∈ B := Finset.max'_mem B hBnonempty
  obtain ⟨iMax, hiMax, hiMaxEq⟩ := Finset.mem_image.mp hbMax
  have honeNot : 1 ∉ B := by
    intro hone
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hone
    have := hlen i hi
    omega
  apply oneChordBoundary hj
  refine {
    prefixes := insert 1 B
    prefixMax := bMax
    offset₁ := 2
    offset₂ := r + 2
    card_prefixes := by
      rw [Finset.card_insert_of_notMem honeNot, hBcard]
      omega
    prefixMax_mem := Finset.mem_insert_of_mem hbMax
    prefix_le_max := ?_
    offset_lt := by omega
    first_odd := ?_
    last_odd := ?_
    first_cycles := ?_
    last_cycle := ?_ }
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · have := hlen iMax hiMax
      omega
    · exact Finset.le_max' B b hb
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · decide
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      exact (hodd i hi).add_even (by decide : Even 2)
  · rw [← hiMaxEq]
    exact (hodd iMax hiMax).add_even hreven |>.add_even (by decide : Even 2)
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hedge
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      exact hshort i hi
  · rw [← hiMaxEq]
    exact hlong iMax hiMax

/-- A positive even prefix family closed through one odd endpoint route,
together with the common-neighbour base cycle, gives one more odd length. -/
private theorem odd_route_family_with_base [Finite V]
    {ι : Type*} {j r : ℕ}
    (M : Finset ι) (hMcard : M.card = j) (len : ι → ℕ)
    (hinj : Set.InjOn len M) (hpos : ∀ i ∈ M, 0 < len i)
    (heven : ∀ i ∈ M, Even (len i)) (hrodd : Odd r)
    (hbase : CycleAtLength G (r + 2))
    (hlong : ∀ i ∈ M, CycleAtLength G (len i + r + 2)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let L : Finset ℕ := M.image fun i ↦ len i + r + 2
  have hLcard : L.card = j := by
    change (M.image fun i ↦ len i + r + 2).card = j
    rw [Finset.card_image_iff.mpr]
    · exact hMcard
    · intro a _ b _ hab
      exact hinj (by assumption) (by assumption)
        (Nat.add_right_cancel (Nat.add_right_cancel hab))
  have hbaseNot : r + 2 ∉ L := by
    intro hb
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hb
    have := hpos i hi
    omega
  let L' := insert (r + 2) L
  have hL'card : L'.card = j + 1 := by
    simp [L', hbaseNot, hLcard]
  apply hL'card ▸ ncard_oddCycleLengths_ge_of_finset (G := G) L'
  · intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact hrodd.add_even (by decide : Even 2)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      exact (heven i hi).add_odd hrodd |>.add_even (by decide : Even 2)
  · intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact hbase
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      exact hlong i hi

/-- Three explicitly ordered odd cycle lengths. -/
private theorem three_odd_cycle_lengths_of_lt [Finite V]
    {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (haodd : Odd a) (hbodd : Odd b) (hcodd : Odd c)
    (ha : CycleAtLength G a) (hb : CycleAtLength G b)
    (hc : CycleAtLength G c) :
    3 ≤ (oddCycleLengths G).ncard := by
  let L : Finset ℕ := {a, b, c}
  have hcard : L.card = 3 := by
    simp [L, Nat.ne_of_lt hab, Nat.ne_of_lt hbc,
      Nat.ne_of_lt (hab.trans hbc)]
  apply hcard ▸ ncard_oddCycleLengths_ge_of_finset (G := G) L
  · intro n hn
    simp only [L, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact haodd
    · exact hbodd
    · exact hcodd
  · intro n hn
    simp only [L, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc

/-- Two actual endpoint routes of distinct lengths and the same parity,
together with `2*j-1` common cycle neighbours, realize `j+1` odd cycle
lengths.  This is the graph-geometric and parity-counting core of the
one-chord boundary lemma for `j ≥ 2`. -/
theorem twoEndpointRoutesBoundary [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 2 ≤ j)
    (S : ExteriorPath C) (X : Finset (Fin C.cycle.length))
    (hXcard : X.card = 2 * j - 1)
    (hXL : X ⊆ cycleNeighborPositions C S.left)
    (hXR : X ⊆ cycleNeighborPositions C S.right)
    (R₁ R₂ : EndpointRoute S)
    (hrlt : R₁.walk.length < R₂.walk.length)
    (hsame : Even (R₁.walk.length + R₂.walk.length)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  have hXnonempty : X.Nonempty := Finset.card_pos.mp (by omega)
  let base : Fin C.cycle.length := X.min' hXnonempty
  have hbaseX : base ∈ X := Finset.min'_mem X hXnonempty
  let T : Finset (Fin C.cycle.length) := X.erase base
  have hTcard : T.card = 2 * j - 2 := by
    change (X.erase base).card = 2 * j - 2
    rw [Finset.card_erase_of_mem hbaseX, hXcard]
    omega
  let oddT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Odd (cycleArc C base t).length
  let evenT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Even (cycleArc C base t).length
  have hpartition : evenT.card + oddT.card = T.card := by
    simpa [evenT, oddT, Nat.not_even_iff_odd] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (fun t ↦ Even (cycleArc C base t).length))
  have hmajority : j - 1 ≤ oddT.card ∨ j - 1 ≤ evenT.card := by
    omega
  have hbaseL : base ∈ cycleNeighborPositions C S.left := hXL hbaseX
  have hbaseR : base ∈ cycleNeighborPositions C S.right := hXR hbaseX
  rcases hmajority with hoddMajority | hevenMajority
  · obtain ⟨M, hMsub, hMcard⟩ := Finset.exists_subset_card_eq hoddMajority
    have hMXL : M ⊆ cycleNeighborPositions C S.left := by
      intro t ht
      exact hXL (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).2
    have hMXR : M ⊆ cycleNeighborPositions C S.right := by
      intro t ht
      exact hXR (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).2
    have hbase_ne : ∀ t ∈ M, base ≠ t := by
      intro t ht hbt
      subst t
      exact (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).1 rfl
    have harcOdd : ∀ t ∈ M, Odd (cycleArc C base t).length := by
      intro t ht
      exact (Finset.mem_filter.mp (hMsub ht)).2
    rcases Nat.even_or_odd R₁.walk.length with hr₁even | hr₁odd
    · have hr₂even : Even R₂.walk.length := by grind
      apply oneChordBoundary_of_even_routes_indexed hj M hMcard
        (fun t ↦ (cycleArc C base t).length)
        (cycleArc_length_injective C base).injOn harcOdd R₁.positive hrlt
        hr₁even hr₂even
      · intro t ht
        exact (R₁.arcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).1
      · intro t ht
        exact (R₁.arcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2
      · intro t ht
        exact (R₂.arcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2

    · have hr₂odd : Odd R₂.walk.length := by grind
      apply oneChordBoundary_of_odd_routes_indexed hj M hMcard
        (fun t ↦ (cycleCoarc C base t).length)
        (cycleCoarc_length_injective C base).injOn
      · intro t ht
        apply Nat.pos_of_ne_zero
        intro hzero
        have hverts := Walk.eq_of_length_eq_zero hzero
        exact (getVert_ne_of_fin_ne C (hbase_ne t ht)) hverts.symm
      · intro t ht
        exact (odd_cycleArc_iff_even_cycleCoarc C base t).mp (harcOdd t ht)
      · exact hrlt
      · exact hr₁odd
      · exact hr₂odd
      · exact R₁.baseCycle C base hbaseL hbaseR
      · intro t ht
        exact (R₁.coarcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2
      · intro t ht
        exact (R₂.coarcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2
  · obtain ⟨M, hMsub, hMcard⟩ := Finset.exists_subset_card_eq hevenMajority
    have hMXL : M ⊆ cycleNeighborPositions C S.left := by
      intro t ht
      exact hXL (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).2
    have hMXR : M ⊆ cycleNeighborPositions C S.right := by
      intro t ht
      exact hXR (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).2
    have hbase_ne : ∀ t ∈ M, base ≠ t := by
      intro t ht hbt
      subst t
      exact (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).1 rfl
    have harcEven : ∀ t ∈ M, Even (cycleArc C base t).length := by
      intro t ht
      exact (Finset.mem_filter.mp (hMsub ht)).2
    rcases Nat.even_or_odd R₁.walk.length with hr₁even | hr₁odd
    · have hr₂even : Even R₂.walk.length := by grind
      apply oneChordBoundary_of_even_routes_indexed hj M hMcard
        (fun t ↦ (cycleCoarc C base t).length)
        (cycleCoarc_length_injective C base).injOn
      · intro t ht
        exact (even_cycleArc_iff_odd_cycleCoarc C base t).mp (harcEven t ht)
      · exact R₁.positive
      · exact hrlt
      · exact hr₁even
      · exact hr₂even
      · intro t ht
        exact (R₁.coarcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).1
      · intro t ht
        exact (R₁.coarcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2
      · intro t ht
        exact (R₂.coarcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2
    · have hr₂odd : Odd R₂.walk.length := by grind
      apply oneChordBoundary_of_odd_routes_indexed hj M hMcard
        (fun t ↦ (cycleArc C base t).length)
        (cycleArc_length_injective C base).injOn
      · intro t ht
        apply Nat.pos_of_ne_zero
        intro hzero
        have hverts := Walk.eq_of_length_eq_zero hzero
        exact (getVert_ne_of_fin_ne C (hbase_ne t ht)) hverts
      · exact harcEven
      · exact hrlt
      · exact hr₁odd
      · exact hr₂odd
      · exact R₁.baseCycle C base hbaseL hbaseR
      · intro t ht
        exact (R₁.arcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2
      · intro t ht
        exact (R₂.arcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2

/-- The direct `j ≥ 2` one-chord branch when the selected left chord has
odd position.  The original exterior path and the left-chord shortcut then
have distinct lengths of the same parity, so `twoEndpointRoutesBoundary`
applies. -/
theorem oneChordEachBoundary_of_odd_left_position [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 2 ≤ j)
    (D : OneChordEachConfiguration C j)
    (a : Fin (D.exterior.walk.length + 1))
    (ha : a ∈ leftChordPositions D.exterior) (haodd : Odd (a : ℕ)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let R₁ : EndpointRoute D.exterior := D.exterior.leftChordRoute a ha
  let R₂ : EndpointRoute D.exterior := D.exterior.toEndpointRoute
  have hrlt : R₁.walk.length < R₂.walk.length := by
    simp only [R₁, R₂, ExteriorPath.leftChordRoute_length,
      ExteriorPath.toEndpointRoute]
    have := (mem_leftChordPositions D.exterior a).mp ha |>.1
    omega
  have hsame : Even (R₁.walk.length + R₂.walk.length) := by
    simp only [R₁, R₂, ExteriorPath.leftChordRoute_length,
      ExteriorPath.toEndpointRoute]
    grind
  refine twoEndpointRoutesBoundary C hj D.exterior
    (cycleNeighborPositions C D.exterior.left)
    D.cycle_neighbor_card (fun _ h ↦ h) ?_ R₁ R₂ hrlt hsame
  intro i hi
  rw [← D.same_neighbors]
  exact hi

/-- Apart from the crossing equality `a + b = |S|`, the three evident
endpoint routes (the original path and the two one-chord shortcuts) contain
two distinct lengths of the same parity. -/
theorem oneChordEachBoundary_of_nonexceptional_positions [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 2 ≤ j)
    (D : OneChordEachConfiguration C j)
    (a b : Fin (D.exterior.walk.length + 1))
    (ha : a ∈ leftChordPositions D.exterior)
    (hb : b ∈ rightChordPositions D.exterior)
    (hne : (a : ℕ) + b ≠ D.exterior.walk.length) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let X := cycleNeighborPositions C D.exterior.left
  have hXL : X ⊆ cycleNeighborPositions C D.exterior.left := fun _ h ↦ h
  have hXR : X ⊆ cycleNeighborPositions C D.exterior.right := by
    intro i hi
    rw [← D.same_neighbors]
    exact hi
  rcases Nat.even_or_odd (a : ℕ) with haeven | haodd
  · let RL : EndpointRoute D.exterior := D.exterior.leftChordRoute a ha
    let RR : EndpointRoute D.exterior := D.exterior.rightChordRoute b hb
    let RS : EndpointRoute D.exterior := D.exterior.toEndpointRoute
    have hLlen : RL.walk.length = D.exterior.walk.length - a + 1 := by
      simp [RL]
    have hRlen : RR.walk.length = (b : ℕ) + 1 := by simp [RR]
    have hSlen : RS.walk.length = D.exterior.walk.length := rfl
    rcases Nat.even_or_odd (RR.walk.length + RS.walk.length) with hrsame | hropp
    · have hrlt : RR.walk.length < RS.walk.length := by
        rw [hRlen, hSlen]
        exact (mem_rightChordPositions D.exterior b).mp hb |>.1
      exact twoEndpointRoutesBoundary C hj D.exterior X
        D.cycle_neighbor_card hXL hXR RR RS hrlt hrsame
    · have hlsame : Even (RL.walk.length + RR.walk.length) := by
        rw [hLlen, hRlen]
        grind
      have hlne : RL.walk.length ≠ RR.walk.length := by
        rw [hLlen, hRlen]
        intro heq
        have hale : (a : ℕ) ≤ D.exterior.walk.length := by omega
        apply hne
        omega
      rcases lt_or_gt_of_ne hlne with hlr | hrl
      · exact twoEndpointRoutesBoundary C hj D.exterior X
          D.cycle_neighbor_card hXL hXR RL RR hlr hlsame
      · exact twoEndpointRoutesBoundary C hj D.exterior X
          D.cycle_neighbor_card hXL hXR RR RL hrl (by grind)
  · exact oneChordEachBoundary_of_odd_left_position C hj D a ha haodd

/-- In the crossing equality `a+b=|S|`, if both chord positions are at
least two steps from the opposite endpoint, the both-chord route is shorter
than `S` and has the same parity. -/
theorem oneChordEachBoundary_of_crossing_interior [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 2 ≤ j)
    (D : OneChordEachConfiguration C j)
    (a b : Fin (D.exterior.walk.length + 1))
    (ha : a ∈ leftChordPositions D.exterior)
    (hb : b ∈ rightChordPositions D.exterior)
    (hsum : (a : ℕ) + b = D.exterior.walk.length)
    (hbge : 2 ≤ (b : ℕ)) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  have hage : 2 ≤ (a : ℕ) := by
    exact (mem_leftChordPositions D.exterior a).mp ha |>.1
  have hmin : 0 < min (a : ℕ) b := by omega
  have hmax : max (a : ℕ) b < D.exterior.walk.length := by omega
  let R₁ : EndpointRoute D.exterior :=
    D.exterior.bothChordRoute a b ha hb hmin hmax
  let R₂ : EndpointRoute D.exterior := D.exterior.toEndpointRoute
  have hrlt : R₁.walk.length < R₂.walk.length := by
    simp only [R₁, R₂, ExteriorPath.bothChordRoute_length,
      ExteriorPath.toEndpointRoute]
    rw [Nat.dist_eq_max_sub_min]
    omega
  have hsame : Even (R₁.walk.length + R₂.walk.length) := by
    simp only [R₁, R₂, ExteriorPath.bothChordRoute_length,
      ExteriorPath.toEndpointRoute]
    rw [Nat.dist_eq_max_sub_min]
    grind
  refine twoEndpointRoutesBoundary C hj D.exterior
    (cycleNeighborPositions C D.exterior.left)
    D.cycle_neighbor_card (fun _ h ↦ h) ?_ R₁ R₂ hrlt hsame
  intro i hi
  rw [← D.same_neighbors]
  exact hi

/-- The first exceptional crossing position: the selected right chord is the
endpoint edge itself (`b = 0`), so the original path and that edge have
opposite parity.  When the original path is even, an unbalanced parity class
uses the direct two-spoke cycles and the path cycles.  In the balanced class,
the endpoint edge contributes the extra prefix `1`; a cycle arc of length
`1` would make its complementary arc close through that edge to an odd cycle
two edges longer than `C`, so every selected prefix is strictly larger. -/
theorem oneChordEachBoundary_of_crossing_zero [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 2 ≤ j)
    (D : OneChordEachConfiguration C j)
    (a b : Fin (D.exterior.walk.length + 1))
    (_ha : a ∈ leftChordPositions D.exterior)
    (hb : b ∈ rightChordPositions D.exterior)
    (_hsum : (a : ℕ) + b = D.exterior.walk.length)
    (hbzero : (b : ℕ) = 0)
    (hpathEven : Even D.exterior.walk.length) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let X := cycleNeighborPositions C D.exterior.left
  have hXnonempty : X.Nonempty := Finset.card_pos.mp (by
    change 0 < (cycleNeighborPositions C D.exterior.left).card
    rw [D.cycle_neighbor_card]
    omega)
  let base : Fin C.cycle.length := X.min' hXnonempty
  have hbaseX : base ∈ X := Finset.min'_mem X hXnonempty
  let T : Finset (Fin C.cycle.length) := X.erase base
  have hTcard : T.card = 2 * j - 2 := by
    change (X.erase base).card = 2 * j - 2
    rw [Finset.card_erase_of_mem hbaseX, D.cycle_neighbor_card]
    omega
  let oddT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Odd (cycleArc C base t).length
  let evenT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Even (cycleArc C base t).length
  have hpartition : evenT.card + oddT.card = T.card := by
    simpa [evenT, oddT, Nat.not_even_iff_odd] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (fun t ↦ Even (cycleArc C base t).length))
  have hbaseL : base ∈ cycleNeighborPositions C D.exterior.left := hbaseX
  have hbaseR : base ∈ cycleNeighborPositions C D.exterior.right := by
    rw [← D.same_neighbors]
    exact hbaseX
  let RE : EndpointRoute D.exterior := D.exterior.rightChordRoute b hb
  let RS : EndpointRoute D.exterior := D.exterior.toEndpointRoute
  have hRElen : RE.walk.length = 1 := by simp [RE, hbzero]
  have hRSlen : RS.walk.length = D.exterior.walk.length := rfl
  by_cases hoddMajority : j ≤ oddT.card
  · obtain ⟨M, hMsub, hMcard⟩ :=
      Finset.exists_subset_card_eq hoddMajority
    have hMXL : M ⊆ cycleNeighborPositions C D.exterior.left := by
      intro t ht
      exact (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).2
    have hMXR : M ⊆ cycleNeighborPositions C D.exterior.right := by
      intro t ht
      rw [← D.same_neighbors]
      exact hMXL ht
    have hbase_ne : ∀ t ∈ M, base ≠ t := by
      intro t ht hbt
      subst t
      exact (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).1 rfl
    apply oneChordBoundary_of_direct_even_route_indexed hj M hMcard
      (fun t ↦ (cycleArc C base t).length)
      (cycleArc_length_injective C base).injOn
    · intro t ht
      exact (Finset.mem_filter.mp (hMsub ht)).2
    · exact D.exterior.positive
    · exact hpathEven
    · intro t ht
      exact (RS.arcCycles C base t (hbase_ne t ht)
        hbaseL hbaseR (hMXL ht) (hMXR ht)).1
    · intro t ht
      simpa [hRSlen] using
        (RS.arcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2
  · by_cases hevenMajority : j ≤ evenT.card
    · obtain ⟨M, hMsub, hMcard⟩ :=
        Finset.exists_subset_card_eq hevenMajority
      have hMXL : M ⊆ cycleNeighborPositions C D.exterior.left := by
        intro t ht
        exact (Finset.mem_erase.mp
          (Finset.mem_filter.mp (hMsub ht)).1).2
      have hMXR : M ⊆ cycleNeighborPositions C D.exterior.right := by
        intro t ht
        rw [← D.same_neighbors]
        exact hMXL ht
      have hbase_ne : ∀ t ∈ M, base ≠ t := by
        intro t ht hbt
        subst t
        exact (Finset.mem_erase.mp
          (Finset.mem_filter.mp (hMsub ht)).1).1 rfl
      apply oneChordBoundary_of_direct_even_route_indexed hj M hMcard
        (fun t ↦ (cycleCoarc C base t).length)
        (cycleCoarc_length_injective C base).injOn
      · intro t ht
        exact (even_cycleArc_iff_odd_cycleCoarc C base t).mp
          ((Finset.mem_filter.mp (hMsub ht)).2)
      · exact D.exterior.positive
      · exact hpathEven
      · intro t ht
        exact (RS.coarcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).1
      · intro t ht
        simpa [hRSlen] using
          (RS.coarcCycles C base t (hbase_ne t ht)
            hbaseL hbaseR (hMXL ht) (hMXR ht)).2
    · have hoddCard : oddT.card = j - 1 := by omega
      have hevenCard : evenT.card = j - 1 := by omega
      have hoddXL : oddT ⊆ cycleNeighborPositions C D.exterior.left := by
        intro t ht
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).2
      have hoddXR : oddT ⊆ cycleNeighborPositions C D.exterior.right := by
        intro t ht
        rw [← D.same_neighbors]
        exact hoddXL ht
      have hbase_ne : ∀ t ∈ oddT, base ≠ t := by
        intro t ht hbt
        subst t
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).1 rfl
      have harcOdd : ∀ t ∈ oddT, Odd (cycleArc C base t).length := by
        intro t ht
        exact (Finset.mem_filter.mp ht).2
      have harcGt : ∀ t ∈ oddT, 1 < (cycleArc C base t).length := by
        intro t ht
        have hpos : 0 < (cycleArc C base t).length := by
          apply Nat.pos_of_ne_zero
          intro hzero
          have hverts := Walk.eq_of_length_eq_zero hzero
          exact (getVert_ne_of_fin_ne C (hbase_ne t ht)) hverts
        by_contra hnot
        have harcEq : (cycleArc C base t).length = 1 := by omega
        have hlongRaw := (RE.coarcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hoddXL ht) (hoddXR ht)).2
        have hlong : CycleAtLength G (C.cycle.length + 2) := by
          convert hlongRaw using 1
          have hsum := cycleArc_add_cycleCoarc_length C base t
          omega
        have hlongOdd : Odd (C.cycle.length + 2) := by
          rcases C.odd_length with ⟨q, hq⟩
          exact ⟨q + 1, by omega⟩
        have hle := C.longest (hlong.mem_oddCycleLengths hlongOdd)
        omega
      apply oneChordBoundary_of_edge_even_route_indexed hj oddT hoddCard
        (fun t ↦ (cycleArc C base t).length)
        (cycleArc_length_injective C base).injOn harcOdd harcGt
        D.exterior.positive hpathEven
      · have hbase := RE.baseCycle C base hbaseL hbaseR
        simpa [hRElen] using hbase
      · intro t ht
        exact (RS.arcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hoddXL ht) (hoddXR ht)).1
      · intro t ht
        simpa [hRSlen] using
          (RS.arcCycles C base t (hbase_ne t ht)
            hbaseL hbaseR (hoddXL ht) (hoddXR ht)).2

/-- The second exceptional crossing position: the selected right chord is at
`b = 1`, the selected left chord is at `a = |S|-1`, and `|S|` is odd.  The
right-chord shortcut has length two.  In the balanced parity case the odd
short-cycle family and the even-prefix family closed through `S` are
disjoint: an equality would be precisely a wrapping cycle of length
`C.length+2`.  This immediately closes `j ≥ 3`; the remaining `j = 2` tail
uses the base cycle and the length-two shortcut, with maximality resolving
the unique possible collision. -/
theorem oneChordEachBoundary_of_crossing_one [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 2 ≤ j)
    (D : OneChordEachConfiguration C j)
    (a b : Fin (D.exterior.walk.length + 1))
    (_ha : a ∈ leftChordPositions D.exterior)
    (hb : b ∈ rightChordPositions D.exterior)
    (_hsum : (a : ℕ) + b = D.exterior.walk.length)
    (hbone : (b : ℕ) = 1)
    (hpathOdd : Odd D.exterior.walk.length) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let X := cycleNeighborPositions C D.exterior.left
  have hXnonempty : X.Nonempty := Finset.card_pos.mp (by
    change 0 < (cycleNeighborPositions C D.exterior.left).card
    rw [D.cycle_neighbor_card]
    omega)
  let base : Fin C.cycle.length := X.min' hXnonempty
  have hbaseX : base ∈ X := Finset.min'_mem X hXnonempty
  let T : Finset (Fin C.cycle.length) := X.erase base
  have hTcard : T.card = 2 * j - 2 := by
    change (X.erase base).card = 2 * j - 2
    rw [Finset.card_erase_of_mem hbaseX, D.cycle_neighbor_card]
    omega
  let oddT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Odd (cycleArc C base t).length
  let evenT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Even (cycleArc C base t).length
  have hpartition : evenT.card + oddT.card = T.card := by
    simpa [evenT, oddT, Nat.not_even_iff_odd] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (fun t ↦ Even (cycleArc C base t).length))
  have hbaseL : base ∈ cycleNeighborPositions C D.exterior.left := hbaseX
  have hbaseR : base ∈ cycleNeighborPositions C D.exterior.right := by
    rw [← D.same_neighbors]
    exact hbaseX
  let R2 : EndpointRoute D.exterior := D.exterior.rightChordRoute b hb
  let RS : EndpointRoute D.exterior := D.exterior.toEndpointRoute
  have hR2len : R2.walk.length = 2 := by simp [R2, hbone]
  have hRSlen : RS.walk.length = D.exterior.walk.length := rfl
  by_cases hoddMajority : j ≤ oddT.card
  · obtain ⟨M, hMsub, hMcard⟩ :=
      Finset.exists_subset_card_eq hoddMajority
    have hMXL : M ⊆ cycleNeighborPositions C D.exterior.left := by
      intro t ht
      exact (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).2
    have hMXR : M ⊆ cycleNeighborPositions C D.exterior.right := by
      intro t ht
      rw [← D.same_neighbors]
      exact hMXL ht
    have hbase_ne : ∀ t ∈ M, base ≠ t := by
      intro t ht hbt
      subst t
      exact (Finset.mem_erase.mp
        (Finset.mem_filter.mp (hMsub ht)).1).1 rfl
    apply oneChordBoundary_of_direct_even_route_indexed (r := 2) hj M hMcard
      (fun t ↦ (cycleArc C base t).length)
      (cycleArc_length_injective C base).injOn
    · intro t ht
      exact (Finset.mem_filter.mp (hMsub ht)).2
    · decide
    · decide
    · intro t ht
      exact (R2.arcCycles C base t (hbase_ne t ht)
        hbaseL hbaseR (hMXL ht) (hMXR ht)).1
    · intro t ht
      simpa [hR2len] using
        (R2.arcCycles C base t (hbase_ne t ht)
          hbaseL hbaseR (hMXL ht) (hMXR ht)).2
  · by_cases hevenMajority : j ≤ evenT.card
    · obtain ⟨M, hMsub, hMcard⟩ :=
        Finset.exists_subset_card_eq hevenMajority
      have hMXL : M ⊆ cycleNeighborPositions C D.exterior.left := by
        intro t ht
        exact (Finset.mem_erase.mp
          (Finset.mem_filter.mp (hMsub ht)).1).2
      have hMXR : M ⊆ cycleNeighborPositions C D.exterior.right := by
        intro t ht
        rw [← D.same_neighbors]
        exact hMXL ht
      have hbase_ne : ∀ t ∈ M, base ≠ t := by
        intro t ht hbt
        subst t
        exact (Finset.mem_erase.mp
          (Finset.mem_filter.mp (hMsub ht)).1).1 rfl
      apply odd_route_family_with_base M hMcard
        (fun t ↦ (cycleArc C base t).length)
        (cycleArc_length_injective C base).injOn
      · intro t ht
        apply Nat.pos_of_ne_zero
        intro hzero
        have hverts := Walk.eq_of_length_eq_zero hzero
        exact (getVert_ne_of_fin_ne C (hbase_ne t ht)) hverts
      · intro t ht
        exact (Finset.mem_filter.mp (hMsub ht)).2
      · exact hpathOdd
      · simpa [hRSlen] using RS.baseCycle C base hbaseL hbaseR
      · intro t ht
        simpa [hRSlen] using
          (RS.arcCycles C base t (hbase_ne t ht)
            hbaseL hbaseR (hMXL ht) (hMXR ht)).2
    · have hoddCard : oddT.card = j - 1 := by omega
      have hevenCard : evenT.card = j - 1 := by omega
      have hoddXL : oddT ⊆ cycleNeighborPositions C D.exterior.left := by
        intro t ht
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).2
      have hoddXR : oddT ⊆ cycleNeighborPositions C D.exterior.right := by
        intro t ht
        rw [← D.same_neighbors]
        exact hoddXL ht
      have hevenXL : evenT ⊆ cycleNeighborPositions C D.exterior.left := by
        intro t ht
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).2
      have hevenXR : evenT ⊆ cycleNeighborPositions C D.exterior.right := by
        intro t ht
        rw [← D.same_neighbors]
        exact hevenXL ht
      have hbase_ne_odd : ∀ t ∈ oddT, base ≠ t := by
        intro t ht hbt
        subst t
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).1 rfl
      have hbase_ne_even : ∀ t ∈ evenT, base ≠ t := by
        intro t ht hbt
        subst t
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).1 rfl
      have harcOdd : ∀ t ∈ oddT, Odd (cycleArc C base t).length := by
        intro t ht
        exact (Finset.mem_filter.mp ht).2
      have harcEven : ∀ t ∈ evenT, Even (cycleArc C base t).length := by
        intro t ht
        exact (Finset.mem_filter.mp ht).2
      have harcPosOdd : ∀ t ∈ oddT, 0 < (cycleArc C base t).length := by
        intro t ht
        apply Nat.pos_of_ne_zero
        intro hzero
        have hverts := Walk.eq_of_length_eq_zero hzero
        exact (getVert_ne_of_fin_ne C (hbase_ne_odd t ht)) hverts
      have harcPosEven : ∀ t ∈ evenT, 0 < (cycleArc C base t).length := by
        intro t ht
        apply Nat.pos_of_ne_zero
        intro hzero
        have hverts := Walk.eq_of_length_eq_zero hzero
        exact (getVert_ne_of_fin_ne C (hbase_ne_even t ht)) hverts
      by_cases hj3 : 3 ≤ j
      · let LO : Finset ℕ := oddT.image fun t ↦ (cycleArc C base t).length + 2
        let LE : Finset ℕ := evenT.image fun t ↦
          (cycleArc C base t).length + D.exterior.walk.length + 2
        have hLOcard : LO.card = j - 1 := by
          change (oddT.image fun t ↦ (cycleArc C base t).length + 2).card = j - 1
          rw [Finset.card_image_iff.mpr]
          · exact hoddCard
          · intro x _ y _ hxy
            exact cycleArc_length_injective C base
              (Nat.add_right_cancel hxy)
        have hLEcard : LE.card = j - 1 := by
          change (evenT.image fun t ↦
            (cycleArc C base t).length + D.exterior.walk.length + 2).card = j - 1
          rw [Finset.card_image_iff.mpr]
          · exact hevenCard
          · intro x _ y _ hxy
            apply cycleArc_length_injective C base
            exact Nat.add_right_cancel (Nat.add_right_cancel hxy)
        have hdisj : Disjoint LO LE := by
          rw [Finset.disjoint_left]
          intro n hnO hnE
          obtain ⟨o, ho, hoEq⟩ := Finset.mem_image.mp hnO
          obtain ⟨e, he, heEq⟩ := Finset.mem_image.mp hnE
          apply mixedWrapContradiction_of_arc_eq C D.exterior base o e
            (hoddXR ho) (hevenXL he)
          omega
        let L := LO ∪ LE
        have hLcard : L.card = 2 * j - 2 := by
          change (LO ∪ LE).card = 2 * j - 2
          rw [Finset.card_union_of_disjoint hdisj, hLOcard, hLEcard]
          omega
        have hcount : L.card ≤ (oddCycleLengths G).ncard := by
          apply ncard_oddCycleLengths_ge_of_finset L
          · intro n hn
            rcases Finset.mem_union.mp hn with hn | hn
            · obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hn
              exact (harcOdd o ho).add_even (by decide : Even 2)
            · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
              exact (harcEven e he).add_odd hpathOdd |>.add_even
                (by decide : Even 2)
          · intro n hn
            rcases Finset.mem_union.mp hn with hn | hn
            · obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hn
              exact (RS.arcCycles C base o (hbase_ne_odd o ho)
                hbaseL hbaseR (hoddXL ho) (hoddXR ho)).1
            · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
              simpa [hRSlen] using
                (RS.arcCycles C base e (hbase_ne_even e he)
                  hbaseL hbaseR (hevenXL he) (hevenXR he)).2
        rw [hLcard] at hcount
        omega
      · have hjEq : j = 2 := by omega
        have hoddOne : oddT.card = 1 := by omega
        have hevenOne : evenT.card = 1 := by omega
        obtain ⟨o, hoddEq⟩ := Finset.card_eq_one.mp hoddOne
        obtain ⟨e, hevenEq⟩ := Finset.card_eq_one.mp hevenOne
        have ho : o ∈ oddT := by simp [hoddEq]
        have he : e ∈ evenT := by simp [hevenEq]
        let g := (cycleArc C base o).length
        let q := (cycleArc C base e).length
        let n := D.exterior.walk.length
        have hgOdd : Odd g := harcOdd o ho
        have hqEven : Even q := harcEven e he
        have hgPos : 0 < g := harcPosOdd o ho
        have hqPos : 0 < q := harcPosEven e he
        have hbaseCycle : CycleAtLength G (n + 2) := by
          simpa [n, hRSlen] using RS.baseCycle C base hbaseL hbaseR
        have hshortCycle : CycleAtLength G (g + 2) := by
          exact (RS.arcCycles C base o (hbase_ne_odd o ho)
            hbaseL hbaseR (hoddXL ho) (hoddXR ho)).1
        have hrouteCycle : CycleAtLength G (g + 4) := by
          have hraw := (R2.arcCycles C base o (hbase_ne_odd o ho)
            hbaseL hbaseR (hoddXL ho) (hoddXR ho)).2
          simpa [g, hR2len] using hraw
        have hevenLongCycle : CycleAtLength G (q + n + 2) := by
          have hraw := (RS.arcCycles C base e (hbase_ne_even e he)
            hbaseL hbaseR (hevenXL he) (hevenXR he)).2
          simpa [q, n, hRSlen] using hraw
        have hbaseOdd : Odd (n + 2) := by
          exact hpathOdd.add_even (by decide : Even 2)
        have hshortOdd : Odd (g + 2) :=
          hgOdd.add_even (by decide : Even 2)
        have hrouteOdd : Odd (g + 4) :=
          hgOdd.add_even (by decide : Even 4)
        have hevenLongOdd : Odd (q + n + 2) :=
          hqEven.add_odd hpathOdd |>.add_even (by decide : Even 2)
        rcases lt_trichotomy g n with hgn | hEq | hng
        · have hlast : n + 2 < q + n + 2 := by omega
          simpa [hjEq] using three_odd_cycle_lengths_of_lt
            (G := G) (by omega : g + 2 < n + 2) hlast
            hshortOdd hbaseOdd hevenLongOdd
            hshortCycle hbaseCycle hevenLongCycle
        · have hqge : 2 ≤ q := by
            rcases hqEven with ⟨r, hr⟩
            omega
          by_cases hqEq : q = 2
          · have hcoPos : 0 < (cycleCoarc C base o).length := by
              apply Nat.pos_of_ne_zero
              intro hzero
              have hverts := Walk.eq_of_length_eq_zero hzero
              exact (getVert_ne_of_fin_ne C (hbase_ne_odd o ho)) hverts.symm
            have hClt : n < C.cycle.length := by
              have hsum := cycleArc_add_cycleCoarc_length C base o
              omega
            rcases hpathOdd with ⟨rn, hrn⟩
            rcases C.odd_length with ⟨rC, hrC⟩
            by_cases hlarge : n + 4 < C.cycle.length
            · have horiginal : CycleAtLength G C.cycle.length :=
                ⟨C.base, C.cycle, C.isCycle, rfl⟩
              have hrouteOddN : Odd (n + 4) := by
                simpa [hEq] using hrouteOdd
              simpa [hjEq, hEq] using three_odd_cycle_lengths_of_lt
                (G := G) (by omega : n + 2 < n + 4) hlarge
                hbaseOdd hrouteOddN C.odd_length
                hbaseCycle (by simpa [hEq] using hrouteCycle) horiginal
            · have hsmall : C.cycle.length = n + 2 ∨
                  C.cycle.length = n + 4 := by omega
              rcases hsmall with hCeq | hCeq
              · have hlong : CycleAtLength G (C.cycle.length + 2) := by
                  simpa [hEq, hCeq] using hrouteCycle
                have hlongOdd : Odd (C.cycle.length + 2) :=
                  C.odd_length.add_even (by decide : Even 2)
                have hle := C.longest
                  (hlong.mem_oddCycleLengths hlongOdd)
                omega
              · have hraw := (RS.coarcCycles C base o
                    (hbase_ne_odd o ho) hbaseL hbaseR
                    (hoddXL ho) (hoddXR ho)).2
                have hlong : CycleAtLength G (C.cycle.length + 2) := by
                  convert hraw using 1
                  have hsum := cycleArc_add_cycleCoarc_length C base o
                  omega
                have hlongOdd : Odd (C.cycle.length + 2) := by
                  exact C.odd_length.add_even (by decide : Even 2)
                have hle := C.longest
                  (hlong.mem_oddCycleLengths hlongOdd)
                omega
          · have hqgt : 2 < q := by omega
            simpa [hjEq, hEq] using three_odd_cycle_lengths_of_lt
              (G := G) (by omega : n + 2 < g + 4)
              (by omega : g + 4 < q + n + 2)
              hbaseOdd hrouteOdd hevenLongOdd
              hbaseCycle hrouteCycle hevenLongCycle
        · have hBDne : g + 2 ≠ q + n + 2 := by
            intro heq
            apply mixedWrapContradiction_of_arc_eq C D.exterior base o e
              (hoddXR ho) (hevenXL he)
            dsimp [g, q, n] at heq
            omega
          rcases lt_or_gt_of_ne hBDne with hBD | hDB
          · simpa [hjEq] using three_odd_cycle_lengths_of_lt
              (G := G) (by omega : n + 2 < g + 2) hBD
              hbaseOdd hshortOdd hevenLongOdd
              hbaseCycle hshortCycle hevenLongCycle
          · simpa [hjEq] using three_odd_cycle_lengths_of_lt
              (G := G) (by omega : n + 2 < q + n + 2) hDB
              hbaseOdd hevenLongOdd hshortOdd
              hbaseCycle hevenLongCycle hshortCycle

/-- **Concrete one-chord boundary theorem for `j ≥ 2`.**  This consumes only
the actual longest odd cycle, actual exterior path, common cycle-neighbour
set, and selected endpoint chords recorded by
`OneChordEachConfiguration`.  The route-position classification is exhaustive:
noncrossing positions, an interior crossing, and the two endpoint exceptions
`b=0` and `b=1`. -/
theorem oneChordEachBoundary_of_two_le [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 2 ≤ j)
    (D : OneChordEachConfiguration C j) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  have hleftNonempty : (leftChordPositions D.exterior).Nonempty :=
    Finset.card_pos.mp (by rw [D.left_chord_card]; decide)
  obtain ⟨a, ha⟩ := hleftNonempty
  obtain ⟨b, hb⟩ := D.right_chord_nonempty
  by_cases hsum : (a : ℕ) + b = D.exterior.walk.length
  · rcases Nat.even_or_odd (a : ℕ) with haEven | haOdd
    · by_cases hbge : 2 ≤ (b : ℕ)
      · exact oneChordEachBoundary_of_crossing_interior C hj D a b
          ha hb hsum hbge
      · have hbsmall : (b : ℕ) = 0 ∨ (b : ℕ) = 1 := by omega
        rcases hbsmall with hbzero | hbone
        · have hpathEven : Even D.exterior.walk.length := by grind
          exact oneChordEachBoundary_of_crossing_zero C hj D a b
            ha hb hsum hbzero hpathEven
        · have hpathOdd : Odd D.exterior.walk.length := by grind
          exact oneChordEachBoundary_of_crossing_one C hj D a b
            ha hb hsum hbone hpathOdd
    · exact oneChordEachBoundary_of_odd_left_position C hj D a ha haOdd
  · exact oneChordEachBoundary_of_nonexceptional_positions C hj D a b
      ha hb hsum

/-- **General concrete no-chord/equal-neighbour boundary theorem.**

This is the unconditional application of Gyárfás's Lemma 7 to the raw
configuration above (for the structural theorem's relevant range `j > 0`).
Select `2*j` common positions and one base.  The `2*j-1` oriented arcs from
that base split by parity; one class has at least `j` members.  Restrict it
to `j` targets.  Their complementary arcs have the opposite parity and
distinct lengths, so the two families populate every field of
`SameNeighborhoodCertificate`.  All cycles in that certificate are the
walks constructed by `commonNeighborArcCycles` and
`commonNeighborCoarcCycles`. -/
theorem sameNeighborhoodNoChordBoundary [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 0 < j)
    (D : SameNeighborhoodNoChordConfiguration C j) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  obtain ⟨X, hXsub, hXcard⟩ :=
    Finset.exists_subset_card_eq D.many_neighbors
  have hXnonempty : X.Nonempty := Finset.card_pos.mp (by omega)
  let base : Fin C.cycle.length := X.min' hXnonempty
  have hbaseX : base ∈ X := Finset.min'_mem X hXnonempty
  let T : Finset (Fin C.cycle.length) := X.erase base
  have hTcard : T.card = 2 * j - 1 := by
    change (X.erase base).card = 2 * j - 1
    rw [Finset.card_erase_of_mem hbaseX, hXcard]
  let oddT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Odd (cycleArc C base t).length
  let evenT : Finset (Fin C.cycle.length) :=
    T.filter fun t ↦ Even (cycleArc C base t).length
  have hpartition : evenT.card + oddT.card = T.card := by
    simpa [evenT, oddT, Nat.not_even_iff_odd] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (fun t ↦ Even (cycleArc C base t).length))
  have hmajority : j ≤ oddT.card ∨ j ≤ evenT.card := by
    omega
  have hbaseL : base ∈ cycleNeighborPositions C D.exterior.left :=
    hXsub hbaseX
  have hbaseR : base ∈ cycleNeighborPositions C D.exterior.right := by
    rw [← D.same_neighbors]
    exact hbaseL
  rcases hmajority with hoddMajority | hevenMajority
  · obtain ⟨M, hMsub, hMcard⟩ :=
      Finset.exists_subset_card_eq hoddMajority
    have hML : M ⊆ cycleNeighborPositions C D.exterior.left := by
      intro t ht
      have htOdd : t ∈ oddT := hMsub ht
      have htT : t ∈ T := (Finset.mem_filter.mp htOdd).1
      exact hXsub (Finset.mem_erase.mp htT).2
    have hbaseNot : base ∉ M := by
      intro hb
      have htT : base ∈ T :=
        (Finset.mem_filter.mp (hMsub hb)).1
      change base ∈ X.erase base at htT
      exact (Finset.mem_erase.mp htT).1 rfl
    have hodd : ∀ t ∈ M, Odd (cycleArc C base t).length := by
      intro t ht
      exact (Finset.mem_filter.mp (hMsub ht)).2
    have hMR : M ⊆ cycleNeighborPositions C D.exterior.right := by
      rw [← D.same_neighbors]
      exact hML
    exact sameNeighborhoodBoundary
      (sameNeighborhoodCertificate_of_odd_forward_family C j D.exterior base M
        hMcard hbaseL hbaseR hML hMR hbaseNot hodd hj)
  · obtain ⟨M, hMsub, hMcard⟩ :=
      Finset.exists_subset_card_eq hevenMajority
    have hML : M ⊆ cycleNeighborPositions C D.exterior.left := by
      intro t ht
      have htEven : t ∈ evenT := hMsub ht
      have htT : t ∈ T := (Finset.mem_filter.mp htEven).1
      exact hXsub (Finset.mem_erase.mp htT).2
    have hbaseNot : base ∉ M := by
      intro hb
      have htT : base ∈ T :=
        (Finset.mem_filter.mp (hMsub hb)).1
      change base ∈ X.erase base at htT
      exact (Finset.mem_erase.mp htT).1 rfl
    have heven : ∀ t ∈ M, Even (cycleArc C base t).length := by
      intro t ht
      exact (Finset.mem_filter.mp (hMsub ht)).2
    have hMR : M ⊆ cycleNeighborPositions C D.exterior.right := by
      rw [← D.same_neighbors]
      exact hML
    exact sameNeighborhoodBoundary
      (sameNeighborhoodCertificate_of_even_forward_family C j D.exterior base M
        hMcard hbaseL hbaseR hML hMR hbaseNot heven hj)

/-- The containment subcase of the different-neighbour boundary.  If every
left attachment is also a right attachment, select `2 * j` of them and use
the common-neighbour subset theorem.  The remaining strict non-containment
case is the genuinely mixed part of Lemma 8. -/
theorem differentNeighborhoodNoChordBoundary_of_left_subset [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 0 < j)
    (D : DifferentNeighborhoodNoChordConfiguration C j)
    (hsub : cycleNeighborPositions C D.exterior.left ⊆
      cycleNeighborPositions C D.exterior.right) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  obtain ⟨X, hXL, hXcard⟩ :=
    Finset.exists_subset_card_eq D.many_left_neighbors
  exact commonNeighborSubsetBoundary C hj D.exterior X hXcard hXL
    (hXL.trans hsub)

/-- **General concrete no-left-chord/different-neighbour boundary theorem.**

This is the corrected form of Gyárfás's Lemma 8.  The endpoint orientation
`card N_C(left) ≤ card N_C(right)` is essential.  Under a contrary
`ncard ≤ j` bound, the forward and complementary mixed-endpoint cycle
families each have exactly `j` lengths and hence each exhaust all odd cycle
lengths.  A second right attachment then gives a right-fan length belonging
to the forward family.  The reflected equality supplied by the complementary
family closes an actual wrapping arc through the exterior path to an odd
cycle of length `C.length + 2`, contradicting maximality of `C`. -/
theorem differentNeighborhoodNoChordBoundary [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 0 < j)
    (D : DifferentNeighborhoodNoChordConfiguration C j) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  by_contra hgoal
  have hcount : (oddCycleLengths G).ncard ≤ j := by omega
  let R := cycleNeighborPositions C D.exterior.right
  obtain ⟨X, hXL, hXcard⟩ :=
    Finset.exists_subset_card_eq D.many_left_neighbors
  obtain ⟨y, hyDiff⟩ := D.extra_right_neighbor
  have ⟨hyR, hyL⟩ := Finset.mem_sdiff.mp hyDiff
  have hyNotX : y ∉ X := fun hyX ↦ hyL (hXL hyX)
  let I : Finset (Fin C.cycle.length) := X.filter fun t ↦
    Odd ((cycleArc C y t).length + D.exterior.walk.length + 2)
  let J : Finset (Fin C.cycle.length) := X.filter fun t ↦
    ¬Odd ((cycleArc C y t).length + D.exterior.walk.length + 2)
  have hIJcard : I.card + J.card = 2 * j := by
    change (X.filter fun t ↦ Odd
      ((cycleArc C y t).length + D.exterior.walk.length + 2)).card +
      (X.filter fun t ↦ ¬Odd
      ((cycleArc C y t).length + D.exterior.walk.length + 2)).card = 2 * j
    exact (Finset.card_filter_add_card_filter_not
      (s := X) (fun t ↦ Odd
        ((cycleArc C y t).length + D.exterior.walk.length + 2))).trans hXcard
  have hcomplement (t : Fin C.cycle.length) :
      Odd ((cycleArc C y t).length + D.exterior.walk.length + 2) ↔
        ¬Odd ((cycleCoarc C y t).length + D.exterior.walk.length + 2) := by
    have hsumOdd : Odd
        (((cycleArc C y t).length + D.exterior.walk.length + 2) +
          ((cycleCoarc C y t).length + D.exterior.walk.length + 2)) := by
      rcases C.odd_length with ⟨q, hq⟩
      refine ⟨q + D.exterior.walk.length + 2, ?_⟩
      have hsum := cycleArc_add_cycleCoarc_length C y t
      omega
    simpa only [Nat.not_odd_iff_even] using (Nat.odd_add.mp hsumOdd)
  let LI : Finset ℕ := I.image fun t ↦
    (cycleArc C y t).length + D.exterior.walk.length + 2
  let LJ : Finset ℕ := J.image fun t ↦
    (cycleCoarc C y t).length + D.exterior.walk.length + 2
  have hLIcard : LI.card = I.card := by
    change (I.image fun t ↦
      (cycleArc C y t).length + D.exterior.walk.length + 2).card = I.card
    rw [Finset.card_image_iff.mpr]
    intro a _ b _ hab
    apply cycleArc_length_injective C y
    exact Nat.add_right_cancel (Nat.add_right_cancel hab)
  have hLJcard : LJ.card = J.card := by
    change (J.image fun t ↦
      (cycleCoarc C y t).length + D.exterior.walk.length + 2).card = J.card
    rw [Finset.card_image_iff.mpr]
    intro a _ b _ hab
    apply cycleCoarc_length_injective C y
    exact Nat.add_right_cancel (Nat.add_right_cancel hab)
  have hLIodd : ∀ n ∈ LI, Odd n := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp ht).2
  have hLJodd : ∀ n ∈ LJ, Odd n := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    by_contra hco
    exact (Finset.mem_filter.mp ht).2 ((hcomplement t).mpr hco)
  have hLIcycle : ∀ n ∈ LI, CycleAtLength G n := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    have htX := (Finset.mem_filter.mp ht).1
    exact mixedEndpointArcCycle C D.exterior y t
      (fun hyt ↦ hyNotX (hyt ▸ htX)) hyR (hXL htX)
  have hLJcycle : ∀ n ∈ LJ, CycleAtLength G n := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    have htX := (Finset.mem_filter.mp ht).1
    exact mixedEndpointCoarcCycle C D.exterior y t
      (fun hyt ↦ hyNotX (hyt ▸ htX)) hyR (hXL htX)
  have hIle : I.card ≤ j := by
    rw [← hLIcard]
    exact (ncard_oddCycleLengths_ge_of_finset LI hLIodd hLIcycle).trans hcount
  have hJle : J.card ≤ j := by
    rw [← hLJcard]
    exact (ncard_oddCycleLengths_ge_of_finset LJ hLJodd hLJcycle).trans hcount
  have hIcard : I.card = j := by omega
  have hJcard : J.card = j := by omega
  have hLIcard' : LI.card = j := hLIcard.trans hIcard
  have hLJcard' : LJ.card = j := hLJcard.trans hJcard
  have hLIsub : (LI : Set ℕ) ⊆ oddCycleLengths G := by
    intro n hn
    exact (hLIcycle n hn).mem_oddCycleLengths (hLIodd n hn)
  have hLJsub : (LJ : Set ℕ) ⊆ oddCycleLengths G := by
    intro n hn
    exact (hLJcycle n hn).mem_oddCycleLengths (hLJodd n hn)
  have hLIeq : (LI : Set ℕ) = oddCycleLengths G := by
    exact Set.eq_of_subset_of_ncard_le hLIsub
      (by simpa [hLIcard'] using hcount) (oddCycleLengths_finite G)
  have hLJeq : (LJ : Set ℕ) = oddCycleLengths G := by
    exact Set.eq_of_subset_of_ncard_le hLJsub
      (by simpa [hLJcard'] using hcount) (oddCycleLengths_finite G)
  have hreflect {i : Fin C.cycle.length} (hiI : i ∈ I) :
      ∃ t ∈ J,
        (cycleArc C y t).length = (cycleCoarc C y i).length := by
    have hiOdd : Odd
        ((cycleArc C y i).length + D.exterior.walk.length + 2) :=
      (Finset.mem_filter.mp hiI).2
    have hiX := (Finset.mem_filter.mp hiI).1
    have hiCycle : CycleAtLength G
        ((cycleArc C y i).length + D.exterior.walk.length + 2) :=
      mixedEndpointArcCycle C D.exterior y i
        (fun hyi ↦ hyNotX (hyi ▸ hiX)) hyR (hXL hiX)
    have hmemOdd := hiCycle.mem_oddCycleLengths hiOdd
    rw [← hLJeq] at hmemOdd
    obtain ⟨t, htJ, heq⟩ := Finset.mem_image.mp hmemOdd
    refine ⟨t, htJ, ?_⟩
    have hlen : (cycleCoarc C y t).length = (cycleArc C y i).length :=
      Nat.add_right_cancel (Nat.add_right_cancel heq)
    have htSum := cycleArc_add_cycleCoarc_length C y t
    have hiSum := cycleArc_add_cycleCoarc_length C y i
    omega
  have hRcard : 2 ≤ R.card := by
    change 2 ≤ (cycleNeighborPositions C D.exterior.right).card
    calc
      2 ≤ 2 * j := by omega
      _ ≤ (cycleNeighborPositions C D.exterior.left).card :=
        D.many_left_neighbors
      _ ≤ (cycleNeighborPositions C D.exterior.right).card :=
        D.left_card_le_right_card
  have hRset : 1 < (R : Set (Fin C.cycle.length)).ncard := by
    rw [Set.ncard_coe_finset]
    omega
  obtain ⟨z, hzR, hzy⟩ :=
    (R : Set (Fin C.cycle.length)).exists_ne_of_one_lt_ncard hRset y
  by_cases hArcOdd : Odd ((cycleArc C y z).length + 2)
  · have hfanCycle := rightEndpointArcCycle C D.exterior y z hzy.symm hyR hzR
    have hfanMem := hfanCycle.mem_oddCycleLengths hArcOdd
    rw [← hLIeq] at hfanMem
    obtain ⟨i, hiI, heq⟩ := Finset.mem_image.mp hfanMem
    have hiX := (Finset.mem_filter.mp hiI).1
    apply mixedWrapContradiction_of_arc_eq C D.exterior y z i hzR (hXL hiX)
    omega
  · have hCoOdd : Odd ((cycleCoarc C y z).length + 2) := by
      have hEven : Even (cycleArc C y z).length := by
        apply Nat.not_odd_iff_even.mp
        intro hOdd
        rcases hOdd with ⟨q, hq⟩
        exact hArcOdd ⟨q + 1, by omega⟩
      have hCo := (even_cycleArc_iff_odd_cycleCoarc C y z).mp hEven
      rcases hCo with ⟨q, hq⟩
      exact ⟨q + 1, by omega⟩
    have hfanCycle := rightEndpointCoarcCycle C D.exterior y z hzy.symm hyR hzR
    have hfanMem := hfanCycle.mem_oddCycleLengths hCoOdd
    rw [← hLIeq] at hfanMem
    obtain ⟨i, hiI, heq⟩ := Finset.mem_image.mp hfanMem
    have hiX := (Finset.mem_filter.mp hiI).1
    obtain ⟨t, htJ, href⟩ := hreflect hiI
    have htX := (Finset.mem_filter.mp htJ).1
    apply mixedWrapContradiction_of_coarc_eq C D.exterior y z i t
      hzR (hXL htX)
    · omega
    · exact href

/-- **Concrete equal-neighbour boundary case for `j = 1`.**

Starting only from the actual longest odd cycle, the actual exterior path,
and equality/cardinality of the endpoint neighbour finsets defined above,
construct two different odd cycle lengths. -/
theorem sameNeighborhoodBoundary_one_of_exteriorPath [Finite V]
    (C : EndpointCount.LongestOddCycle G)
    (D : SameNeighborhoodTwoConfiguration C) :
    2 ≤ (oddCycleLengths G).ncard := by
  classical
  obtain ⟨i, j, hij, hN⟩ := Finset.card_eq_two.mp D.two_neighbors
  let x : V := C.cycle.getVert i
  let y : V := C.cycle.getVert j
  have hxy : x ≠ y := by
    exact getVert_ne_of_fin_ne C hij

  have hiL : i ∈ cycleNeighborPositions C D.exterior.left := by
    rw [hN]
    simp
  have hjL : j ∈ cycleNeighborPositions C D.exterior.left := by
    rw [hN]
    simp
  have hiR : i ∈ cycleNeighborPositions C D.exterior.right := by
    rw [← D.same_neighbors]
    exact hiL
  have hjR : j ∈ cycleNeighborPositions C D.exterior.right := by
    rw [← D.same_neighbors]
    exact hjL
  have hLx : G.Adj D.exterior.left x :=
    (mem_cycleNeighborPositions C D.exterior.left i).mp hiL
  have hLy : G.Adj D.exterior.left y :=
    (mem_cycleNeighborPositions C D.exterior.left j).mp hjL
  have hRx : G.Adj D.exterior.right x :=
    (mem_cycleNeighborPositions C D.exterior.right i).mp hiR
  have hRy : G.Adj D.exterior.right y :=
    (mem_cycleNeighborPositions C D.exterior.right j).mp hjR

  have hxC : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  have hyC : y ∈ C.cycle.support := C.cycle.getVert_mem_support j
  let c : G.Walk x x := C.cycle.rotate x hxC
  have hc : c.IsCycle := C.isCycle.rotate hxC
  have hyc : y ∈ c.support := by
    exact (C.cycle.mem_support_rotate_iff x hxC).mpr hyC
  let P : G.Walk x y := c.takeUntil y hyc
  let Q : G.Walk y x := c.dropUntil y hyc
  have hP : P.IsPath := hc.isPath_takeUntil hyc
  have hPnonempty : ¬ P.Nil := by
    intro hnil
    have : x = y := (c.nil_takeUntil hyc).mp hnil
    exact hxy this
  have hQ : Q.IsPath := by
    exact Walk.IsCycle.isPath_of_append_right hPnonempty (by
      simpa only [P, Q, c.take_spec hyc] using hc)
  have hPQlen : P.length + Q.length = C.cycle.length := by
    calc
      P.length + Q.length = (P.append Q).length :=
        (Walk.length_append P Q).symm
      _ = c.length := congrArg Walk.length (c.take_spec hyc)
      _ = C.cycle.length := by simp [c]

  have hxOutside : x ∉ D.exterior.walk.support := by
    intro hx
    exact D.exterior.avoids_cycle hx hxC
  have hyOutside : y ∉ D.exterior.walk.support := by
    intro hy
    exact D.exterior.avoids_cycle hy hyC
  have hleftOutsideCycle : D.exterior.left ∉ C.cycle.support :=
    D.exterior.avoids_cycle D.exterior.walk.start_mem_support
  have hrightOutsideCycle : D.exterior.right ∉ C.cycle.support :=
    D.exterior.avoids_cycle D.exterior.walk.end_mem_support
  have hLx_ne : D.exterior.left ≠ x := fun h ↦
    hleftOutsideCycle (h.symm ▸ hxC)
  have hLy_ne : D.exterior.left ≠ y := fun h ↦
    hleftOutsideCycle (h.symm ▸ hyC)
  have hRx_ne : D.exterior.right ≠ x := fun h ↦
    hrightOutsideCycle (h.symm ▸ hxC)
  have hRy_ne : D.exterior.right ≠ y := fun h ↦
    hrightOutsideCycle (h.symm ▸ hyC)
  have hLR : D.exterior.left ≠ D.exterior.right := by
    intro h
    have hnil : D.exterior.walk.Nil := D.exterior.isPath.nil_iff_eq.mpr h
    exact (Nat.ne_of_gt D.exterior.positive) hnil.length_eq_zero

  let shortXY : G.Walk x y := Walk.cons hLx.symm hLy.toWalk
  let shortYX : G.Walk y x := Walk.cons hLy.symm hLx.toWalk
  let longXY : G.Walk x y :=
    Walk.cons hLx.symm (D.exterior.walk.concat hRy)
  let longYX : G.Walk y x :=
    Walk.cons hRy.symm (D.exterior.walk.reverse.concat hLx)
  let baseX : G.Walk x x :=
    Walk.cons hLx.symm (D.exterior.walk.concat hRx)

  have hshortXY : shortXY.IsPath := by
    dsimp [shortXY]
    rw [Walk.cons_isPath_iff]
    exact ⟨hLy.isPath_toWalk, by
      simp only [hLy.support_toWalk, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      exact ⟨hLx_ne.symm, hxy⟩⟩
  have hshortYX : shortYX.IsPath := by
    dsimp [shortYX]
    rw [Walk.cons_isPath_iff]
    exact ⟨hLx.isPath_toWalk, by
      simp only [hLx.support_toWalk, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      exact ⟨hLy_ne.symm, hxy.symm⟩⟩
  have hlongXY : longXY.IsPath := by
    dsimp [longXY]
    rw [Walk.cons_isPath_iff]
    constructor
    · exact D.exterior.isPath.concat hyOutside hRy
    · simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
      exact fun h ↦ h.elim hxOutside hxy
  have hlongYX : longYX.IsPath := by
    dsimp [longYX]
    rw [Walk.cons_isPath_iff]
    constructor
    · exact D.exterior.isPath.reverse.concat
        (by simpa [Walk.support_reverse] using hxOutside) hLx
    · simp only [Walk.support_concat, List.mem_append, List.mem_singleton,
        Walk.support_reverse, List.mem_reverse]
      exact fun h ↦ h.elim hyOutside hxy.symm
  have hbaseX : baseX.IsCycle := by
    dsimp [baseX]
    rw [Walk.cons_isCycle_iff]
    constructor
    · exact D.exterior.isPath.concat hxOutside hRx
    · intro he
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
      simp only [List.mem_singleton] at he
      rcases he with he | he
      · exact hxOutside (D.exterior.walk.fst_mem_support_of_mem_edges he)
      · rw [Sym2.eq_iff] at he
        rcases he with ⟨hxr, hLx'⟩ | ⟨-, hLR'⟩
        · exact hRx_ne hxr.symm
        · exact hLR hLR'

  have hshortXY_inter :
      ∀ z ∈ shortXY.support, z ∈ C.cycle.support → z = x ∨ z = y := by
    intro z hz hzC
    simp only [shortXY, Walk.support_cons, hLy.support_toWalk,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim
        (D.exterior.avoids_cycle D.exterior.walk.start_mem_support hzC)
    · exact Or.inr rfl
  have hshortYX_inter :
      ∀ z ∈ shortYX.support, z ∈ C.cycle.support → z = y ∨ z = x := by
    intro z hz hzC
    simp only [shortYX, Walk.support_cons, hLx.support_toWalk,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim
        (D.exterior.avoids_cycle D.exterior.walk.start_mem_support hzC)
    · exact Or.inr rfl
  have hlongXY_inter :
      ∀ z ∈ longXY.support, z ∈ C.cycle.support → z = x ∨ z = y := by
    intro z hz hzC
    simp only [longXY, Walk.support_cons, Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact Or.inl rfl
    · exact False.elim (D.exterior.avoids_cycle hz hzC)
    · exact Or.inr rfl
  have hlongYX_inter :
      ∀ z ∈ longYX.support, z ∈ C.cycle.support → z = y ∨ z = x := by
    intro z hz hzC
    simp only [longYX, Walk.support_cons, Walk.support_concat,
      Walk.support_reverse, List.mem_cons, List.mem_append,
      List.mem_reverse, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact Or.inl rfl
    · exact False.elim (D.exterior.avoids_cycle hz hzC)
    · exact Or.inr rfl

  have hPsub : ∀ z ∈ P.support, z ∈ C.cycle.support := by
    intro z hz
    apply mem_cycle_of_mem_rotated C hxC
    exact c.support_takeUntil_subset_support hyc hz
  have hQsub : ∀ z ∈ Q.support, z ∈ C.cycle.support := by
    intro z hz
    apply mem_cycle_of_mem_rotated C hxC
    exact c.support_dropUntil_subset_support hyc hz

  have hP_shortYX : P.support.tail.Disjoint shortYX.support.tail := by
    intro z hzP hzS
    have hzPin : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzSin : z ∈ shortYX.support := List.mem_of_mem_tail hzS
    rcases hshortYX_inter z hzSin (hPsub z hzPin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath hshortYX hzS
    · exact start_not_mem_tail_of_isPath hP hzP
  have hP_longYX : P.support.tail.Disjoint longYX.support.tail := by
    intro z hzP hzS
    have hzPin : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzSin : z ∈ longYX.support := List.mem_of_mem_tail hzS
    rcases hlongYX_inter z hzSin (hPsub z hzPin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath hlongYX hzS
    · exact start_not_mem_tail_of_isPath hP hzP
  have hQ_shortXY : Q.support.tail.Disjoint shortXY.support.tail := by
    intro z hzQ hzS
    have hzQin : z ∈ Q.support := List.mem_of_mem_tail hzQ
    have hzSin : z ∈ shortXY.support := List.mem_of_mem_tail hzS
    rcases hshortXY_inter z hzSin (hQsub z hzQin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath hshortXY hzS
    · exact start_not_mem_tail_of_isPath hQ hzQ
  have hQ_longXY : Q.support.tail.Disjoint longXY.support.tail := by
    intro z hzQ hzS
    have hzQin : z ∈ Q.support := List.mem_of_mem_tail hzQ
    have hzSin : z ∈ longXY.support := List.mem_of_mem_tail hzS
    rcases hlongXY_inter z hzSin (hQsub z hzQin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath hlongXY hzS
    · exact start_not_mem_tail_of_isPath hQ hzQ

  have hshortP : CycleAtLength G (P.length + 2) := by
    convert cycleAtLength_of_append P shortYX hP hshortYX hP_shortYX
      (Or.inr (by simp [shortYX])) using 1 <;> simp [shortYX]
  have hlongP : CycleAtLength G (P.length + D.exterior.walk.length + 2) := by
    convert cycleAtLength_of_append P longYX hP hlongYX hP_longYX
      (Or.inr (by simp [longYX])) using 1 <;>
      simp [longYX] <;> omega
  have hshortQ : CycleAtLength G (Q.length + 2) := by
    convert cycleAtLength_of_append Q shortXY hQ hshortXY hQ_shortXY
      (Or.inr (by simp [shortXY])) using 1 <;> simp [shortXY]
  have hlongQ : CycleAtLength G (Q.length + D.exterior.walk.length + 2) := by
    convert cycleAtLength_of_append Q longXY hQ hlongXY hQ_longXY
      (Or.inr (by simp [longXY])) using 1 <;>
      simp [longXY] <;> omega
  have hbase : CycleAtLength G (D.exterior.walk.length + 2) := by
    exact ⟨x, baseX, hbaseX, by simp [baseX]⟩

  have hparity : Odd P.length ∨ Odd Q.length := by
    have hsum : Odd (P.length + Q.length) := by
      rw [hPQlen]
      exact C.odd_length
    by_cases hp : Odd P.length
    · exact Or.inl hp
    · exact Or.inr <| Nat.not_even_iff_odd.mp fun hQeven ↦
        hp ((Nat.odd_add.mp hsum).mpr hQeven)
  have hPpos : 0 < P.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hxy
    exact hP.nil_iff_eq.mp (Walk.length_eq_zero_iff.mp hzero)
  have hQpos : 0 < Q.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hxy.symm
    exact hQ.nil_iff_eq.mp (Walk.length_eq_zero_iff.mp hzero)
  rcases hparity with hPodd | hQodd
  · have hQeven : Even Q.length :=
      (Nat.odd_add.mp (by simpa [hPQlen] using C.odd_length)).mp hPodd
    let Cert : SameNeighborhoodCertificate G 1 D.exterior.walk.length := {
      path_pos := D.exterior.positive
      oddPrefixes := {P.length}
      oddPrefixMax := P.length
      evenPrefixes := {Q.length}
      odd_card := by simp
      even_card := by simp
      odd_values := by simpa using hPodd
      even_values := by
        intro b hb
        simp only [Finset.mem_singleton] at hb
        subst b
        exact hQeven
      oddPrefixMax_mem := by simp
      oddPrefix_le_max := by simp
      even_pos := by
        intro b hb
        simp only [Finset.mem_singleton] at hb
        subst b
        exact hQpos
      short_cycles := by
        intro b hb
        rcases Finset.mem_singleton.mp hb with rfl
        exact hshortP
      even_path_long_cycle := by simpa [Nat.add_assoc] using hlongP
      odd_path_base_cycle := hbase
      odd_path_long_cycles := by
        intro b hb
        rcases Finset.mem_singleton.mp hb with rfl
        simpa [Nat.add_assoc] using hlongQ
    }
    exact sameNeighborhoodBoundary Cert
  · have hPeven : Even P.length :=
      (Nat.odd_add'.mp (by simpa [hPQlen] using C.odd_length)).mp hQodd
    let Cert : SameNeighborhoodCertificate G 1 D.exterior.walk.length := {
      path_pos := D.exterior.positive
      oddPrefixes := {Q.length}
      oddPrefixMax := Q.length
      evenPrefixes := {P.length}
      odd_card := by simp
      even_card := by simp
      odd_values := by simpa using hQodd
      even_values := by
        intro b hb
        simp only [Finset.mem_singleton] at hb
        subst b
        exact hPeven
      oddPrefixMax_mem := by simp
      oddPrefix_le_max := by simp
      even_pos := by
        intro b hb
        simp only [Finset.mem_singleton] at hb
        subst b
        exact hPpos
      short_cycles := by
        intro b hb
        rcases Finset.mem_singleton.mp hb with rfl
        exact hshortQ
      even_path_long_cycle := by simpa [Nat.add_assoc] using hlongQ
      odd_path_base_cycle := hbase
      odd_path_long_cycles := by
        intro b hb
        rcases Finset.mem_singleton.mp hb with rfl
        simpa [Nat.add_assoc] using hlongP
    }
    exact sameNeighborhoodBoundary Cert

end

end Erdos58.Structural
