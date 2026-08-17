/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos58.Structural.BoundaryApplication
import Mathlib.Tactic

/-!
# Concrete cycle constructors for the different-neighborhood boundary case

This helper is deliberately separate from `BoundaryApplication.lean` so the
selection/counting proof of Gyárfás's Lemma 8 can be developed without edit
conflicts.  Every conclusion below is an actual `CycleAtLength` witness made
from a simple cycle arc and explicit endpoint edges; no cycle-family
certificate is assumed.
-/

namespace Erdos58.Structural

open SimpleGraph

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- If a `j`-element finset of genuine odd cycle lengths sits inside the
whole length set and that whole set has cardinality at most `j`, then the
family already exhausts all odd cycle lengths.  This is the finite step used
twice in the corrected different-neighborhood argument. -/
theorem oddCycleLength_mem_of_full_family [Finite V]
    {j n : ℕ} (L : Finset ℕ) (hcard : L.card = j)
    (hsub : ∀ m ∈ L, m ∈ oddCycleLengths G)
    (hbound : (oddCycleLengths G).ncard ≤ j)
    (hn : n ∈ oddCycleLengths G) : n ∈ L := by
  by_contra hnL
  let K : Finset ℕ := insert n L
  have hinsert : (K : Set ℕ) ⊆ oddCycleLengths G := by
    intro m hm
    simp only [K, Finset.mem_coe, Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · exact hn
    · exact hsub m hm
  have hle := Set.ncard_le_ncard hinsert (oddCycleLengths_finite G)
  rw [Set.ncard_coe_finset] at hle
  have hKcard : K.card = j + 1 := by simp [K, hnL, hcard]
  omega

private theorem append_left_cancel'
    {u v w : V} (p : G.Walk u v) {q r : G.Walk v w}
    (h : p.append q = p.append r) : q = r := by
  induction p with
  | nil => simpa using h
  | cons hadj p ih =>
      apply ih
      exact eq_of_heq ((by
        simpa only [Walk.cons_append, Walk.cons.injEq] using h :
          True ∧ p.append q ≍ p.append r)).2

/-- Suppose that, after rotating the cycle to start at `y`, the occurrence
of `i` precedes the occurrence of `z`.  The complementary wrapping segment
from `z` back to `i` is a simple path supported on the cycle, and its
length is the expected suffix-plus-prefix length.

This is the geometric ingredient needed at the end of the corrected
different-neighborhood argument: an equality `b = a + s` makes this path
have length `C.cycle.length - s`. -/
theorem exists_cycleSupported_wrapPath
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
    have hgetpz : pz.getVert pi.length = c.getVert pi.length := by
      exact c.getVert_takeUntil hz hlt'.le
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
  have hpzsuffix : pz.append suffix = c := by
    exact c.take_spec hz
  have hpicsuffix : pi.append (q.append suffix) = c := by
    rw [Walk.append_assoc, hpiq, hpzsuffix]
  have hpicdrop : pi.append (c.dropUntil vi hi) = c := c.take_spec hi
  have hq_suffix : q.append suffix = c.dropUntil vi hi := by
    apply append_left_cancel' pi
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

private theorem cycleAtLength_of_append'
    {x y : V} (p : G.Walk x y) (q : G.Walk y x)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : p.support.tail.Disjoint q.support.tail)
    (hlong : 1 < p.length ∨ 1 < q.length) :
    CycleAtLength G (p.length + q.length) := by
  exact ⟨x, p.append q, hp.isCycle_append hq hdisj hlong,
    Walk.length_append p q⟩

private lemma getVert_ne_of_fin_ne'
    (C : EndpointCount.LongestOddCycle G)
    {i j : Fin C.cycle.length} (hij : i ≠ j) :
    C.cycle.getVert i ≠ C.cycle.getVert j := by
  intro h
  apply hij
  apply Fin.ext
  exact C.isCycle.getVert_injOn'
    (by simp; omega) (by simp; omega) h

private lemma start_not_mem_tail_of_isPath'
    {x y : V} {p : G.Walk x y} (hp : p.IsPath) :
    x ∉ p.support.tail := by
  have hnodup := hp.support_nodup
  rw [← p.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

/-- Close a cycle-supported path from a right-endpoint neighbor to a
left-endpoint neighbor through the actual exterior path. -/
theorem mixedNeighborPathCycle
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
  have hxy : x ≠ y := getVert_ne_of_fin_ne' C hrt
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
    · exact start_not_mem_tail_of_isPath' hclose hzQ
    · exact start_not_mem_tail_of_isPath' hP hzP
  convert cycleAtLength_of_append' P closeYX hP hclose hdisj
    (Or.inr (by simp [closeYX])) using 1 <;>
    simp [closeYX] <;> omega

/-- The forward oriented arc from the extra right neighbor to a selected
left neighbor closes through the exterior path. -/
theorem mixedNeighborArcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (r t : Fin C.cycle.length) (hrt : r ≠ t)
    (hrR : r ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left) :
    CycleAtLength G
      ((cycleArc C r t).length + S.walk.length + 2) :=
  mixedNeighborPathCycle C S r t hrt hrR htL
    (cycleArc C r t) (cycleArc_isPath C r t)
    (cycleArc_support_subset_cycle C r t)

/-- The complementary oriented arc gives the second actual mixed-endpoint
cycle.  It is reversed so that its endpoints agree with the forward arc. -/
theorem mixedNeighborCoarcCycle
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
  simpa using mixedNeighborPathCycle C S r t hrt hrR htL
    (cycleCoarc C r t).reverse hp hsub

/-- If, from a fixed cyclic base `y`, a left-neighbor position `i`
precedes a right-neighbor position `z` by exactly the length of the
exterior path, the wrapping arc from `z` to `i` closes through the exterior
path to give a cycle two edges longer than `C`. -/
theorem mixedNeighborLongCycle_of_left_before_right
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (y i z : Fin C.cycle.length)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hzR : z ∈ cycleNeighborPositions C S.right)
    (hgap : (cycleArc C y z).length =
      (cycleArc C y i).length + S.walk.length) :
    CycleAtLength G (C.cycle.length + 2) := by
  have hlt : (cycleArc C y i).length < (cycleArc C y z).length := by
    rw [hgap]
    have := S.positive
    omega
  have hzi : z ≠ i := by
    intro h
    subst z
    omega
  obtain ⟨P, hPpath, hPsub, hPlength⟩ :=
    exists_cycleSupported_wrapPath C y i z hlt
  have harcbound := cycleArc_add_cycleCoarc_length C y z
  have hlength : P.length + S.walk.length + 2 = C.cycle.length + 2 := by
    omega
  rw [← hlength]
  exact mixedNeighborPathCycle C S z i hzi hzR hiL P hPpath hPsub

/-- Reflected form of `mixedNeighborLongCycle_of_left_before_right`: if
the right-neighbor position precedes the left-neighbor position by the
exterior-path length, reverse the wrapping arc before closing it. -/
theorem mixedNeighborLongCycle_of_right_before_left
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (y z i : Fin C.cycle.length)
    (hzR : z ∈ cycleNeighborPositions C S.right)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hgap : (cycleArc C y i).length =
      (cycleArc C y z).length + S.walk.length) :
    CycleAtLength G (C.cycle.length + 2) := by
  have hlt : (cycleArc C y z).length < (cycleArc C y i).length := by
    rw [hgap]
    have := S.positive
    omega
  have hzi : z ≠ i := by
    intro h
    subst i
    omega
  obtain ⟨P, hPpath, hPsub, hPlength⟩ :=
    exists_cycleSupported_wrapPath C y z i hlt
  have hPrevPath : P.reverse.IsPath := hPpath.reverse
  have hPrevSub : ∀ x ∈ P.reverse.support, x ∈ C.cycle.support := by
    intro x hx
    apply hPsub x
    simpa [Walk.support_reverse] using hx
  have harcbound := cycleArc_add_cycleCoarc_length C y i
  have hlength : P.reverse.length + S.walk.length + 2 =
      C.cycle.length + 2 := by
    simp only [Walk.length_reverse]
    omega
  rw [← hlength]
  exact mixedNeighborPathCycle C S z i hzi hzR hiL
    P.reverse hPrevPath hPrevSub

/-- Close a cycle-supported path between two distinct left-endpoint
neighbors through their common exterior endpoint. -/
theorem leftNeighborPathCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (htL : t ∈ cycleNeighborPositions C S.left)
    (P : G.Walk (C.cycle.getVert i) (C.cycle.getVert t))
    (hP : P.IsPath)
    (hPsub : ∀ z ∈ P.support, z ∈ C.cycle.support) :
    CycleAtLength G (P.length + 2) := by
  classical
  let x := C.cycle.getVert i
  let y := C.cycle.getVert t
  have hxy : x ≠ y := getVert_ne_of_fin_ne' C hit
  have hLx : G.Adj S.left x :=
    (mem_cycleNeighborPositions C S.left i).mp hiL
  have hLy : G.Adj S.left y :=
    (mem_cycleNeighborPositions C S.left t).mp htL
  have hleftOutsideCycle : S.left ∉ C.cycle.support :=
    S.avoids_cycle S.walk.start_mem_support
  have hLy_ne : S.left ≠ y := fun h ↦
    hleftOutsideCycle (h.symm ▸ C.cycle.getVert_mem_support t)
  let closeYX : G.Walk y x := Walk.cons hLy.symm hLx.toWalk
  have hclose : closeYX.IsPath := by
    dsimp [closeYX]
    rw [Walk.cons_isPath_iff]
    exact ⟨hLx.isPath_toWalk, by
      simp only [hLx.support_toWalk, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      exact ⟨hLy_ne.symm, hxy.symm⟩⟩
  have hclose_inter :
      ∀ z ∈ closeYX.support, z ∈ C.cycle.support → z = y ∨ z = x := by
    intro z hz hzC
    simp only [closeYX, Walk.support_cons, hLx.support_toWalk,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim
        (S.avoids_cycle S.walk.start_mem_support hzC)
    · exact Or.inr rfl
  have hdisj : P.support.tail.Disjoint closeYX.support.tail := by
    intro z hzP hzQ
    have hzPin : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzQin : z ∈ closeYX.support := List.mem_of_mem_tail hzQ
    rcases hclose_inter z hzQin (hPsub z hzPin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath' hclose hzQ
    · exact start_not_mem_tail_of_isPath' hP hzP
  convert cycleAtLength_of_append' P closeYX hP hclose hdisj
    (Or.inr (by simp [closeYX])) using 1 <;> simp [closeYX]

/-- The forward arc between two distinct left neighbors gives an ordinary
two-spoke fan cycle. -/
theorem leftNeighborArcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (htL : t ∈ cycleNeighborPositions C S.left) :
    CycleAtLength G ((cycleArc C i t).length + 2) :=
  leftNeighborPathCycle C S i t hit hiL htL
    (cycleArc C i t) (cycleArc_isPath C i t)
    (cycleArc_support_subset_cycle C i t)

/-- The complementary arc between two distinct left neighbors gives the
other ordinary two-spoke fan cycle. -/
theorem leftNeighborCoarcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (htL : t ∈ cycleNeighborPositions C S.left) :
    CycleAtLength G ((cycleCoarc C i t).length + 2) := by
  classical
  have hp : (cycleCoarc C i t).reverse.IsPath :=
    (cycleCoarc_isPath C hit).reverse
  have hsub : ∀ z ∈ (cycleCoarc C i t).reverse.support,
      z ∈ C.cycle.support := by
    intro z hz
    apply cycleCoarc_support_subset_cycle C i t z
    simpa [Walk.support_reverse] using hz
  simpa using leftNeighborPathCycle C S i t hit hiL htL
    (cycleCoarc C i t).reverse hp hsub

/-- Close a cycle-supported path between two distinct right-endpoint
neighbors through their common exterior endpoint. -/
theorem rightNeighborPathCycle
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
  have hxy : x ≠ y := getVert_ne_of_fin_ne' C hit
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
    · exact start_not_mem_tail_of_isPath' hclose hzQ
    · exact start_not_mem_tail_of_isPath' hP hzP
  convert cycleAtLength_of_append' P closeYX hP hclose hdisj
    (Or.inr (by simp [closeYX])) using 1 <;> simp [closeYX]

/-- The forward arc between two distinct right neighbors gives an ordinary
two-spoke fan cycle. -/
theorem rightNeighborArcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (htR : t ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G ((cycleArc C i t).length + 2) :=
  rightNeighborPathCycle C S i t hit hiR htR
    (cycleArc C i t) (cycleArc_isPath C i t)
    (cycleArc_support_subset_cycle C i t)

/-- The complementary arc between two distinct right neighbors gives the
other ordinary two-spoke fan cycle. -/
theorem rightNeighborCoarcCycle
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
  simpa using rightNeighborPathCycle C S i t hit hiR htR
    (cycleCoarc C i t).reverse hp hsub

/-- Close a cycle-supported path between common endpoint neighbors through
an arbitrary simple left-to-right route supported on the exterior path. -/
theorem commonNeighborRoutePathCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (R : G.Walk S.left S.right) (hR : R.IsPath)
    (hRsub : ∀ x ∈ R.support, x ∈ S.walk.support)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left)
    (P : G.Walk (C.cycle.getVert i) (C.cycle.getVert t))
    (hP : P.IsPath)
    (hPsub : ∀ x ∈ P.support, x ∈ C.cycle.support) :
    CycleAtLength G (P.length + R.length + 2) := by
  classical
  let x := C.cycle.getVert i
  let y := C.cycle.getVert t
  have hxy : x ≠ y := getVert_ne_of_fin_ne' C hit
  have hxC : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  have hyC : y ∈ C.cycle.support := C.cycle.getVert_mem_support t
  have hRx : G.Adj S.right x :=
    (mem_cycleNeighborPositions C S.right i).mp hiR
  have hLy : G.Adj S.left y :=
    (mem_cycleNeighborPositions C S.left t).mp htL
  have hxOutside : x ∉ R.support := fun hx ↦
    S.avoids_cycle (hRsub x hx) hxC
  have hyOutside : y ∉ R.support := fun hy ↦
    S.avoids_cycle (hRsub y hy) hyC
  let closeYX : G.Walk y x := Walk.cons hLy.symm (R.concat hRx)
  have hclose : closeYX.IsPath := by
    dsimp [closeYX]
    rw [Walk.cons_isPath_iff]
    constructor
    · exact hR.concat hxOutside hRx
    · simp only [Walk.support_concat, List.mem_append,
        List.mem_singleton]
      exact fun h ↦ h.elim hyOutside hxy.symm
  have hclose_inter :
      ∀ z ∈ closeYX.support, z ∈ C.cycle.support → z = y ∨ z = x := by
    intro z hz hzC
    simp only [closeYX, Walk.support_cons, Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact Or.inl rfl
    · exact False.elim (S.avoids_cycle (hRsub z hz) hzC)
    · exact Or.inr rfl
  have hdisj : P.support.tail.Disjoint closeYX.support.tail := by
    intro z hzP hzQ
    have hzPin : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzQin : z ∈ closeYX.support := List.mem_of_mem_tail hzQ
    rcases hclose_inter z hzQin (hPsub z hzPin) with rfl | rfl
    · exact start_not_mem_tail_of_isPath' hclose hzQ
    · exact start_not_mem_tail_of_isPath' hP hzP
  convert cycleAtLength_of_append' P closeYX hP hclose hdisj
    (Or.inr (by simp [closeYX])) using 1 <;>
    simp [closeYX] <;> omega

theorem commonNeighborRouteArcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (R : G.Walk S.left S.right) (hR : R.IsPath)
    (hRsub : ∀ x ∈ R.support, x ∈ S.walk.support)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left) :
    CycleAtLength G ((cycleArc C i t).length + R.length + 2) :=
  commonNeighborRoutePathCycle C S R hR hRsub i t hit hiR htL
    (cycleArc C i t) (cycleArc_isPath C i t)
    (cycleArc_support_subset_cycle C i t)

theorem commonNeighborRouteCoarcCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (R : G.Walk S.left S.right) (hR : R.IsPath)
    (hRsub : ∀ x ∈ R.support, x ∈ S.walk.support)
    (i t : Fin C.cycle.length) (hit : i ≠ t)
    (hiR : i ∈ cycleNeighborPositions C S.right)
    (htL : t ∈ cycleNeighborPositions C S.left) :
    CycleAtLength G ((cycleCoarc C i t).length + R.length + 2) := by
  have hp : (cycleCoarc C i t).reverse.IsPath :=
    (cycleCoarc_isPath C hit).reverse
  have hsub : ∀ x ∈ (cycleCoarc C i t).reverse.support,
      x ∈ C.cycle.support := by
    intro x hx
    apply cycleCoarc_support_subset_cycle C i t x
    simpa [Walk.support_reverse] using hx
  simpa using commonNeighborRoutePathCycle C S R hR hRsub i t hit
    hiR htL (cycleCoarc C i t).reverse hp hsub

/-- A common neighbor closes any positive simple exterior route to a base
cycle. -/
theorem commonNeighborRouteBaseCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C)
    (R : G.Walk S.left S.right) (hR : R.IsPath)
    (hRsub : ∀ x ∈ R.support, x ∈ S.walk.support)
    (i : Fin C.cycle.length)
    (hiL : i ∈ cycleNeighborPositions C S.left)
    (hiR : i ∈ cycleNeighborPositions C S.right) :
    CycleAtLength G (R.length + 2) := by
  classical
  let x := C.cycle.getVert i
  have hxC : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  have hLx : G.Adj S.left x :=
    (mem_cycleNeighborPositions C S.left i).mp hiL
  have hRx : G.Adj S.right x :=
    (mem_cycleNeighborPositions C S.right i).mp hiR
  have hxOutside : x ∉ R.support := fun hx ↦
    S.avoids_cycle (hRsub x hx) hxC
  have hLR : S.left ≠ S.right := by
    intro h
    have hnil : S.walk.Nil := S.isPath.nil_iff_eq.mpr h
    exact (Nat.ne_of_gt S.positive) hnil.length_eq_zero
  have hRx_ne : S.right ≠ x := fun h ↦
    S.avoids_cycle S.walk.end_mem_support (h ▸ hxC)
  let base : G.Walk x x := Walk.cons hLx.symm (R.concat hRx)
  have hbase : base.IsCycle := by
    dsimp [base]
    rw [Walk.cons_isCycle_iff]
    constructor
    · exact hR.concat hxOutside hRx
    · intro he
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
      simp only [List.mem_singleton] at he
      rcases he with he | he
      · exact hxOutside (R.fst_mem_support_of_mem_edges he)
      · rw [Sym2.eq_iff] at he
        rcases he with ⟨hxr, -⟩ | ⟨-, hLR'⟩
        · exact hRx_ne hxr.symm
        · exact hLR hLR'
  exact ⟨x, base, hbase, by simp [base]⟩

/-- Package the even-route branch of the one-chord argument.  The extra
prefix `bMax + r₁` represents closing the maximal selected cycle path
through the shorter exterior route. -/
noncomputable def oneChordCertificate_of_even_routes
    {j r₁ r₂ bMax : ℕ} (B : Finset ℕ)
    (hj : 1 ≤ j) (hcard : B.card = j - 1) (hbMax : bMax ∈ B)
    (hmax : ∀ b ∈ B, b ≤ bMax)
    (hr₁pos : 0 < r₁) (hrlt : r₁ < r₂)
    (hr₁even : Even r₁) (hr₂even : Even r₂)
    (hBodd : ∀ b ∈ B, Odd b)
    (hshort : ∀ b ∈ B, CycleAtLength G (b + 2))
    (hlong₁ : CycleAtLength G (bMax + r₁ + 2))
    (hlong₂ : CycleAtLength G (bMax + r₂ + 2)) :
    OneChordBoundaryCertificate G j := by
  classical
  let top := bMax + r₁
  let prefixes := insert top B
  refine {
    prefixes := prefixes
    prefixMax := top
    offset₁ := 2
    offset₂ := r₂ - r₁ + 2
    card_prefixes := ?_
    prefixMax_mem := by simp [prefixes]
    prefix_le_max := ?_
    offset_lt := by omega
    first_odd := ?_
    last_odd := ?_
    first_cycles := ?_
    last_cycle := ?_ }
  · have htopNot : top ∉ B := by
      intro ht
      have := hmax top ht
      dsimp [top] at this
      omega
    simp [prefixes, htopNot, hcard]
    omega
  · intro b hb
    simp only [prefixes, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact le_rfl
    · have := hmax b hb
      dsimp [top]
      omega
  · intro b hb
    simp only [prefixes, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact (hBodd bMax hbMax).add_even hr₁even |>.add_even (by simp)
    · exact (hBodd b hb).add_even (by simp)
  · have hbOdd := hBodd bMax hbMax
    have heq : top + (r₂ - r₁ + 2) = bMax + r₂ + 2 := by
      dsimp [top]
      omega
    rw [heq]
    exact hbOdd.add_even hr₂even |>.add_even (by simp)
  · intro b hb
    simp only [prefixes, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · simpa [top, Nat.add_assoc] using hlong₁
    · simpa [Nat.add_assoc] using hshort b hb
  · have heq : top + (r₂ - r₁ + 2) = bMax + r₂ + 2 := by
      dsimp [top]
      omega
    rwa [heq]

/-- Package the odd-route branch.  Prefix zero is the common-neighbor base
cycle, while every positive selected prefix closes through the shorter
route. -/
noncomputable def oneChordCertificate_of_odd_routes
    {j r₁ r₂ bMax : ℕ} (B : Finset ℕ)
    (hj : 1 ≤ j) (hcard : B.card = j - 1) (hbMax : bMax ∈ B)
    (hmax : ∀ b ∈ B, b ≤ bMax)
    (hBpos : ∀ b ∈ B, 0 < b)
    (hrlt : r₁ < r₂) (hr₁odd : Odd r₁) (hr₂odd : Odd r₂)
    (hBeven : ∀ b ∈ B, Even b)
    (hbase₁ : CycleAtLength G (r₁ + 2))
    (hlong₁ : ∀ b ∈ B, CycleAtLength G (b + r₁ + 2))
    (hlong₂ : CycleAtLength G (bMax + r₂ + 2)) :
    OneChordBoundaryCertificate G j := by
  classical
  let prefixes := insert 0 B
  refine {
    prefixes := prefixes
    prefixMax := bMax
    offset₁ := r₁ + 2
    offset₂ := r₂ + 2
    card_prefixes := ?_
    prefixMax_mem := by simp [prefixes, hbMax]
    prefix_le_max := ?_
    offset_lt := by omega
    first_odd := ?_
    last_odd := by exact (hBeven bMax hbMax).add_odd hr₂odd |>.add_even even_two
    first_cycles := ?_
    last_cycle := by simpa [Nat.add_assoc] using hlong₂ }
  · have hzeroNot : 0 ∉ B := fun h ↦ (Nat.ne_of_gt (hBpos 0 h)) rfl
    simp [prefixes, hzeroNot, hcard]
    omega
  · intro b hb
    simp only [prefixes, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact Nat.zero_le _
    · exact hmax b hb
  · intro b hb
    simp only [prefixes, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · simpa using hr₁odd.add_even even_two
    · exact (hBeven b hb).add_odd hr₁odd |>.add_even even_two
  · intro b hb
    simp only [prefixes, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · simpa using hbase₁
    · simpa [Nat.add_assoc] using hlong₁ b hb

/-- The corrected different-neighborhood boundary argument.  The two
mixed families exhaust all odd cycle lengths under the contrary cardinality
bound; an ordinary right-endpoint fan cycle then reflects into an actual
cycle of length `C.cycle.length + 2`, contradicting maximality. -/
theorem differentNeighborhoodNoChordBoundary_corrected [Finite V]
    (C : EndpointCount.LongestOddCycle G) {j : ℕ} (hj : 0 < j)
    (D : DifferentNeighborhoodNoChordConfiguration C j) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  by_contra hconclusion
  have hbound : (oddCycleLengths G).ncard ≤ j := by omega
  let S := D.exterior
  let L := cycleNeighborPositions C S.left
  let R := cycleNeighborPositions C S.right
  obtain ⟨y, hyDiff⟩ := D.extra_right_neighbor
  have hyR : y ∈ R := (Finset.mem_sdiff.mp hyDiff).1
  have hyNotL : y ∉ L := (Finset.mem_sdiff.mp hyDiff).2
  obtain ⟨X, hXL, hXcard⟩ :=
    Finset.exists_subset_card_eq D.many_left_neighbors
  let f : Fin C.cycle.length → ℕ := fun x ↦
    (cycleArc C y x).length + S.walk.length + 2
  let g : Fin C.cycle.length → ℕ := fun x ↦
    (cycleCoarc C y x).length + S.walk.length + 2
  let I := X.filter fun x ↦ Odd (f x)
  let J := X.filter fun x ↦ ¬ Odd (f x)
  let FI := I.image f
  let HJ := J.image g
  have hy_ne_of_mem_X {x : Fin C.cycle.length} (hx : x ∈ X) : y ≠ x := by
    intro h
    subst x
    exact hyNotL (hXL hx)
  have hfgOdd (x : Fin C.cycle.length) : Odd (f x + g x) := by
    have hsum := cycleArc_add_cycleCoarc_length C y x
    have heq : f x + g x =
        C.cycle.length + 2 * (S.walk.length + 2) := by
      dsimp [f, g]
      omega
    rw [heq]
    exact C.odd_length.add_even (even_two_mul _)
  have hJOdd {x : Fin C.cycle.length} (hx : x ∈ J) : Odd (g x) := by
    have hxNot : ¬ Odd (f x) := (Finset.mem_filter.mp hx).2
    apply Nat.not_even_iff_odd.mp
    intro hxEven
    exact hxNot ((Nat.odd_add.mp (hfgOdd x)).mpr hxEven)
  have hpartition : I.card + J.card = X.card := by
    simpa only [I, J] using
      (Finset.card_filter_add_card_filter_not
        (s := X) (fun x ↦ Odd (f x)))
  have hfInjective : Function.Injective f := by
    intro a b hab
    apply cycleArc_length_injective C y
    change (cycleArc C y a).length + S.walk.length + 2 =
      (cycleArc C y b).length + S.walk.length + 2 at hab
    change (cycleArc C y a).length = (cycleArc C y b).length
    omega
  have hgInjective : Function.Injective g := by
    intro a b hab
    apply cycleCoarc_length_injective C y
    change (cycleCoarc C y a).length + S.walk.length + 2 =
      (cycleCoarc C y b).length + S.walk.length + 2 at hab
    change (cycleCoarc C y a).length = (cycleCoarc C y b).length
    omega
  have hFIcard : FI.card = I.card := by
    exact Finset.card_image_of_injective I hfInjective
  have hHJcard : HJ.card = J.card := by
    exact Finset.card_image_of_injective J hgInjective
  have hFISub : ∀ n ∈ FI, n ∈ oddCycleLengths G := by
    intro n hn
    obtain ⟨x, hxI, rfl⟩ := Finset.mem_image.mp hn
    have hxX : x ∈ X := (Finset.mem_filter.mp hxI).1
    have hxL : x ∈ cycleNeighborPositions C S.left := hXL hxX
    have hodd : Odd (f x) := (Finset.mem_filter.mp hxI).2
    apply (mixedNeighborArcCycle C S y x (hy_ne_of_mem_X hxX)
      hyR hxL).mem_oddCycleLengths
    simpa only [f] using hodd
  have hHJSub : ∀ n ∈ HJ, n ∈ oddCycleLengths G := by
    intro n hn
    obtain ⟨x, hxJ, rfl⟩ := Finset.mem_image.mp hn
    have hxX : x ∈ X := (Finset.mem_filter.mp hxJ).1
    have hxL : x ∈ cycleNeighborPositions C S.left := hXL hxX
    have hodd : Odd (g x) := hJOdd hxJ
    apply (mixedNeighborCoarcCycle C S y x (hy_ne_of_mem_X hxX)
      hyR hxL).mem_oddCycleLengths
    simpa only [g] using hodd
  have hFIle : FI.card ≤ (oddCycleLengths G).ncard := by
    simpa using Set.ncard_le_ncard (s := (FI : Set ℕ))
      (t := oddCycleLengths G) hFISub (oddCycleLengths_finite G)
  have hHJle : HJ.card ≤ (oddCycleLengths G).ncard := by
    simpa using Set.ncard_le_ncard (s := (HJ : Set ℕ))
      (t := oddCycleLengths G) hHJSub (oddCycleLengths_finite G)
  have hIcard : I.card = j := by omega
  have hJcard : J.card = j := by omega
  have hFIcardj : FI.card = j := hFIcard.trans hIcard
  have hHJcardj : HJ.card = j := hHJcard.trans hJcard
  have hRtwo : 1 < R.card := by
    have hLlarge : 2 * j ≤ L.card := D.many_left_neighbors
    have hLR : L.card ≤ R.card := D.left_card_le_right_card
    omega
  have hRnontrivial : R.Nontrivial :=
    Finset.one_lt_card_iff_nontrivial.mp hRtwo
  obtain ⟨z, hzErase⟩ := hRnontrivial.erase_nonempty (a := y)
  have hzR : z ∈ R := (Finset.mem_erase.mp hzErase).2
  have hzy : z ≠ y := (Finset.mem_erase.mp hzErase).1
  let u := (cycleArc C y z).length + 2
  let v := (cycleCoarc C y z).length + 2
  have huvOdd : Odd (u + v) := by
    have hsum := cycleArc_add_cycleCoarc_length C y z
    have heq : u + v = C.cycle.length + 4 := by
      dsimp [u, v]
      omega
    rw [heq]
    exact C.odd_length.add_even (by
      simpa using (even_two_mul 2 : Even (2 * 2)))
  have huv : Odd u ∨ Odd v := by
    by_cases hu : Odd u
    · exact Or.inl hu
    · right
      apply Nat.not_even_iff_odd.mp
      intro hvEven
      exact hu ((Nat.odd_add.mp huvOdd).mpr hvEven)
  rcases huv with huOdd | hvOdd
  · have huCycle : CycleAtLength G u := by
      simpa only [u] using rightNeighborArcCycle C S y z hzy.symm hyR hzR
    have huMem : u ∈ oddCycleLengths G :=
      huCycle.mem_oddCycleLengths huOdd
    have huFI : u ∈ FI :=
      oddCycleLength_mem_of_full_family FI hFIcardj hFISub hbound huMem
    obtain ⟨i, hiI, hfi⟩ := Finset.mem_image.mp huFI
    have hiX : i ∈ X := (Finset.mem_filter.mp hiI).1
    have hiL : i ∈ cycleNeighborPositions C S.left := hXL hiX
    have hgap : (cycleArc C y z).length =
        (cycleArc C y i).length + S.walk.length := by
      dsimp [f, u] at hfi
      omega
    have hlong := mixedNeighborLongCycle_of_left_before_right
      C S y i z hiL hzR hgap
    have hlongOdd : Odd (C.cycle.length + 2) :=
      C.odd_length.add_even (by simp)
    have hle := C.longest (hlong.mem_oddCycleLengths hlongOdd)
    omega
  · have hvCycle : CycleAtLength G v := by
      simpa only [v] using rightNeighborCoarcCycle C S y z hzy.symm hyR hzR
    have hvMem : v ∈ oddCycleLengths G :=
      hvCycle.mem_oddCycleLengths hvOdd
    have hvFI : v ∈ FI :=
      oddCycleLength_mem_of_full_family FI hFIcardj hFISub hbound hvMem
    obtain ⟨i, hiI, hfi⟩ := Finset.mem_image.mp hvFI
    have hiX : i ∈ X := (Finset.mem_filter.mp hiI).1
    have hfiFI : f i ∈ FI := Finset.mem_image.mpr ⟨i, hiI, rfl⟩
    have hfiMem : f i ∈ oddCycleLengths G := hFISub _ hfiFI
    have hfiHJ : f i ∈ HJ :=
      oddCycleLength_mem_of_full_family HJ hHJcardj hHJSub hbound hfiMem
    obtain ⟨t, htJ, hgt⟩ := Finset.mem_image.mp hfiHJ
    have htX : t ∈ X := (Finset.mem_filter.mp htJ).1
    have htL : t ∈ cycleNeighborPositions C S.left := hXL htX
    have hreflect : (cycleArc C y t).length =
        (cycleCoarc C y i).length := by
      have hsumt := cycleArc_add_cycleCoarc_length C y t
      have hsumi := cycleArc_add_cycleCoarc_length C y i
      dsimp [f, g] at hgt
      omega
    have hgap : (cycleArc C y t).length =
        (cycleArc C y z).length + S.walk.length := by
      have hsumz := cycleArc_add_cycleCoarc_length C y z
      have hsumi := cycleArc_add_cycleCoarc_length C y i
      dsimp [f, v] at hfi
      omega
    have hlong := mixedNeighborLongCycle_of_right_before_left
      C S y z t hzR htL hgap
    have hlongOdd : Odd (C.cycle.length + 2) :=
      C.odd_length.add_even (by simp)
    have hle := C.longest (hlong.mem_oddCycleLengths hlongOdd)
    omega

end

end Erdos58.Structural
