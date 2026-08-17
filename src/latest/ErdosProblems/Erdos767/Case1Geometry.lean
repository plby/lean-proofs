import ErdosProblems.Erdos767.Lollipop
import ErdosProblems.Erdos767.Case1Count
import ErdosProblems.Erdos767.Aligned

open Finset
open scoped SimpleGraph

namespace Erdos767Scratch

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Membership in the support of a `take` implies membership in the original
walk. -/
private lemma mem_support_of_mem_take {a b x : V} (p : G.Walk a b) (n : ℕ)
    (hx : x ∈ (p.take n).support) : x ∈ p.support := by
  obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  rw [Walk.take_getVert] at hjx
  exact hjx ▸ p.getVert_mem_support (min n j)

/-- Membership in the support of a `drop` implies membership in the original
walk. -/
private lemma mem_support_of_mem_drop {a b x : V} (p : G.Walk a b) (n : ℕ)
    (hx : x ∈ (p.drop n).support) : x ∈ p.support := by
  obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  rw [Walk.drop_getVert] at hjx
  exact hjx ▸ p.getVert_mem_support (n + j)

/-- A simple path of length at least two, closed by an edge between its
endpoints, gives a cycle.  The chosen orientation is convenient below. -/
private lemma isCycle_cons_reverse_of_isPath {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hlen : 2 ≤ p.length) (hba : G.Adj b a) :
    (p.reverse.cons hba.symm).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp.reverse, ?_⟩
  intro hedge
  have hedge' : s(a, b) ∈ p.edges := by
    simpa [Walk.edges_reverse] using hedge
  have hone := hp.length_eq_one_of_mem_edges hedge'
  omega

/-- The terminal of a positive lollipop tail is outside its cycle. -/
lemma Lollipop.terminal_not_mem_cycle (L : Lollipop G)
    (hpos : 0 < L.tail.length) : L.terminal ∉ L.cycle.support := by
  intro hyC
  have hEq : L.terminal = L.start :=
    L.cycle_tail_inter hyC L.tail.end_mem_support
  have hzero : L.tail.length = 0 := by
    symm
    apply L.tail_isPath.getVert_injOn (x₁ := 0) (x₂ := L.tail.length)
      (by simp) (by simp)
    rw [L.tail.getVert_zero, L.tail.getVert_length, hEq]
  omega

/-- The longest cycle rotated to start at the tail attachment. -/
def BestLollipop.rotatedCycle (B : BestLollipop G) :
    G.Walk B.start B.start :=
  B.cycle.rotate B.start B.start_mem_cycle

@[simp] lemma BestLollipop.rotatedCycle_length (B : BestLollipop G) :
    B.rotatedCycle.length = B.cycle.length :=
  Walk.length_rotate B.cycle B.start B.start_mem_cycle

lemma BestLollipop.rotatedCycle_isCycle (B : BestLollipop G) :
    B.rotatedCycle.IsCycle :=
  B.cycle_isCycle.rotate B.start_mem_cycle

lemma BestLollipop.mem_cycle_of_mem_rotatedCycle (B : BestLollipop G) {w : V}
    (hw : w ∈ B.rotatedCycle.support) : w ∈ B.cycle.support :=
  (Walk.mem_support_rotate_iff B.cycle B.start B.start_mem_cycle).mp hw

/-- In the complementary prefix and suffix obtained by deleting the cycle
edge at positions `i,i+1`, the only common vertex is the cycle base. -/
private lemma drop_succ_meet_take_eq_start {x : V} {C : G.Walk x x}
    (hC : C.IsCycle) {i : ℕ} (hi : i + 1 < C.length) :
    ∀ ⦃w : V⦄, w ∈ (C.drop (i + 1)).support →
      w ∈ (C.take i).support → w = x := by
  intro w hwD hwT
  obtain ⟨j, hjw, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hwD
  obtain ⟨k, hkw, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hwT
  rw [Walk.drop_getVert] at hjw
  rw [Walk.take_length, min_eq_left (by omega : i ≤ C.length)] at hkle
  rw [Walk.take_getVert, min_eq_right hkle] at hkw
  have hjbound : i + 1 + j ≤ C.length := by
    rw [Walk.drop_length] at hjle
    omega
  by_cases hjend : i + 1 + j = C.length
  · calc
      w = C.getVert (i + 1 + j) := hjw.symm
      _ = C.getVert C.length := by rw [hjend]
      _ = x := C.getVert_length
  · have hjlt : i + 1 + j < C.length := lt_of_le_of_ne hjbound hjend
    have hkeq : i + 1 + j = k := by
      apply hC.getVert_injOn' (x₁ := i + 1 + j) (x₂ := k)
      · show i + 1 + j ≤ C.length - 1
        omega
      · show k ≤ C.length - 1
        omega
      · exact hjw.trans hkw.symm
    omega

/-- Geometry of one positive-index cycle neighbor of the terminal.  Both
complementary cycle arcs can be closed through the lollipop tail, so longest-
cycle maximality puts the index in the exact interval
`[tail.length+1, cycle.length-tail.length-1]`. -/
theorem BestLollipop.cycle_neighbor_index_bounds
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {i : ℕ} (hi : i < B.rotatedCycle.length) (hi0 : 0 < i)
    (hyi : G.Adj B.terminal (B.rotatedCycle.getVert i)) :
    B.tail.length + 1 ≤ i ∧
      i ≤ B.rotatedCycle.length - B.tail.length - 1 := by
  let C := B.rotatedCycle
  let A₁ : G.Walk (C.getVert i) B.start := C.drop i
  have hA₁ : A₁.IsPath := B.rotatedCycle_isCycle.isPath_drop hi0
  have hmeet₁ : ∀ ⦃w : V⦄, w ∈ A₁.support →
      w ∈ B.tail.support → w = B.start := by
    intro w hwA hwP
    apply B.cycle_tail_inter _ hwP
    apply B.mem_cycle_of_mem_rotatedCycle
    exact mem_support_of_mem_drop C i hwA
  let R₁ : G.Walk (C.getVert i) B.terminal := A₁.append B.tail
  have hR₁ : R₁.IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hA₁ B.tail_isPath hmeet₁
  have hR₁len : R₁.length =
      (C.length - i) + B.tail.length := by
    simp [R₁, A₁]
  have hR₁two : 2 ≤ R₁.length := by
    have hApos : 0 < C.length - i := Nat.sub_pos_of_lt hi
    rw [hR₁len]
    omega
  let D₁ : G.Walk (C.getVert i) (C.getVert i) :=
    R₁.reverse.cons hyi.symm
  have hD₁ : D₁.IsCycle :=
    isCycle_cons_reverse_of_isPath R₁ hR₁ hR₁two hyi
  have hD₁len : D₁.length =
      (C.length - i) + B.tail.length + 1 := by
    simp [D₁, hR₁len]
  have hmax₁ : D₁.length ≤ B.cycle.length := B.cycle_maximal D₁ hD₁
  have hmax₁' : D₁.length ≤ C.length := by simpa [C] using hmax₁
  have hlower : B.tail.length + 1 ≤ i := by
    rw [hD₁len] at hmax₁'
    omega

  let A₂ : G.Walk (C.getVert i) B.start := (C.take i).reverse
  have hA₂ : A₂.IsPath := (B.rotatedCycle_isCycle.isPath_take hi).reverse
  have hmeet₂ : ∀ ⦃w : V⦄, w ∈ A₂.support →
      w ∈ B.tail.support → w = B.start := by
    intro w hwA hwP
    apply B.cycle_tail_inter _ hwP
    apply B.mem_cycle_of_mem_rotatedCycle
    apply mem_support_of_mem_take C i
    simpa [A₂] using hwA
  let R₂ : G.Walk (C.getVert i) B.terminal := A₂.append B.tail
  have hR₂ : R₂.IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hA₂ B.tail_isPath hmeet₂
  have hiC : i ≤ C.length := by simpa [C] using hi.le
  have hR₂len : R₂.length = i + B.tail.length := by
    simp [R₂, A₂, min_eq_left hiC]
  have hR₂two : 2 ≤ R₂.length := by rw [hR₂len]; omega
  let D₂ : G.Walk (C.getVert i) (C.getVert i) :=
    R₂.reverse.cons hyi.symm
  have hD₂ : D₂.IsCycle :=
    isCycle_cons_reverse_of_isPath R₂ hR₂ hR₂two hyi
  have hD₂len : D₂.length = i + B.tail.length + 1 := by
    simp [D₂, hR₂len]
  have hmax₂ : D₂.length ≤ B.cycle.length := B.cycle_maximal D₂ hD₂
  have hmax₂' : D₂.length ≤ C.length := by simpa [C] using hmax₂
  have hupper : i ≤ C.length - B.tail.length - 1 := by
    rw [hD₂len] at hmax₂'
    omega
  exact ⟨hlower, hupper⟩

/-- Two positive cycle-neighbor indices of the lollipop terminal cannot be
consecutive: replacing their intervening cycle edge by the two-edge detour
through the terminal would produce a cycle one edge longer. -/
theorem BestLollipop.not_succ_cycle_neighbor
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {i : ℕ} (hi : i + 1 < B.rotatedCycle.length)
    (hyi : G.Adj B.terminal (B.rotatedCycle.getVert i)) :
    ¬ G.Adj B.terminal (B.rotatedCycle.getVert (i + 1)) := by
  intro hyi1
  let C := B.rotatedCycle
  have hiC : i + 1 < C.length := by simpa [C] using hi
  let A : G.Walk (C.getVert (i + 1)) B.start := C.drop (i + 1)
  let Z : G.Walk B.start (C.getVert i) := C.take i
  have hA : A.IsPath := B.rotatedCycle_isCycle.isPath_drop (by omega)
  have hZ : Z.IsPath := B.rotatedCycle_isCycle.isPath_take (by omega)
  have hmeet : ∀ ⦃w : V⦄, w ∈ A.support → w ∈ Z.support → w = B.start := by
    intro w hwA hwZ
    exact drop_succ_meet_take_eq_start B.rotatedCycle_isCycle hiC hwA hwZ
  let R : G.Walk (C.getVert (i + 1)) (C.getVert i) := A.append Z
  have hR : R.IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hA hZ hmeet
  have hRlen : R.length = C.length - 1 := by
    simp [R, A, Z, min_eq_left (show i ≤ C.length by omega)]
    omega
  have hyOut : B.terminal ∉ B.cycle.support :=
    B.toLollipop.terminal_not_mem_cycle hpos
  have hyR : B.terminal ∉ R.support := by
    intro hy
    simp only [R, Walk.mem_support_append_iff] at hy
    rcases hy with hyA | hyZ
    · apply hyOut
      apply B.mem_cycle_of_mem_rotatedCycle
      exact mem_support_of_mem_drop C (i + 1) hyA
    · apply hyOut
      apply B.mem_cycle_of_mem_rotatedCycle
      exact mem_support_of_mem_take C i hyZ
  let S : G.Walk (C.getVert (i + 1)) B.terminal :=
    R.concat hyi.symm
  have hS : S.IsPath := hR.concat hyR hyi.symm
  have hSlen : S.length = C.length := by
    simp [S, hRlen]
    have := B.rotatedCycle_isCycle.three_le_length
    omega
  have hStwo : 2 ≤ S.length := by
    rw [hSlen]
    exact B.rotatedCycle_isCycle.three_le_length.trans' (by omega)
  let D : G.Walk (C.getVert (i + 1)) (C.getVert (i + 1)) :=
    S.reverse.cons hyi1.symm
  have hD : D.IsCycle :=
    isCycle_cons_reverse_of_isPath S hS hStwo hyi1
  have hDlen : D.length = C.length + 1 := by
    simp [D, hSlen]
  have hmax := B.cycle_maximal D hD
  have hmax' : D.length ≤ C.length := by simpa [C] using hmax
  rw [hDlen] at hmax'
  omega

/-- The exact interval and successor-exclusion package consumed by the
nonconsecutive-index count. -/
theorem BestLollipop.positive_cycle_neighbor_geometry
    (B : BestLollipop G) (hpos : 0 < B.tail.length) :
    (∀ i ∈ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal,
      B.tail.length + 1 ≤ i) ∧
    (∀ i ∈ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal,
      i ≤ B.rotatedCycle.length - B.tail.length - 1) ∧
    (∀ i ∈ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal,
      i + 1 ∉ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [E767Case1Fixed.mem_positiveCycleNeighborIndices] at hi
    exact (B.cycle_neighbor_index_bounds hpos hi.2.1
      (Nat.pos_of_ne_zero hi.1) hi.2.2).1
  · intro i hi
    rw [E767Case1Fixed.mem_positiveCycleNeighborIndices] at hi
    exact (B.cycle_neighbor_index_bounds hpos hi.2.1
      (Nat.pos_of_ne_zero hi.1) hi.2.2).2
  · intro i hi hi1
    rw [E767Case1Fixed.mem_positiveCycleNeighborIndices] at hi hi1
    exact B.not_succ_cycle_neighbor hpos hi1.2.1 hi.2.2 hi1.2.2

/-- Fully assembled Case 1: if the positive cycle-neighbor set is nonempty,
the terminal degree is at most half the longest-cycle length. -/
theorem BestLollipop.two_mul_degree_terminal_le_cycle_length_case1
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    (hcover : G.neighborFinset B.terminal ⊆
      B.rotatedCycle.support.dropLast.toFinset ∪ B.tail.support.toFinset)
    (hnonempty : (E767Case1Fixed.positiveCycleNeighborIndices
      B.rotatedCycle B.terminal).Nonempty) :
    2 * G.degree B.terminal ≤ B.cycle.length := by
  obtain ⟨hlower, hupper, hnext⟩ := B.positive_cycle_neighbor_geometry hpos
  have hbound := E767Case1Fixed.case1_of_positive_indices
    B.rotatedCycle_isCycle B.tail_isPath hcover hnonempty
    hlower hupper hnext (k := G.degree B.terminal) (le_refl _)
  simpa using hbound

end

end Erdos767Scratch

