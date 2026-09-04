import ErdosProblems.Erdos58.Independent
import ErdosProblems.Erdos58.Linkage
import ErdosProblems.Erdos58.Boundary
import ErdosProblems.Erdos58.Structural.HamiltonianBranch
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

namespace Erdos58.Structural

open Set
open SimpleGraph
open scoped SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace IndependentGap

/-- The canonical simple cycle on `cycleGraph n`, with its type rewritten
from Mathlib's `m + 3` presentation. -/
def cycleWalk (n : ℕ) (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).Walk
      ⟨0, Nat.zero_lt_of_lt hn⟩ ⟨0, Nat.zero_lt_of_lt hn⟩ := by
  obtain _ | _ | _ | n := n
  · omega
  · omega
  · omega
  · exact SimpleGraph.cycleGraph.cycle n

@[simp] theorem cycleWalk_length (n : ℕ) (hn : 3 ≤ n) :
    (cycleWalk n hn).length = n := by
  obtain _ | _ | _ | n := n
  · omega
  · omega
  · omega
  · simp [cycleWalk]

theorem cycleWalk_isCycle (n : ℕ) (hn : 3 ≤ n) :
    (cycleWalk n hn).IsCycle := by
  obtain _ | _ | _ | n := n
  · omega
  · omega
  · omega
  · simpa [cycleWalk] using
      SimpleGraph.cycleGraph.isCycle_cycle (n := n)

theorem cycleWalk_getVert (n : ℕ) (hn : 3 ≤ n) (i : ℕ) (hi : i ≤ n) :
    (cycleWalk n hn).getVert i =
      ⟨(n - i) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt hn)⟩ := by
  obtain _ | _ | _ | n := n
  · omega
  · omega
  · omega
  · simpa [cycleWalk, Nat.add_assoc] using
      (SimpleGraph.cycleGraph.getVert_cycle (n := n) hi)

/-- Rebase a copy of a cycle at `x`, with its canonical walk running in the
positive direction from `x`. -/
def rebaseCopy (C : LongestOddCycle G) (x : Fin C.length) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph C.length) G := by
  letI : NeZero C.length :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  exact
    { toHom :=
        { toFun := fun z => C.copy (x - z)
          map_rel' := by
            intro a b hab
            apply C.copy.toHom.map_adj
            rw [SimpleGraph.cycleGraph_adj'] at hab ⊢
            rcases hab with hab | hab
            · right
              have heq : x - b - (x - a) = a - b := by abel
              rw [heq]
              exact hab
            · left
              have heq : x - a - (x - b) = b - a := by abel
              rw [heq]
              exact hab }
      injective' := by
        intro a b hab
        have hab' : x - a = x - b := C.copy.injective hab
        have := congrArg (fun z => x - z) hab'
        have hxa : x - (x - a) = a := by abel
        have hxb : x - (x - b) = b := by abel
        rwa [hxa, hxb] at this }

/-- The designated rim, rebased at `x` and oriented so that its `i`-th
vertex is `x+i` in `Fin C.length`. -/
def rimWalk (C : LongestOddCycle G) (x : Fin C.length) :
    G.Walk (C.copy x) (C.copy x) := by
  letI : NeZero C.length :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  let q := (cycleWalk C.length C.three_le).map (rebaseCopy C x).toHom
  exact q.copy (by change C.copy (x - 0) = C.copy x; simp)
    (by change C.copy (x - 0) = C.copy x; simp)

@[simp] theorem rimWalk_length (C : LongestOddCycle G) (x : Fin C.length) :
    (rimWalk C x).length = C.length := by
  simp [rimWalk]

theorem rimWalk_isCycle (C : LongestOddCycle G) (x : Fin C.length) :
    (rimWalk C x).IsCycle := by
  rw [rimWalk]
  simpa only [SimpleGraph.Walk.isCycle_copy] using
    (cycleWalk_isCycle C.length C.three_le).map (rebaseCopy C x).injective

theorem rimWalk_getVert (C : LongestOddCycle G) (x : Fin C.length)
    (i : ℕ) (hi : i ≤ C.length) :
    (rimWalk C x).getVert i =
      C.copy (x + ⟨i % C.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩) := by
  rw [rimWalk]
  simp only [SimpleGraph.Walk.getVert_copy]
  rw [SimpleGraph.Walk.getVert_map]
  simp only [rebaseCopy]
  rw [cycleWalk_getVert C.length C.three_le i hi]
  change C.copy
      (x - ⟨(C.length - i) % C.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩) =
    C.copy (x + ⟨i % C.length,
      Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩)
  congr 1
  let : NeZero C.length :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  let a : Fin C.length := ⟨i % C.length,
    Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩
  have hz : (⟨(C.length - i) % C.length,
      Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩ : Fin C.length) = -a := by
    by_cases hieq : i = C.length
    · subst i
      apply Fin.ext
      simp [a]
    · have hilt : i < C.length := lt_of_le_of_ne hi hieq
      by_cases hi0 : i = 0
      · subst i
        apply Fin.ext
        simp [a]
      · have hsub : C.length - i < C.length :=
          Nat.sub_lt (Nat.zero_lt_of_lt C.three_le) (Nat.zero_lt_of_ne_zero hi0)
        apply Fin.ext
        simp [a, Fin.val_neg, Nat.mod_eq_of_lt hilt,
          Nat.mod_eq_of_lt hsub, hi0]
  change x - _ = x + a
  rw [hz]
  abel

/-- Closing a nontrivial rim arc through a vertex outside the rim gives an
actual simple cycle of the expected length. -/
theorem hubArc_cycleAtLength (C : LongestOddCycle G) {t : V}
    (ht : t ∈ C.carrierᶜ) {x y : Fin C.length}
    (hxy : y ≠ x) (htx : G.Adj t (C.copy x)) (hty : G.Adj t (C.copy y)) :
    CycleAtLength G ((y - x).val + 2) := by
  let : NeZero C.length := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  let d := (y - x).val
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    apply hxy
    apply sub_eq_zero.mp
    apply Fin.ext
    exact hd0
  have hdlt : d < C.length := (y - x).isLt
  let p := (rimWalk C x).take d
  have hpPath : p.IsPath := (rimWalk_isCycle C x).isPath_take (by simpa using hdlt)
  have hpEnd : (rimWalk C x).getVert d = C.copy y := by
    rw [rimWalk_getVert C x d hdlt.le]
    congr 1
    have hz : (⟨d % C.length, Nat.mod_lt _
        (Nat.zero_lt_of_lt C.three_le)⟩ : Fin C.length) = y - x := by
      apply Fin.ext
      simp [d, Nat.mod_eq_of_lt (y - x).isLt]
    rw [hz]
    abel
  let p' : G.Walk (C.copy x) (C.copy y) := p.copy rfl hpEnd
  have hp'Path : p'.IsPath := by simpa [p'] using hpPath
  have htNot : t ∉ p'.support := by
    intro hmem
    have hmem' : t ∈ C.carrier := by
      rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem with
        ⟨i, hiEq, hile⟩
      have hplen : p'.length = d := by simp [p', p, d, hdlt.le]
      have hid : i ≤ d := by omega
      have hiL : i ≤ C.length := hid.trans hdlt.le
      refine ⟨x + ⟨i % C.length, Nat.mod_lt _
        (Nat.zero_lt_of_lt C.three_le)⟩, ?_⟩
      calc
        C.copy (x + ⟨i % C.length, Nat.mod_lt _
          (Nat.zero_lt_of_lt C.three_le)⟩) = (rimWalk C x).getVert i :=
            (rimWalk_getVert C x i hiL).symm
        _ = p'.getVert i := by
          simp [p', p, SimpleGraph.Walk.take_getVert, Nat.min_eq_right hid]
        _ = t := hiEq
    exact ht hmem'
  let q : G.Walk t t := (p'.concat hty.symm).cons htx
  refine ⟨t, q, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · simpa [q] using hp'Path.concat htNot hty.symm
    · simp [q, p', p, d, hdlt.le]
      omega
  · simp [q, p', p, d, hdlt.le]

theorem mem_carrier_of_mem_rimWalk_support (C : LongestOddCycle G)
    (x : Fin C.length) {v : V} (hv : v ∈ (rimWalk C x).support) :
    v ∈ C.carrier := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv with
    ⟨i, hiEq, hi⟩
  refine ⟨x + ⟨i % C.length,
    Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩, ?_⟩
  rw [← hiEq]
  exact (rimWalk_getVert C x i (by simpa using hi)).symm

/-- Cutting the two edges incident with a chosen vertex of the canonical
rim leaves a path through all the other rim vertices. -/
def cycleCutPath (C : LongestOddCycle G) (x : Fin C.length) : CycleCutPath C := by
  let p := rimWalk C x
  let w := p.tail.dropLast
  have hpcycle : p.IsCycle := rimWalk_isCycle C x
  have hptailPath : p.tail.IsPath := hpcycle.isPath_tail
  have htailLen : p.tail.length = C.length - 1 := by
    simp [p]
  have htailNonempty : ¬p.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    rw [htailLen]
    have hC := C.three_le
    omega

  refine
    { cut := C.copy x
      start := p.snd
      finish := p.tail.penultimate
      walk := w
      isPath := hptailPath.dropLast
      support_subset := ?_
      cut_mem := ⟨x, rfl⟩
      cut_notMem_support := ?_
      length_add_two := ?_ }
  · intro v hv
    have hvtail : v ∈ p.tail.support := by
      change v ∈ p.tail.dropLast.support at hv
      rw [SimpleGraph.Walk.support_dropLast htailNonempty] at hv
      exact List.mem_of_mem_dropLast hv
    have hvp : v ∈ p.support := by
      rw [p.support_tail_of_not_nil hpcycle.not_nil] at hvtail
      exact List.mem_of_mem_tail hvtail
    exact mem_carrier_of_mem_rimWalk_support C x hvp
  · intro hxmem
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxmem with
      ⟨i, hiEq, hi⟩
    have hwlen : w.length = p.tail.length - 1 := by simp [w]
    have hilt : i < p.tail.length := by
      rw [hwlen] at hi
      have hC := C.three_le
      have htl := htailLen
      omega
    have hiEq' : p.tail.getVert i = C.copy x := by
      rw [← SimpleGraph.Walk.getVert_dropLast hilt]
      exact hiEq
    have hiEnd : i = p.tail.length :=
      (hptailPath.getVert_eq_end_iff (by omega)).mp hiEq'
    omega
  · have hwlen : w.length = p.tail.length - 1 := by simp [w]
    rw [hwlen, htailLen]
    have hC := C.three_le
    omega

/-- Indices on the designated cycle which are adjacent to `t`. -/
def neighborIndices (C : LongestOddCycle G) (t : V) : Finset (Fin C.length) :=
  Finset.univ.filter fun x => G.Adj t (C.copy x)

theorem card_neighborIndices_eq_degree (C : LongestOddCycle G) {t : V}
    (hind : HasIndependentExterior C) (ht : t ∈ C.carrierᶜ) :
    (neighborIndices C t).card = G.degree t := by
  classical
  have hmap : (neighborIndices C t).map C.copy.toEmbedding = G.neighborFinset t := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_filter.mp hx).2
    · intro hv
      have hadj : G.Adj t v :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := t) v).mp hv
      have hvC : v ∈ C.carrier := by
        by_contra hvC
        exact hind ht hvC (G.ne_of_adj hadj) hadj
      rcases hvC with ⟨x, rfl⟩
      apply Finset.mem_map.mpr
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hmap,
    Finset.card_map]

theorem forward_reverse_distance_sum {n : ℕ} [NeZero n] {x y : Fin n}
    (hxy : y ≠ x) : (y - x).val + (x - y).val = n := by
  have hforward : 0 < (y - x).val := by
    by_contra h
    have hv0 : (y - x).val = 0 := Nat.eq_zero_of_not_pos h
    apply hxy
    apply sub_eq_zero.mp
    apply Fin.ext
    simpa using hv0
  have hreverse : 0 < (x - y).val := by
    by_contra h
    have hv0 : (x - y).val = 0 := Nat.eq_zero_of_not_pos h
    apply hxy
    symm
    apply sub_eq_zero.mp
    apply Fin.ext
    simpa using hv0
  have hmod : ((y - x).val + (x - y).val) % n = 0 := by
    have hzero : (y - x) + (x - y) = (0 : Fin n) := by abel
    exact congrArg Fin.val hzero
  have hdvd : n ∣ (y - x).val + (x - y).val := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨q, hq⟩ := hdvd
  have hnpos : 0 < n := NeZero.pos n
  have hflt := (y - x).isLt
  have hrlt := (x - y).isLt
  have hmul : n * q < n * 2 := by omega
  have hq2 : q < 2 := (Nat.mul_lt_mul_left hnpos).mp hmul
  have hqpos : 0 < q := by
    by_contra hq0
    have : q = 0 := Nat.eq_zero_of_not_pos hq0
    subst q
    have hsum0 : (y - x).val + (x - y).val = 0 := by simpa using hq
    omega
  have hqeq : q = 1 := by omega
  subst q
  simpa using hq

theorem reverse_distance_odd_of_forward_not_odd {n : ℕ} [NeZero n]
    (hnodd : Odd n) {x y : Fin n} (hxy : y ≠ x)
    (hnot : ¬Odd (y - x).val) : Odd (x - y).val := by
  have hsum := forward_reverse_distance_sum hxy
  have hoddSum : Odd ((y - x).val + (x - y).val) := by simpa [hsum] using hnodd
  rw [Nat.odd_add] at hoddSum
  rw [← Nat.not_even_iff_odd]
  intro heven
  exact hnot (hoddSum.mpr heven)

theorem forwardLength_injective {n : ℕ} [NeZero n] (x : Fin n) :
    Function.Injective fun y : Fin n => (y - x).val + 2 := by
  intro y z h
  change (y - x).val + 2 = (z - x).val + 2 at h
  have hv : (y - x).val = (z - x).val := Nat.add_right_cancel h
  have hfin : y - x = z - x := Fin.ext hv
  have := congrArg (fun q => q + x) hfin
  simpa only [sub_add_cancel] using this

theorem reverseLength_injective {n : ℕ} [NeZero n] (x : Fin n) :
    Function.Injective fun y : Fin n => (x - y).val + 2 := by
  intro y z h
  change (x - y).val + 2 = (x - z).val + 2 at h
  have hv : (x - y).val = (x - z).val := Nat.add_right_cancel h
  exact sub_right_injective (Fin.ext hv)

/-- For a fixed selected neighbour `x`, the odd forward arcs already realize
all allowable odd cycle lengths.  In particular one of them has length equal
to the designated longest cycle. -/
theorem selected_neighbors_have_long_arc (C : LongestOddCycle G) {t : V}
    (ht : t ∈ C.carrierᶜ) {j : ℕ} (X : Finset (Fin C.length))
    (hXsub : X ⊆ neighborIndices C t) (hXcard : X.card = 2 * j + 1)
    (hcount : (oddCycleLengths G).ncard ≤ j) {x : Fin C.length} (hx : x ∈ X) :
    ∃ y ∈ X, (y - x).val + 2 = C.length := by
  classical
  let : NeZero C.length :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  let D := X.erase x
  let O := D.filter fun y => Odd (y - x).val
  let E := D.filter fun y => ¬Odd (y - x).val
  let LO := O.image fun y => (y - x).val + 2
  let LE := E.image fun y => (x - y).val + 2

  have hxAdj : G.Adj t (C.copy x) := by
    have hxN := hXsub hx
    exact (Finset.mem_filter.mp hxN).2
  have hDcard : D.card = 2 * j := by
    change (X.erase x).card = 2 * j
    rw [Finset.card_erase_of_mem hx, hXcard]
    omega
  have hpartition : O.card + E.card = 2 * j := by
    change (D.filter fun y => Odd (y - x).val).card +
      (D.filter fun y => ¬Odd (y - x).val).card = 2 * j
    exact (Finset.card_filter_add_card_filter_not
      (s := D) (fun y => Odd (y - x).val)).trans hDcard
  have hLOcard : LO.card = O.card := by
    exact Finset.card_image_of_injective O (forwardLength_injective x)
  have hLEcard : LE.card = E.card := by
    exact Finset.card_image_of_injective E (reverseLength_injective x)

  have hLOodd : ∀ n ∈ LO, Odd n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨y, hyO, rfl⟩
    have hyodd : Odd (y - x).val := (Finset.mem_filter.mp hyO).2
    rcases hyodd with ⟨q, hq⟩
    refine ⟨q + 1, ?_⟩
    omega
  have hLOcycle : ∀ n ∈ LO, CycleAtLength G n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨y, hyO, rfl⟩
    have hyD : y ∈ D := (Finset.mem_filter.mp hyO).1
    have hyX : y ∈ X := (Finset.mem_erase.mp hyD).2
    have hyne : y ≠ x := (Finset.mem_erase.mp hyD).1
    have hyAdj : G.Adj t (C.copy y) := by
      exact (Finset.mem_filter.mp (hXsub hyX)).2
    exact hubArc_cycleAtLength C ht hyne hxAdj hyAdj

  have hLEodd : ∀ n ∈ LE, Odd n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨y, hyE, rfl⟩
    have hyD : y ∈ D := (Finset.mem_filter.mp hyE).1
    have hyne : y ≠ x := (Finset.mem_erase.mp hyD).1
    have hyodd : Odd (x - y).val :=
      reverse_distance_odd_of_forward_not_odd C.odd hyne
        (Finset.mem_filter.mp hyE).2
    rcases hyodd with ⟨q, hq⟩
    refine ⟨q + 1, ?_⟩
    omega
  have hLEcycle : ∀ n ∈ LE, CycleAtLength G n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨y, hyE, rfl⟩
    have hyD : y ∈ D := (Finset.mem_filter.mp hyE).1
    have hyX : y ∈ X := (Finset.mem_erase.mp hyD).2
    have hyne : y ≠ x := (Finset.mem_erase.mp hyD).1
    have hyAdj : G.Adj t (C.copy y) := by
      exact (Finset.mem_filter.mp (hXsub hyX)).2
    exact hubArc_cycleAtLength C ht hyne.symm hyAdj hxAdj

  have hOcard_le : O.card ≤ j := by
    rw [← hLOcard]
    exact (ncard_oddCycleLengths_ge_of_finset LO hLOodd hLOcycle).trans hcount
  have hEcard_le : E.card ≤ j := by
    rw [← hLEcard]
    exact (ncard_oddCycleLengths_ge_of_finset LE hLEodd hLEcycle).trans hcount
  have hOcard : O.card = j := by omega
  have hLOcard' : LO.card = j := hLOcard.trans hOcard

  have hLOsub : (LO : Set ℕ) ⊆ oddCycleLengths G := by
    intro n hn
    exact (hLOcycle n hn).mem_oddCycleLengths (hLOodd n hn)
  have hLOeq : (LO : Set ℕ) = oddCycleLengths G := by
    exact Set.eq_of_subset_of_ncard_le hLOsub
      (by simpa [hLOcard'] using hcount) (oddCycleLengths_finite G)
  have hClenLO : C.length ∈ LO := by
    have hClen : C.length ∈ oddCycleLengths G := C.length_mem_oddCycleLengths
    rwa [← hLOeq] at hClen
  rcases Finset.mem_image.mp hClenLO with ⟨y, hyO, hylen⟩
  refine ⟨y, ?_, hylen⟩
  exact (Finset.mem_erase.mp (Finset.mem_filter.mp hyO).1).2

theorem finRotate_sq_eq_of_long_arc {n : ℕ} (hn : 3 ≤ n) {x y : Fin n}
    (h : (y - x).val + 2 = n) : (finRotate n ^ 2) y = x := by
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  have hadd : y + (2 : Fin n) = x := by
    have hz : y - x + (2 : Fin n) = 0 := by
      apply Fin.ext
      change (((y - x).val + (2 : Fin n).val) % n) = 0
      have htwo : (2 : Fin n).val = 2 := by
        simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn]
      rw [htwo, h]
      simp
    calc
      y + (2 : Fin n) = (y - x + (2 : Fin n)) + x := by abel
      _ = 0 + x := congrArg (fun z : Fin n => z + x) hz
      _ = x := zero_add x
  rw [pow_two, Equiv.Perm.mul_apply, finRotate_apply, finRotate_apply]
  have hone : (1 : Fin n) + 1 = (2 : Fin n) := by
    apply Fin.ext
    have htwo : 2 < n := lt_of_lt_of_le (by omega) hn
    simp [Fin.val_add, Nat.mod_eq_of_lt htwo]
  calc
    y + 1 + 1 = y + ((1 : Fin n) + 1) := add_assoc _ _ _
    _ = y + (2 : Fin n) := congrArg (fun z : Fin n => y + z) hone
    _ = x := hadd

/-- A selected set of `2j+1` neighbours of an exterior vertex must be the
whole rim.  The key point is that it is closed under a two-step cyclic shift,
and a two-step shift is a single cycle on an odd rim. -/
theorem selected_neighbors_eq_univ (C : LongestOddCycle G) {t : V}
    (ht : t ∈ C.carrierᶜ) {j : ℕ} (X : Finset (Fin C.length))
    (hXsub : X ⊆ neighborIndices C t) (hXcard : X.card = 2 * j + 1)
    (hcount : (oddCycleLengths G).ncard ≤ j) : X = Finset.univ := by
  classical
  let : NeZero C.length :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  let r : Equiv.Perm (Fin C.length) := finRotate C.length
  let σ : Equiv.Perm (Fin C.length) := r ^ 2
  have htwo : 2 ≤ C.length := (by omega : 2 ≤ 3).trans C.three_le
  have hr : r.IsCycle := by
    exact isCycle_finRotate_of_le htwo
  have hrSupport : r.support = Finset.univ := by
    exact support_finRotate_of_le htwo
  have hrOrder : orderOf r = C.length := by
    rw [hr.orderOf, hrSupport, Finset.card_univ, Fintype.card_fin]
  have hcop : Nat.Coprime 2 (orderOf r) := by
    rw [hrOrder]
    exact Nat.coprime_two_left.mpr C.odd
  have hσcycle : σ.IsCycle := by
    exact hr.pow_iff.mpr hcop
  have hσSupport : σ.support = Finset.univ := by
    change (r ^ 2).support = Finset.univ
    rw [hr.support_pow_of_pos_of_lt_orderOf (by omega)
        (by rw [hrOrder]; exact lt_of_lt_of_le (by omega) C.three_le),
      hrSupport]

  have hpre : ∀ x ∈ X, ∃ y ∈ X, σ y = x := by
    intro x hx
    rcases selected_neighbors_have_long_arc C ht X hXsub hXcard hcount hx with
      ⟨y, hyX, hylen⟩
    refine ⟨y, hyX, ?_⟩
    exact finRotate_sq_eq_of_long_arc C.three_le hylen
  let emb : Fin C.length ↪ Fin C.length := σ.toEmbedding
  have hXsubMap : X ⊆ X.map emb := by
    intro x hx
    rcases hpre x hx with ⟨y, hyX, hyEq⟩
    exact Finset.mem_map.mpr ⟨y, hyX, hyEq⟩
  have hMapEq : X.map emb = X := by
    symm
    exact Finset.eq_of_subset_of_card_le hXsubMap (by simp)
  have hforward : ∀ x ∈ X, σ x ∈ X := by
    intro x hx
    rw [← hMapEq]
    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩

  have hXnonempty : X.Nonempty := by
    rw [← Finset.card_pos, hXcard]
    omega
  obtain ⟨x₀, hx₀⟩ := hXnonempty
  apply Finset.eq_univ_iff_forall.mpr
  intro z
  have hxmove : σ x₀ ≠ x₀ := by
    exact Equiv.Perm.mem_support.mp (by rw [hσSupport]; simp)
  have hzmove : σ z ≠ z := by
    exact Equiv.Perm.mem_support.mp (by rw [hσSupport]; simp)
  rcases hσcycle.exists_pow_eq hxmove hzmove with ⟨k, hk⟩
  have hpow : (σ ^ k) x₀ ∈ X := by
    clear hk
    induction k with
    | zero => simpa using hx₀
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hforward _ ih
  rwa [hk] at hpow

/-- The cyclic-gap conclusion once an exterior vertex is known. -/
theorem length_eq_of_exterior_vertex {j : ℕ} (C : LongestOddCycle G)
    (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hcount : (oddCycleLengths G).ncard ≤ j) {t : V}
    (ht : t ∈ C.carrierᶜ) : C.length = 2 * j + 1 := by
  classical
  have hNcard : 2 * j + 1 ≤ (neighborIndices C t).card := by
    rw [card_neighborIndices_eq_degree C hind ht]
    exact hdegree t
  rcases Finset.exists_subset_card_eq hNcard with ⟨X, hXsub, hXcard⟩
  have hXuniv := selected_neighbors_eq_univ C ht X hXsub hXcard hcount
  have hcards := congrArg Finset.card hXuniv
  simpa [hXcard] using hcards.symm

/-- Gyárfás's independent-exterior rigidity lemma.  The two-connectedness
hypothesis used by the surrounding structural theorem is not needed in this
branch: the minimum degree, the odd-length count, and independence suffice. -/
theorem independentExteriorRigidity_of_count {j : ℕ} (hj : 0 < j)
    (C : LongestOddCycle G) (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hcount : (oddCycleLengths G).ncard ≤ j) :
    IndependentExteriorRigidity j C := by
  obtain ⟨t, ht⟩ := longestOddCycle_exterior_nonempty hj C hdegree hcount
  have hlength : C.length = 2 * j + 1 :=
    length_eq_of_exterior_vertex C hind hdegree hcount ht
  exact independentExteriorRigidity_of_length hind hlength hdegree

/-- The certificate-free complete-graph endpoint of the independent branch. -/
theorem independent_exterior_forces_complete_of_count {j : ℕ} (hj : 0 < j)
    (C : LongestOddCycle G) (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hcount : (oddCycleLengths G).ncard ≤ j) :
    G = SimpleGraph.completeGraph V := by
  exact independent_exterior_forces_complete_of_rigidity hdegree
    (independentExteriorRigidity_of_count hj C hind hdegree hcount)

/-- Exact-count wrapper matching the hypotheses of the main structural
theorem. -/
theorem independentExteriorRigidity {j : ℕ} (hj : 0 < j)
    (_hG : TwoConnected G) (C : LongestOddCycle G)
    (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) :
    IndependentExteriorRigidity j C :=
  independentExteriorRigidity_of_count hj C hind hdegree hodd.le

/-- Exact-count completeness wrapper matching the main structural theorem. -/
theorem independentExteriorForcesComplete {j : ℕ} (hj : 0 < j)
    (_hG : TwoConnected G) (C : LongestOddCycle G)
    (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) :
    G = SimpleGraph.completeGraph V :=
  independent_exterior_forces_complete_of_count hj C hind hdegree hodd.le

end IndependentGap

end

end Erdos58.Structural
