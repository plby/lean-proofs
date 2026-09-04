/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos58.Structural.BoundaryApplication
import ErdosProblems.Erdos58.Linkage
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# The escape path in the one-chord boundary case at `j = 1`

When the two endpoints of the longest exterior path have a unique common
neighbour `x` on the longest odd cycle, the `j = 1` argument deletes `x`.
Two-connectivity then supplies a path from the rest of the cycle to the
exterior path.  This file constructs the exact cleaned path used in the
eight-order argument: its endpoints lie on the cycle and exterior path,
respectively, while its interior meets neither.
-/

namespace Erdos58.Structural.K1Boundary

open Set SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path escaping from the longest cycle to the exterior path after the
unique common cycle neighbour `x` has been deleted. -/
structure EscapePath (C : EndpointCount.LongestOddCycle G)
    (S : ExteriorPath C) (x : V) where
  cycleEnd : V
  exteriorEnd : V
  path : G.Walk cycleEnd exteriorEnd
  isPath : path.IsPath
  cycleEnd_mem : cycleEnd ∈ C.cycle.support
  exteriorEnd_mem : exteriorEnd ∈ S.walk.support
  avoids_deleted : x ∉ path.support
  interior_avoids_cycle :
    ∀ v ∈ path.support.tail.dropLast, v ∉ C.cycle.support
  interior_avoids_exterior :
    ∀ v ∈ path.support.tail.dropLast, v ∉ S.walk.support

namespace EscapePath

variable {C : EndpointCount.LongestOddCycle G} {S : ExteriorPath C} {x : V}

lemma cycleEnd_ne_exteriorEnd (P : EscapePath C S x) :
    P.cycleEnd ≠ P.exteriorEnd := by
  intro h
  exact S.avoids_cycle P.exteriorEnd_mem (h ▸ P.cycleEnd_mem)

lemma positive (P : EscapePath C S x) : 0 < P.path.length := by
  exact Nat.pos_of_ne_zero fun hzero ↦
    P.cycleEnd_ne_exteriorEnd
      (P.isPath.nil_iff_eq.mp (SimpleGraph.Walk.length_eq_zero_iff.mp hzero))

lemma cycleEnd_ne_deleted (P : EscapePath C S x) : P.cycleEnd ≠ x := by
  intro h
  have hxmem : x ∈ P.path.support := by
    simpa only [h] using P.path.start_mem_support
  exact P.avoids_deleted hxmem

lemma exteriorEnd_not_cycle (P : EscapePath C S x) :
    P.exteriorEnd ∉ C.cycle.support :=
  S.avoids_cycle P.exteriorEnd_mem

private lemma mem_interior_of_mem_support_of_ne_ends
    {a b v : V} {p : G.Walk a b} (hp : p.IsPath)
    (hv : v ∈ p.support) (hva : v ≠ a) (hvb : v ≠ b) :
    v ∈ p.support.tail.dropLast := by
  have htail : v ∈ p.support.tail := by
    rw [← p.cons_tail_support] at hv
    exact (List.mem_cons.mp hv).resolve_left hva
  apply List.mem_dropLast_of_mem_of_ne_getLast htail
  simpa [Walk.getLast_support] using hvb

/-- The cleaning conditions imply that the cycle meets the escape path only
at its first endpoint. -/
lemma cycle_inter_support (P : EscapePath C S x) {v : V}
    (hvP : v ∈ P.path.support) (hvC : v ∈ C.cycle.support) :
    v = P.cycleEnd := by
  by_contra hne
  have hvz : v ≠ P.exteriorEnd := fun h ↦
    P.exteriorEnd_not_cycle (h ▸ hvC)
  exact P.interior_avoids_cycle v
    (mem_interior_of_mem_support_of_ne_ends P.isPath hvP hne hvz) hvC

/-- The exterior path meets the cleaned escape path only at its last
endpoint. -/
lemma exterior_inter_support (P : EscapePath C S x) {v : V}
    (hvP : v ∈ P.path.support) (hvS : v ∈ S.walk.support) :
    v = P.exteriorEnd := by
  by_contra hne
  have hvy : v ≠ P.cycleEnd := fun h ↦
    S.avoids_cycle hvS (h ▸ P.cycleEnd_mem)
  exact P.interior_avoids_exterior v
    (mem_interior_of_mem_support_of_ne_ends P.isPath hvP hvy hne) hvS

/-- Close an actual route in the chorded exterior path with the actual
cleaned escape path and an actual path on the longest cycle.  The support
hypothesis says precisely that the route uses only the deleted cycle vertex
and vertices of `S`.  All simplicity/disjointness obligations are discharged
here, so the finite path-order analysis only has to construct routes. -/
theorem cycleAtLength_of_route
    (P : EscapePath C S x) (hxC : x ∈ C.cycle.support)
    (R : G.Walk P.exteriorEnd x) (hR : R.IsPath)
    (hRsupport : ∀ v ∈ R.support, v = x ∨ v ∈ S.walk.support)
    (Q : G.Walk x P.cycleEnd) (hQ : Q.IsPath)
    (hQsupport : ∀ v ∈ Q.support, v ∈ C.cycle.support) :
    CycleAtLength G (Q.length + P.path.length + R.length) := by
  classical
  have hRpos : 0 < R.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hzx : P.exteriorEnd = x :=
      hR.nil_iff_eq.mp (Walk.length_eq_zero_iff.mp hzero)
    exact P.exteriorEnd_not_cycle (hzx.symm ▸ hxC)
  let T : G.Walk P.cycleEnd x := P.path.append R
  have hP_R_disj : P.path.support.Disjoint R.support.tail := by
    intro v hvP hvR
    have hvR' : v ∈ R.support := List.mem_of_mem_tail hvR
    rcases hRsupport v hvR' with rfl | hvS
    · exact P.avoids_deleted hvP
    · have hvz : v = P.exteriorEnd := P.exterior_inter_support hvP hvS
      subst v
      have hnot : P.exteriorEnd ∉ R.support.tail := by
        have hn := hR.support_nodup
        rw [← R.cons_tail_support] at hn
        exact (List.nodup_cons.mp hn).1
      exact hnot hvR
  have hT : T.IsPath := by
    simp only [T, Walk.isPath_def, Walk.support_append]
    exact P.isPath.support_nodup.append hR.support_nodup.tail hP_R_disj
  have hQT : Q.support.tail.Disjoint T.support.tail := by
    have hx_not_Qtail : x ∉ Q.support.tail := by
      have hn := hQ.support_nodup
      rw [← Q.cons_tail_support] at hn
      exact (List.nodup_cons.mp hn).1
    intro v hvQ hvT
    have hvQ' : v ∈ Q.support := List.mem_of_mem_tail hvQ
    have hvT' : v ∈ T.support := List.mem_of_mem_tail hvT
    have hvC : v ∈ C.cycle.support := hQsupport v hvQ'
    change v ∈ (P.path.append R).support at hvT'
    rw [Walk.support_append, List.mem_append] at hvT'
    rcases hvT' with hvP | hvR
    · have hvy : v = P.cycleEnd := P.cycle_inter_support hvP hvC
      subst v
      have hnot : P.cycleEnd ∉ T.support.tail := by
        have hn := hT.support_nodup
        rw [← T.cons_tail_support] at hn
        exact (List.nodup_cons.mp hn).1
      exact hnot hvT
    · have hvR' : v ∈ R.support := List.mem_of_mem_tail hvR
      rcases hRsupport v hvR' with rfl | hvS
      · exact hx_not_Qtail hvQ
      · exact S.avoids_cycle hvS hvC
  refine ⟨x, Q.append T, hQ.isCycle_append hT hQT ?_, ?_⟩
  · right
    simp only [T, Walk.length_append]
    have hPpos := P.positive
    omega
  · simp [T, Walk.length_append, Nat.add_assoc]

private lemma odd_replace_of_even_sum {a r s : ℕ}
    (ha : Odd (a + r)) (hrs : Even (r + s)) : Odd (a + s) := by
  grind

/-- Two actual exterior routes of the same parity and different lengths
give two different odd cycle lengths.  The same one of the two complementary
`x`--`cycleEnd` arcs is used for both routes. -/
theorem two_odd_lengths_of_routes [Finite V]
    (P : EscapePath C S x) (hxC : x ∈ C.cycle.support)
    (R₁ R₂ : G.Walk P.exteriorEnd x)
    (hR₁ : R₁.IsPath) (hR₂ : R₂.IsPath)
    (hR₁support : ∀ v ∈ R₁.support, v = x ∨ v ∈ S.walk.support)
    (hR₂support : ∀ v ∈ R₂.support, v = x ∨ v ∈ S.walk.support)
    (hsame : Even (R₁.length + R₂.length))
    (hne : R₁.length ≠ R₂.length) :
    2 ≤ (oddCycleLengths G).ncard := by
  classical
  let c : G.Walk x x := C.cycle.rotate x hxC
  have hc : c.IsCycle := C.isCycle.rotate hxC
  have hyc : P.cycleEnd ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hxC).mpr P.cycleEnd_mem
  let Q₁ : G.Walk x P.cycleEnd := c.takeUntil P.cycleEnd hyc
  let Qback : G.Walk P.cycleEnd x := c.dropUntil P.cycleEnd hyc
  let Q₂ : G.Walk x P.cycleEnd := Qback.reverse
  have hQ₁ : Q₁.IsPath := hc.isPath_takeUntil hyc
  have hQ₁nonempty : ¬Q₁.Nil := by
    intro hnil
    exact P.cycleEnd_ne_deleted
      ((c.nil_takeUntil hyc).mp hnil).symm
  have hQback : Qback.IsPath := by
    exact Walk.IsCycle.isPath_of_append_right hQ₁nonempty (by
      simpa only [Q₁, Qback, c.take_spec hyc] using hc)
  have hQ₂ : Q₂.IsPath := hQback.reverse
  have hQ₁support : ∀ v ∈ Q₁.support, v ∈ C.cycle.support := by
    intro v hv
    exact (C.cycle.mem_support_rotate_iff x hxC).mp
      (c.support_takeUntil_subset_support hyc hv)
  have hQ₂support : ∀ v ∈ Q₂.support, v ∈ C.cycle.support := by
    intro v hv
    apply (C.cycle.mem_support_rotate_iff x hxC).mp
    apply c.support_dropUntil_subset_support hyc
    simpa [Q₂, Qback, Walk.support_reverse] using hv
  have hQsum : Q₁.length + Q₂.length = C.cycle.length := by
    calc
      Q₁.length + Q₂.length = (Q₁.append Qback).length := by
        simp [Q₂, Walk.length_append]
      _ = c.length := congrArg Walk.length (c.take_spec hyc)
      _ = C.cycle.length := by simp [c]
  let a₁ := Q₁.length + P.path.length
  let a₂ := Q₂.length + P.path.length
  have hchoice :
      (Odd (a₁ + R₁.length) ∧ Odd (a₁ + R₂.length) ∧
        CycleAtLength G (a₁ + R₁.length) ∧
        CycleAtLength G (a₁ + R₂.length)) ∨
      (Odd (a₂ + R₁.length) ∧ Odd (a₂ + R₂.length) ∧
        CycleAtLength G (a₂ + R₁.length) ∧
        CycleAtLength G (a₂ + R₂.length)) := by
    rcases Nat.even_or_odd (a₁ + R₁.length) with heven | hodd
    · right
      have hodd' : Odd (a₂ + R₁.length) := by
        have hN := C.odd_length
        dsimp [a₁, a₂] at heven ⊢
        grind
      refine ⟨hodd', odd_replace_of_even_sum hodd' hsame, ?_, ?_⟩
      · exact P.cycleAtLength_of_route hxC R₁ hR₁ hR₁support
          Q₂ hQ₂ hQ₂support
      · exact P.cycleAtLength_of_route hxC R₂ hR₂ hR₂support
          Q₂ hQ₂ hQ₂support
    · left
      refine ⟨hodd, odd_replace_of_even_sum hodd hsame, ?_, ?_⟩
      · exact P.cycleAtLength_of_route hxC R₁ hR₁ hR₁support
          Q₁ hQ₁ hQ₁support
      · exact P.cycleAtLength_of_route hxC R₂ hR₂ hR₂support
          Q₁ hQ₁ hQ₁support
  rcases hchoice with ⟨ho₁, ho₂, hc₁, hc₂⟩ | ⟨ho₁, ho₂, hc₁, hc₂⟩
  · let f : Fin 2 → ℕ := fun i ↦ if i = 0 then a₁ + R₁.length
      else a₁ + R₂.length
    apply ncard_oddCycleLengths_ge_of_injective (G := G) f
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, zero_ne_one] at hij ⊢
      · have hsum : a₁ + R₁.length = a₁ + R₂.length := by
          simpa [f] using hij
        exact (hne (Nat.add_left_cancel hsum)).elim
      · have hsum : a₁ + R₁.length = a₁ + R₂.length := by
          simpa [f] using hij.symm
        exact (hne (Nat.add_left_cancel hsum)).elim
    · intro i
      fin_cases i <;> simp [f, ho₁, ho₂]
    · intro i
      fin_cases i
      · simpa [f] using hc₁
      · simpa [f] using hc₂
  · let f : Fin 2 → ℕ := fun i ↦ if i = 0 then a₂ + R₁.length
      else a₂ + R₂.length
    apply ncard_oddCycleLengths_ge_of_injective (G := G) f
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, zero_ne_one] at hij ⊢
      · have hsum : a₂ + R₁.length = a₂ + R₂.length := by
          simpa [f] using hij
        exact (hne (Nat.add_left_cancel hsum)).elim
      · have hsum : a₂ + R₁.length = a₂ + R₂.length := by
          simpa [f] using hij.symm
        exact (hne (Nat.add_left_cancel hsum)).elim
    · intro i
      fin_cases i <;> simp [f, ho₁, ho₂]
    · intro i
      fin_cases i
      · simpa [f] using hc₁
      · simpa [f] using hc₂

end EscapePath

/-! ## Actual subpaths and endpoint routes on `S` -/

/-- The forward segment of the actual exterior path between two ordered
positions. -/
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
    (ExteriorPath.segment S i j hij).length = j - i := by
  simp only [ExteriorPath.segment, Walk.length_copy,
    Walk.take_length, Walk.drop_length]
  have hi : (i : ℕ) ≤ S.walk.length := by omega
  have hj : (j : ℕ) ≤ S.walk.length := by omega
  omega

lemma ExteriorPath.segment_isPath
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j) :
    (ExteriorPath.segment S i j hij).IsPath := by
  rw [ExteriorPath.segment, Walk.isPath_copy]
  exact (S.isPath.drop i).take _

lemma ExteriorPath.segment_support_subset
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j) :
    ∀ v ∈ (ExteriorPath.segment S i j hij).support, v ∈ S.walk.support := by
  intro v hv
  rw [ExteriorPath.segment, Walk.support_copy, Walk.support_take] at hv
  have hvdrop : v ∈ (S.walk.drop i).support := List.mem_of_mem_take hv
  rw [Walk.drop_support_eq_support_drop_min] at hvdrop
  exact List.mem_of_mem_drop hvdrop

/-- Two segments lying on opposite sides of a strict cut in a simple path
have disjoint supports (after removing the common path start from the lower
segment).  This is the only list-order fact needed by the final exceptional
route. -/
private lemma ExteriorPath.segment_disjoint_lower_tail
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (b c a : Fin (S.walk.length + 1)) (hca : c ≤ a) (hbc : b < c) :
    (ExteriorPath.segment S c a hca).support.Disjoint
      (ExteriorPath.segment S 0 b (Fin.zero_le b)).support.tail := by
  have hcut := List.disjoint_take_drop S.isPath.support_nodup
    (show (b : ℕ) + 1 ≤ c by omega)
  intro v hvhigh hvlow
  apply hcut
  · have hvlow' : v ∈ (ExteriorPath.segment S 0 b (Fin.zero_le b)).support :=
      List.mem_of_mem_tail hvlow
    rw [ExteriorPath.segment, Walk.support_copy, Walk.support_take,
      Walk.drop_support_eq_support_drop_min] at hvlow'
    simp only [Fin.val_zero, Nat.min_eq_left (Nat.zero_le _), List.drop_zero] at hvlow'
    exact (List.take_isPrefix_take.mpr (Or.inl (by omega))).subset hvlow'
  · rw [ExteriorPath.segment, Walk.support_copy, Walk.support_take] at hvhigh
    have hvdrop : v ∈ (S.walk.drop c).support := List.mem_of_mem_take hvhigh
    rw [Walk.drop_support_eq_support_drop_min] at hvdrop
    have hcle : (c : ℕ) ≤ S.walk.length := by omega
    simpa [Nat.min_eq_left hcle] using hvdrop

private lemma ExteriorPath.left_not_mem_segment_of_pos
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j) (hi : 0 < (i : ℕ)) :
    S.left ∉ (ExteriorPath.segment S i j hij).support := by
  intro hleft
  rw [ExteriorPath.segment, Walk.support_copy, Walk.support_take] at hleft
  have hdrop : S.left ∈ (S.walk.drop i).support :=
    List.mem_of_mem_take hleft
  have hi_le : (i : ℕ) ≤ S.walk.length := by
    have := i.isLt
    omega
  rw [Walk.drop_support_eq_support_drop_min,
    Nat.min_eq_left hi_le, ← S.walk.cons_tail_support] at hdrop
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (i : ℕ) ≠ 0)
  rw [hn] at hdrop
  simp only [List.drop_succ_cons] at hdrop
  have hn := S.isPath.support_nodup
  rw [← S.walk.cons_tail_support] at hn
  exact hn.notMem (List.mem_of_mem_drop hdrop)

private lemma ExteriorPath.right_not_mem_segment_of_lt
    {C : EndpointCount.LongestOddCycle G} (S : ExteriorPath C)
    (i j : Fin (S.walk.length + 1)) (hij : i ≤ j)
    (hj : (j : ℕ) < S.walk.length) :
    S.right ∉ (ExteriorPath.segment S i j hij).support := by
  intro hright
  rw [ExteriorPath.segment, Walk.support_copy, Walk.support_take,
    Walk.drop_support_eq_support_drop_min] at hright
  have hi_le : (i : ℕ) ≤ S.walk.length := by
    have := i.isLt
    omega
  rw [Nat.min_eq_left hi_le] at hright
  have hsum : (i : ℕ) + ((j : ℕ) - i + 1) = j + 1 := by omega
  have htake : S.right ∈ S.walk.support.take ((j : ℕ) + 1) := by
    rw [← hsum, List.take_add, List.mem_append]
    exact Or.inr hright
  have hmem : S.right ∈ S.walk.support := List.mem_of_mem_take htake
  have hidx : S.walk.support.idxOf S.right < (j : ℕ) + 1 :=
    (List.mem_take_iff_idxOf_lt hmem).mp htake
  have hdrop : S.right ∈ S.walk.support.dropLast := by
    apply (List.mem_dropLast_iff_idxOf_lt hmem).mpr
    rw [Walk.length_support]
    omega
  have hne := S.isPath.support_nodup.rel_dropLast_getLast hdrop
  exact hne (by simpa [Walk.getLast_support])

private theorem cycleAtLength_of_path_edge
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (huv : G.Adj u v) (htwo : 1 < p.length) :
    CycleAtLength G (p.length + 1) := by
  let w : G.Walk u u := Walk.cons huv p.reverse
  have hw : w.IsCycle := by
    change (Walk.cons huv p.reverse).IsCycle
    rw [Walk.cons_isCycle_iff]
    refine ⟨hp.reverse, ?_⟩
    intro he
    have he' : s(u, v) ∈ p.edges := by
      simpa [Walk.edges_reverse] using he
    exact (Nat.ne_of_gt htwo) (hp.length_eq_one_of_mem_edges he')
  exact ⟨u, w, hw, by simp [w]⟩

/-- A vertex on the longest cycle adjacent to both ends of an exterior
path closes that exterior path to an actual simple cycle. -/
private theorem commonNeighborExteriorCycle
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C) (x : V)
    (hxC : x ∈ C.cycle.support)
    (hleft : G.Adj S.left x) (hright : G.Adj S.right x) :
    CycleAtLength G (S.walk.length + 2) := by
  classical
  have hxOutside : x ∉ S.walk.support := fun hx ↦ S.avoids_cycle hx hxC
  have hleft_ne_right : S.left ≠ S.right := by
    intro h
    have hnil : S.walk.Nil := S.isPath.nil_iff_eq.mpr h
    exact (Nat.ne_of_gt S.positive) hnil.length_eq_zero
  have hright_ne_x : S.right ≠ x := fun h ↦
    S.avoids_cycle S.walk.end_mem_support (h ▸ hxC)
  let base : G.Walk x x := Walk.cons hleft.symm (S.walk.concat hright)
  have hbase : base.IsCycle := by
    dsimp [base]
    rw [Walk.cons_isCycle_iff]
    constructor
    · exact S.isPath.concat hxOutside hright
    · intro he
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
      simp only [List.mem_singleton] at he
      rcases he with he | he
      · exact hxOutside (S.walk.fst_mem_support_of_mem_edges he)
      · rw [Sym2.eq_iff] at he
        rcases he with ⟨hxr, -⟩ | ⟨-, hLR⟩
        · exact hright_ne_x hxr.symm
        · exact hleft_ne_right hLR
  exact ⟨x, base, hbase, by simp [base]⟩

/-- The left endpoint chord itself cuts off an actual cycle. -/
theorem leftChordCycle
    {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C) (a : Fin (S.walk.length + 1))
    (ha : a ∈ leftChordPositions S) :
    CycleAtLength G ((a : ℕ) + 1) := by
  classical
  have ha' : 1 < (a : ℕ) ∧ G.Adj S.left (S.walk.getVert a) := by
    simpa [leftChordPositions] using ha
  have hpos : 1 < (a : ℕ) := ha'.1
  have hadj : G.Adj S.left (S.walk.getVert a) := ha'.2
  let z : Fin (S.walk.length + 1) := ⟨0, by omega⟩
  have hz : S.walk.getVert z = S.left := by simp [z]
  let p : G.Walk S.left (S.walk.getVert a) :=
    (ExteriorPath.segment S z a (by simp [z])).copy hz rfl
  have hp : p.IsPath := by
    change ((ExteriorPath.segment S z a _).copy hz rfl).IsPath
    rw [Walk.isPath_copy]
    exact ExteriorPath.segment_isPath S z a _
  have hlen : p.length = a := by
    simp [p, ExteriorPath.segment, z]
    have ha_le := a.isLt
    omega
  apply hlen ▸ cycleAtLength_of_path_edge p hp hadj
  omega

/-- The selected right endpoint chord cuts off an actual cycle. -/
theorem rightChordCycle
    {C : EndpointCount.LongestOddCycle G}
    (S : ExteriorPath C) (b : Fin (S.walk.length + 1))
    (hb : b ∈ rightChordPositions S) :
    CycleAtLength G (S.walk.length - b + 1) := by
  classical
  have hb' : (b : ℕ) + 1 < S.walk.length ∧
      G.Adj S.right (S.walk.getVert b) := by
    simpa [rightChordPositions] using hb
  have hpos : (b : ℕ) + 1 < S.walk.length := hb'.1
  have hbadj : G.Adj S.right (S.walk.getVert b) := hb'.2
  let e : Fin (S.walk.length + 1) := ⟨S.walk.length, by omega⟩
  have he : S.walk.getVert e = S.right := by simp [e]
  let p : G.Walk S.right (S.walk.getVert b) :=
    (ExteriorPath.segment S b e (by
      apply Fin.le_iff_val_le_val.mpr
      dsimp [e]
      omega)).reverse.copy he rfl
  have hp : p.IsPath := by
    change ((ExteriorPath.segment S b e _).reverse.copy he rfl).IsPath
    rw [Walk.isPath_copy]
    exact (ExteriorPath.segment_isPath S b e _).reverse
  have hlen : p.length = S.walk.length - b := by
    simp [p, ExteriorPath.segment, e]
  have htwo : 1 < p.length := by omega
  simpa [hlen] using cycleAtLength_of_path_edge p hp hbadj htwo

/-- The two direct routes from a marked vertex of `S` to the deleted cycle
vertex, one through each endpoint of `S`. -/
theorem EscapePath.exists_direct_routes
    {C : EndpointCount.LongestOddCycle G} {S : ExteriorPath C} {x : V}
    (P : EscapePath C S x) (hxC : x ∈ C.cycle.support)
    (c : Fin (S.walk.length + 1))
    (hc : S.walk.getVert c = P.exteriorEnd)
    (hleft : G.Adj S.left x) (hright : G.Adj S.right x) :
    ∃ (Rleft Rright : G.Walk P.exteriorEnd x),
      Rleft.IsPath ∧ Rright.IsPath ∧
      (∀ v ∈ Rleft.support, v = x ∨ v ∈ S.walk.support) ∧
      (∀ v ∈ Rright.support, v = x ∨ v ∈ S.walk.support) ∧
      Rleft.length = (c : ℕ) + 1 ∧
      Rright.length = S.walk.length - c + 1 := by
  classical
  let z₀ : Fin (S.walk.length + 1) := ⟨0, by omega⟩
  let zL : Fin (S.walk.length + 1) := ⟨S.walk.length, by omega⟩
  have hzero : S.walk.getVert z₀ = S.left := by simp [z₀]
  have hlast : S.walk.getVert zL = S.right := by simp [zL]
  let pleft : G.Walk S.left P.exteriorEnd :=
    (ExteriorPath.segment S z₀ c (by simp [z₀])).copy hzero hc
  let pright : G.Walk P.exteriorEnd S.right :=
    (ExteriorPath.segment S c zL (by
      apply Fin.le_iff_val_le_val.mpr
      dsimp [zL]
      have hc' := c.isLt
      omega)).copy hc rfl |>.copy rfl hlast
  let Rleft : G.Walk P.exteriorEnd x := pleft.reverse.concat hleft
  let Rright : G.Walk P.exteriorEnd x := pright.concat hright
  have hpleft : pleft.IsPath := by
    simp only [pleft, Walk.isPath_copy]
    exact ExteriorPath.segment_isPath S z₀ c _
  have hpright : pright.IsPath := by
    simp only [pright, Walk.isPath_copy]
    exact ExteriorPath.segment_isPath S c zL _
  have hx_left : x ∉ pleft.support := by
    intro hx
    apply S.avoids_cycle _ hxC
    apply ExteriorPath.segment_support_subset S z₀ c _
    simpa [pleft] using hx
  have hx_right : x ∉ pright.support := by
    intro hx
    apply S.avoids_cycle _ hxC
    apply ExteriorPath.segment_support_subset S c zL _
    simpa [pright] using hx
  have hRl : Rleft.IsPath := hpleft.reverse.concat (by
    simpa [Walk.support_reverse] using hx_left) hleft
  have hRr : Rright.IsPath := hpright.concat hx_right hright
  refine ⟨Rleft, Rright, hRl, hRr, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Rleft, Walk.support_concat, Walk.support_reverse,
      List.mem_append, List.mem_reverse, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · right
      apply ExteriorPath.segment_support_subset S z₀ c _
      simpa [pleft] using hv
    · exact Or.inl rfl
  · intro v hv
    simp only [Rright, Walk.support_concat, List.mem_append,
      List.mem_singleton] at hv
    rcases hv with hv | rfl
    · right
      apply ExteriorPath.segment_support_subset S c zL _
      simpa [pright] using hv
    · exact Or.inl rfl
  · simp [Rleft, pleft, ExteriorPath.segment, z₀]
    have hc' := c.isLt
    omega
  · simp [Rright, pright, ExteriorPath.segment, zL]

/-- The route from the marked exterior vertex to `x` which first reaches
the left chord endpoint, takes that chord back to `S.left`, and then uses
the edge `S.left-x`. -/
theorem EscapePath.exists_left_chord_route
    {C : EndpointCount.LongestOddCycle G} {S : ExteriorPath C} {x : V}
    (P : EscapePath C S x) (hxC : x ∈ C.cycle.support)
    (c a : Fin (S.walk.length + 1))
    (hc : S.walk.getVert c = P.exteriorEnd)
    (hcpos : 0 < (c : ℕ))
    (ha : a ∈ leftChordPositions S)
    (hleft : G.Adj S.left x) :
    ∃ R : G.Walk P.exteriorEnd x,
      R.IsPath ∧
      (∀ v ∈ R.support, v = x ∨ v ∈ S.walk.support) ∧
      R.length = Nat.dist (a : ℕ) c + 2 := by
  classical
  have ha' : 1 < (a : ℕ) ∧ G.Adj S.left (S.walk.getVert a) := by
    simpa [leftChordPositions] using ha
  have hapos : 0 < (a : ℕ) := by omega
  have hadj : G.Adj S.left (S.walk.getVert a) := ha'.2
  have hleft_mem : S.left ∈ S.walk.support := S.walk.start_mem_support
  have hx_not_S : x ∉ S.walk.support := fun hx ↦ S.avoids_cycle hx hxC
  by_cases hca : c ≤ a
  · let p : G.Walk P.exteriorEnd (S.walk.getVert a) :=
      (ExteriorPath.segment S c a hca).copy hc rfl
    have hp : p.IsPath := by
      simp only [p, Walk.isPath_copy]
      exact ExteriorPath.segment_isPath S c a hca
    have hleft_not : S.left ∉ p.support := by
      simpa [p] using
        ExteriorPath.left_not_mem_segment_of_pos S c a hca hcpos
    let q : G.Walk P.exteriorEnd S.left := p.concat hadj.symm
    have hq : q.IsPath := hp.concat hleft_not hadj.symm
    have hx_not_q : x ∉ q.support := by
      intro hx
      simp only [q, Walk.support_concat, List.mem_append,
        List.mem_singleton] at hx
      rcases hx with hx | hx
      · apply hx_not_S
        apply ExteriorPath.segment_support_subset S c a hca
        simpa [p] using hx
      · exact S.avoids_cycle S.walk.start_mem_support (hx ▸ hxC)
    let R : G.Walk P.exteriorEnd x := q.concat hleft
    have hR : R.IsPath := hq.concat hx_not_q hleft
    refine ⟨R, hR, ?_, ?_⟩
    · intro v hv
      simp only [R, q, Walk.support_concat, Walk.support_concat,
        List.mem_append, List.mem_singleton] at hv
      rcases hv with (hv | rfl) | rfl
      · right
        apply ExteriorPath.segment_support_subset S c a hca
        simpa [p] using hv
      · exact Or.inr hleft_mem
      · exact Or.inl rfl
    · rw [Nat.dist_eq_sub_of_le_right (show (c : ℕ) ≤ a by exact hca)]
      simp [R, q, p, ExteriorPath.segment]
      omega

  · have hac : a ≤ c := by omega
    let p : G.Walk P.exteriorEnd (S.walk.getVert a) :=
      (ExteriorPath.segment S a c hac).reverse.copy hc rfl
    have hp : p.IsPath := by
      simp only [p, Walk.isPath_copy]
      exact (ExteriorPath.segment_isPath S a c hac).reverse
    have hleft_not : S.left ∉ p.support := by
      simpa [p, Walk.support_reverse] using
        ExteriorPath.left_not_mem_segment_of_pos S a c hac hapos
    let q : G.Walk P.exteriorEnd S.left := p.concat hadj.symm
    have hq : q.IsPath := hp.concat hleft_not hadj.symm
    have hx_not_q : x ∉ q.support := by
      intro hx
      simp only [q, Walk.support_concat, List.mem_append,
        List.mem_singleton] at hx
      rcases hx with hx | hx
      · apply hx_not_S
        apply ExteriorPath.segment_support_subset S a c hac
        simpa [p, Walk.support_reverse] using hx
      · exact S.avoids_cycle S.walk.start_mem_support (hx ▸ hxC)
    let R : G.Walk P.exteriorEnd x := q.concat hleft
    have hR : R.IsPath := hq.concat hx_not_q hleft
    refine ⟨R, hR, ?_, ?_⟩
    · intro v hv
      simp only [R, q, Walk.support_concat, Walk.support_concat,
        List.mem_append, List.mem_singleton] at hv
      rcases hv with (hv | rfl) | rfl
      · right
        apply ExteriorPath.segment_support_subset S a c hac
        simpa [p, Walk.support_reverse] using hv
      · exact Or.inr hleft_mem
      · exact Or.inl rfl
    · rw [Nat.dist_eq_sub_of_le (show (a : ℕ) ≤ c by exact hac)]
      simp [R, q, p, ExteriorPath.segment]
      omega


/-- Symmetric route through a selected right endpoint chord. -/
theorem EscapePath.exists_right_chord_route
    {C : EndpointCount.LongestOddCycle G} {S : ExteriorPath C} {x : V}
    (P : EscapePath C S x) (hxC : x ∈ C.cycle.support)
    (c b : Fin (S.walk.length + 1))
    (hc : S.walk.getVert c = P.exteriorEnd)
    (hclt : (c : ℕ) < S.walk.length)
    (hb : b ∈ rightChordPositions S)
    (hright : G.Adj S.right x) :
    ∃ R : G.Walk P.exteriorEnd x,
      R.IsPath ∧
      (∀ v ∈ R.support, v = x ∨ v ∈ S.walk.support) ∧
      R.length = Nat.dist (b : ℕ) c + 2 := by
  classical
  have hb' : (b : ℕ) + 1 < S.walk.length ∧
      G.Adj S.right (S.walk.getVert b) := by
    simpa [rightChordPositions] using hb
  have hblt : (b : ℕ) < S.walk.length := by omega
  have hadj : G.Adj S.right (S.walk.getVert b) := hb'.2
  have hright_mem : S.right ∈ S.walk.support := S.walk.end_mem_support
  have hx_not_S : x ∉ S.walk.support := fun hx ↦ S.avoids_cycle hx hxC
  by_cases hcb : c ≤ b
  · let p : G.Walk P.exteriorEnd (S.walk.getVert b) :=
      (ExteriorPath.segment S c b hcb).copy hc rfl
    have hp : p.IsPath := by
      simp only [p, Walk.isPath_copy]
      exact ExteriorPath.segment_isPath S c b hcb
    have hright_not : S.right ∉ p.support := by
      simpa [p] using
        ExteriorPath.right_not_mem_segment_of_lt S c b hcb hblt
    let q : G.Walk P.exteriorEnd S.right := p.concat hadj.symm
    have hq : q.IsPath := hp.concat hright_not hadj.symm
    have hx_not_q : x ∉ q.support := by
      intro hx
      simp only [q, Walk.support_concat, List.mem_append,
        List.mem_singleton] at hx
      rcases hx with hx | hx
      · apply hx_not_S
        apply ExteriorPath.segment_support_subset S c b hcb
        simpa [p] using hx
      · exact S.avoids_cycle S.walk.end_mem_support (hx ▸ hxC)
    let R : G.Walk P.exteriorEnd x := q.concat hright
    have hR : R.IsPath := hq.concat hx_not_q hright
    refine ⟨R, hR, ?_, ?_⟩
    · intro v hv
      simp only [R, q, Walk.support_concat, Walk.support_concat,
        List.mem_append, List.mem_singleton] at hv
      rcases hv with (hv | rfl) | rfl
      · right
        apply ExteriorPath.segment_support_subset S c b hcb
        simpa [p] using hv
      · exact Or.inr hright_mem
      · exact Or.inl rfl
    · rw [Nat.dist_eq_sub_of_le_right (show (c : ℕ) ≤ b by exact hcb)]
      simp [R, q, p, ExteriorPath.segment]
      omega
  · have hbc : b ≤ c := by omega
    let p : G.Walk P.exteriorEnd (S.walk.getVert b) :=
      (ExteriorPath.segment S b c hbc).reverse.copy hc rfl
    have hp : p.IsPath := by
      simp only [p, Walk.isPath_copy]
      exact (ExteriorPath.segment_isPath S b c hbc).reverse
    have hright_not : S.right ∉ p.support := by
      simpa [p, Walk.support_reverse] using
        ExteriorPath.right_not_mem_segment_of_lt S b c hbc hclt
    let q : G.Walk P.exteriorEnd S.right := p.concat hadj.symm
    have hq : q.IsPath := hp.concat hright_not hadj.symm
    have hx_not_q : x ∉ q.support := by
      intro hx
      simp only [q, Walk.support_concat, List.mem_append,
        List.mem_singleton] at hx
      rcases hx with hx | hx
      · apply hx_not_S
        apply ExteriorPath.segment_support_subset S b c hbc
        simpa [p, Walk.support_reverse] using hx
      · exact S.avoids_cycle S.walk.end_mem_support (hx ▸ hxC)
    let R : G.Walk P.exteriorEnd x := q.concat hright
    have hR : R.IsPath := hq.concat hx_not_q hright
    refine ⟨R, hR, ?_, ?_⟩
    · intro v hv
      simp only [R, q, Walk.support_concat, Walk.support_concat,
        List.mem_append, List.mem_singleton] at hv
      rcases hv with (hv | rfl) | rfl
      · right
        apply ExteriorPath.segment_support_subset S b c hbc
        simpa [p, Walk.support_reverse] using hv
      · exact Or.inr hright_mem
      · exact Or.inl rfl
    · rw [Nat.dist_eq_sub_of_le (show (b : ℕ) ≤ c by exact hbc)]
      simp [R, q, p, ExteriorPath.segment]
      omega

/-- In the sole order left after the parity cases, the escape point lies
strictly between a right-chord endpoint `b` and a left-chord endpoint `a`.
The route goes forward from the escape point to `a`, takes the left chord,
follows the low initial segment to `b`, takes the right chord, and finally
uses `S.right-x`.  The two path segments are disjoint because `b < c ≤ a`.
-/
theorem EscapePath.exists_cross_chord_route
    {C : EndpointCount.LongestOddCycle G} {S : ExteriorPath C} {x : V}
    (P : EscapePath C S x) (hxC : x ∈ C.cycle.support)
    (c a b : Fin (S.walk.length + 1))
    (hc : S.walk.getVert c = P.exteriorEnd)
    (hbc : b < c) (hca : c ≤ a) (halt : (a : ℕ) < S.walk.length)
    (ha : a ∈ leftChordPositions S)
    (hb : b ∈ rightChordPositions S)
    (hright : G.Adj S.right x) :
    ∃ R : G.Walk P.exteriorEnd x,
      R.IsPath ∧
      (∀ v ∈ R.support, v = x ∨ v ∈ S.walk.support) ∧
      R.length = (a : ℕ) - c + b + 3 := by
  classical
  have ha' : 1 < (a : ℕ) ∧ G.Adj S.left (S.walk.getVert a) := by
    simpa [leftChordPositions] using ha
  have hb' : (b : ℕ) + 1 < S.walk.length ∧
      G.Adj S.right (S.walk.getVert b) := by
    simpa [rightChordPositions] using hb
  have hleft_ne_right : S.left ≠ S.right := by
    intro heq
    have hnil : S.walk.Nil := S.isPath.nil_iff_eq.mpr heq
    have hzero := Walk.length_eq_zero_iff.mpr hnil
    omega
  let pHigh : G.Walk P.exteriorEnd (S.walk.getVert a) :=
    (ExteriorPath.segment S c a hca).copy hc rfl
  let qHigh : G.Walk P.exteriorEnd S.left := pHigh.concat ha'.2.symm
  let pLow : G.Walk S.left (S.walk.getVert b) :=
    (ExteriorPath.segment S 0 b (Fin.zero_le b)).copy (by simp) rfl
  let q : G.Walk P.exteriorEnd (S.walk.getVert b) := qHigh.append pLow
  let t : G.Walk P.exteriorEnd S.right := q.concat hb'.2.symm
  let R : G.Walk P.exteriorEnd x := t.concat hright
  have hpHigh : pHigh.IsPath := by
    simp only [pHigh, Walk.isPath_copy]
    exact ExteriorPath.segment_isPath S c a hca
  have hleft_not_high : S.left ∉ pHigh.support := by
    simpa [pHigh] using ExteriorPath.left_not_mem_segment_of_pos
      S c a hca (by omega)
  have hqHigh : qHigh.IsPath := hpHigh.concat hleft_not_high ha'.2.symm
  have hpLow : pLow.IsPath := by
    simp only [pLow, Walk.isPath_copy]
    exact ExteriorPath.segment_isPath S 0 b (Fin.zero_le b)
  have hhigh_low : pHigh.support.Disjoint pLow.support.tail := by
    simpa only [pHigh, pLow, Walk.support_copy] using
      ExteriorPath.segment_disjoint_lower_tail S b c a hca hbc
  have hleft_not_low_tail : S.left ∉ pLow.support.tail := by
    have hn := hpLow.support_nodup
    rw [← pLow.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hq_disj : qHigh.support.Disjoint pLow.support.tail := by
    intro v hvq hvlow
    simp only [qHigh, Walk.support_concat, List.mem_append,
      List.mem_singleton] at hvq
    rcases hvq with hvhigh | rfl
    · exact hhigh_low hvhigh hvlow
    · exact hleft_not_low_tail hvlow
  have hq : q.IsPath := by
    rw [Walk.isPath_def]
    change (qHigh.append pLow).support.Nodup
    rw [Walk.support_append]
    exact hqHigh.support_nodup.append hpLow.support_nodup.tail hq_disj
  have hright_not_q : S.right ∉ q.support := by
    intro hv
    change S.right ∈ (qHigh.append pLow).support at hv
    rw [Walk.support_append, List.mem_append] at hv
    rcases hv with hvhigh | hvlow
    · simp only [qHigh, Walk.support_concat, List.mem_append,
        List.mem_singleton] at hvhigh
      rcases hvhigh with hvhigh | hvleft
      · have hnot := ExteriorPath.right_not_mem_segment_of_lt
          S c a hca halt
        apply hnot
        simpa [pHigh] using hvhigh
      · exact hleft_ne_right hvleft.symm
    · have hnot := ExteriorPath.right_not_mem_segment_of_lt
        S 0 b (Fin.zero_le b) (by omega)
      apply hnot
      exact List.mem_of_mem_tail (by
        simpa only [pLow, Walk.support_copy] using hvlow)
  have ht : t.IsPath := hq.concat hright_not_q hb'.2.symm
  have hx_not_t : x ∉ t.support := by
    intro hx
    apply S.avoids_cycle ?_ hxC
    simp only [t, q, qHigh, Walk.support_concat, Walk.support_append,
      List.mem_append, List.mem_singleton] at hx ⊢
    rcases hx with (hvhigh | hvlow) | rfl
    · rcases hvhigh with hvhigh | rfl
      · apply ExteriorPath.segment_support_subset S c a hca
        simpa [pHigh] using hvhigh
      · exact S.walk.start_mem_support
    · apply ExteriorPath.segment_support_subset S 0 b (Fin.zero_le b)
      exact List.mem_of_mem_tail (by
        simpa only [pLow, Walk.support_copy] using hvlow)
    · exact S.walk.end_mem_support
  have hR : R.IsPath := ht.concat hx_not_t hright
  refine ⟨R, hR, ?_, ?_⟩
  · intro v hv
    simp only [R, t, q, qHigh, Walk.support_concat, Walk.support_append,
      List.mem_append, List.mem_singleton] at hv
    rcases hv with ((hvhigh | hvlow) | rfl) | rfl
    · rcases hvhigh with hvhigh | rfl
      · right
        apply ExteriorPath.segment_support_subset S c a hca
        simpa [pHigh] using hvhigh
      · exact Or.inr S.walk.start_mem_support
    · right
      apply ExteriorPath.segment_support_subset S 0 b (Fin.zero_le b)
      exact List.mem_of_mem_tail (by
        simpa only [pLow, Walk.support_copy] using hvlow)
    · exact Or.inr S.walk.end_mem_support
    · exact Or.inl rfl
  · have hpHighlen : pHigh.length = (a : ℕ) - c := by
      simp [pHigh, ExteriorPath.segment_length]
    have hpLowlen : pLow.length = (b : ℕ) := by
      simp only [pLow, Walk.length_copy]
      simpa using ExteriorPath.segment_length S (0 : Fin (S.walk.length + 1))
        b (Fin.zero_le b)
    simp [R, t, q, qHigh, hpHighlen, hpLowlen]
    omega

private theorem two_odd_lengths_of_cycle_ne_longest [Finite V]
    (C : EndpointCount.LongestOddCycle G) {n : ℕ}
    (hnodd : Odd n) (hncycle : CycleAtLength G n)
    (hne : n ≠ C.cycle.length) :
    2 ≤ (oddCycleLengths G).ncard := by
  let f : Fin 2 → ℕ := fun i ↦ if i = 0 then C.cycle.length else n
  have hCcycle : CycleAtLength G C.cycle.length :=
    ⟨C.base, C.cycle, C.isCycle, rfl⟩
  apply ncard_oddCycleLengths_ge_of_injective (G := G) f
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, zero_ne_one] at hij ⊢
    · exact (hne hij.symm).elim
    · exact (hne hij).elim
  · intro i
    fin_cases i
    · simpa [f] using C.odd_length
    · simpa [f] using hnodd
  · intro i
    fin_cases i
    · simpa [f] using hCcycle
    · simpa [f] using hncycle

/-- Opposite-parity routes must use complementary arcs of the odd cycle.
If their total exterior contribution is too large, the two resulting odd
cycles cannot both be bounded by the chosen longest odd cycle. -/
theorem EscapePath.not_opposite_routes_of_long
    {C : EndpointCount.LongestOddCycle G} {S : ExteriorPath C} {x : V}
    (P : EscapePath C S x) (hxC : x ∈ C.cycle.support)
    (R₁ R₂ : G.Walk P.exteriorEnd x)
    (hR₁ : R₁.IsPath) (hR₂ : R₂.IsPath)
    (hR₁support : ∀ v ∈ R₁.support, v = x ∨ v ∈ S.walk.support)
    (hR₂support : ∀ v ∈ R₂.support, v = x ∨ v ∈ S.walk.support)
    (hopposite : Odd (R₁.length + R₂.length))
    (hlong : C.cycle.length <
      2 * P.path.length + R₁.length + R₂.length) : False := by
  classical
  let c : G.Walk x x := C.cycle.rotate x hxC
  have hc : c.IsCycle := C.isCycle.rotate hxC
  have hyc : P.cycleEnd ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hxC).mpr P.cycleEnd_mem
  let Q₁ : G.Walk x P.cycleEnd := c.takeUntil P.cycleEnd hyc
  let Qback : G.Walk P.cycleEnd x := c.dropUntil P.cycleEnd hyc
  let Q₂ : G.Walk x P.cycleEnd := Qback.reverse
  have hQ₁ : Q₁.IsPath := hc.isPath_takeUntil hyc
  have hQ₁nonempty : ¬Q₁.Nil := by
    intro hnil
    exact P.cycleEnd_ne_deleted ((c.nil_takeUntil hyc).mp hnil).symm
  have hQback : Qback.IsPath :=
    Walk.IsCycle.isPath_of_append_right hQ₁nonempty (by
      simpa only [Q₁, Qback, c.take_spec hyc] using hc)
  have hQ₂ : Q₂.IsPath := hQback.reverse
  have hQ₁support : ∀ v ∈ Q₁.support, v ∈ C.cycle.support := by
    intro v hv
    exact (C.cycle.mem_support_rotate_iff x hxC).mp
      (c.support_takeUntil_subset_support hyc hv)
  have hQ₂support : ∀ v ∈ Q₂.support, v ∈ C.cycle.support := by
    intro v hv
    apply (C.cycle.mem_support_rotate_iff x hxC).mp
    apply c.support_dropUntil_subset_support hyc
    simpa [Q₂, Qback, Walk.support_reverse] using hv
  have hQsum : Q₁.length + Q₂.length = C.cycle.length := by
    calc
      Q₁.length + Q₂.length = (Q₁.append Qback).length := by
        simp [Q₂, Walk.length_append]
      _ = c.length := congrArg Walk.length (c.take_spec hyc)
      _ = C.cycle.length := by simp [c]
  let a₁ := Q₁.length + P.path.length
  let a₂ := Q₂.length + P.path.length
  have hCodd := C.odd_length
  have hpair : ∃ n₁ n₂,
      Odd n₁ ∧ Odd n₂ ∧ CycleAtLength G n₁ ∧ CycleAtLength G n₂ ∧
      n₁ + n₂ = C.cycle.length +
        2 * P.path.length + R₁.length + R₂.length := by
    rcases Nat.even_or_odd (a₁ + R₁.length) with heven | hodd
    · refine ⟨a₂ + R₁.length, a₁ + R₂.length, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp [a₁, a₂] at heven ⊢
        grind
      · dsimp [a₁] at heven ⊢
        grind
      · exact P.cycleAtLength_of_route hxC R₁ hR₁ hR₁support
          Q₂ hQ₂ hQ₂support
      · exact P.cycleAtLength_of_route hxC R₂ hR₂ hR₂support
          Q₁ hQ₁ hQ₁support
      · dsimp [a₁, a₂]
        omega
    · refine ⟨a₁ + R₁.length, a₂ + R₂.length, hodd, ?_, ?_, ?_, ?_⟩
      · dsimp [a₁, a₂] at hodd ⊢
        grind
      · exact P.cycleAtLength_of_route hxC R₁ hR₁ hR₁support
          Q₁ hQ₁ hQ₁support
      · exact P.cycleAtLength_of_route hxC R₂ hR₂ hR₂support
          Q₂ hQ₂ hQ₂support
      · dsimp [a₁, a₂]
        omega
  obtain ⟨n₁, n₂, hn₁, hn₂, hc₁, hc₂, hsum⟩ := hpair
  have hn₁mem := hc₁.mem_oddCycleLengths hn₁
  have hn₂mem := hc₂.mem_oddCycleLengths hn₂
  have hle₁ := C.longest hn₁mem
  have hle₂ := C.longest hn₂mem
  omega

/-- Clean a path whose first endpoint is on `C` and whose last endpoint is
on `S`: stop at the first visit to `S`, then discard everything before the
last visit to `C`. -/
private theorem clean_path
    (C : EndpointCount.LongestOddCycle G) (S : ExteriorPath C) {x y : V}
    (p : G.Walk y S.left) (hp : p.IsPath)
    (hyC : y ∈ C.cycle.support) (hxavoid : x ∉ p.support) :
    Nonempty (EscapePath C S x) := by
  classical
  let cycleVertices : Finset V := C.cycle.support.toFinset
  let exteriorVertices : Finset V := S.walk.support.toFinset
  have hExteriorMeet :
      {v ∈ exteriorVertices | v ∈ p.support}.Nonempty := by
    refine ⟨S.left, ?_⟩
    simp [exteriorVertices]
  obtain ⟨z, hzS, hzp, hfirstS⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq
      exteriorVertices hExteriorMeet
  let pS : G.Walk y z := p.takeUntil z hzp
  have hy_pS : y ∈ pS.support := pS.start_mem_support
  have hCycleMeet :
      {v ∈ cycleVertices | v ∈ pS.reverse.support}.Nonempty := by
    refine ⟨y, ?_⟩
    simp [cycleVertices, hyC, hy_pS]
  obtain ⟨y', hy'C, hy'pr, hfirstC⟩ :=
    pS.reverse.exists_mem_support_forall_mem_support_imp_eq
      cycleVertices hCycleMeet
  let r₀ : G.Walk z y' := pS.reverse.takeUntil y' hy'pr
  let r : G.Walk y' z := r₀.reverse
  have hpS : pS.IsPath := hp.takeUntil hzp
  have hr₀ : r₀.IsPath := hpS.reverse.takeUntil hy'pr
  have hr : r.IsPath := hr₀.reverse
  have hr₀_sub : r₀.support ⊆ pS.reverse.support :=
    pS.reverse.support_takeUntil_subset_support hy'pr
  have hpS_sub : pS.support ⊆ p.support :=
    p.support_takeUntil_subset_support hzp
  have hr_sub : r.support ⊆ p.support := by
    intro v hv
    have hv₀ : v ∈ r₀.support := by simpa [r] using hv
    have hvpr : v ∈ pS.reverse.support := hr₀_sub hv₀
    have hvpS : v ∈ pS.support := by simpa using hvpr
    exact hpS_sub hvpS
  refine ⟨{
    cycleEnd := y'
    exteriorEnd := z
    path := r
    isPath := hr
    cycleEnd_mem := by simpa [cycleVertices] using hy'C
    exteriorEnd_mem := by simpa [exteriorVertices] using hzS
    avoids_deleted := fun hx ↦ hxavoid (hr_sub hx)
    interior_avoids_cycle := ?_
    interior_avoids_exterior := ?_ }⟩
  · intro v hvint hvC
    have hvtail : v ∈ r.support.tail := List.mem_of_mem_dropLast hvint
    have hv_ne_start : v ≠ y' := by
      have hne := hr.support_nodup.rel_head_tail hvtail
      simpa using hne.symm
    have hv₀ : v ∈ r₀.support := by
      have hvr : v ∈ r.support := List.mem_of_mem_tail hvtail
      simpa [r] using hvr
    have hy'eq := hfirstC v (by simpa [cycleVertices] using hvC) hv₀
    exact hv_ne_start hy'eq
  · intro v hvint hvS
    have hvdrop : v ∈ r.support.dropLast := by
      apply List.mem_of_mem_tail
      rw [List.tail_dropLast]
      exact hvint
    have hvtail : v ∈ r.support.tail := List.mem_of_mem_dropLast hvint
    have hv_ne_end : v ≠ z := by
      have hne := hr.support_nodup.rel_dropLast_getLast hvdrop
      simpa using hne
    have hv₀ : v ∈ r₀.support := by
      have hvr : v ∈ r.support := List.mem_of_mem_tail hvtail
      simpa [r] using hvr
    have hvpr : v ∈ pS.reverse.support := hr₀_sub hv₀
    have hvpS : v ∈ pS.support := by simpa using hvpr
    have hzeq := hfirstS v (by simpa [exteriorVertices] using hvS) hvpS
    exact hv_ne_end hzeq

/-- The cleaned escape path required in the omitted `j = 1` part of
Gyárfás's one-chord boundary lemma. -/
theorem TwoConnected.exists_escapePath
    (hG : TwoConnected G) (C : EndpointCount.LongestOddCycle G)
    (S : ExteriorPath C) {x : V} (hxC : x ∈ C.cycle.support) :
    Nonempty (EscapePath C S x) := by
  classical
  let c : G.Walk x x := C.cycle.rotate x hxC
  have hc : c.IsCycle := C.isCycle.rotate hxC
  have hc_notNil : ¬c.Nil := hc.not_nil
  let y : V := c.snd
  have hxyAdj : G.Adj x y := c.adj_snd hc_notNil
  have hyC : y ∈ C.cycle.support := by
    apply (C.cycle.mem_support_rotate_iff x hxC).mp
    exact List.mem_of_mem_tail (c.snd_mem_tail_support hc_notNil)
  have hleft_ne_x : S.left ≠ x := by
    intro h
    exact S.avoids_cycle S.walk.start_mem_support (h ▸ hxC)
  obtain ⟨p, hp, hxavoid⟩ :=
    hG.exists_path_avoiding x hxyAdj.ne.symm hleft_ne_x
  exact clean_path C S p hp hyC hxavoid

/-- In the `j = 1` one-chord configuration, the endpoint count supplies a
literal singleton common neighbourhood on the cycle.  Deleting its unique
vertex and applying two-connectivity gives the cleaned escape path, while
the two endpoint-chord hypotheses supply actual marked chord positions.

This is the complete geometric input to the remaining finite order check:
no path, cycle, or cycle-length witness is assumed. -/
theorem OneChordEachConfiguration.exists_marked_escapePath
    (hG : TwoConnected G) (C : EndpointCount.LongestOddCycle G)
    (D : OneChordEachConfiguration C 1) :
    ∃ (i : Fin C.cycle.length)
      (a b : Fin (D.exterior.walk.length + 1)),
      cycleNeighborPositions C D.exterior.left = {i} ∧
      cycleNeighborPositions C D.exterior.right = {i} ∧
      a ∈ leftChordPositions D.exterior ∧
      b ∈ rightChordPositions D.exterior ∧
      Nonempty
        (EscapePath C D.exterior (C.cycle.getVert i)) := by
  classical
  have hcard :
      (cycleNeighborPositions C D.exterior.left).card = 1 := by
    simpa using D.cycle_neighbor_card
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have haleft : 0 < (leftChordPositions D.exterior).card := by
    rw [D.left_chord_card]
    exact Nat.zero_lt_one
  obtain ⟨a, ha⟩ := Finset.card_pos.mp haleft
  obtain ⟨b, hb⟩ := D.right_chord_nonempty
  refine ⟨i, a, b, hi, ?_, ha, hb, ?_⟩
  · rw [← D.same_neighbors]
    exact hi
  · apply TwoConnected.exists_escapePath hG C D.exterior
    exact C.cycle.getVert_mem_support i

/-- The geometric core of the `j = 1` singleton-neighbour boundary case.
Only existence, rather than uniqueness, of an endpoint chord on each side is
used.  Thus the theorem also applies when the exterior endpoint has several
path chords.  All cycles are built from actual walks. -/
theorem singletonChordBoundary_one_of_twoConnected [Finite V]
    (hG : TwoConnected G) (C : EndpointCount.LongestOddCycle G)
    (S : ExteriorPath C)
    (hsame : cycleNeighborPositions C S.left =
      cycleNeighborPositions C S.right)
    (hsingleton : (cycleNeighborPositions C S.left).card = 1)
    (hleftChord : (leftChordPositions S).Nonempty)
    (hrightChord : (rightChordPositions S).Nonempty) :
    2 ≤ (oddCycleLengths G).ncard := by
  classical
  obtain ⟨i, hiLset⟩ := Finset.card_eq_one.mp hsingleton
  have hiRset : cycleNeighborPositions C S.right = {i} := by
    rw [← hsame]
    exact hiLset
  obtain ⟨a, ha⟩ := hleftChord
  obtain ⟨b, hb⟩ := hrightChord
  let x := C.cycle.getVert i
  have hxC : x ∈ C.cycle.support := C.cycle.getVert_mem_support i
  obtain ⟨P⟩ := TwoConnected.exists_escapePath hG C S hxC
  have hiL : i ∈ cycleNeighborPositions C S.left := by
    rw [hiLset]
    simp
  have hiR : i ∈ cycleNeighborPositions C S.right := by
    rw [hiRset]
    simp
  have hleft : G.Adj S.left x :=
    (mem_cycleNeighborPositions C S.left i).mp hiL
  have hright : G.Adj S.right x :=
    (mem_cycleNeighborPositions C S.right i).mp hiR
  obtain ⟨cn, hcn, hcnle⟩ :=
    Walk.mem_support_iff_exists_getVert.mp P.exteriorEnd_mem
  have hcnleS : cn ≤ S.walk.length := hcnle
  let c : Fin (S.walk.length + 1) := ⟨cn, by omega⟩
  have hc : S.walk.getVert c = P.exteriorEnd := by
    simpa [c] using hcn
  have haNum : 1 < (a : ℕ) := (mem_leftChordPositions S a).mp ha |>.1
  have hbNum : (b : ℕ) + 1 < S.walk.length :=
    (mem_rightChordPositions S b).mp hb |>.1
  obtain ⟨Rleft, Rright, hRleft, hRright, hRleftSupport,
      hRrightSupport, hRleftLen, hRrightLen⟩ :=
    P.exists_direct_routes hxC c hc hleft hright
  rcases Nat.even_or_odd S.walk.length with hLeven | hLodd
  · have hDirectSame : Even (Rleft.length + Rright.length) := by
      rw [hRleftLen, hRrightLen]
      grind
    by_cases hDirectNe : Rleft.length ≠ Rright.length
    · exact P.two_odd_lengths_of_routes hxC Rleft Rright
        hRleft hRright hRleftSupport hRrightSupport hDirectSame hDirectNe
    · have hmid : 2 * (c : ℕ) = S.walk.length := by
        have heq : Rleft.length = Rright.length := not_ne_iff.mp hDirectNe
        rw [hRleftLen, hRrightLen] at heq
        have hcLe : (c : ℕ) ≤ S.walk.length := by omega
        omega
      have hcpos : 0 < (c : ℕ) := by omega
      have hclt : (c : ℕ) < S.walk.length := by omega
      obtain ⟨RchordL, hRchordL, hRchordLSupport, hRchordLLen⟩ :=
        P.exists_left_chord_route hxC c a hc hcpos ha hleft
      rcases Nat.even_or_odd (a : ℕ) with haEven | haOdd
      · have hleftCycle := leftChordCycle S a ha
        have hleftOdd : Odd ((a : ℕ) + 1) := by grind
        by_cases hleftNe : (a : ℕ) + 1 ≠ C.cycle.length
        · exact two_odd_lengths_of_cycle_ne_longest C hleftOdd
            hleftCycle hleftNe
        · have hopposite : Odd (Rleft.length + RchordL.length) := by
            rw [hRleftLen, hRchordLLen]
            rcases le_total (a : ℕ) c with hac | hca
            · rw [Nat.dist_eq_sub_of_le hac]
              grind
            · rw [Nat.dist_eq_sub_of_le_right hca]
              grind
          have hlong : C.cycle.length <
              2 * P.path.length + Rleft.length + RchordL.length := by
            rw [hRleftLen, hRchordLLen]
            have hPpos := P.positive
            rcases le_total (a : ℕ) c with hac | hca
            · rw [Nat.dist_eq_sub_of_le hac]
              omega
            · rw [Nat.dist_eq_sub_of_le_right hca]
              omega
          exact (P.not_opposite_routes_of_long hxC Rleft RchordL
            hRleft hRchordL hRleftSupport hRchordLSupport
            hopposite hlong).elim
      · have hLeftSame : Even (Rleft.length + RchordL.length) := by
          rw [hRleftLen, hRchordLLen]
          rcases le_total (a : ℕ) c with hac | hca
          · rw [Nat.dist_eq_sub_of_le hac]
            grind
          · rw [Nat.dist_eq_sub_of_le_right hca]
            grind
        by_cases hLeftNe : Rleft.length ≠ RchordL.length
        · exact P.two_odd_lengths_of_routes hxC Rleft RchordL
            hRleft hRchordL hRleftSupport hRchordLSupport
            hLeftSame hLeftNe
        · have haLast : (a : ℕ) = S.walk.length - 1 := by
            rw [hRleftLen, hRchordLLen] at hLeftNe
            rcases le_total (a : ℕ) c with hac | hca
            · rw [Nat.dist_eq_sub_of_le hac] at hLeftNe
              omega
            · rw [Nat.dist_eq_sub_of_le_right hca] at hLeftNe
              omega
          obtain ⟨RchordR, hRchordR, hRchordRSupport, hRchordRLen⟩ :=
            P.exists_right_chord_route hxC c b hc hclt hb hright
          rcases Nat.even_or_odd (b : ℕ) with hbEven | hbOdd
          · have hrightCycle := rightChordCycle S b hb
            have hrightOdd : Odd (S.walk.length - (b : ℕ) + 1) := by
              grind
            by_cases hrightNe :
                S.walk.length - (b : ℕ) + 1 ≠ C.cycle.length
            · exact two_odd_lengths_of_cycle_ne_longest C hrightOdd
                hrightCycle hrightNe
            · have hopposite : Odd (Rleft.length + RchordR.length) := by
                rw [hRleftLen, hRchordRLen]
                rcases le_total (b : ℕ) c with hbc | hcb
                · rw [Nat.dist_eq_sub_of_le hbc]
                  grind
                · rw [Nat.dist_eq_sub_of_le_right hcb]
                  grind
              have hlong : C.cycle.length <
                  2 * P.path.length + Rleft.length + RchordR.length := by
                rw [hRleftLen, hRchordRLen]
                have hPpos := P.positive
                rcases le_total (b : ℕ) c with hbc | hcb
                · rw [Nat.dist_eq_sub_of_le hbc]
                  omega
                · rw [Nat.dist_eq_sub_of_le_right hcb]
                  omega
              exact (P.not_opposite_routes_of_long hxC Rleft RchordR
                hRleft hRchordR hRleftSupport hRchordRSupport
                hopposite hlong).elim
          · have hRightSame : Even (Rleft.length + RchordR.length) := by
              rw [hRleftLen, hRchordRLen]
              rcases le_total (b : ℕ) c with hbc | hcb
              · rw [Nat.dist_eq_sub_of_le hbc]
                grind
              · rw [Nat.dist_eq_sub_of_le_right hcb]
                grind
            by_cases hRightNe : Rleft.length ≠ RchordR.length
            · exact P.two_odd_lengths_of_routes hxC Rleft RchordR
                hRleft hRchordR hRleftSupport hRchordRSupport
                hRightSame hRightNe
            · have hbFirst : (b : ℕ) = 1 := by
                rw [hRleftLen, hRchordRLen] at hRightNe
                rcases le_total (b : ℕ) c with hbc | hcb
                · rw [Nat.dist_eq_sub_of_le hbc] at hRightNe
                  omega
                · rw [Nat.dist_eq_sub_of_le_right hcb] at hRightNe
                  omega
              have hbc : b < c := Fin.lt_iff_val_lt_val.mpr (by omega)
              have hca : c ≤ a := Fin.le_iff_val_le_val.mpr (by omega)
              have halt : (a : ℕ) < S.walk.length := by omega
              obtain ⟨Rcross, hRcross, hRcrossSupport, hRcrossLen⟩ :=
                P.exists_cross_chord_route hxC c a b hc hbc hca halt
                  ha hb hright
              have hCrossSame : Even (Rleft.length + Rcross.length) := by
                rw [hRleftLen, hRcrossLen]
                grind
              have hCrossNe : Rleft.length ≠ Rcross.length := by
                rw [hRleftLen, hRcrossLen]
                omega
              exact P.two_odd_lengths_of_routes hxC Rleft Rcross
                hRleft hRcross hRleftSupport hRcrossSupport
                hCrossSame hCrossNe
  · have hbaseCycle := commonNeighborExteriorCycle C S x hxC hleft hright
    have hbaseOdd : Odd (S.walk.length + 2) := by grind
    by_cases hbaseNe : S.walk.length + 2 ≠ C.cycle.length
    · exact two_odd_lengths_of_cycle_ne_longest C hbaseOdd hbaseCycle hbaseNe
    · have hopposite : Odd (Rleft.length + Rright.length) := by
        rw [hRleftLen, hRrightLen]
        grind
      have hlong : C.cycle.length <
          2 * P.path.length + Rleft.length + Rright.length := by
        have hbaseEq : S.walk.length + 2 = C.cycle.length :=
          not_ne_iff.mp hbaseNe
        rw [hRleftLen, hRrightLen]
        have hPpos := P.positive
        omega
      exact (P.not_opposite_routes_of_long hxC Rleft Rright
        hRleft hRright hRleftSupport hRrightSupport
        hopposite hlong).elim

/-- The original one-chord configuration is an immediate instance of the
more general singleton-neighbour theorem above. -/
theorem oneChordEachBoundary_one_of_twoConnected [Finite V]
    (hG : TwoConnected G) (C : EndpointCount.LongestOddCycle G)
    (D : OneChordEachConfiguration C 1) :
    2 ≤ (oddCycleLengths G).ncard := by
  have hleftChord : (leftChordPositions D.exterior).Nonempty := by
    apply Finset.card_pos.mp
    rw [D.left_chord_card]
    exact Nat.zero_lt_one
  apply singletonChordBoundary_one_of_twoConnected hG C D.exterior
    D.same_neighbors
  · simpa using D.cycle_neighbor_card
  · exact hleftChord
  · exact D.right_chord_nonempty

end

end Erdos58.Structural.K1Boundary
