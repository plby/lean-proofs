/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Disjoint length-four routes from common-neighbour lower bounds. -/

import ErdosProblems.Erdos717.DependentRandomChoice
import ErdosProblems.Erdos717.RouteAssembly

open Function Set
open SimpleGraph

namespace Erdos717

/-- A uniform lower bound on a finite family of sets supplies a system of
distinct representatives.  This is the easy uniform-cardinality corollary of
Hall's theorem. -/
theorem exists_injective_mem_of_fintype_card_le
    {ι α : Type*} [Fintype ι] [DecidableEq α]
    (t : ι → Finset α) (hcard : ∀ i, Fintype.card ι ≤ (t i).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i := by
  classical
  rw [← Finset.all_card_le_biUnion_card_iff_exists_injective]
  intro A
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi⟩ := hA
    calc
      A.card ≤ Fintype.card ι := Finset.card_le_univ A
      _ ≤ (t i).card := hcard i
      _ ≤ (A.biUnion t).card := Finset.card_le_card <|
        Finset.subset_biUnion_of_mem t hi
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

/-- The four-edge walk `u-a-x-b-v`, packaged as a `ShortRoute`. -/
def ShortRoute.ofFour
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S T : Finset V} (hST : Disjoint S T)
    {u v x a b : V}
    (hu : u ∈ S) (hv : v ∈ S) (hx : x ∈ S)
    (ha : a ∈ T) (hb : b ∈ T)
    (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v) (hab : a ≠ b)
    (hua : G.Adj u a) (hax : G.Adj a x)
    (hxb : G.Adj x b) (hbv : G.Adj b v) :
    ShortRoute G u v {a, x, b} := by
  let p : G.Walk u v := ((hax.toWalk.cons hua).concat hxb).concat hbv
  have hsupport : p.support = [u, a, x, b, v] := by
    simp [p, SimpleGraph.Adj.support_toWalk]
  have hua_ne : u ≠ a := fun h =>
    (Finset.disjoint_left.mp hST) hu (h ▸ ha)
  have hub_ne : u ≠ b := fun h =>
    (Finset.disjoint_left.mp hST) hu (h ▸ hb)
  have hva_ne : v ≠ a := fun h =>
    (Finset.disjoint_left.mp hST) hv (h ▸ ha)
  have hvb_ne : v ≠ b := fun h =>
    (Finset.disjoint_left.mp hST) hv (h ▸ hb)
  have hxa_ne : x ≠ a := fun h =>
    (Finset.disjoint_left.mp hST) hx (h ▸ ha)
  have hxb_ne : x ≠ b := fun h =>
    (Finset.disjoint_left.mp hST) hx (h ▸ hb)
  refine {
    path := p
    isPath := ?_
    interior_eq := ?_
  }
  · rw [SimpleGraph.Walk.isPath_def, hsupport]
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.nodup_singleton, not_or, not_false_eq_true, and_true]
    aesop
  · ext z
    simp only [Erdos718.walkInteriorSet, hsupport, List.mem_cons,
      List.mem_singleton, Set.mem_setOf_eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton]
    aesop

/-- For one pair `u,v` on the `S` side of a bipartition, many intermediate
vertices `x` with large codegrees yield a pairwise internally-disjoint family
of length-four routes. -/
theorem exists_short_route_reservoir
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T U Q : Finset V) (u v : V) (L : ℕ)
    (hST : Disjoint S T) (hUS : U ⊆ S) (hQSU : Q ⊆ S \ U)
    (hu : u ∈ U) (hv : v ∈ U) (huv : u ≠ v)
    (hQavoid : ∀ x ∈ Q, x ≠ u ∧ x ≠ v)
    (hcodegLeft : ∀ x ∈ Q, L ≤ (commonNeighborFinset G T u x).card)
    (hcodegRight : ∀ x ∈ Q, L ≤ (commonNeighborFinset G T x v).card)
    (hL : 2 * Q.card ≤ L) :
    ∃ C : Finset (Finset V),
      C.card = Q.card ∧
      (C : Set (Finset V)).Pairwise Disjoint ∧
      (∀ A ∈ C, A.card ≤ 3) ∧
      (∀ A ∈ C, Nonempty (ShortRoute G u v A)) ∧
      (∀ A ∈ C, Disjoint (A : Set V) (U : Set V)) := by
  classical
  let IQ := {x : V // x ∈ Q}
  have hxS (x : IQ) : (x : V) ∈ S :=
    (Finset.mem_sdiff.mp (hQSU x.property)).1
  have hxNotU (x : IQ) : (x : V) ∉ U :=
    (Finset.mem_sdiff.mp (hQSU x.property)).2
  have hIQcard : Fintype.card IQ = Q.card := by simp [IQ]
  let left (x : IQ) := commonNeighborFinset G T u x
  obtain ⟨a, haInj, haMem⟩ := exists_injective_mem_of_fintype_card_le left (by
    intro x
    have hc := hcodegLeft x x.property
    dsimp only [left]
    rw [hIQcard]
    omega)
  let usedA : Finset V := Finset.univ.image a
  have husedAcard : usedA.card = Q.card := by
    rw [Finset.card_image_iff.mpr fun _ _ _ _ h => haInj h]
    simp [IQ, usedA]
  let right (x : IQ) := (commonNeighborFinset G T x v) \ usedA
  have hrightCard (x : IQ) : Q.card ≤ (right x).card := by
    have hdiff := Finset.card_sdiff_add_card_inter
      (commonNeighborFinset G T x v) usedA
    have hinter :
        ((commonNeighborFinset G T x v) ∩ usedA).card ≤ Q.card := by
      rw [← husedAcard]
      exact Finset.card_le_card Finset.inter_subset_right
    have hcodeg := hcodegRight x x.property
    dsimp only [right]
    omega
  obtain ⟨b, hbInj, hbMem⟩ := exists_injective_mem_of_fintype_card_le right (by
    intro x
    simpa [IQ] using hrightCard x)
  let interior (x : IQ) : Finset V := {a x, (x : V), b x}
  let C : Finset (Finset V) := Finset.univ.image interior
  have haT (x : IQ) : a x ∈ T :=
    (mem_commonNeighborFinset G T u x (a x)).mp (haMem x) |>.1
  have hbT (x : IQ) : b x ∈ T := by
    have hx := hbMem x
    exact (mem_commonNeighborFinset G T x v (b x)).mp
      (Finset.mem_sdiff.mp hx).1 |>.1
  have habRange (x : IQ) : b x ∉ usedA := (Finset.mem_sdiff.mp (hbMem x)).2
  have hab (x y : IQ) : a x ≠ b y := by
    intro h
    apply habRange y
    rw [← h]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hinteriorInj : Function.Injective interior := by
    intro x y hxy
    have hxmem : (x : V) ∈ interior x := by simp [interior]
    have hxmem' : (x : V) ∈ interior y := hxy ▸ hxmem
    simp only [interior, Finset.mem_insert, Finset.mem_singleton] at hxmem'
    rcases hxmem' with hxa | hxy | hxb
    · exact (Finset.disjoint_left.mp hST) (hxS x) (hxa ▸ haT y) |>.elim
    · exact Subtype.ext hxy
    · exact (Finset.disjoint_left.mp hST) (hxS x) (hxb ▸ hbT y) |>.elim
  have hCcard : C.card = Q.card := by
    rw [Finset.card_image_iff.mpr fun _ _ _ _ h => hinteriorInj h]
    simp [IQ, C]
  have hpair : (C : Set (Finset V)).Pairwise Disjoint := by
    intro A hAC B hBC hAB
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hAC
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hBC
    have hxy : x ≠ y := fun h => hAB (h ▸ rfl)
    rw [Finset.disjoint_left]
    intro z hzX hzY
    simp only [interior, Finset.mem_insert, Finset.mem_singleton] at hzX hzY
    rcases hzX with hza | hzx | hzb <;>
      rcases hzY with hza' | hzy | hzb'
    · exact hxy (haInj (hza.symm.trans hza'))
    · exact (Finset.disjoint_left.mp hST) (hxS y)
        (hzy ▸ hza ▸ haT x)
    · exact hab x y (hza.symm.trans hzb')
    · exact (Finset.disjoint_left.mp hST) (hxS x)
        (hzx ▸ hza' ▸ haT y)
    · exact hxy (Subtype.ext (hzx.symm.trans hzy))
    · exact (Finset.disjoint_left.mp hST) (hxS x)
        (hzx ▸ hzb' ▸ hbT y)
    · exact hab y x (hza'.symm.trans hzb)
    · exact (Finset.disjoint_left.mp hST) (hxS y)
        (hzy ▸ hzb ▸ hbT x)
    · exact hxy (hbInj (hzb.symm.trans hzb'))
  refine ⟨C, hCcard, hpair, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hA
    dsimp only [interior]
    calc
      Finset.card ({a x, (x : V), b x} : Finset V) ≤
          Finset.card ({(x : V), b x} : Finset V) + 1 :=
        Finset.card_insert_le _ _
      _ ≤ Finset.card ({b x} : Finset V) + 1 + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  · intro A hA
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hA
    have hua := (mem_commonNeighborFinset G T u x (a x)).mp (haMem x) |>.2.1
    have hax := (mem_commonNeighborFinset G T u x (a x)).mp (haMem x) |>.2.2
    have hxb := (mem_commonNeighborFinset G T x v (b x)).mp
      (Finset.mem_sdiff.mp (hbMem x)).1 |>.2.1
    have hbv := (mem_commonNeighborFinset G T x v (b x)).mp
      (Finset.mem_sdiff.mp (hbMem x)).1 |>.2.2
    have habx : a x ≠ b x := hab x x
    exact ⟨ShortRoute.ofFour hST (hUS hu) (hUS hv) (hxS x)
      (haT x) (hbT x) huv (hQavoid x x.property).1
      (hQavoid x x.property).2 habx hua hax.symm hxb hbv.symm⟩
  · intro A hA
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hA
    rw [Finset.disjoint_coe]
    rw [Finset.disjoint_left]
    intro z hz hU
    simp only [interior, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · exact (Finset.disjoint_left.mp hST) (hUS hU) (hz ▸ haT x)
    · exact (hxNotU x) (hz ▸ hU)
    · exact (Finset.disjoint_left.mp hST) (hUS hU) (hz ▸ hbT x)

end Erdos717
