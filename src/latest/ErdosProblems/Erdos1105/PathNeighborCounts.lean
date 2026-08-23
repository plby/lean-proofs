import ErdosProblems.Erdos1105.PosaCrossing
import ErdosProblems.Erdos1105.Disintegration

namespace Erdos1105

open SimpleGraph Finset

theorem degreeWithin_eq_induce_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : (S : Set V)) :
    degreeWithin G S v.val = (G.induce (S : Set V)).degree v := by
  classical
  let e : ↥(S.filter (G.Adj v.val)) ≃ (G.induce (S : Set V)).neighborSet v :=
    { toFun := fun w ↦ ⟨⟨w.val, (mem_filter.mp w.property).1⟩, (mem_filter.mp w.property).2⟩
      invFun := fun w ↦ ⟨w.val.val, mem_filter.mpr ⟨w.val.property, w.property⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← card_neighborSet_eq_degree]
  calc
    degreeWithin G S v.val = (S.filter (G.Adj v.val)).card := by
      unfold degreeWithin
      apply congrArg Finset.card
      ext w
      simp
    _ = _ := by simpa only [Fintype.card_coe] using Fintype.card_congr e

theorem startNeighborIndices_card {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (hp : p.IsPath) :
    (startNeighborIndices p).card = degreeWithin G p.support.toFinset x := by
  classical
  let A := startNeighborIndices p
  have hinj : Set.InjOn (fun i ↦ p.getVert (i + 1)) (A : Set ℕ) := by
    intro i hi j hj heq
    have hiL := mem_range.mp (mem_filter.mp hi).1
    have hjL := mem_range.mp (mem_filter.mp hj).1
    have h := hp.getVert_injOn (show i + 1 ≤ p.length by omega)
      (show j + 1 ≤ p.length by omega) heq
    omega
  have heq : A.image (fun i ↦ p.getVert (i + 1)) = p.support.toFinset.filter (G.Adj x) := by
    ext z
    constructor
    · rintro hz
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _), (mem_filter.mp hi).2⟩
    · rintro hz
      have hzx := (mem_filter.mp hz).2
      obtain ⟨i, hi, hiL⟩ := Walk.mem_support_iff_exists_getVert.mp
        (List.mem_toFinset.mp (mem_filter.mp hz).1)
      have hipos : 0 < i := by
        by_contra h
        have hi0 : i = 0 := by omega
        have hxz : x = z := by simpa only [hi0, Walk.getVert_zero] using hi
        exact hzx.ne hxz
      refine mem_image.mpr ⟨i - 1, ?_, ?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_range.mpr (by omega), ?_⟩
        change G.Adj x (p.getVert (i - 1 + 1))
        rw [Nat.sub_add_cancel hipos, hi]
        exact hzx
      · rw [Nat.sub_add_cancel hipos]
        exact hi
  calc
    A.card = (A.image (fun i ↦ p.getVert (i + 1))).card := (card_image_of_injOn hinj).symm
    _ = _ := by rw [heq]; unfold degreeWithin; congr 1

theorem endNeighborIndices_card {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (hp : p.IsPath) :
    (endNeighborIndices p).card = degreeWithin G p.support.toFinset y := by
  classical
  let B := endNeighborIndices p
  have hinj : Set.InjOn p.getVert (B : Set ℕ) := by
    intro i hi j hj heq
    exact hp.getVert_injOn (mem_range.mp (mem_filter.mp hi).1).le
      (mem_range.mp (mem_filter.mp hj).1).le heq
  have heq : B.image p.getVert = p.support.toFinset.filter (G.Adj y) := by
    ext z
    constructor
    · rintro hz
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _), (mem_filter.mp hi).2⟩
    · rintro hz
      have hzy := (mem_filter.mp hz).2
      obtain ⟨i, hi, hiL⟩ := Walk.mem_support_iff_exists_getVert.mp
        (List.mem_toFinset.mp (mem_filter.mp hz).1)
      have hiLt : i < p.length := by
        by_contra h
        have hieq : i = p.length := by omega
        have hyz : y = z := by simpa only [hieq, Walk.getVert_length] using hi
        exact hzy.ne hyz
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_range.mpr hiLt, hi.symm ▸ hzy⟩, hi⟩
  calc
    B.card = (B.image p.getVert).card := (card_image_of_injOn hinj).symm
    _ = _ := by rw [heq]; unfold degreeWithin; congr 1

end Erdos1105

#print axioms Erdos1105.startNeighborIndices_card
#print axioms Erdos1105.endNeighborIndices_card
