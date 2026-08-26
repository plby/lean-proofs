import ErdosProblems.Erdos118.Imported591.ExactCanonicalSequence

/-! Larson's eleven-segment pattern, with literal box tags. This is a
different graph from the preserved nine-segment negative-six witness. -/

namespace Erdos118.Pentagram

open Negative

structure Split6 (s : List TaggedCoord) where
  p0 : List TaggedCoord
  p1 : List TaggedCoord
  p2 : List TaggedCoord
  p3 : List TaggedCoord
  p4 : List TaggedCoord
  p5 : List TaggedCoord
  eq_append : s = p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5
  ne0 : p0 ≠ []
  ne1 : p1 ≠ []
  ne2 : p2 ≠ []
  ne3 : p3 ≠ []
  ne4 : p4 ≠ []
  ne5 : p5 ≠ []

theorem Split6.mem_cases {s : List TaggedCoord} (P : Split6 s)
    {a : TaggedCoord} (ha : a ∈ s) :
    a ∈ P.p0 ∨ a ∈ P.p1 ∨ a ∈ P.p2 ∨ a ∈ P.p3 ∨ a ∈ P.p4 ∨ a ∈ P.p5 := by
  rw [P.eq_append] at ha
  simp only [List.mem_append] at ha
  aesop

theorem Split6.mem2 {s : List TaggedCoord} (P : Split6 s)
    {a : TaggedCoord} (ha : a ∈ P.p2) : a ∈ s := by
  rw [P.eq_append]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr ha)))

theorem Split6.mem3 {s : List TaggedCoord} (P : Split6 s)
    {a : TaggedCoord} (ha : a ∈ P.p3) : a ∈ s := by
  rw [P.eq_append]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr ha))

structure Witness (x y : List TaggedCoord) where
  X : Split6 x
  Y : Split5 y
  x0_y0 : AllLT X.p0 Y.p0
  y0_x1 : AllLT Y.p0 X.p1
  x1_y1 : AllLT X.p1 Y.p1
  y1_x2 : AllLT Y.p1 X.p2
  x2_y2 : AllLT X.p2 Y.p2
  y2_x3 : AllLT Y.p2 X.p3
  x3_y3 : AllLT X.p3 Y.p3
  y3_x4 : AllLT Y.p3 X.p4
  x4_y4 : AllLT X.p4 Y.p4
  y4_x5 : AllLT Y.p4 X.p5
  box_x0 : HasBox X.p0
  box_x2 : HasBox X.p2
  box_x3 : HasBox X.p3
  box_x5 : HasBox X.p5
  box_y0 : HasBox Y.p0
  box_y4 : HasBox Y.p4
  noBox_x1 : NoBox X.p1
  noBox_x4 : NoBox X.p4
  noBox_y1 : NoBox Y.p1
  noBox_y2 : NoBox Y.p2
  noBox_y3 : NoBox Y.p3

def Witness.blockList {x y : List TaggedCoord} (w : Witness x y) : List SegmentBlock :=
  [⟨w.X.p0, w.X.ne0⟩, ⟨w.Y.p0, w.Y.ne0⟩,
   ⟨w.X.p1, w.X.ne1⟩, ⟨w.Y.p1, w.Y.ne1⟩,
   ⟨w.X.p2, w.X.ne2⟩, ⟨w.Y.p2, w.Y.ne2⟩,
   ⟨w.X.p3, w.X.ne3⟩, ⟨w.Y.p3, w.Y.ne3⟩,
   ⟨w.X.p4, w.X.ne4⟩, ⟨w.Y.p4, w.Y.ne4⟩, ⟨w.X.p5, w.X.ne5⟩]

theorem Witness.blockList_chain {x y : List TaggedCoord} (w : Witness x y) :
    w.blockList.IsChain BlockLT := by
  simp [Witness.blockList, BlockLT, w.x0_y0, w.y0_x1, w.x1_y1, w.y1_x2,
    w.x2_y2, w.y2_x3, w.x3_y3, w.y3_x4, w.x4_y4, w.y4_x5]

def Witness.blockAt {x y : List TaggedCoord} (w : Witness x y) (i : Fin 11) : SegmentBlock :=
  w.blockList.get ⟨i, i.isLt⟩

def Witness.InBlock {x y : List TaggedCoord} (w : Witness x y)
    (a : TaggedCoord) (i : Fin 11) : Prop := a ∈ (w.blockAt i).coords

theorem Witness.blockAt_lt {x y : List TaggedCoord} (w : Witness x y)
    {i j : Fin 11} (hij : i < j) : BlockLT (w.blockAt i) (w.blockAt j) := by
  let ii : Fin w.blockList.length := ⟨i, i.isLt⟩
  let jj : Fin w.blockList.length := ⟨j, j.isLt⟩
  have h : ii < jj := hij
  exact w.blockList_chain.pairwise.rel_get_of_lt h

theorem Witness.index_lt_of_value_lt {x y : List TaggedCoord} (w : Witness x y)
    {a b : TaggedCoord} {i j : Fin 11} (ha : w.InBlock a i) (hb : w.InBlock b j)
    (hab : a.value < b.value) (hij : i ≠ j) : i < j := by
  rcases lt_trichotomy i j with h | h | h
  · exact h
  · exact (hij h).elim
  · exact (hab.not_gt ((w.blockAt_lt h).mem hb ha)).elim

theorem Witness.left_index {x y : List TaggedCoord} (w : Witness x y)
    {a : TaggedCoord} (ha : a ∈ x) : ∃ i : Fin 11, w.InBlock a i ∧ i.val % 2 = 0 := by
  rcases w.X.mem_cases ha with h | h | h | h | h | h
  · exact ⟨0, h, by decide⟩
  · exact ⟨2, h, by decide⟩
  · exact ⟨4, h, by decide⟩
  · exact ⟨6, h, by decide⟩
  · exact ⟨8, h, by decide⟩
  · exact ⟨10, h, by decide⟩

theorem Witness.right_index {x y : List TaggedCoord} (w : Witness x y)
    {a : TaggedCoord} (ha : a ∈ y) : ∃ i : Fin 11, w.InBlock a i ∧ i.val % 2 = 1 := by
  rcases w.Y.mem_cases ha with h | h | h | h | h
  · exact ⟨1, h, by decide⟩
  · exact ⟨3, h, by decide⟩
  · exact ⟨5, h, by decide⟩
  · exact ⟨7, h, by decide⟩
  · exact ⟨9, h, by decide⟩

theorem Witness.firstValue_lt {x y : List TaggedCoord} (w : Witness x y) :
    firstValue x < firstValue y := by
  cases hx : w.X.p0 with
  | nil => exact (w.X.ne0 hx).elim
  | cons a as =>
    cases hy : w.Y.p0 with
    | nil => exact (w.Y.ne0 hy).elim
    | cons b bs =>
      have hab : a.value < b.value := w.x0_y0.mem (by simp [hx]) (by simp [hy])
      simpa [firstValue, w.X.eq_append, w.Y.eq_append, hx, hy] using hab

/-- Larson's alternating-five-coordinate test forces an intervening box. -/
theorem Witness.alternating_box {a b : List TaggedCoord} (w : Witness a b)
    {x r y s z : TaggedCoord} (hx : x ∈ b) (hr : r ∈ a) (hy : y ∈ b)
    (hs : s ∈ a) (hz : z ∈ b) (hxr : x.value < r.value) (hry : r.value < y.value)
    (hys : y.value < s.value) (hsz : s.value < z.value) :
    ∃ f : TaggedCoord, IsBoxCoord a f ∧ x.value < f.value ∧ f.value < z.value := by
  obtain ⟨ix, hix, hixOdd⟩ := w.right_index hx
  obtain ⟨ir, hir, hirEven⟩ := w.left_index hr
  obtain ⟨iy, hiy, hiyOdd⟩ := w.right_index hy
  obtain ⟨is, his, hisEven⟩ := w.left_index hs
  obtain ⟨iz, hiz, hizOdd⟩ := w.right_index hz
  have h₁ : ix < ir := w.index_lt_of_value_lt hix hir hxr (by intro he; subst ir; omega)
  have h₂ : ir < iy := w.index_lt_of_value_lt hir hiy hry (by intro he; subst iy; omega)
  have h₃ : iy < is := w.index_lt_of_value_lt hiy his hys (by intro he; subst is; omega)
  have h₄ : is < iz := w.index_lt_of_value_lt his hiz hsz (by intro he; subst iz; omega)
  have hcases : (ix < (4 : Fin 11) ∧ (4 : Fin 11) < iz) ∨
      (ix < (6 : Fin 11) ∧ (6 : Fin 11) < iz) := by
    omega
  rcases hcases with h | h
  · obtain ⟨f, hf, hbox⟩ := w.box_x2
    exact ⟨f, ⟨w.X.mem2 hf, hbox⟩,
      (w.blockAt_lt h.1).mem hix hf, (w.blockAt_lt h.2).mem hf hiz⟩
  · obtain ⟨f, hf, hbox⟩ := w.box_x3
    exact ⟨f, ⟨w.X.mem3 hf, hbox⟩,
      (w.blockAt_lt h.1).mem hix hf, (w.blockAt_lt h.2).mem hf hiz⟩

def graphOf {V : Type*} (seq : V → List TaggedCoord) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦ Nonempty (Witness (seq x) (seq y))

theorem graphOf_adj {V : Type*} (seq : V → List TaggedCoord) (x y : V) :
    (graphOf seq).Adj x y ↔ x ≠ y ∧
      (Nonempty (Witness (seq x) (seq y)) ∨ Nonempty (Witness (seq y) (seq x))) :=
  SimpleGraph.fromRel_adj _ _ _

/-- The literal sharper coloring. Its five-clique exclusion is proved separately. -/
def graph : SimpleGraph Negative.Exact.G := graphOf Negative.Exact.sequence

end Erdos118.Pentagram
