import ErdosProblems.Erdos118.PentagramPattern

/-! Intrinsic boxed cores and the finite segment geometry of Larson edges. -/

namespace Erdos118.Pentagram

open Negative

theorem Split6.mem0 {s : List TaggedCoord} (P : Split6 s)
    {a : TaggedCoord} (ha : a ∈ P.p0) : a ∈ s := by
  rw [P.eq_append]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ha))))

theorem Split6.mem1 {s : List TaggedCoord} (P : Split6 s)
    {a : TaggedCoord} (ha : a ∈ P.p1) : a ∈ s := by
  rw [P.eq_append]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ha))))

theorem Split6.mem4 {s : List TaggedCoord} (P : Split6 s)
    {a : TaggedCoord} (ha : a ∈ P.p4) : a ∈ s := by
  rw [P.eq_append]
  simp only [List.mem_append]
  exact Or.inl (Or.inr ha)

theorem Split6.mem5 {s : List TaggedCoord} (P : Split6 s)
    {a : TaggedCoord} (ha : a ∈ P.p5) : a ∈ s := by
  rw [P.eq_append]
  simp only [List.mem_append]
  exact Or.inr ha

/-- The boxed core is defined from the two words, independently of a witness. -/
def Core (x y : List TaggedCoord) : Set TaggedCoord :=
  {q | IsBoxCoord x q ∧ Inside y q}

theorem inside_between {s : List TaggedCoord} {a q b : TaggedCoord}
    (ha : Inside s a) (hb : Inside s b) (haq : a.value < q.value)
    (hqb : q.value < b.value) : Inside s q := by
  obtain ⟨lo, hlo, _, _, hloa, _⟩ := ha
  obtain ⟨_, _, hi, hhi, _, hbhi⟩ := hb
  exact ⟨lo, hlo, hi, hhi, hloa.trans haq, hqb.trans hbhi⟩

theorem Witness.x0_before_y {x y : List TaggedCoord} (w : Witness x y)
    {a b : TaggedCoord} (ha : a ∈ w.X.p0) (hb : b ∈ y) : a.value < b.value := by
  obtain ⟨i, hi, hodd⟩ := w.right_index hb
  exact (w.blockAt_lt (show (0 : Fin 11) < i by omega)).mem ha hi

theorem Witness.y_before_x5 {x y : List TaggedCoord} (w : Witness x y)
    {a b : TaggedCoord} (ha : a ∈ y) (hb : b ∈ w.X.p5) : a.value < b.value := by
  obtain ⟨i, hi, hodd⟩ := w.right_index ha
  exact (w.blockAt_lt (show i < (10 : Fin 11) by omega)).mem hi hb

theorem Witness.inside_first_of_inside_second {x y : List TaggedCoord} (w : Witness x y)
    {q : TaggedCoord} (hq : Inside y q) : Inside x q := by
  obtain ⟨lo, hlo, hi, hhi, hlq, hqh⟩ := hq
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w.X.p0 w.X.ne0
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil w.X.p5 w.X.ne5
  exact ⟨a, w.X.mem0 ha, b, w.X.mem5 hb,
    (w.x0_before_y ha hlo).trans hlq, hqh.trans (w.y_before_x5 hhi hb)⟩

theorem Witness.second_mem_inside_first {x y : List TaggedCoord} (w : Witness x y)
    {q : TaggedCoord} (hq : q ∈ y) : Inside x q := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w.X.p0 w.X.ne0
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil w.X.p5 w.X.ne5
  exact ⟨a, w.X.mem0 ha, b, w.X.mem5 hb, w.x0_before_y ha hq, w.y_before_x5 hq hb⟩

theorem Witness.inside_of_internal_index {x y : List TaggedCoord} (w : Witness x y)
    {q : TaggedCoord} {i : Fin 11} (hq : w.InBlock q i)
    (hlo : (1 : Fin 11) < i) (hhi : i < (9 : Fin 11)) : Inside y q := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w.Y.p0 w.Y.ne0
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil w.Y.p4 w.Y.ne4
  exact ⟨a, w.Y.mem0 ha, b, w.Y.mem4 hb,
    (w.blockAt_lt hlo).mem ha hq, (w.blockAt_lt hhi).mem hq hb⟩

theorem Witness.index_bounds_of_inside {x y : List TaggedCoord} (w : Witness x y)
    {q : TaggedCoord} {i : Fin 11} (hq : w.InBlock q i) (heven : i.val % 2 = 0)
    (hinside : Inside y q) : (2 : Fin 11) ≤ i ∧ i ≤ (8 : Fin 11) := by
  obtain ⟨lo, hlo, hi, hhi, hlq, hqh⟩ := hinside
  obtain ⟨j, hj, hjodd⟩ := w.right_index hlo
  obtain ⟨k, hk, hkodd⟩ := w.right_index hhi
  have hji : j < i := w.index_lt_of_value_lt hj hq hlq (by intro h; subst j; omega)
  have hik : i < k := w.index_lt_of_value_lt hq hk hqh (by intro h; subst k; omega)
  omega

theorem Witness.core_iff {x y : List TaggedCoord} (w : Witness x y) (q : TaggedCoord) :
    q ∈ Core x y ↔ (q ∈ w.X.p2 ∨ q ∈ w.X.p3) ∧ q.box = true := by
  constructor
  · rintro ⟨⟨hq, hbox⟩, hin⟩
    refine ⟨?_, hbox⟩
    rcases w.X.mem_cases hq with h | h | h | h | h | h
    · have hb := w.index_bounds_of_inside (i := 0) h (by decide) hin
      omega
    · have hn := w.noBox_x1 q h
      simp only [hbox, Bool.true_eq_false] at hn
    · exact Or.inl h
    · exact Or.inr h
    · have hn := w.noBox_x4 q h
      simp only [hbox, Bool.true_eq_false] at hn
    · have hb := w.index_bounds_of_inside (i := 10) h (by decide) hin
      omega
  · rintro ⟨hq | hq, hbox⟩
    · exact ⟨⟨w.X.mem2 hq, hbox⟩,
        w.inside_of_internal_index (i := 4) hq (by decide) (by decide)⟩
    · exact ⟨⟨w.X.mem3 hq, hbox⟩,
        w.inside_of_internal_index (i := 6) hq (by decide) (by decide)⟩

theorem Witness.core_nonempty {x y : List TaggedCoord} (w : Witness x y) :
    (Core x y).Nonempty := by
  obtain ⟨q, hq, hbox⟩ := w.box_x2
  exact ⟨q, (w.core_iff q).mpr ⟨Or.inl hq, hbox⟩⟩

theorem core_subset {a b c : List TaggedCoord} (w : Witness b c) :
    Core a c ⊆ Core a b := by
  intro q hq
  exact ⟨hq.1, w.inside_first_of_inside_second hq.2⟩

theorem Witness.box_right_parts {x y : List TaggedCoord} (w : Witness x y)
    {q : TaggedCoord} (hq : IsBoxCoord y q) : q ∈ w.Y.p0 ∨ q ∈ w.Y.p4 := by
  rcases w.Y.mem_cases hq.1 with h | h | h | h | h
  · exact Or.inl h
  · have hn := w.noBox_y1 q h
    simp only [hq.2, Bool.true_eq_false] at hn
  · have hn := w.noBox_y2 q h
    simp only [hq.2, Bool.true_eq_false] at hn
  · have hn := w.noBox_y3 q h
    simp only [hq.2, Bool.true_eq_false] at hn
  · exact Or.inr h

theorem Witness.low_before_inside {x y : List TaggedCoord} (w : Witness x y)
    {q r : TaggedCoord} (hq : q ∈ w.Y.p0) (hr : r ∈ x) (hin : Inside y r) :
    q.value < r.value := by
  obtain ⟨i, hi, heven⟩ := w.left_index hr
  have hbound := w.index_bounds_of_inside hi heven hin
  exact (w.blockAt_lt (show (1 : Fin 11) < i by omega)).mem hq hi

theorem Witness.inside_before_high {x y : List TaggedCoord} (w : Witness x y)
    {q r : TaggedCoord} (hq : q ∈ x) (hin : Inside y q) (hr : r ∈ w.Y.p4) :
    q.value < r.value := by
  obtain ⟨i, hi, heven⟩ := w.left_index hq
  have hbound := w.index_bounds_of_inside hi heven hin
  exact (w.blockAt_lt (show i < (9 : Fin 11) by omega)).mem hi hr

theorem Witness.twixt_before_core {x y : List TaggedCoord} (w : Witness x y)
    {q r : TaggedCoord} (hq : q ∈ w.Y.p1) (hr : r ∈ Core x y) : q.value < r.value := by
  rcases (w.core_iff r).mp hr with ⟨hr | hr, _⟩
  · exact w.y1_x2.mem hq hr
  · exact (w.blockAt_lt (show (3 : Fin 11) < 6 by decide)).mem hq hr

theorem Witness.core_before_tween {x y : List TaggedCoord} (w : Witness x y)
    {q r : TaggedCoord} (hq : q ∈ Core x y) (hr : r ∈ w.Y.p3) : q.value < r.value := by
  rcases (w.core_iff q).mp hq with ⟨hq | hq, _⟩
  · exact (w.blockAt_lt (show (4 : Fin 11) < 7 by decide)).mem hq hr
  · exact w.x3_y3.mem hq hr

theorem Witness.mid_between_core_boxes {x y : List TaggedCoord} (w : Witness x y)
    {q : TaggedCoord} (hq : q ∈ w.Y.p2) :
    ∃ a ∈ Core x y, ∃ b ∈ Core x y, a.value < q.value ∧ q.value < b.value := by
  obtain ⟨a, ha, habox⟩ := w.box_x2
  obtain ⟨b, hb, hbbox⟩ := w.box_x3
  exact ⟨a, (w.core_iff a).mpr ⟨Or.inl ha, habox⟩,
    b, (w.core_iff b).mpr ⟨Or.inr hb, hbbox⟩, w.x2_y2.mem ha hq, w.y2_x3.mem hq hb⟩

theorem Witness.between_core_mem_mid {x y : List TaggedCoord} (w : Witness x y)
    {a q b : TaggedCoord} (ha : a ∈ Core x y) (hq : q ∈ y) (hb : b ∈ Core x y)
    (haq : a.value < q.value) (hqb : q.value < b.value) : q ∈ w.Y.p2 := by
  rcases w.Y.mem_cases hq with h | h | h | h | h
  · exact (haq.not_gt (w.low_before_inside h ha.1.1 ha.2)).elim
  · exact (haq.not_gt (w.twixt_before_core h ha)).elim
  · exact h
  · exact (hqb.not_gt (w.core_before_tween hb h)).elim
  · exact (hqb.not_gt (w.inside_before_high hb.1.1 hb.2 h)).elim

theorem Witness.no_first_between_mid {x y : List TaggedCoord} (w : Witness x y)
    {a q b : TaggedCoord} (ha : a ∈ w.Y.p2) (hq : q ∈ x) (hb : b ∈ w.Y.p2)
    (haq : a.value < q.value) (hqb : q.value < b.value) : False := by
  obtain ⟨i, hi, heven⟩ := w.left_index hq
  have h₁ : (5 : Fin 11) < i :=
    w.index_lt_of_value_lt ha hi haq (by intro h; subst i; simp at heven)
  have h₂ : i < (5 : Fin 11) :=
    w.index_lt_of_value_lt hi hb hqb (by intro h; subst i; simp at heven)
  exact h₁.not_gt h₂

end Erdos118.Pentagram
