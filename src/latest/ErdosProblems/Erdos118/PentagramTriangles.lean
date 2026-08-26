import ErdosProblems.Erdos118.PentagramGeometry

/-! Larson's triangle geometry: separated cores and a common partition
of the last vertex's boxed coordinates. -/

namespace Erdos118.Pentagram

open Negative

theorem Witness.left_wing {a b c : List TaggedCoord}
    (ab : Witness a b) (ac : Witness a c) (bc : Witness b c) :
    ∃ l ∈ ab.X.p1, ∀ q ∈ ac.Y.p1, l.value < q.value := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil ac.X.p1 ac.X.ne1
  have hin := bc.inside_first_of_inside_second
    (ac.inside_of_internal_index (i := 2) hp (by decide) (by decide))
  obtain ⟨i, hi, heven⟩ := ab.left_index (ac.X.mem1 hp)
  have hb := ab.index_bounds_of_inside hi heven hin
  by_cases he : i = 2
  · subst i
    exact ⟨p, hi, fun q hq ↦ ac.x1_y1.mem hp hq⟩
  · obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil ab.X.p1 ab.X.ne1
    have hlp := (ab.blockAt_lt (show (2 : Fin 11) < i by omega)).mem hl hi
    exact ⟨l, hl, fun q hq ↦ hlp.trans (ac.x1_y1.mem hp hq)⟩

theorem Witness.right_wing {a b c : List TaggedCoord}
    (ab : Witness a b) (ac : Witness a c) (bc : Witness b c) :
    ∃ r ∈ ab.X.p4, ∀ q ∈ ac.Y.p3, q.value < r.value := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil ac.X.p4 ac.X.ne4
  have hin := bc.inside_first_of_inside_second
    (ac.inside_of_internal_index (i := 8) hp (by decide) (by decide))
  obtain ⟨i, hi, heven⟩ := ab.left_index (ac.X.mem4 hp)
  have hb := ab.index_bounds_of_inside hi heven hin
  by_cases he : i = 8
  · subst i
    exact ⟨p, hi, fun q hq ↦ ac.y3_x4.mem hq hp⟩
  · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil ab.X.p4 ab.X.ne4
    have hpr := (ab.blockAt_lt (show i < (8 : Fin 11) by omega)).mem hi hr
    exact ⟨r, hr, fun q hq ↦ (ac.y3_x4.mem hq hp).trans hpr⟩

theorem Witness.no_spanning_core {a b c : List TaggedCoord}
    (ab : Witness a b) (ac : Witness a c) (bc : Witness b c)
    {l r : TaggedCoord} (hl : l ∈ Core b c) (hlow : l ∈ ab.Y.p0)
    (hr : r ∈ Core b c) (hhigh : r ∈ ab.Y.p4) : False := by
  have hcore : Core a b ⊆ Core a c := by
    intro q hq
    exact ⟨hq.1, inside_between hl.2 hr.2
      (ab.low_before_inside hlow hq.1.1 hq.2)
      (ab.inside_before_high hq.1.1 hq.2 hhigh)⟩
  obtain ⟨left, hleft, hleftBelow⟩ := ab.left_wing ac bc
  obtain ⟨right, hright, hrightAbove⟩ := ab.right_wing ac bc
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil ac.Y.p1 ac.Y.ne1
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil ac.Y.p3 ac.Y.ne3
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil ab.Y.p2 ab.Y.ne2
  obtain ⟨p, hp, q, hq, hpm, hmq⟩ := ab.mid_between_core_boxes hm
  have hum : u.value < m.value := (ac.twixt_before_core hu (hcore hp)).trans hpm
  have hmv : m.value < v.value := hmq.trans (ac.core_before_tween (hcore hq) hv)
  have hlu : l.value < u.value :=
    (ab.y0_x1.mem hlow hleft).trans (hleftBelow u hu)
  have hvr : v.value < r.value :=
    (hrightAbove v hv).trans (ab.x4_y4.mem hright hhigh)
  have huMid := bc.between_core_mem_mid hl (ac.Y.mem1 hu) hr hlu (hum.trans (hmv.trans hvr))
  have hvMid := bc.between_core_mem_mid hl (ac.Y.mem3 hv) hr (hlu.trans (hum.trans hmv)) hvr
  exact bc.no_first_between_mid huMid (ab.Y.mem2 hm) hvMid hum hmv

theorem Witness.core_one_side {a b c : List TaggedCoord}
    (ab : Witness a b) (ac : Witness a c) (bc : Witness b c) :
    (∀ q ∈ Core b c, q ∈ ab.Y.p0) ∨ (∀ q ∈ Core b c, q ∈ ab.Y.p4) := by
  classical
  by_cases hall : ∀ q ∈ Core b c, q ∈ ab.Y.p0
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨r, hr, hrNotLow⟩ := hall
    have hrHigh := (ab.box_right_parts hr.1).resolve_left hrNotLow
    apply Or.inr
    intro q hq
    rcases ab.box_right_parts hq.1 with hlow | hhigh
    · exact (ab.no_spanning_core ac bc hq hlow hr hrHigh).elim
    · exact hhigh

/-- A coordinate of the last word strictly separates its two earlier boxed cores. -/
theorem Witness.core_separator {a b c : List TaggedCoord}
    (ab : Witness a b) (ac : Witness a c) (bc : Witness b c) :
    (∃ q ∈ c, (∀ p ∈ Core a c, p.value < q.value) ∧
      (∀ r ∈ Core b c, q.value < r.value)) ∨
    (∃ q ∈ c, (∀ r ∈ Core b c, r.value < q.value) ∧
      (∀ p ∈ Core a c, q.value < p.value)) := by
  rcases ab.core_one_side ac bc with hlow | hhigh
  · obtain ⟨l, hl, hlq⟩ := ab.left_wing ac bc
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil ac.Y.p1 ac.Y.ne1
    exact Or.inr ⟨q, ac.Y.mem1 hq,
      fun r hr ↦ (ab.y0_x1.mem (hlow r hr) hl).trans (hlq q hq),
      fun p hp ↦ ac.twixt_before_core hq hp⟩
  · obtain ⟨r, hr, hqr⟩ := ab.right_wing ac bc
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil ac.Y.p3 ac.Y.ne3
    exact Or.inl ⟨q, ac.Y.mem3 hq, fun p hp ↦ ac.core_before_tween hp hq,
      fun p hp ↦ (hqr q hq).trans (ab.x4_y4.mem hr (hhigh p hp))⟩

def Witness.lowBoxes {x y : List TaggedCoord} (w : Witness x y) : Set TaggedCoord :=
  {q | IsBoxCoord w.Y.p0 q}

def Witness.highBoxes {x y : List TaggedCoord} (w : Witness x y) : Set TaggedCoord :=
  {q | IsBoxCoord w.Y.p4 q}

private theorem box_cuts_eq_of_separator {a b c : List TaggedCoord}
    (ac : Witness a c) (bc : Witness b c) {p : TaggedCoord}
    (hp : p ∈ a) (hin : Inside c p)
    (hlow : ∀ q ∈ bc.Y.p0, q.value < p.value)
    (hhigh : ∀ q ∈ bc.Y.p4, p.value < q.value) :
    ac.lowBoxes = bc.lowBoxes ∧ ac.highBoxes = bc.highBoxes := by
  constructor
  · ext q
    constructor
    · rintro ⟨hq, hbox⟩
      have hqp := ac.low_before_inside hq hp hin
      rcases bc.box_right_parts ⟨ac.Y.mem0 hq, hbox⟩ with h | h
      · exact ⟨h, hbox⟩
      · exact (hqp.not_gt (hhigh q h)).elim
    · rintro ⟨hq, hbox⟩
      have hqp := hlow q hq
      rcases ac.box_right_parts ⟨bc.Y.mem0 hq, hbox⟩ with h | h
      · exact ⟨h, hbox⟩
      · exact (hqp.not_gt (ac.inside_before_high hp hin h)).elim
  · ext q
    constructor
    · rintro ⟨hq, hbox⟩
      have hpq := ac.inside_before_high hp hin hq
      rcases bc.box_right_parts ⟨ac.Y.mem4 hq, hbox⟩ with h | h
      · exact (hpq.not_gt (hlow q h)).elim
      · exact ⟨h, hbox⟩
    · rintro ⟨hq, hbox⟩
      have hpq := hhigh q hq
      rcases ac.box_right_parts ⟨bc.Y.mem4 hq, hbox⟩ with h | h
      · exact (hpq.not_gt (ac.low_before_inside h hp hin)).elim
      · exact ⟨h, hbox⟩

/-- The low/high partition of the last vertex's boxes agrees on both edges. -/
theorem Witness.common_box_cuts {a b c : List TaggedCoord}
    (ab : Witness a b) (ac : Witness a c) (bc : Witness b c) :
    ac.lowBoxes = bc.lowBoxes ∧ ac.highBoxes = bc.highBoxes := by
  obtain ⟨p, hp⟩ := bc.core_nonempty
  obtain ⟨q, hq⟩ := ac.core_nonempty
  have hqAB := core_subset bc hq
  rcases ab.core_one_side ac bc with hlow | hhigh
  · obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil ab.X.p1 ab.X.ne1
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil ab.Y.p1 ab.Y.ne1
    have hpl : p.value < l.value := ab.y0_x1.mem (hlow p hp) hl
    have hlt : l.value < t.value := ab.x1_y1.mem hl ht
    have htq : t.value < q.value := ab.twixt_before_core ht hqAB
    have hlIn := inside_between hp.2 hq.2 hpl (hlt.trans htq)
    have htIn := inside_between hp.2 hq.2 (hpl.trans hlt) htq
    apply box_cuts_eq_of_separator ac bc (ab.X.mem1 hl) hlIn
    · intro v hv
      exact (bc.low_before_inside hv hp.1.1 hp.2).trans hpl
    · intro v hv
      exact hlt.trans (bc.inside_before_high (ab.Y.mem1 ht) htIn hv)
  · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil ab.X.p4 ab.X.ne4
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil ab.Y.p3 ab.Y.ne3
    have hqt : q.value < t.value := ab.core_before_tween hqAB ht
    have htr : t.value < r.value := ab.y3_x4.mem ht hr
    have hrp : r.value < p.value := ab.x4_y4.mem hr (hhigh p hp)
    have hrIn := inside_between hq.2 hp.2 (hqt.trans htr) hrp
    have htIn := inside_between hq.2 hp.2 hqt (htr.trans hrp)
    apply box_cuts_eq_of_separator ac bc (ab.X.mem4 hr) hrIn
    · intro v hv
      exact (bc.low_before_inside hv (ab.Y.mem3 ht) htIn).trans htr
    · intro v hv
      exact hrp.trans (bc.inside_before_high hp.1.1 hp.2 hv)

end Erdos118.Pentagram
