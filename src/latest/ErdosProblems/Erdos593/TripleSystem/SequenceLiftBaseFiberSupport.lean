import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseIncidence

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pairwise support geometry of sequence-lift base fibres

This module isolates the strongest pairwise support consequence of linearity:
two distinct canonical base fibres have at most one supported point in common.
It is deliberately a pairwise result.  It does not establish the stronger
running-intersection condition required to assemble an arbitrary finite list
of fibres, since several singleton overlaps can still accumulate in one
assembly step.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

namespace Node

/-- If two nodes extend to one target and the first starts earlier, the first
already extends through the second. -/
theorem extendsBy_of_common_target_of_lt
    {q u t : Node G} {a b : Alphabet G}
    (hqt : q.ExtendsBy a t) (hut : u.ExtendsBy b t)
    (hqu : q.length < u.length) : q.ExtendsBy a u := by
  apply Exists.intro hqu
  constructor
  · intro i
    calc
      q.entry i = t.entry ⟨i.1, i.2.trans hqt.choose⟩ := hqt.choose_spec.1 i
      _ = t.entry ⟨i.1, (i.2.trans hqu).trans hut.choose⟩ := by
        exact congrArg t.entry (Subtype.ext rfl)
      _ = u.entry ⟨i.1, i.2.trans hqu⟩ :=
        (hut.choose_spec.1 ⟨i.1, i.2.trans hqu⟩).symm
  · calc
      u.entry ⟨q.length, hqu⟩ = t.entry ⟨q.length, hqu.trans hut.choose⟩ :=
        hut.choose_spec.1 ⟨q.length, hqu⟩
      _ = t.entry ⟨q.length, hqt.choose⟩ := by
        exact congrArg t.entry (Subtype.ext rfl)
      _ = a := hqt.choose_spec.2

/-- Two nodes of equal length that both extend to one target are equal. -/
theorem eq_of_common_target_of_length_eq
    {q u t : Node G} {a b : Alphabet G}
    (hqt : q.ExtendsBy a t) (hut : u.ExtendsBy b t)
    (hqu : q.length = u.length) : q = u := by
  cases q
  cases u
  cases hqu
  congr
  funext i
  calc
    _ = t.entry ⟨i.1, i.2.trans hqt.choose⟩ := hqt.choose_spec.1 i
    _ = t.entry ⟨i.1, i.2.trans hut.choose⟩ := by
      exact congrArg t.entry (Subtype.ext rfl)
    _ = _ := (hut.choose_spec.1 i).symm

end Node

/-- A point supported by two base fibres is an apex of the shorter fibre, and
the longer base node follows the shorter fibre's base letter. -/
theorem common_point_right_of_lt
    {S : Set (Edge G)} {q u : Node G} (hqlt : q.length < u.length)
    {p : Point G} {e f : Edge G}
    (he : e ∈ baseFiber S q) (hf : f ∈ baseFiber S u)
    (hpe : (system G).Inc p e) (hpf : (system G).Inc p f) :
    p = baseApex e ∧ q.ExtendsBy (baseLetter e) u := by
  rcases (inc_iff_baseNode_baseLetter_or_baseApex G e p).mp hpe with hpcore | hpApex
  · rcases (inc_iff_baseNode_baseLetter_or_baseApex G f p).mp hpf with hpucore | huApex
    · have hpq : p.1 = q := hpcore.1.trans he.2
      have hpu : p.1 = u := hpucore.1.trans hf.2
      have hqu : q = u := hpq.symm.trans hpu
      exact (hqlt.ne (congrArg Node.length hqu)).elim
    · rcases exists_mkEdge_at_baseNode f with ⟨t, x, y, z, hxy, hext, hfm⟩
      have hextu : u.ExtendsBy (edgeLetter hxy) t := by
        rw [hf.2] at hext
        exact hext
      have hapexf : baseApex f = (t, z) := by
        rw [hfm]
        exact baseApex_mkEdge
      have hpq : p.1 = q := hpcore.1.trans he.2
      have hqt : q = t := by
        calc
          q = p.1 := hpq.symm
          _ = (baseApex f).1 := congrArg Prod.fst huApex
          _ = t := congrArg Prod.fst hapexf
      have huq : u.length < q.length := by
        rw [hqt]
        exact hextu.choose
      exact (lt_asymm hqlt huq).elim
  · rcases (inc_iff_baseNode_baseLetter_or_baseApex G f p).mp hpf with hpucore | huApex
    · rcases exists_mkEdge_at_baseNode e with ⟨t, x, y, z, hxy, hext, hem⟩
      have hextq : q.ExtendsBy (edgeLetter hxy) t := by
        rw [he.2] at hext
        exact hext
      have hapexe : baseApex e = (t, z) := by
        rw [hem]
        exact baseApex_mkEdge
      have hpu : p.1 = u := hpucore.1.trans hf.2
      have htp : t = p.1 := by
        calc
          t = (baseApex e).1 := (congrArg Prod.fst hapexe).symm
          _ = p.1 := (congrArg Prod.fst hpApex).symm
      have htu : t = u := htp.trans hpu
      have hletter : baseLetter e = edgeLetter hxy := by
        rw [hem]
        exact baseLetter_mkEdge
      refine ⟨hpApex, ?_⟩
      rw [hletter]
      rw [← htu]
      exact hextq
    · rcases exists_mkEdge_at_baseNode e with ⟨t, x, y, z, hxy, hext, hem⟩
      rcases exists_mkEdge_at_baseNode f with ⟨v, w, r, s, hwr, hfext, hfm⟩
      have hextq : q.ExtendsBy (edgeLetter hxy) t := by
        rw [he.2] at hext
        exact hext
      have hextu : u.ExtendsBy (edgeLetter hwr) v := by
        rw [hf.2] at hfext
        exact hfext
      have hapexe : baseApex e = (t, z) := by
        rw [hem]
        exact baseApex_mkEdge
      have hapexf : baseApex f = (v, s) := by
        rw [hfm]
        exact baseApex_mkEdge
      have htv : t = v := by
        calc
          t = (baseApex e).1 := (congrArg Prod.fst hapexe).symm
          _ = p.1 := (congrArg Prod.fst hpApex).symm
          _ = (baseApex f).1 := congrArg Prod.fst huApex
          _ = v := congrArg Prod.fst hapexf
      have hextu' : u.ExtendsBy (edgeLetter hwr) t := by
        rw [htv]
        exact hextu
      have hletter : baseLetter e = edgeLetter hxy := by
        rw [hem]
        exact baseLetter_mkEdge
      refine ⟨hpApex, ?_⟩
      rw [hletter]
      exact Node.extendsBy_of_common_target_of_lt hextq hextu' hqlt

/-- Equal-length base fibres sharing an incident point have the same base
node. -/
theorem common_base_eq_of_length_eq
    {S : Set (Edge G)} {q u : Node G} (hqu : q.length = u.length)
    {p : Point G} {e f : Edge G}
    (he : e ∈ baseFiber S q) (hf : f ∈ baseFiber S u)
    (hpe : (system G).Inc p e) (hpf : (system G).Inc p f) : q = u := by
  rcases (inc_iff_baseNode_baseLetter_or_baseApex G e p).mp hpe with hpcore | hpApex
  · rcases (inc_iff_baseNode_baseLetter_or_baseApex G f p).mp hpf with hpucore | huApex
    · have hpq : p.1 = q := hpcore.1.trans he.2
      have hpu : p.1 = u := hpucore.1.trans hf.2
      exact hpq.symm.trans hpu
    · rcases exists_mkEdge_at_baseNode f with ⟨t, x, y, z, hxy, hext, hfm⟩
      have hextu : u.ExtendsBy (edgeLetter hxy) t := by
        rw [hf.2] at hext
        exact hext
      have hapexf : baseApex f = (t, z) := by
        rw [hfm]
        exact baseApex_mkEdge
      have hpq : p.1 = q := hpcore.1.trans he.2
      have hqt : q = t := by
        calc
          q = p.1 := hpq.symm
          _ = (baseApex f).1 := congrArg Prod.fst huApex
          _ = t := congrArg Prod.fst hapexf
      have huq : u.length < q.length := by
        rw [hqt]
        exact hextu.choose
      rw [hqu] at huq
      exact (lt_irrefl _ huq).elim
  · rcases (inc_iff_baseNode_baseLetter_or_baseApex G f p).mp hpf with hpucore | huApex
    · rcases exists_mkEdge_at_baseNode e with ⟨t, x, y, z, hxy, hext, hem⟩
      have hextq : q.ExtendsBy (edgeLetter hxy) t := by
        rw [he.2] at hext
        exact hext
      have hapexe : baseApex e = (t, z) := by
        rw [hem]
        exact baseApex_mkEdge
      have hpu : p.1 = u := hpucore.1.trans hf.2
      have htp : t = p.1 := by
        calc
          t = (baseApex e).1 := (congrArg Prod.fst hapexe).symm
          _ = p.1 := (congrArg Prod.fst hpApex).symm
      have htu : t = u := htp.trans hpu
      have hqut : q.length < u.length := by
        rw [← htu]
        exact hextq.choose
      rw [hqu] at hqut
      exact (lt_irrefl _ hqut).elim
    · rcases exists_mkEdge_at_baseNode e with ⟨t, x, y, z, hxy, hext, hem⟩
      rcases exists_mkEdge_at_baseNode f with ⟨v, w, r, s, hwr, hfext, hfm⟩
      have hextq : q.ExtendsBy (edgeLetter hxy) t := by
        rw [he.2] at hext
        exact hext
      have hextu : u.ExtendsBy (edgeLetter hwr) v := by
        rw [hf.2] at hfext
        exact hfext
      have hapexe : baseApex e = (t, z) := by
        rw [hem]
        exact baseApex_mkEdge
      have hapexf : baseApex f = (v, s) := by
        rw [hfm]
        exact baseApex_mkEdge
      have htv : t = v := by
        calc
          t = (baseApex e).1 := (congrArg Prod.fst hapexe).symm
          _ = p.1 := (congrArg Prod.fst hpApex).symm
          _ = (baseApex f).1 := congrArg Prod.fst huApex
          _ = v := congrArg Prod.fst hapexf
      have hextu' : u.ExtendsBy (edgeLetter hwr) t := by
        rw [htv]
        exact hextu
      exact Node.eq_of_common_target_of_length_eq hextq hextu' hqu

/-- Distinct canonical base fibres of a linear selected restriction have at
most one common supported point. -/
theorem baseFiber_support_inter_subsingleton_of_linear
    {S : Set (Edge G)} {q u : Node G}
    (hlin : ((system G).edgeRestriction S).Linear) (hne : q ≠ u) :
    (((system G).edgeSupportSet (baseFiber S q) ∩
      (system G).edgeSupportSet (baseFiber S u))).Subsingleton := by
  intro p hp r hr
  rcases hp with ⟨hpq, hpu⟩
  rcases hr with ⟨hrq, hru⟩
  rcases hpq with ⟨e, he, hpe⟩
  rcases hpu with ⟨f, hf, hpf⟩
  rcases hrq with ⟨e', he', hre⟩
  rcases hru with ⟨f', hf', hrf⟩
  rcases lt_trichotomy q.length u.length with hqlt | hqu | huqlt
  · rcases common_point_right_of_lt hqlt he hf hpe hpf with ⟨hpApex, hqe⟩
    rcases common_point_right_of_lt hqlt he' hf' hre hrf with ⟨hrApex, hqe'⟩
    have hletter : baseLetter e = baseLetter e' :=
      Node.letter_eq_of_extendsBy_same_target hqe hqe'
    have heq : e = e' :=
      eq_of_same_baseNode_baseLetter_of_mem_of_linear
        hlin he.1 he'.1 (he.2.trans he'.2.symm) hletter
    calc
      p = baseApex e := hpApex
      _ = baseApex e' := by rw [heq]
      _ = r := hrApex.symm
  · exact (hne (common_base_eq_of_length_eq hqu he hf hpe hpf)).elim
  · rcases common_point_right_of_lt (q := u) (u := q) huqlt hf he hpf hpe with
      ⟨hpApex, huf⟩
    rcases common_point_right_of_lt (q := u) (u := q) huqlt hf' he' hrf hre with
      ⟨hrApex, huf'⟩
    have hletter : baseLetter f = baseLetter f' :=
      Node.letter_eq_of_extendsBy_same_target huf huf'
    have hfeq : f = f' :=
      eq_of_same_baseNode_baseLetter_of_mem_of_linear
        hlin hf.1 hf'.1 (hf.2.trans hf'.2.symm) hletter
    calc
      p = baseApex f := hpApex
      _ = baseApex f' := by rw [hfeq]
      _ = r := hrApex.symm

end SequenceLift

end Erdos593
