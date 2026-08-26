import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupport

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Branch geometry for sequence-lift base-fibre supports

This module exposes the elementary prefix geometry needed to audit possible
cycles in the finite base-fibre/support incidence graph.  It deliberately
contains no graph acyclicity conclusion: those cycle-level obligations remain
in the dedicated incidence-acyclicity module.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

namespace Node

/-- Extending through two successive nodes preserves the first prescribed
letter. -/
theorem ExtendsBy.trans
    {q u v : Node G} {a b : Alphabet G}
    (hqu : q.ExtendsBy a u) (huv : u.ExtendsBy b v) :
    q.ExtendsBy a v := by
  rcases hqu with ⟨hqu, hqu_entries, hqu_letter⟩
  rcases huv with ⟨huv, huv_entries, huv_letter⟩
  refine ⟨hqu.trans huv, ?_, ?_⟩
  · intro i
    calc
      q.entry i = u.entry ⟨i.1, i.2.trans hqu⟩ := hqu_entries i
      _ = v.entry ⟨i.1, (i.2.trans hqu).trans huv⟩ :=
        huv_entries ⟨i.1, i.2.trans hqu⟩
      _ = v.entry ⟨i.1, i.2.trans (hqu.trans huv)⟩ := by
        exact congrArg v.entry (Subtype.ext rfl)
  · calc
      v.entry ⟨q.length, hqu.trans huv⟩ =
          u.entry ⟨q.length, hqu⟩ :=
        (huv_entries ⟨q.length, hqu⟩).symm
      _ = a := hqu_letter

end Node

/-- Unpack a shared supported point of two fibres when the first base node is
strictly shorter. -/
theorem exists_baseFiber_edge_of_common_support_of_lt
    {S : Set (Edge G)} {q u : Node G} (hqu : q.length < u.length)
    {p : Point G}
    (hpq : p ∈ (system G).edgeSupportSet (baseFiber S q))
    (hpu : p ∈ (system G).edgeSupportSet (baseFiber S u)) :
    ∃ e ∈ baseFiber S q,
      p = baseApex e ∧ q.ExtendsBy (baseLetter e) u := by
  rcases hpq with ⟨e, he, hpe⟩
  rcases hpu with ⟨f, hf, hpf⟩
  exact ⟨e, he, (common_point_right_of_lt hqu he hf hpe hpf).1,
    (common_point_right_of_lt hqu he hf hpe hpf).2⟩

/-- Equal-length base fibres sharing a supported point have the same base
node. -/
theorem eq_of_common_support_of_length_eq
    {S : Set (Edge G)} {q u : Node G} (hqu : q.length = u.length)
    {p : Point G}
    (hpq : p ∈ (system G).edgeSupportSet (baseFiber S q))
    (hpu : p ∈ (system G).edgeSupportSet (baseFiber S u)) :
    q = u := by
  rcases hpq with ⟨e, he, hpe⟩
  rcases hpu with ⟨f, hf, hpf⟩
  exact common_base_eq_of_length_eq hqu he hf hpe hpf

/-- A branch out of `q` propagates across a shared supported point, provided
`q` is no longer than the new fibre and is not that fibre itself.  This is the
local induction step used when following the nontrivial arc of an incidence
cycle. -/
theorem Node.extendsBy_of_common_support_of_le
    {S : Set (Edge G)} {q u v : Node G} {a : Alphabet G}
    (hqu : q.ExtendsBy a u)
    (hqvle : q.length ≤ v.length) (hqvne : q ≠ v)
    {p : Point G}
    (hpu : p ∈ (system G).edgeSupportSet (baseFiber S u))
    (hpv : p ∈ (system G).edgeSupportSet (baseFiber S v)) :
    q.ExtendsBy a v := by
  rcases lt_trichotomy u.length v.length with huv | huv | hvu
  · rcases exists_baseFiber_edge_of_common_support_of_lt huv hpu hpv with
      ⟨e, he, hp, huv'⟩
    exact hqu.trans huv'
  · have huv' : u = v := eq_of_common_support_of_length_eq huv hpu hpv
    simpa [huv'] using! hqu
  · rcases exists_baseFiber_edge_of_common_support_of_lt (S := S) (q := v) (u := u)
      hvu hpv hpu with ⟨e, he, hp, hvu'⟩
    have hqv : q.length < v.length := by
      rcases hqvle.eq_or_lt with hqv | hqv
      · exact (hqvne (Node.eq_of_common_target_of_length_eq hqu hvu' hqv)).elim
      · exact hqv
    exact Node.extendsBy_of_common_target_of_lt hqu hvu' hqv

end SequenceLift

end Erdos593
