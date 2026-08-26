import ErdosProblems.Erdos593.TripleSystem.SequenceLift
import ErdosProblems.Erdos593.TripleSystem.EdgeRestriction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Linear trace uniqueness for sequence lifts

In a linear edge restriction, two sequence-lifted edges with the same
base trace and base pair must coincide.  This is the local rigidity fact
needed for the finite-trace decomposition.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

namespace Node

/-- The letter appended by a node extension is determined by its source and
target nodes. -/
theorem letter_eq_of_extendsBy_same_target
    {q t : Node G} {a b : Alphabet G}
    (ha : q.ExtendsBy a t) (hb : q.ExtendsBy b t) : a = b := by
  rcases ha with ⟨haLength, _, haLetter⟩
  rcases hb with ⟨hbLength, _, hbLetter⟩
  have hIndex : (⟨q.length, haLength⟩ : Set.Iio t.length) =
      ⟨q.length, hbLength⟩ := Subtype.ext (by rfl)
  calc
    a = t.entry ⟨q.length, haLength⟩ := haLetter.symm
    _ = t.entry ⟨q.length, hbLength⟩ := congrArg t.entry hIndex
    _ = b := hbLetter

end Node

/-- If two lifted-edge apexes agree over a common base trace, then the
underlying graph-edge letters agree. -/
theorem edgeLetter_eq_of_apex_eq
    {q t1 t2 : Node G} {x1 y1 x2 y2 z1 z2 : V}
    {hxy1 : G.Adj x1 y1} {hxy2 : G.Adj x2 y2}
    {hext1 : q.ExtendsBy (edgeLetter hxy1) t1}
    {hext2 : q.ExtendsBy (edgeLetter hxy2) t2}
    (hapex : (t1, z1) = (t2, z2)) :
    edgeLetter hxy1 = edgeLetter hxy2 := by
  have ht : t1 = t2 := congrArg Prod.fst hapex
  subst t2
  exact Node.letter_eq_of_extendsBy_same_target hext1 hext2

/-- In a linear restriction, two lifted edges extending the same trace by the
same base edge cannot differ. -/
theorem mkEdge_eq_of_same_basePair_of_linearTrace
    {S : Set (Edge G)}
    (hlin : ((system G).edgeRestriction S).Linear)
    {q t₁ t₂ : Node G} {x y z₁ z₂ : V}
    {hxy : G.Adj x y}
    {hext₁ : q.ExtendsBy (edgeLetter hxy) t₁}
    {hext₂ : q.ExtendsBy (edgeLetter hxy) t₂}
    (hmem₁ : mkEdge q t₁ x y z₁ hxy hext₁ ∈ S)
    (hmem₂ : mkEdge q t₂ x y z₂ hxy hext₂ ∈ S) :
    mkEdge q t₁ x y z₁ hxy hext₁ =
      mkEdge q t₂ x y z₂ hxy hext₂ := by
  let e₁ : S := ⟨mkEdge q t₁ x y z₁ hxy hext₁, hmem₁⟩
  let e₂ : S := ⟨mkEdge q t₂ x y z₂ hxy hext₂, hmem₂⟩
  let pₓ : (system G).EdgeSupport S :=
    ⟨(q, x), ⟨mkEdge q t₁ x y z₁ hxy hext₁, hmem₁,
      (inc_mkEdge_iff.mpr (Or.inl rfl))⟩⟩
  let pᵧ : (system G).EdgeSupport S :=
    ⟨(q, y), ⟨mkEdge q t₁ x y z₁ hxy hext₁, hmem₁,
      (inc_mkEdge_iff.mpr (Or.inr (Or.inl rfl)))⟩⟩
  have hpx₁ : ((system G).edgeRestriction S).Inc pₓ e₁ := by
    change (system G).Inc (q, x) (mkEdge q t₁ x y z₁ hxy hext₁)
    exact inc_mkEdge_iff.mpr (Or.inl rfl)
  have hpx₂ : ((system G).edgeRestriction S).Inc pₓ e₂ := by
    change (system G).Inc (q, x) (mkEdge q t₂ x y z₂ hxy hext₂)
    exact inc_mkEdge_iff.mpr (Or.inl rfl)
  have hpy₁ : ((system G).edgeRestriction S).Inc pᵧ e₁ := by
    change (system G).Inc (q, y) (mkEdge q t₁ x y z₁ hxy hext₁)
    exact inc_mkEdge_iff.mpr (Or.inr (Or.inl rfl))
  have hpy₂ : ((system G).edgeRestriction S).Inc pᵧ e₂ := by
    change (system G).Inc (q, y) (mkEdge q t₂ x y z₂ hxy hext₂)
    exact inc_mkEdge_iff.mpr (Or.inr (Or.inl rfl))
  have heq : e₁ = e₂ := by
    by_contra hne
    have hp : pₓ = pᵧ := hlin hne hpx₁ hpx₂ hpy₁ hpy₂
    apply hxy.ne
    exact congrArg Prod.snd (congrArg Subtype.val hp)
  simpa only [e₁, e₂] using! congrArg Subtype.val heq

/-- In a linear restriction, a lifted edge is determined by its base trace,
its unordered base graph edge, and membership in the restriction. -/
theorem mkEdge_eq_of_same_edgeLetter_of_linearTrace
    {S : Set (Edge G)}
    (hlin : ((system G).edgeRestriction S).Linear)
    {q t1 t2 : Node G} {x1 y1 x2 y2 z1 z2 : V}
    {hxy1 : G.Adj x1 y1} {hxy2 : G.Adj x2 y2}
    {hext1 : q.ExtendsBy (edgeLetter hxy1) t1}
    {hext2 : q.ExtendsBy (edgeLetter hxy2) t2}
    (hletter : edgeLetter hxy1 = edgeLetter hxy2)
    (hmem1 : mkEdge q t1 x1 y1 z1 hxy1 hext1 ∈ S)
    (hmem2 : mkEdge q t2 x2 y2 z2 hxy2 hext2 ∈ S) :
    mkEdge q t1 x1 y1 z1 hxy1 hext1 =
      mkEdge q t2 x2 y2 z2 hxy2 hext2 := by
  have hpairs : s(x1, y1) = s(x2, y2) := congrArg Subtype.val hletter
  rcases Sym2.eq_iff.mp hpairs with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact mkEdge_eq_of_same_basePair_of_linearTrace hlin hmem1 hmem2
  · rcases h with ⟨hxy, hyx⟩
    subst y2
    subst x2
    have hext2' : q.ExtendsBy (edgeLetter hxy1) t2 := by
      rwa [hletter]
    have hswap :
        mkEdge q t2 y1 x1 z2 hxy2 hext2 =
          mkEdge q t2 x1 y1 z2 hxy1 hext2' := by
      apply Subtype.ext
      ext p
      simp [mkEdge, or_left_comm]
    have hmem2' : mkEdge q t2 x1 y1 z2 hxy1 hext2' ∈ S := by
      rw [← hswap]
      exact hmem2
    exact (mkEdge_eq_of_same_basePair_of_linearTrace hlin hmem1 hmem2').trans
      hswap.symm

end SequenceLift

end Erdos593
