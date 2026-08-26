import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiber

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical apex points in sequence-lift base fibres

Every lift edge has one point away from its canonical base node. In a linear
canonical base fibre, that point is private to its own selected edge. These
are factor-local facts; this module makes no global trace-decomposition or
cardinality-sum claim.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The unique point of a lift edge lying away from its canonical base node. -/
def IsBaseApex (e : Edge G) (p : Point G) : Prop :=
  (system G).Inc p e ∧ p.1 ≠ baseNode e

/-- Every lift edge has exactly one point away from its canonical base node. -/
theorem existsUnique_isBaseApex (e : Edge G) :
    ∃! p : Point G, IsBaseApex e p := by
  rcases exists_mkEdge_at_baseNode e with ⟨t, x, y, z, hxy, hext, he⟩
  rw [he]
  refine ⟨(t, z), ?_, ?_⟩
  · constructor
    · exact inc_mkEdge_iff.mpr (Or.inr (Or.inr rfl))
    · simpa only [baseNode_mkEdge] using! (Node.ne_of_extendsBy hext).symm
  · intro p hp
    rcases inc_mkEdge_iff.mp hp.1 with h | h | h
    · exfalso
      apply hp.2
      simp only [h, baseNode_mkEdge]
    · exfalso
      apply hp.2
      simp only [h, baseNode_mkEdge]
    · exact h

/-- The canonically chosen apex point of a sequence-lift edge. -/
noncomputable def baseApex (e : Edge G) : Point G :=
  Classical.choose (existsUnique_isBaseApex e).exists

/-- The canonical apex lies on its edge and is away from its base node. -/
theorem isBaseApex_baseApex (e : Edge G) :
    IsBaseApex e (baseApex e) :=
  Classical.choose_spec (existsUnique_isBaseApex e).exists

/-- The canonical apex is incident with its defining lift edge. -/
theorem inc_baseApex (e : Edge G) :
    (system G).Inc (baseApex e) e :=
  (isBaseApex_baseApex e).1

/-- The canonical apex lies over a node different from the canonical base. -/
theorem baseApex_node_ne_baseNode (e : Edge G) :
    (baseApex e).1 ≠ baseNode e :=
  (isBaseApex_baseApex e).2

/-- Any point satisfying the base-apex predicate is the chosen apex. -/
theorem eq_baseApex_of_isBaseApex {e : Edge G} {p : Point G}
    (hp : IsBaseApex e p) :
    p = baseApex e := by
  exact (existsUnique_isBaseApex e).unique hp (isBaseApex_baseApex e)

/-- The base-apex predicate characterizes the canonically chosen apex. -/
theorem isBaseApex_iff_eq_baseApex {e : Edge G} {p : Point G} :
    IsBaseApex e p ↔ p = baseApex e := by
  constructor
  · exact eq_baseApex_of_isBaseApex
  · rintro rfl
    exact isBaseApex_baseApex e

/-- The selected apex of an explicit lift edge is its displayed apex. -/
theorem baseApex_mkEdge
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (edgeLetter hxy) t} :
    baseApex (mkEdge q t x y z hxy hext) = (t, z) := by
  symm
  apply eq_baseApex_of_isBaseApex
  constructor
  · exact inc_mkEdge_iff.mpr (Or.inr (Or.inr rfl))
  · simpa only [baseNode_mkEdge] using! (Node.ne_of_extendsBy hext).symm

/-- Within one canonical base fibre of a linear restriction, an edge's apex is
incident with no other selected fibre edge. -/
theorem baseApex_inc_iff_eq_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).edgeRestriction S).Linear)
    {e f : Edge G}
    (he : e ∈ baseFiber S q) (hf : f ∈ baseFiber S q) :
    (system G).Inc (baseApex e) f ↔ e = f := by
  constructor
  · intro hinc
    rcases exists_mkEdge_at_baseNode e with
      ⟨t₁, x₁, y₁, z₁, hxy₁, hext₁, he₁⟩
    rcases exists_mkEdge_at_baseNode f with
      ⟨t₂, x₂, y₂, z₂, hxy₂, hext₂, he₂⟩
    have hapex₁ : baseApex e = (t₁, z₁) := by
      rw [he₁]
      exact baseApex_mkEdge
    have hinc' : (system G).Inc (t₁, z₁) f := by
      rw [← hapex₁]
      exact hinc
    rw [he₂, inc_mkEdge_iff] at hinc'
    rcases hinc' with hcore | hcore | hapex
    · have hext₁' : q.ExtendsBy (edgeLetter hxy₁) t₁ := by
        simpa only [he.2] using! hext₁
      have htq : t₁ ≠ q := (Node.ne_of_extendsBy hext₁').symm
      exact (htq ((congrArg Prod.fst hcore).trans hf.2)).elim
    · have hext₁' : q.ExtendsBy (edgeLetter hxy₁) t₁ := by
        simpa only [he.2] using! hext₁
      have htq : t₁ ≠ q := (Node.ne_of_extendsBy hext₁').symm
      exact (htq ((congrArg Prod.fst hcore).trans hf.2)).elim
    · have hext₁' : q.ExtendsBy (edgeLetter hxy₁) t₁ := by
        simpa only [he.2] using! hext₁
      have hext₂' : q.ExtendsBy (edgeLetter hxy₂) t₂ := by
        simpa only [hf.2] using! hext₂
      have hletter : baseLetter e = baseLetter f := by
        calc
          baseLetter e = edgeLetter hxy₁ := by
            rw [he₁]
            exact baseLetter_mkEdge
          _ = edgeLetter hxy₂ :=
            edgeLetter_eq_of_apex_eq
              (q := q) (hext1 := hext₁') (hext2 := hext₂') hapex
          _ = baseLetter f := by
            rw [he₂]
            exact baseLetter_mkEdge.symm
      exact eq_of_same_baseNode_baseLetter_of_mem_of_linear
        hlin he.1 hf.1 (he.2.trans hf.2.symm) hletter
  · rintro rfl
    exact (isBaseApex_baseApex e).1

/-- The canonical apex assignment is injective inside every linear base fibre. -/
theorem baseApex_injOn_baseFiber_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).edgeRestriction S).Linear) :
    Set.InjOn baseApex (baseFiber S q) := by
  intro e he f hf hapex
  apply (baseApex_inc_iff_eq_of_linear q hlin he hf).mp
  rw [hapex]
  exact (isBaseApex_baseApex f).1

end SequenceLift
end Erdos593
