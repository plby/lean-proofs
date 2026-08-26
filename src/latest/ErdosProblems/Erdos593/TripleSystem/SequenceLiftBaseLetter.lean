import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseNormalForm
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftTrace

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical trace letters for sequence-lift edges

Each sequence-lift edge has a unique unordered graph-edge letter at its
canonical base node.  Together with the canonical base node, that letter is a
trace key which is injective on every linear edge restriction.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- `a` is the unordered base-graph letter of `e` in a representation at its
canonical base node. -/
def IsBaseLetter (e : Edge G) (a : Alphabet G) : Prop :=
  ∃ (t : Node G) (x y z : V) (hxy : G.Adj x y)
      (hext : (baseNode e).ExtendsBy (edgeLetter hxy) t),
    e = mkEdge (baseNode e) t x y z hxy hext ∧
      a = edgeLetter hxy

/-- Equality of two displayed lift edges at a common base node identifies
their apex points. -/
theorem apex_eq_of_mkEdge_eq_same_base
    {q t₁ t₂ : Node G} {x₁ y₁ z₁ x₂ y₂ z₂ : V}
    {hxy₁ : G.Adj x₁ y₁} {hxy₂ : G.Adj x₂ y₂}
    {hext₁ : q.ExtendsBy (edgeLetter hxy₁) t₁}
    {hext₂ : q.ExtendsBy (edgeLetter hxy₂) t₂}
    (heq :
      mkEdge q t₁ x₁ y₁ z₁ hxy₁ hext₁ =
        mkEdge q t₂ x₂ y₂ z₂ hxy₂ hext₂) :
    (t₁, z₁) = (t₂, z₂) := by
  have hinc :
      (system G).Inc (t₁, z₁) (mkEdge q t₂ x₂ y₂ z₂ hxy₂ hext₂) := by
    rw [← heq]
    exact inc_mkEdge_iff.mpr (Or.inr (Or.inr rfl))
  rcases inc_mkEdge_iff.mp hinc with h | h | h
  · exact
      (Node.ne_of_extendsBy hext₁ (congrArg Prod.fst h).symm).elim
  · exact
      (Node.ne_of_extendsBy hext₁ (congrArg Prod.fst h).symm).elim
  · exact h

/-- Every sequence-lift edge has a base letter. -/
theorem exists_isBaseLetter (e : Edge G) :
    ∃ a : Alphabet G, IsBaseLetter e a := by
  rcases exists_mkEdge_at_baseNode e with ⟨t, x, y, z, hxy, hext, he⟩
  exact ⟨edgeLetter hxy, t, x, y, z, hxy, hext, he, rfl⟩

/-- The base letter of a sequence-lift edge is unique. -/
theorem isBaseLetter_unique
    {e : Edge G} {a b : Alphabet G}
    (ha : IsBaseLetter e a) (hb : IsBaseLetter e b) :
    a = b := by
  rcases ha with ⟨t₁, x₁, y₁, z₁, hxy₁, hext₁, he₁, ha⟩
  rcases hb with ⟨t₂, x₂, y₂, z₂, hxy₂, hext₂, he₂, hb⟩
  have hmk :
      mkEdge (baseNode e) t₁ x₁ y₁ z₁ hxy₁ hext₁ =
        mkEdge (baseNode e) t₂ x₂ y₂ z₂ hxy₂ hext₂ :=
    he₁.symm.trans he₂
  have hapex : (t₁, z₁) = (t₂, z₂) :=
    apex_eq_of_mkEdge_eq_same_base hmk
  calc
    a = edgeLetter hxy₁ := ha
    _ = edgeLetter hxy₂ :=
      edgeLetter_eq_of_apex_eq
        (q := baseNode e) (hext1 := hext₁) (hext2 := hext₂) hapex
    _ = b := hb.symm

/-- The canonical unordered graph-edge letter of a sequence-lift edge. -/
noncomputable def baseLetter (e : Edge G) : Alphabet G :=
  Classical.choose (exists_isBaseLetter e)

/-- The canonical base letter satisfies its defining representation predicate. -/
theorem isBaseLetter_baseLetter (e : Edge G) :
    IsBaseLetter e (baseLetter e) :=
  Classical.choose_spec (exists_isBaseLetter e)

/-- Characterization of the unique base letter of a sequence-lift edge. -/
theorem isBaseLetter_iff_eq_baseLetter (e : Edge G) (a : Alphabet G) :
    IsBaseLetter e a ↔ a = baseLetter e := by
  constructor
  · intro ha
    exact isBaseLetter_unique ha (isBaseLetter_baseLetter e)
  · intro ha
    rw [ha]
    exact isBaseLetter_baseLetter e

/-- An explicit lift edge has the letter used to construct it as its base
letter. -/
theorem isBaseLetter_mkEdge
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (edgeLetter hxy) t} :
    IsBaseLetter (mkEdge q t x y z hxy hext) (edgeLetter hxy) := by
  simp only [IsBaseLetter, baseNode_mkEdge]
  exact ⟨t, x, y, z, hxy, hext, rfl, rfl⟩

/-- The canonical base letter recovers the displayed graph-edge letter. -/
theorem baseLetter_mkEdge
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (edgeLetter hxy) t} :
    baseLetter (mkEdge q t x y z hxy hext) = edgeLetter hxy := by
  exact isBaseLetter_unique (isBaseLetter_baseLetter _) isBaseLetter_mkEdge

/-- Canonical finite-trace key: the unique two-point base node paired with its
unordered graph-edge letter. -/
noncomputable def traceKey (e : Edge G) : Node G × Alphabet G :=
  (baseNode e, baseLetter e)

/-- The trace key of a displayed lift edge is its displayed base and letter. -/
theorem traceKey_mkEdge
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (edgeLetter hxy) t} :
    traceKey (mkEdge q t x y z hxy hext) = (q, edgeLetter hxy) := by
  simp only [traceKey, baseNode_mkEdge, baseLetter_mkEdge]

/-- On a linear restriction, the canonical base node and base letter determine
a sequence-lift edge. -/
theorem eq_of_same_baseNode_baseLetter_of_mem_of_linear
    {S : Set (Edge G)}
    (hlin : ((system G).edgeRestriction S).Linear)
    {e₁ e₂ : Edge G}
    (hmem₁ : e₁ ∈ S) (hmem₂ : e₂ ∈ S)
    (hbase : baseNode e₁ = baseNode e₂)
    (hletter : baseLetter e₁ = baseLetter e₂) :
    e₁ = e₂ := by
  rcases exists_mkEdge_at_baseNode e₁ with
    ⟨t₁, x₁, y₁, z₁, hxy₁, hext₁, he₁⟩
  rcases exists_mkEdge_at_baseNode e₂ with
    ⟨t₂, x₂, y₂, z₂, hxy₂, hext₂, he₂⟩
  have hext₂' : (baseNode e₁).ExtendsBy (edgeLetter hxy₂) t₂ := by
    rw [hbase]
    exact hext₂
  have he₂' : e₂ = mkEdge (baseNode e₁) t₂ x₂ y₂ z₂ hxy₂ hext₂' := by
    simpa only [hbase] using! he₂
  have hbaseLetter₁ : baseLetter e₁ = edgeLetter hxy₁ := by
    rw [he₁]
    exact baseLetter_mkEdge
  have hbaseLetter₂ : baseLetter e₂ = edgeLetter hxy₂ := by
    rw [he₂']
    exact baseLetter_mkEdge
  have hdisplayedLetter : edgeLetter hxy₁ = edgeLetter hxy₂ := by
    calc
      edgeLetter hxy₁ = baseLetter e₁ := hbaseLetter₁.symm
      _ = baseLetter e₂ := hletter
      _ = edgeLetter hxy₂ := hbaseLetter₂
  have hmem₁' : mkEdge (baseNode e₁) t₁ x₁ y₁ z₁ hxy₁ hext₁ ∈ S := by
    rw [← he₁]
    exact hmem₁
  have hmem₂' : mkEdge (baseNode e₁) t₂ x₂ y₂ z₂ hxy₂ hext₂' ∈ S := by
    rw [← he₂']
    exact hmem₂
  calc
    e₁ = mkEdge (baseNode e₁) t₁ x₁ y₁ z₁ hxy₁ hext₁ := he₁
    _ = mkEdge (baseNode e₁) t₂ x₂ y₂ z₂ hxy₂ hext₂' :=
      mkEdge_eq_of_same_edgeLetter_of_linearTrace hlin hdisplayedLetter hmem₁' hmem₂'
    _ = e₂ := he₂'.symm

/-- Pointwise equality form of trace-key injectivity on a linear restriction. -/
theorem eq_of_traceKey_eq_of_mem_of_linear
    {S : Set (Edge G)}
    (hlin : ((system G).edgeRestriction S).Linear)
    {e₁ e₂ : Edge G}
    (hmem₁ : e₁ ∈ S) (hmem₂ : e₂ ∈ S)
    (hkey : traceKey e₁ = traceKey e₂) :
    e₁ = e₂ := by
  have hbase : baseNode e₁ = baseNode e₂ := by
    simpa only [traceKey] using! congrArg Prod.fst hkey
  have hletter : baseLetter e₁ = baseLetter e₂ := by
    simpa only [traceKey] using! congrArg Prod.snd hkey
  exact eq_of_same_baseNode_baseLetter_of_mem_of_linear
    hlin hmem₁ hmem₂ hbase hletter

/-- The canonical trace key is injective on every linear edge restriction. -/
theorem traceKey_injOn_of_linear
    {S : Set (Edge G)}
    (hlin : ((system G).edgeRestriction S).Linear) :
    Set.InjOn traceKey S := by
  intro e₁ hmem₁ e₂ hmem₂ hkey
  exact eq_of_traceKey_eq_of_mem_of_linear hlin hmem₁ hmem₂ hkey

end SequenceLift
end Erdos593
