import ErdosProblems.Erdos593.TripleSystem.SequenceLift

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical base nodes of sequence-lift edges

Every sequence-lift hyperedge has exactly one node containing its two
base-graph vertices. This gives the canonical trace index for grouping finite
edge restrictions.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- `q` is the unique node of `e` which contains two distinct points of the
edge. -/
def BasedAt (q : Node G) (e : Edge G) : Prop :=
  ∃ x y : V, x ≠ y ∧ (system G).Inc (q, x) e ∧ (system G).Inc (q, y) e

/-- Every displayed lift edge is based at its displayed base node. -/
theorem mkEdge_basedAt
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (edgeLetter hxy) t} :
    BasedAt q (mkEdge q t x y z hxy hext) := by
  refine ⟨x, y, hxy.ne, ?_, ?_⟩
  · exact inc_mkEdge_iff.mpr (Or.inl rfl)
  · exact inc_mkEdge_iff.mpr (Or.inr (Or.inl rfl))

/-- Any node witnessing `BasedAt` for a displayed lift edge is its displayed
base node. -/
theorem basedAt_eq_base_of_mkEdge
    {q r t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (edgeLetter hxy) t}
    (hr : BasedAt r (mkEdge q t x y z hxy hext)) : r = q := by
  rcases hr with ⟨u, v, huv, hu, hv⟩
  rw [inc_mkEdge_iff] at hu hv
  by_contra hrq
  rcases hu with hu | hu | hu
  · exact hrq (congrArg Prod.fst hu)
  · exact hrq (congrArg Prod.fst hu)
  rcases hv with hv | hv | hv
  · exact hrq (congrArg Prod.fst hv)
  · exact hrq (congrArg Prod.fst hv)
  apply huv
  calc
    u = z := congrArg Prod.snd hu
    _ = v := (congrArg Prod.snd hv).symm

/-- A sequence-lift edge has a unique base node. -/
theorem basedAt_unique
    {q r : Node G} {e : Edge G}
    (hq : BasedAt q e) (hr : BasedAt r e) : q = r := by
  rcases e.2 with ⟨q0, t0, x0, y0, z0, hxy0, hext0, hset⟩
  have he : e = mkEdge q0 t0 x0 y0 z0 hxy0 hext0 := by
    apply Subtype.ext
    simpa only [mkEdge] using! hset
  rw [he] at hq hr
  exact (basedAt_eq_base_of_mkEdge hq).trans
    (basedAt_eq_base_of_mkEdge hr).symm

/-- Equality of two displayed lift-edge representations forces equality of
their base nodes. -/
theorem baseNode_eq_of_mkEdge_eq
    {q₁ q₂ t₁ t₂ : Node G} {x₁ y₁ z₁ x₂ y₂ z₂ : V}
    {hxy₁ : G.Adj x₁ y₁} {hxy₂ : G.Adj x₂ y₂}
    {hext₁ : q₁.ExtendsBy (edgeLetter hxy₁) t₁}
    {hext₂ : q₂.ExtendsBy (edgeLetter hxy₂) t₂}
    (heq : mkEdge q₁ t₁ x₁ y₁ z₁ hxy₁ hext₁ =
      mkEdge q₂ t₂ x₂ y₂ z₂ hxy₂ hext₂) :
    q₁ = q₂ := by
  have hbased : BasedAt q₁ (mkEdge q₂ t₂ x₂ y₂ z₂ hxy₂ hext₂) := by
    rw [← heq]
    exact mkEdge_basedAt
  exact basedAt_eq_base_of_mkEdge hbased

/-- Every sequence-lift edge is based at some node. -/
theorem exists_basedAt (e : Edge G) : ∃ q : Node G, BasedAt q e := by
  rcases e.2 with ⟨q, t, x, y, z, hxy, hext, hset⟩
  have he : e = mkEdge q t x y z hxy hext := by
    apply Subtype.ext
    simpa only [mkEdge] using! hset
  rw [he]
  exact ⟨q, mkEdge_basedAt⟩

/-- The canonical base node of a sequence-lift edge. -/
noncomputable def baseNode (e : Edge G) : Node G :=
  Classical.choose (exists_basedAt e)

/-- The selected canonical base node witnesses `BasedAt`. -/
theorem baseNode_basedAt (e : Edge G) : BasedAt (baseNode e) e :=
  Classical.choose_spec (exists_basedAt e)

/-- A node witnesses `BasedAt` exactly when it is the canonical base node. -/
theorem basedAt_iff_baseNode_eq (q : Node G) (e : Edge G) :
    BasedAt q e ↔ q = baseNode e := by
  constructor
  · intro hq
    exact basedAt_unique hq (baseNode_basedAt e)
  · rintro rfl
    exact baseNode_basedAt e

/-- The canonical base node of an explicit lift edge is the displayed base
node. -/
theorem baseNode_mkEdge
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (edgeLetter hxy) t} :
    baseNode (mkEdge q t x y z hxy hext) = q := by
  exact basedAt_unique (baseNode_basedAt _) mkEdge_basedAt

end SequenceLift
end Erdos593
