import ErdosProblems.Erdos593.TripleSystem.SequenceLiftFiniteTrace

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical base fibres for sequence lifts

The canonical base node defines local fibres within any selected family of
sequence-lift edges.  On a linear edge restriction, the canonical base letter is
injective within each such fibre.  This supplies fibre-local cardinality
transfer without asserting that a global finite-trace decomposition exists.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The edges of a selected family whose canonical base node is `q`. -/
def baseFiber (S : Set (Edge G)) (q : Node G) : Set (Edge G) :=
  {e | e ∈ S ∧ baseNode e = q}

@[simp]
theorem mem_baseFiber {S : Set (Edge G)} {q : Node G} {e : Edge G} :
    e ∈ baseFiber S q ↔ e ∈ S ∧ baseNode e = q :=
  Iff.rfl

/-- Every canonical base fibre is a subfamily of its ambient edge family. -/
theorem baseFiber_subset (S : Set (Edge G)) (q : Node G) :
    baseFiber S q ⊆ S := by
  intro e he
  exact he.1

/-- On a linear restriction, a canonical base letter determines an edge inside
a fixed canonical base fibre. -/
theorem baseLetter_injOn_baseFiber_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).edgeRestriction S).Linear) :
    Set.InjOn baseLetter (baseFiber S q) := by
  intro e₁ he₁ e₂ he₂ hletter
  exact eq_of_same_baseNode_baseLetter_of_mem_of_linear
    hlin he₁.1 he₂.1 (he₁.2.trans he₂.2.symm) hletter

/-- On a canonical base fibre of a linear restriction, base letters preserve
extended natural cardinality. -/
theorem baseLetter_image_encard_eq_on_baseFiber_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).edgeRestriction S).Linear) :
    (baseLetter '' baseFiber S q).encard = (baseFiber S q).encard := by
  exact (baseLetter_injOn_baseFiber_of_linear q hlin).encard_image

/-- On a canonical base fibre of a linear restriction, base-letter images are
finite exactly when the fibre is finite. -/
theorem baseLetter_image_finite_iff_on_baseFiber_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).edgeRestriction S).Linear) :
    (baseLetter '' baseFiber S q).Finite ↔ (baseFiber S q).Finite := by
  constructor
  · intro himage
    exact Set.Finite.of_finite_image himage
      (baseLetter_injOn_baseFiber_of_linear q hlin)
  · intro hfiber
    exact hfiber.image baseLetter

/-- On a canonical base fibre of a linear restriction, base letters preserve
natural cardinality.  The preceding `encard` theorem is the nondegenerate
formulation for an infinite fibre. -/
theorem ncard_baseLetter_image_eq_on_baseFiber_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).edgeRestriction S).Linear) :
    (baseLetter '' baseFiber S q).ncard = (baseFiber S q).ncard := by
  exact (baseLetter_injOn_baseFiber_of_linear q hlin).ncard_image

/-- The canonical base fibre of an embedded source is indexed exactly by the
source edges whose images have the selected base node. -/
theorem baseFiber_edgeImage_eq_range
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) (q : Node G) :
    baseFiber f.edgeImage q =
      Set.range (fun i : {i : E // baseNode (f.edge i) = q} => f.edge i) := by
  ext e
  constructor
  · rintro ⟨⟨i, hi⟩, hbase⟩
    refine ⟨⟨i, ?_⟩, hi⟩
    simpa only [hi] using! hbase
  · rintro ⟨i, hi⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [← hi]
    exact i.property

/-- A finite linear source with no isolated points has finite base-letter
image at every canonical base fibre, with one base letter per fibre edge. -/
theorem finiteLinear_baseFiber_baseLetter_image
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E]
    (f : F.Embedding (system G)) (hF : F.HasNoIsolatedPoints)
    (hlinear : F.Linear) (q : Node G) :
    (baseLetter '' baseFiber f.edgeImage q).Finite ∧
      (baseLetter '' baseFiber f.edgeImage q).ncard =
        (baseFiber f.edgeImage q).ncard := by
  have hlin : ((system G).edgeRestriction f.edgeImage).Linear :=
    f.imageEdgeRestriction_linear hF hlinear
  constructor
  · exact ((Set.finite_range f.edge).subset (baseFiber_subset _ _)).image baseLetter
  · exact ncard_baseLetter_image_eq_on_baseFiber_of_linear q hlin

end SequenceLift

end Erdos593
