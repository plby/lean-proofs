import ErdosProblems.Erdos593.TripleSystem.EmbeddingEdgeRestriction
import ErdosProblems.Erdos593.TripleSystem.ObligatoryIsolatedReduction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite linear image traces

An embedding is generally not induced, but its selected host-edge indices form
an exact edge restriction.  For a finite linear source this restriction is
finite, linear, and isomorphic to the source after isolated vertices have
been removed.
-/

namespace Erdos593

universe u v w x

namespace TripleSystem

namespace Embedding

variable {V : Type u} {E : Type v} {W : Type w} {D : Type x}
variable {F : TripleSystem V E} {H : TripleSystem W D}

/-- A finite linear source with no isolated vertices determines a finite
linear exact host-edge trace, isomorphic to the source. -/
theorem finiteLinear_imageTrace [Fintype E]
    (f : F.Embedding H) (hF : F.HasNoIsolatedPoints) (hlinear : F.Linear) :
    f.edgeImage.Finite ∧
      (H.edgeRestriction f.edgeImage).Linear ∧
      Nonempty (Iso F (H.edgeRestriction f.edgeImage)) := by
  refine ⟨Set.finite_range f.edge, f.imageEdgeRestriction_linear hF hlinear,
    ⟨f.imageEdgeRestrictionIso hF⟩⟩

/-- Removing isolated source vertices yields the same finite linear exact
trace for an arbitrary finite linear source. -/
theorem finiteLinear_isolatedReduction_imageTrace [Fintype E]
    (f : F.Embedding H) (hlinear : F.Linear) :
    let f' := (isolatedReductionEmbedding F).trans f
    f'.edgeImage.Finite ∧
      (H.edgeRestriction f'.edgeImage).Linear ∧
      Nonempty (Iso F.isolatedReduction (H.edgeRestriction f'.edgeImage)) := by
  dsimp
  have hlinear' : F.isolatedReduction.Linear :=
    F.isolatedReduction_linear hlinear
  refine ⟨Set.finite_range _, ?_, ?_⟩
  · exact ((isolatedReductionEmbedding F).trans f).imageEdgeRestriction_linear
      F.isolatedReduction_hasNoIsolatedPoints hlinear'
  · exact ⟨((isolatedReductionEmbedding F).trans f).imageEdgeRestrictionIso
      F.isolatedReduction_hasNoIsolatedPoints⟩

end Embedding

end TripleSystem

end Erdos593
