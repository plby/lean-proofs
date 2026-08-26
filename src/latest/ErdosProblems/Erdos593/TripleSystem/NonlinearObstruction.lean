import ErdosProblems.Erdos593.TripleSystem.EmbeddingLinearity
import ErdosProblems.Erdos593.TripleSystem.Obligatory

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Nonlinearity obstruction to obligatoriness

This is a generic negative-host endpoint.  It says that a non-linear source
cannot be obligatory whenever an uncountably chromatic linear host in the
ambient universes is available.  Constructing such a host is intentionally a
separate Erdős--Rado task.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} {W : Type u} {D : Type v}
variable {F : TripleSystem V E} {H : TripleSystem W D}

/-- A non-linear source fails to be obligatory in the presence of a linear
host of uncountable chromatic cardinality. -/
theorem not_isObligatory_of_not_linear_of_linear_highChromatic
    [DecidableEq W]
    (hnotlinear : ¬ F.Linear) (hHlinear : H.Linear)
    (hchi : Cardinal.aleph0 < H.chromaticCardinal) : ¬ F.IsObligatory := by
  intro hF
  rcases hF W D H hchi with ⟨f⟩
  exact hnotlinear (f.source_linear_of_target_linear hHlinear)

end TripleSystem

end Erdos593
