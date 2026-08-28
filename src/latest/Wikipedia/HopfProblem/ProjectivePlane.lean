import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.OpenQuotient

/-!
# The complex projective plane with its scalar-quotient topology

The underlying type is Mathlib's projectivization of `ℂ³`, not a quotient
of the toric surface.  Its topology is the canonical quotient topology
from the nonzero homogeneous vectors by nonzero complex scaling.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ProjectivePlane

abbrev Homogeneous := Fin 3 → ℂ

abbrev NonzeroVector := {v : Homogeneous // v ≠ 0}

abbrev Space := Projectivization ℂ Homogeneous

instance spaceTopology : TopologicalSpace Space :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ Homogeneous)))

/-- The canonical projection of nonzero vectors onto their complex lines. -/
def quotientMap : NonzeroVector → Space := Projectivization.mk' ℂ

theorem quotientMap_isQuotientMap : IsQuotientMap quotientMap :=
  isQuotientMap_quotient_mk'

theorem quotientMap_continuous : Continuous quotientMap :=
  quotientMap_isQuotientMap.continuous

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  quotientMap_isQuotientMap.surjective

theorem quotientMap_eq_iff (v w : NonzeroVector) :
    quotientMap v = quotientMap w ↔ ∃ a : ℂˣ, a • (w : Homogeneous) = (v : Homogeneous) :=
  Projectivization.mk_eq_mk_iff ℂ _ _ _ _

theorem quotientMap_eq_iff_scalar (v w : NonzeroVector) :
    quotientMap v = quotientMap w ↔ ∃ a : ℂ, a • (w : Homogeneous) = (v : Homogeneous) :=
  Projectivization.mk_eq_mk_iff' ℂ _ _ _ _

end Wikipedia.HopfProblem.ProjectivePlane
