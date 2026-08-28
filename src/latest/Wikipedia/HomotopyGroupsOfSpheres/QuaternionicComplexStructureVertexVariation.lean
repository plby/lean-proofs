import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonTangent

/-! # Actual exponential variations of complex-structure polygon vertices -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

def vertexVariation (v : ComplexStructureVertices.Space n m) (W : Model v) (s : ℝ) :
    ComplexStructureVertices.Space n m := fun i ↦ exponentialCurve (v i) (W i) s

theorem forget_vertexVariation (v : ComplexStructureVertices.Space n m) (W : Model v) (s : ℝ) :
    forget (vertexVariation v W s) = Polygon.vertexVariation (forget v) (modelInclusion v W) s :=
  funext (fun i ↦ exponentialCurve_toSymplectic (v i) (W i) s)

theorem continuous_vertexVariation (v : ComplexStructureVertices.Space n m) (W : Model v) :
    Continuous (vertexVariation v W) :=
  continuous_pi (fun i ↦ continuous_exponentialCurve (v i) (W i))

theorem vertexVariation_zero (v : ComplexStructureVertices.Space n m) (W : Model v) :
    vertexVariation v W 0 = v := funext (fun i ↦ exponentialCurve_zero (v i) (W i))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
