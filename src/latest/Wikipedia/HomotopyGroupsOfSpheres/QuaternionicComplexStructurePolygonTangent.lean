import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygon
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonDifferential

/-!
# The actual tangent directions and velocity jumps of complex-structure polygons

The inclusion of each local vertex model intertwines the two Cayley inverse
charts. Edge logarithms anticommute at both endpoints, so the full symplectic
velocity jump belongs to the smaller complex-structure tangent model.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

namespace ComplexStructures.ShortLog

variable {n : ℕ}

theorem generator_anticommute_end {J J' : Space n} (h : (J, J') ∈ domain n) :
    J'.val.val.comp (generator J J').val = -((generator J J').val.comp J'.val.val) := by
  have hs := generator_anticommute (swap_mem_domain h)
  rw [generator_swap h] at hs
  apply ContinuousLinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hs x
  change J'.val.val (-((generator J J').val x)) = -(-((generator J J').val (J'.val.val x))) at hx
  rw [map_neg, neg_neg] at hx
  exact neg_eq_iff_eq_neg.mp hx

end ComplexStructures.ShortLog

namespace ComplexStructureVertices

open ComplexStructures

variable {n m : ℕ}

def modelInclusion (v : Space n m) : Model v →L[ℝ] VertexSpace.Model n m where
  toFun W i := antiSkewToSkew (v i) (W i)
  map_add' W Z := funext (fun i ↦ (antiSkewToSkew (v i)).map_add (W i) (Z i))
  map_smul' c W := funext (fun i ↦ (antiSkewToSkew (v i)).map_smul c (W i))
  cont := continuous_pi (fun i ↦ (continuous_antiSkewToSkew (v i)).comp (continuous_apply i))

theorem modelInclusion_apply (v : Space n m) (W : Model v) (i : Fin m) :
    modelInclusion v W i = antiSkewToSkew (v i) (W i) := rfl

theorem forget_chart_symm (v : Space n m) (W : Model v) :
    forget ((atVertices v).symm W) =
      (VertexSpace.atVertices (forget v)).symm (modelInclusion v W) := by
  funext i
  change toSymplectic (Cayley.point (v i) (W i)) =
    (CayleyAtlas.atOperator (toSymplectic (v i))).symm (antiSkewToSkew (v i) (W i))
  rw [Cayley.point_toSymplectic, CayleyAtlas.atOperator_symm_apply]

end ComplexStructureVertices

namespace ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

theorem incoming_generator_mem (a b : ComplexStructures.Space n)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) (j : Fin m) :
    (generator a b v j.castSucc).val ∈ antiSkewSubmodule (v j) := by
  refine ⟨(generator a b v j.castSucc).property, ?_⟩
  have h := ShortLog.generator_anticommute_end (hv j.castSucc)
  change (vertices a b v j.castSucc.succ).val.val.comp (generator a b v j.castSucc).val =
    -((generator a b v j.castSucc).val.comp (vertices a b v j.castSucc.succ).val.val) at h
  rw [vertices_interior] at h
  exact h

theorem outgoing_generator_mem (a b : ComplexStructures.Space n)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) (j : Fin m) :
    (generator a b v j.succ).val ∈ antiSkewSubmodule (v j) := by
  refine ⟨(generator a b v j.succ).property, ?_⟩
  have h := ShortLog.generator_anticommute (hv j.succ)
  change (vertices a b v j.castSucc.succ).val.val.comp (generator a b v j.succ).val =
    -((generator a b v j.succ).val.comp (vertices a b v j.castSucc.succ).val.val) at h
  rw [vertices_interior] at h
  exact h

theorem velocityJump_mem (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) (j : Fin m) :
    (Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v) j).val ∈
      antiSkewSubmodule (v j) := by
  let p := antiSkewSubmodule (v j)
  have hin := p.smul_mem (1 / (τ j.castSucc.succ - τ j.castSucc.castSucc))
    (incoming_generator_mem a b hv j)
  have hout := p.smul_mem (1 / (τ j.succ.succ - τ j.succ.castSucc))
    (outgoing_generator_mem a b hv j)
  have h := p.sub_mem hin hout
  simpa only [Polygon.velocityJump, Polygon.edgeVelocity, generator_forget,
    Submodule.coe_sub, Submodule.coe_smul] using h

def jumpDirection (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) : Model v :=
  fun j ↦ ⟨(Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v) j).val,
    velocityJump_mem a b τ hv j⟩

theorem modelInclusion_jumpDirection (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    modelInclusion v (jumpDirection a b τ v hv) =
      Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v) := by
  funext j
  apply Subtype.ext
  rfl

end ComplexStructurePolygon
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
