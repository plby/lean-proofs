import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygon
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVertexFamilies
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonStationarity

/-!
# Reversible tangent directions and actual polygon velocity jumps

Each edge logarithm is reversible at both endpoints and has trace zero.
Consequently the incoming-minus-outgoing velocity at a vertex is an allowed
direction in the original symmetric determinant-one space.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace ComplexSkewMatrices

theorem toOrthogonalSkew_injective {N : Type*} [Fintype N] [DecidableEq N] :
    Function.Injective (toOrthogonalSkew (N := N)) := by
  intro K L h
  apply Subtype.ext
  exact ComplexMatrixRealRepresentation.action_injective (congrArg Subtype.val h)

end ComplexSkewMatrices

namespace QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

def reversibleDirections (B : SpecialSpace N) : Submodule ℝ (ComplexSkewMatrices.Space N) where
  carrier := {K | K.val.trace = 0 ∧ K.val.transpose * B.val.val.val = B.val.val.val * K.val}
  zero_mem' := by simp
  add_mem' := by
    intro K L hK hL
    change (K.val + L.val).trace = 0 ∧
      (K.val + L.val).transpose * B.val.val.val = B.val.val.val * (K.val + L.val)
    simp only [Matrix.trace_add, hK.1, hL.1, add_zero, Matrix.transpose_add,
      add_mul, mul_add, hK.2, hL.2, and_self]
  smul_mem' := by
    intro c K hK
    change (c • K.val).trace = 0 ∧
      (c • K.val).transpose * B.val.val.val = B.val.val.val * (c • K.val)
    simp only [Matrix.trace_smul, hK.1, smul_zero, Matrix.transpose_smul,
      smul_mul_assoc, mul_smul_comm, hK.2, and_self]

abbrev ReversibleDirection (B : SpecialSpace N) := ↥(reversibleDirections B)

namespace ShortLog

theorem generator_reversible_end {B C : SpecialSpace N} (h : (B, C) ∈ domain N) :
    (generator B C).val.transpose * C.val.val.val = C.val.val.val * (generator B C).val := by
  have hs := generator_reversible (swap_mem_domain h)
  rw [generator_swap h] at hs
  simpa only [Submodule.coe_neg, Matrix.transpose_neg, neg_mul, mul_neg, neg_inj] using hs

theorem generator_mem_start {B C : SpecialSpace N} (h : (B, C) ∈ domain N) :
    generator B C ∈ reversibleDirections B := ⟨generator_trace h, generator_reversible h⟩

theorem generator_mem_end {B C : SpecialSpace N} (h : (B, C) ∈ domain N) :
    generator B C ∈ reversibleDirections C := ⟨generator_trace h, generator_reversible_end h⟩

end ShortLog

namespace Polygon

open VertexSpace ComplexMatrixRealRepresentation

variable {m : ℕ}

def edgeVelocity (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (i : Fin (m + 1)) : ComplexSkewMatrices.Space N :=
  (1 / (τ i.succ - τ i.castSucc)) • generator a b v i

def velocityJump (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (j : Fin m) : ComplexSkewMatrices.Space N :=
  edgeVelocity a b τ v j.castSucc - edgeVelocity a b τ v j.succ

theorem edgeVelocity_forget (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    NoExoticSixSphere.OrthogonalPolygon.edgeVelocity (specialOrthogonal a) (specialOrthogonal b)
      τ (forget v) i = ComplexSkewMatrices.toOrthogonalSkew (edgeVelocity a b τ v i) := by
  rw [NoExoticSixSphere.OrthogonalPolygon.edgeVelocity, generator_forget a b hv i,
    edgeVelocity, map_smul]

theorem velocityJump_forget (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) (j : Fin m) :
    NoExoticSixSphere.OrthogonalPolygon.velocityJump (specialOrthogonal a) (specialOrthogonal b)
      τ (forget v) j = ComplexSkewMatrices.toOrthogonalSkew (velocityJump a b τ v j) := by
  rw [NoExoticSixSphere.OrthogonalPolygon.velocityJump, edgeVelocity_forget a b τ hv,
    edgeVelocity_forget a b τ hv, velocityJump, map_sub]

theorem incoming_generator_mem (a b : SpecialSpace N) {v : VertexSpace.Space N m}
    (hv : v ∈ admissible a b m) (j : Fin m) :
    generator a b v j.castSucc ∈ reversibleDirections (v j) := by
  have h := ShortLog.generator_mem_end (hv j.castSucc)
  change generator a b v j.castSucc ∈ reversibleDirections (vertices a b v j.castSucc.succ) at h
  rwa [vertices_interior] at h

theorem outgoing_generator_mem (a b : SpecialSpace N) {v : VertexSpace.Space N m}
    (hv : v ∈ admissible a b m) (j : Fin m) :
    generator a b v j.succ ∈ reversibleDirections (v j) := by
  have h := ShortLog.generator_mem_start (hv j.succ)
  change generator a b v j.succ ∈ reversibleDirections (vertices a b v j.castSucc.succ) at h
  rwa [vertices_interior] at h

theorem velocityJump_mem (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) (j : Fin m) :
    velocityJump a b τ v j ∈ reversibleDirections (v j) :=
  (reversibleDirections (v j)).sub_mem
    ((reversibleDirections (v j)).smul_mem _ (incoming_generator_mem a b hv j))
    ((reversibleDirections (v j)).smul_mem _ (outgoing_generator_mem a b hv j))

def jumpDirection (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) :
    (j : Fin m) → ReversibleDirection (v j) :=
  fun j ↦ ⟨velocityJump a b τ v j, velocityJump_mem a b τ hv j⟩

def vertexVariation (v : VertexSpace.Space N m)
    (W : (j : Fin m) → ReversibleDirection (v j)) (s : ℝ) : VertexSpace.Space N m :=
  fun j ↦ reversibleStep (v j) (W j).val (W j).property.1 (W j).property.2 s

theorem vertexVariation_zero (v : VertexSpace.Space N m)
    (W : (j : Fin m) → ReversibleDirection (v j)) : vertexVariation v W 0 = v :=
  funext (fun j ↦ reversibleStep_zero (v j) (W j).val (W j).property.1 (W j).property.2)

theorem contMDiff_vertexVariation (v : VertexSpace.Space N m)
    (W : (j : Fin m) → ReversibleDirection (v j)) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model N m) ∞ (vertexVariation v W) := by
  apply VertexSpace.contMDiff_iff_coordinatewise.mpr
  intro j
  exact contMDiff_reversibleStep (v j) (W j).val (W j).property.1 (W j).property.2

theorem forget_vertexVariation (v : VertexSpace.Space N m)
    (W : (j : Fin m) → ReversibleDirection (v j)) (s : ℝ) :
    forget (vertexVariation v W s) = NoExoticSixSphere.OrthogonalPolygon.vertexVariation
      (forget v) (fun j ↦ ComplexSkewMatrices.toOrthogonalSkew (W j).val) s := by
  funext j
  change orthogonal ((v j).val.val * ComplexSkewMatrices.exponential (s • (W j).val)) = _
  rw [map_mul, ComplexSkewMatrices.orthogonal_exponential, map_smul]
  rfl

end Polygon
end QuaternionicSymmetricMatrices
end Wikipedia.HomotopyGroupsOfSpheres
