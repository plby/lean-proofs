import Wikipedia.NoExoticSixSphere.ComplexStructureColumn
import Wikipedia.NoExoticSixSphere.ComplexStructureBlock

/-!
# Orthogonal coordinates adapted to a complex-structure column

Two successive orthogonal splittings place the fixed vector and its prescribed
complex-structure image on the first two coordinate axes. Isometric operator
conjugation preserves the actual skew-adjoint and square-minus-identity equations.
-/

namespace NoExoticSixSphere.ComplexStructureCoordinates

section Conjugation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem conjugate_skew (e : E ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] E) (hA : A.adjoint = -A) :
    (e.conjStarAlgEquiv A).adjoint = -(e.conjStarAlgEquiv A) := by
  change star (e.conjStarAlgEquiv A) = -(e.conjStarAlgEquiv A)
  rw [← map_star]
  change e.conjStarAlgEquiv A.adjoint = -(e.conjStarAlgEquiv A)
  rw [hA, map_neg]

theorem conjugate_square (e : E ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] E)
    (hA : A.comp A = -(1 : E →L[ℝ] E)) :
    (e.conjStarAlgEquiv A).comp (e.conjStarAlgEquiv A) = -(1 : F →L[ℝ] F) := by
  change e.conjStarAlgEquiv A * e.conjStarAlgEquiv A = -(1 : F →L[ℝ] F)
  rw [← map_mul]
  change e.conjStarAlgEquiv (A.comp A) = -(1 : F →L[ℝ] F)
  rw [hA, map_neg, map_one]

theorem continuous_conjugate (e : E ≃ₗᵢ[ℝ] F) : Continuous e.conjStarAlgEquiv :=
  continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

end Conjugation

open GLOrthonormalization ColumnCoordinates OrthogonalComplexStructures

variable {n : ℕ}

local instance dimensionFact (r : ℕ) : Fact (Module.finrank ℝ (Vector (r + 1)) = r + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable def coordinates (v : UnitSphere (Vector (n + 2))) (c : Sphere n) :
    Vector (n + 2) ≃ₗᵢ[ℝ] ComplexStructureBlock.Space (Vector n) :=
  (split (r := n + 1) v).trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ) (split (r := n) c))

theorem coordinates_apply (v : UnitSphere (Vector (n + 2))) (c : Sphere n)
    (x : Vector (n + 2)) :
    coordinates v c x = WithLp.toLp 2 ((split (r := n + 1) v x).fst,
      split (r := n) c (split (r := n + 1) v x).snd) := rfl

theorem coordinates_self (v : UnitSphere (Vector (n + 2))) (c : Sphere n) :
    coordinates v c (v : Vector (n + 2)) = ComplexStructureBlock.firstVector := by
  rw [coordinates_apply, split_self]
  simp [ComplexStructureBlock.firstVector]

theorem coordinates_symm_firstVector (v : UnitSphere (Vector (n + 2))) (c : Sphere n) :
    (coordinates v c).symm ComplexStructureBlock.firstVector = (v : Vector (n + 2)) := by
  rw [← coordinates_self v c, LinearIsometryEquiv.symm_apply_apply]

theorem coordinates_column (v : UnitSphere (Vector (n + 2))) (c : Sphere n)
    (J : Space (n + 2)) :
    coordinates v c (J.1.1 v) = WithLp.toLp 2 ((0 : ℝ), split c (column v J : Vector (n + 1))) := by
  rw [coordinates_apply, split_column]
  rfl

noncomputable def adapted (v : UnitSphere (Vector (n + 2))) (c : Sphere n)
    (J : Space (n + 2)) :
    ComplexStructureBlock.Space (Vector n) →L[ℝ] ComplexStructureBlock.Space (Vector n) :=
  (coordinates v c).conjStarAlgEquiv J.1.1

theorem adapted_apply (v : UnitSphere (Vector (n + 2))) (c : Sphere n)
    (J : Space (n + 2)) (z : ComplexStructureBlock.Space (Vector n)) :
    adapted v c J z = coordinates v c (J.1.1 ((coordinates v c).symm z)) := rfl

theorem adapted_skew (v : UnitSphere (Vector (n + 2))) (c : Sphere n)
    (J : Space (n + 2)) : (adapted v c J).adjoint = -(adapted v c J) :=
  conjugate_skew (coordinates v c) J.1.1 J.1.2

theorem adapted_square (v : UnitSphere (Vector (n + 2))) (c : Sphere n)
    (J : Space (n + 2)) : (adapted v c J).comp (adapted v c J) =
      -(1 : ComplexStructureBlock.Space (Vector n) →L[ℝ] ComplexStructureBlock.Space (Vector n)) :=
  conjugate_square (coordinates v c) J.1.1 J.2

theorem column_eq_iff_adapted_first (v : UnitSphere (Vector (n + 2))) (c : Sphere n)
    (J : Space (n + 2)) :
    column v J = c ↔ adapted v c J ComplexStructureBlock.firstVector =
      ComplexStructureBlock.secondVector := by
  rw [adapted_apply, coordinates_symm_firstVector, coordinates_column]
  constructor
  · intro h
    rw [h, split_self]
    rfl
  · intro h
    apply Subtype.ext
    apply (split (r := n) c).injective
    rw [split_self]
    exact congrArg (fun z : ComplexStructureBlock.Space (Vector n) ↦ z.snd) h

theorem continuous_adapted (v : UnitSphere (Vector (n + 2))) (c : Sphere n) :
    Continuous (adapted v c) :=
  (continuous_conjugate (coordinates v c)).comp
    (continuous_subtype_val.comp continuous_subtype_val)

end NoExoticSixSphere.ComplexStructureCoordinates
