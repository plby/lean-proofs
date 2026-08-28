import Wikipedia.NoExoticSixSphere.ComplexStructureCoordinates

/-!
# The actual fixed-column fiber of orthogonal complex structures

Restriction to the complement of the fixed complex line and reconstruction
by a standard quarter-turn are continuous inverse maps. Thus the column fiber
in rank `n + 2` is homeomorphic to the actual rank-`n` complex-structure space.
-/

namespace NoExoticSixSphere.ComplexStructureColumnFiber

open GLOrthonormalization OrthogonalComplexStructures ComplexStructureCoordinates

variable {n : ℕ} (v : UnitSphere (Vector (n + 2))) (c : Sphere n)

noncomputable def residual (J : Space (n + 2)) (hJ : column v J = c) : Space n :=
  ⟨⟨ComplexStructureBlock.tailMap (adapted v c J),
      ComplexStructureBlock.tailMap_skew (adapted v c J)
        (adapted_skew v c J) (adapted_square v c J)
        ((column_eq_iff_adapted_first v c J).mp hJ)⟩,
    ComplexStructureBlock.tailMap_square (adapted v c J)
      (adapted_skew v c J) (adapted_square v c J)
      ((column_eq_iff_adapted_first v c J).mp hJ)⟩

noncomputable def reconstruct (K : Space n) : Space (n + 2) :=
  ⟨⟨(coordinates v c).symm.conjStarAlgEquiv (ComplexStructureBlock.block K.1.1),
      ComplexStructureCoordinates.conjugate_skew (coordinates v c).symm
        (ComplexStructureBlock.block K.1.1) (ComplexStructureBlock.block_skew K.1.1 K.1.2)⟩,
    ComplexStructureCoordinates.conjugate_square (coordinates v c).symm
      (ComplexStructureBlock.block K.1.1) (ComplexStructureBlock.block_square K.1.1 K.2)⟩

theorem adapted_reconstruct (K : Space n) :
    adapted v c (reconstruct v c K) = ComplexStructureBlock.block K.1.1 :=
  (coordinates v c).conjStarAlgEquiv.apply_symm_apply _

theorem reconstruct_column (K : Space n) : column v (reconstruct v c K) = c := by
  apply (column_eq_iff_adapted_first v c _).mpr
  rw [adapted_reconstruct, ComplexStructureBlock.block_firstVector]

theorem reconstruct_residual (J : Space (n + 2)) (hJ : column v J = c) :
    reconstruct v c (residual v c J hJ) = J := by
  apply Subtype.ext
  apply Subtype.ext
  change (coordinates v c).conjStarAlgEquiv.symm
    (ComplexStructureBlock.block (ComplexStructureBlock.tailMap (adapted v c J))) = J.1.1
  rw [← ComplexStructureBlock.eq_block_tailMap (adapted v c J)
    (adapted_skew v c J) (adapted_square v c J)
    ((column_eq_iff_adapted_first v c J).mp hJ)]
  exact (coordinates v c).conjStarAlgEquiv.symm_apply_apply J.1.1

theorem residual_reconstruct (K : Space n) :
    residual v c (reconstruct v c K) (reconstruct_column v c K) = K := by
  apply Subtype.ext
  apply Subtype.ext
  change ComplexStructureBlock.tailMap (adapted v c (reconstruct v c K)) = K.1.1
  rw [adapted_reconstruct, ComplexStructureBlock.tailMap_block]

theorem continuous_reconstruct : Continuous (reconstruct v c) := by
  have hblock := ComplexStructureBlock.continuous_block
    (fun K : Space n ↦ K.1.1) (continuous_subtype_val.comp continuous_subtype_val)
  have hc := (ComplexStructureCoordinates.continuous_conjugate (coordinates v c).symm).comp hblock
  exact (hc.subtype_mk _).subtype_mk _

variable {X : Type*} [TopologicalSpace X]

theorem continuous_residual (J : X → Space (n + 2)) (hJ : Continuous J)
    (hcol : ∀ x, column v (J x) = c) :
    Continuous (fun x ↦ residual v c (J x) (hcol x)) := by
  have htail := ComplexStructureBlock.continuous_tailMap (fun x ↦ adapted v c (J x))
    ((continuous_adapted v c).comp hJ)
  exact (htail.subtype_mk _).subtype_mk _

abbrev Fiber := {J : Space (n + 2) // column v J = c}

noncomputable def homeomorph : Fiber v c ≃ₜ Space n where
  toFun J := residual v c J.1 J.2
  invFun K := ⟨reconstruct v c K, reconstruct_column v c K⟩
  left_inv J := Subtype.ext (reconstruct_residual v c J.1 J.2)
  right_inv := residual_reconstruct v c
  continuous_toFun := continuous_residual v c Subtype.val continuous_subtype_val Subtype.property
  continuous_invFun := (continuous_reconstruct v c).subtype_mk _

noncomputable def reconstructMap (K : C(X, Space n)) : C(X, Space (n + 2)) :=
  ⟨fun x ↦ reconstruct v c (K x), (continuous_reconstruct v c).comp K.continuous⟩

noncomputable def residualMap (J : C(X, Space (n + 2)))
    (hJ : ∀ x, column v (J x) = c) : C(X, Space n) :=
  ⟨fun x ↦ residual v c (J x) (hJ x), continuous_residual v c J J.continuous hJ⟩

theorem reconstructMap_residualMap (J : C(X, Space (n + 2)))
    (hJ : ∀ x, column v (J x) = c) : reconstructMap v c (residualMap v c J hJ) = J := by
  apply ContinuousMap.ext
  intro x
  exact reconstruct_residual v c (J x) (hJ x)

theorem homotopic_reconstructMap {K L : C(X, Space n)} (h : K.Homotopic L) :
    (reconstructMap v c K).Homotopic (reconstructMap v c L) :=
  (ContinuousMap.Homotopic.refl
    (⟨reconstruct v c, continuous_reconstruct v c⟩ : C(Space n, Space (n + 2)))).comp h

theorem reconstructMap_const (K : Space n) :
    reconstructMap v c (ContinuousMap.const X K) =
      ContinuousMap.const X (reconstruct v c K) := rfl

end NoExoticSixSphere.ComplexStructureColumnFiber
