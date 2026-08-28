import Wikipedia.HopfProblem.CuspHoneycombLinearBridgeSides
import Wikipedia.HopfProblem.CuspHoneycombHexagonBoundary

/-!
# Opposite-side coordinates differ by the exact lattice translation

Reversing the unit-interval parameter on the opposite standard side changes
the corresponding dual-plane coordinate by minus the side's integral ray.
Consequently the whole common edge is carried to the opposite common edge.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

theorem standard_vertex_opposite (k : Fin 6) :
    CuspHoneycombHexagon.vertex (k + 3) = -CuspHoneycombHexagon.vertex k := by
  funext i
  change (ToricComponent.hexagonRay (k + 3) i : ℝ) =
    -(ToricComponent.hexagonRay k i : ℝ)
  rw [ToricComponent.hexagonRay_opposite]
  simp only [Pi.neg_apply, Int.cast_neg]

/-- The transformed integral ray is the sum of its side's two standard endpoints. -/
theorem dual_latticePoint_ray (k : Fin 6) :
    dualStandardLinearEquiv (latticePoint (ToricComponent.hexagonRay k)) =
      CuspHoneycombHexagon.vertex (k - 1) + CuspHoneycombHexagon.vertex k := by
  have h : ∀ k : Fin 6,
      ToricComponent.hexagonRay (k - 1) 0 + ToricComponent.hexagonRay k 0 =
        2 * ToricComponent.hexagonRay k 0 + ToricComponent.hexagonRay k 1 ∧
      ToricComponent.hexagonRay (k - 1) 1 + ToricComponent.hexagonRay k 1 =
        ToricComponent.hexagonRay k 1 - ToricComponent.hexagonRay k 0 := by decide
  funext i
  fin_cases i
  · change 2 * (ToricComponent.hexagonRay k 0 : ℝ) +
        (ToricComponent.hexagonRay k 1 : ℝ) =
      (ToricComponent.hexagonRay (k - 1) 0 : ℝ) + (ToricComponent.hexagonRay k 0 : ℝ)
    exact_mod_cast (h k).1.symm
  · change (ToricComponent.hexagonRay k 1 : ℝ) -
        (ToricComponent.hexagonRay k 0 : ℝ) =
      (ToricComponent.hexagonRay (k - 1) 1 : ℝ) + (ToricComponent.hexagonRay k 1 : ℝ)
    exact_mod_cast (h k).2.symm

/-- The reversed opposite-side parameter differs by exactly the actual lattice ray. -/
theorem dual_sideInterval_opposite (k : Fin 6) (t : unitInterval) :
    dualStandardPlaneHomeomorph.symm
        (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
      dualStandardPlaneHomeomorph.symm
        (CuspHoneycombHexagon.sideIntervalHomeomorph k t : Plane) -
          latticePoint (ToricComponent.hexagonRay k) := by
  change dualStandardLinearEquiv.symm
      (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
    dualStandardLinearEquiv.symm (CuspHoneycombHexagon.sideIntervalHomeomorph k t : Plane) -
      latticePoint (ToricComponent.hexagonRay k)
  apply dualStandardLinearEquiv.injective
  simp only [map_sub, LinearEquiv.apply_symm_apply, dual_latticePoint_ray]
  have hidx : ∀ k : Fin 6, k + 3 - 1 = (k - 1) + 3 := by decide
  simp only [CuspHoneycombHexagon.sideIntervalHomeomorph_apply, unitInterval.coe_symm_eq,
    hidx, standard_vertex_opposite]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The same translation identity holds for the entire closed sides, including endpoints. -/
theorem dual_side_sub_latticePoint_image (k : Fin 6) :
    (fun x : Plane => x - latticePoint (ToricComponent.hexagonRay k)) ''
        (dualStandardPlaneHomeomorph.symm '' CuspHoneycombHexagon.side k) =
      dualStandardPlaneHomeomorph.symm '' CuspHoneycombHexagon.side (k + 3) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨t, ht⟩ := (CuspHoneycombHexagon.sideIntervalHomeomorph k).surjective ⟨z, hz⟩
    have ht' : (CuspHoneycombHexagon.sideIntervalHomeomorph k t : Plane) = z :=
      congrArg Subtype.val ht
    refine ⟨(CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane),
      (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) (unitInterval.symm t)).property, ?_⟩
    rw [dual_sideInterval_opposite, ht']
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨t, ht⟩ :=
      (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3)).surjective ⟨z, hz⟩
    have ht' : (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) t : Plane) = z :=
      congrArg Subtype.val ht
    refine ⟨dualStandardPlaneHomeomorph.symm
      (CuspHoneycombHexagon.sideIntervalHomeomorph k (unitInterval.symm t) : Plane), ?_, ?_⟩
    · exact ⟨_, (CuspHoneycombHexagon.sideIntervalHomeomorph k (unitInterval.symm t)).property,
        rfl⟩
    · change dualStandardPlaneHomeomorph.symm
        (CuspHoneycombHexagon.sideIntervalHomeomorph k (unitInterval.symm t) : Plane) -
          latticePoint (ToricComponent.hexagonRay k) = dualStandardPlaneHomeomorph.symm z
      rw [← dual_sideInterval_opposite]
      simp only [unitInterval.symm_symm, ht']

theorem baseCell_edge_sub_latticePoint_image (k : Fin 6) :
    (fun x : Plane => x - latticePoint (ToricComponent.hexagonRay k)) ''
        (baseCell ∩ cell (ToricComponent.hexagonRay k)) =
      baseCell ∩ cell (ToricComponent.hexagonRay (k + 3)) := by
  rw [← dual_image_side k, ← dual_image_side (k + 3)]
  exact dual_side_sub_latticePoint_image k

end Wikipedia.HopfProblem.CuspHoneycombTiling
