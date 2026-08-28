import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPolygons

/-! # Continuous and uniformly bounded orthogonal generators of balanced rotations -/

open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open ComplexMatrixRealRepresentation QuaternionicSymmetricMatrices

theorem continuous_minimumGenerator (n : ℕ) :
    Continuous (minimumGenerator : Space n → RealSymmetricMixing.DirectionSpace (Index n)) := by
  have h : Continuous (fun J : Space n ↦ Real.pi • J.val) := by
    simpa only [] using!
      (continuous_subtype_val : Continuous (fun J : Space n ↦ J.val)).const_smul Real.pi
  exact h.subtype_mk _

theorem continuous_orthogonalMinimumGenerator (n : ℕ) :
    Continuous (fun J : Space n ↦ skewMap (minimumGenerator J)) :=
  (finiteLinearMap_contDiff (skewMap (N := Index n))).continuous.comp
    (continuous_minimumGenerator n)

theorem exists_orthogonalMinimumGenerator_bound (n : ℕ) :
    ∃ B : ℝ, ∀ J : Space n, ‖skewMap (minimumGenerator J)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_orthogonalMinimumGenerator n).norm).bddAbove
  exact ⟨B, fun J ↦ hB ⟨J, rfl⟩⟩

theorem rotation_toOrthogonal {n : ℕ} (J : Space n) (t : ℝ) :
    specialOrthogonal (rotation J (t * Real.pi)) =
      NoExoticSixSphere.OrthogonalExponential.exp (t • skewMap (minimumGenerator J)) := by
  rw [← exponentialCurve_minimumGenerator, specialOrthogonal_curve]

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
