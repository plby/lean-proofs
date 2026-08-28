import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottDegreeShift
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumPathFamily
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-!
# The first symplectic Bott comparison uses the original minimum-path map

The general endpoint construction agrees with the previously defined map
`MinimumPaths.loopMap` at the identity. The comparison also transports through
the actual matrix/operator homeomorphism, preserving the identity base point.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization Exponential

variable {n : ℕ}

theorem identity_antipodal (n : ℕ) :
    ((1 : symplecticSubgroup n)⁻¹ * ComplexStructures.antipode n).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by
  rw [inv_one, one_mul, ComplexStructures.antipode_operator]

theorem minimumPathMap_eq_pathMap (n : ℕ) :
    minimumPathMap 1 (ComplexStructures.antipode n) (identity_antipodal n) =
      MinimumPaths.pathMap n := by
  apply ContinuousMap.ext
  intro J
  apply Path.ext
  funext t
  change 1 * exp ((t : ℝ) • (Real.pi • J.val)) =
    exp (((t : ℝ) * Real.pi) • J.val)
  rw [one_mul, smul_smul]

theorem bottLoopMap_eq_loopMap (J₀ : ComplexStructures.Space n) :
    bottLoopMap 1 (ComplexStructures.antipode n) (identity_antipodal n) J₀ =
      MinimumPaths.loopMap J₀ := by
  simp only [bottLoopMap, minimumPathMap_eq_pathMap, MinimumPaths.loopMap]

theorem bottHomotopyMap_eq_original (d : ℕ) (J₀ : ComplexStructures.Space n) :
    bottHomotopyMap d 1 (ComplexStructures.antipode n) (identity_antipodal n) J₀ =
      NoExoticSixSphere.HigherHomotopy.map (MinimumPaths.loopMap J₀)
        (MinimumPaths.loopMap_reference J₀) := by
  unfold bottHomotopyMap
  congr 1
  exact bottLoopMap_eq_loopMap J₀

/-- The isomorphism acts on a representative by the original loop map and
ordinary cubical uncurrying. -/
theorem bottDegreeShiftMulEquiv_mk (d : ℕ) [NeZero d]
    (J₀ : ComplexStructures.Space n) (hd : d + 1 < n)
    (p : GenLoop (Fin d) (ComplexStructures.Space n) J₀) :
    bottDegreeShiftMulEquiv d 1 (ComplexStructures.antipode n)
      (identity_antipodal n) J₀ hd (Quotient.mk' p) =
      Quotient.mk' (NoExoticSixSphere.GeneralizedLoopCurrying.uncurry
        (NoExoticSixSphere.HigherHomotopy.genLoopMap (MinimumPaths.loopMap J₀)
          (MinimumPaths.loopMap_reference J₀) p)) := by
  change NoExoticSixSphere.GeneralizedLoopCurrying.homotopyEquiv d 1
    (bottHomotopyMap d 1 (ComplexStructures.antipode n) (identity_antipodal n) J₀
      (Quotient.mk' p)) = _
  rw [bottHomotopyMap_eq_original, NoExoticSixSphere.HigherHomotopy.map_mk,
    NoExoticSixSphere.GeneralizedLoopCurrying.homotopyEquiv_mk]

/-- The native degree shift, for the original matrix model of `Sp(n+1)`. -/
def bottMatrixDegreeShiftMulEquiv (d : ℕ) [NeZero d]
    (J₀ : ComplexStructures.Space n) (hd : d + 1 < n) :
    HomotopyGroup (Fin d) (ComplexStructures.Space n) J₀ ≃*
      HomotopyGroup (Fin (d + 1)) (SpGroup (Fin (n + 1))) 1 :=
  (bottDegreeShiftMulEquiv d 1 (ComplexStructures.antipode n)
    (identity_antipodal n) J₀ hd).trans
    (pointedHomeomorphMulEquiv (N := Fin (d + 1)) (symplecticHomeomorph n)
      1 1 (map_one (symplecticMulEquiv n))).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
