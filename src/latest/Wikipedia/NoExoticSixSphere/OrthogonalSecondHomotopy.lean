import Wikipedia.NoExoticSixSphere.QuaternionColumnSection
import Wikipedia.NoExoticSixSphere.OrthogonalColumnRetraction
import Wikipedia.NoExoticSixSphere.OrthogonalStableRange
import Wikipedia.NoExoticSixSphere.OrthogonalBottDegreeShift
import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.RankSixComplexStructurePiOne

/-!
# Nullhomotopy of actual two-sphere families in the rank-three orthogonal group

The checked Bott comparison and spinor contraction give the rank-six
second-group vanishing. Stable-range reflection descends to rank four.
The quaternionic column section supplies the remaining retraction to rank
three, where the strict stable-range inequality no longer applies.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere

namespace SmoothCube

theorem sphereMap_nullhomotopic_of_subsingleton {n : ℕ} (hn : 0 < n)
    {Y : Type*} [TopologicalSpace Y] (f : C(Sphere n, Y))
    [Subsingleton (HomotopyGroup (Fin n) Y (f (spherePole n)))] :
    f.Homotopic (ContinuousMap.const _ (f (spherePole n))) := by
  let F : BasedMap n Y (f (spherePole n)) := ⟨f, rfl⟩
  let C : BasedMap n Y (f (spherePole n)) :=
    ⟨ContinuousMap.const _ (f (spherePole n)), rfl⟩
  exact ((sphereClass_eq_iff hn F C).mp (Subsingleton.elim _ _)).homotopic

end SmoothCube

namespace OrthogonalSecondHomotopy

open GLOrthonormalization OrthogonalStabilization

theorem rankSix_subsingleton (a : OrthogonalOperators 6) :
    Subsingleton (HomotopyGroup (Fin 2) (OrthogonalOperators 6) a) := by
  let q : RankSixComplexProjection.UnitSpinor :=
    Classical.choice (NormedSpace.sphere_nonempty_rclike ℂ zero_le_one)
  let J := RankSixComplexProjection.fromSpinor q
  let := RankSixComplexProjection.complexStructure_piOne_subsingleton J
  let e := OrthogonalPolygon.bottDegreeShiftMulEquiv 1 a
    (a * OrthogonalExponential.exp (Real.pi • J.val))
    (by simpa only [inv_mul_cancel_left] using OrthogonalComplexStructures.exp_pi J)
    J (by decide : 1 + 3 < 6)
  exact e.symm.injective.subsingleton

theorem rankSix_nullhomotopic (f : C(Sphere 2, OrthogonalOperators 6)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let := rankSix_subsingleton (f (spherePole 2))
  exact ⟨f (spherePole 2),
    SmoothCube.sphereMap_nullhomotopic_of_subsingleton (by decide) f⟩

theorem rankFour_nullhomotopic (f : C(Sphere 2, OrthogonalOperators 4)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  sphereOrthogonalVanishing_descends (by decide : 2 + 1 < 4) 6 (by decide)
    rankSix_nullhomotopic f

theorem rankThree_nullhomotopic (f : C(Sphere 2, OrthogonalOperators 3)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let v := QuaternionColumnSection.column
  obtain ⟨c, hc⟩ := rankFour_nullhomotopic (stabilizeMap v f)
  exact OrthogonalColumnSection.nullhomotopic_of_stabilized v
    QuaternionColumnSection.sectionMap QuaternionColumnSection.rotation_column
    QuaternionColumnSection.rotation_basepoint f c hc

theorem generalLinear_rankThree_nullhomotopic
    (f : C(Sphere 2, InvertibleOperators (Vector 3))) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  nullhomotopic_of_orthogonal_nullhomotopic 3 rankThree_nullhomotopic f

end OrthogonalSecondHomotopy

end NoExoticSixSphere
