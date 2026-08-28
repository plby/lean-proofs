import Wikipedia.NoExoticSixSphere.QuaternionicHopfFiberDivision
import Wikipedia.NoExoticSixSphere.QuaternionicHopfNativeClass

/-!
# The actual right unit-quaternion action on the Hopf fibers

The total space remains the standard seven-sphere. Right multiplication
in both quaternion coordinates preserves its norm and the Hopf polynomial.
The north fiber is parametrized by the ordinary unit quaternion group.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HopfProblem.UnitQuaternionSphere

def rightVector (x : V 8) (q : ℍ) : V 8 := pairCoordinates (first x * q, second x * q)

theorem first_rightVector (x : V 8) (q : ℍ) : first (rightVector x q) = first x * q := by
  change (Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration.planeCoordinates.symm
    (Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration.planeCoordinates
      (WithLp.toLp 2 (first x * q, second x * q)))).fst = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem second_rightVector (x : V 8) (q : ℍ) : second (rightVector x q) = second x * q := by
  change (Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration.planeCoordinates.symm
    (Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration.planeCoordinates
      (WithLp.toLp 2 (first x * q, second x * q)))).snd = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem fiberGroup_normSq (q : FiberGroup) : Quaternion.normSq q.val = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self,
    (mem_unitary_iff_norm_eq_one q.val).mp q.property, one_mul]

theorem rightVector_mem_sphere (x : Sphere 7) (q : FiberGroup) :
    rightVector x.val q.val ∈ Sphere 7 := by
  rw [mem_sphere_zero_iff_norm]
  have hn := normSq_sum (rightVector x.val q.val)
  rw [first_rightVector, second_rightVector, map_mul, map_mul,
    fiberGroup_normSq, mul_one, mul_one, unit_normSq_sum] at hn
  nlinarith [norm_nonneg (rightVector x.val q.val)]

def rightAction (x : Sphere 7) (q : FiberGroup) : Sphere 7 :=
  ⟨rightVector x.val q.val, rightVector_mem_sphere x q⟩

theorem continuous_rightAction : Continuous (fun z : Sphere 7 × FiberGroup ↦
    rightAction z.1 z.2) :=
  (pairCoordinates.continuous.comp
    (((first.continuous.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).prodMk
        ((second.continuous.comp (continuous_subtype_val.comp continuous_fst)).mul
          (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

def fiberInverseMap : C(FiberGroup, FiberGroup) :=
  ⟨Inv.inv, by
    apply Continuous.subtype_mk
    change Continuous (fun q : FiberGroup ↦ star q.val)
    exact conjugation.continuous.comp continuous_subtype_val⟩

def rightActionMap : C(Sphere 7 × FiberGroup, Sphere 7) :=
  ⟨fun z ↦ rightAction z.1 z.2, continuous_rightAction⟩

def rightInverseActionMap {X : Type*} [TopologicalSpace X]
    (a : C(X, Sphere 7)) (q : C(X, FiberGroup)) : C(X, Sphere 7) :=
  rightActionMap.comp (a.prodMk (fiberInverseMap.comp q))

theorem rightAction_one (x : Sphere 7) : rightAction x 1 = x := by
  apply Subtype.ext
  apply first_second_ext
  · simp only [rightAction, first_rightVector, OneMemClass.coe_one, mul_one]
  · simp only [rightAction, second_rightVector, OneMemClass.coe_one, mul_one]

theorem rightAction_mul (x : Sphere 7) (q r : FiberGroup) :
    rightAction (rightAction x q) r = rightAction x (q * r) := by
  apply Subtype.ext
  apply first_second_ext
  · simp only [rightAction, first_rightVector, Submonoid.coe_mul, mul_assoc]
  · simp only [rightAction, second_rightVector, Submonoid.coe_mul, mul_assoc]

theorem sphereMap_rightAction (x : Sphere 7) (q : FiberGroup) :
    sphereMap (rightAction x q) = sphereMap x := by
  have hc (a b : ℍ) : (a * q.val) * star (b * q.val) = a * star b := by
    rw [star_mul, mul_assoc, ← mul_assoc q.val, Unitary.mul_star_self_of_mem q.property,
      one_mul]
  apply Subtype.ext
  change polynomial (rightVector x.val q.val) = polynomial x.val
  simp only [polynomial, first_rightVector, second_rightVector, map_mul,
    fiberGroup_normSq, mul_one, hc]

theorem rightAction_fiberDivision (x y : Sphere 7) (h : sphereMap x = sphereMap y) :
    rightAction x (fiberDivision x y h) = y := by
  apply Subtype.ext
  apply first_second_ext
  · exact (first_rightVector _ _).trans (first_mul_division x y h)
  · exact (second_rightVector _ _).trans (second_mul_division x y h)

theorem divisionQuaternion_rightVector (x : Sphere 7) (q : ℍ) :
    divisionQuaternion x.val (rightVector x.val q) = q := by
  rw [divisionQuaternion, first_rightVector, second_rightVector,
    ← mul_assoc, ← mul_assoc, Quaternion.star_mul_self, Quaternion.star_mul_self,
    Quaternion.coe_mul_eq_smul, Quaternion.coe_mul_eq_smul,
    ← add_smul, unit_normSq_sum, one_smul]

theorem rightAction_injective (x : Sphere 7) : Function.Injective (rightAction x) := by
  intro q r h
  apply Subtype.ext
  have he := congrArg (fun y : Sphere 7 ↦ divisionQuaternion x.val y.val) h
  change divisionQuaternion x.val (rightVector x.val q.val) =
    divisionQuaternion x.val (rightVector x.val r.val) at he
  simpa only [divisionQuaternion_rightVector] using he

def unitFiberPoint : C(FiberGroup, Sphere 7) := fiberPoint.comp sphereHomeomorph

theorem first_unitFiberPoint (q : FiberGroup) : first (unitFiberPoint q).val = q.val := by
  change first (fiberPoint (sphereHomeomorph q)).val = q.val
  rw [first_fiberPoint]
  exact Quaternion.linearIsometryEquivTuple.symm_apply_apply q.val

theorem second_unitFiberPoint (q : FiberGroup) : second (unitFiberPoint q).val = 0 :=
  second_fiberPoint (sphereHomeomorph q)

theorem sphereMap_unitFiberPoint (q : FiberGroup) : sphereMap (unitFiberPoint q) = spherePole 4 :=
  sphereMap_fiberPoint (sphereHomeomorph q)

theorem unitFiberPoint_one : unitFiberPoint 1 = spherePole 7 := by
  change fiberPoint (sphereHomeomorph (1 : FiberGroup)) = spherePole 7
  rw [QuaternionCommutatorNativeSphere.sphereHomeomorph_one, fiberPoint_pole]

theorem unitFiberPoint_injective : Function.Injective unitFiberPoint := by
  intro q r h
  apply Subtype.ext
  have he := congrArg (fun x : Sphere 7 ↦ first x.val) h
  simpa only [first_unitFiberPoint] using he

theorem unitFiberPoint_mul (q r : FiberGroup) :
    unitFiberPoint (q * r) = rightAction (unitFiberPoint q) r := by
  apply Subtype.ext
  apply first_second_ext
  · simp only [first_unitFiberPoint, rightAction, first_rightVector, Submonoid.coe_mul]
  · simp only [second_unitFiberPoint, rightAction, second_rightVector, zero_mul]

def unitFiberCoordinate (x : Sphere 7) (h : sphereMap x = spherePole 4) : FiberGroup :=
  sphereHomeomorph.symm (fiberInverse ⟨x, h⟩)

theorem unitFiberPoint_coordinate (x : Sphere 7) (h : sphereMap x = spherePole 4) :
    unitFiberPoint (unitFiberCoordinate x h) = x := by
  change fiberPoint (sphereHomeomorph (sphereHomeomorph.symm (fiberInverse ⟨x, h⟩))) = x
  rw [Homeomorph.apply_symm_apply]
  exact fiberPoint_fiberInverse ⟨x, h⟩

theorem unitFiberCoordinate_point (q : FiberGroup) :
    unitFiberCoordinate (unitFiberPoint q) (sphereMap_unitFiberPoint q) = q := by
  apply unitFiberPoint_injective
  exact unitFiberPoint_coordinate _ _

theorem unitFiberCoordinate_pole : unitFiberCoordinate (spherePole 7) sphereMap_pole = 1 := by
  apply unitFiberPoint_injective
  rw [unitFiberPoint_coordinate, unitFiberPoint_one]

theorem continuous_unitFiberCoordinate {X : Type*} [TopologicalSpace X]
    (a : C(X, Sphere 7)) (h : ∀ x, sphereMap (a x) = spherePole 4) :
    Continuous (fun x ↦ unitFiberCoordinate (a x) (h x)) :=
  sphereHomeomorph.symm.continuous.comp
    (fiberHomeomorph.symm.continuous.comp (a.continuous.subtype_mk h))

end NoExoticSixSphere.QuaternionicHopf
