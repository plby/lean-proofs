import Wikipedia.HomotopyGroupsOfSpheres.CliffordBalancedNormalization
import Wikipedia.HomotopyGroupsOfSpheres.CliffordLatitudeCover
import Wikipedia.HomotopyGroupsOfSpheres.BalancedHomotopyMap

/-!
# The actual reference-corrected Clifford family and the native Bott cube

The global sphere map is in the determinant-one locus. Its reference correction
is a based homotopy, and its angular cube formula is the existing native Bott
construction on the actual balanced map. No generator assertion is assumed.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

theorem balancedSphereMap_determinant (z : ComplexCrossProductUnitary.UnitSphere) :
    determinant (balancedSphereMap z) = 1 := by
  obtain ⟨θ, h0, hπ, v, rfl⟩ := latitudePoint_surjective z
  rw [balancedSphereMap_latitude θ v h0 hπ]
  exact (BalancedRealInvolutions.rotation (balancedMap v) θ).property

def balancedSpecialSphereMap :
    C(ComplexCrossProductUnitary.UnitSphere, SpecialSpace (Fin 6 ⊕ Fin 6)) where
  toFun z := ⟨balancedSphereMap z, balancedSphereMap_determinant z⟩
  continuous_toFun := balancedSphereMap.continuous.subtype_mk _

theorem balancedSpecialSphereMap_axis : balancedSpecialSphereMap axis = specialIdentity :=
  Subtype.ext balancedSphereMap_axis

theorem balancedSpecialSphereMap_latitude
    (θ : ℝ) (v : UnitSphere) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    balancedSpecialSphereMap (latitudePoint θ v) =
      BalancedRealInvolutions.rotation (balancedMap v) θ :=
  Subtype.ext (balancedSphereMap_latitude θ v h0 hπ)

def referenceActionMap :
    C(ℝ × SpecialSpace (Fin 6 ⊕ Fin 6), SpecialSpace (Fin 6 ⊕ Fin 6)) :=
  ⟨fun p ↦ BalancedRealInvolutions.referenceAction 6 p.1 p.2,
    BalancedRealInvolutions.continuous_referenceAction 6⟩

def correctedSphereMap :
    C(ComplexCrossProductUnitary.UnitSphere, SpecialSpace (Fin 6 ⊕ Fin 6)) :=
  referenceActionMap.comp
    ⟨fun z ↦ (-polarAngle z / 2, balancedSpecialSphereMap z),
      (polarAngle.continuous.neg.div_const 2).prodMk balancedSpecialSphereMap.continuous⟩

def referenceCorrectionHomotopy :
    balancedSpecialSphereMap.HomotopyRel correctedSphereMap {axis} where
  toContinuousMap := referenceActionMap.comp
    ⟨fun p : I × ComplexCrossProductUnitary.UnitSphere ↦
      (-((p.1 : ℝ) * polarAngle p.2) / 2, balancedSpecialSphereMap p.2), by
      exact (((continuous_subtype_val.comp continuous_fst).mul
        (polarAngle.continuous.comp continuous_snd)).neg.div_const 2).prodMk
          (balancedSpecialSphereMap.continuous.comp continuous_snd)⟩
  map_zero_left z := by
    change BalancedRealInvolutions.referenceAction 6 (-((0 : ℝ) * polarAngle z) / 2)
      (balancedSpecialSphereMap z) = balancedSpecialSphereMap z
    rw [zero_mul, neg_zero, zero_div, BalancedRealInvolutions.referenceAction_zero]
  map_one_left z := by
    change BalancedRealInvolutions.referenceAction 6 (-((1 : ℝ) * polarAngle z) / 2)
      (balancedSpecialSphereMap z) =
        BalancedRealInvolutions.referenceAction 6 (-polarAngle z / 2) (balancedSpecialSphereMap z)
    rw [one_mul]
  prop' t z hz := by
    have he : z = axis := Set.mem_singleton_iff.mp hz
    subst z
    change BalancedRealInvolutions.referenceAction 6 (-((t : ℝ) * polarAngle axis) / 2)
      (balancedSpecialSphereMap axis) = balancedSpecialSphereMap axis
    rw [polarAngle_axis, mul_zero, neg_zero, zero_div,
      BalancedRealInvolutions.referenceAction_zero]

theorem correctedSphereMap_axis : correctedSphereMap axis = specialIdentity := by
  change BalancedRealInvolutions.referenceAction 6 (-polarAngle axis / 2)
    (balancedSpecialSphereMap axis) = specialIdentity
  rw [polarAngle_axis, neg_zero, zero_div, BalancedRealInvolutions.referenceAction_zero,
    balancedSpecialSphereMap_axis]

theorem correctedSphereMap_latitude
    (θ : ℝ) (v : UnitSphere) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    correctedSphereMap (latitudePoint θ v) =
      BalancedRealInvolutions.referenceAction 6 (-θ / 2)
        (BalancedRealInvolutions.rotation (balancedMap v) θ) := by
  change BalancedRealInvolutions.referenceAction 6 (-polarAngle (latitudePoint θ v) / 2)
    (balancedSpecialSphereMap (latitudePoint θ v)) = _
  rw [polarAngle_latitude θ v h0 hπ, balancedSpecialSphereMap_latitude θ v h0 hπ]

theorem correctedSphereMap_reference (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    correctedSphereMap (latitudePoint θ pole) = specialIdentity := by
  rw [correctedSphereMap_latitude θ pole h0 hπ, balancedMap_pole,
    BalancedRealInvolutions.referenceAction_reference]

def balancedCube (p : GenLoop (Fin 4) UnitSphere pole) :
    GenLoop (Fin 4) (BalancedRealInvolutions.Space 6) (BalancedRealInvolutions.standard 6) :=
  pointedMapGenLoop balancedMap pole (BalancedRealInvolutions.standard 6) balancedMap_pole p

theorem balancedCube_apply (p : GenLoop (Fin 4) UnitSphere pole) (t : Fin 4 → I) :
    balancedCube p t = balancedMap (p t) := rfl

theorem correctedSphereMap_cube (p : GenLoop (Fin 4) UnitSphere pole) (t : Fin 5 → I) :
    correctedSphereMap (latitudePoint ((t 0 : ℝ) * Real.pi) (p (Fin.tail t))) =
      BalancedRealInvolutions.inducedCube 6 (balancedCube p) t := by
  have h0 : 0 ≤ (t 0 : ℝ) * Real.pi := mul_nonneg (t 0).property.1 Real.pi_pos.le
  have hπ : (t 0 : ℝ) * Real.pi ≤ Real.pi := by
    nlinarith [(t 0).property.2, Real.pi_pos]
  rw [correctedSphereMap_latitude _ _ h0 hπ, BalancedRealInvolutions.inducedCube_apply,
    balancedCube_apply]
  simp only [BalancedRealInvolutions.halfAngle, neg_div]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
