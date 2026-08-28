import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryExponential
import Wikipedia.HomotopyGroupsOfSpheres.CliffordCanonicalHopfEndpoint
import Wikipedia.HomotopyGroupsOfSpheres.PointedHomotopyClassComparison

/-! # A based global correction identifies the actual endpoint with the orthogonal Bott family -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open CliffordFiveHermitian
open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

def referenceMap : C(ℝ, OrthogonalOperators 6) :=
  ⟨fun θ ↦ boundaryOrthogonal (latitudePoint θ structurePole),
    continuous_boundaryOrthogonal.comp
      (continuous_latitudePoint.comp (continuous_id.prodMk continuous_const))⟩

theorem referenceMap_zero : referenceMap 0 = 1 := by
  change boundaryOrthogonal (latitudePoint 0 structurePole) = 1
  rw [latitudePoint_zero, boundaryOrthogonal_equatorPole]

def correctedMap : C(EquatorSphere, OrthogonalOperators 6) :=
  ⟨fun q ↦ boundaryOrthogonal q * (referenceMap (polarAngle q))⁻¹,
    continuous_boundaryOrthogonal.mul (referenceMap.continuous.comp polarAngle.continuous).inv⟩

def correctionHomotopy : boundaryMap.HomotopyRel correctedMap {equatorPole} where
  toFun p := boundaryOrthogonal p.2 * (referenceMap ((p.1 : ℝ) * polarAngle p.2))⁻¹
  continuous_toFun := (continuous_boundaryOrthogonal.comp continuous_snd).mul
    (referenceMap.continuous.comp ((continuous_subtype_val.comp continuous_fst).mul
      (polarAngle.continuous.comp continuous_snd))).inv
  map_zero_left q := by
    change boundaryOrthogonal q * (referenceMap ((0 : ℝ) * polarAngle q))⁻¹ = boundaryOrthogonal q
    rw [zero_mul, referenceMap_zero, inv_one, mul_one]
  map_one_left q := by
    change boundaryOrthogonal q * (referenceMap ((1 : ℝ) * polarAngle q))⁻¹ =
      boundaryOrthogonal q * (referenceMap (polarAngle q))⁻¹
    rw [one_mul]
  prop' t q hq := by
    have h : q = equatorPole := Set.mem_singleton_iff.mp hq
    subst q
    change boundaryOrthogonal equatorPole * (referenceMap ((t : ℝ) * polarAngle equatorPole))⁻¹ =
      boundaryOrthogonal equatorPole
    rw [polarAngle_equatorPole, mul_zero, referenceMap_zero, inv_one, mul_one]

theorem correctedMap_equatorPole : correctedMap equatorPole = 1 := by
  change boundaryOrthogonal equatorPole * (referenceMap (polarAngle equatorPole))⁻¹ = 1
  rw [boundaryOrthogonal_equatorPole, polarAngle_equatorPole, referenceMap_zero, inv_one, mul_one]

theorem correctedMap_latitude (θ : ℝ) (v : Sphere 2) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    correctedMap (latitudePoint θ v) =
      boundaryOrthogonal (latitudePoint θ v) *
        (boundaryOrthogonal (latitudePoint θ structurePole))⁻¹ := by
  change boundaryOrthogonal (latitudePoint θ v) *
    (referenceMap (polarAngle (latitudePoint θ v)))⁻¹ = _
  rw [polarAngle_latitude θ v h0 hπ]
  rfl

theorem correctedMap_reference (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    correctedMap (latitudePoint θ structurePole) = 1 := by
  rw [correctedMap_latitude θ structurePole h0 hπ, mul_inv_cancel]

theorem correctedMap_pi (v : Sphere 2) : correctedMap (latitudePoint Real.pi v) = 1 := by
  rw [latitudePoint_pi_eq v structurePole]
  exact correctedMap_reference Real.pi Real.pi_pos.le le_rfl

theorem correctedMap_bott (t : I) (v : Sphere 2) :
    correctedMap (latitudePoint ((t : ℝ) * Real.pi) v) =
      OrthogonalBottNative.loopMap (structureMap structurePole) (structureMap v) t := by
  rw [OrthogonalBottNative.loopMap_apply, exponential_reference]
  exact correctedMap_latitude _ v (mul_nonneg t.property.1 Real.pi_pos.le)
    (by nlinarith [t.property.2, Real.pi_pos])

def correctedCube (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    GenLoop (Fin 3) (OrthogonalOperators 6) 1 :=
  pointedMapGenLoop correctedMap equatorPole 1 correctedMap_equatorPole p

theorem boundaryClass_eq_corrected (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    (⟦boundaryCube p⟧ : π_ 3 (OrthogonalOperators 6) 1) = ⟦correctedCube p⟧ :=
  Quotient.sound (pointedMapGenLoop_homotopic_of_homotopyRel
    boundaryMap correctedMap equatorPole 1 boundaryOrthogonal_equatorPole
      correctedMap_equatorPole correctionHomotopy p)

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
