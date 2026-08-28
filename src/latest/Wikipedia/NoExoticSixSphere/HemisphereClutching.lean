import Wikipedia.NoExoticSixSphere.Equator
import Wikipedia.NoExoticSixSphere.HemisphereFrames

/-!
# The actual hemisphere clutching map

Two transported hemisphere frames determine a continuous invertible change of
basis on their common equator. This records the concrete topological obstruction;
it does not assume that this map is nullhomotopic after stabilization.
-/

namespace NoExoticSixSphere

variable {E F K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The space of actual invertible continuous linear endomorphisms of a model fiber. -/
abbrev InvertibleOperators (K : Type*) [NormedAddCommGroup K] [NormedSpace ℝ K] :=
  {A : K →L[ℝ] K // A.IsInvertible}

namespace HemisphereClutching

variable (P : UnitSphere E → F →L[ℝ] F) (v : UnitSphere E)
  (aN : ContinuousRangeTransport (fun _ : ClosedHemisphere v ↦ P v)
    (fun x : ClosedHemisphere v ↦ P x.1))
  (aS : ContinuousRangeTransport (fun _ : ClosedHemisphere (antipode v) ↦ P (antipode v))
    (fun x : ClosedHemisphere (antipode v) ↦ P x.1))
  (qN : K ≃L[ℝ] (P v).range) (qS : K ≃L[ℝ] (P (antipode v)).range)

/-- Change from the northern model coordinates to the southern model coordinates. -/
noncomputable def equiv (x : Equator v) : K ≃L[ℝ] K :=
  (qN.trans (aN.rangeEquiv (equatorNorth v x))).trans
    (qS.trans (aS.rangeEquiv (equatorSouth v x))).symm

/-- An ambient operator formula for the coordinate change. -/
noncomputable def operator (x : Equator v) : K →L[ℝ] K :=
  (qS.symm.toContinuousLinearMap.comp (P (antipode v)).rangeRestrict).comp
    ((aS.toFun (equatorSouth v x)).inverse.comp
      ((aN.toFun (equatorNorth v x)).comp
        ((P v).range.subtypeL.comp qN.toContinuousLinearMap)))

omit [CompleteSpace F] in
/-- The ambient formula is the actual invertible change of basis. -/
theorem operator_eq_equiv (hP : IsIdempotentElem (P (antipode v))) (x : Equator v) :
    operator P v aN aS qN qS x = (equiv P v aN aS qN qS x).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  let z := (aS.rangeEquiv (equatorSouth v x)).symm
    (aN.rangeEquiv (equatorNorth v x) (qN w))
  change qS.symm ((P (antipode v)).rangeRestrict (z : F)) = qS.symm z
  apply congrArg qS.symm
  apply Subtype.ext
  exact projection_apply_range (P (antipode v)) hP z

/-- The explicit operator formula varies continuously along the equator. -/
theorem continuous_operator : Continuous (operator P v aN aS qN qS) :=
  continuous_const.clm_comp
    ((aS.continuous_inverse.comp (continuous_equatorSouth v)).clm_comp
      ((aN.continuous.comp (continuous_equatorNorth v)).clm_comp continuous_const))

/-- The actual change-of-basis equivalences are continuous in operator norm. -/
theorem continuous_equiv (hP : IsIdempotentElem (P (antipode v))) :
    Continuous (fun x ↦ (equiv P v aN aS qN qS x).toContinuousLinearMap) := by
  have heq : (fun x ↦ (equiv P v aN aS qN qS x).toContinuousLinearMap) =
      operator P v aN aS qN qS := funext (fun x ↦ (operator_eq_equiv P v aN aS qN qS hP x).symm)
  rw [heq]
  exact continuous_operator P v aN aS qN qS

/-- The clutching map takes values in the genuine general linear space. -/
noncomputable def map (hP : IsIdempotentElem (P (antipode v))) :
    C(Equator v, InvertibleOperators K) where
  toFun x := ⟨(equiv P v aN aS qN qS x).toContinuousLinearMap,
    ⟨equiv P v aN aS qN qS x, rfl⟩⟩
  continuous_toFun := (continuous_equiv P v aN aS qN qS hP).subtype_mk _

end HemisphereClutching

/-- The clutching map obtained from the two hemisphere contractions of a sphere projection. -/
noncomputable def sphereClutchingMap [FiniteDimensional ℝ E]
    (P : UnitSphere E → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (hc : Continuous P)
    (v : UnitSphere E) (qN : K ≃L[ℝ] (P v).range)
    (qS : K ≃L[ℝ] (P (antipode v)).range) : C(Equator v, InvertibleOperators K) :=
  HemisphereClutching.map P v
    (hemisphereTransport P hP hc v) (hemisphereTransport P hP hc (antipode v)) qN qS
    (hP (antipode v))

end NoExoticSixSphere
