import Wikipedia.NoExoticSixSphere.InjectiveOperatorExtensionCoordinates
import Wikipedia.NoExoticSixSphere.InjectiveOperatorDimensionParity

/-!
# Frame coordinate changes through an actual nullhomotopic parameter map

A specified parameter contraction gives a homotopy of the actual
recoordinated injective-operator maps. At its constant endpoint, the
coordinate changes extend constantly over the four-ball. Thus the original
frame parity is preserved, even across different dimension presentations.
No arbitrary sphere-dependent coordinate change is treated as extendible.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization DiskBoundary

variable {P : Type*} [TopologicalSpace P] {N n N' n' : ℕ}
  (U : P → Vector N ≃L[ℝ] Vector N') (V : P → Vector n' ≃L[ℝ] Vector n)
  (hU : Continuous (fun p ↦ (U p).toContinuousLinearMap))
  (hV : Continuous (fun p ↦ (V p).toContinuousLinearMap))

def parameterRecoordinate (q : C(Sphere 3, P)) (F : C(Sphere 3, Space N n)) :
    C(Sphere 3, Space N' n') where
  toFun x := recoordinate (U (q x)) (V (q x)) (F x)
  continuous_toFun := ((hU.comp q.continuous).clm_comp
    ((continuous_subtype_val.comp F.continuous).clm_comp (hV.comp q.continuous))).subtype_mk _

theorem parameterRecoordinate_apply (q : C(Sphere 3, P)) (F : C(Sphere 3, Space N n))
    (x : Sphere 3) :
    parameterRecoordinate U V hU hV q F x = recoordinate (U (q x)) (V (q x)) (F x) := rfl

def parameterRecoordinateHomotopy (q : C(Sphere 3, P)) (F : C(Sphere 3, Space N n))
    (p₀ : P) (H : q.Homotopy (ContinuousMap.const _ p₀)) :
    (parameterRecoordinate U V hU hV q F).Homotopy
      (parameterRecoordinate U V hU hV (ContinuousMap.const _ p₀) F) where
  toFun p := recoordinate (U (H p)) (V (H p)) (F p.2)
  continuous_toFun := ((hU.comp H.continuous).clm_comp
    ((continuous_subtype_val.comp (F.continuous.comp continuous_snd)).clm_comp
      (hV.comp H.continuous))).subtype_mk _
  map_zero_left x := by
    rw [H.apply_zero]
    rfl
  map_one_left x := by
    rw [H.apply_one]
    rfl

theorem sphereParityOfDimension_parameterRecoordinate
    (r s : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (hN' : N' = 3 + (s + 2)) (hn' : n' = s + 2)
    (q : C(Sphere 3, P)) (F : C(Sphere 3, Space N n))
    (p₀ : P) (H : q.Homotopy (ContinuousMap.const _ p₀)) :
    sphereParityOfDimension s hN' hn' (parameterRecoordinate U V hU hV q F) =
      sphereParityOfDimension r hN hn F := by
  calc
    _ = sphereParityOfDimension s hN' hn'
        (parameterRecoordinate U V hU hV (ContinuousMap.const _ p₀) F) :=
      sphereParityOfDimension_homotopic s hN' hn'
        ⟨parameterRecoordinateHomotopy U V hU hV q F p₀ H⟩
    _ = _ := by
      apply zmodTwo_eq_of_zero_iff
      rw [sphereParityOfDimension_zero_iff, sphereParityOfDimension_zero_iff]
      exact extends_recoordinate_iff (fun _ ↦ U p₀) (fun _ ↦ V p₀)
        continuous_const continuous_const continuous_const continuous_const F
        (parameterRecoordinate U V hU hV (ContinuousMap.const _ p₀) F) (fun _ ↦ rfl)

end NoExoticSixSphere.Stiefel.Monomorphism
