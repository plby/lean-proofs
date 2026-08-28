import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackCoordinatesAnalytic

/-!
# Canonical pullback in the actual local trivializations

Intrinsic derivative pullback has the expected local coefficient: the
determinant of the actual coordinate derivative.  Its inverse over a local
biholomorphism has the inverse determinant coefficient.  Both statements
are derived from the original tangent and canonical bundle atlases.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- The scalar coefficient of genuine pullback in two actual bundle charts. -/
theorem pullbackLinear_localCoefficient (f : M → N)
    (i : atlas Model M) (j : atlas Model N) {x : M}
    (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (hf : MDifferentiableAt I I f x) (v : (Atlas.core N).Fiber (f x)) :
    ((Atlas.core M).localTriv i ⟨x, pullbackLinear f x v⟩).2 =
      chartDeterminant f i j x * ((Atlas.core N).localTriv j ⟨f x, v⟩).2 := by
  change Atlas.jacobian M i (achart Model x) x * id (α := ℂ) (pullbackLinear f x v) =
    chartDeterminant f i j x *
      (Atlas.jacobian N j (achart Model (f x)) (f x) * id (α := ℂ) v)
  have hrev := Atlas.jacobian_reverse_mul N j (achart Model (f x))
    hj (mem_chart_source Model (f x))
  calc
    _ = Atlas.jacobian M i (achart Model x) x *
        (LinearMap.det (mfderiv I I f x).toLinearMap * id (α := ℂ) v) :=
      congrArg (fun c : ℂ => Atlas.jacobian M i (achart Model x) x * c)
        (pullbackLinear_preferred_coefficient f x v)
    _ = (Atlas.jacobian N (achart Model (f x)) j (f x) *
          Atlas.jacobian N j (achart Model (f x)) (f x)) *
        (Atlas.jacobian M i (achart Model x) x *
          (LinearMap.det (mfderiv I I f x).toLinearMap * id (α := ℂ) v)) := by
      rw [hrev, one_mul]
    _ = (Atlas.jacobian N (achart Model (f x)) j (f x) *
          LinearMap.det (mfderiv I I f x).toLinearMap *
          Atlas.jacobian M i (achart Model x) x) *
        (Atlas.jacobian N j (achart Model (f x)) (f x) * id (α := ℂ) v) := by ring
    _ = _ := congrArg (fun c : ℂ => c *
        (Atlas.jacobian N j (achart Model (f x)) (f x) * id (α := ℂ) v))
      (chartDeterminant_eq_jacobians f i j hi hj hf).symm

/-- Full top-covector compatibility with the actual coordinate derivative. -/
theorem inCoordinates_pullbackLinear (f : M → N)
    (i : atlas Model M) (j : atlas Model N) {x : M}
    (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (hf : MDifferentiableAt I I f x) (v : (Atlas.core N).Fiber (f x)) :
    Atlas.inCoordinates M i x (pullbackLinear f x v) =
      (Atlas.inCoordinates N j (f x) v).compContinuousLinearMap
        (chartDerivative f i j x) := by
  calc
    _ = coefficientEquiv (((Atlas.core M).localTriv i
        ⟨x, pullbackLinear f x v⟩).2) := rfl
    _ = coefficientEquiv (chartDeterminant f i j x *
        ((Atlas.core N).localTriv j ⟨f x, v⟩).2) :=
      congrArg coefficientEquiv (pullbackLinear_localCoefficient f i j hi hj hf v)
    _ = _ := (coefficientEquiv_pullback
      (((Atlas.core N).localTriv j ⟨f x, v⟩).2) (chartDerivative f i j x)).symm

theorem pullbackEquiv_localCoefficient {f : M → N}
    (hf : IsLocalDiffeomorph I I ω f) (i : atlas Model M) (j : atlas Model N)
    {x : M} (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (v : (Atlas.core N).Fiber (f x)) :
    ((Atlas.core M).localTriv i ⟨x, pullbackEquiv hf x v⟩).2 =
      chartDeterminant f i j x * ((Atlas.core N).localTriv j ⟨f x, v⟩).2 :=
  pullbackLinear_localCoefficient f i j hi hj ((hf x).mdifferentiableAt (by simp)) v

theorem inCoordinates_pullbackEquiv {f : M → N}
    (hf : IsLocalDiffeomorph I I ω f) (i : atlas Model M) (j : atlas Model N)
    {x : M} (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (v : (Atlas.core N).Fiber (f x)) :
    Atlas.inCoordinates M i x (pullbackEquiv hf x v) =
      (Atlas.inCoordinates N j (f x) v).compContinuousLinearMap
        (chartDerivative f i j x) :=
  inCoordinates_pullbackLinear f i j hi hj ((hf x).mdifferentiableAt (by simp)) v

/-- The inverse fibre comparison has the inverse actual chart Jacobian as
its scalar multiplier. -/
theorem pullbackEquiv_symm_localCoefficient {f : M → N}
    (hf : IsLocalDiffeomorph I I ω f) (i : atlas Model M) (j : atlas Model N)
    {x : M} (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (v : (Atlas.core M).Fiber x) :
    ((Atlas.core N).localTriv j ⟨f x, (pullbackEquiv hf x).symm v⟩).2 =
      (chartDeterminant f i j x)⁻¹ * ((Atlas.core M).localTriv i ⟨x, v⟩).2 := by
  have h : ((Atlas.core M).localTriv i ⟨x, v⟩).2 =
      chartDeterminant f i j x *
        ((Atlas.core N).localTriv j ⟨f x, (pullbackEquiv hf x).symm v⟩).2 := by
    calc
      _ = ((Atlas.core M).localTriv i
          ⟨x, pullbackEquiv hf x ((pullbackEquiv hf x).symm v)⟩).2 :=
        congrArg (fun w : (Atlas.core M).Fiber x =>
          ((Atlas.core M).localTriv i ⟨x, w⟩).2)
            ((pullbackEquiv hf x).apply_symm_apply v).symm
      _ = _ := pullbackEquiv_localCoefficient hf i j hi hj ((pullbackEquiv hf x).symm v)
  have hd := chartDeterminant_ne_zero f i j hi hj (hf x)
  calc
    _ = (chartDeterminant f i j x)⁻¹ * (chartDeterminant f i j x *
        ((Atlas.core N).localTriv j ⟨f x, (pullbackEquiv hf x).symm v⟩).2) := by
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    _ = _ := congrArg (fun c : ℂ => (chartDeterminant f i j x)⁻¹ * c) h.symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
