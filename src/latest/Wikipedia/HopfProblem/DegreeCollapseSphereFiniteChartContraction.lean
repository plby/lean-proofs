import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteRadialCoordinates
import Wikipedia.NoExoticSixSphere.SpanningDiskSourceTwist

/-!
# Removing the actual inverse-chart coordinates by an injective homotopy

Scale the finite coordinate to zero inside its entire Euclidean chart.
The actual radial/tangent coordinate operator stays invertible, so its
composition with any injective frame stays injective. A contraction of the
finite frame therefore gives a contraction of its actual sphere-chart lift.
The original twisted stabilization transports this homotopy unchanged.
-/

noncomputable section

open unitInterval
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteChartContraction

open NoExoticSixSphere GLOrthonormalization Stiefel
open SphereFiniteRadialCoordinates SpanningDiskFrameCoordinates

variable {X : Type*} [TopologicalSpace X] {m k : ℕ}

def transport (u : C(X, Vector m)) (A : C(X, Monomorphism.Space (m + 1) k)) :
    C(X, Monomorphism.Space (m + 1) k) where
  toFun x := ⟨(frameOperator (u x)).comp (A x).val,
    (frameOperator_injective (u x)).comp (A x).property⟩
  continuous_toFun :=
    (((contDiff_frameOperator (n := m)).continuous.comp u.continuous).clm_comp
      (continuous_subtype_val.comp A.continuous)).subtype_mk _

theorem transport_value (u : C(X, Vector m))
    (A : C(X, Monomorphism.Space (m + 1) k)) (x : X) :
    (transport u A x).val = (frameOperator (u x)).comp (A x).val := rfl

def contraction (u : C(X, Vector m)) (A : C(X, Monomorphism.Space (m + 1) k)) :
    (transport u A).Homotopy (transport (ContinuousMap.const X 0) A) where
  toFun p := ⟨(frameOperator ((1 - (p.1 : ℝ)) • u p.2)).comp (A p.2).val,
    (frameOperator_injective _).comp (A p.2).property⟩
  continuous_toFun := by
    have hu : Continuous (fun p : I × X ↦ (1 - (p.1 : ℝ)) • u p.2) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (u.continuous.comp continuous_snd)
    exact (((contDiff_frameOperator (n := m)).continuous.comp hu).clm_comp
      (continuous_subtype_val.comp (A.continuous.comp continuous_snd))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change (frameOperator ((1 - (0 : ℝ)) • u x)).comp (A x).val = _
    rw [sub_zero, one_smul]
    rfl
  map_one_left x := by
    apply Subtype.ext
    change (frameOperator ((1 - (1 : ℝ)) • u x)).comp (A x).val = _
    rw [sub_self, zero_smul]
    rfl

def fixedCoordinates (z : Vector m) :
    C(Monomorphism.Space (m + 1) k, Monomorphism.Space (m + 1) k) :=
  ⟨Monomorphism.recoordinate (frameEquiv z) (ContinuousLinearEquiv.refl ℝ (Vector k)),
    Monomorphism.continuous_recoordinate _ _⟩

theorem transport_constant_eq (z : Vector m) (A : C(X, Monomorphism.Space (m + 1) k)) :
    transport (ContinuousMap.const X z) A =
      (fixedCoordinates z).comp A := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem homotopic_fixed (u : C(X, Vector m)) (A : C(X, Monomorphism.Space (m + 1) k)) :
    (transport u A).Homotopic
      ((fixedCoordinates (0 : Vector m)).comp A) := by
  rw [← transport_constant_eq]
  exact ⟨contraction u A⟩

theorem homotopic_constant (u : C(X, Vector m)) (A : C(X, Monomorphism.Space (m + 1) k))
    (a : Monomorphism.Space (m + 1) k) (ha : A.Homotopic (ContinuousMap.const X a)) :
    (transport u A).Homotopic (ContinuousMap.const X
      (fixedCoordinates (0 : Vector m) a)) := by
  let F : C(Monomorphism.Space (m + 1) k, Monomorphism.Space (m + 1) k) :=
    fixedCoordinates (0 : Vector m)
  have h : (F.comp A).Homotopic (F.comp (ContinuousMap.const X a)) :=
    (ContinuousMap.Homotopic.refl F).comp ha
  have he : F.comp (ContinuousMap.const X a) = ContinuousMap.const X (F a) := by
    ext x
    rfl
  rw [he] at h
  exact (homotopic_fixed u A).trans h

theorem twisted_homotopic_constant (u : C(Sphere 3, Vector m))
    (A : C(Sphere 3, Monomorphism.Space (m + 1) (k + 3)))
    (a : Monomorphism.Space (m + 1) (k + 3))
    (ha : A.Homotopic (ContinuousMap.const _ a)) :
    (twistedBlockMap (transport u A)).Homotopic (twistedBlockMap (ContinuousMap.const _
      (fixedCoordinates (0 : Vector m) a))) :=
  twistedBlockMap_homotopic (homotopic_constant u A a ha)

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteChartContraction
