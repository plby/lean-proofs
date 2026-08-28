import Wikipedia.NoExoticSixSphere.SpherePairLocalReparametrization

/-!
# Native sphere derivatives with their common Euclidean models explicit

These definitions retain the actual native derivatives. Their fixed
codomains avoid repeated comparisons of basepoint-indexed tangent-space
instances when the sphere map is a large piecewise expression.
-/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

def nativeSphereDerivative (f : Sphere 3 → M) (x : Sphere 3) : Vector 3 →L[ℝ] Vector 6 :=
  mfderiv (𝓡 3) (𝓡 6) f x

def nativeSphereSourceDerivative (u : Sphere 3 → Sphere 3) (x : Sphere 3) :
    Vector 3 →L[ℝ] Vector 3 := mfderiv (𝓡 3) (𝓡 3) u x

def NativeSphereTransverseAt (f g : Sphere 3 → M) (x y : Sphere 3) : Prop :=
  Surjective ((nativeSphereDerivative f x).coprod (nativeSphereDerivative g y))

def NativeSphereSelfTransverse (f : Sphere 3 → M) : Prop :=
  ∀ x y, x ≠ y → f x = f y → NativeSphereTransverseAt f f x y

def NativeSpherePairTransverse (f g : Sphere 3 → M) : Prop :=
  ∀ x y, f x = g y → NativeSphereTransverseAt f g x y

theorem nativeSphereSelfTransverse_iff (f : Sphere 3 → M) :
    NativeSphereSelfTransverse f ↔ ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x : Vector 3 →L[ℝ] Vector 6).coprod
        (mfderiv (𝓡 3) (𝓡 6) f y : Vector 3 →L[ℝ] Vector 6)) := Iff.rfl

theorem nativeSpherePairTransverse_iff (f g : Sphere 3 → M) :
    NativeSpherePairTransverse f g ↔ ∀ x y, f x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x : Vector 3 →L[ℝ] Vector 6).coprod
        (mfderiv (𝓡 3) (𝓡 6) g y : Vector 3 →L[ℝ] Vector 6)) := Iff.rfl

theorem nativeSphereDerivative_germ {f g : Sphere 3 → M} {x : Sphere 3}
    (h : f =ᶠ[𝓝 x] g) : nativeSphereDerivative f x = nativeSphereDerivative g x := h.mfderiv_eq

theorem nativeSphereDerivative_comp (f : Sphere 3 → M) (u : Sphere 3 → Sphere 3)
    (x : Sphere 3) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) :
    nativeSphereDerivative (f ∘ u) x =
      (nativeSphereDerivative f (u x)).comp (nativeSphereSourceDerivative u x) :=
  mfderiv_comp (f := u) (g := f) x (hf.mdifferentiableAt (by simp))
    (hu.mdifferentiableAt (by simp))

theorem nativeSphereSourceDerivative_surjective (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) :
    Surjective (nativeSphereSourceDerivative u x) :=
  (hu.mfderivToContinuousLinearEquiv (by simp)).surjective

theorem nativeSphereTransverseAt_swap {f g : Sphere 3 → M} {x y : Sphere 3}
    (h : NativeSphereTransverseAt f g x y) : NativeSphereTransverseAt g f y x :=
  surjective_coprod_swap _ _ h

theorem nativeSphereTransverseAt_of_local_reparametrizations
    (K F G : Sphere 3 → M) (u v : Sphere 3 → Sphere 3) (x y : Sphere 3)
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x)
    (hv : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ v y)
    (hx : K =ᶠ[𝓝 x] F ∘ u) (hy : K =ᶠ[𝓝 y] G ∘ v)
    (ht : NativeSphereTransverseAt F G (u x) (v y)) : NativeSphereTransverseAt K K x y := by
  unfold NativeSphereTransverseAt
  rw [nativeSphereDerivative_germ hx, nativeSphereDerivative_germ hy,
    nativeSphereDerivative_comp F u x hF hu, nativeSphereDerivative_comp G v y hG hv]
  exact surjective_coprod_comp_both _ _ _ _ (nativeSphereSourceDerivative_surjective u x hu)
    (nativeSphereSourceDerivative_surjective v y hv) ht

end NoExoticSixSphere.SphereSumNeck
