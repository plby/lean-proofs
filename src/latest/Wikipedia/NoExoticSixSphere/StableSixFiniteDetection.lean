import Wikipedia.NoExoticSixSphere.OrdinarySuspensionReflection
import Wikipedia.NoExoticSixSphere.SixSphereThirteenCollapse

/-!
# Finite-stage detection for the actual sixth-stem collapse

Once the target dimension is eight, further ordinary suspensions reflect
nullhomotopy. Thus the original candidate's stable class is the identity
exactly when the first suspension of its actual S¹³ → S⁷ collapse is
nullhomotopic, equivalently when its native class in π₁₄(S⁸) is the identity.
Neither of those equivalent vanishing statements is supplied as a proof.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

theorem iterate_nullhomotopic_iff {m n : ℕ} (hd : m + 3 < 2 * (n + 1))
    (f : C(Sphere m, Sphere n)) (r : ℕ) :
    (iterate f r).Nullhomotopic ↔ f.Nullhomotopic := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (map (iterate f r)).Nullhomotopic ↔ f.Nullhomotopic
    exact (map_nullhomotopic_iff (by omega) (iterate f r)).trans ih

theorem finite_nullhomotopic_iff_map {m n : ℕ} (hd : (m + 1) + 3 < 2 * ((n + 1) + 1))
    (f : C(Sphere m, Sphere n)) :
    (∃ r : ℕ, (iterate f r).Nullhomotopic) ↔ (map f).Nullhomotopic := by
  constructor
  · rintro ⟨r, hr⟩
    cases r with
    | zero => exact map_nullhomotopic hr
    | succ r =>
      exact (iterate_nullhomotopic_iff hd (map f) r).mp
        ((iterate_map_nullhomotopic_iff f r).mpr hr)
  · intro h
    exact ⟨1, h⟩

end NoExoticSixSphere.SphereMapSuspension

namespace NoExoticSixSphere.CubicalStableSix

open SmoothCube SphereMapSuspension

theorem ofNative_sphereClass_eq_one_iff_native {k : ℕ} (hk : 6 ≤ k) (f : BasedStage k) :
    ofNative (sphereClass f) = 1 ↔ sphereClass f = 1 := by
  rw [ofNative_sphereClass_eq_one_iff, StableSixSphereMaps.ofMap_eq_nullClass_iff,
    sphereClass_eq_one_iff_nullhomotopic (by omega)]
  constructor
  · rintro ⟨r, hr⟩
    exact (iterate_nullhomotopic_iff (by omega) f.val r).mp hr
  · intro h
    exact ⟨0, h⟩

theorem ofNative_eq_one_iff_native {k : ℕ} (hk : 6 ≤ k)
    (x : StableSixSphereMaps.NativeStage k) : ofNative x = 1 ↔ x = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    let f := (basedEquiv (by omega : 0 < k + 8)).symm p
    simpa only [f, sphereClass_basedEquiv_symm] using
      ofNative_sphereClass_eq_one_iff_native hk f

theorem ofNative_injective {k : ℕ} (hk : 6 ≤ k) :
    Function.Injective (ofNative (k := k)) := by
  intro x y hxy
  apply div_eq_one.mp
  apply (ofNative_eq_one_iff_native hk (x / y)).mp
  change ofNativeHom k (x / y) = 1
  rw [map_div]
  change ofNative x / ofNative y = 1
  rw [hxy]
  exact div_self' _

end NoExoticSixSphere.CubicalStableSix

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SixSphereThirteen

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  (h : M ≃ₜ Sphere 6)

def suspendedNativeClass : StableSixSphereMaps.NativeStage 6 :=
  SmoothCube.sphereClass (SphereMapSuspension.basedMap (sphereMap h))

theorem stableClass_eq_one_iff_suspension_nullhomotopic :
    stableClass h = 1 ↔ (SphereMapSuspension.map (sphereMap h)).Nullhomotopic :=
  (stableClass_eq_one_iff h).trans
    (SphereMapSuspension.finite_nullhomotopic_iff_map (by decide) (sphereMap h))

theorem stableClass_eq_one_iff_suspendedNativeClass :
    stableClass h = 1 ↔ suspendedNativeClass h = 1 := by
  rw [stableClass_eq_one_iff_suspension_nullhomotopic]
  exact (SmoothCube.sphereClass_eq_one_iff_nullhomotopic (by decide)
    (SphereMapSuspension.basedMap (sphereMap h))).symm

end NoExoticSixSphere.SixSphereThirteen
