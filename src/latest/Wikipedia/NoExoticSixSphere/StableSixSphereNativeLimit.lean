import Wikipedia.NoExoticSixSphere.StableSixSphereNativeSuspension
import Wikipedia.NoExoticSixSphere.StableSixSphereMaps

/-!
# The native suspension direct limit is the original sphere-map direct limit

Both directions are induced by the checked stage equivalences, and the
transition squares commute. In particular the original constant class
corresponds to the native identity class, whose equality has an actual
finite-stage witness. No size or algebraic computation of the limit is
asserted here.
-/

noncomputable section

namespace NoExoticSixSphere.StableSixSphereMaps

abbrev NativeClass := DirectLimit NativeStage nativeTransition

def nativeClassOf {k : ℕ} (x : NativeStage k) : NativeClass := Quotient.mk _ ⟨k, x⟩

def nativeIdentityClass : NativeClass := nativeClassOf (k := 0) 1

def nativeToClass : NativeClass → Class :=
  DirectLimit.map nativeTransition transitionHom (fun k x ↦ nativeStageEquiv k x)
    (fun _ _ h x ↦ (nativeStageEquiv_transition h x).symm)

def classToNative : Class → NativeClass :=
  DirectLimit.map transitionHom nativeTransition (fun k ↦ (nativeStageEquiv k).symm)
    (by
      intro k l h x
      apply (nativeStageEquiv l).injective
      rw [nativeStageEquiv_transition, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl)

def nativeClassEquiv : NativeClass ≃ Class where
  toFun := nativeToClass
  invFun := classToNative
  left_inv x := by
    induction x using DirectLimit.induction nativeTransition with
    | ih k x =>
      change (Quotient.mk _ ⟨k, (nativeStageEquiv k).symm (nativeStageEquiv k x)⟩ :
        NativeClass) = Quotient.mk _ ⟨k, x⟩
      rw [Equiv.symm_apply_apply]
  right_inv x := by
    induction x using DirectLimit.induction transitionHom with
    | ih k x =>
      change (Quotient.mk _ ⟨k, nativeStageEquiv k ((nativeStageEquiv k).symm x)⟩ :
        Class) = Quotient.mk _ ⟨k, x⟩
      rw [Equiv.apply_symm_apply]

theorem nativeClassEquiv_classOf {k : ℕ} (x : NativeStage k) :
    nativeClassEquiv (nativeClassOf x) = (Quotient.mk _ ⟨k, nativeStageEquiv k x⟩ : Class) := rfl

theorem nativeClassEquiv_sphereClass {k : ℕ}
    (f : SmoothCube.BasedMap (k + 8) (Sphere (k + 2)) (spherePole (k + 2))) :
    nativeClassEquiv (nativeClassOf (SmoothCube.sphereClass f)) = ofMap f.val := by
  rw [nativeClassEquiv_classOf, nativeStageEquiv_sphereClass]
  rfl

theorem nativeClassEquiv_identity : nativeClassEquiv nativeIdentityClass = nullClass := by
  change (Quotient.mk _ ⟨0, nativeStageEquiv 0 1⟩ : Class) = nullClass
  rw [nativeStageEquiv_one]
  rfl

theorem nativeIdentityClass_eq_stage (k : ℕ) :
    nativeIdentityClass = nativeClassOf (k := k) 1 := by
  apply nativeClassEquiv.injective
  rw [nativeClassEquiv_identity, nativeClassEquiv_classOf, nativeStageEquiv_one]
  exact nullClass_eq_stage k

theorem nativeClassOf_eq_identity_iff {k : ℕ} (x : NativeStage k) :
    nativeClassOf x = nativeIdentityClass ↔
      ∃ (l : ℕ) (h : k ≤ l), nativeTransition k l h x = 1 := by
  rw [nativeIdentityClass_eq_stage k]
  constructor
  · intro h
    obtain ⟨l, hl, _, he⟩ := Quotient.exact h
    change nativeTransition k l hl x = nativeTransition k l hl 1 at he
    rw [map_one] at he
    exact ⟨l, hl, he⟩
  · rintro ⟨l, hl, he⟩
    apply Quotient.sound
    refine ⟨l, hl, hl, ?_⟩
    change nativeTransition k l hl x = nativeTransition k l hl 1
    rw [map_one]
    exact he

end NoExoticSixSphere.StableSixSphereMaps
