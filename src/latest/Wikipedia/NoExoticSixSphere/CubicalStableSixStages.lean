import Wikipedia.NoExoticSixSphere.CubicalSuspensionProductMap
import Wikipedia.NoExoticSixSphere.StableSixSphereNativeStages
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# A directed system of genuine native sixth-stem group homomorphisms

The transitions are the constructed cubical product suspensions. Their
representative formula is retained at every stage. The resulting direct
limit inherits a commutative group structure from the actual native
homotopy groups and the proved homomorphism laws.
-/

noncomputable section

namespace NoExoticSixSphere.CubicalStableSix

open StableSixSphereMaps SmoothCube

def stepHom (k : ℕ) : NativeStage k →* NativeStage (k + 1) :=
  CubicalSphereSuspension.hom (k + 8) (k + 2)

def transition (k l : ℕ) (h : k ≤ l) : NativeStage k →* NativeStage l :=
  Nat.leRecOn h (fun {j} F ↦ (stepHom j).comp F) (MonoidHom.id (NativeStage k))

theorem transition_self (k : ℕ) : transition k k le_rfl = MonoidHom.id (NativeStage k) :=
  Nat.leRecOn_self _

theorem transition_succ {k l : ℕ} (h : k ≤ l) :
    transition k (l + 1) (h.trans (Nat.le_succ l)) = (stepHom l).comp (transition k l h) :=
  Nat.leRecOn_succ h _

instance : DirectedSystem NativeStage (fun {k l} h ↦ transition k l h) where
  map_self {k} x := by rw [transition_self]; rfl
  map_map := by
    intro k j i h h' x
    induction k, h' using Nat.le_induction with
    | base => rw [transition_self]; rfl
    | succ k hk ih =>
      rw [transition_succ hk, transition_succ (h.trans hk), MonoidHom.comp_apply,
        MonoidHom.comp_apply, ih]

abbrev BasedStage (k : ℕ) :=
  BasedMap (k + 8) (Sphere (k + 2)) (spherePole (k + 2))

def basedLift {k l : ℕ} (h : k ≤ l) (f : BasedStage k) : BasedStage l :=
  Nat.leRecOn h (fun g ↦ CubicalSphereSuspension.productBasedMap g) f

theorem basedLift_self (k : ℕ) (f : BasedStage k) : basedLift le_rfl f = f :=
  Nat.leRecOn_self _

theorem basedLift_succ {k l : ℕ} (h : k ≤ l) (f : BasedStage k) :
    basedLift (h.trans (Nat.le_succ l)) f =
      CubicalSphereSuspension.productBasedMap (basedLift h f) := Nat.leRecOn_succ h _

theorem transition_sphereClass {k l : ℕ} (h : k ≤ l) (f : BasedStage k) :
    transition k l h (sphereClass f) = sphereClass (basedLift h f) := by
  induction l, h using Nat.le_induction with
  | base => rw [transition_self, basedLift_self]; rfl
  | succ l h ih =>
    rw [transition_succ h, MonoidHom.comp_apply, ih, basedLift_succ h]
    exact CubicalSphereSuspension.hom_sphereClass _

abbrev Group := DirectLimit NativeStage transition

instance : CommGroup Group := inferInstanceAs (CommGroup (DirectLimit NativeStage transition))

def ofNative {k : ℕ} (x : NativeStage k) : Group := Quotient.mk _ ⟨k, x⟩

theorem ofNative_one (k : ℕ) : ofNative (k := k) 1 = 1 := (DirectLimit.one_def k).symm

theorem ofNative_mul {k : ℕ} (x y : NativeStage k) :
    ofNative (x * y) = ofNative x * ofNative y := (DirectLimit.mul_def k x y).symm

def ofNativeHom (k : ℕ) : NativeStage k →* Group where
  toFun := ofNative
  map_one' := ofNative_one k
  map_mul' := ofNative_mul

theorem ofNative_eq_one_iff {k : ℕ} (x : NativeStage k) :
    ofNative x = 1 ↔ ∃ (l : ℕ) (h : k ≤ l), transition k l h x = 1 :=
  DirectLimit.exists_eq_one ⟨k, x⟩

end NoExoticSixSphere.CubicalStableSix
