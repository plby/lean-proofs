import Wikipedia.NoExoticSixSphere.StableSixSphereNativeStages

/-!
# The actual suspension maps on native sixth-stem homotopy groups

The suspension sends the north pole to the north pole independently of
the original map. The transported transition is proved to be the native
class of that actual suspension, and sends the native identity to itself.
No suspension-isomorphism range or homomorphism computation is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

open Wikipedia.HopfProblem.SphereHomology

theorem latitude_one_eq_pole (n : ℕ) (x : Sphere n) :
    Latitude.point n 1 x = spherePole (n + 1) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [Latitude.point, spherePole]
  · simp [Latitude.point, spherePole]

theorem map_pole {m n : ℕ} (f : C(Sphere m, Sphere n)) :
    map f (spherePole (m + 1)) = spherePole (n + 1) := by
  rw [← latitude_one_eq_pole m (spherePole m), map_point, latitude_one_eq_pole]

def basedMap {m n : ℕ} (f : C(Sphere m, Sphere n)) :
    SmoothCube.BasedMap (m + 1) (Sphere (n + 1)) (spherePole (n + 1)) :=
  ⟨map f, map_pole f⟩

end NoExoticSixSphere.SphereMapSuspension

namespace NoExoticSixSphere.StableSixSphereMaps

open SmoothCube

def nativeStep {k : ℕ} (x : NativeStage k) : NativeStage (k + 1) :=
  (nativeStageEquiv (k + 1)).symm (step (nativeStageEquiv k x))

theorem nativeStageEquiv_nativeStep {k : ℕ} (x : NativeStage k) :
    nativeStageEquiv (k + 1) (nativeStep x) = step (nativeStageEquiv k x) :=
  (nativeStageEquiv (k + 1)).apply_symm_apply _

theorem nativeStep_sphereClass {k : ℕ}
    (f : BasedMap (k + 8) (Sphere (k + 2)) (spherePole (k + 2))) :
    nativeStep (sphereClass f) = sphereClass (SphereMapSuspension.basedMap f.val) := by
  apply (nativeStageEquiv (k + 1)).injective
  rw [nativeStageEquiv_nativeStep, nativeStageEquiv_sphereClass, step_classOf,
    nativeStageEquiv_sphereClass]
  rfl

theorem nativeStep_one (k : ℕ) : nativeStep (1 : NativeStage k) = 1 := by
  apply (nativeStageEquiv (k + 1)).injective
  rw [nativeStageEquiv_nativeStep, nativeStageEquiv_one, step_stageZero,
    nativeStageEquiv_one]

def nativeTransition (k l : ℕ) (h : k ≤ l) : OneHom (NativeStage k) (NativeStage l) where
  toFun x := (nativeStageEquiv l).symm (transition k l h (nativeStageEquiv k x))
  map_one' := by
    apply (nativeStageEquiv l).injective
    rw [Equiv.apply_symm_apply, nativeStageEquiv_one, transition_stageZero,
      nativeStageEquiv_one]

theorem nativeStageEquiv_transition {k l : ℕ} (h : k ≤ l) (x : NativeStage k) :
    nativeStageEquiv l (nativeTransition k l h x) =
      transition k l h (nativeStageEquiv k x) := (nativeStageEquiv l).apply_symm_apply _

instance : DirectedSystem NativeStage (fun {k l} h ↦ nativeTransition k l h) where
  map_self {k} x := by
    change (nativeStageEquiv k).symm (transition k k le_rfl (nativeStageEquiv k x)) = x
    rw [transition_self, Equiv.symm_apply_apply]
  map_map := by
    intro k j i h h' x
    apply (nativeStageEquiv k).injective
    rw [nativeStageEquiv_transition, nativeStageEquiv_transition, nativeStageEquiv_transition]
    exact (Nat.leRecOn_trans h h' (nativeStageEquiv i x)).symm

theorem nativeTransition_succ {k l : ℕ} (h : k ≤ l) (x : NativeStage k) :
    nativeTransition k (l + 1) (h.trans (Nat.le_succ l)) x =
      nativeStep (nativeTransition k l h x) := by
  apply (nativeStageEquiv (l + 1)).injective
  rw [nativeStageEquiv_transition, nativeStageEquiv_nativeStep, nativeStageEquiv_transition,
    transition_succ]

end NoExoticSixSphere.StableSixSphereMaps
