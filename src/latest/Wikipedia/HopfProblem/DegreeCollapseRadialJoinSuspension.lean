import Wikipedia.HopfProblem.DegreeCollapseRadialSphereJoin
import Wikipedia.NoExoticSixSphere.SphereMapSuspension
import Wikipedia.NoExoticSixSphere.SphereCylinderVector

/-!
# One radial join is the original latitude suspension

Move the added real coordinate to the first Euclidean coordinate.
The exact radial homogeneity law then identifies both maps on every
latitude, including its zero-radius endpoints. Surjectivity of the
original latitude quotient gives equality on the whole sphere.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization unitInterval
open Wikipedia.HopfProblem.SphereHomology

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialJoinSuspension

open HopfBlockCoordinates RadialSphereMap

def leftCoordinates (n : ℕ) : WithLp 2 (ℝ × Vector (n + 1)) ≃ₗᵢ[ℝ] Vector (n + 2) where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (ℝ × Vector (n + 1))).trans
    (SphereCylinder.join n).toLinearEquiv
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖SphereCylinder.join n (x.fst, x.snd)‖ ^ 2 = ‖x‖ ^ 2
    rw [SphereCylinder.norm_join_sq, WithLp.prod_norm_sq_eq_of_L2,
      Real.norm_eq_abs, sq_abs]

def rightCoordinates (n : ℕ) : WithLp 2 (Vector (n + 1) × ℝ) ≃ₗᵢ[ℝ] Vector (n + 2) :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ (Vector (n + 1)) ℝ).trans (leftCoordinates n)

theorem rightCoordinates_apply (n : ℕ) (x : WithLp 2 (Vector (n + 1) × ℝ)) :
    rightCoordinates n x = SphereCylinder.join n (x.snd, x.fst) := rfl

def coordinates (n : ℕ) :
    NoExoticSixSphere.UnitSphere (WithLp 2 (Vector (n + 1) × ℝ)) ≃ₜ Sphere (n + 1) :=
  unitSphereCoordinates (rightCoordinates n)

def latitudePreimage (n : ℕ) (t : I) (x : Sphere n) :
    NoExoticSixSphere.UnitSphere (WithLp 2 (Vector (n + 1) × ℝ)) :=
  (coordinates n).symm (Latitude.point n t x)

theorem latitudePreimage_val (n : ℕ) (t : I) (x : Sphere n) :
    (latitudePreimage n t x).val =
      WithLp.toLp 2 (Latitude.radius t • x.val, Latitude.height t) := by
  apply (rightCoordinates n).injective
  change rightCoordinates n ((rightCoordinates n).symm (Latitude.point n t x).val) =
    SphereCylinder.join n (Latitude.height t, Latitude.radius t • x.val)
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact Fin.cases rfl (fun _ ↦ rfl) i

variable {m n : ℕ}

theorem map_latitude (f : C(Sphere m, Sphere n)) (t : I) (x : Sphere m) :
    coordinates n (RadialSphereJoin.sphereMap (G := ℝ) f (latitudePreimage m t x)) =
      Latitude.point n t (f x) := by
  apply Subtype.ext
  change rightCoordinates n (RadialSphereJoin.vector f (latitudePreimage m t x).val) = _
  rw [latitudePreimage_val]
  change SphereCylinder.join n (Latitude.height t, extend f (Latitude.radius t • x.val)) = _
  rw [extend_smul_unit f _ (Latitude.radius_nonneg t)]
  apply PiLp.ext
  intro i
  exact Fin.cases rfl (fun _ ↦ rfl) i

theorem map_coordinates (f : C(Sphere m, Sphere n))
    (x : NoExoticSixSphere.UnitSphere (WithLp 2 (Vector (m + 1) × ℝ))) :
    coordinates n (RadialSphereJoin.sphereMap (G := ℝ) f x) =
      SphereMapSuspension.map f (coordinates m x) := by
  obtain ⟨⟨t, z⟩, hz⟩ := Latitude.point_surjective m (coordinates m x)
  have hx : x = latitudePreimage m t z := by
    apply (coordinates m).injective
    change coordinates m x = (coordinates m) ((coordinates m).symm (Latitude.point m t z))
    rw [Homeomorph.apply_symm_apply]
    exact hz.symm
  rw [hx, map_latitude]
  change Latitude.point n t (f z) =
    SphereMapSuspension.map f ((coordinates m) ((coordinates m).symm (Latitude.point m t z)))
  rw [Homeomorph.apply_symm_apply, SphereMapSuspension.map_point]

def joinedSphereMap (f : C(Sphere m, Sphere n)) : C(Sphere (m + 1), Sphere (n + 1)) :=
  (coordinates n : C(_, _)).comp
    ((RadialSphereJoin.sphereMap (G := ℝ) f).comp ((coordinates m).symm : C(_, _)))

theorem joinedSphereMap_eq_suspension (f : C(Sphere m, Sphere n)) :
    joinedSphereMap f = SphereMapSuspension.map f := by
  apply ContinuousMap.ext
  intro x
  change coordinates n (RadialSphereJoin.sphereMap (G := ℝ) f ((coordinates m).symm x)) =
    SphereMapSuspension.map f x
  simpa only [Homeomorph.apply_symm_apply] using map_coordinates f ((coordinates m).symm x)

end Wikipedia.HopfProblem.DegreeCollapse.RadialJoinSuspension
