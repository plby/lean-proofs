import Wikipedia.HopfProblem.DegreeCollapseRadialJoinNaturality
import Wikipedia.NoExoticSixSphere.IteratedSphereSuspension

/-!
# A finite radial join is the original iterated sphere suspension

Recursively specified linear isometries move each newly added coordinate
to the front. The comparison is proved first for the whole ambient
radial extensions, then restricted to the actual unit spheres. Thus
nullhomotopy agrees with the original iterate at every specified stage.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialJoinIteration

open RadialSphereMap HopfBlockCoordinates RadialJoinNaturality
open RadialJoinSuspension (rightCoordinates)

def realCoordinate : ℝ ≃ₗᵢ[ℝ] Vector 1 where
  toFun t := WithLp.toLp 2 (fun _ : Fin 1 ↦ t)
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    apply PiLp.ext
    intro i
    exact congrArg x (Subsingleton.elim 0 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' t := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ _i : Fin 1, t ^ 2) = ‖t‖ ^ 2
    simp only [Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]

def coordinateStep (r : ℕ) : WithLp 2 (Vector r × ℝ) ≃ₗᵢ[ℝ] Vector (r + 1) :=
  (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ (Vector r))
    realCoordinate).trans
      (((EuclideanSpace.basisFun (Fin r) ℝ).prod (EuclideanSpace.basisFun (Fin 1) ℝ)).equiv
        (EuclideanSpace.basisFun (Fin (r + 1)) ℝ) finSumFinEquiv)

def coordinates (m : ℕ) : (r : ℕ) →
    WithLp 2 (Vector (m + 1) × Vector r) ≃ₗᵢ[ℝ] Vector (m + r + 1)
  | 0 => LinearIsometryEquiv.withLpProdUnique 2 ℝ (Vector (m + 1)) (Vector 0)
  | r + 1 =>
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ (Vector (m + 1)))
      (coordinateStep r).symm).trans
        ((LinearIsometryEquiv.withLpProdAssoc 2 ℝ (Vector (m + 1)) (Vector r) ℝ).symm.trans
          ((LinearIsometryEquiv.withLpProdCongr 2 (coordinates m r)
            (LinearIsometryEquiv.refl ℝ ℝ)).trans (rightCoordinates (m + r))))

theorem coordinates_zero_apply (m : ℕ) (x : WithLp 2 (Vector (m + 1) × Vector 0)) :
    coordinates m 0 x = x.fst := rfl

theorem coordinates_succ_apply (m r : ℕ) (x : WithLp 2 (Vector (m + 1) × Vector (r + 1))) :
    coordinates m (r + 1) x = rightCoordinates (m + r)
      (WithLp.toLp 2 (coordinates m r
        (WithLp.toLp 2 (x.fst, ((coordinateStep r).symm x.snd).fst)),
          ((coordinateStep r).symm x.snd).snd)) := rfl

variable {m n : ℕ}

theorem extend_suspension_coordinates (f : C(Sphere m, Sphere n))
    (x : WithLp 2 (Vector (m + 1) × ℝ)) :
    extend (SphereMapSuspension.map f) (rightCoordinates m x) =
      rightCoordinates n (RadialSphereJoin.vector f x) := by
  have h := extend_naturality (rightCoordinates m) (rightCoordinates n)
    (RadialSphereJoin.sphereMap (G := ℝ) f) (SphereMapSuspension.map f)
    (fun y ↦ (RadialJoinSuspension.map_coordinates f y).symm) x
  rw [RadialSphereJoin.extend_sphereMap] at h
  exact h

theorem extend_iterate_coordinates (f : C(Sphere m, Sphere n)) (r : ℕ)
    (x : WithLp 2 (Vector (m + 1) × Vector r)) :
    extend (SphereMapSuspension.iterate f r) (coordinates m r x) =
      coordinates n r (RadialSphereJoin.vector f x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change extend (SphereMapSuspension.map (SphereMapSuspension.iterate f r))
      (coordinates m (r + 1) x) = _
    rw [coordinates_succ_apply, extend_suspension_coordinates, coordinates_succ_apply]
    apply congrArg (rightCoordinates (n + r))
    apply congrArg (WithLp.toLp 2)
    apply Prod.ext
    · exact ih (WithLp.toLp 2 (x.fst, ((coordinateStep r).symm x.snd).fst))
    · rfl

theorem sphereMap_coordinates (f : C(Sphere m, Sphere n)) (r : ℕ)
    (x : UnitSphere (WithLp 2 (Vector (m + 1) × Vector r))) :
    unitSphereCoordinates (coordinates n r) (RadialSphereJoin.sphereMap (G := Vector r) f x) =
      SphereMapSuspension.iterate f r (unitSphereCoordinates (coordinates m r) x) := by
  apply Subtype.ext
  exact (extend_iterate_coordinates f r x.val).symm.trans
    (extend_unit (SphereMapSuspension.iterate f r) (unitSphereCoordinates (coordinates m r) x))

theorem nullhomotopic_iff_iterate (f : C(Sphere m, Sphere n)) (r : ℕ) :
    (RadialSphereJoin.sphereMap (G := Vector r) f).Nullhomotopic ↔
      (SphereMapSuspension.iterate f r).Nullhomotopic :=
  nullhomotopic_iff_of_homeomorph_square (unitSphereCoordinates (coordinates m r))
    (unitSphereCoordinates (coordinates n r)) (RadialSphereJoin.sphereMap f)
    (SphereMapSuspension.iterate f r) (sphereMap_coordinates f r)

end Wikipedia.HopfProblem.DegreeCollapse.RadialJoinIteration
