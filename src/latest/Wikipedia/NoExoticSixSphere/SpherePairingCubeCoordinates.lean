import Wikipedia.NoExoticSixSphere.JamesSpherePairingQuotient
import Wikipedia.NoExoticSixSphere.CubicalSuspensionCoordinates
import Wikipedia.NoExoticSixSphere.NativeSpherePermutations

/-!
# Exact cube coordinates for the original equal-factor sphere pairing

The product of the two original cube quotients is their concatenated
coordinate cube, including all boundary faces. Consequently an actual
permutation exchanging the two coordinate blocks exchanges the original
sphere factors. This retains the map needed for native smash squares.
-/

noncomputable section

open scoped Topology unitInterval OnePoint

namespace NoExoticSixSphere.JamesSphere.PairingCoordinates

theorem append_boundary_iff {n : ℕ} (u v : Fin n → I) :
    Fin.append u v ∈ Cube.boundary (Fin (n + n)) ↔
      u ∈ Cube.boundary (Fin n) ∨ v ∈ Cube.boundary (Fin n) := by
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.addCases (fun j hj ↦ ?_) (fun j hj ↦ ?_) i hi
    · exact Or.inl ⟨j, by simpa only [Fin.append_left] using hj⟩
    · exact Or.inr ⟨j, by simpa only [Fin.append_right] using hj⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i.castAdd n, by simpa only [Fin.append_left] using hi⟩
    · exact ⟨i.natAdd n, by simpa only [Fin.append_right] using hi⟩

theorem pairing_cubes (n : ℕ) (u v : Fin n → I) :
    pairing n (SmoothCube.quotient n u, SmoothCube.quotient n v) =
      SmoothCube.quotient (n + n) (Fin.append u v) := by
  by_cases hu : u ∈ Cube.boundary (Fin n)
  · rw [SmoothCube.quotient_boundary n u hu, pairing_left_pole,
      SmoothCube.quotient_boundary (n + n) _ ((append_boundary_iff u v).mpr (Or.inl hu))]
  by_cases hv : v ∈ Cube.boundary (Fin n)
  · rw [SmoothCube.quotient_boundary n v hv, pairing_right_pole,
      SmoothCube.quotient_boundary (n + n) _ ((append_boundary_iff u v).mpr (Or.inr hv))]
  have huv : Fin.append u v ∉ Cube.boundary (Fin (n + n)) := by
    rw [append_boundary_iff]
    exact not_or.mpr ⟨hu, hv⟩
  change euclideanOnePointSphere (n + n)
    ((EuclideanFactorProduct.productCoordinates n n).onePointCongr
      (OnePointProduct.map
        ((euclideanOnePointSphere n).symm (SmoothCube.quotient n u),
          (euclideanOnePointSphere n).symm (SmoothCube.quotient n v)))) = _
  rw [CubicalSphereSuspension.quotient_finite_coordinates n u hu,
    CubicalSphereSuspension.quotient_finite_coordinates n v hv, OnePointProduct.map_coe]
  have he : EuclideanFactorProduct.productCoordinates n n
      (SmoothCube.coordinate n (SmoothCube.vectorOfCube n u),
        SmoothCube.coordinate n (SmoothCube.vectorOfCube n v)) =
      SmoothCube.coordinate (n + n) (SmoothCube.vectorOfCube (n + n) (Fin.append u v)) := by
    apply PiLp.ext
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [EuclideanFactorProduct.productCoordinates, SmoothCube.coordinate,
        SmoothCube.vectorOfCube]
    · simp [EuclideanFactorProduct.productCoordinates, SmoothCube.coordinate,
        SmoothCube.vectorOfCube]
      have hj : j.addNat n = Fin.natAdd n j := by
        apply Fin.ext
        exact Nat.add_comm _ _
      rw [hj, finSumFinEquiv_symm_apply_natAdd, Fin.append_right]
  change euclideanOnePointSphere (n + n)
    (↑(EuclideanFactorProduct.productCoordinates n n
      (SmoothCube.coordinate n (SmoothCube.vectorOfCube n u),
        SmoothCube.coordinate n (SmoothCube.vectorOfCube n v)))) = _
  rw [he]
  exact (congrArg (euclideanOnePointSphere (n + n))
    (CubicalSphereSuspension.quotient_finite_coordinates (n + n) (Fin.append u v) huv)).symm.trans
      ((euclideanOnePointSphere (n + n)).apply_symm_apply _)

theorem pairing_swap_of_coordinates (n : ℕ) (hn : 0 < n)
    (e : Equiv.Perm (Fin (n + n)))
    (he : ∀ u v : Fin n → I, Fin.append v u = fun j ↦ Fin.append u v (e j))
    (x y : Sphere n) :
    pairing n (y, x) = SmoothCube.permutation (n + n) (by omega) e (pairing n (x, y)) := by
  obtain ⟨u, rfl⟩ := SmoothCube.quotient_surjective hn x
  obtain ⟨v, rfl⟩ := SmoothCube.quotient_surjective hn y
  rw [pairing_cubes, pairing_cubes, SmoothCube.permutation_quotient, he]

end NoExoticSixSphere.JamesSphere.PairingCoordinates
