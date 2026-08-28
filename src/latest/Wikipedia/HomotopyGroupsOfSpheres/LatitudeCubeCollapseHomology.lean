import Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapseFibers
import Wikipedia.HomotopyGroupsOfSpheres.SpherePinchHomology
import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenDegreeMagnitude

/-! # The actual latitude-to-cube comparison has degree of absolute value one -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapse

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open Wikipedia.HopfProblem.SingularMayerVietoris

theorem quotient_eq_point_iff (n : ℕ) (u : Fin n → I) :
    quotient n u = point n ↔ u ∈ Cube.boundary (Fin n) := by
  change compactification n (Wikipedia.HopfProblem.SixSphereCube.collapse
    (Cube.boundary (Fin n)) u) = compactification n OnePoint.infty ↔ _
  rw [(compactification n).injective.eq_iff,
    Wikipedia.HopfProblem.SixSphereCube.collapse_eq_infty_iff]

def cubeCenter (n : ℕ) : Fin n → I := fun _ ↦ ⟨1 / 2, by constructor <;> norm_num⟩

theorem cubeCenter_not_boundary (n : ℕ) : cubeCenter n ∉ Cube.boundary (Fin n) := by
  rintro ⟨i, h | h⟩
  · have he := congrArg (fun t : I ↦ (t : ℝ)) h
    norm_num [cubeCenter] at he
  · have he := congrArg (fun t : I ↦ (t : ℝ)) h
    norm_num [cubeCenter] at he

theorem quotient_cubeCenter_ne_point (n : ℕ) : quotient n (cubeCenter n) ≠ point n :=
  fun h ↦ cubeCenter_not_boundary n ((quotient_eq_point_iff n _).mp h)

theorem collapse_homology_bijective (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Function.Bijective (singularHomologyMap (collapse n hn) (k + 2)) := by
  obtain ⟨p, hp⟩ := collapse_surjective n hn (quotient (n + 2) (cubeCenter (n + 2)))
  exact SpherePinch.homologyMap_bijective (collapse n hn) (point (n + 2))
    (collapse_isQuotientMap n hn) (collapse_injective_off_point n hn) p
    (hp ▸ quotient_cubeCenter_ne_point (n + 2)) k

def collapseHomologyEquiv (n : ℕ) (hn : 0 < n) (k : ℕ) :
    SingularHomology (Sphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularHomology (Sphere (n + 2)) (k + 2) :=
  LinearEquiv.ofBijective (singularHomologyMap (collapse n hn) (k + 2))
    (collapse_homology_bijective n hn k)

theorem collapseHomologyEquiv_apply (n : ℕ) (hn : 0 < n) (k : ℕ)
    (a : SingularHomology (Sphere (n + 2)) (k + 2)) :
    collapseHomologyEquiv n hn k a = singularHomologyMap (collapse n hn) (k + 2) a := rfl

theorem collapse_five_degree_natAbs : Int.natAbs (sphereSevenDegree (collapse 5 (by decide))) = 1 :=
  sphereSevenDegree_natAbs_of_homology_smul (collapse 5 (by decide)) 1
    (collapseHomologyEquiv 5 (by decide) 5) (fun a ↦ by
      rw [one_smul, collapseHomologyEquiv_apply])

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapse
