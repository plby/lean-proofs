import Wikipedia.HopfProblem.ThreefoldHomotopyFive
import Wikipedia.HopfProblem.ThreefoldHomologyTopDegree
import Wikipedia.HopfProblem.SixthHurewicz

/-!
# Native sixth homotopy and a cube realizing the original top class

The constructed threefold is genuinely five-connected. The actual sixth
Hurewicz map therefore identifies its native sixth homotopy with its original
sixth singular homology, and hence with the integers. The generator is marked
by the preexisting cusp connecting/Wang coordinate, not a new orientation or
a stipulated sphere comparison.

In particular, an actual based six-cube realizes this original top homology
class. This is not yet a homotopy equivalence or a smooth sphere recognition.
There is no recognition hypothesis in this file.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopySix

open SingularMayerVietoris

/-- The original native sixth Hurewicz map is an equivalence on the actual threefold. -/
def hurewiczEquiv (x : Space) : Additive (π_ 6 Space x) ≃ₗ[ℤ] SingularHomology Space 6 := by
  letI := space_simplyConnected
  letI := HomotopyTwo.piTwo_subsingleton x
  letI := HomotopyThree.piThree_subsingleton x
  letI := HomotopyFour.piFour_subsingleton x
  letI := HomotopyFive.piFive_subsingleton x
  exact SixthHurewicz.hurewiczLinearEquiv x

@[simp] theorem hurewiczEquiv_toLinearMap (x : Space) :
    (hurewiczEquiv x).toLinearMap = SixthHurewicz.hurewiczMap x := rfl

/-- The forward map retains the original cube's actual singular homology class. -/
@[simp] theorem hurewiczEquiv_mk (x : Space) (p : GenLoop (Fin 6) Space x) :
    hurewiczEquiv x (Additive.ofMul (⟦p⟧ : π_ 6 Space x)) =
      SixthHurewicz.cubeHomologyClass p := rfl

/-- Native sixth homotopy is infinite cyclic in the original cusp marking. -/
def piSixEquiv (x : Space) : Additive (π_ 6 Space x) ≃ₗ[ℤ] ℤ :=
  (hurewiczEquiv x).trans Homology.TopDegree.homologySixEquiv

@[simp] theorem piSixEquiv_apply (x : Space) (a : Additive (π_ 6 Space x)) :
    piSixEquiv x a = Homology.TopDegree.homologySixEquiv (hurewiczEquiv x a) := rfl

/-- The native homotopy generator whose image is the preexisting marked top class. -/
def generator (x : Space) : Additive (π_ 6 Space x) :=
  (hurewiczEquiv x).symm Homology.TopDegree.topClass

@[simp] theorem hurewiczEquiv_generator (x : Space) :
    hurewiczEquiv x (generator x) = Homology.TopDegree.topClass :=
  (hurewiczEquiv x).apply_symm_apply _

@[simp] theorem piSixEquiv_generator (x : Space) : piSixEquiv x (generator x) = 1 := by
  rw [piSixEquiv_apply, hurewiczEquiv_generator, Homology.TopDegree.homologySixEquiv_topClass]

theorem generator_ne_zero (x : Space) : generator x ≠ 0 := by
  intro h
  have he := congrArg (piSixEquiv x) h
  rw [piSixEquiv_generator, map_zero] at he
  exact one_ne_zero he

/-- Every original sixth homotopy class is an integral multiple of this marked generator. -/
theorem eq_zsmul_generator (x : Space) (a : Additive (π_ 6 Space x)) :
    a = piSixEquiv x a • generator x := by
  apply (piSixEquiv x).injective
  rw [map_zsmul, piSixEquiv_generator]
  simp

/-- The original marked top class is realized by an actual based six-cube. -/
theorem exists_cube_topClass (x : Space) :
    ∃ p : GenLoop (Fin 6) Space x,
      SixthHurewicz.cubeHomologyClass p = Homology.TopDegree.topClass := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep (Additive.toMul (generator x))
  have hclass : Additive.ofMul (⟦p⟧ : π_ 6 Space x) = generator x :=
    congrArg Additive.ofMul hp
  exact ⟨p, (hurewiczEquiv_mk x p).symm.trans
    ((congrArg (hurewiczEquiv x) hclass).trans (hurewiczEquiv_generator x))⟩

/-- A genuine representative, for subsequent constructions of maps of spaces. -/
def generatingCube (x : Space) : GenLoop (Fin 6) Space x :=
  Classical.choose (exists_cube_topClass x)

@[simp] theorem generatingCube_homologyClass (x : Space) :
    SixthHurewicz.cubeHomologyClass (generatingCube x) = Homology.TopDegree.topClass :=
  Classical.choose_spec (exists_cube_topClass x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopySix
