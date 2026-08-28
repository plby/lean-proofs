import Wikipedia.HopfProblem.ThreefoldHomologyMiddleVanishing
import Wikipedia.HopfProblem.ThreefoldHomologyFifthDegree
import Wikipedia.HopfProblem.ThreefoldHomologyTopDegree
import Wikipedia.HopfProblem.ThreefoldHomologyFiniteness
import Wikipedia.HopfProblem.SixSphereHomology

/-!
# The constructed threefold is an integral homology six-sphere

The original attachment maps now determine every integral singular homology
group: degrees zero and six are infinite cyclic and every other degree vanishes.
The degree-zero marking is the actual positive augmentation; the degree-six
marking is the original cusp connecting/Wang marking.

The resulting degreewise linear equivalences with the standard six-sphere's
actual homology do not assert a continuous map, a homotopy equivalence, a
homeomorphism, or a diffeomorphism between the spaces.
-/

noncomputable section

open scoped TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomologySphere

open SingularMayerVietoris PeriodTorusHigherHomology Homology

/-- Every actual integral homology group except degrees zero and six is zero. -/
theorem homology_subsingleton (n : ℕ) (hn0 : n ≠ 0) (hn6 : n ≠ 6) :
    Subsingleton (SingularHomology Space n) := by
  by_cases hn : 6 < n
  · exact Finiteness.homology_subsingleton_of_lt hn
  have hn' : n ≤ 6 := Nat.le_of_not_gt hn
  interval_cases n
  · exact (hn0 rfl).elim
  · exact LowDegrees.singularH1_subsingleton
  · exact SecondDegree.homologyTwo_subsingleton
  · exact ThirdDegree.homologyThree_subsingleton
  · exact FourthDegree.homologyFour_subsingleton
  · exact FifthDegree.homologyFive_subsingleton
  · exact (hn6 rfl).elim

theorem homology_eq_zero (n : ℕ) (hn0 : n ≠ 0) (hn6 : n ≠ 6)
    (a : SingularHomology Space n) : a = 0 :=
  (homology_subsingleton n hn0 hn6).elim _ _

theorem homology_isZero (n : ℕ) (hn0 : n ≠ 0) (hn6 : n ≠ 6) :
    CategoryTheory.Limits.IsZero (SingularHomology Space n) := by
  let := homology_subsingleton n hn0 hn6
  exact ModuleCat.isZero_of_subsingleton _

/-- The complete integral homology is free; no torsion remains in an uncomputed degree. -/
theorem homology_free (n : ℕ) : Module.Free ℤ (SingularHomology Space n) := by
  by_cases hn0 : n = 0
  · subst n
    exact LowDegrees.singularH0_free
  by_cases hn6 : n = 6
  · subst n
    exact TopDegree.homologySix_free
  let := homology_subsingleton n hn0 hn6
  exact Module.Free.of_subsingleton ℤ _

theorem homology_finite (n : ℕ) : Module.Finite ℤ (SingularHomology Space n) :=
  Finiteness.homology_finite n

theorem homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology Space n) =
      if n = 0 ∨ n = 6 then 1 else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simpa using LowDegrees.singularH0_finrank
  by_cases hn6 : n = 6
  · subst n
    simpa using TopDegree.homologySix_finrank
  let := homology_subsingleton n hn0 hn6
  simp [hn0, hn6, Module.finrank_zero_of_subsingleton]

/-- These are the original rationalized singular Betti numbers of the constructed space. -/
theorem rationalBetti_eq (n : ℕ) : Finiteness.rationalBetti n =
    if n = 0 ∨ n = 6 then 1 else 0 := by
  let := homology_free n
  change Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology Space n) = _
  rw [Module.finrank_baseChange]
  exact homology_finrank n

/-- Comparison of the two genuine positive degree-zero augmentations. -/
def homologyZeroEquivSixSphere :
    SingularHomology Space 0 ≃ₗ[ℤ] SingularHomology SixSphere 0 :=
  LowDegrees.singularH0Equiv.trans SixSphereHomology.homologyZeroEquiv.symm

/-- Comparison of the original cusp-marked top class and the standard suspension-marked class. -/
def homologySixEquivSixSphere :
    SingularHomology Space 6 ≃ₗ[ℤ] SingularHomology SixSphere 6 :=
  TopDegree.homologySixEquiv.trans SixSphereHomology.homologySixEquiv.symm

/-- All-degree comparison of actual integral homology, without asserting a map of spaces. -/
def homologyEquivSixSphere (n : ℕ) :
    SingularHomology Space n ≃ₗ[ℤ] SingularHomology SixSphere n := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exact homologyZeroEquivSixSphere
  by_cases hn6 : n = 6
  · subst n
    exact homologySixEquivSixSphere
  let := homology_subsingleton n hn0 hn6
  let := SixSphereHomology.homology_subsingleton n hn0 hn6
  exact LinearEquiv.ofSubsingleton _ _

@[simp] theorem homologyEquivSixSphere_zero :
    homologyEquivSixSphere 0 = homologyZeroEquivSixSphere := by
  simp [homologyEquivSixSphere]

@[simp] theorem homologyEquivSixSphere_six :
    homologyEquivSixSphere 6 = homologySixEquivSixSphere := by
  simp [homologyEquivSixSphere]

/-- The chosen top generators correspond with coefficient positive one. -/
@[simp] theorem homologySixEquivSixSphere_topClass :
    homologySixEquivSixSphere TopDegree.topClass = SixSphereHomology.topClass := by
  rw [homologySixEquivSixSphere, LinearEquiv.trans_apply,
    TopDegree.homologySixEquiv_topClass]
  exact SixSphereHomology.homologySixEquiv.symm_apply_eq.mpr
    SixSphereHomology.homologySixEquiv_topClass.symm

/-- Every original point class maps to every standard-sphere point class in degree zero. -/
theorem homologyZeroEquivSixSphere_pointClass (x : Space) (y : SixSphere) :
    homologyZeroEquivSixSphere (pointClass x) = pointClass y := by
  apply SixSphereHomology.homologyZeroEquiv.injective
  rw [homologyZeroEquivSixSphere, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LowDegrees.singularH0Equiv_pointClass]
  exact (SphereHomology.unitSphereHomologyZeroEquiv_pointClass 5 y).symm

/-- The full integral homology-sphere assertion for the original constructed threefold. -/
theorem integralHomologySphere :
    Nonempty (SingularHomology Space 0 ≃ₗ[ℤ] ℤ) ∧
      Nonempty (SingularHomology Space 6 ≃ₗ[ℤ] ℤ) ∧
      ∀ n, n ≠ 0 → n ≠ 6 → Subsingleton (SingularHomology Space n) :=
  ⟨⟨LowDegrees.singularH0Equiv⟩, ⟨TopDegree.homologySixEquiv⟩, homology_subsingleton⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomologySphere
