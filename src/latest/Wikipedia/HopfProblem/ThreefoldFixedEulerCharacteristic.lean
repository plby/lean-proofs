import Wikipedia.HopfProblem.ThreefoldFiniteFixedHomologyIntegral
import Wikipedia.HopfProblem.ThreefoldHomologyFiniteness

/-!
# The Euler characteristic of the actual fixed locus

The original multiplicative action fixes a literal subset of the constructed
threefold. Its geometric two-sphere homeomorphism computes its actual integral
homology and rational Betti numbers. Their alternating sum is two, independently
of any cutoff above degree two, and equals the already proved Euler characteristic
of the ambient threefold. No fixed-point Euler theorem is assumed.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FixedEulerCharacteristic

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology
open FiniteFixedHomology ThreefoldHomologyFinitenessAlgebra

/-- The literal fixed subset for the original action of the full multiplicative group. -/
abbrev FixedSpace : Set Space := by
  letI := VerticalAction.action
  exact MulAction.fixedPoints ℂˣ Space

theorem fixedSpace_eq_D₀ : FixedSpace = VerticalAction.D₀ := by
  let := VerticalAction.action
  exact VerticalAction.fixedPoints_eq_D₀

/-- The comparison with the two-sphere uses the original fixed-curve parametrization. -/
def fixedSphereHomeomorph : FixedSpace ≃ₜ UnitSphere 2 :=
  (Homeomorph.setCongr
    (fixedSpace_eq_D₀.trans (rootsFixedSpace_eq_D₀ 2 (by decide)).symm)).trans
      (rootsFixedSphereHomeomorph 2 (by decide))

/-- Actual integral homology, transported by the geometric fixed-locus homeomorphism. -/
def fixedHomologyEquiv (n : ℕ) :
    SingularHomology FixedSpace n ≃ₗ[ℤ] SingularHomology (UnitSphere 2) n :=
  homeomorphHomologyEquiv fixedSphereHomeomorph n

@[simp] theorem fixedHomologyEquiv_toLinearMap (n : ℕ) :
    (fixedHomologyEquiv n).toLinearMap =
      singularHomologyMap (fixedSphereHomeomorph : C(FixedSpace, UnitSphere 2)) n := rfl

theorem fixedHomology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology FixedSpace n) :=
  Module.Free.of_equiv (fixedHomologyEquiv n).symm

theorem fixedHomology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology FixedSpace n) :=
  Module.Finite.of_surjective (fixedHomologyEquiv n).symm.toLinearMap
    (fixedHomologyEquiv n).symm.surjective

theorem fixedHomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology FixedSpace n) =
      if n = 0 ∨ n = 2 then 1 else 0 := by
  rw [(fixedHomologyEquiv n).finrank_eq]
  exact unitSphere_homology_finrank 1 n

theorem fixedHomology_subsingleton (n : ℕ) (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    Subsingleton (SingularHomology FixedSpace n) := by
  let := unitSphere_homology_subsingleton 1 n hn0 hn2
  exact (fixedHomologyEquiv n).injective.subsingleton

/-- Rationalization of the original integral singular homology of the actual fixed subset. -/
abbrev RationalHomology (n : ℕ) := ℚ ⊗[ℤ] SingularHomology FixedSpace n

theorem rationalHomology_finite (n : ℕ) : Module.Finite ℚ (RationalHomology n) := by
  let := fixedHomology_finite n
  exact rationalization_finite (SingularHomology FixedSpace n)

/-- Betti numbers of the genuine fixed-subspace homology, not assigned ranks. -/
def rationalBetti (n : ℕ) : ℕ := Module.finrank ℚ (RationalHomology n)

theorem rationalBetti_eq (n : ℕ) : rationalBetti n =
    if n = 0 ∨ n = 2 then 1 else 0 := by
  let := fixedHomology_free n
  change Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology FixedSpace n) = _
  rw [Module.finrank_baseChange]
  exact fixedHomology_finrank n

theorem rationalBetti_eq_zero_of_two_lt {n : ℕ} (hn : 2 < n) : rationalBetti n = 0 := by
  rw [rationalBetti_eq]
  simp [show n ≠ 0 by omega, show n ≠ 2 by omega]

/-- Every cutoff beyond the last actual nonzero homology degree gives two. -/
theorem euler_sum_eq_two (N : ℕ) (hN : 3 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (rationalBetti n : ℤ)) = 2 := by
  calc
    _ = ∑ n ∈ Finset.range 3, (-1 : ℤ) ^ n * (rationalBetti n : ℤ) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro n _ hn
      have hn' : 3 ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
      rw [rationalBetti_eq_zero_of_two_lt (by omega), Nat.cast_zero, mul_zero]
    _ = 2 := by norm_num [Finset.sum_range_succ, rationalBetti_eq]

/-- Euler characteristic from the actual, finitely supported rational homology. -/
def eulerCharacteristic : ℤ :=
  ∑ n ∈ Finset.range 3, (-1 : ℤ) ^ n * (rationalBetti n : ℤ)

theorem eulerCharacteristic_eq_two : eulerCharacteristic = 2 :=
  euler_sum_eq_two 3 (by decide)

theorem eulerCharacteristic_eq_sum (N : ℕ) (hN : 3 ≤ N) :
    eulerCharacteristic =
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (rationalBetti n : ℤ) :=
  eulerCharacteristic_eq_two.trans (euler_sum_eq_two N hN).symm

/-- The literal fixed-subspace Euler characteristic equals that of the original threefold. -/
theorem eulerCharacteristic_eq_ambient :
    eulerCharacteristic = Homology.Finiteness.eulerCharacteristic :=
  eulerCharacteristic_eq_two.trans Homology.Finiteness.eulerCharacteristic_eq_two.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FixedEulerCharacteristic
