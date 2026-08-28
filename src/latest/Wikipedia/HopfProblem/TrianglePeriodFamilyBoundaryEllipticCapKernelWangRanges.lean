import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangOne
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTwo

/-!
# Exact ranges of the original elliptic cap-kernel Wang coordinates

The two genuine columns generate each actual image. The original surface
markings and their shear corrections are retained. The output coordinates
also show that both actual maps are injective.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris
open SpecialPeriods.EllipticFilling

local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

private theorem range_eq_span_two_columns {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] (Fin 2 → R)) (f : M →ₗ[R] N) :
    LinearMap.range f = Submodule.span R
      ({f (e.symm ![1, 0]), f (e.symm ![0, 1])} : Set N) := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    apply Submodule.mem_span_pair.mpr
    refine ⟨e a 0, e a 1, ?_⟩
    have ha : a = e a 0 • e.symm ![1, 0] + e a 1 • e.symm ![0, 1] := by
      apply e.injective
      simp only [map_add, map_smul, LinearEquiv.apply_symm_apply]
      ext i
      fin_cases i <;> simp
    simpa only [map_add, map_smul] using (congrArg f ha).symm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      exact ⟨e.symm ![1, 0], rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨e.symm ![0, 1], rfl⟩

/-- The exact actual degree-two Wang image, in the original period-loop coordinates. -/
theorem h1Coordinates_range (j : Kind) :
    LinearMap.range (h1Coordinates j) = Submodule.span ℤ
      ({(fibreNormIndex j : ℤ) • deltaVector,
        j.twist - h1ShearCorrection j • deltaVector} : Set Lattice) := by
  rw [range_eq_span_two_columns (surfaceH1Equiv j (specialLocalData j).centralPeriod),
    h1Coordinates_first_axis, h1Coordinates_second_axis]

/-- The exact actual degree-three Wang image, in the original six-minor coordinates. -/
theorem h2Coordinates_range (j : Kind) :
    LinearMap.range (h2Coordinates j) = Submodule.span ℤ
      ({(fibreNormIndex j : ℤ) • fibreInvariantPairVector j,
        twistDeltaVector j - sourceShearTwo j • fibreInvariantPairVector j} : Set (Fin 6 → ℤ)) := by
  rw [range_eq_span_two_columns (surfaceH2Equiv j (specialLocalData j).centralPeriod),
    h2Coordinates_first_axis, h2Coordinates_second_axis]

private theorem span_pair_sub_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x y : M) (k : R) :
    Submodule.span R ({x, y - k • x} : Set M) = Submodule.span R ({x, y} : Set M) := by
  ext z
  rw [Submodule.mem_span_pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a - b * k, b, ?_⟩
    simp only [sub_smul, smul_sub, smul_smul]
    abel
  · rintro ⟨a, b, rfl⟩
    refine ⟨a + b * k, b, ?_⟩
    simp only [add_smul, smul_sub, smul_smul]
    abel

/-- For order three the primitive first column absorbs the genuine integral shear. -/
theorem h1Coordinates_range_three :
    LinearMap.range (h1Coordinates .three) =
      Submodule.span ℤ ({deltaVector, Kind.three.twist} : Set Lattice) := by
  rw [h1Coordinates_range]
  simp only [fibreNormIndex_three, Nat.cast_one, one_smul]
  exact span_pair_sub_smul deltaVector Kind.three.twist (h1ShearCorrection .three)

private theorem ranges_twist_zero_ne_zero (j : Kind) : j.twist 0 ≠ 0 := by
  cases j <;> decide

private theorem ranges_h1_zero (j : Kind) (a : SingularHomology (S j) 1) :
    h1Coordinates j a 0 =
      surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 * j.twist 0 := by
  rw [h1Coordinates_formula]
  simp [deltaVector]

private theorem ranges_h1_three (j : Kind) (a : SingularHomology (S j) 1) :
    h1Coordinates j a 3 =
      (fibreNormIndex j : ℤ) * surfaceH1Equiv j (specialLocalData j).centralPeriod a 0 -
        h1ShearCorrection j * surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 := by
  rw [h1Coordinates_formula]
  simp [deltaVector, twist_fourth_zero]

/-- The original first-homology Wang coordinate map is injective. -/
theorem h1Coordinates_injective (j : Kind) : Function.Injective (h1Coordinates j) := by
  intro a b hab
  let e := surfaceH1Equiv j (specialLocalData j).centralPeriod
  have h₁ : e a 1 = e b 1 := by
    apply mul_right_cancel₀ (ranges_twist_zero_ne_zero j)
    simpa only [ranges_h1_zero] using congrFun hab (0 : Fin 4)
  have hδ := congrFun hab (3 : Fin 4)
  rw [ranges_h1_three, ranges_h1_three, h₁] at hδ
  have h₀ : e a 0 = e b 0 := by
    apply mul_left_cancel₀ (fibreNormIndex_int_ne_zero j)
    linarith only [hδ]
  apply e.injective
  funext i
  fin_cases i
  · exact h₀
  · exact h₁

private theorem ranges_fibre_kernel_zero_ne_zero (j : Kind) :
    fibreSquareKernelVector j 0 ≠ 0 := by
  cases j <;> decide

private theorem ranges_h2_two (j : Kind) (a : SingularHomology (S j) 2) :
    h2Coordinates j a 2 =
      surfaceH2Equiv j (specialLocalData j).centralPeriod a 1 * j.twist 0 := by
  rw [h2Coordinates_formula]
  simp [fibreInvariantPairVector, twistDeltaVector]

private theorem ranges_h2_three (j : Kind) (a : SingularHomology (S j) 2) :
    h2Coordinates j a 3 =
      ((fibreNormIndex j : ℤ) * surfaceH2Equiv j (specialLocalData j).centralPeriod a 0 -
        sourceShearTwo j * surfaceH2Equiv j (specialLocalData j).centralPeriod a 1) *
          fibreSquareKernelVector j 0 := by
  rw [h2Coordinates_formula]
  simp [fibreInvariantPairVector, twistDeltaVector]

/-- The original second-homology Wang coordinate map is injective. -/
theorem h2Coordinates_injective (j : Kind) : Function.Injective (h2Coordinates j) := by
  intro a b hab
  let e := surfaceH2Equiv j (specialLocalData j).centralPeriod
  have h₁ : e a 1 = e b 1 := by
    apply mul_right_cancel₀ (ranges_twist_zero_ne_zero j)
    simpa only [ranges_h2_two] using congrFun hab (2 : Fin 6)
  have hL := congrFun hab (3 : Fin 6)
  rw [ranges_h2_three, ranges_h2_three] at hL
  have hcoef := mul_right_cancel₀ (ranges_fibre_kernel_zero_ne_zero j) hL
  rw [h₁] at hcoef
  have h₀ : e a 0 = e b 0 := by
    apply mul_left_cancel₀ (fibreNormIndex_int_ne_zero j)
    linarith only [hcoef]
  apply e.injective
  funext i
  fin_cases i
  · exact h₀
  · exact h₁

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
