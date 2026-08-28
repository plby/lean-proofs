import Wikipedia.HopfProblem.MappingTorusHomology
import Mathlib.Algebra.Ring.GeomSum

/-!
# The actual homology norm of a finite-order homeomorphism

The norm is the sum of the actual singular homology maps of the powers of a
homeomorphism. Functoriality identifies it with the geometric sum of the induced
endomorphism. A finite-order relation gives equality with the inverse norm and
places its image in the kernel of the actual Wang difference.

The assertions also hold for `m = 0`; no nonzero-order hypothesis is needed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.MappingTorusHomology.Covering

open SingularMayerVietoris PeriodTorusHigherHomology
open scoped BigOperators

variable {X : Type} [TopologicalSpace X]

/-- Actual singular homology is multiplicative on self-homeomorphisms. -/
def monodromyHomologyMonoidHom (n : ℕ) :
    (X ≃ₜ X) →* Module.End ℤ (SingularHomology X n) where
  toFun B := monodromyHomologyMap B n
  map_one' := singularHomologyMap_id X n
  map_mul' B D := singularHomologyMap_comp (D : C(X, X)) (B : C(X, X)) n

/-- The actual homology map of a power is the corresponding power of the map. -/
@[simp] theorem monodromyHomologyMap_pow (B : X ≃ₜ X) (n k : ℕ) :
    monodromyHomologyMap (B ^ k) n = (monodromyHomologyMap B n) ^ k :=
  map_pow (monodromyHomologyMonoidHom (X := X) n) B k

/-- A finite-order relation remains an actual relation on singular homology. -/
theorem monodromyHomologyMap_pow_eq_one (m : ℕ) (B : X ≃ₜ X) (n : ℕ)
    (hB : B ^ m = 1) : (monodromyHomologyMap B n) ^ m = 1 := by
  rw [← monodromyHomologyMap_pow, hB]
  exact singularHomologyMap_id X n

/-- The norm formed from the actual homology maps of the powers of `B`. -/
def homologyNorm (m : ℕ) (B : X ≃ₜ X) (n : ℕ) :
    SingularHomology X n →ₗ[ℤ] SingularHomology X n :=
  ∑ k ∈ Finset.range m, singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n

@[simp] theorem homologyNorm_apply (m : ℕ) (B : X ≃ₜ X) (n : ℕ)
    (a : SingularHomology X n) :
    homologyNorm m B n a =
      ∑ k ∈ Finset.range m, singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n a := by
  simp only [homologyNorm, LinearMap.sum_apply]

/-- The actual norm equals the geometric sum of the induced endomorphism. -/
theorem homologyNorm_eq_sum_powers (m : ℕ) (B : X ≃ₜ X) (n : ℕ) :
    homologyNorm m B n = ∑ k ∈ Finset.range m, (monodromyHomologyMap B n) ^ k := by
  apply Finset.sum_congr rfl
  intro k _
  exact monodromyHomologyMap_pow B n k

@[simp] theorem homologyNorm_zero (B : X ≃ₜ X) (n : ℕ) :
    homologyNorm 0 B n = 0 := by
  simp only [homologyNorm, Finset.range_zero, Finset.sum_empty]

@[simp] theorem homologyNorm_one (B : X ≃ₜ X) (n : ℕ) :
    homologyNorm 1 B n = LinearMap.id := by
  rw [homologyNorm_eq_sum_powers]
  simp only [Finset.sum_range_one, pow_zero]
  rfl

private theorem sum_range_shift_of_endpoints {A : Type*} [AddCommGroup A]
    (F : ℕ → A) (m : ℕ) (hF : F m = F 0) :
    ∑ k ∈ Finset.range m, F (k + 1) = ∑ k ∈ Finset.range m, F k := by
  apply add_right_cancel (b := F 0)
  calc
    (∑ k ∈ Finset.range m, F (k + 1)) + F 0 =
        ∑ k ∈ Finset.range (m + 1), F k := (Finset.sum_range_succ' F m).symm
    _ = (∑ k ∈ Finset.range m, F k) + F 0 := by
      rw [Finset.sum_range_succ, hF]

/-- The finite-order relation identifies an inverse power with the complementary power. -/
theorem homeomorph_symm_pow_eq (m : ℕ) (B : X ≃ₜ X) (hB : B ^ m = 1)
    (k : ℕ) (hk : k ≤ m) : B.symm ^ k = B ^ (m - k) := by
  change B⁻¹ ^ k = B ^ (m - k)
  rw [pow_sub B hk, hB, one_mul, inv_pow]

/-- Reversing one complete period does not change the actual homology norm. -/
theorem homologyNorm_symm (m : ℕ) (B : X ≃ₜ X) (n : ℕ) (hB : B ^ m = 1) :
    homologyNorm m B.symm n = homologyNorm m B n := by
  unfold homologyNorm
  calc
    (∑ k ∈ Finset.range m, singularHomologyMap ((B.symm ^ k : X ≃ₜ X) : C(X, X)) n) =
        ∑ k ∈ Finset.range m,
          singularHomologyMap ((B ^ (m - 1 - k + 1) : X ≃ₜ X) : C(X, X)) n := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k < m := Finset.mem_range.mp hk
      have hexp : m - k = m - 1 - k + 1 := by omega
      rw [homeomorph_symm_pow_eq m B hB k hkm.le, hexp]
    _ = ∑ k ∈ Finset.range m, singularHomologyMap ((B ^ (k + 1) : X ≃ₜ X) : C(X, X)) n :=
      Finset.sum_range_reflect
        (fun k => singularHomologyMap ((B ^ (k + 1) : X ≃ₜ X) : C(X, X)) n) m
    _ = ∑ k ∈ Finset.range m, singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n := by
      apply sum_range_shift_of_endpoints
        (fun k => singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n) m
      rw [hB, pow_zero]

/-- The actual Wang difference kills the finite-order norm. -/
theorem wangDifference_comp_homologyNorm (m : ℕ) (B : X ≃ₜ X) (n : ℕ)
    (hB : B ^ m = 1) : (wangDifference B n).comp (homologyNorm m B n) = 0 := by
  change (1 - monodromyHomologyMap B n) * homologyNorm m B n = 0
  rw [homologyNorm_eq_sum_powers, mul_neg_geom_sum,
    monodromyHomologyMap_pow_eq_one m B n hB, sub_self]

/-- The norm also kills the image of the actual Wang difference. -/
theorem homologyNorm_comp_wangDifference (m : ℕ) (B : X ≃ₜ X) (n : ℕ)
    (hB : B ^ m = 1) : (homologyNorm m B n).comp (wangDifference B n) = 0 := by
  change homologyNorm m B n * (1 - monodromyHomologyMap B n) = 0
  rw [homologyNorm_eq_sum_powers, geom_sum_mul_neg,
    monodromyHomologyMap_pow_eq_one m B n hB, sub_self]

/-- Every value of the actual norm is invariant under the actual monodromy map. -/
theorem homologyNorm_range_le_ker_wangDifference (m : ℕ) (B : X ≃ₜ X) (n : ℕ)
    (hB : B ^ m = 1) :
    LinearMap.range (homologyNorm m B n) ≤ LinearMap.ker (wangDifference B n) := by
  rintro a ⟨b, rfl⟩
  exact LinearMap.congr_fun (wangDifference_comp_homologyNorm m B n hB) b

end Wikipedia.HopfProblem.MappingTorusHomology.Covering
