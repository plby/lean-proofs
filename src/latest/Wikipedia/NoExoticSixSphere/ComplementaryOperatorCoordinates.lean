import Wikipedia.NoExoticSixSphere.PartialFrameBlockSum
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Continuous coordinates from complementary injective operator families

The actual sum of two injective operators with disjoint ranges is a linear
equivalence when their dimensions add to the ambient dimension. Both the
coordinates and their inverses are continuous for continuous input families.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.OperatorSum

open GLOrthonormalization Function

variable {N n d : ℕ}

def operator (A : Vector n →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N) :
    Vector (n + d) →L[ℝ] Vector N :=
  ((A.comp (ContinuousLinearMap.fst ℝ _ _)) +
    (B.comp (ContinuousLinearMap.snd ℝ _ _))).comp
      EuclideanSpace.finAddEquivProd.toContinuousLinearMap

theorem operator_apply (A : Vector n →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N)
    (v : Vector (n + d)) : operator A B v =
      A (EuclideanSpace.finAddEquivProd v).1 + B (EuclideanSpace.finAddEquivProd v).2 := rfl

theorem range_operator (A : Vector n →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N) :
    (operator A B).range = A.range ⊔ B.range := by
  change LinearMap.range ((A.toLinearMap.coprod B.toLinearMap).comp
    EuclideanSpace.finAddEquivProd.toLinearEquiv.toLinearMap) = _
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), LinearMap.range_coprod]

theorem contDiffAt_operator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Vector n →L[ℝ] Vector N} {B : E → Vector d →L[ℝ] Vector N} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (fun y ↦ operator (A y) (B y)) x :=
  ((hA.clm_comp contDiffAt_const).add
    (hB.clm_comp contDiffAt_const)).clm_comp contDiffAt_const

theorem injective_operator (A : Vector n →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N)
    (hA : Injective A) (hB : Injective B) (hr : Disjoint A.range B.range) :
    Injective (operator A B) := by
  have hc : Injective (A.toLinearMap.coprod B.toLinearMap) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_coprod_of_disjoint_range _ _ hr,
      LinearMap.ker_eq_bot.mpr hA, LinearMap.ker_eq_bot.mpr hB, Submodule.prod_bot]
  exact hc.comp EuclideanSpace.finAddEquivProd.injective

theorem bijective_operator (A : Vector n →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N)
    (hA : Injective A) (hB : Injective B) (hr : Disjoint A.range B.range) (hN : n + d = N) :
    Bijective (operator A B) := by
  have hi := injective_operator A B hA hB hr
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℝ (Vector (n + d)) = Module.finrank ℝ (Vector N) from ?_)).mp hi
  simpa only [finrank_euclideanSpace_fin] using hN

def coordinates (A : Vector n →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N)
    (hA : Injective A) (hB : Injective B) (hr : Disjoint A.range B.range) (hN : n + d = N) :
    Vector (n + d) ≃L[ℝ] Vector N :=
  (LinearEquiv.ofBijective (operator A B).toLinearMap
    (bijective_operator A B hA hB hr hN)).toContinuousLinearEquiv

theorem coordinates_toContinuousLinearMap
    (A : Vector n →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N)
    (hA : Injective A) (hB : Injective B) (hr : Disjoint A.range B.range) (hN : n + d = N) :
    (coordinates A B hA hB hr hN).toContinuousLinearMap = operator A B := rfl

theorem coordinates_symm_toContinuousLinearMap
    (A : Vector n →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N)
    (hA : Injective A) (hB : Injective B) (hr : Disjoint A.range B.range) (hN : n + d = N) :
    (coordinates A B hA hB hr hN).symm.toContinuousLinearMap = (operator A B).inverse :=
  (ContinuousLinearMap.inverse_equiv (coordinates A B hA hB hr hN)).symm

variable {X : Type*} [TopologicalSpace X]

theorem continuous_operator (A : X → Vector n →L[ℝ] Vector N)
    (B : X → Vector d →L[ℝ] Vector N) (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x ↦ operator (A x) (B x)) :=
  ((hA.clm_comp continuous_const).add (hB.clm_comp continuous_const)).clm_comp continuous_const

theorem continuous_coordinates (A : X → Vector n →L[ℝ] Vector N)
    (B : X → Vector d →L[ℝ] Vector N) (hA : Continuous A) (hB : Continuous B)
    (hiA : ∀ x, Injective (A x)) (hiB : ∀ x, Injective (B x))
    (hr : ∀ x, Disjoint (A x).range (B x).range) (hN : n + d = N) :
    Continuous (fun x ↦
      (coordinates (A x) (B x) (hiA x) (hiB x) (hr x) hN).toContinuousLinearMap) :=
  continuous_operator A B hA hB

theorem continuous_inverse_coordinates (A : X → Vector n →L[ℝ] Vector N)
    (B : X → Vector d →L[ℝ] Vector N) (hA : Continuous A) (hB : Continuous B)
    (hiA : ∀ x, Injective (A x)) (hiB : ∀ x, Injective (B x))
    (hr : ∀ x, Disjoint (A x).range (B x).range) (hN : n + d = N) :
    Continuous (fun x ↦
      (coordinates (A x) (B x) (hiA x) (hiB x) (hr x) hN).symm.toContinuousLinearMap) := by
  rw [continuous_iff_continuousAt]
  intro x
  simp_rw [coordinates_symm_toContinuousLinearMap]
  have hi : (operator (A x) (B x)).IsInvertible :=
    ⟨coordinates (A x) (B x) (hiA x) (hiB x) (hr x) hN, rfl⟩
  exact ContinuousAt.comp (f := fun y : X ↦ operator (A y) (B y))
    (hi.contDiffAt_map_inverse (n := ∞)).continuousAt
    (continuous_operator A B hA hB).continuousAt

theorem operator_comp_block {k : ℕ} (A : Vector n →L[ℝ] Vector N)
    (B : Vector d →L[ℝ] Vector N) (a : Vector k →L[ℝ] Vector n) :
    (operator A B).comp (Stiefel.BlockSum.operator d a) = operator (A.comp a) B := by
  apply ContinuousLinearMap.ext
  intro v
  change operator A B (Stiefel.BlockSum.operator d a v) = operator (A.comp a) B v
  rw [Stiefel.BlockSum.operator_apply, operator_apply,
    ContinuousLinearEquiv.apply_symm_apply, operator_apply]
  rfl

end NoExoticSixSphere.OperatorSum
