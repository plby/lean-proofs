import Wikipedia.HopfProblem.ThreefoldHomologyFourthWangInvariants
import Wikipedia.HopfProblem.ThreefoldHomologyStar
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspSourceProjection

/-!
# Cancellation of the actual three boundary Wang classes

The original cusp column and both original elliptic columns are applied
to the literal sum of overlap inclusions.  If that regular-family image
is zero, the three Wang classes agree and are fixed by both original
source generators.  All signs and the inverse first-generator action
come from the already proved geometric boundary comparisons.

This does not discard the regular fibre component or assert that the
full attachment map is injective.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthWang

open SingularMayerVietoris ThreefoldOverlapMappingTorus TrianglePeriodFamily
open TrianglePeriodFamily.Homology

local notation "Dsp" => TrianglePeriodFamily.regularData
  specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The two actual source-kernel coordinates, with the kernel subtype forgotten. -/
def regularSourcePair (n : ℕ) :
    SingularHomology SpecialRegularFamily (n + 1) →ₗ[ℤ]
      (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun := fun a => (sourceKernelProjection Dsp n a).val
      map_zero' := congrArg Subtype.val (map_zero (sourceKernelProjection Dsp n))
      map_add' := fun a b => congrArg Subtype.val (map_add (sourceKernelProjection Dsp n) a b) }

@[simp] theorem regularSourcePair_apply (n : ℕ)
    (a : SingularHomology SpecialRegularFamily (n + 1)) :
    regularSourcePair n a = (sourceKernelProjection Dsp n a).val := rfl

/-- The original overlap's actual Wang class through its actual boundary equivalence. -/
def overlapWangHomologyMap (i : Puncture) (n : ℕ) :
    SingularHomology (RegularOverlap i) (n + 1) →ₗ[ℤ] SingularHomology RealTorus₄ n :=
  (MappingTorusHomology.wangBoundary (monodromy i) n).comp
    (overlapHomologyEquiv i (n + 1)).toLinearMap

@[simp] theorem overlapWangHomologyMap_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology (RegularOverlap i) (n + 1)) :
    overlapWangHomologyMap i n a = MappingTorusHomology.wangBoundary (monodromy i) n
      (overlapHomologyEquiv i (n + 1) a) := rfl

/-- The proved three geometric source columns, in their original order. -/
def sourceColumn (i : Puncture) (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n :=
  match i with
  | none => (-triangleHomologyEquiv triangleGenerator₁⁻¹ n a, -a)
  | some .three => (a, 0)
  | some .four => (0, a)

/-- The literal boundary-to-regular coefficient has its proved native source column. -/
theorem regularSourcePair_boundary (i : Puncture) (n : ℕ)
    (a : SingularHomology (Boundary i) (n + 1)) :
    regularSourcePair n (boundaryRegularHomologyMap i (n + 1) a) =
      sourceColumn i n (MappingTorusHomology.wangBoundary (monodromy i) n a) := by
  rw [regularSourcePair_apply]
  cases i with
  | none =>
    simpa only [sourceColumn, monodromy] using!
      (TrianglePeriodFamily.Boundary.Cusp.boundary_sourceKernelProjection n a)
  | some j =>
    cases j with
    | three =>
      simpa only [sourceColumn, monodromy] using!
        (TrianglePeriodFamily.Boundary.ellipticThreeBoundary_sourceKernelProjection n a)
    | four =>
      simpa only [sourceColumn, monodromy] using!
        (TrianglePeriodFamily.Boundary.ellipticFourBoundary_sourceKernelProjection n a)

/-- Transfer that actual formula to each original full overlap. -/
theorem regularSourcePair_overlap (i : Puncture) (n : ℕ)
    (a : SingularHomology (RegularOverlap i) (n + 1)) :
    regularSourcePair n (singularHomologyMap (overlapToRegularFamily i) (n + 1) a) =
      sourceColumn i n (overlapWangHomologyMap i n a) := by
  have h := LinearMap.congr_fun (boundaryRegularHomologyMap_retraction i (n + 1)) a
  change boundaryRegularHomologyMap i (n + 1) (overlapHomologyEquiv i (n + 1) a) =
    singularHomologyMap (overlapToRegularFamily i) (n + 1) a at h
  rw [← h]
  exact regularSourcePair_boundary i n _

/-- The original three-column sum retains both genuine regular source coordinates. -/
theorem regularSourcePair_star (n : ℕ) (a : StarOverlapHomology (n + 1)) :
    regularSourcePair n (starOverlapToRegularHomologyMap (n + 1) a) =
      (overlapWangHomologyMap (some .three) n (a (some .three)) -
          triangleHomologyEquiv triangleGenerator₁⁻¹ n (overlapWangHomologyMap none n (a none)),
        overlapWangHomologyMap (some .four) n (a (some .four)) -
          overlapWangHomologyMap none n (a none)) := by
  classical
  rw [starOverlapToRegularHomologyMap_apply, map_sum]
  simp only [regularSourcePair_overlap]
  rw [Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)]
  simp only [sourceColumn, Prod.mk_add_mk, add_zero, zero_add, sub_eq_add_neg]
  exact Prod.ext (add_comm _ _) (add_comm _ _)

/-- A zero actual regular image forces equality and common invariance of all three Wang classes. -/
theorem wang_cancellation (n : ℕ) (a : StarOverlapHomology (n + 1))
    (ha : starOverlapToRegularHomologyMap (n + 1) a = 0) :
    overlapWangHomologyMap (some .three) n (a (some .three)) =
        overlapWangHomologyMap none n (a none) ∧
      overlapWangHomologyMap (some .four) n (a (some .four)) =
        overlapWangHomologyMap none n (a none) ∧
      generatorHomologyEquiv false n (overlapWangHomologyMap none n (a none)) =
        overlapWangHomologyMap none n (a none) ∧
      generatorHomologyEquiv true n (overlapWangHomologyMap none n (a none)) =
        overlapWangHomologyMap none n (a none) := by
  let w₀ := overlapWangHomologyMap none n (a none)
  let w₃ := overlapWangHomologyMap (some .three) n (a (some .three))
  let w₄ := overlapWangHomologyMap (some .four) n (a (some .four))
  have h := regularSourcePair_star n a
  rw [ha, map_zero] at h
  have h₃ : w₃ = triangleHomologyEquiv triangleGenerator₁⁻¹ n w₀ :=
    sub_eq_zero.mp (congrArg Prod.fst h).symm
  have h₄ : w₄ = w₀ := sub_eq_zero.mp (congrArg Prod.snd h).symm
  have hf₃ : generatorHomologyEquiv false n w₃ = w₃ :=
    TrianglePeriodFamily.Boundary.ellipticWangBoundary_generator_fixed
      .three Elliptic.Kind.three.twist n (overlapHomologyEquiv (some .three) (n + 1) _)
  have hf₄ : generatorHomologyEquiv true n w₄ = w₄ :=
    TrianglePeriodFamily.Boundary.ellipticWangBoundary_generator_fixed
      .four Elliptic.Kind.four.twist n (overlapHomologyEquiv (some .four) (n + 1) _)
  have he₃ : w₃ = w₀ := by
    rw [triangleHomologyEquiv_inv] at h₃
    calc
      w₃ = generatorHomologyEquiv false n w₃ := hf₃.symm
      _ = generatorHomologyEquiv false n ((generatorHomologyEquiv false n).symm w₀) :=
        congrArg (generatorHomologyEquiv false n) h₃
      _ = w₀ := LinearEquiv.apply_symm_apply _ _
  refine ⟨he₃, h₄, ?_, ?_⟩
  · simpa only [he₃] using hf₃
  · simpa only [h₄] using hf₄

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthWang
