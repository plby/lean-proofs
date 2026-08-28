import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegers
import Wikipedia.HopfProblem.HolomorphicExponentialSheafUnits
import Wikipedia.HopfProblem.HolomorphicExponentialSheafLocalLog
import Wikipedia.HopfProblem.HolomorphicExponentialSheafExactLocal
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# The genuine holomorphic exponential short exact sequence

The first arrow sends an integer to the holomorphic constant `2πi n`.
The second arrow is the ordinary complex exponential, with target the
actual units of the holomorphic section rings. Constructed local
logarithms give epimorphy, and actual local integer representatives give
the kernel. Exactness is proved in the native category of abelian sheaves.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The two actual sheaf arrows compose to the additive zero of the
units sheaf, namely the multiplicative constant `1`. -/
theorem integerInclusion_exponential :
    (integerInclusion I M ≫ exponential I M :
      (show TopCat.Sheaf AddCommGrpCat (TopCat.of M) from integerSheaf (TopCat.of M)) ⟶
        unitsSheaf I M) = 0 := by
  apply integerHom_ext_on_constants
  intro U n
  apply unitSection_ext
  intro x
  change unitSectionEval ((exponential I M).hom.app (op U)
    ((integerInclusion I M).hom.app (op U)
      ((integerUnit (TopCat.of M)).app (op U) n))) x =
        unitSectionEval (0 : UnitSection I M U) x
  change Complex.exp ((fun f : HolomorphicFunctionSheaf.Section I M U => f x)
    ((integerInclusion I M).hom.app (op U)
      ((integerUnit (TopCat.of M)).app (op U) n))) = 1
  exact (congrArg Complex.exp (integerInclusion_app_unit_apply I M U n x)).trans
    (Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩)

/-- The three actual sheaves with their literal normalized maps. -/
abbrev exponentialComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of M)) :=
  ShortComplex.mk (integerInclusion I M) (exponential I M) (integerInclusion_exponential I M)

/-- Local analytic logarithms make the ordinary exponential an actual
epimorphism of sheaves, not an assertion of global logarithms on each open set. -/
instance exponential_epi : Epi (exponential I M) := by
  apply HolomorphicSheafCohomology.DolbeaultLocal.epi_of_local_section_lifts
  intro U x hx u
  obtain ⟨V, hVU, hxV, g, hg⟩ := exists_localSectionLog I M
    (unitSectionVal u) ⟨x, hx⟩ (unitSectionEval_ne_zero u ⟨x, hx⟩)
  refine ⟨V, hVU, hxV, g, ?_⟩
  apply unitSection_ext
  intro y
  change Complex.exp (g y) = (unitSectionVal u) ⟨y, hVU y.property⟩
  exact hg y

/-- The actual constant integer sheaf is the kernel of the ordinary
exponential, with its specified `2πi` normalization. -/
theorem exponentialComplex_exact : (exponentialComplex I M).Exact := by
  apply exact_of_local_section_kernels
  intro U x hx f hf
  change HolomorphicFunctionSheaf.Section I M U at f
  change (exponential I M).hom.app (op U) f = 0 at hf
  have hpoint : ∀ y : U, Complex.exp (f y) = 1 := by
    intro y
    have h := congrArg (fun u : UnitSection I M U => unitSectionEval u y) hf
    change Complex.exp (f y) = 1 at h
    exact h
  obtain ⟨V, hVU, hxV, n, hn⟩ := exists_localKernelInteger I M f hpoint ⟨x, hx⟩
  refine ⟨V, hVU, hxV, (integerUnit (TopCat.of M)).app (op V) n, ?_⟩
  apply ContMDiffMap.ext
  intro y
  change (fun g : HolomorphicFunctionSheaf.Section I M V => g y)
    ((integerInclusion I M).hom.app (op V)
    ((integerUnit (TopCat.of M)).app (op V) n)) = f ⟨y, hVU y.property⟩
  rw [integerInclusion_app_unit_apply]
  exact (hn y).symm

/-- The genuine sequence `0 → ℤ → O → O* → 0` is short exact.
All local analytic and categorical exactness assertions have been proved. -/
theorem exponentialComplex_shortExact : (exponentialComplex I M).ShortExact :=
  { exact := exponentialComplex_exact I M
    mono_f := integerInclusion_mono I M
    epi_g := exponential_epi I M }

/-- On every open set, the kernel consists of genuine sections of the
constant integer sheaf; these need not be globally constant integers. -/
theorem exists_integerSection_of_exp_eq_one (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) (hf : ∀ x : U, Complex.exp (f x) = 1) :
    ∃ n : (integerSheaf (TopCat.of M)).obj.obj (op U),
      (integerInclusion I M).hom.app (op U) n = f := by
  apply TopCat.Sheaf.sections_exact_of_left_exact (exponentialComplex_exact I M)
    (exponentialComplex_shortExact I M).mono_f f
  apply unitSection_ext
  intro x
  exact hf x

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
