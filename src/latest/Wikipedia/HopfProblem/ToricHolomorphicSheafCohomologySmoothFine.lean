import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothMultipliers
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineBasic
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Genuine fine decompositions for the smooth complex-function sheaf

A proved subordinate smooth partition of unity supplies actual sheaf
multipliers.  Their supports are the closed topological supports of the
partition functions, their sum is the identity, and their restrictions
outside those supports are zero.  No such assertion is made about the
holomorphic-function sheaf.
-/

noncomputable section

open Set Function TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SmoothFunctions

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- A genuine real smooth function, regarded as complex-valued through
the actual real-linear inclusion of the real line into the complex line. -/
def complexify (g : ContMDiffMap I 𝓘(ℝ) M ℝ ∞) : GlobalFunction I M :=
  ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp g.contMDiff⟩

@[simp] theorem complexify_apply (g : ContMDiffMap I 𝓘(ℝ) M ℝ ∞) (x : M) :
    complexify I M g x = (g x : ℂ) := rfl

variable {ι : Type} [Fintype ι]

/-- The actual complex-valued partition functions have literal sum one. -/
theorem complexify_partition_sum (ρ : SmoothPartitionOfUnity ι I M univ) :
    ∑ i, complexify I M (ρ i) = 1 := by
  classical
  apply ContMDiffMap.ext
  intro x
  change (ContMDiffMap.evalRingHom x : GlobalFunction I M →+* ℂ)
    (∑ i, complexify I M (ρ i)) = 1
  rw [map_sum]
  change (∑ i, (ρ i x : ℂ)) = 1
  have hsum : ∑ i, ρ i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  exact_mod_cast hsum

/-- An actual subordinate smooth partition gives a finite decomposition
of the genuine smooth-function sheaf, with its actual closed supports. -/
def partitionDecomposition {U : ι → Opens M} (ρ : SmoothPartitionOfUnity ι I M univ)
    (hρ : ρ.IsSubordinate (fun i => (U i : Set M))) :
    FiniteDecomposition (additiveSheaf I M) U where
  operator i := multiplier I M (complexify I M (ρ i))
  support i := tsupport (ρ i)
  support_closed _ := isClosed_closure
  subordinate := hρ
  zeroOutside i := by
    intro V hV
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ContMDiffMap.ext
    intro x
    have hzero : ρ i (x : M) = 0 :=
      notMem_support.mp (fun hx => hV x.property (subset_tsupport (ρ i) hx))
    change (ρ i (x : M) : ℂ) * s x = 0
    rw [hzero, Complex.ofReal_zero, zero_mul]
  total := by
    change ∑ i, multiplierRingHom I M (complexify I M (ρ i)) = 1
    rw [← map_sum, complexify_partition_sum, map_one]

/-- The genuine smooth complex-function sheaf is finite fine on every
finite-dimensional, Hausdorff, sigma-compact smooth real manifold.  These
are the standard hypotheses of the proved smooth partition theorem. -/
theorem finiteFine [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] : FiniteFine (additiveSheaf I M) := by
  intro ι _ U hU
  have hcover : (univ : Set M) ⊆ ⋃ i, (U i : Set M) := by
    intro x _
    obtain ⟨i, hi⟩ := hU x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i => (U i : Set M)) (fun i => (U i).isOpen) hcover
  exact ⟨partitionDecomposition I M ρ hρ⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SmoothFunctions
