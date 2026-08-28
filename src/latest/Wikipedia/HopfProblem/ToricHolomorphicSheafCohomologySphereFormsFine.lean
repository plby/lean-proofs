import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsMultipliers
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothFine
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineAcyclic

/-!
# Proved fine structure and genuine higher acyclicity of sphere forms

Actual smooth partitions on the original compact sphere act on the
actual derivative-compatible form coefficients.  Their closed supports
give genuine finite fine decompositions.  The proved fine-sheaf Ext
dimension shifting therefore gives vanishing in every positive degree
for this form sheaf, and for the actual smooth-function sheaf as well.
-/

noncomputable section

open Set Function TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms

variable {ι : Type} [Fintype ι]

/-- A genuine smooth sphere partition acts on actual form sections with
its actual closed subordinate supports. -/
def partitionDecomposition {U : ι → Opens RiemannSphere}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) RiemannSphere univ)
    (hρ : ρ.IsSubordinate (fun i => (U i : Set RiemannSphere))) :
    FiniteDecomposition sheaf U where
  operator i := multiplier (SmoothFunctions.complexify 𝓘(ℝ, ℂ) RiemannSphere (ρ i))
  support i := tsupport (ρ i)
  support_closed _ := isClosed_closure
  subordinate := hρ
  zeroOutside i := by
    intro V hV
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply section_ext
    intro b z
    have hzero : ρ i (RiemannSphere.standardCharts.affineMap b z) = 0 :=
      notMem_support.mp (fun hz => hV z.property (subset_tsupport (ρ i) hz))
    change (ρ i (RiemannSphere.standardCharts.affineMap b z) : ℂ) * coefficient s b z = 0
    rw [hzero, Complex.ofReal_zero, zero_mul]
  total := by
    change ∑ i, multiplierRingHom
      (SmoothFunctions.complexify 𝓘(ℝ, ℂ) RiemannSphere (ρ i)) = 1
    rw [← map_sum, SmoothFunctions.complexify_partition_sum, map_one]

/-- The actual smooth `(0,1)`-form sheaf on the constructed sphere is
finite fine; no partition or support data is assumed. -/
theorem finiteFine : FiniteFine sheaf := by
  intro ι _ U hU
  have hcover : (univ : Set RiemannSphere) ⊆ ⋃ i, (U i : Set RiemannSphere) := by
    intro x _
    obtain ⟨i, hi⟩ := hU x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ
    (fun i => (U i : Set RiemannSphere)) (fun i => (U i).isOpen) hcover
  exact ⟨partitionDecomposition ρ hρ⟩

/-- Every positive genuine Ext-defined cohomology group of the actual
sphere form sheaf is zero. -/
theorem higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} sheaf (n + 1)) :=
  finiteFine.higher_subsingleton scalarEnd n

/-- The additive operations remain mathlib's actual Ext group operations. -/
instance cohomologyAddCommGroup (n : ℕ) : AddCommGroup (CategoryTheory.Sheaf.H.{0} sheaf n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Every actual positive-degree cohomology class of this form sheaf is zero. -/
theorem higher_eq_zero (n : ℕ) (a : CategoryTheory.Sheaf.H.{0} sheaf (n + 1)) : a = 0 :=
  (higher_subsingleton n).elim a 0

/-- The genuine smooth-function sheaf on the same real smooth compact
sphere is likewise acyclic in every positive Ext degree. -/
theorem smooth_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (SmoothFunctions.additiveSheaf 𝓘(ℝ, ℂ) RiemannSphere) (n + 1)) :=
  (SmoothFunctions.finiteFine 𝓘(ℝ, ℂ) RiemannSphere).higher_subsingleton
    (SmoothFunctions.scalarEnd 𝓘(ℝ, ℂ) RiemannSphere) n

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms
