import Wikipedia.HopfProblem.ConstantSheafSingularComparisonFineCochainsRaw
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonFineCochainsSheafification
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonFineAcyclic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonClosedRefinement

/-!
# The actual sheafified singular cochain terms are finite-fine

For a closed refinement of a finite open cover, select an index at each
point whose closed member contains it. The original cochain endomorphism
retains a simplex precisely when its first vertex has that index. This
construction uses only zero and identity on the arbitrary coefficient
group. Its actual sheafification has the prescribed closed support, and
the finite sum is the identity on the original cochain sheaf.

The resulting genuine finite-fine decomposition gives positive-degree
sheaf cohomology vanishing on compact Hausdorff spaces for every abelian
coefficient group and every original singular cochain degree.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.FineCochains

open HolomorphicSheafCohomology

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)
variable {ι : Type}

/-- The genuine sheafification of the original selector endomorphism. -/
def selectorSheafEnd (sel : X → ι) (i : ι) :
    cochainSheaf X A n ⟶ cochainSheaf X A n :=
  (cochainSheafification X).map (selectorPresheafEnd X A n sel i)

/-- The original unit intertwines the actual raw and sheafified selectors. -/
@[reassoc]
theorem cochainSheafUnit_selector (sel : X → ι) (i : ι) :
    cochainSheafUnit X A n ≫ (selectorSheafEnd X A n sel i).hom =
      selectorPresheafEnd X A n sel i ≫ cochainSheafUnit X A n :=
  (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
    (selectorPresheafEnd X A n sel i)).symm

/-- The finite sum of the original sheafified selectors is the identity. -/
theorem selectorSheafEnd_sum [Fintype ι] (sel : X → ι) :
    ∑ i, selectorSheafEnd X A n sel i = 𝟙 (cochainSheaf X A n) := by
  change (∑ i, (cochainSheafification X).map (selectorPresheafEnd X A n sel i)) = _
  rw [← Functor.map_sum, selectorPresheafEnd_sum]
  exact (cochainSheafification X).map_id _

variable {X}

/-- A selected member contains every first vertex on which its original
endomorphism is nonzero, so the sheafified map vanishes off that closed set. -/
theorem selectorSheafEnd_zeroOutside {U : ι → Opens X} (R : ClosedRefinement U) (i : ι) :
    IsZeroOn (selectorSheafEnd X A n R.index i)
      ⟨(R.support i)ᶜ, (R.isClosed i).isOpen_compl⟩ := by
  apply Sheafification.map_isZeroOn_of_app_eq_zero
  intro V hV
  apply selectorPresheafEnd_app_eq_zero X A n R.index i V
  intro x hxV hsel
  exact (hV hxV) (hsel ▸ R.mem_support_index x)

/-- The original sheafified cochains carry an actual finite decomposition
with the closed supports of the given refinement. -/
def finiteDecomposition [Fintype ι] {U : ι → Opens X} (R : ClosedRefinement U) :
    FiniteDecomposition (cochainSheaf X A n) U where
  operator i := selectorSheafEnd X A n R.index i
  support := R.support
  support_closed := R.isClosed
  subordinate := R.subordinate
  zeroOutside i := selectorSheafEnd_zeroOutside A n R i
  total := selectorSheafEnd_sum X A n R.index

variable (X)

/-- On a normal paracompact space the actual sheafified cochain term is
finite-fine for arbitrary abelian coefficients. -/
theorem cochainSheaf_finiteFine_of_normal [NormalSpace X] [ParacompactSpace X] :
    FiniteFine (cochainSheaf X A n) := by
  intro ι _ U hU
  obtain ⟨R⟩ := exists_closedRefinement U hU
  exact ⟨finiteDecomposition A n R⟩

/-- In particular, every original cochain sheaf on a compact Hausdorff
space is finite-fine, without a scalar-action hypothesis. -/
theorem cochainSheaf_finiteFine [CompactSpace X] [T2Space X] :
    FiniteFine (cochainSheaf X A n) :=
  cochainSheaf_finiteFine_of_normal X A n

/-- All genuine positive sheaf cohomology groups of the actual cochain
terms vanish on a compact Hausdorff base. -/
theorem cochainSheaf_higher_subsingleton [CompactSpace X] [T2Space X] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (cochainSheaf X A n) (q + 1)) :=
  (cochainSheaf_finiteFine X A n).higher_subsingleton_abelian q

/-- Every original positive sheaf cohomology class of a cochain term is zero. -/
theorem cochainSheaf_higher_eq_zero [CompactSpace X] [T2Space X] (q : ℕ)
    (ξ : CategoryTheory.Sheaf.H.{0} (cochainSheaf X A n) (q + 1)) : ξ = 0 :=
  (cochainSheaf_higher_subsingleton X A n q).elim ξ 0

/-- The original positive sheaf cohomology object of each actual cochain
term is zero on every compact Hausdorff base. -/
theorem cochainSheaf_higher_isZero [CompactSpace X] [T2Space X] (q : ℕ) :
    IsZero ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X)
      (q + 1)).obj (cochainSheaf X A n)) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr (cochainSheaf_higher_subsingleton X A n q)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.FineCochains
