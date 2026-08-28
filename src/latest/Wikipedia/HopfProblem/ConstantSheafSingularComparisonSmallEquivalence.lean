import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallBasis
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSubdivisionSupport
import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# The original small-chain inclusion is a homotopy equivalence

The comparison is proved for arbitrary open covers. Subdivision supplies
small representatives of actual cycles, and its carrier-preserving
homotopy supplies small lifts of actual boundaries. This proves the
literal inclusion is a quasi-isomorphism. The genuine simplex bases make
both complexes degreewise projective, so Mathlib's nonnegative-projective
complex theorem upgrades that same map to a chain-homotopy equivalence.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {ι : Type*}

/-- The actual inclusion of cover-small chains is a quasi-isomorphism
for every open cover, including in degree zero. -/
theorem smallInclusion_quasiIso (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) :
    QuasiIso (smallInclusion U) := by
  apply ModuleHomology.quasiIso_of_injective_chain_conditions (smallInclusion U)
  · intro n
    exact smallInclusion_f_injective U n
  · intro n c hc
    obtain ⟨k, hk⟩ := eventually_subdivision_mem_small U hU hcover n c
    exact ⟨⟨subdivision X k n c, hk k le_rfl⟩,
      subdivisionHomotopy X k n c, subdivisionHomotopy_boundary_of_cycle k n c hc⟩
  · intro n c hc b hb
    have hc' : ((singularComplex X).d n (n - 1)).hom c.1 = 0 :=
      congrArg (fun z : (smallComplex U).X (n - 1) => z.1) hc
    change ((singularComplex X).d (n + 1) n).hom b = c.1 at hb
    obtain ⟨k, hk⟩ := eventually_subdivision_mem_small U hU hcover (n + 1) b
    refine ⟨⟨subdivision X k (n + 1) b + subdivisionHomotopy X k n c.1,
      (smallChainSubmodule U (n + 1)).add_mem (hk k le_rfl)
        (subdivisionHomotopy_mem_small U k n c.1 c.2)⟩, ?_⟩
    apply Subtype.ext
    change ((singularComplex X).d (n + 1) n).hom
      (subdivision X k (n + 1) b + subdivisionHomotopy X k n c.1) = c.1
    rw [map_add, subdivision_boundary, hb, subdivisionHomotopy_boundary_of_cycle k n c.1 hc']
    rw [← add_sub_assoc, add_comm, add_sub_cancel_right]

/-- Both original complexes have genuine simplex bases, so the proved
quasi-isomorphism is a chain-homotopy equivalence of the same map. -/
theorem smallInclusion_isHomotopyEquivalence (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{0} ℤ) (ComplexShape.down ℕ)
      (smallInclusion U) := by
  let (n : ℕ) : CategoryTheory.Projective ((smallComplex U).X n) :=
    smallChain_projective U n
  let (n : ℕ) : CategoryTheory.Projective ((singularComplex X).X n) :=
    ModuleCat.projective_of_free (chainBasis X n)
  exact (ChainComplex.quasiIso_iff_of_projective (smallInclusion U)).mp
    (smallInclusion_quasiIso U hU hcover)

/-- An actual chain-homotopy equivalence whose forward map is, by
definition, the original small-chain inclusion. -/
def smallChainHomotopyEquiv (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) :
    HomotopyEquiv (smallComplex U) (singularComplex X) := by
  let e := (smallInclusion_isHomotopyEquivalence U hU hcover).choose
  have he : e.hom = smallInclusion U :=
    (smallInclusion_isHomotopyEquivalence U hU hcover).choose_spec
  exact
    { hom := smallInclusion U
      inv := e.inv
      homotopyHomInvId := he ▸ e.homotopyHomInvId
      homotopyInvHomId := he ▸ e.homotopyInvHomId }

@[simp] theorem smallChainHomotopyEquiv_hom (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) :
    (smallChainHomotopyEquiv U hU hcover).hom = smallInclusion U := rfl

/-- The inverse is an actual chain map into the small-chain subcomplex. -/
def smallChainRetraction (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) :
    singularComplex X ⟶ smallComplex U :=
  (smallChainHomotopyEquiv U hU hcover).inv

/-- Retraction followed by the actual inclusion is chain-homotopic to
the original identity map. -/
def smallChainRetraction_inclusion_homotopy (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) :
    Homotopy (smallChainRetraction U hU hcover ≫ smallInclusion U)
      (𝟙 (singularComplex X)) :=
  (smallChainHomotopyEquiv U hU hcover).homotopyInvHomId

/-- The reverse composition is also chain-homotopic to its actual
identity, inside the original small-chain subcomplex. -/
def smallInclusion_retraction_homotopy (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) :
    Homotopy (smallInclusion U ≫ smallChainRetraction U hU hcover)
      (𝟙 (smallComplex U)) :=
  (smallChainHomotopyEquiv U hU hcover).homotopyHomInvId

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
