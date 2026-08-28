import Wikipedia.NoExoticSixSphere.RelativeChainNeighborhood

/-!
# Lifting an actual supported homology class to a neighborhood

Choose an ambient representative. Its boundary vanishes relative to the
support complement, and the compact-carrier argument preserves that
vanishing on a neighborhood. The same original ambient chain therefore
represents a lift on every intermediate support in that neighborhood.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.SupportedRelativeHomology

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X] [T2Space X]

/-- Every actual supported class lifts to each sufficiently small larger support. -/
theorem exists_lift_neighborhood (K : Set X) (n : ℕ) (a : Homology A K n) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      ∀ (L : Set X) (_hL : L ⊆ U) (hKL : K ⊆ L),
        ∃ b : Homology A L n, restrict A hKL n b = a := by
  obtain ⟨c, hc, hca⟩ := RelativeCoefficients.exists_cycle_representative A Kᶜ n a
  have hboundary : RelativeCoefficients.quotientMap A Kᶜ (n - 1)
      (((coefficientComplex A X).d n (n - 1)).hom c) = 0 :=
    (RelativeCoefficients.boundary_quotientMap A Kᶜ n (n - 1) c).symm.trans hc
  obtain ⟨U, hU, hKU, hzero⟩ := RelativeCoefficients.quotientMap_zero_neighborhood
    A K (n - 1) (((coefficientComplex A X).d n (n - 1)).hom c) hboundary
  refine ⟨U, hU, hKU, ?_⟩
  intro L hL hKL
  have hcL : ((Complex A L).d n (n - 1)).hom
      (RelativeCoefficients.quotientMap A Lᶜ n c) = 0 :=
    (RelativeCoefficients.boundary_quotientMap A Lᶜ n (n - 1) c).trans (hzero L hL)
  let z := ModuleHomology.mkCycle (Complex A L) n
    (RelativeCoefficients.quotientMap A Lᶜ n c) hcL
  refine ⟨ModuleHomology.cycleClass (Complex A L) n z, ?_⟩
  change (HomologicalComplex.homologyMap (restrictChain A hKL) n).hom
    (ModuleHomology.cycleClass (Complex A L) n z) = a
  rw [ModuleHomology.homologyMap_cycleClass]
  apply Eq.trans _ hca
  apply congrArg (ModuleHomology.cycleClass (Complex A K) n)
  apply Subtype.ext
  exact (ModuleHomology.mapCycles_val (restrictChain A hKL) n z).trans
    (restrictChain_quotientMap A hKL n c)

end NoExoticSixSphere.SupportedRelativeHomology
