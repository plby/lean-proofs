import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesTori
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyIntervals
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint

/-!
# Actual homology of the two radial phase slices

The literal product of the compact fibre torus, two discrete directions,
and a nonempty open radial interval is homotopy equivalent to two disjoint
copies of the compact fibre torus.  The actual singular-chain splitting
of a disjoint union therefore proves its integral homology vanishes in
every degree greater than two.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open Set ContinuousMap ToricSpace SingularMayerVietoris
open CuspCentralHomology PeriodTorusHigherHomology

/-- Contract only the actual interval factor, leaving the compact phase
and the discrete direction unchanged. -/
def phaseSlicesHomotopyEquiv (a : ℝ) (ha : a < 1) :
    (CompactFibreTorus × (Fin 2 × Ioo a (1 : ℝ))) ≃ₕ (CompactFibreTorus × Fin 2) := by
  letI : ContractibleSpace (Ioo a (1 : ℝ)) := CircleTopology.intervalContractible a 1 ha
  exact (Homeomorph.prodAssoc CompactFibreTorus (Fin 2) (Ioo a (1 : ℝ))).symm.toHomotopyEquiv.trans
    ((Homeomorph.prodComm (CompactFibreTorus × Fin 2) (Ioo a (1 : ℝ))).toHomotopyEquiv.trans
      (CircleTopology.contractibleProdHomotopyEquiv (Ioo a (1 : ℝ))
        (CompactFibreTorus × Fin 2)))

@[simp] theorem phaseSlicesHomotopyEquiv_apply (a : ℝ) (ha : a < 1)
    (p : CompactFibreTorus × (Fin 2 × Ioo a (1 : ℝ))) :
    phaseSlicesHomotopyEquiv a ha p = (p.1, p.2.1) := rfl

/-- The two actual discrete directions select the two topological summands. -/
def phaseDirectionsHomeomorph :
    (CompactFibreTorus × Fin 2) ≃ₜ (CompactFibreTorus ⊕ CompactFibreTorus) :=
  ((Homeomorph.refl CompactFibreTorus).prodCongr
      (Equiv.toHomeomorphOfDiscrete
        (finTwoEquiv.trans
          (Equiv.boolEquivPUnitSumPUnit : Bool ≃ PUnit.{1} ⊕ PUnit.{1})))).trans
    (Homeomorph.prodSumDistrib.trans
      ((Homeomorph.prodUnique CompactFibreTorus PUnit.{1}).sumCongr
        (Homeomorph.prodUnique CompactFibreTorus PUnit.{1})))

@[simp] theorem phaseDirectionsHomeomorph_zero (φ : CompactFibreTorus) :
    phaseDirectionsHomeomorph (φ, 0) = Sum.inl φ := rfl

@[simp] theorem phaseDirectionsHomeomorph_one (φ : CompactFibreTorus) :
    phaseDirectionsHomeomorph (φ, 1) = Sum.inr φ := rfl

/-- The all-degree splitting comes from the actual interval contraction
and the actual singular-chain splitting of the two disjoint copies. -/
def phaseSlicesHomologyEquiv (a : ℝ) (ha : a < 1) (n : ℕ) :
    SingularHomology (CompactFibreTorus × (Fin 2 × Ioo a (1 : ℝ))) n ≃ₗ[ℤ]
      (SingularHomology CompactFibreTorus n × SingularHomology CompactFibreTorus n) :=
  ((homotopyEquivHomologyEquiv (phaseSlicesHomotopyEquiv a ha) n).trans
    (homeomorphHomologyEquiv phaseDirectionsHomeomorph n)).trans
      (sumHomologyEquiv CompactFibreTorus CompactFibreTorus n)

theorem phaseSlices_homology_subsingleton_of_lt (a : ℝ) (ha : a < 1)
    {n : ℕ} (hn : 2 < n) :
    Subsingleton (SingularHomology (CompactFibreTorus × (Fin 2 × Ioo a (1 : ℝ))) n) := by
  let := compactFibreTorus_homology_subsingleton_of_lt hn
  exact (phaseSlicesHomologyEquiv a ha n).injective.subsingleton

theorem phaseSlices_homology_subsingleton (a : ℝ) (ha : a < 1) (n : ℕ) :
    Subsingleton
      (SingularHomology (CompactFibreTorus × (Fin 2 × Ioo a (1 : ℝ))) (n + 3)) :=
  phaseSlices_homology_subsingleton_of_lt a ha (by omega)

/-- In particular the literal two radial phase slices have zero third homology. -/
theorem phaseSlices_homologyThree_subsingleton (a : ℝ) (ha : a < 1) :
    Subsingleton
      (SingularHomology (CompactFibreTorus × (Fin 2 × Ioo a (1 : ℝ))) 3) :=
  phaseSlices_homology_subsingleton a ha 0

/-- Reassociating the literal product does not change the vanishing statement. -/
theorem phaseSlices_assoc_homology_subsingleton (a : ℝ) (ha : a < 1) (n : ℕ) :
    Subsingleton
      (SingularHomology ((CompactFibreTorus × Fin 2) × Ioo a (1 : ℝ)) (n + 3)) := by
  let := phaseSlices_homology_subsingleton a ha n
  exact (homeomorphHomologyEquiv
    (Homeomorph.prodAssoc CompactFibreTorus (Fin 2) (Ioo a (1 : ℝ)))
      (n + 3)).injective.subsingleton

theorem phaseSlices_assoc_homologyThree_subsingleton (a : ℝ) (ha : a < 1) :
    Subsingleton
      (SingularHomology ((CompactFibreTorus × Fin 2) × Ioo a (1 : ℝ)) 3) :=
  phaseSlices_assoc_homology_subsingleton a ha 0

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
