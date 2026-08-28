import Wikipedia.NoExoticSixSphere.RelativeSimplexHomotopyHomology
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic

/-!
# Actual relative cycles carried by simplices with subspace boundary

An original singular simplex whose entire boundary is in the subspace
defines a cycle in the genuine relative complex. No quotient of homotopy
classes is substituted for relative homology.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeSimplexCycles

open RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

abbrev RelativeSimplex (n : ℕ) :=
  {smp : C(Simplex n, X) // ∀ s ∈ simplexBoundary n, smp s ∈ U}

theorem boundary_mem (n : ℕ) (smp : RelativeSimplex U (n + 1)) :
    ((singularComplex X).d (n + 1) n).hom (simplexChain X (n + 1) smp.val) ∈
      supportedChainSubmodule U n := by
  rw [boundary_simplex]
  apply Submodule.sum_mem
  intro i _
  apply (supportedChainSubmodule U n).toAddSubgroup.zsmul_mem
  apply simplexChain_mem_supported
  rintro _ ⟨s, rfl⟩
  exact smp.property (simplexFace n i s) (simplexFace_mem_boundary n i s)

def cycle (n : ℕ) (smp : RelativeSimplex U (n + 1)) :
    ModuleHomology.Cycle (complex U) (n + 1) :=
  ModuleHomology.mkCycle (complex U) (n + 1)
    (quotientMap U (n + 1) (simplexChain X (n + 1) smp.val)) (by
      exact (relativeCycle_iff U (n + 1) n _).mpr (boundary_mem U n smp))

def homologyClass (n : ℕ) (smp : RelativeSimplex U (n + 1)) : Homology U (n + 1) :=
  ModuleHomology.cycleClass (complex U) (n + 1) (cycle U n smp)

end NoExoticSixSphere.RelativeSimplexCycles
