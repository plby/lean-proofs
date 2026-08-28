import Wikipedia.NoExoticSixSphere.JamesSphereHomologyComparisonSquare
import Wikipedia.NoExoticSixSphere.SphereProjectionKernel
import Wikipedia.NoExoticSixSphere.JamesPathConnected
import Wikipedia.NoExoticSixSphere.PathSpaceConnected
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedTopology

/-!
# The actual James comparison induces integral homology isomorphisms

For a positive-dimensional sphere, restrict the checked word and loop
splittings to kernels of second projection. Their second coordinates
identify these kernels with word and loop homology in the same degree.
The comparison commutes with these identifications. The natural sphere
kernel calculation reduces bijectivity to lower homology degrees, and
path connectedness supplies degree zero. Strong induction proves the
claim for the actual comparison map in every degree.

This proves homology isomorphisms, not yet a homotopy equivalence or EHP.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.HomologyComparison

def wordKernelEquiv (n d : ℕ) (hd : d ≠ 0) :
    ProductProjectionHomology.Kernel (Sphere n) (WordHomology.Words n) d ≃ₗ[ℤ]
      SingularHomology (WordHomology.Words n) d :=
  SplitProjectionKernel.equiv (WordHomology.projectionActionEquiv n d hd).toAddEquiv
    (ProductProjectionHomology.projection (Sphere n) (WordHomology.Words n) d)
    (fun a ↦ congrArg Prod.fst (WordHomology.projectionActionEquiv_apply n d hd a))

def loopKernelEquiv (n d : ℕ) (hd : d ≠ 0) :
    ProductProjectionHomology.Kernel (Sphere n) (CoverMaps.Loops n) d ≃ₗ[ℤ]
      SingularHomology (CoverMaps.Loops n) d :=
  SplitProjectionKernel.equiv (LoopHomology.projectionActionEquiv n d hd).toAddEquiv
    (ProductProjectionHomology.projection (Sphere n) (CoverMaps.Loops n) d)
    (fun a ↦ congrArg Prod.fst (LoopHomology.projectionActionEquiv_apply n d hd a))

theorem kernel_square (n d : ℕ) (hd : d ≠ 0)
    (a : ProductProjectionHomology.Kernel (Sphere n) (WordHomology.Words n) d) :
    loopKernelEquiv n d hd (ProductProjectionHomology.map (Sphere n) (loopComparison n) d a) =
      singularHomologyMap (loopComparison n) d (wordKernelEquiv n d hd a) :=
  congrArg Prod.snd (splitting_square n d hd a.val)

theorem kernel_bijective_iff (n d : ℕ) (hd : d ≠ 0) :
    Function.Bijective (ProductProjectionHomology.map (Sphere n) (loopComparison n) d) ↔
      Function.Bijective (singularHomologyMap (loopComparison n) d) := by
  have h : loopKernelEquiv n d hd ∘ ProductProjectionHomology.map (Sphere n) (loopComparison n) d =
      singularHomologyMap (loopComparison n) d ∘ wordKernelEquiv n d hd :=
    funext (kernel_square n d hd)
  have h₁ := Function.Bijective.of_comp_iff' (loopKernelEquiv n d hd).bijective
    (ProductProjectionHomology.map (Sphere n) (loopComparison n) d)
  have h₂ := Function.Bijective.of_comp_iff (singularHomologyMap (loopComparison n) d)
    (wordKernelEquiv n d hd).bijective
  rw [← h₁, h, h₂]

theorem loops_pathConnected (n : ℕ) : PathConnectedSpace (CoverMaps.Loops (n + 1)) :=
  PathSpaceConnected.loop_space (spherePole (n + 2))

theorem comparison_homology_bijective (n d : ℕ) :
    Function.Bijective (singularHomologyMap (loopComparison (n + 1)) d) := by
  let : PathConnectedSpace (CoverMaps.Loops (n + 1)) := loops_pathConnected n
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hd : d = 0
      · subst d
        exact SphereHomology.singularHomologyMap_zero_bijective (loopComparison (n + 1))
      · apply (kernel_bijective_iff (n + 1) d hd).mp
        exact SphereProjectionKernel.map_bijective_of_lower (loopComparison (n + 1)) n d ih

theorem comparison_homology_bijective_of_pos (n d : ℕ) (hn : 0 < n) :
    Function.Bijective (singularHomologyMap (loopComparison n) d) := by
  cases n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n => exact comparison_homology_bijective n d

def comparisonHomologyEquiv (n d : ℕ) (hn : 0 < n) :
    SingularHomology (WordHomology.Words n) d ≃ₗ[ℤ] SingularHomology (CoverMaps.Loops n) d :=
  LinearEquiv.ofBijective (singularHomologyMap (loopComparison n) d)
    (comparison_homology_bijective_of_pos n d hn)

theorem comparisonHomologyEquiv_apply (n d : ℕ) (hn : 0 < n)
    (a : SingularHomology (WordHomology.Words n) d) :
    comparisonHomologyEquiv n d hn a = singularHomologyMap (loopComparison n) d a := rfl

end NoExoticSixSphere.JamesSphere.HomologyComparison
