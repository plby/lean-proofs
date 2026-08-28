import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationNative

/-!
# The precise remaining native second-homology attachment problem

Second homology is the actual regular-family homology modulo the sum of
the actual regular images of native cap kernels.  This file records the
exact relation criterion and the equivalence between vanishing and the
remaining genuine image calculation.  It does not assume that image is
the whole regular group.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination

open SingularMayerVietoris

/-- A regular class dies globally exactly when it is the sum of genuine native cap-kernel images. -/
theorem regularInclusion_eq_zero_iff_native (n : ℕ)
    (a : SingularHomology SpecialRegularFamily n) :
    singularHomologyMap originalRegularInclusion n a = 0 ↔
      ∃ b : ∀ i : Puncture, NativeCapKernel i n, nativeCapKernelRegularMap n b = a := by
  change a ∈ LinearMap.ker (singularHomologyMap originalRegularInclusion n) ↔ _
  rw [regularInclusion_native_kernel]
  rfl

/-- The remaining native image calculation is exactly what is required for second-homology
vanishing; neither direction substitutes an assumed matrix for the genuine maps. -/
theorem homologyTwo_subsingleton_iff_nativeCapKernel_surjective :
    Subsingleton (SingularHomology Space 2) ↔
      Function.Surjective (nativeCapKernelRegularMap 2) := by
  constructor
  · intro h a
    exact (regularInclusion_eq_zero_iff_native 2 a).mp (h.elim _ _)
  · intro h
    have hz (a : SingularHomology Space 2) : a = 0 := by
      obtain ⟨b, rfl⟩ := regularInclusion_two_surjective a
      exact (regularInclusion_eq_zero_iff_native 2 b).mpr (h b)
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination
