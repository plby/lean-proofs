import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingNative
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1LiftingLocal

/-!
# Actual global kernel sections from closed native coefficient pairs

Left exactness of sections for the original second Dolbeault short exact
sequence lifts each actual closed pair into its actual kernel sheaf on
the same open. The original kernel inclusion retains the literal pair,
and its injectivity makes this section unique.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicFunctionSheaf.SphereH1 PeriodTorusHolomorphicCohomology

variable (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤)
  (hs : Dolbeault.topSection p ⊤ s = 0)

include hs in
/-- The genuine section-exactness theorem supplies a lift into the
original native kernel sheaf, with no global primitive assumption. -/
theorem exists_nativeKernelLift :
    ∃ k : GlobalKernelSections p, nativeKernelSection p k = s :=
  section_kernel_lift (Dolbeault.resolution p).second_shortExact s hs

/-- The actual native kernel section of a given closed coefficient pair. -/
def nativeKernelLift : GlobalKernelSections p :=
  Classical.choose (exists_nativeKernelLift p s hs)

/-- Its image is exactly the original native pair of smooth functions. -/
@[simp] theorem nativeKernelSection_nativeKernelLift :
    nativeKernelSection p (nativeKernelLift p s hs) = s :=
  Classical.choose_spec (exists_nativeKernelLift p s hs)

/-- Injectivity of the original kernel inclusion makes the lift unique. -/
theorem nativeKernelLift_unique (k : GlobalKernelSections p)
    (hk : nativeKernelSection p k = s) : k = nativeKernelLift p s hs :=
  section_f_injective (Dolbeault.resolution p).second_shortExact ⊤
    (hk.trans (nativeKernelSection_nativeKernelLift p s hs).symm)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting
