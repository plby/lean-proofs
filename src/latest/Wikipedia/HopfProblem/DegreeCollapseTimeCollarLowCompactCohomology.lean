import Wikipedia.HopfProblem.DegreeCollapseTimeCollarCoreComplement
import Wikipedia.HopfProblem.DegreeCollapseIntegralConnectedLowCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralTopClassLift

/-!
# The interior's compactly supported H0 and H1 vanish

Each sufficiently small positive core has a path-connected collar-strip
complement. The actual interior is homotopy equivalent to the simply
connected half. The original relative groups vanish in degrees zero and
one, and every compact support extends into such a core. Passing to the
actual support direct limit proves the two compact-support vanishings.
-/

noncomputable section

open Set TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open SingularMayerVietoris IntegralCompactSupportCohomology

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)
  [PathConnectedSpace B] [SimplyConnectedSpace (NonnegativeHalf t)]

theorem interiorCore_low_cohomology (c : ℝ) (hc0 : 0 < c) (hc : c < C.width)
    (p : ℕ) (hp : p ≤ 1) :
    Subsingleton (IntegralSupportedCohomology.Cohomology (C.interiorCore c) p) := by
  let : SimplyConnectedSpace C.positiveInterior := C.interiorHalfHomotopyEquiv.simplyConnectedSpace
  let : PathConnectedSpace ↥((C.interiorCore c)ᶜ) :=
    C.pathConnectedSpace_coreComplement c hc hc0
  cases p with
  | zero =>
    exact RelativeIntegralCohomology.connected_zero_cohomology_subsingleton (C.interiorCore c)ᶜ
  | succ p =>
    have h : p = 0 := by omega
    subst p
    let : Subsingleton (SingularHomology C.positiveInterior 1) :=
      IntegralTopClassLift.first_homology_subsingleton C.positiveInterior
    exact RelativeIntegralCohomology.connected_first_cohomology_subsingleton (C.interiorCore c)ᶜ

theorem interior_compactSupport_low_cohomology [CompactSpace M] (p : ℕ) (hp : p ≤ 1) :
    Subsingleton (Cohomology C.positiveInterior p) := by
  have hz (a : Cohomology C.positiveInterior p) : a = 0 := by
    obtain ⟨K, b, rfl⟩ := exists_representative C.positiveInterior p a
    obtain ⟨c, hc0, hc, hK⟩ := C.exists_interiorCore_containing K
    let N := C.interiorCoreCompact c hc0
    have hKN : K ≤ N := hK
    let : Subsingleton (Component C.positiveInterior p N) :=
      C.interiorCore_low_cohomology c hc0 hc p hp
    rw [← of_transition C.positiveInterior p hKN b]
    exact (congrArg (of C.positiveInterior p N)
      (Subsingleton.elim (transition C.positiveInterior p K N hKN b) 0)).trans (map_zero _)
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
