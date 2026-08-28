import Wikipedia.NoExoticSixSphere.OpenSupportCohomology
import Wikipedia.NoExoticSixSphere.CompactSupportCohomology

/-!
# Actual compact-support cohomology maps for open inclusions

Each original compact support in the open subspace is sent to its actual
ambient image. The inverse excision maps commute with the proved support
transition maps, so they descend to the genuine compact-support direct
limit. The resulting map retains the formula on every representative.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.CompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] (U : Set X) (hU : IsOpen U) (p : ℕ)

/-- The same compact subset, viewed in the original ambient space by inclusion. -/
def imageCompact (K : Compacts U) : Compacts X :=
  ⟨OpenSupportCohomology.imageSupport U (K : Set U), K.isCompact.image continuous_subtype_val⟩

/-- Extend an actual compact-support representative and insert its original image support. -/
def inclusionComponent (K : Compacts U) : Component U p K →ₗ[ℤ] Cohomology X p :=
  (of X p (imageCompact U K)).comp
    (OpenSupportCohomology.extension U hU (K : Set U) K.isCompact p)

/-- The original support transitions give a compatible family of actual component maps. -/
theorem inclusionComponent_transition (K L : Compacts U) (h : K ≤ L) (a : Component U p K) :
    inclusionComponent U hU p L (transition U p K L h a) = inclusionComponent U hU p K a := by
  change of X p (imageCompact U L)
      (OpenSupportCohomology.extension U hU (L : Set U) L.isCompact p
        (SupportedModTwoCohomology.extend h p a)) = _
  rw [← OpenSupportCohomology.extension_extend U hU h K.isCompact L.isCompact p a]
  exact of_transition X p (K := imageCompact U K) (L := imageCompact U L)
    (show imageCompact U K ≤ imageCompact U L from Set.image_mono h)
    (OpenSupportCohomology.extension U hU (K : Set U) K.isCompact p a)

/-- Extension along an open inclusion on the actual compact-support direct limits. -/
def inclusion : Cohomology U p →ₗ[ℤ] Cohomology X p :=
  lift U p (inclusionComponent U hU p) (inclusionComponent_transition U hU p)

/-- Every genuine representative retains its inverse-excision extension formula. -/
theorem inclusion_of (K : Compacts U) (a : Component U p K) :
    inclusion U hU p (of U p K a) =
      of X p (imageCompact U K)
        (OpenSupportCohomology.extension U hU (K : Set U) K.isCompact p a) := rfl

end NoExoticSixSphere.CompactSupportCohomology
