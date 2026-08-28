import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureChart

/-!
# Smooth changes between complex-structure Cayley coordinates

Each chart has the anticommuting skew space at its own center as its model.
The actual coordinate changes are smooth on their stated open domains.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.Cayley

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform

variable {n : ℕ}

def inclusion (J : Space n) : AntiSkewSpace J →L[ℝ]
    (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  (antiSkewSubmodule J).subtypeL

def projection (J : Space n) :
    (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →L[ℝ] AntiSkewSpace J :=
  finiteSubmoduleProjection (antiSkewSubmodule J)

theorem projection_coe (J : Space n) (K : AntiSkewSpace J) : projection J K.val = K :=
  finiteSubmoduleProjection_apply (antiSkewSubmodule J) K

theorem contDiff_projection (J : Space n) : ContDiff ℝ ∞ (projection J) :=
  contDiff_finiteSubmoduleProjection (antiSkewSubmodule J)

theorem projection_fraction (J J' : Space n) (h : J' ∈ domain J) :
    projection J (fraction (relative J J').val.val.val) = coordinate J J' h :=
  projection_coe J (coordinate J J' h)

def transitionAmbient (J J' : Space n) (K : AntiSkewSpace J) :
    Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4) :=
  ((toSymplectic J')⁻¹).val.val.val.comp (point J K).val.val

theorem relative_point_operator (J J' : Space n) (K : AntiSkewSpace J) :
    (relative J' (point J K)).val.val.val = transitionAmbient J J' K := rfl

theorem contDiff_transitionAmbient (J J' : Space n) :
    ContDiff ℝ ∞ (transitionAmbient J J') :=
  contDiff_const.clm_comp (contDiff_point_operator J)

theorem transition_mem_domain (J J' : Space n) (K : AntiSkewSpace J)
    (h : K ∈ ((chart J).symm.trans (chart J')).source) : point J K ∈ domain J' := h.2

theorem transition_eq (J J' : Space n) (K : AntiSkewSpace J)
    (h : K ∈ ((chart J).symm.trans (chart J')).source) :
    ((chart J).symm.trans (chart J')) K = projection J' (fraction (transitionAmbient J J' K)) := by
  have hm := transition_mem_domain J J' K h
  change coordinates J' (point J K) = _
  rw [coordinates_of_mem J' _ hm, ← relative_point_operator]
  exact (projection_fraction J' (point J K) hm).symm

theorem contDiffOn_transition (J J' : Space n) :
    ContDiffOn ℝ ∞ ((chart J).symm.trans (chart J'))
      ((chart J).symm.trans (chart J')).source := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun K : AntiSkewSpace J ↦ projection J' (fraction (transitionAmbient J J' K)))
      ((chart J).symm.trans (chart J')).source := by
    intro K hK
    have hden : (1 + transitionAmbient J J' K).IsInvertible := by
      rw [← relative_point_operator]
      exact transition_mem_domain J J' K hK
    have hf : ContDiffAt ℝ ∞ (fun K : AntiSkewSpace J ↦ fraction (transitionAmbient J J' K)) K :=
      ContDiffAt.comp (f := transitionAmbient J J') (g := fraction) K
        (contDiffAt_fraction _ hden) (contDiff_transitionAmbient J J').contDiffAt
    exact ((contDiff_projection J').contDiffAt.comp K hf).contDiffWithinAt
  exact hsmooth.congr (fun K hK ↦ transition_eq J J' K hK)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.Cayley
