import Wikipedia.HopfProblem.DegreeCollapseMiddleHandleCrossing
import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopyExtension

/-!
# Compose and invert native isotopies while retaining their full support

Both constructions retain a uniform support for every real-time slice and
the prescribed fixed locus. They are used to place an attaching disk without
moving the other handles, rather than merely to obtain an unqualified
endpoint isotopy class.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {d e : Diffeomorph J J M M ∞} {K L S T : Set M}

def compose_supported_relative_isotopies (A : SupportedRelativeIsotopy d K S)
    (B : SupportedRelativeIsotopy e L S) : SupportedRelativeIsotopy (d.trans e) (K ∪ L) S where
  family p := B.family (p.1, A.family p)
  smooth := B.smooth.comp (contMDiff_fst.prodMk A.smooth)
  zero x := by rw [A.zero, B.zero]
  one x := by change B.family (1, A.family (1, x)) = e (d x); rw [A.one, B.one]
  slices t := by
    obtain ⟨dₜ, hdₜ⟩ := A.slices t
    obtain ⟨eₜ, heₜ⟩ := B.slices t
    refine ⟨dₜ.trans eₜ, ?_⟩
    intro x
    change eₜ (dₜ x) = B.family (t, A.family (t, x))
    rw [hdₜ, heₜ]
  fixedOutside t x hx := by
    rw [A.fixedOutside t x (fun h => hx (Or.inl h)),
      B.fixedOutside t x (fun h => hx (Or.inr h))]
  fixedOn t x hx := by rw [A.fixedOn t x hx, B.fixedOn t x hx]

def inverse_supported_relative_isotopy (A : SupportedRelativeIsotopy d K S) :
    SupportedRelativeIsotopy d.symm K S where
  family p := d.symm (A.family (1 - p.1, p.2))
  smooth := by
    have hrev : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 - t) :=
      (contDiff_const.sub contDiff_id).contMDiff
    exact d.symm.contMDiff.comp
      (A.smooth.comp ((hrev.comp contMDiff_fst).prodMk contMDiff_snd))
  zero x := by rw [sub_zero, A.one, d.symm_apply_apply]
  one x := by rw [sub_self, A.zero]
  slices t := by
    obtain ⟨dₜ, hdₜ⟩ := A.slices (1 - t)
    refine ⟨dₜ.trans d.symm, ?_⟩
    intro x
    exact congrArg d.symm (hdₜ x)
  fixedOutside t x hx := by
    rw [A.fixedOutside (1 - t) x hx]
    exact (congrArg d.symm (A.endpoint_fixed_outside x hx)).symm.trans (d.symm_apply_apply x)
  fixedOn t x hx := by
    rw [A.fixedOn (1 - t) x hx]
    exact (congrArg d.symm (A.endpoint_fixed_on x hx)).symm.trans (d.symm_apply_apply x)

def weaken_supported_relative_isotopy (A : SupportedRelativeIsotopy d K S)
    (hKL : K ⊆ L) (hTS : T ⊆ S) : SupportedRelativeIsotopy d L T where
  family := A.family
  smooth := A.smooth
  zero := A.zero
  one := A.one
  slices := A.slices
  fixedOutside t x hx := A.fixedOutside t x (fun h => hx (hKL h))
  fixedOn t x hx := A.fixedOn t x (hTS hx)

theorem supported_isotopy_endpoint_mapsTo (A : SupportedRelativeIsotopy d K S)
    {U : Set M} (hKU : K ⊆ U) : MapsTo d U U := by
  intro x hx
  have hh := A.mapsTo_superset hKU 1 hx
  change A.family (1, x) ∈ U at hh
  rwa [A.one] at hh

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
