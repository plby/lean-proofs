import Wikipedia.HopfProblem.HolomorphicCousinSmoothCocycleNormalized
import Wikipedia.HopfProblem.HolomorphicCousinLocalForcing

/-!
# Compactly supported forcing constructed from an actual local cocycle

Given an open cover of the complex plane and a holomorphic additive cocycle,
the relative partition-of-unity construction gives actual smooth local
potentials.  If a distinguished cover member contains the complement of a
disc, its potential can be made zero on a neighborhood of that complement.
The resulting global antiholomorphic forcing has topological support inside
the disc and is therefore compactly supported.

No local holomorphic sections on an entire affine patch, global solution of a
`∂̄` equation, or cohomology-vanishing statement is assumed here.
-/

noncomputable section

open Complex Filter Function Metric Set
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCousin

variable {ι : Type*}

namespace LocalPotential

/-- A zero local representative on an open set makes the actual global
forcing vanish on that set. -/
theorem forcing_eq_zero_on_normalization (P : LocalPotential ι)
    {i : ι} {V : Set ℂ} (hV : IsOpen V) (hVi : V ⊆ P.domain i)
    (hzero : EqOn (P.potential i) (fun _ => 0) V) :
    EqOn P.forcing (fun _ => 0) V := by
  intro z hz
  apply P.forcing_eq_zero (hVi hz)
  apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hz] with w hw
  exact hzero hw

/-- The topological support, not merely the pointwise support, misses an
open region on which a local representative has been normalized to zero. -/
theorem forcing_tsupport_subset_of_normalization (P : LocalPotential ι)
    {i : ι} {V : Set ℂ} (hV : IsOpen V) (hVi : V ⊆ P.domain i)
    (hzero : EqOn (P.potential i) (fun _ => 0) V) :
    tsupport P.forcing ⊆ Vᶜ := by
  apply closure_minimal ?_ hV.isClosed_compl
  intro z hz hzV
  exact hz (P.forcing_eq_zero_on_normalization hV hVi hzero hzV)

end LocalPotential

/-- Construct a normalized local potential directly from a holomorphic
additive cocycle.  Its exact transition functions are preserved and its actual
forcing has compact topological support inside the prescribed disc. -/
theorem exists_normalized_cocycle_localPotential {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i)
    {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k →
      h i j z + h j k z = h i k z)
    (i₀ : ι) (R : ℝ) (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ P : LocalPotential ι,
      P.domain = U ∧
      (∀ i j z, z ∈ U i → z ∈ U j →
        P.potential i z - P.potential j z = h i j z) ∧
      (∃ V : Set ℂ, IsOpen V ∧ (ball (0 : ℂ) R)ᶜ ⊆ V ∧ V ⊆ U i₀ ∧
        EqOn (P.potential i₀) (fun _ => 0) V ∧
        ∀ i, EqOn (P.potential i) (h i i₀) (U i ∩ V)) ∧
      tsupport P.forcing ⊆ ball (0 : ℂ) R ∧ HasCompactSupport P.forcing := by
  have hsmooth i j : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (h i j) (U i ∩ U j) :=
    ((hh i j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ |>.contMDiffOn
  obtain ⟨V, s, hVo, hRV, hVU, hs, htrans, hs0, hsOverlap⟩ :=
    exists_normalized_smooth_cocycle_cochain hU hcover hsmooth hc i₀
      isOpen_ball.isClosed_compl hRU
  let P : LocalPotential ι := {
    domain := U
    isOpen_domain := hU
    cover := hcover
    potential := s
    smooth := fun i => (hs i).contDiffOn
    analytic_difference := fun i j =>
      (hh i j).congr ((hU i).inter (hU j))
        (fun z hz => (htrans i j z hz.1 hz.2).symm) }
  have hsupport : tsupport P.forcing ⊆ ball (0 : ℂ) R := by
    have hsub := P.forcing_tsupport_subset_of_normalization hVo hVU hs0
    intro z hz
    by_contra hzR
    exact hsub hz (hRV hzR)
  have hcompact : HasCompactSupport P.forcing := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R)
    exact (subset_tsupport P.forcing).trans (hsupport.trans ball_subset_closedBall)
  exact ⟨P, rfl, htrans, ⟨V, hVo, hRV, hVU, hs0, hsOverlap⟩, hsupport, hcompact⟩

end Wikipedia.HopfProblem.HolomorphicCousin
