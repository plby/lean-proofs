import Wikipedia.HopfProblem.SpecialPeriodsModularSurjective
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Compactness.Lindelof

/-!
# Topology of the actual modular j-function

The holomorphic modular function of Section 3.1 is an open quotient map.
Its fibres, and the inverse image of any finite set of values, are closed
and discrete.  These results concern the constructed Eisenstein-series
function; no modular covering or fundamental-domain classification is
assumed.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual modular function has no accumulation of points with a fixed
value, even at points outside that fibre. -/
theorem modularJ_eventually_ne (c : ℂ) (z : ℍ) :
    ∀ᶠ w in 𝓝[≠] z, modularJ w ≠ c := by
  by_contra h
  have hfreq : ∃ᶠ w in 𝓝[≠] z, modularJ w = c := by
    simpa only [not_not] using (not_eventually.mp h)
  have hzero : (fun w : ℍ => modularJ w - c) = 0 :=
    UpperHalfPlane.eq_zero_of_frequently
      (modularJ_mdifferentiable.sub mdifferentiable_const)
      (hfreq.mono fun w hw => sub_eq_zero.mpr hw)
  apply modularJ_not_constant
  exact ⟨c, fun w => sub_eq_zero.mp (congr_fun hzero w)⟩

/-- The inverse image of any finite set of finite modular values is closed
and discrete in the upper half-plane. -/
theorem modularJ_preimage_finite_closed_discrete {s : Set ℂ} (hs : s.Finite) :
    IsClosed (modularJ ⁻¹' s) ∧ IsDiscrete (modularJ ⁻¹' s) := by
  rw [isClosed_and_discrete_iff]
  intro z
  rw [disjoint_principal_right]
  have h : ∀ᶠ w in 𝓝[≠] z, ∀ c ∈ s, modularJ w ≠ c :=
    hs.eventually_all.mpr (fun c _ => modularJ_eventually_ne c z)
  exact h.mono fun w hw hmem => hw (modularJ w) hmem rfl

theorem modularJ_fibre_isClosed (c : ℂ) : IsClosed {z : ℍ | modularJ z = c} :=
  (modularJ_preimage_finite_closed_discrete (finite_singleton c)).1

theorem modularJ_fibre_isDiscrete (c : ℂ) : IsDiscrete {z : ℍ | modularJ z = c} :=
  (modularJ_preimage_finite_closed_discrete (finite_singleton c)).2

/-- A direct application of the open mapping theorem on the ordinary
complex upper half-plane, transferred along its open embedding into ℂ. -/
theorem modularJ_isOpenMap : IsOpenMap modularJ := by
  have hA : AnalyticOnNhd ℂ (modularJ ∘ UpperHalfPlane.ofComplex)
      {z : ℂ | 0 < z.im} := by
    intro z hz
    exact modularJ_analyticAt ⟨z, hz⟩
  have hU : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hO := (hA.is_constant_or_isOpen hU).resolve_left (by
    rintro ⟨c, hc⟩
    apply modularJ_not_constant
    refine ⟨c, fun z => ?_⟩
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hc z z.im_pos)
  intro s hs
  have ho := hO (((↑) : ℍ → ℂ) '' s) (by
    rintro _ ⟨z, _, rfl⟩
    exact z.im_pos) (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap s hs)
  simpa only [Set.image_image, Function.comp_def, UpperHalfPlane.ofComplex_apply] using ho

/-- The actual modular function is a continuous, open surjection.  This
does not identify its fibres with modular orbits; that requires a further
argument. -/
theorem modularJ_isOpenQuotientMap : IsOpenQuotientMap modularJ :=
  ⟨modularJ_surjective, modularJ_continuous, modularJ_isOpenMap⟩

/-- The elliptic exceptional locus in the upper half-plane. -/
def modularExceptionalSet : Set ℍ := modularJ ⁻¹' ({0, 1728} : Set ℂ)

theorem modularExceptionalSet_isClosed : IsClosed modularExceptionalSet :=
  (modularJ_preimage_finite_closed_discrete ((finite_singleton 1728).insert 0)).1

theorem modularExceptionalSet_isDiscrete : IsDiscrete modularExceptionalSet :=
  (modularJ_preimage_finite_closed_discrete ((finite_singleton 1728).insert 0)).2

theorem modularExceptionalSet_countable : modularExceptionalSet.Countable :=
  (HereditarilyLindelofSpace.isLindelof modularExceptionalSet).countable_of_isDiscrete
    modularExceptionalSet_isDiscrete

/-- An explicit real-coordinate homeomorphism, used only for topology;
it is not asserted to be holomorphic. -/
private def upperHalfPlaneEuclideanHomeomorph : ℂ ≃ₜ ℍ where
  toFun z := ⟨⟨z.re, Real.exp z.im⟩, Real.exp_pos z.im⟩
  invFun z := ⟨z.re, Real.log z.im⟩
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv z := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [Real.exp_log z.im_pos]
  continuous_toFun := Continuous.upperHalfPlaneMk
    (Complex.equivRealProdCLM.symm.continuous.comp
      (Complex.continuous_re.prodMk (Real.continuous_exp.comp Complex.continuous_im)))
    (fun z => Real.exp_pos z.im)
  continuous_invFun := Complex.equivRealProdCLM.symm.continuous.comp
    (UpperHalfPlane.continuous_re.prodMk
      (UpperHalfPlane.continuous_im.log (fun z => ne_of_gt z.im_pos)))

/-- Removing a countable subset from the upper half-plane preserves path
connectedness, by its explicit homeomorphism with the real plane. -/
theorem upperHalfPlane_compl_isPathConnected_of_countable {s : Set ℍ} (hs : s.Countable) :
    IsPathConnected sᶜ := by
  let e := upperHalfPlaneEuclideanHomeomorph
  have h : IsPathConnected (e ⁻¹' s)ᶜ :=
    (hs.preimage e.injective).isPathConnected_compl_of_one_lt_rank (by simp)
  exact e.isPathConnected_preimage.mp h

/-- The domain left after removing the elliptic exceptional values is
path connected, without assuming the modular-cover description. -/
theorem modularExceptionalSet_compl_isPathConnected :
    IsPathConnected modularExceptionalSetᶜ :=
  upperHalfPlane_compl_isPathConnected_of_countable modularExceptionalSet_countable

theorem modularExceptionalSet_compl_isConnected : IsConnected modularExceptionalSetᶜ :=
  modularExceptionalSet_compl_isPathConnected.isConnected

theorem modularExceptionalSet_compl_isOpen : IsOpen modularExceptionalSetᶜ :=
  modularExceptionalSet_isClosed.isOpen_compl

end Wikipedia.HopfProblem.SpecialPeriods
