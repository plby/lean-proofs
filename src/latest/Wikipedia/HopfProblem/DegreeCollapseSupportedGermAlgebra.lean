import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopyExtension
import Wikipedia.SmoothSixDPoincare.SupportedShearGerm

/-!
# Composition and coordinate transport of supported smooth germs

The witnesses retain a jointly smooth isotopy, a common compact support,
and a fixed origin. Thus finite products of local linear generators remain
actual supported ambient motions, rather than only formal germ identities.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def Realizes (U : Set E) (f : E → E) : Prop :=
  ∃ (d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E),
    IsCompact K ∧ K ⊆ U ∧ Nonempty (SupportedRelativeIsotopy d K {0}) ∧
    (d : E → E) =ᶠ[𝓝 (0 : E)] f

theorem Realizes.comp {U : Set E} {f g : E → E}
    (hf : Realizes U f) (hg : Realizes U g) : Realizes U (f ∘ g) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  obtain ⟨e, L, hL, hLU, ⟨B⟩, he⟩ := hg
  have he0 : e (0 : E) = 0 := B.endpoint_fixed_on 0 rfl
  have het : Tendsto e (𝓝 (0 : E)) (𝓝 0) := by
    simpa only [he0] using e.continuous.tendsto (0 : E)
  have C : SupportedRelativeIsotopy (e.trans d) (K ∪ L) {0} := by
    refine ⟨(fun p => A.family (p.1, B.family p)),
      A.smooth.comp (contMDiff_fst.prodMk B.smooth), ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [B.zero, A.zero]
    · intro x
      change A.family (1, B.family (1, x)) = d (e x)
      rw [B.one, A.one]
    · intro t
      obtain ⟨dₜ, hdₜ⟩ := A.slices t
      obtain ⟨eₜ, heₜ⟩ := B.slices t
      refine ⟨eₜ.trans dₜ, ?_⟩
      intro x
      change dₜ (eₜ x) = A.family (t, B.family (t, x))
      rw [heₜ, hdₜ]
    · intro t x hx
      rw [B.fixedOutside t x (fun h => hx (Or.inr h)),
        A.fixedOutside t x (fun h => hx (Or.inl h))]
    · intro t x hx
      rw [B.fixedOn t x hx, A.fixedOn t x hx]
  refine ⟨e.trans d, K ∪ L, hK.union hL, union_subset hKU hLU, ⟨C⟩, ?_⟩
  filter_upwards [hd.comp_tendsto het, he] with x hx hy
  change d (e x) = f (g x)
  exact hx.trans (congrArg f hy)

theorem Realizes.conj (c : E ≃L[ℝ] F) {U : Set E} {f : E → E}
    (hf : Realizes U f) :
    Realizes (c '' U) (fun y => c (f (c.symm y))) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  let D := (c.symm.toDiffeomorph.trans d).trans c.toDiffeomorph
  have B : SupportedRelativeIsotopy D (c '' K) {0} := by
    refine ⟨(fun p => c (A.family (p.1, c.symm p.2))),
      c.toDiffeomorph.contMDiff.comp (A.smooth.comp
        (contMDiff_fst.prodMk (c.symm.toDiffeomorph.contMDiff.comp contMDiff_snd))),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro y
      rw [A.zero, c.apply_symm_apply]
    · intro y
      change c (A.family (1, c.symm y)) = c (d (c.symm y))
      rw [A.one]
    · intro t
      obtain ⟨e, he⟩ := A.slices t
      refine ⟨(c.symm.toDiffeomorph.trans e).trans c.toDiffeomorph, ?_⟩
      intro y
      change c (e (c.symm y)) = c (A.family (t, c.symm y))
      rw [he]
    · intro t y hy
      have hnot : c.symm y ∉ K := fun h => hy ⟨c.symm y, h, c.apply_symm_apply y⟩
      rw [A.fixedOutside t (c.symm y) hnot, c.apply_symm_apply]
    · intro t y hy
      have hy0 : y = 0 := mem_singleton_iff.mp hy
      subst y
      rw [map_zero, A.fixedOn t 0 rfl, map_zero]
  refine ⟨D, c '' K, hK.image c.continuous, image_mono hKU, ⟨B⟩, ?_⟩
  have ht : Tendsto c.symm (𝓝 (0 : F)) (𝓝 0) := by
    simpa only [map_zero] using c.symm.continuous.tendsto (0 : F)
  filter_upwards [hd.comp_tendsto ht] with y hy
  exact congrArg c hy

theorem realizes_shear [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : F →L[ℝ] E) {U : Set (E × F)} (hU : IsOpen U) (h0 : (0 : E × F) ∈ U) :
    Realizes U (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨A, K, hK, hKU, hA, hA0, hdiff, hfix, -, hcore, hgerm⟩ :=
    exists_supported_shear_isotopy L hU h0
  obtain ⟨d, hd⟩ := hdiff 1
  have H : SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    have hx0 : x = 0 := mem_singleton_iff.mp hx
    subst x
    exact hcore t 0
  refine ⟨d, K, hK, hKU, ⟨H⟩, ?_⟩
  filter_upwards [hgerm] with x hx
  exact (hd x).trans hx

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
