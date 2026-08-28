import Wikipedia.SmoothSixDPoincare.SheetNormalCoordinates

/-!
# The kernel of an actual tubular normal-coordinate derivative

For a genuine partial diffeomorphism with the given map as its zero section,
the kernel of the native normal-coordinate derivative is exactly the image
of the zero-section derivative. The proof uses the native inverse chain rule,
not a dimension count or an assumed normal-bundle identification.
-/

noncomputable section

open Set Function
open Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D B E M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞)

/-- The zero-section derivative is the actual chart derivative on the horizontal subspace. -/
theorem mfderiv_zero_section {f : D → M} (hzero : ∀ x, Φ (x, 0) = f x)
    {x : D} (hx : (x, 0) ∈ Φ.source) :
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x =
      (mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (x, 0)).comp
        (ContinuousLinearMap.inl ℝ D B) := by
  have heq : f = Φ ∘ (ContinuousLinearMap.inl ℝ D B) :=
    funext (fun y => (hzero y).symm)
  have hinl : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, D × B) ∞ (ContinuousLinearMap.inl ℝ D B) :=
    (ContinuousLinearMap.inl ℝ D B).contDiff.contMDiff
  rw [heq, mfderiv_comp x (Φ.mdifferentiableAt (by simp) hx)
    (hinl.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
    (ContinuousLinearMap.inl ℝ D B).fderiv]
  rfl

/-- The normal-coordinate derivative kills exactly, and only, the zero-section tangents. -/
theorem ker_normalDerivative_eq_range_zero_section {f : D → M}
    (hzero : ∀ x, Φ (x, 0) = f x) {x : D} (hx : (x, 0) ∈ Φ.source) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x)).ker =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).range := by
  let L : (D × B) →L[ℝ] E := mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (x, 0)
  let R : E →L[ℝ] (D × B) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (Φ (x, 0))
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, D × B) 𝓘(ℝ, E) :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  have hRL : R.comp L = ContinuousLinearMap.id ℝ (D × B) :=
    hdiff.symm_comp_deriv hx
  have hRL_apply (q : D × B) : R (L q) = q := by
    change (R.comp L) q = q
    rw [hRL]
    rfl
  have hsurj : Surjective L := (PartialChart.bijective_mfderiv Φ hx).2
  have hnormal : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x) =
      (ContinuousLinearMap.snd ℝ D B).comp R := by
    rw [← hzero x, mfderiv_normalCoordinate Φ (Φ.map_source' hx)]
    rfl
  rw [hnormal, mfderiv_zero_section Φ hzero hx]
  ext v
  constructor
  · intro hv
    obtain ⟨⟨a, b⟩, hab⟩ := hsurj v
    have hb : b = 0 := by
      change (R v).2 = 0 at hv
      rw [← hab, hRL_apply] at hv
      exact hv
    subst b
    exact ⟨a, hab⟩
  · rintro ⟨a, rfl⟩
    change (R (L (a, 0))).2 = 0
    rw [hRL_apply]

/-- A full strip germ with a surjective coordinate derivative identifies the same tangent kernel. -/
theorem ker_normalDerivative_eq_range_of_germ {f k : D → M}
    (hzero : ∀ x, Φ (x, 0) = f x) {x : D} (hx : (x, 0) ∈ Φ.source)
    {c : D → D} (hc : ContDiffAt ℝ ∞ c x)
    (hk : ContMDiffAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ k (c x))
    (hcs : Surjective (fderiv ℝ c x)) (hgerm : f =ᶠ[𝓝 x] k ∘ c) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x)).ker =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) k (c x)).range := by
  rw [ker_normalDerivative_eq_range_zero_section Φ hzero hx, hgerm.mfderiv_eq,
    mfderiv_comp x (hk.mdifferentiableAt (by simp))
      (hc.contMDiffAt.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hcs)

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates
