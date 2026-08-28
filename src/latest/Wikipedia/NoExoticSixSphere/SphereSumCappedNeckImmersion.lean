import Wikipedia.NoExoticSixSphere.SpherePositiveRadialCoordinates
import Wikipedia.NoExoticSixSphere.SphereSumCappedNeck

/-!
# The capped neck is immersive for every positive opening

At least one radial projection has positive radius and positive scalar
derivative. Its actual local inverse proves injectivity of the full native
derivative. Positive scaling and the original target chart preserve it.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem injective_mfderiv_capPair {a : ℝ} (ha : 0 < a) (q : Parameter) :
    Injective (mfderiv Model 𝓘(ℝ, Vector 3 × Vector 3) (capPair a) q) := by
  have hfactor : ∃ π : Vector 3 × Vector 3 → Vector 3,
      ContMDiff 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 3) ∞ π ∧
      IsLocalDiffeomorphAt Model (𝓡 3) ∞ (π ∘ capPair a) q := by
    by_cases hq : -a < q.1
    · exact ⟨Prod.fst, contDiff_fst.contMDiff,
        isLocalDiffeomorphAt_radial_profile (contDiff_capProfile_slice a) q
          (capProfile_pos hq) (deriv_capProfile_pos hq).ne'⟩
    · have hq' : -a < (reverse q).1 := by dsimp [reverse]; linarith
      have hr : IsLocalDiffeomorphAt Model Model ∞ reverse q :=
        ⟨reverseCoordinates, mem_univ _, fun _ _ ↦ rfl⟩
      exact ⟨Prod.snd, contDiff_snd.contMDiff, hr.comp (𝓡 3) (Vector 3)
        (isLocalDiffeomorphAt_radial_profile (contDiff_capProfile_slice a) (reverse q)
          (capProfile_pos hq') (deriv_capProfile_pos hq').ne')⟩
  obtain ⟨π, hπ, hd⟩ := hfactor
  have hi := (hd.mfderivToContinuousLinearEquiv (by simp)).injective
  change Injective (mfderiv Model (𝓡 3) (π ∘ capPair a) q) at hi
  rw [mfderiv_comp q (hπ.mdifferentiableAt (by simp))
    ((contMDiff_capPair_slice a).mdifferentiableAt (by simp))] at hi
  intro v w hvw
  apply hi
  exact congrArg (mfderiv 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 3) π (capPair a q)) hvw

def scaledCapPair (ε a : ℝ) (q : Parameter) : Vector 3 × Vector 3 := ε • capPair a q

theorem contMDiff_scaledCapPair (ε a : ℝ) :
    ContMDiff Model 𝓘(ℝ, Vector 3 × Vector 3) ∞ (scaledCapPair ε a) := by
  have hc : ContMDiff Model 𝓘(ℝ, ℝ) ∞ (fun _ : Parameter ↦ ε) := contMDiff_const
  exact hc.smul (contMDiff_capPair_slice a)

theorem injective_mfderiv_scaledCapPair {ε a : ℝ} (hε : ε ≠ 0) (ha : 0 < a)
    (q : Parameter) :
    Injective (mfderiv Model 𝓘(ℝ, Vector 3 × Vector 3) (scaledCapPair ε a) q) := by
  let π : Vector 3 × Vector 3 → Vector 3 × Vector 3 := fun z ↦ ε⁻¹ • z
  have hc : ContMDiff 𝓘(ℝ, Vector 3 × Vector 3) 𝓘(ℝ, ℝ) ∞
      (fun _ : Vector 3 × Vector 3 ↦ ε⁻¹) := contMDiff_const
  have hπ : ContMDiff 𝓘(ℝ, Vector 3 × Vector 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ π :=
    hc.smul contMDiff_id
  have he : capPair a = π ∘ scaledCapPair ε a := by
    funext w
    exact (inv_smul_smul₀ hε (capPair a w)).symm
  have hi := injective_mfderiv_capPair ha q
  rw [he, mfderiv_comp q (hπ.mdifferentiableAt (by simp))
    ((contMDiff_scaledCapPair ε a).mdifferentiableAt (by simp))] at hi
  intro v w hvw
  apply hi
  exact congrArg (mfderiv 𝓘(ℝ, Vector 3 × Vector 3)
    𝓘(ℝ, Vector 3 × Vector 3) π (scaledCapPair ε a q)) hvw

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

theorem injective_mfderiv_chartCapNeck_slice {ε a R : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (hR : 1 ≤ R)
    (hprod : closedBall (0 : Vector 3) (ε * R) ×ˢ
      closedBall (0 : Vector 3) (ε * R) ⊆ Φ.source)
    (q : Parameter) (hq : q.1 ∈ Icc (-R) R) :
    Injective (mfderiv Model (𝓡 6) (fun w ↦ chartCapNeck Φ ε (a, w)) q) := by
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ
      (scaledCapPair ε a q) :=
    ⟨Φ, hprod (scaled_capPair_mem_product hε hR a q hq), fun _ _ ↦ rfl⟩
  have hi := (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  change Injective (mfderiv 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) Φ (scaledCapPair ε a q)) at hi
  change Injective (mfderiv Model (𝓡 6) (Φ ∘ scaledCapPair ε a) q)
  rw [mfderiv_comp q (hlocal.mdifferentiableAt (by simp))
    ((contMDiff_scaledCapPair ε a).mdifferentiableAt (by simp))]
  exact hi.comp (injective_mfderiv_scaledCapPair hε.ne' ha q)

end NoExoticSixSphere.SphereSumNeck
