import Wikipedia.NoExoticSixSphere.SmoothSphereRotation
import Wikipedia.NoExoticSixSphere.CollaredValueCurve
import Wikipedia.NoExoticSixSphere.CylinderTargetCorrection

/-!
# Endpoint-preserving correction of a nearby regular sphere value

The explicit smooth rotation is the identity on the protected ends and is
constant in time in the middle. Its homotopy from the identity fixes those
ends at every stage. Regularity of the corrected cylinder still requires a
nearby regular value of the original cylinder, together with regularity of
the endpoint maps at the moving values. These requirements are explicit.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere.SphereTargetCorrection

variable {n : ℕ} (b c : Sphere n) (hc : dist c b < 1 / 2)

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable def value : C(ℝ, Sphere n) :=
  CollaredValueCurve.curve b c (by linarith)

theorem value_dist_lt (t : ℝ) : dist (value b c hc t) b < 1 :=
  (CollaredValueCurve.dist_curve_le b c (by linarith) t).trans_lt (by linarith)

theorem value_sum_ne_zero (t : ℝ) :
    (value b c hc t : EuclideanSpace ℝ (Fin (n + 1))) + b ≠ 0 := by
  simpa only [add_comm] using nearby_sum_ne_zero b (value b c hc t) (value_dist_lt b c hc t)

noncomputable def rotation (t : ℝ) : Sphere n ≃ₘ⟮𝓡 n, 𝓡 n⟯ Sphere n :=
  sphereRotation (n := n) (value b c hc t) b

theorem contMDiff_rotation_action :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × Sphere n ↦ rotation b c hc p.1 p.2) :=
  contMDiff_sphereRotation_apply
    ((CollaredValueCurve.contMDiff_curve b c (by linarith)).comp contMDiff_fst)
    contMDiff_const contMDiff_snd (fun p ↦ value_sum_ne_zero b c hc p.1)

variable {M : Type*} [TopologicalSpace M]

noncomputable def action : C(ℝ × Sphere n, Sphere n) :=
  ⟨fun p ↦ rotation b c hc p.1 p.2, (contMDiff_rotation_action b c hc).continuous⟩

noncomputable def corrected (F : C(ℝ × M, Sphere n)) : C(ℝ × M, Sphere n) :=
  (action b c hc).comp ⟨fun p ↦ (p.1, F p), continuous_fst.prodMk F.continuous⟩

theorem corrected_eq_of_cutoff_zero (F : C(ℝ × M, Sphere n)) {t : ℝ}
    (ht : CollaredValueCurve.cutoff t = 0) (x : M) : corrected b c hc F (t, x) = F (t, x) := by
  change sphereRotation (n := n) (CollaredValueCurve.curve b c (by linarith) t) b (F (t, x)) = _
  rw [CollaredValueCurve.curve_of_cutoff_zero b c _ ht]
  exact sphereRotation_self b _

noncomputable def homotopy (F : C(ℝ × M, Sphere n)) :
    F.HomotopyRel (corrected b c hc F) {p | p.1 ≤ 1 / 8 ∨ 7 / 8 ≤ p.1} where
  toFun p := sphereRotation (n := n)
    (CollaredValueCurve.homotopy b c (by linarith) (p.1, p.2.1)) b (F p.2)
  continuous_toFun := by
    have hA : Continuous (fun p : unitInterval × (ℝ × M) ↦
        CollaredValueCurve.homotopy b c (by linarith) (p.1, p.2.1)) :=
      (CollaredValueCurve.homotopy b c (by linarith)).continuous.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    apply continuous_sphereRotation_apply (n := n) hA continuous_const
      (F.continuous.comp continuous_snd)
    intro p
    have hd : dist (CollaredValueCurve.homotopy b c (by linarith) (p.1, p.2.1)) b < 1 :=
      (CollaredValueCurve.homotopy_dist_le b c (by linarith) p.1 p.2.1).trans_lt (by linarith)
    simpa only [add_comm] using nearby_sum_ne_zero b _ hd
  map_zero_left p := by
    rw [(CollaredValueCurve.homotopy b c (by linarith)).apply_zero]
    exact sphereRotation_self b (F p)
  map_one_left p := by
    rw [(CollaredValueCurve.homotopy b c (by linarith)).apply_one]
    rfl
  prop' u p hp := by
    have ht : CollaredValueCurve.cutoff p.1 = 0 :=
      hp.elim CollaredValueCurve.cutoff_left CollaredValueCurve.cutoff_right
    change sphereRotation (n := n)
      (CollaredValueCurve.homotopy b c (by linarith) (u, p.1)) b (F p) = F p
    rw [CollaredValueCurve.homotopy_of_cutoff_zero b c _ u ht]
    exact sphereRotation_self b (F p)

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [ChartedSpace H M]

theorem contMDiff_corrected {F : C(ℝ × M, Sphere n)}
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) ∞ F) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) ∞ (corrected b c hc F) :=
  contMDiff_cylinderTargetCorrection (rotation b c hc) (contMDiff_rotation_action b c hc) hF

theorem regular_corrected {F : C(ℝ × M, Sphere n)}
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) ∞ F)
    {f₀ f₁ : M → Sphere n} (h₀ : ContMDiff I (𝓡 n) ∞ f₀) (h₁ : ContMDiff I (𝓡 n) ∞ f₁)
    (hleft : ∀ t ≤ (1 / 4 : ℝ), ∀ x, F (t, x) = f₀ x)
    (hright : ∀ t, (3 / 4 : ℝ) ≤ t → ∀ x, F (t, x) = f₁ x)
    (hreg₀ : ∀ t x, f₀ x = value b c hc t → Function.Surjective (mfderiv I (𝓡 n) f₀ x))
    (hreg₁ : ∀ t x, f₁ x = value b c hc t → Function.Surjective (mfderiv I (𝓡 n) f₁ x))
    (hreg : ∀ p, F p = c → Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) F p)) :
    ∀ p, corrected b c hc F p = b → Function.Surjective
      (mfderiv ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) (corrected b c hc F) p) := by
  apply regular_cylinderTargetCorrection (rotation b c hc) (contMDiff_rotation_action b c hc)
    hF h₀ h₁ (1 / 4) (3 / 4) hleft hright (value b c hc) b c
    (fun t ↦ sphereRotation_apply (value b c hc t) b) hreg₀ hreg₁
    (sphereRotation (n := n) c b) ?_ (sphereRotation_apply c b) hreg
  intro t ht
  change sphereRotation (n := n) (CollaredValueCurve.curve b c (by linarith) t) b =
    sphereRotation (n := n) c b
  rw [CollaredValueCurve.curve_middle b c _ ⟨ht.1.le, ht.2.le⟩]

end NoExoticSixSphere.SphereTargetCorrection
