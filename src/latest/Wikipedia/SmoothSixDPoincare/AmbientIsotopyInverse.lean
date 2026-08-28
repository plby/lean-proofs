import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-! # Inverting a native isotopy by time reversal and a fixed endpoint inverse -/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem IsotopicToIdentity.symm {e : Diffeomorph J J M M ∞}
    (he : IsotopicToIdentity e) : IsotopicToIdentity e.symm := by
  obtain ⟨A, hA, hA₀, hA₁, hdiff⟩ := he
  let B : ℝ × M → M := fun p => e.symm (A (1 - p.1, p.2))
  have hrev : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 - t) :=
    (contDiff_const.sub contDiff_id).contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B :=
    e.symm.contMDiff.comp (hA.comp ((hrev.comp contMDiff_fst).prodMk contMDiff_snd))
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro x
    change e.symm (A (1 - 0, x)) = x
    rw [sub_zero, hA₁, e.symm_apply_apply]
  · intro x
    change e.symm (A (1 - 1, x)) = e.symm x
    rw [sub_self, hA₀]
  · intro t
    obtain ⟨d, hd⟩ := hdiff (1 - t)
    refine ⟨d.trans e.symm, ?_⟩
    intro x
    change e.symm (A (1 - t, x)) = e.symm (d x)
    rw [hd]

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
