import StackExchange.Puzzling139335.CentralRotation.LiftPropagation.Pointwise

/-!
# The decreasing lift at the first boundary-arc overlap

The image cut uses the interval `[G(1/2), G(1)]` in the outer circle chart.
Every preceding orbit step has the increasing lift `H ∘ G⁻¹`, whereas the
first orbit arc starts with the reversed lift `H ∘ G⁻¹ ∘ (1-·)`.  Their
composition is a concrete decreasing lift for the actual overlap map.
-/

open Set

namespace Puzzling139335.CentralRotation.BoundaryLifts

variable {M Γ N : Set Plane} {d : BoundaryCoordinates M Γ N}
variable {g h : Plane ≃ᵃⁱ[ℝ] Plane} (L : BoundaryLifts d g h)

theorem image_cut_interval (hJ : g '' Γ ⊆ N) :
    g '' Γ = circleParam d.outerParam '' Icc (L.G (1 / 2)) (L.G 1) := by
  have hGimage : L.G '' Icc (1 / 2 : ℝ) 1 = Icc (L.G (1 / 2)) (L.G 1) :=
    L.G.continuous.continuousOn.image_Icc_of_monotoneOn (by norm_num)
      (L.G_increasing.monotone.monotoneOn _)
  calc
    g '' Γ = g '' (circleParam d.leftParam '' Icc (1 / 2 : ℝ) 1) :=
      congrArg (fun S : Set Plane => g '' S) d.leftCutImage.symm
    _ = (g ∘ circleParam d.leftParam) '' Icc (1 / 2 : ℝ) 1 := (image_comp _ _ _).symm
    _ = (circleParam d.outerParam ∘ L.G) '' Icc (1 / 2 : ℝ) 1 := by
      apply image_congr
      intro t ht
      exact L.image_cut_agrees hJ ht
    _ = circleParam d.outerParam '' Icc (L.G (1 / 2)) (L.G 1) := by
      rw [image_comp, hGimage]

theorem image_cut_interval_nondegenerate : L.G (1 / 2) < L.G 1 :=
  L.G_increasing (by norm_num)

theorem image_cut_interval_short : L.G 1 < L.G (1 / 2) + 1 := by
  have hh := L.G_increasing (show (1 : ℝ) < 1 / 2 + 1 by norm_num)
  simpa only [L.G_period] using hh

theorem inverse_mem_cut_interval {t : ℝ}
    (ht : t ∈ Icc (L.G (1 / 2)) (L.G 1)) : L.G.symm t ∈ Icc (1 / 2 : ℝ) 1 := by
  constructor
  · simpa only [L.G.symm_apply_apply] using L.inverse_increasing.monotone ht.1
  · simpa only [L.G.symm_apply_apply] using L.inverse_increasing.monotone ht.2

/-- The actual image-cut interior is its open outer parameter interval. -/
theorem image_cut_open_interval (hJ : g '' Γ ⊆ N) :
    g '' (Γ \ {circleParam d.leftParam (1 / 2), circleParam d.leftParam 1}) =
      circleParam d.outerParam '' Ioo (L.G (1 / 2)) (L.G 1) := by
  rw [image_sdiff g.injective, image_pair, L.image_cut_interval hJ,
    L.image_cut_agrees hJ (show (1 / 2 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 by norm_num),
    L.image_cut_agrees hJ (show (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 by norm_num)]
  exact (circleParam_image_Ioo d.outerInjective L.image_cut_interval_nondegenerate
    L.image_cut_interval_short).symm

/-- The overlap map starts on the image cut, so its source parameter is
first pulled back through the increasing lift of `g`. -/
def overlapParameter (n : ℕ) (t : ℝ) : ℝ := L.iterateParameter n (L.G.symm t)

theorem overlapParameter_continuous (n : ℕ) : Continuous (L.overlapParameter n) :=
  (L.iterateParameter_continuous n).comp L.G.symm.continuous

theorem overlapParameter_antitone (n : ℕ) : StrictAnti (L.overlapParameter n) := by
  intro s t hst
  exact L.iterateParameter_antitone n (L.inverse_increasing hst)

/-- Concrete reversed-lift formula for `F^(n+1) ∘ g⁻¹` on the image cut.
Every admissibility condition is a membership in the actual orbit gap. -/
theorem overlap_agrees (F : Plane ≃ᵃⁱ[ℝ] Plane)
    (hF : ∀ x, F x = h (g.symm x)) (hI : g.symm '' Γ ⊆ M) (hJ : g '' Γ ⊆ N)
    {Jopen : Set Plane} (hpreimage : g.symm '' (N \ Jopen) ⊆ M)
    (n : ℕ) (hbefore : ∀ k : ℕ, 1 ≤ k → k ≤ n → ((F : Plane → Plane)^[k]) '' Γ ⊆ N \ Jopen)
    {t : ℝ} (ht : t ∈ Icc (L.G (1 / 2)) (L.G 1)) :
    ((F : Plane → Plane)^[n + 1]) (g.symm (circleParam d.outerParam t)) =
      circleParam d.outerParam (L.overlapParameter n t) := by
  have ht' := L.inverse_mem_cut_interval ht
  have hpre : g.symm (circleParam d.outerParam t) = circleParam d.leftParam (L.G.symm t) := by
    apply g.injective
    rw [g.apply_symm_apply]
    simpa only [L.G.apply_symm_apply] using (L.image_cut_agrees hJ ht').symm
  rw [hpre]
  exact L.iterate_agrees F hF hI hpreimage n hbefore ht'

end Puzzling139335.CentralRotation.BoundaryLifts
