import Wikipedia.HopfProblem.DegreeCollapseFiniteSphereProductCharts

/-!
# Transfer of actual smooth regularity through the fixed sphere charts

An eventual coordinate square suffices for smoothness and surjectivity of
the original native derivative. The source and target chart derivatives are
the proved bijective derivatives of the actual stereographic product charts.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereChartRegularity

open NoExoticSixSphere FiniteSphereProductCharts

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {m n : ℕ}
  (e : E ≃L[ℝ] V m) (d : F ≃L[ℝ] V n)

def conjugate (v : E → F) : Sphere m → Sphere n :=
  (chart n d).symm ∘ (v ∘ chart m e)

theorem eventuallyEq_of_inverse_square (f : Sphere m → Sphere n) (v : E → F) (p : E)
    (h : (fun u ↦ f ((chart m e).symm u)) =ᶠ[𝓝 p]
      (fun u ↦ (chart n d).symm (v u))) :
    f =ᶠ[𝓝 ((chart m e).symm p)] conjugate e d v := by
  have hc := (chart_contMDiffAt m e (chart_symm_ne_pole m e p)).continuousAt
  have ht : Tendsto (chart m e) (𝓝 ((chart m e).symm p))
      (𝓝 (chart m e ((chart m e).symm p))) := hc
  rw [chart_right_inv] at ht
  have hh := h.comp_tendsto ht
  have hs : (chart m e).source ∈ 𝓝 ((chart m e).symm p) :=
    (chart m e).open_source.mem_nhds
      (by simpa only [chart_source, mem_compl_iff, mem_singleton_iff]
        using chart_symm_ne_pole m e p)
  filter_upwards [hh, hs] with y hy hys
  change f ((chart m e).symm (chart m e y)) = (chart n d).symm (v (chart m e y)) at hy
  have hl : (chart m e).symm (chart m e y) = y := (chart m e).left_inv hys
  exact (congrArg f hl).symm.trans hy

theorem contMDiffAt_of_square (f : Sphere m → Sphere n) (v : E → F) {x : Sphere m}
    (hx : x ≠ spherePole m)
    (hv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ v (chart m e x))
    (h : f =ᶠ[𝓝 x] conjugate e d v) : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f x := by
  have hc := chart_contMDiffAt m e hx
  exact ((chart_symm_contMDiff n d).contMDiffAt.comp x (hv.comp x hc)).congr_of_eventuallyEq h

theorem mfderiv_surjective_of_square (f : Sphere m → Sphere n) (v : E → F) {x : Sphere m}
    (hx : x ≠ spherePole m)
    (hv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ v (chart m e x))
    (hs : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) v (chart m e x)))
    (h : f =ᶠ[𝓝 x] conjugate e d v) :
    Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x) := by
  have hc := (chart_contMDiffAt m e hx).mdifferentiableAt (by simp)
  have hd := hv.mdifferentiableAt (by simp)
  have hi : MDifferentiableAt 𝓘(ℝ, F) (𝓡 n) (chart n d).symm (v (chart m e x)) :=
    (chart_symm_contMDiff n d).mdifferentiable (by simp) _
  have hg : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) (conjugate e d v) x) := by
    change Function.Surjective (mfderiv (𝓡 m) (𝓡 n)
      ((chart n d).symm ∘ (v ∘ chart m e)) x)
    rw [mfderiv_comp x hi (hd.comp x hc), mfderiv_comp x hd hc]
    exact (chart_symm_mfderiv_bijective n d _).surjective.comp
      (hs.comp (chart_mfderiv_bijective m e hx).surjective)
  have he : mfderiv (𝓡 m) (𝓡 n) f x =
      mfderiv (𝓡 m) (𝓡 n) (conjugate e d v) x := h.mfderiv_eq
  intro z
  obtain ⟨w, hw⟩ := hg z
  exact ⟨w, (congrArg (fun L : V m →L[ℝ] V n ↦ L w) he).trans hw⟩

theorem contMDiffAt_of_inverse_square (f : Sphere m → Sphere n) (v : E → F) (p : E)
    (hv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ v p)
    (h : (fun u ↦ f ((chart m e).symm u)) =ᶠ[𝓝 p]
      (fun u ↦ (chart n d).symm (v u))) :
    ContMDiffAt (𝓡 m) (𝓡 n) ∞ f ((chart m e).symm p) := by
  apply contMDiffAt_of_square e d f v (chart_symm_ne_pole m e p)
  · simpa only [chart_right_inv] using hv
  · exact eventuallyEq_of_inverse_square e d f v p h

theorem mfderiv_surjective_of_inverse_square (f : Sphere m → Sphere n) (v : E → F) (p : E)
    (hv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ v p)
    (hs : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) v p))
    (h : (fun u ↦ f ((chart m e).symm u)) =ᶠ[𝓝 p]
      (fun u ↦ (chart n d).symm (v u))) :
    Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f ((chart m e).symm p)) := by
  apply mfderiv_surjective_of_square e d f v (chart_symm_ne_pole m e p)
  · simpa only [chart_right_inv] using hv
  · exact (chart_right_inv m e p).symm ▸ hs
  · exact eventuallyEq_of_inverse_square e d f v p h

theorem mfderiv_surjective_iff_fderiv (v : E → F) (p : E) :
    Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) v p) ↔
      Function.Surjective (fderiv ℝ v p) := by
  have hd : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) v p : E →L[ℝ] F) = fderiv ℝ v p :=
    mfderiv_eq_fderiv
  constructor
  · intro hs z
    obtain ⟨w, hw⟩ := hs z
    exact ⟨w, (congrArg (fun L : E →L[ℝ] F ↦ L w) hd).symm.trans hw⟩
  · intro hs z
    obtain ⟨w, hw⟩ := hs z
    exact ⟨w, (congrArg (fun L : E →L[ℝ] F ↦ L w) hd).trans hw⟩

theorem mfderiv_injective_of_square (f : Sphere m → Sphere n) (v : E → F) {x : Sphere m}
    (hx : x ≠ spherePole m)
    (hv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ v (chart m e x))
    (hs : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) v (chart m e x)))
    (h : f =ᶠ[𝓝 x] conjugate e d v) :
    Function.Injective (mfderiv (𝓡 m) (𝓡 n) f x) := by
  have hc := (chart_contMDiffAt m e hx).mdifferentiableAt (by simp)
  have hd := hv.mdifferentiableAt (by simp)
  have hi : MDifferentiableAt 𝓘(ℝ, F) (𝓡 n) (chart n d).symm (v (chart m e x)) :=
    (chart_symm_contMDiff n d).mdifferentiable (by simp) _
  have hg : Function.Injective (mfderiv (𝓡 m) (𝓡 n) (conjugate e d v) x) := by
    change Function.Injective (mfderiv (𝓡 m) (𝓡 n)
      ((chart n d).symm ∘ (v ∘ chart m e)) x)
    rw [mfderiv_comp x hi (hd.comp x hc), mfderiv_comp x hd hc]
    exact (chart_symm_mfderiv_bijective n d _).injective.comp
      (hs.comp (chart_mfderiv_bijective m e hx).injective)
  have he : mfderiv (𝓡 m) (𝓡 n) f x =
      mfderiv (𝓡 m) (𝓡 n) (conjugate e d v) x := h.mfderiv_eq
  intro a b hab
  apply hg
  exact (congrArg (fun L : V m →L[ℝ] V n ↦ L a) he).symm.trans
    (hab.trans (congrArg (fun L : V m →L[ℝ] V n ↦ L b) he))

theorem mfderiv_injective_of_inverse_square (f : Sphere m → Sphere n) (v : E → F) (p : E)
    (hv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ v p)
    (hs : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) v p))
    (h : (fun u ↦ f ((chart m e).symm u)) =ᶠ[𝓝 p]
      (fun u ↦ (chart n d).symm (v u))) :
    Function.Injective (mfderiv (𝓡 m) (𝓡 n) f ((chart m e).symm p)) := by
  apply mfderiv_injective_of_square e d f v (chart_symm_ne_pole m e p)
  · simpa only [chart_right_inv] using hv
  · exact (chart_right_inv m e p).symm ▸ hs
  · exact eventuallyEq_of_inverse_square e d f v p h

theorem mfderiv_injective_iff_fderiv (v : E → F) (p : E) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) v p) ↔
      Function.Injective (fderiv ℝ v p) := by
  have hd : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) v p : E →L[ℝ] F) = fderiv ℝ v p :=
    mfderiv_eq_fderiv
  constructor
  · intro hs a b hab
    apply hs
    exact (congrArg (fun L : E →L[ℝ] F ↦ L a) hd).trans
      (hab.trans (congrArg (fun L : E →L[ℝ] F ↦ L b) hd).symm)
  · intro hs a b hab
    apply hs
    exact (congrArg (fun L : E →L[ℝ] F ↦ L a) hd).symm.trans
      (hab.trans (congrArg (fun L : E →L[ℝ] F ↦ L b) hd))


end Wikipedia.HopfProblem.DegreeCollapse.SphereChartRegularity
