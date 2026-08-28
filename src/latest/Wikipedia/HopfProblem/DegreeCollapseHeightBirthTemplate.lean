import Wikipedia.HopfProblem.DegreeCollapseExactCubicBirth
import Wikipedia.HopfProblem.DegreeCollapsePositiveCubicCoordinates
import Wikipedia.HopfProblem.DegreeCollapseNativeCubicCancellation

/-!
# A compact birth template for a linear height function

Global positive-cubic coordinates transport the supported birth to a smooth
function equal to the first coordinate off a compact set. Its critical set
is exactly the transported pair, and both complete negative-cubic endpoint
germs survive. No compatibility between a chosen native chart and a cubic
normal form is assumed.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem fderiv_comp_diffeomorph_symm_zero_iff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : V ≃ₘ[ℝ] V) {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (p : V) :
    fderiv ℝ (g ∘ D.symm) p = 0 ↔ fderiv ℝ g (D.symm p) = 0 := by
  have h := LocalFunctionReplacement.replace_critical_iff D.toPartialDiffeomorph
    (fun _ => 0) hg (mem_univ p)
  have heq : LocalFunctionReplacement.replace D.toPartialDiffeomorph (fun _ => 0) g =
      g ∘ D.symm := by
    funext x
    exact LocalFunctionReplacement.replace_of_mem D.toPartialDiffeomorph
      (fun _ => 0) g (mem_univ x)
  rw [heq, mfderiv_eq_fderiv] at h
  exact h

theorem exists_compact_height_birth_template {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∃ D : Model m ≃ₘ[ℝ] Model m,
      (∀ p, D p = (cubic σ (a ^ 2) p, p.2)) ∧
      ∃ K : Set (Model m), IsCompact K ∧ D (a, 0) ∈ K ∧ D (-a, 0) ∈ K ∧
        ∃ g : Model m → ℝ, ContDiff ℝ ∞ g ∧
          (∀ p, fderiv ℝ g p = 0 ↔ p = D (a, 0) ∨ p = D (-a, 0)) ∧
          (g =ᶠ[𝓝 (D (a, 0))] (cubic σ (-(a ^ 2)) ∘ D.symm)) ∧
          (g =ᶠ[𝓝 (D (-a, 0))] (cubic σ (-(a ^ 2)) ∘ D.symm)) ∧
          ∀ p, p ∉ K → g =ᶠ[𝓝 p] Prod.fst := by
  obtain ⟨φ, hφ, hc, -, U, hU, h0, hφU⟩ :=
    NativeCubicCancellation.exists_cutoff (m := m) isOpen_univ (mem_univ _)
  obtain ⟨a, ha, hp, hq, b, hb, hcrit, hgerms, hfix⟩ :=
    exists_exact_cubic_birth σ hσ hφ hc hU h0 hφU
  obtain ⟨D, hD⟩ := exists_positive_cubic_height_diffeomorph σ ha
  let K := D '' tsupport φ
  let g : Model m → ℝ := b ∘ D.symm
  have hUK : U ⊆ tsupport φ := by
    intro p hpU
    apply subset_tsupport φ
    change φ p ≠ 0
    rw [hφU hpU]
    norm_num
  have hcont : ContDiff ℝ ∞ g := hb.comp (contMDiff_iff_contDiff.mp D.symm.contMDiff)
  have hend (p : Model m) (hpU : p ∈ U) :
      g =ᶠ[𝓝 (D p)] cubic σ (-(a ^ 2)) ∘ D.symm := by
    have ht : Tendsto D.symm (𝓝 (D p)) (𝓝 p) := by
      simpa only [D.symm_apply_apply] using D.symm.continuous.continuousAt.tendsto (x := D p)
    exact ht.eventually (hgerms p hpU)
  refine ⟨a, ha, D, hD, K, hc.image D.continuous,
    mem_image_of_mem D (hUK hp), mem_image_of_mem D (hUK hq), g, hcont, ?_,
    hend (a, 0) hp, hend (-a, 0) hq, ?_⟩
  · intro p
    rw [fderiv_comp_diffeomorph_symm_zero_iff D hb, hcrit]
    constructor
    · rintro (h | h)
      · exact Or.inl ((D.apply_symm_apply p).symm.trans (congrArg D h))
      · exact Or.inr ((D.apply_symm_apply p).symm.trans (congrArg D h))
    · rintro (rfl | rfl) <;> simp
  · intro p hpK
    have hnot : D.symm p ∉ tsupport φ := fun h => hpK ⟨D.symm p, h, D.apply_symm_apply p⟩
    filter_upwards [D.symm.continuous.continuousAt.tendsto.eventually (hfix _ hnot)] with x hx
    change b (D.symm x) = x.1
    rw [hx]
    have h := congrArg Prod.fst (hD (D.symm x))
    simpa only [D.apply_symm_apply] using h.symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
