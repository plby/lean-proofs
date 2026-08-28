import Wikipedia.HopfProblem.DegreeCollapseBirthPlacement
import Wikipedia.HopfProblem.DegreeCollapseNativePairInsertion
import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationHessian

/-!
# Construct a supported Morse birth near any original regular point

All model and placement data are constructed. A positive-cubic global height
change and a small dilation place the entire compact cutoff in an original
regular chart. Reversing the cubic parameter then adds exactly two native
Morse points and leaves all exterior function germs unchanged. Both full
scaled negative-cubic endpoint germs are retained for intrinsic index control.
No handle trade or global handle elimination is asserted here.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_native_morse_birth {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {x : M} (hx : x ∉ criticalPoints E f) {m : ℕ}
    (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
        (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧ (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ.target ⊆ U ∧
        (∀ z ∈ Φ.source, f (Φ z) = f x + δ * cubic σ (a ^ 2) z) ∧
        ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
          (criticalPoints E g).ncard = (criticalPoints E f).ncard + 2 ∧
          (∀ y, y ∈ criticalPoints E g ↔
            y ∈ criticalPoints E f ∨ y = Φ (a, 0) ∨ y = Φ (-a, 0)) ∧
          (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
          (∀ y ∈ criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
          (g ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => f x + δ * cubic σ (-(a ^ 2)) z) ∧
          (g ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z => f x + δ * cubic σ (-(a ^ 2)) z) := by
  obtain ⟨H, h0H, -, hHU, hH⟩ := exists_centered_native_height_chart hf hx hdim hU hxU
  obtain ⟨φ, hφ, hc, -, W, hW, h0W, hφW⟩ :=
    NativeCubicCancellation.exists_cutoff (m := m) isOpen_univ (mem_univ _)
  obtain ⟨a, ha, hpW, hqW, b, hb, hcritb, hgerms, hfix⟩ :=
    exists_exact_cubic_birth σ hσ hφ hc hW h0W hφW
  have hmb : MorsePerturbation.IsMorse b := by
    intro z hz
    have hzW : z ∈ W := (hcritb z).mp hz |>.elim (fun h => h ▸ hpW) (fun h => h ▸ hqW)
    have heq := hgerms z hzW
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]
    apply cubic_isMorse σ hσ (neg_ne_zero.mpr (pow_ne_zero 2 ha.ne'))
    rw [← heq.fderiv_eq]
    exact hz
  obtain ⟨D, hD⟩ := exists_positive_cubic_height_diffeomorph σ ha
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_compact_smul_subset (hc.image D.continuous) H.open_source h0H
  let A : Model m ≃L[ℝ] Model m :=
    (LinearEquiv.smulOfNeZero ℝ (Model m) δ hδ.ne').toContinuousLinearEquiv
  let C := D.trans A.toDiffeomorph
  let Φ := C.toPartialDiffeomorph.trans H
  have hC (z : Model m) : C z = δ • D z := rfl
  have hKΦ : tsupport φ ⊆ Φ.source := by
    intro z hz
    change z ∈ univ ∧ C z ∈ H.source
    exact ⟨mem_univ _, hsmall ⟨D z, mem_image_of_mem D hz, rfl⟩⟩
  have hWK : W ⊆ tsupport φ := by
    intro z hz
    apply subset_tsupport φ
    change φ z ≠ 0
    rw [hφW hz]
    norm_num
  have hpΦ := hKΦ (hWK hpW)
  have hqΦ := hKΦ (hWK hqW)
  have hΦU : Φ.target ⊆ U := fun _ hy => hHU hy.1
  let b₀ : Model m → ℝ := fun z => f x + δ * cubic σ (a ^ 2) z
  let b₁ : Model m → ℝ := fun z => f x + δ * b z
  have hb₀ : ContDiff ℝ ∞ b₀ := contDiff_const.add (contDiff_const.mul (contDiff_cubic σ _))
  have hb₁ : ContDiff ℝ ∞ b₁ := contDiff_const.add (contDiff_const.mul hb)
  have hmb₁ : MorsePerturbation.IsMorse b₁ := euclidean_isMorse_affine hb hmb hδ.ne' (f x)
  have hmodel (z : Model m) (hz : z ∈ Φ.source) : f (Φ z) = b₀ z := by
    change f (H (C z)) = _
    rw [hH (C z) hz.2, hC, hD]
    rfl
  have hfix₁ (z : Model m) (hz : z ∉ tsupport φ) : b₁ z = b₀ z := by
    dsimp [b₁, b₀]
    rw [(hfix z hz).self_of_nhds]
  have hderiv (v : Model m → ℝ) (hv : ContDiff ℝ ∞ v) (z : Model m) :
      fderiv ℝ (fun y => f x + δ * v y) z = δ • fderiv ℝ v z := by
    rw [fderiv_const_add, fderiv_const_mul (hv.differentiable (by simp) z)]
  have hreg₀ (z : Model m) : fderiv ℝ b₀ z ≠ 0 := by
    rw [hderiv _ (contDiff_cubic σ _) z]
    exact smul_ne_zero hδ.ne' (positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) z)
  have hcrit₁ (z : Model m) : fderiv ℝ b₁ z = 0 ↔ z = (a, 0) ∨ z = (-a, 0) := by
    rw [hderiv b hb z, smul_eq_zero]
    simp only [hδ.ne', false_or, hcritb]
  have hpq : (a, (0 : Fin m → ℝ)) ≠ (-a, 0) := by
    intro h
    have hh := congrArg Prod.fst h
    change a = -a at hh
    linarith
  let L : E ≃L[ℝ] Model m := ContinuousLinearEquiv.ofFinrankEq (by
    simp only [Model, Module.finrank_prod, Module.finrank_self, Module.finrank_pi, Fintype.card_fin]
    exact hdim.symm)
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior, hkeep, hnew⟩ := insert_morse_chart_pair Φ L hf hm
    hb₀ hb₁ hmb₁ hc hKΦ hmodel hfix₁ hpΦ hqΦ hpq hreg₀ hcrit₁
  have hend (z : Model m) (hzΦ : z ∈ Φ.source) (hzW : z ∈ W) :
      g ∘ Φ =ᶠ[𝓝 z] fun w => f x + δ * cubic σ (-(a ^ 2)) w := by
    filter_upwards [Φ.open_source.mem_nhds hzΦ, hgerms z hzW] with w hw heq
    change g (Φ w) = _
    rw [hnew w hw]
    change f x + δ * b w = _
    rw [heq]
  refine ⟨a, δ, ha, hδ, Φ, hpΦ, hqΦ, hΦU, hmodel,
    g, hg, hmg, hcount, hcritg, ?_, hkeep, hend _ hpΦ hpW, hend _ hqΦ hqW⟩
  intro y hy
  apply hexterior y
  rintro ⟨z, hz, rfl⟩
  exact hy (hΦU (Φ.map_source' (hKΦ hz)))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
