import Wikipedia.HopfProblem.DegreeCollapseInvertibleFrameJoin
import Wikipedia.HopfProblem.DegreeCollapseAxisDerivativeBlock

/-!
# Smooth joins retaining the full axis derivative, including shear

The tangential shear is joined in its vector space, while the transverse
block is joined inside its actual determinant component. Both whole local
germs are retained; the resulting full derivative is invertible everywhere.
-/

noncomputable section

open Set Filter Function Module
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι] [Nontrivial ι]

/-- Join local shear and transverse data, keeping both complete endpoint germs. -/
theorem exists_smooth_sheared_frame_join (basis : Basis ι ℝ V)
    {A₀ A₁ : ℝ → (V →L[ℝ] ℝ)} {T₀ T₁ : ℝ → (V →L[ℝ] V)}
    {U₀ U₁ : Set ℝ}
    (hA₀ : ContDiffOn ℝ ∞ A₀ U₀) (hA₁ : ContDiffOn ℝ ∞ A₁ U₁)
    (hT₀ : ContDiffOn ℝ ∞ T₀ U₀) (hT₁ : ContDiffOn ℝ ∞ T₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (h0 : (0 : ℝ) ∈ U₀) (h1 : (1 : ℝ) ∈ U₁)
    (hsign : 0 < (T₀ 0).toLinearMap.det * (T₁ 1).toLinearMap.det) :
    ∃ A : ℝ → (V →L[ℝ] ℝ), ∃ T : ℝ → (V →L[ℝ] V),
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ T ∧
      (∀ s, (T s).IsInvertible) ∧
      (∀ s, (FrameField.shearedBlock (A s) (T s)).IsInvertible) ∧
      (A =ᶠ[𝓝 (0 : ℝ)] A₀) ∧ (A =ᶠ[𝓝 (1 : ℝ)] A₁) ∧
      (T =ᶠ[𝓝 (0 : ℝ)] T₀) ∧ (T =ᶠ[𝓝 (1 : ℝ)] T₁) := by
  let S : TopologicalSpace.Opens (V →L[ℝ] ℝ) := ⟨univ, isOpen_univ⟩
  let γ : Path (⟨A₀ 0, mem_univ _⟩ : S) ⟨A₁ 1, mem_univ _⟩ := {
    toFun := fun t => ⟨(1 - (t : ℝ)) • A₀ 0 + (t : ℝ) • A₁ 1, mem_univ _⟩
    continuous_toFun := by fun_prop
    source' := by apply Subtype.ext; simp
    target' := by apply Subtype.ext; simp }
  obtain ⟨A, hA, -, ha₀, ha₁⟩ := exists_smooth_open_curve_with_endpoint_germs S
    hA₀ hA₁ hU₀ hU₁ h0 h1 (mem_univ _) (mem_univ _) γ
  obtain ⟨T, hT, hi, -, ht₀, ht₁⟩ := LinearFramePaths.exists_smooth_invertible_frame_join
    basis hT₀ hT₁ hU₀ hU₁ h0 h1 hsign
  have hTi (s : ℝ) : (T s).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (T s).toLinearMap (hi s)).toContinuousLinearEquiv, rfl⟩
  exact ⟨A, T, hA, hT, hTi,
    fun s => FrameField.isInvertible_shearedBlock (A s) (T s) (hTi s), ha₀, ha₁, ht₀, ht₁⟩

/-- The same construction retains germs at any two ordered scalar parameters. -/
theorem exists_smooth_sheared_frame_join_at (basis : Basis ι ℝ V)
    {p q : ℝ} (hpq : p < q)
    {A₀ A₁ : ℝ → (V →L[ℝ] ℝ)} {T₀ T₁ : ℝ → (V →L[ℝ] V)}
    {U₀ U₁ : Set ℝ}
    (hA₀ : ContDiffOn ℝ ∞ A₀ U₀) (hA₁ : ContDiffOn ℝ ∞ A₁ U₁)
    (hT₀ : ContDiffOn ℝ ∞ T₀ U₀) (hT₁ : ContDiffOn ℝ ∞ T₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hp : p ∈ U₀) (hq : q ∈ U₁)
    (hsign : 0 < (T₀ p).toLinearMap.det * (T₁ q).toLinearMap.det) :
    ∃ A : ℝ → (V →L[ℝ] ℝ), ∃ T : ℝ → (V →L[ℝ] V),
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ T ∧
      (∀ s, (T s).IsInvertible) ∧
      (∀ s, (FrameField.shearedBlock (A s) (T s)).IsInvertible) ∧
      (A =ᶠ[𝓝 p] A₀) ∧ (A =ᶠ[𝓝 q] A₁) ∧
      (T =ᶠ[𝓝 p] T₀) ∧ (T =ᶠ[𝓝 q] T₁) := by
  let ξ : ℝ → ℝ := fun t => p + (q - p) * t
  let ζ : ℝ → ℝ := fun s => (s - p) / (q - p)
  have hn : q - p ≠ 0 := ne_of_gt (sub_pos.mpr hpq)
  have hξ : ContDiff ℝ ∞ ξ := by dsimp [ξ]; fun_prop
  have hζ : ContDiff ℝ ∞ ζ := by dsimp [ζ]; fun_prop
  have hξ0 : ξ 0 = p := by simp [ξ]
  have hξ1 : ξ 1 = q := by simp [ξ]
  have hζp : ζ p = 0 := by simp [ζ]
  have hζq : ζ q = 1 := by simp [ζ, hn]
  have hξζ (s : ℝ) : ξ (ζ s) = s := by
    dsimp [ξ, ζ]
    field_simp
    ring
  have h0 : (0 : ℝ) ∈ ξ ⁻¹' U₀ := by simpa only [mem_preimage, hξ0] using hp
  have h1 : (1 : ℝ) ∈ ξ ⁻¹' U₁ := by simpa only [mem_preimage, hξ1] using hq
  have hsgn : 0 < ((T₀ ∘ ξ) 0).toLinearMap.det * ((T₁ ∘ ξ) 1).toLinearMap.det := by
    simpa only [Function.comp_apply, hξ0, hξ1] using hsign
  obtain ⟨A, T, hA, hT, hi, hb, ha₀, ha₁, ht₀, ht₁⟩ :=
    exists_smooth_sheared_frame_join basis
      (hA₀.comp hξ.contDiffOn (fun _ hs => hs))
      (hA₁.comp hξ.contDiffOn (fun _ hs => hs))
      (hT₀.comp hξ.contDiffOn (fun _ hs => hs))
      (hT₁.comp hξ.contDiffOn (fun _ hs => hs))
      (hU₀.preimage hξ.continuous) (hU₁.preimage hξ.continuous) h0 h1 hsgn
  have hζ0 : Tendsto ζ (𝓝 p) (𝓝 0) := by
    simpa only [hζp] using hζ.continuous.continuousAt.tendsto (x := p)
  have hζ1 : Tendsto ζ (𝓝 q) (𝓝 1) := by
    simpa only [hζq] using hζ.continuous.continuousAt.tendsto (x := q)
  refine ⟨A ∘ ζ, T ∘ ζ, hA.comp hζ, hT.comp hζ, fun s => hi (ζ s),
    fun s => hb (ζ s), ?_, ?_, ?_, ?_⟩
  · filter_upwards [hζ0 ha₀] with s hs
    exact hs.trans (congrArg A₀ (hξζ s))
  · filter_upwards [hζ1 ha₁] with s hs
    exact hs.trans (congrArg A₁ (hξζ s))
  · filter_upwards [hζ0 ht₀] with s hs
    exact hs.trans (congrArg T₀ (hξζ s))
  · filter_upwards [hζ1 ht₁] with s hs
    exact hs.trans (congrArg T₁ (hξζ s))

end Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates
