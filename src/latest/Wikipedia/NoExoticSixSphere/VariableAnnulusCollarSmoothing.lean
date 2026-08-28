import Wikipedia.NoExoticSixSphere.AnnulusCollarSmoothing

/-!
# Relative annulus smoothing with arbitrary collar widths

The two geometric collars need not have fixed rational widths. Nested
radii suffice to install their ambient extensions, protect narrower
collars during smoothing, and retain the open target condition throughout
the interior. Neither boundary value nor collar parameter is changed.
-/

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

open GLOrthonormalization

namespace SphereAnnulus

theorem exists_ambient_extension_of_radii {p : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (τ₀ ρ₀ ρ₁ τ₁ : ℝ) (hτ₀ : 0 < τ₀) (hτ₀ρ₀ : τ₀ < ρ₀)
    (hρ₀ρ₁ : ρ₀ < ρ₁) (hρ₁τ₁ : ρ₁ < τ₁)
    (G : C(domain p, F)) (H₀ H₁ : C(Vector (p + 1), F))
    (h₀ : ∀ x : domain p, ‖x.val‖ ≤ ρ₀ → H₀ x.val = G x)
    (h₁ : ∀ x : domain p, ρ₁ ≤ ‖x.val‖ → H₁ x.val = G x) :
    ∃ B : C(Vector (p + 1), F), (∀ x : domain p, B x.val = G x) ∧
      (∀ x, ‖x‖ ≤ τ₀ → B x = H₀ x) ∧
      ∀ x, τ₁ ≤ ‖x‖ → B x = H₁ x := by
  obtain ⟨A, hA⟩ := G.exists_restrict_eq (isClosed_domain p)
  have hAG (x : domain p) : A x.val = G x := ContinuousMap.congr_fun hA x
  let χ₀ : ContDiffBump (0 : Vector (p + 1)) := {
    rIn := τ₀
    rOut := ρ₀
    rIn_pos := hτ₀
    rIn_lt_rOut := hτ₀ρ₀ }
  let χ₁ : ContDiffBump (0 : Vector (p + 1)) := {
    rIn := ρ₁
    rOut := τ₁
    rIn_pos := hτ₀.trans (hτ₀ρ₀.trans hρ₀ρ₁)
    rIn_lt_rOut := hρ₁τ₁ }
  let T : C(Vector (p + 1), F) :=
    ⟨fun x ↦ χ₁ x • A x + (1 - χ₁ x) • H₁ x,
      (χ₁.continuous.smul A.continuous).add
        ((continuous_const.sub χ₁.continuous).smul H₁.continuous)⟩
  let B : C(Vector (p + 1), F) :=
    ⟨fun x ↦ χ₀ x • H₀ x + (1 - χ₀ x) • T x,
      (χ₀.continuous.smul H₀.continuous).add
        ((continuous_const.sub χ₀.continuous).smul T.continuous)⟩
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x
    change χ₀ x.val • H₀ x.val +
      (1 - χ₀ x.val) • (χ₁ x.val • A x.val + (1 - χ₁ x.val) • H₁ x.val) = G x
    by_cases hx : ‖x.val‖ ≤ ρ₀
    · have hχ₁ : χ₁ x.val = 1 := χ₁.one_of_mem_closedBall
        (mem_closedBall_zero_iff.mpr (hx.trans hρ₀ρ₁.le))
      rw [hχ₁, one_smul, sub_self, zero_smul, add_zero, hAG, h₀ x hx,
        ← add_smul, add_sub_cancel, one_smul]
    · have hχ₀ : χ₀ x.val = 0 := χ₀.zero_of_le_dist (by
        change ρ₀ ≤ dist x.val 0
        rw [dist_zero_right]
        exact (lt_of_not_ge hx).le)
      rw [hχ₀, zero_smul, sub_zero, one_smul, zero_add]
      by_cases hy : ρ₁ ≤ ‖x.val‖
      · rw [hAG, h₁ x hy, ← add_smul, add_sub_cancel, one_smul]
      · have hχ₁ : χ₁ x.val = 1 := χ₁.one_of_mem_closedBall
          (mem_closedBall_zero_iff.mpr (le_of_not_ge hy))
        rw [hχ₁, one_smul, sub_self, zero_smul, add_zero, hAG]
  · intro x hx
    have hχ₀ : χ₀ x = 1 := χ₀.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
    change χ₀ x • H₀ x + (1 - χ₀ x) • T x = H₀ x
    rw [hχ₀, one_smul, sub_self, zero_smul, add_zero]
  · intro x hx
    have hχ₀ : χ₀ x = 0 := χ₀.zero_of_le_dist (by
      change ρ₀ ≤ dist x 0
      rw [dist_zero_right]
      exact (hρ₀ρ₁.trans hρ₁τ₁).le.trans hx)
    have hχ₁ : χ₁ x = 0 := χ₁.zero_of_le_dist (by
      simpa only [dist_zero_right] using hx)
    change χ₀ x • H₀ x + (1 - χ₀ x) •
      (χ₁ x • A x + (1 - χ₁ x) • H₁ x) = H₁ x
    rw [hχ₀, zero_smul, sub_zero, one_smul, zero_add,
      hχ₁, zero_smul, sub_zero, one_smul, zero_add]

end SphereAnnulus

namespace EuclideanEmbedding

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Vector n) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
  (e : EuclideanEmbedding n M)

theorem exists_smooth_annulus_with_collars_of_radii
    (σ₀ ρ₀ ρ₁ σ₁ : ℝ) (hσ₀ : 1 < σ₀) (hσ₀ρ₀ : σ₀ < ρ₀)
    (hρ₀ρ₁ : ρ₀ < ρ₁) (hρ₁σ₁ : ρ₁ < σ₁) (hσ₁ : σ₁ < 2)
    (G : C(SphereAnnulus.domain p, M))
    (H₀ H₁ : C(Vector (p + 1), Vector e.ambientDimension))
    (hH₀ : ContDiff ℝ ∞ H₀) (hH₁ : ContDiff ℝ ∞ H₁)
    (h₀ : ∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ ρ₀ → H₀ x.val = e.toFun (G x))
    (h₁ : ∀ x : SphereAnnulus.domain p, ρ₁ ≤ ‖x.val‖ → H₁ x.val = e.toFun (G x))
    (V : Set M) (hV : IsOpen V)
    (hGV : ∀ x : SphereAnnulus.domain p, 1 < ‖x.val‖ → ‖x.val‖ < 2 → G x ∈ V) :
    ∃ g : Vector (p + 1) → M,
      (∀ x ∈ SphereAnnulus.domain p, ContMDiffAt (𝓡 (p + 1)) (𝓡 n) ∞ g x) ∧
      (∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ σ₀ ∨ σ₁ ≤ ‖x.val‖ →
        g x.val = G x) ∧
      ∀ x : Vector (p + 1), 1 < ‖x‖ → ‖x‖ < 2 → g x ∈ V := by
  let A : C(SphereAnnulus.domain p, Vector e.ambientDimension) :=
    ⟨e.toFun ∘ G, e.smooth.continuous.comp G.continuous⟩
  let τ₀ := (σ₀ + ρ₀) / 2
  let τ₁ := (ρ₁ + σ₁) / 2
  have hσ₀τ₀ : σ₀ < τ₀ := by dsimp only [τ₀]; linarith
  have hτ₀ρ₀ : τ₀ < ρ₀ := by dsimp only [τ₀]; linarith
  have hρ₁τ₁ : ρ₁ < τ₁ := by dsimp only [τ₁]; linarith
  have hτ₁σ₁ : τ₁ < σ₁ := by dsimp only [τ₁]; linarith
  obtain ⟨B, hBG, hB₀, hB₁⟩ := SphereAnnulus.exists_ambient_extension_of_radii
    τ₀ ρ₀ ρ₁ τ₁ (by linarith) hτ₀ρ₀ hρ₀ρ₁ hρ₁τ₁ A H₀ H₁ h₀ h₁
  let L : Set (Vector (p + 1)) := {x | σ₀ ≤ ‖x‖ ∧ ‖x‖ ≤ σ₁}
  let S : Set (Vector (p + 1)) := {x | ‖x‖ ≤ σ₀ ∨ σ₁ ≤ ‖x‖}
  let U : Set (Vector (p + 1)) := {x | ‖x‖ < τ₀ ∨ τ₁ < ‖x‖}
  have hL : IsCompact L :=
    (isCompact_closedBall (0 : Vector (p + 1)) σ₁).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      (fun _ hx ↦ mem_closedBall_zero_iff.mpr hx.2)
  have hLK : L ⊆ SphereAnnulus.domain p :=
    fun _ hx ↦ ⟨hσ₀.le.trans hx.1, hx.2.trans hσ₁.le⟩
  have hS : IsClosed S := (isClosed_le continuous_norm continuous_const).union
    (isClosed_le continuous_const continuous_norm)
  have hU : IsOpen U := (isOpen_lt continuous_norm continuous_const).union
    (isOpen_lt continuous_const continuous_norm)
  have hSU : S ⊆ U := fun _ hx ↦
    hx.elim (fun h ↦ Or.inl (h.trans_lt hσ₀τ₀)) (fun h ↦ Or.inr (hτ₁σ₁.trans_le h))
  have hBs : ContDiffOn ℝ ∞ B U := by
    intro x hx
    rcases hx with hx | hx
    · have he : (B : Vector (p + 1) → Vector e.ambientDimension) =ᶠ[𝓝 x] H₀ := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
        exact hB₀ y hy.le
      exact (hH₀.contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
    · have he : (B : Vector (p + 1) → Vector e.ambientDimension) =ᶠ[𝓝 x] H₁ := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
        exact hB₁ y hy.le
      exact (hH₁.contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
  obtain ⟨g, hgs, hgeq, hgV⟩ := e.exists_smooth_near_compact_relative
    (SphereAnnulus.isCompact_domain p) hL hLK G B hBG hS (hU.mem_nhdsSet.mpr hSU) hBs
    V hV (fun x hx ↦ hGV x (hσ₀.trans_le hx.1) (hx.2.trans_lt hσ₁))
  refine ⟨g, hgs, hgeq, ?_⟩
  intro x hx₀ hx₁
  have hx : x ∈ SphereAnnulus.domain p := ⟨hx₀.le, hx₁.le⟩
  by_cases hcore : x ∈ L
  · exact hgV x hcore
  · have hprotected : x ∈ S := by
      by_contra hn
      change ¬ (‖x‖ ≤ σ₀ ∨ σ₁ ≤ ‖x‖) at hn
      push Not at hn
      exact hcore ⟨hn.1.le, hn.2.le⟩
    rw [hgeq ⟨x, hx⟩ hprotected]
    exact hGV ⟨x, hx⟩ hx₀ hx₁

end EuclideanEmbedding
end NoExoticSixSphere
