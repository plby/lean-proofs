import Wikipedia.NoExoticSixSphere.DiskCollarSmoothing

/-!
# Relative disk smoothing with an arbitrary positive collar width

The constructed geometric collar need not start at radius one half.
Two arbitrary nested radii suffice: the ambient extension is installed
before the protected outer radius, so smoothing fixes that entire outer
annulus and retains the prescribed open target condition in the interior.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

namespace DiskCollarAmbientExtension

theorem exists_extension_of_radii {p : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ τ : ℝ) (hρ : 0 < ρ) (hρτ : ρ < τ)
    (G : C(Disk (E := Vector (p + 1)), F)) (H : C(Vector (p + 1), F))
    (hHG : ∀ x : Disk (E := Vector (p + 1)), ρ ≤ ‖x.val‖ → H x.val = G x) :
    ∃ B : C(Vector (p + 1), F),
      (∀ x : Disk (E := Vector (p + 1)), B x.val = G x) ∧
      ∀ x, τ ≤ ‖x‖ → B x = H x := by
  obtain ⟨A, hA⟩ := G.exists_restrict_eq isClosed_closedBall
  have hAG (x : Disk (E := Vector (p + 1))) : A x.val = G x :=
    ContinuousMap.congr_fun hA x
  let χ : ContDiffBump (0 : Vector (p + 1)) := {
    rIn := ρ
    rOut := τ
    rIn_pos := hρ
    rIn_lt_rOut := hρτ
  }
  let B : C(Vector (p + 1), F) :=
    ⟨fun x ↦ χ x • A x + (1 - χ x) • H x,
      (χ.continuous.smul A.continuous).add
        ((continuous_const.sub χ.continuous).smul H.continuous)⟩
  refine ⟨B, ?_, ?_⟩
  · intro x
    change χ x.val • A x.val + (1 - χ x.val) • H x.val = G x
    by_cases hx : ‖x.val‖ ≤ ρ
    · have hχ : χ x.val = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
      rw [hχ, one_smul, sub_self, zero_smul, add_zero, hAG]
    · rw [hAG, hHG x (le_of_not_ge hx), ← add_smul, add_sub_cancel, one_smul]
  · intro x hx
    have hχ : χ x = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
    change χ x • A x + (1 - χ x) • H x = H x
    rw [hχ, zero_smul, sub_zero, one_smul, zero_add]

end DiskCollarAmbientExtension

namespace EuclideanEmbedding

variable {n p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] [Nonempty M] (e : EuclideanEmbedding n M)

theorem exists_smooth_disk_with_collar_of_radii
    (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ1 : σ < 1)
    (G : C(Disk (E := Vector (p + 1)), M))
    (H : C(Vector (p + 1), Vector e.ambientDimension)) (hH : ContDiff ℝ ∞ H)
    (hHG : ∀ x : Disk (E := Vector (p + 1)), ρ ≤ ‖x.val‖ → H x.val = e.toFun (G x))
    (V : Set M) (hV : IsOpen V) (hGV : ∀ x, ‖x.val‖ < 1 → G x ∈ V) :
    ∃ g : Vector (p + 1) → M,
      (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 (p + 1)) (𝓡 n) ∞ g x) ∧
      (∀ x : Disk (E := Vector (p + 1)), σ ≤ ‖x.val‖ → g x.val = G x) ∧
      ∀ x ∈ ball 0 1, g x ∈ V := by
  let A : C(Disk (E := Vector (p + 1)), Vector e.ambientDimension) :=
    ⟨e.toFun ∘ G, e.smooth.continuous.comp G.continuous⟩
  let τ := (ρ + σ) / 2
  have hρτ : ρ < τ := by dsimp only [τ]; linarith
  have hτσ : τ < σ := by dsimp only [τ]; linarith
  obtain ⟨B, hBG, hBH⟩ :=
    DiskCollarAmbientExtension.exists_extension_of_radii ρ τ hρ hρτ A H hHG
  let S : Set (Vector (p + 1)) := {x | σ ≤ ‖x‖}
  let U : Set (Vector (p + 1)) := {x | τ < ‖x‖}
  have hS : IsClosed S := isClosed_le continuous_const continuous_norm
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hSU : S ⊆ U := fun _ hx ↦ hτσ.trans_le hx
  have hBs : ContDiffOn ℝ ∞ B U := hH.contDiffOn.congr (fun x hx ↦ hBH x hx.le)
  obtain ⟨g, hgs, hgeq, hgV⟩ := e.exists_smooth_near_compact_relative
    (isCompact_closedBall (0 : Vector (p + 1)) 1)
    (isCompact_closedBall (0 : Vector (p + 1)) σ)
    (closedBall_subset_closedBall hσ1.le) G B hBG hS (hU.mem_nhdsSet.mpr hSU) hBs
    V hV (fun x hx ↦ hGV x ((mem_closedBall_zero_iff.mp hx).trans_lt hσ1))
  refine ⟨g, hgs, hgeq, ?_⟩
  intro x hx
  by_cases hinner : ‖x‖ ≤ σ
  · exact hgV x (mem_closedBall_zero_iff.mpr hinner)
  · rw [hgeq ⟨x, ball_subset_closedBall hx⟩ (le_of_not_ge hinner)]
    exact hGV _ (mem_ball_zero_iff.mp hx)

end EuclideanEmbedding
end NoExoticSixSphere
