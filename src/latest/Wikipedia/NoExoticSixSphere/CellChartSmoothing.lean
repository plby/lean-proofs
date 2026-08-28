import Wikipedia.NoExoticSixSphere.CellChartSmoothingInput
import Wikipedia.NoExoticSixSphere.CellChartHomotopy

/-!
# Local smoothing of a continuous map inside a genuine open cell

The original target need not be a manifold. Coordinate approximation on
the larger core and the supported interpolation produce a homotopy
fixed outside the cell and preserving cell membership. Every fiber over
the smaller core is described by one globally smooth coordinate map.
The no-entry estimate ensures that the transition region creates no
additional smaller-core fibers.
-/

noncomputable section

open Set Metric TopologicalSpace
open scoped unitInterval ContDiff

namespace NoExoticSixSphere.CellChart

variable {X D : Type} [TopologicalSpace X] [T2Space X]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

theorem exists_smoothing (n : ℕ) (U : Opens X) (e : (Fin n → ℝ) ≃ₜ U)
    (f : C(D, X)) (r : ℝ) (hr : 0 < r) :
    ∃ f' : C(D, X), ∃ H : f.Homotopy f', ∃ G : D → (Fin n → ℝ),
      ContDiff ℝ ∞ G ∧
      (∀ s z, f z ∉ U → H (s, z) = f z) ∧
      (∀ s z, H (s, z) ∈ U ↔ f z ∈ U) ∧
      ∀ v, ‖v‖ < r → ∀ z, f' z = encode n U e v → G z = v := by
  obtain ⟨β, hβ1, hβsupport, hβ⟩ := exists_core_cutoff n U e f r hr
  obtain ⟨f₀, G, hG, hclose, hmatch⟩ :=
    exists_smooth_coordinate_approximation n U e f (3 * r) r hr
  let g : C(D, (Fin n → ℝ)) := ⟨G, hG.continuous⟩
  have hs : tsupport β ⊆ f ⁻¹' (U : Set X) :=
    fun _ hz ↦ openCore_subset n U e (3 * r) (hβsupport hz)
  refine ⟨updatedMap n U e f g β hβ hs, updateHomotopy n U e f g β hβ hs, G, hG,
    updateHomotopy_of_notMem n U e f g β hβ hs,
    updateHomotopy_mem_iff n U e f g β hβ hs, ?_⟩
  intro v hv z hznew
  have hzU : f z ∈ U := by
    apply (updateHomotopy_mem_iff n U e f g β hβ hs 1 z).mp
    change updatedMap n U e f g β hβ hs z ∈ U
    rw [hznew]
    exact encode_mem n U e v
  let q := coordinates n U e f (⟨z, hzU⟩ : f ⁻¹' (U : Set X))
  have hfactor : updatedMap n U e f g β hβ hs z =
      encode n U e (q + β z • (g z - q)) := by
    change updateHomotopy n U e f g β hβ hs (1, z) =
      encode n U e (coordinates n U e f ⟨z, hzU⟩ + β z •
        (g z - coordinates n U e f ⟨z, hzU⟩))
    simpa only [Set.Icc.coe_one, one_mul] using
      updateHomotopy_coordinates n U e f g β hβ hs 1 z hzU
  have hblend : q + β z • (g z - q) = v :=
    encode_injective n U e (hfactor.symm.trans hznew)
  have hdist : dist (q + β z • (g z - q)) q < r := by
    by_cases hzero : β z = 0
    · rw [hzero, zero_smul, add_zero, dist_self]
      exact hr
    · have hzcore : f z ∈ core n U e (3 * r) :=
        openCore_subset_core n U e (3 * r) (hβsupport (subset_tsupport β hzero))
      have hq : f₀ z = q := encode_injective n U e
        ((hmatch z hzcore).trans (encode_coordinates n U e f ⟨z, hzU⟩).symm)
      have hc : dist (g z) q < r := by
        change dist (G z) q < r
        rw [← hq]
        exact hclose z
      have hn : ‖β z • (g z - q)‖ ≤ ‖g z - q‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβ z).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (hβ z).2
      rw [dist_eq_norm] at hc
      simpa only [dist_eq_norm, add_sub_cancel_left] using hn.trans_lt hc
  rw [hblend] at hdist
  have hqnorm : ‖q‖ < 2 * r := by
    have hc : ‖q - v‖ < r := by
      rw [← dist_eq_norm, dist_comm]
      exact hdist
    have ht := norm_add_le (q - v) v
    rw [sub_add_cancel] at ht
    linarith
  have hzcore : f z ∈ core n U e (2 * r) := by
    rw [← encode_coordinates n U e f ⟨z, hzU⟩]
    exact (encode_mem_core_iff n U e (2 * r) q).mpr hqnorm.le
  have hgnew := updatedMap_of_one n U e f g β hβ hs z hzU (hβ1 hzcore)
  exact encode_injective n U e (hgnew.symm.trans hznew)

end NoExoticSixSphere.CellChart
