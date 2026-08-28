import Wikipedia.NoExoticSixSphere.CellChartSmoothing

/-!
# Simultaneous smoothing in two disjoint actual open cells

The two supported smoothings are composed on the original target space.
Cell membership is preserved throughout. The second smoothing leaves
the first cell's selected fibers unchanged, so both sets of fibers have
globally smooth coordinate descriptions at the same final map.
-/

noncomputable section

open Set TopologicalSpace
open scoped unitInterval ContDiff

namespace NoExoticSixSphere.CellChart

section Homotopy

variable {X D : Type} [TopologicalSpace X] [TopologicalSpace D]
  {f g : C(D, X)} (H : f.Homotopy g) (U : Set X)
  (hfix : ∀ s z, f z ∉ U → H (s, z) = f z)
  (hmem : ∀ s z, H (s, z) ∈ U ↔ f z ∈ U)

include hfix hmem

theorem homotopy_mem_disjoint_iff (V : Set X) (hd : Disjoint V U) (s : I) (z : D) :
    H (s, z) ∈ V ↔ f z ∈ V := by
  by_cases hz : f z ∈ U
  · have hH := (hmem s z).mpr hz
    exact iff_of_false (fun h ↦ Set.disjoint_left.mp hd h hH)
      (fun h ↦ Set.disjoint_left.mp hd h hz)
  · rw [hfix s z hz]

theorem original_eq_of_homotopy_eq (s : I) (z : D) {a : X}
    (ha : a ∉ U) (he : H (s, z) = a) : f z = a := by
  have hz : f z ∉ U := by
    intro hz
    have hH := (hmem s z).mpr hz
    rw [he] at hH
    exact ha hH
  rwa [hfix s z hz] at he

end Homotopy

variable {X D : Type} [TopologicalSpace X] [T2Space X]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

theorem exists_two_cell_smoothing (a b : ℕ) (U V : Opens X)
    (eU : (Fin a → ℝ) ≃ₜ U) (eV : (Fin b → ℝ) ≃ₜ V)
    (hd : Disjoint (U : Set X) (V : Set X)) (f : C(D, X)) (r : ℝ) (hr : 0 < r) :
    ∃ f' : C(D, X), ∃ H : f.Homotopy f',
      ∃ F : D → (Fin a → ℝ), ∃ G : D → (Fin b → ℝ),
      ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ G ∧
      (∀ s z, f z ∉ U → f z ∉ V → H (s, z) = f z) ∧
      (∀ s z, H (s, z) ∈ U ↔ f z ∈ U) ∧
      (∀ s z, H (s, z) ∈ V ↔ f z ∈ V) ∧
      (∀ v, ‖v‖ < r → ∀ z, f' z = encode a U eU v → F z = v) ∧
      (∀ v, ‖v‖ < r → ∀ z, f' z = encode b V eV v → G z = v) := by
  obtain ⟨f₁, H₁, F, hF, hfix₁, hmem₁, hfiber₁⟩ := exists_smoothing a U eU f r hr
  obtain ⟨f₂, H₂, G, hG, hfix₂, hmem₂, hfiber₂⟩ := exists_smoothing b V eV f₁ r hr
  have hV₁ := homotopy_mem_disjoint_iff H₁ (U : Set X) hfix₁ hmem₁ (V : Set X) hd.symm
  have hU₂ := homotopy_mem_disjoint_iff H₂ (V : Set X) hfix₂ hmem₂ (U : Set X) hd
  refine ⟨f₂, H₁.trans H₂, F, G, hF, hG, ?_, ?_, ?_, ?_, hfiber₂⟩
  · intro s z hzU hzV
    have hf₁ : f₁ z = f z := by simpa only [H₁.apply_one] using hfix₁ 1 z hzU
    have hzV₁ : f₁ z ∉ V := by rwa [hf₁]
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hfix₁ _ z hzU
    · exact (hfix₂ _ z hzV₁).trans hf₁
  · intro s z
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hmem₁ _ z
    · have h1end := hmem₁ 1 z
      rw [H₁.apply_one] at h1end
      change (f₁ z ∈ (U : Set X) ↔ f z ∈ (U : Set X)) at h1end
      exact (hU₂ _ z).trans h1end
  · intro s z
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hV₁ _ z
    · have h1end := hV₁ 1 z
      rw [H₁.apply_one] at h1end
      change (f₁ z ∈ V ↔ f z ∈ V) at h1end
      exact (hmem₂ _ z).trans h1end
  · intro v hv z hz
    have hnot : encode a U eU v ∉ V :=
      fun h ↦ Set.disjoint_left.mp hd (encode_mem a U eU v) h
    have he : f₁ z = encode a U eU v := original_eq_of_homotopy_eq
      H₂ (V : Set X) hfix₂ hmem₂ 1 z hnot (by simpa only [H₂.apply_one] using hz)
    exact hfiber₁ v hv z he

end NoExoticSixSphere.CellChart
