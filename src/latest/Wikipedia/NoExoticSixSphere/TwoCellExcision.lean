import Wikipedia.NoExoticSixSphere.CubicalCellSmoothing
import Wikipedia.NoExoticSixSphere.CellExcisionSmoothCylinder

/-!
# Cell-point excision for the original arbitrary continuous cubical map

Both smooth coordinate descriptions are now constructed. The strict
dimension inequality separates chosen cell fibers, and the continuous
graph removes one fiber while the moving bottom avoids the other.
The preliminary homotopy preserves membership in both cells and fixes
their complement. Keeping it explicit also retains the endpoint faces
needed when this construction is applied to a homotopy between maps.

This is the geometric cell-point step, not yet the full homotopy-excision
theorem: punctured-cell retractions and original relative-map comparison
still have to be supplied in the intended James-space application.
-/

noncomputable section

open Set Metric Module TopologicalSpace
open scoped unitInterval ContDiff

namespace NoExoticSixSphere.TwoCellExcision

open CubicalCellSmoothing

variable {X : Type} [TopologicalSpace X] [T2Space X]

theorem exists_excision (a b d : ℕ) (U V : Opens X)
    (eU : (Fin a → ℝ) ≃ₜ U) (eV : (Fin b → ℝ) ≃ₜ V)
    (hUV : Disjoint (U : Set X) (V : Set X)) (hdim : d + 2 < a + b)
    (f : C(I × Parameters d, X)) (S : Set (Parameters d)) (hS : IsClosed S)
    (hside : ∀ t p, p ∈ S → f (t, p) ∉ V)
    (htop : ∀ p, f (1, p) ∉ V) (hbottom : ∀ p, f (0, p) ∉ U) :
    ∃ f₁ : C(I × Parameters d, X), ∃ K : f.Homotopy f₁,
      (∀ s z, f z ∉ U → f z ∉ V → K (s, z) = f z) ∧
      (∀ s z, K (s, z) ∈ U ↔ f z ∈ U) ∧
      (∀ s z, K (s, z) ∈ V ↔ f z ∈ V) ∧
      ∃ u : Fin a → ℝ, ∃ v : Fin b → ℝ, ‖u‖ < 1 ∧ ‖v‖ < 1 ∧
        ∃ g : C(I × Parameters d, X), ∃ H : f₁.Homotopy g,
          (∀ s p, H (s, (1, p)) = f₁ (1, p)) ∧
          (∀ s t p, p ∈ S → H (s, (t, p)) = f₁ (t, p)) ∧
          (∀ s p, H (s, (0, p)) ≠ CellChart.encode a U eU u) ∧
          ∀ z, g z ≠ CellChart.encode b V eV v := by
  obtain ⟨f₁, K, F, G, hF, hG, hfix, hU, hV, hFU, hGV⟩ :=
    exists_two_cell_smoothing a b d U V eU eV hUV f 1 (by norm_num)
  have hU₁ (z : I × Parameters d) : f₁ z ∈ U ↔ f z ∈ U := by
    have h := hU 1 z
    rwa [K.apply_one] at h
  have hV₁ (z : I × Parameters d) : f₁ z ∈ V ↔ f z ∈ V := by
    have h := hV 1 z
    rwa [K.apply_one] at h
  have hdim' : finrank ℝ (Fin d → ℝ) + 2 <
      finrank ℝ (Fin a → ℝ) + finrank ℝ (Fin b → ℝ) := by simpa using hdim
  have hFA : ∀ u ∈ ball (0 : Fin a → ℝ) 1, ∀ z : I × Parameters d,
      f₁ z = CellChart.encode a U eU u →
        ((z.1 : ℝ), parameterEmbedding d z.2) ∈ (⊤ : Opens (ℝ × (Fin d → ℝ))) ∧
          F ((z.1 : ℝ), parameterEmbedding d z.2) = u := by
    intro u hu z hz
    exact ⟨mem_univ _, hFU u (mem_ball_zero_iff.mp hu) z hz⟩
  have hGB : ∀ v ∈ ball (0 : Fin b → ℝ) 1, ∀ z : I × Parameters d,
      f₁ z = CellChart.encode b V eV v →
        ((z.1 : ℝ), parameterEmbedding d z.2) ∈ (⊤ : Opens (ℝ × (Fin d → ℝ))) ∧
          G ((z.1 : ℝ), parameterEmbedding d z.2) = v := by
    intro v hv z hz
    exact ⟨mem_univ _, hGV v (mem_ball_zero_iff.mp hv) z hz⟩
  have hside₁ : ∀ v ∈ ball (0 : Fin b → ℝ) 1, ∀ t p, p ∈ S →
      f₁ (t, p) ≠ CellChart.encode b V eV v := by
    intro v _ t p hp he
    have hm : f₁ (t, p) ∈ V := he.symm ▸ CellChart.encode_mem b V eV v
    exact hside t p hp ((hV₁ (t, p)).mp hm)
  have htop₁ : ∀ v ∈ ball (0 : Fin b → ℝ) 1, ∀ p,
      f₁ (1, p) ≠ CellChart.encode b V eV v := by
    intro v _ p he
    have hm : f₁ (1, p) ∈ V := he.symm ▸ CellChart.encode_mem b V eV v
    exact htop p ((hV₁ (1, p)).mp hm)
  have hbottom₁ : ∀ u ∈ ball (0 : Fin a → ℝ) 1, ∀ p,
      f₁ (0, p) ≠ CellChart.encode a U eU u := by
    intro u _ p he
    have hm : f₁ (0, p) ∈ U := he.symm ▸ CellChart.encode_mem a U eU u
    exact hbottom p ((hU₁ (0, p)).mp hm)
  obtain ⟨u, hu, v, hv, g, H, hHt, hHs, hHb, hg⟩ :=
    CellExcisionSmoothCylinder.exists_excision_homotopy f₁ (parameterEmbedding d)
      (CellChart.encode a U eU) (CellChart.encode b V eV) F G ⊤ ⊤
      (hF.of_le (by simp)).contDiffOn (hG.of_le (by simp)).contDiffOn hdim'
      (ball 0 1) (ball 0 1) isOpen_ball isOpen_ball ⟨0, by simp⟩ ⟨0, by simp⟩
      hFA hGB S hS hside₁ htop₁ hbottom₁
  exact ⟨f₁, K, hfix, hU, hV, u, v, mem_ball_zero_iff.mp hu, mem_ball_zero_iff.mp hv,
    g, H, hHt, hHs, hHb, hg⟩

end NoExoticSixSphere.TwoCellExcision
