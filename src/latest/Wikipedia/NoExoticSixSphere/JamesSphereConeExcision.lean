import Wikipedia.NoExoticSixSphere.JamesSphereConeAttachments
import Wikipedia.NoExoticSixSphere.TwoCellExcision

/-!
# Cell-point excision on the actual two-cell James cone

The open-cell hypotheses and dimensions are discharged for the concrete
cone model. Face conditions are expressed using the original embedded
James stage and cone disk. The preliminary smoothing preserves both
subspaces and fixes their intersection. The graph homotopy then avoids
the selected points with its precise endpoint and moving-bottom controls.

This is the geometric step. `JamesSphereCubicalCompression` corrects
the moving bottom, and `JamesSphereConeFiberComparison` assembles the
resulting comparison on the actual finite-pair homotopy fibers.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

open CubicalCellSmoothing

theorem firstOpenCell_eq_attached (n : ℕ) (hn : 0 < n) :
    (firstOpenCell n hn : Set (Space n)) =
      (CellAttachmentChart.openCell (first_isPushout n hn) : Set (Space n)) := rfl

theorem mem_cone_iff_not_first (n : ℕ) (hn : 0 < n) (z : Space n) :
    z ∈ Set.range (cone n) ↔ z ∉ firstOpenCell n hn :=
  CellAttachmentChart.mem_base_iff_not_mem_openCell (first_isPushout n hn) z

theorem mem_base_iff_not_second (n : ℕ) (z : Space n) :
    z ∈ Set.range (base n) ↔ z ∉ secondOpenCell n :=
  CellAttachmentChart.mem_base_iff_not_mem_openCell (isPushout n) z

theorem exists_point_excision (n d : ℕ) (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 2)
    (f : C(I × Parameters d, Space n)) (S : Set (Parameters d)) (hS : IsClosed S)
    (hside : ∀ t p, p ∈ S → f (t, p) ∈ Set.range (base n))
    (htop : ∀ p, f (1, p) ∈ Set.range (base n))
    (hbottom : ∀ p, f (0, p) ∈ Set.range (cone n)) :
    ∃ f₁ : C(I × Parameters d, Space n), ∃ K : f.Homotopy f₁,
      (∀ s z, f z ∈ Set.range (base n) → f z ∈ Set.range (cone n) → K (s, z) = f z) ∧
      (∀ s z, K (s, z) ∈ Set.range (base n) ↔ f z ∈ Set.range (base n)) ∧
      (∀ s z, K (s, z) ∈ Set.range (cone n) ↔ f z ∈ Set.range (cone n)) ∧
      ∃ u : Fin (2 * n) → ℝ, ∃ v : Fin (n + 1) → ℝ, ‖u‖ < 1 ∧ ‖v‖ < 1 ∧
        ∃ g : C(I × Parameters d, Space n), ∃ H : f₁.Homotopy g,
          (∀ s p, H (s, (1, p)) = f₁ (1, p)) ∧
          (∀ s t p, p ∈ S → H (s, (t, p)) = f₁ (t, p)) ∧
          (∀ s p, H (s, (0, p)) ≠ (firstChart n (by omega) u).val) ∧
          ∀ z, g z ≠ (secondChart n v).val := by
  have hn0 : 0 < n := by omega
  have hdim : d + 2 < 2 * n + (n + 1) := by omega
  obtain ⟨f₁, K, hfix, hU, hV, u, v, hu, hv, g, H, htopH, hsideH, hbottomH, hg⟩ :=
    TwoCellExcision.exists_excision (2 * n) (n + 1) d (firstOpenCell n hn0) (secondOpenCell n)
      (firstChart n hn0) (secondChart n) (cells_disjoint n hn0) hdim f S hS
      (fun t p hp ↦ (mem_base_iff_not_second n _).mp (hside t p hp))
      (fun p ↦ (mem_base_iff_not_second n _).mp (htop p))
      (fun p ↦ (mem_cone_iff_not_first n hn0 _).mp (hbottom p))
  refine ⟨f₁, K, ?_, ?_, ?_, u, v, hu, hv, g, H, htopH, hsideH, hbottomH, hg⟩
  · intro s z hb hc
    exact hfix s z ((mem_cone_iff_not_first n hn0 _).mp hc)
      ((mem_base_iff_not_second n _).mp hb)
  · intro s z
    rw [mem_base_iff_not_second, mem_base_iff_not_second]
    exact not_congr (hV s z)
  · intro s z
    rw [mem_cone_iff_not_first n hn0, mem_cone_iff_not_first n hn0]
    exact not_congr (hU s z)

end NoExoticSixSphere.JamesSphere.SecondStageCone
