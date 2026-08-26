import ErdosProblems.Erdos1148.ModularRightTranslation
import ErdosProblems.Erdos1148.ForwardHaarTube
import Mathlib.Analysis.Matrix.Normed

/-! # Uniform small right thickenings inside a nonempty modular open set -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped MatrixGroups Topology Matrix.Norms.Elementwise

theorem exists_entryCloseOne_subset_nhds_one {W : Set SL(2, ℝ)} (hW : W ∈ 𝓝 (1 : SL(2, ℝ))) :
    ∃ η : ℝ, 0 < η ∧ {g : SL(2, ℝ) | EntryCloseOne η g} ⊆ W := by
  have hi : Topology.IsInducing
      (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.isInducing
  rw [hi.nhds_eq_comap (1 : SL(2, ℝ))] at hW
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.mp hW
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro g hg
  apply hVW
  apply hball
  change dist (g : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) < r
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hr)
  apply (Matrix.norm_le_iff (half_pos hr).le).mpr
  intro i j
  simpa only [Matrix.sub_apply, Real.norm_eq_abs] using
    (entryCloseOne_iff_entries (r / 2) g).mp hg i j

theorem exists_open_modular_right_thickening {U : Set ModularOrbitSpace}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (V : Set ModularOrbitSpace) (η : ℝ), IsOpen V ∧ V.Nonempty ∧ 0 < η ∧
      ∀ x ∈ V, ∀ u ∈ forwardHaarTube η 0, modularRightTranslate u x ∈ U := by
  obtain ⟨x, hx⟩ := hne
  have hpre : (fun p : SL(2, ℝ) × ModularOrbitSpace => modularRightTranslate p.1 p.2) ⁻¹' U ∈
      𝓝 ((1 : SL(2, ℝ)), x) := by
    apply continuous_modularRightTranslate_joint.continuousAt.preimage_mem_nhds
    simpa only [modularRightTranslate_one, id_eq] using hU.mem_nhds hx
  rw [nhds_prod_eq] at hpre
  obtain ⟨W, hW, V, hV, hWV⟩ := Filter.mem_prod_iff.mp hpre
  obtain ⟨V', hV'V, hV'open, hxV'⟩ := mem_nhds_iff.mp hV
  obtain ⟨η, hη, hηW⟩ := exists_entryCloseOne_subset_nhds_one hW
  refine ⟨V', η, hV'open, ⟨x, hxV'⟩, hη, ?_⟩
  intro y hy u hu
  exact hWV (show (u, y) ∈ W ×ˢ V from ⟨hηW hu.1, hV'V hy⟩)

end Erdos1148.DukeArithmetic
