import ErdosProblems.Erdos1148.ForwardHaarTube
import ErdosProblems.Erdos1148.CompactLiftThickening

/-! # Algebra and compactness of forward Bowen tubes -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma isClosed_forwardHaarTube (η S : ℝ) : IsClosed (forwardHaarTube η S) :=
  (isClosed_entryCloseOne η).inter
    (isClosed_le (continuous_realMatrixEntry 1 0).abs continuous_const)

lemma one_mem_forwardHaarTube {η S : ℝ} (hη : 0 ≤ η) : (1 : SL(2, ℝ)) ∈ forwardHaarTube η S := by
  simp [forwardHaarTube, EntryForwardBowenTube, EntryCloseOne, hη,
    mul_nonneg hη (Real.exp_pos (-S)).le]

lemma forwardHaarTube_mono {η δ S : ℝ} (hηδ : η ≤ δ) :
    forwardHaarTube η S ⊆ forwardHaarTube δ S := by
  intro g hg
  exact ⟨entryCloseOne_mono hg.1 hηδ,
    hg.2.trans (mul_le_mul_of_nonneg_right hηδ (Real.exp_pos _).le)⟩

lemma forwardHaarTube_inv {η S : ℝ} (hS : 0 ≤ S) {g : SL(2, ℝ)}
    (hg : g ∈ forwardHaarTube η S) : g⁻¹ ∈ forwardHaarTube η S := by
  apply (entryForwardBowenTube_iff_flow_closeness hS g⁻¹).mpr
  intro t ht
  have h := entryCloseOne_inv ((entryForwardBowenTube_iff_flow_closeness hS g).mp hg t ht)
  have heq : (diagonalFlow (-t) * g * diagonalFlow t)⁻¹ =
      diagonalFlow (-t) * g⁻¹ * diagonalFlow t := by rw [diagonalFlow_neg]; group
  rwa [heq] at h

lemma forwardHaarTube_mul {η δ S : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hS : 0 ≤ S)
    {g h : SL(2, ℝ)} (hg : g ∈ forwardHaarTube η S) (hh : h ∈ forwardHaarTube δ S) :
    g * h ∈ forwardHaarTube (η + δ + 2 * η * δ) S := by
  apply (entryForwardBowenTube_iff_flow_closeness hS (g * h)).mpr
  intro t ht
  have hp := entryCloseOne_mul hη hδ
    ((entryForwardBowenTube_iff_flow_closeness hS g).mp hg t ht)
    ((entryForwardBowenTube_iff_flow_closeness hS h).mp hh t ht)
  have heq : (diagonalFlow (-t) * g * diagonalFlow t) *
      (diagonalFlow (-t) * h * diagonalFlow t) =
      diagonalFlow (-t) * (g * h) * diagonalFlow t := by rw [diagonalFlow_neg]; group
  rwa [heq] at hp

lemma forwardHaarTube_liftForwardClose {η S : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1) (hS : 0 ≤ S) :
    LiftForwardClose (4 * η) S (forwardHaarTube η S) := by
  intro g hg h hh t ht
  have hp := forwardHaarTube_mul hη hη hS (forwardHaarTube_inv hS hg) hh
  have hbound : η + η + 2 * η * η ≤ 4 * η := by
    nlinarith [mul_nonneg hη (sub_nonneg.mpr hηone)]
  have hflow := (entryForwardBowenTube_iff_flow_closeness hS (g⁻¹ * h)).mp
    (forwardHaarTube_mono hbound hp) t ht
  have heq : diagonalFlow (-t) * (g⁻¹ * h) * diagonalFlow t =
      (g * diagonalFlow t)⁻¹ * (h * diagonalFlow t) := by rw [diagonalFlow_neg]; group
  rwa [heq] at hflow

theorem isCompact_forwardHaarTube {η S : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8) (hS : 0 ≤ S) :
    IsCompact (forwardHaarTube η S) := by
  obtain ⟨K, hKsub, hK, _⟩ :=
    (forwardHaarTube_liftForwardClose hη (by linarith) hS).exists_compact_superset
      (by positivity) (by linarith) hS
  exact hK.of_isClosed_subset (isClosed_forwardHaarTube η S) hKsub

end Erdos1148.DukeArithmetic
