import ErdosProblems.Erdos1148.BowenTubeFlowGrid
import ErdosProblems.Erdos1148.PacketClosePairs

/-! # A finite flow-translate cover for pairs in the same Bowen tube -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

def modularBowenPairs (η δ : ℝ) : Set (ModularOrbitSpace × ModularOrbitSpace) :=
  {z | ∃ g h : SL(2, ℝ), z = (modularMk g, modularMk h) ∧ EntryBowenTube η δ (g⁻¹ * h)}

lemma isClosed_entryBowenTube (η δ : ℝ) : IsClosed {g : SL(2, ℝ) | EntryBowenTube η δ g} := by
  exact (isClosed_le ((continuous_realMatrixEntry 0 0).sub continuous_const).abs
    continuous_const).inter
    ((isClosed_le (continuous_realMatrixEntry 0 1).abs continuous_const).inter
      ((isClosed_le (continuous_realMatrixEntry 1 0).abs continuous_const).inter
        (isClosed_le ((continuous_realMatrixEntry 1 1).sub continuous_const).abs continuous_const)))

lemma measurableSet_modularBowenPairs (η δ : ℝ) : MeasurableSet (modularBowenPairs η δ) := by
  let : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → ℝ))
  let : SigmaCompactSpace SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.sigmaCompactSpace
  have himage : modularBowenPairs η δ = Prod.map modularMk modularMk ''
      {p : SL(2, ℝ) × SL(2, ℝ) | EntryBowenTube η δ (p.1⁻¹ * p.2)} := by
    ext z
    constructor
    · rintro ⟨g, h, hz, hclose⟩
      exact ⟨(g, h), hclose, hz.symm⟩
    · rintro ⟨⟨g, h⟩, hclose, rfl⟩
      exact ⟨g, h, rfl, hclose⟩
  rw [himage]
  exact measurableSet_image_of_isClosed_sigmaCompact
    (continuous_modularMk.prodMap continuous_modularMk)
    ((isClosed_entryBowenTube η δ).preimage (continuous_fst.inv.mul continuous_snd))

theorem modularBowenPairs_subset_flow_grid {η δ : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (N : ℕ) (s : Fin N → ℝ), (N : ℝ) ≤ 2 / δ ∧
      modularBowenPairs η δ ⊆ ⋃ i : Fin N,
        (Prod.map id (modularRightTranslate (diagonalFlow (s i)))) ⁻¹'
          modularClosePairs (3 * δ) := by
  obtain ⟨N, s, hN, hcover⟩ := exists_bowenTube_flow_grid hη0 hη hδ hδ1
  refine ⟨N, s, hN, ?_⟩
  rintro z ⟨g, h, rfl, hgh⟩
  obtain ⟨i, hi⟩ := hcover (g⁻¹ * h) hgh
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  refine ⟨g, h * diagonalFlow (s i), rfl, ?_⟩
  simpa only [mul_assoc] using hi

lemma modularProduct_map_second_flow (μ : Measure ModularOrbitSpace) [SFinite μ]
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ) (t : ℝ) :
    Measure.map (Prod.map id (modularRightTranslate (diagonalFlow t))) (μ.prod μ) = μ.prod μ := by
  rw [← Measure.map_prod_map μ μ measurable_id
    (continuous_modularRightTranslate _).measurable, Measure.map_id, hinv]

theorem modularBowenPairs_mass_le_closePairs (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ)
    {η δ : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (μ.prod μ).real (modularBowenPairs η δ) ≤
      (2 / δ) * (μ.prod μ).real (modularClosePairs (3 * δ)) := by
  obtain ⟨N, s, hN, hcover⟩ := modularBowenPairs_subset_flow_grid hη0 hη hδ hδ1
  have heq (t : ℝ) :
      (μ.prod μ).real ((Prod.map id (modularRightTranslate (diagonalFlow t))) ⁻¹'
        modularClosePairs (3 * δ)) = (μ.prod μ).real (modularClosePairs (3 * δ)) := by
    unfold Measure.real
    rw [← Measure.map_apply
      (measurable_id.prodMap (continuous_modularRightTranslate _).measurable)
      (measurableSet_modularClosePairs _), modularProduct_map_second_flow μ hinv]
  calc
    _ ≤ (μ.prod μ).real (⋃ i : Fin N,
        (Prod.map id (modularRightTranslate (diagonalFlow (s i)))) ⁻¹'
          modularClosePairs (3 * δ)) := measureReal_mono hcover
    _ ≤ ∑ i : Fin N, (μ.prod μ).real
        ((Prod.map id (modularRightTranslate (diagonalFlow (s i)))) ⁻¹'
          modularClosePairs (3 * δ)) := measureReal_iUnion_fintype_le _
    _ = (N : ℝ) * (μ.prod μ).real (modularClosePairs (3 * δ)) := by
      simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hN measureReal_nonneg

end Erdos1148.DukeArithmetic
