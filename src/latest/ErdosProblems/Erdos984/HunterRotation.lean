/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterTypicalParameters

/-!
# A rotation satisfying both Hunter requirements

The blue-progression condition and the Diophantine character condition are
obtained from one Haar-random rotation by excluding the union of their two
bad sets.
-/

open Set Function MeasureTheory Metric
open scoped ENNReal BigOperators

namespace Erdos984

noncomputable section

/-- The explicit nonsingular-minor formulation of Hunter typicality. -/
def HunterTypicalRotation (D : ℕ) (θ : UnitAddTorus (Fin D)) : Prop :=
  ∀ (n : Fin (hunterN D))
    (q : Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D)
    (σ : Fin (hunterRankWitness D) → Fin D),
    (integerCharacterMinorRealMatrix
      (decodedFrequency (decodeHunterFrequency D) q) σ).det ≠ 0 →
    nsmulIntegerCharacterTuple (n + 1)
      (decodedFrequency (decodeHunterFrequency D) q) θ ∉
      closedBall (0 : UnitAddTorus (Fin (hunterRankWitness D)))
        (hunterPhaseTolerance D)

/-- There is a single rotation which is typical and whose relevant positive
multiples satisfy the geometric blue-step inequality. -/
lemma exists_hunter_full_rotation (D : ℕ) (hD : 2 ≤ D) :
    ∃ θ : UnitAddTorus (Fin D), HunterTypicalRotation D θ ∧
      ∀ d : ℕ, 0 < d → d < hunterN D →
        radialSquaredWidth (hunterDelta D) (hunterK D) <
          squaredNorm (centeredTorusLift (d • θ)) := by
  let _ : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  let U : Set (UnitAddTorus (Fin D)) :=
    characterMinorBadSet
      (R := Fin (hunterRankWitness D)) (Q := HunterFrequencyAlphabet D)
      (hunterN D) (decodeHunterFrequency D) (hunterPhaseTolerance D)
  let V : Set (UnitAddTorus (Fin D)) :=
    smallMultipleBadSet (hunterN D) (hunterTau D)
  let qU : ENNReal :=
    (Fintype.card
      (Fin (hunterN D) ×
        (Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D) ×
        (Fin (hunterRankWitness D) → Fin D)) : ENNReal) *
      (ENNReal.ofReal (2 * hunterPhaseTolerance D)) ^ hunterRankWitness D
  let qV : ENNReal := (hunterN D : ENNReal) *
    (ENNReal.ofReal (2 * hunterTau D)) ^ D
  have hU : volume U ≤ qU := by
    simpa [U, qU] using volume_characterMinorBadSet_le
      (D := Fin D) (R := Fin (hunterRankWitness D))
      (Q := HunterFrequencyAlphabet D) (hunterN D)
      (decodeHunterFrequency D) (hunterPhaseTolerance_nonneg D)
      (hunterPhaseTolerance_le_half D hD)
  have hV : volume V ≤ qV := by
    simpa [V, qV] using volume_smallMultipleBadSet_le
      (D := Fin D) (hunterN D) (hunterTau_pos (by omega)).le
      (hunterTau_le_half (by omega))
  have hqU : qU < ENNReal.ofReal ((1 : ℝ) / 2) := by
    simpa [qU] using hunter_typical_cost_lt_half D hD
  have hqV : qV < ENNReal.ofReal ((1 : ℝ) / 2) := by
    simpa [qV] using hunter_haar_cost_lt_half D hD
  have hsum : qU + qV < 1 := by
    calc
      qU + qV < ENNReal.ofReal ((1 : ℝ) / 2) +
          ENNReal.ofReal ((1 : ℝ) / 2) := ENNReal.add_lt_add hqU hqV
      _ = ENNReal.ofReal ((1 : ℝ) / 2 + (1 : ℝ) / 2) := by
        rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
      _ = 1 := by norm_num
  have hUV : volume (U ∪ V) < 1 :=
    (measure_union_le U V).trans_lt ((add_le_add hU hV).trans_lt hsum)
  have hne : U ∪ V ≠ Set.univ := by
    intro hEq
    rw [hEq, volume_unitAddTorus_univ] at hUV
    exact (lt_self_iff_false 1).mp hUV
  obtain ⟨θ, hθ⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hθU : θ ∉ U := fun h ↦ hθ (Or.inl h)
  have hθV : θ ∉ V := fun h ↦ hθ (Or.inr h)
  refine ⟨θ, ?_, ?_⟩
  · intro n q σ hdet hmem
    apply hθU
    apply Set.mem_iUnion_of_mem (n, q, σ)
    simp [characterMinorBadCell, hdet, hmem]
  · intro d hd hdN
    have hdI : d ∈ (Finset.range (hunterN D)).erase 0 := by
      simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨hd.ne', hdN⟩
    have hnotball : d • θ ∉ closedBall (0 : UnitAddTorus (Fin D))
        (hunterTau D) := by
      intro hmem
      apply hθV
      exact Set.mem_iUnion_of_mem d (Set.mem_iUnion_of_mem hdI hmem)
    have hnorm : hunterTau D < ‖d • θ‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hnotball
      exact lt_of_not_ge hnotball
    exact (hunter_width_lt_tau_sq D hD).trans
      (sq_lt_squaredNorm_centeredTorusLift_of_lt_norm
        (hunterTau_pos (by omega)).le hnorm)

end

end Erdos984
