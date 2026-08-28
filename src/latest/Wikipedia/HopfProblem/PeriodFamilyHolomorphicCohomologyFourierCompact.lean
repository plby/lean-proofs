import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierUniform

/-!
# Uniform symbol estimates over compact parts of the base

A finite subcover of the proved local estimates gives a single positive bound
on any compact base set.  The set need not be nonempty.  No compactness of the
whole base, or further regularity of the period functions, is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier

open Set
open PeriodTorusLineBundleClassification

/-- Finitely many positive bounds admit one positive common lower bound. -/
theorem finite_positive_lowerBound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c ≤ f i := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    intro hf
    obtain ⟨c, hc, hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) c, lt_min (hf i (Finset.mem_insert_self _ _)) hc, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound j hj)

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- One positive lower bound works for every real frequency above a compact base set. -/
theorem exists_compact_uniform_symbol_lowerBound (K : Set B) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ K, ∀ v : Fin 4 → ℝ,
      c * ‖v‖ ≤ ‖dolbeaultSymbol (P.point b) v‖ := by
  classical
  choose U C hU hb hC hbound using exists_open_uniform_symbol_lowerBound P
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU
    (fun b _ => mem_iUnion.mpr ⟨b, hb b⟩)
  obtain ⟨c, hc, hcs⟩ := finite_positive_lowerBound s C (fun i _ => hC i)
  refine ⟨c, hc, fun b hbK v => ?_⟩
  obtain ⟨i, his, hbi⟩ := mem_iUnion₂.mp (hs hbK)
  exact (mul_le_mul_of_nonneg_right (hcs i his) (norm_nonneg v)).trans
    (hbound i b hbi v)

/-- The compact-set estimate retains the actual norm of the integer frequency. -/
theorem exists_compact_uniform_integer_lowerBound (K : Set B) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ K, ∀ k : Fin 4 → ℤ,
      c * ‖k‖ ≤ ‖dolbeaultSymbol (P.point b) (integerFrequency k)‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_compact_uniform_symbol_lowerBound P K hK
  refine ⟨c, hc, fun b hb k => ?_⟩
  simpa only [integerFrequency_norm] using hbound b hb (integerFrequency k)

/-- The nonzero integer modes stay uniformly away from zero on any compact base set. -/
theorem exists_compact_uniform_integer_gap (K : Set B) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ K, ∀ k : Fin 4 → ℤ, k ≠ 0 →
      c ≤ ‖dolbeaultSymbol (P.point b) (integerFrequency k)‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_compact_uniform_integer_lowerBound P K hK
  refine ⟨c, hc, fun b hb k hk => ?_⟩
  calc
    c = c * 1 := (mul_one c).symm
    _ ≤ c * ‖k‖ := mul_le_mul_of_nonneg_left (one_le_norm_integerVector hk) hc.le
    _ ≤ ‖dolbeaultSymbol (P.point b) (integerFrequency k)‖ := hbound b hb k

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier
