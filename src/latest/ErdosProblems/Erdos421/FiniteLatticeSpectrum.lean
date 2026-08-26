import ErdosProblems.Erdos421.RationalLatticeFrequencies
import ErdosProblems.Erdos421.DivisorFourierCoefficients

/-! # Grouping a finite lattice spectrum by its reduced rational frequency -/

namespace Erdos421

noncomputable def groupedLatticeCoefficient (T : Finset (ℕ × ℤ)) (a : ℕ → ℂ)
    (q : ℚ) : ℂ :=
  ∑ v ∈ T.filter (fun v ↦ (v.2 : ℚ) / v.1 = q), a v.1 / (v.1 : ℂ)

theorem groupedLatticeCoefficient_norm_le (T : Finset (ℕ × ℤ)) (a : ℕ → ℂ)
    {M : ℕ} (hT : ∀ v ∈ T, 0 < v.1 ∧ v.1 ≤ M)
    (ha : ∀ v ∈ T, ‖a v.1‖ ≤ 1) (q : ℚ) :
    ‖groupedLatticeCoefficient T a q‖ ≤ (harmonic M : ℝ) / q.den := by
  classical
  let U := T.filter (fun v ↦ (v.2 : ℚ) / v.1 = q)
  have hinj : Set.InjOn Prod.fst (↑U : Set (ℕ × ℤ)) := by
    intro v hv w hw heq
    have hvq := (Finset.mem_filter.mp hv).2
    have hwq := (Finset.mem_filter.mp hw).2
    have hpos := (hT v (Finset.mem_filter.mp hv).1).1
    apply Prod.ext heq
    apply lattice_frequency_injective hpos
    change v.1 = w.1 at heq
    rw [← heq] at hwq
    exact hvq.trans hwq.symm
  have hS : ∀ m ∈ U.image Prod.fst, 0 < m ∧ m ≤ M ∧ q.den ∣ m := by
    intro m hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hvT, hvq⟩ := Finset.mem_filter.mp hv
    refine ⟨(hT v hvT).1, (hT v hvT).2, ?_⟩
    rw [← hvq]
    exact lattice_frequency_den_dvd v.2 v.1
  calc
    _ ≤ ∑ v ∈ U, ‖a v.1 / (v.1 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ U, 1 / (v.1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (ha v (Finset.mem_filter.mp hv).1)
        (Nat.cast_nonneg v.1)
    _ = ∑ m ∈ U.image Prod.fst, 1 / (m : ℝ) := by rw [Finset.sum_image hinj]
    _ ≤ _ := sum_reciprocal_multiples_le (U.image Prod.fst) q.den_pos hS

theorem finite_lattice_spectrum_grouping (T : Finset (ℕ × ℤ)) (a : ℕ → ℂ)
    (f : ℚ → ℂ) :
    (∑ v ∈ T, (a v.1 / (v.1 : ℂ)) * f ((v.2 : ℚ) / v.1)) =
      ∑ q ∈ T.image (fun v ↦ (v.2 : ℚ) / v.1), groupedLatticeCoefficient T a q * f q := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun v hv ↦ Finset.mem_image_of_mem (fun v : ℕ × ℤ ↦ (v.2 : ℚ) / v.1) hv)
    (fun v : ℕ × ℤ ↦ (a v.1 / (v.1 : ℂ)) * f ((v.2 : ℚ) / v.1))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [groupedLatticeCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [(Finset.mem_filter.mp hv).2]

end Erdos421
