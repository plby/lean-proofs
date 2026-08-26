import ErdosProblems.Erdos421.PeriodSum

/-! # First-derivative bounds for interval and band subsums -/

namespace Erdos421

theorem integer_band_Icc_sum_bound (f : ℕ → ℝ) (a b : ℕ) (j : ℤ) {δ : ℝ}
    (hab : a ≤ b) (hanti : AntitoneOn (phaseIncrement f) (Set.Icc a b)) (hδ : 0 < δ)
    (hlo : 2 * Real.pi * j + δ ≤ phaseIncrement f b)
    (hhi : phaseIncrement f a ≤ 2 * Real.pi * (j + 1) - δ) :
    ‖∑ n ∈ Finset.Icc a b, oscillatoryPhase 1 (f n)‖ ≤ 1 + 12 / δ := by
  let g : ℕ → ℝ := fun n ↦ f (a + n)
  have hg : ∀ n, phaseIncrement g n = phaseIncrement f (a + n) := by
    intro n
    simp only [phaseIncrement, g, Nat.add_assoc]
  have hga : AntitoneOn (phaseIncrement g) (Set.Icc 0 (b - a)) := by
    intro i hi k hk hik
    obtain ⟨hi0, hiN⟩ := hi
    obtain ⟨hk0, hkN⟩ := hk
    rw [hg, hg]
    apply hanti
    · constructor <;> omega
    · constructor <;> omega
    · omega
  have hgl : 2 * Real.pi * j + δ ≤ phaseIncrement g (b - a) := by
    rw [hg, Nat.add_sub_of_le hab]
    exact hlo
  have hgh : phaseIncrement g 0 ≤ 2 * Real.pi * (j + 1) - δ := by
    simpa only [hg, Nat.add_zero] using hhi
  have h := integer_band_increment_sum_bound g (b - a) j hga hδ hgl hgh
  have hsum : (∑ n ∈ Finset.Ico a b, oscillatoryPhase 1 (f n)) =
      ∑ n ∈ Finset.range (b - a), oscillatoryPhase 1 (g n) := by
    rw [Finset.sum_Ico_eq_sum_range]
  have hIcc : Finset.Icc a b = insert b (Finset.Ico a b) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_insert (by simp), hsum]
  have hnorm := norm_add_le (oscillatoryPhase 1 (f b))
    (∑ n ∈ Finset.range (b - a), oscillatoryPhase 1 (g n))
  rw [norm_oscillatoryPhase] at hnorm
  exact hnorm.trans (add_le_add le_rfl h)

theorem finset_eq_Icc_of_between (S : Finset ℕ) (hS : S.Nonempty)
    (hbetween : ∀ a ∈ S, ∀ b ∈ S, ∀ n, a ≤ n → n ≤ b → n ∈ S) :
    S = Finset.Icc (S.min' hS) (S.max' hS) := by
  ext n
  constructor
  · intro hn
    exact Finset.mem_Icc.mpr ⟨S.min'_le n hn, S.le_max' n hn⟩
  · intro hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    exact hbetween _ (S.min'_mem hS) _ (S.max'_mem hS) n hlo hhi

noncomputable def phaseBandIndices (f : ℕ → ℝ) (N : ℕ) (j : ℤ) (δ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n ↦
    2 * Real.pi * j + δ ≤ phaseIncrement f n ∧
      phaseIncrement f n ≤ 2 * Real.pi * (j + 1) - δ)

theorem phaseBandIndices_sum_bound (f : ℕ → ℝ) (N : ℕ) (j : ℤ) {δ : ℝ}
    (hanti : AntitoneOn (phaseIncrement f) (Set.Icc 0 N)) (hδ : 0 < δ) :
    ‖∑ n ∈ phaseBandIndices f N j δ, oscillatoryPhase 1 (f n)‖ ≤ 1 + 12 / δ := by
  classical
  let S := phaseBandIndices f N j δ
  have hmem : ∀ n ∈ S, n < N ∧ 2 * Real.pi * j + δ ≤ phaseIncrement f n ∧
      phaseIncrement f n ≤ 2 * Real.pi * (j + 1) - δ := by
    intro n hn
    obtain ⟨hnN, hlo, hhi⟩ := Finset.mem_filter.mp hn
    exact ⟨Finset.mem_range.mp hnN, hlo, hhi⟩
  by_cases hS : S.Nonempty
  · have hbetween : ∀ a ∈ S, ∀ b ∈ S, ∀ n, a ≤ n → n ≤ b → n ∈ S := by
      intro a ha b hb n han hnb
      have ham := hmem a ha
      have hbm := hmem b hb
      have hnN : n < N := by omega
      have hna : phaseIncrement f n ≤ phaseIncrement f a :=
        hanti ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ han
      have hbn : phaseIncrement f b ≤ phaseIncrement f n :=
        hanti ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hnb
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN,
        hbm.2.1.trans hbn, hna.trans ham.2.2⟩
    have heq := finset_eq_Icc_of_between S hS hbetween
    have hmin := hmem _ (S.min'_mem hS)
    have hmax := hmem _ (S.max'_mem hS)
    have ha : AntitoneOn (phaseIncrement f) (Set.Icc (S.min' hS) (S.max' hS)) := by
      intro i hi k hk hik
      obtain ⟨hil, hir⟩ := hi
      obtain ⟨hkl, hkr⟩ := hk
      apply hanti
      · constructor <;> omega
      · constructor <;> omega
      · exact hik
    have h := integer_band_Icc_sum_bound f (S.min' hS) (S.max' hS) j
      (S.min'_le_max' hS) ha hδ hmax.2.1 hmin.2.2
    rwa [← heq] at h
  · have heq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change ‖∑ n ∈ S, oscillatoryPhase 1 (f n)‖ ≤ _
    rw [heq, Finset.sum_empty, norm_zero]
    positivity

end Erdos421
