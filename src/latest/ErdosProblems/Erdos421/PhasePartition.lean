import ErdosProblems.Erdos421.PhaseBandCounts

/-! # Partitioning a monotone sequence of phase increments -/

namespace Erdos421

theorem phaseBandIndices_subset_range (f : ℕ → ℝ) (N : ℕ) (j : ℤ) (δ : ℝ) :
    phaseBandIndices f N j δ ⊆ Finset.range N := Finset.filter_subset _ _

theorem phaseBandIndices_disjoint (f : ℕ → ℝ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (phaseBandIndices f N j δ) (phaseBandIndices f N k δ) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hnJ hnK
  have hJ := (Finset.mem_filter.mp hnJ).2
  have hK := (Finset.mem_filter.mp hnK).2
  simp only [Int.cast_natCast] at hJ hK
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · have hreal : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    have hmul := mul_le_mul_of_nonneg_left hreal (show 0 ≤ 2 * Real.pi by positivity)
    linarith
  · have hreal : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
    have hmul := mul_le_mul_of_nonneg_left hreal (show 0 ≤ 2 * Real.pi by positivity)
    linarith

theorem phase_band_cover (f : ℕ → ℝ) (N K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hrange : ∀ n < N, 0 ≤ phaseIncrement f n ∧ phaseIncrement f n ≤ 2 * Real.pi * K) :
    Finset.range N ⊆
      (Finset.range (K + 1)).biUnion (fun j ↦ phaseBandIndices f N j δ) ∪
      (Finset.range (K + 2)).biUnion (fun j ↦ phaseNearPeriodIndices f N j δ) := by
  classical
  intro n hn
  have hd := hrange n (Finset.mem_range.mp hn)
  have hpi : 0 < 2 * Real.pi := by positivity
  let j := ⌊phaseIncrement f n / (2 * Real.pi)⌋₊
  have hjK : j ≤ K := Nat.floor_le_of_le
    ((div_le_iff₀ hpi).mpr (by simpa only [mul_comm] using hd.2))
  have hjlo : 2 * Real.pi * j ≤ phaseIncrement f n := by
    have h := Nat.floor_le (div_nonneg hd.1 hpi.le)
    have hm := (le_div_iff₀ hpi).mp h
    simpa only [mul_comm, j] using hm
  have hjhi : phaseIncrement f n < 2 * Real.pi * ((j : ℝ) + 1) := by
    have h := Nat.lt_floor_add_one (phaseIncrement f n / (2 * Real.pi))
    have hm := (div_lt_iff₀ hpi).mp h
    simpa only [mul_comm, j] using hm
  by_cases hlo : 2 * Real.pi * j + δ ≤ phaseIncrement f n
  · by_cases hhi : phaseIncrement f n ≤ 2 * Real.pi * ((j : ℝ) + 1) - δ
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨hn, ?_⟩⟩
      simpa only [Int.cast_natCast] using And.intro hlo hhi
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j + 1, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨hn, ?_⟩⟩
      push_cast
      constructor <;> linarith
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨hn, ?_⟩⟩
    simp only [Int.cast_natCast]
    constructor <;> linarith

/-- A discrete second-derivative estimate in terms of the increment range and
its minimum decrease per index. The free parameter `δ` is optimized later. -/
theorem separated_increment_sum_bound (f : ℕ → ℝ) (N K : ℕ) {δ η : ℝ}
    (hanti : AntitoneOn (phaseIncrement f) (Set.Icc 0 N)) (hδ : 0 < δ) (hη : 0 < η)
    (hrange : ∀ n < N, 0 ≤ phaseIncrement f n ∧ phaseIncrement f n ≤ 2 * Real.pi * K)
    (hsep : ∀ i < N, ∀ k < N, i ≤ k →
      η * ((k : ℝ) - i) ≤ phaseIncrement f i - phaseIncrement f k) :
    ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (f n)‖ ≤
      ((K : ℝ) + 2) * (2 + 12 / δ + 2 * δ / η) := by
  classical
  let G := (Finset.range (K + 1)).biUnion (fun j ↦ phaseBandIndices f N j δ)
  let R := Finset.range N \ G
  let U := (Finset.range (K + 2)).biUnion (fun j ↦ phaseNearPeriodIndices f N j δ)
  have hG : G ⊆ Finset.range N := by
    intro n hn
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hn
    exact phaseBandIndices_subset_range f N j δ hj
  have hR : R ⊆ U := by
    intro n hn
    obtain ⟨hnN, hnG⟩ := Finset.mem_sdiff.mp hn
    have hc := phase_band_cover f N K hδ hrange hnN
    exact (Finset.mem_union.mp hc).resolve_left hnG
  have hdisj : (↑(Finset.range (K + 1)) : Set ℕ).Pairwise
      (fun j k ↦ Disjoint (phaseBandIndices f N j δ) (phaseBandIndices f N k δ)) :=
    fun _ _ _ _ hjk ↦ phaseBandIndices_disjoint f N hδ hjk
  have hGsum : ‖∑ n ∈ G, oscillatoryPhase 1 (f n)‖ ≤
      ((K : ℝ) + 1) * (1 + 12 / δ) := by
    calc
      _ = ‖∑ j ∈ Finset.range (K + 1),
          ∑ n ∈ phaseBandIndices f N j δ, oscillatoryPhase 1 (f n)‖ := by
        rw [Finset.sum_biUnion hdisj]
      _ ≤ ∑ j ∈ Finset.range (K + 1),
          ‖∑ n ∈ phaseBandIndices f N j δ, oscillatoryPhase 1 (f n)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (K + 1), (1 + 12 / δ) :=
        Finset.sum_le_sum (fun j _ ↦ phaseBandIndices_sum_bound f N j hanti hδ)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one]
  have hRcard : (R.card : ℝ) ≤ ((K : ℝ) + 2) * (2 * δ / η + 1) := by
    have hcard := (Finset.card_le_card hR).trans
      (Finset.card_biUnion_le (s := Finset.range (K + 2)))
    calc
      _ ≤ ∑ j ∈ Finset.range (K + 2), ((phaseNearPeriodIndices f N j δ).card : ℝ) := by
        exact_mod_cast hcard
      _ ≤ ∑ _j ∈ Finset.range (K + 2), (2 * δ / η + 1) :=
        Finset.sum_le_sum (fun j _ ↦ phaseNearPeriodIndices_card_bound f N j hδ.le hη hsep)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_ofNat]
  have hRsum : ‖∑ n ∈ R, oscillatoryPhase 1 (f n)‖ ≤ (R.card : ℝ) := by
    calc
      _ ≤ ∑ n ∈ R, ‖oscillatoryPhase 1 (f n)‖ := norm_sum_le _ _
      _ = _ := by simp
  have hid := Finset.sum_sdiff hG (f := fun n ↦ oscillatoryPhase 1 (f n))
  have htotal := (norm_add_le (∑ n ∈ R, oscillatoryPhase 1 (f n))
    (∑ n ∈ G, oscillatoryPhase 1 (f n))).trans
      (add_le_add (hRsum.trans hRcard) hGsum)
  change (∑ n ∈ R, oscillatoryPhase 1 (f n)) + (∑ n ∈ G, oscillatoryPhase 1 (f n)) = _ at hid
  rw [hid] at htotal
  have hn : 0 ≤ 1 + 12 / δ := by positivity
  nlinarith

end Erdos421
