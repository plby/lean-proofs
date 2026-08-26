import ErdosProblems.Erdos538.AnalyticBaseline

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- Membership characterization for the union of positive exact squarefree
layers through `K`. -/
theorem mem_lowSquarefreeLayers_iff {N K n : ℕ} :
    n ∈ lowSquarefreeLayers N K ↔
      n ∈ positiveSquarefree N ∧ 1 ≤ n.primeFactors.card ∧
        n.primeFactors.card ≤ K := by
  classical
  constructor
  · intro hn
    obtain ⟨k, hk, hnk⟩ := Finset.mem_biUnion.mp hn
    have hkIcc := Finset.mem_Icc.mp hk
    have hnLayer := Finset.mem_filter.mp hnk
    have hnSF : n ∈ positiveSquarefree N :=
      Finset.mem_filter.mpr ⟨hnLayer.1, hnLayer.2.1⟩
    exact ⟨hnSF, hkIcc.1.trans_eq hnLayer.2.2.symm,
      hnLayer.2.2.le.trans hkIcc.2⟩
  · rintro ⟨hnSF, hn1, hnK⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨n.primeFactors.card, Finset.mem_Icc.mpr ⟨hn1, hnK⟩, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hnSF).1, (Finset.mem_filter.mp hnSF).2, rfl⟩

/-- Squarefree integers above the truncation in prime-factor count. -/
def highSquarefreeLayers (N K : ℕ) : Finset ℕ :=
  (positiveSquarefree N).filter fun n => K < n.primeFactors.card

/-- The high-layer reciprocal mass is controlled by the first moment. -/
theorem highSquarefree_mass_markov (N K : ℕ) :
    (K + 1) • reciprocalMassNN (highSquarefreeLayers N K) ≤
      squarefreePrimeFactorMomentNN N := by
  classical
  unfold reciprocalMassNN highSquarefreeLayers
  rw [Finset.smul_sum]
  calc
    (∑ n ∈ (positiveSquarefree N).filter
        (fun n => K < n.primeFactors.card),
        (K + 1) • ((1 : ℚ≥0) / n)) ≤
      ∑ n ∈ (positiveSquarefree N).filter
        (fun n => K < n.primeFactors.card),
        n.primeFactors.card • ((1 : ℚ≥0) / n) := by
          apply Finset.sum_le_sum
          intro n hn
          exact nsmul_le_nsmul_left bot_le
            (Nat.succ_le_iff.mpr (Finset.mem_filter.mp hn).2)
    _ ≤ ∑ n ∈ positiveSquarefree N,
        n.primeFactors.card • ((1 : ℚ≥0) / n) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = squarefreePrimeFactorMomentNN N := rfl

/-- The squarefree mass splits into the unit, low layers, and high layers. -/
theorem squarefree_mass_le_one_add_low_add_high (N K : ℕ) :
    reciprocalMassNN (positiveSquarefree N) ≤
      1 + reciprocalMassNN (lowSquarefreeLayers N K) +
        reciprocalMassNN (highSquarefreeLayers N K) := by
  classical
  let zeroLayer := (positiveSquarefree N).filter
    (fun n => n.primeFactors.card = 0)
  have hzero : zeroLayer ⊆ {1} := by
    intro n hn
    have hnSF := (Finset.mem_filter.mp hn).1
    have hcard := (Finset.mem_filter.mp hn).2
    have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard
    have hn01 := Nat.primeFactors_eq_empty.mp hempty
    have hnpos : 1 ≤ n :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hnSF).1).1
    have hn1 : n = 1 := by omega
    simpa [hn1]
  have hzeroMass : reciprocalMassNN zeroLayer ≤ 1 := by
    calc
      reciprocalMassNN zeroLayer ≤ reciprocalMassNN {1} := by
        unfold reciprocalMassNN
        exact Finset.sum_le_sum_of_subset hzero
      _ = 1 := by simp [reciprocalMassNN]
  have hzeroLow : Disjoint zeroLayer (lowSquarefreeLayers N K) := by
    rw [Finset.disjoint_left]
    intro n hnzero hnlow
    have hz : n.primeFactors.card = 0 := (Finset.mem_filter.mp hnzero).2
    have hl := (mem_lowSquarefreeLayers_iff.mp hnlow).2.1
    omega
  have hunionHigh : Disjoint
      (zeroLayer ∪ lowSquarefreeLayers N K) (highSquarefreeLayers N K) := by
    rw [Finset.disjoint_left]
    intro n hnunion hnhigh
    have hh : K < n.primeFactors.card := (Finset.mem_filter.mp hnhigh).2
    rcases Finset.mem_union.mp hnunion with hnzero | hnlow
    · have hz : n.primeFactors.card = 0 := (Finset.mem_filter.mp hnzero).2
      omega
    · have hl := (mem_lowSquarefreeLayers_iff.mp hnlow).2.2
      omega
  have hunion :
      (zeroLayer ∪ lowSquarefreeLayers N K) ∪ highSquarefreeLayers N K =
        positiveSquarefree N := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_union.mp hn with hnzl | hnhigh
      · rcases Finset.mem_union.mp hnzl with hnzero | hnlow
        · exact (Finset.mem_filter.mp hnzero).1
        · exact (mem_lowSquarefreeLayers_iff.mp hnlow).1
      · exact (Finset.mem_filter.mp hnhigh).1
    · intro hnSF
      by_cases hz : n.primeFactors.card = 0
      · apply Finset.mem_union.mpr
        exact Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨hnSF, hz⟩)))
      · have hpos : 1 ≤ n.primeFactors.card := Nat.one_le_iff_ne_zero.mpr hz
        by_cases hle : n.primeFactors.card ≤ K
        · apply Finset.mem_union.mpr
          exact Or.inl (Finset.mem_union.mpr (Or.inr
            (mem_lowSquarefreeLayers_iff.mpr ⟨hnSF, hpos, hle⟩)))
        · apply Finset.mem_union.mpr
          exact Or.inr (Finset.mem_filter.mpr
            ⟨hnSF, Nat.lt_of_not_ge hle⟩)
  have hsplit : reciprocalMassNN (positiveSquarefree N) =
      reciprocalMassNN zeroLayer +
        reciprocalMassNN (lowSquarefreeLayers N K) +
          reciprocalMassNN (highSquarefreeLayers N K) := by
    rw [← hunion]
    unfold reciprocalMassNN
    rw [Finset.sum_union hunionHigh, Finset.sum_union hzeroLow]
  rw [hsplit]
  have h := add_le_add_right
    (add_le_add_right hzeroMass
      (reciprocalMassNN (lowSquarefreeLayers N K)))
    (reciprocalMassNN (highSquarefreeLayers N K))
  calc
    reciprocalMassNN zeroLayer + reciprocalMassNN (lowSquarefreeLayers N K) +
        reciprocalMassNN (highSquarefreeLayers N K) =
      reciprocalMassNN (highSquarefreeLayers N K) +
        (reciprocalMassNN (lowSquarefreeLayers N K) +
          reciprocalMassNN zeroLayer) := by ac_rfl
    _ ≤ reciprocalMassNN (highSquarefreeLayers N K) +
        (reciprocalMassNN (lowSquarefreeLayers N K) + 1) := h
    _ = 1 + reciprocalMassNN (lowSquarefreeLayers N K) +
        reciprocalMassNN (highSquarefreeLayers N K) := by ac_rfl

/-- Finite truncation inequality, with the analytic prime reciprocal sum left
explicit. -/
theorem squarefree_truncation_inequality (N K : ℕ) :
    (K + 1) • reciprocalMassNN (positiveSquarefree N) ≤
      (K + 1) •
          (1 + reciprocalMassNN (lowSquarefreeLayers N K)) +
        primeHarmonicNN N * harmonicMassNN N := by
  have hsplit := squarefree_mass_le_one_add_low_add_high N K
  have hmarkov := highSquarefree_mass_markov N K
  have hmoment := squarefreePrimeFactorMomentNN_le N
  simp only [nsmul_eq_mul] at hmarkov ⊢
  qify at hsplit hmarkov hmoment ⊢
  have hq : (0 : ℚ) ≤ K + 1 := by positivity
  nlinarith

/-- The complete finite baseline engine: there is an admissible family whose
mass appears in the low-layer term of the truncation inequality. -/
theorem exists_admissible_baseline_inequality (N K : ℕ) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      (K + 1) • reciprocalMassNN (positiveSquarefree N) ≤
        (K + 1) • (1 + (4 * K * K) • reciprocalMassNN A) +
          primeHarmonicNN N * harmonicMassNN N := by
  obtain ⟨A, hAdm, -, hlow⟩ := exists_admissible_lowSquarefreeLayers N K
  have hlow' : reciprocalMassNN (lowSquarefreeLayers N K) ≤
      (4 * K * K) • reciprocalMassNN A := by
    rw [reciprocalMassNN_lowSquarefreeLayers]
    exact hlow
  refine ⟨A, hAdm, ?_⟩
  have hmono := add_le_add_right
    (nsmul_le_nsmul_right (add_le_add_left hlow' 1) (K + 1))
    (primeHarmonicNN N * harmonicMassNN N)
  apply (squarefree_truncation_inequality N K).trans
  simpa only [add_comm] using hmono

/-- If `K` is at least four times the prime reciprocal sum (up to the harmless
`+1`), the finite engine gives the expected harmonic-over-`K²` lower bound. -/
theorem exists_admissible_of_primeHarmonic_le
    (N K : ℕ) (hprime : 4 * primeHarmonicNN N ≤ K + 1) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      harmonicMassNN N ≤ 4 + (16 * K * K) • reciprocalMassNN A := by
  obtain ⟨A, hAdm, hbase⟩ := exists_admissible_baseline_inequality N K
  refine ⟨A, hAdm, ?_⟩
  let S := reciprocalMassNN (positiveSquarefree N)
  let H := harmonicMassNN N
  let P := primeHarmonicNN N
  let M := reciprocalMassNN A
  let q : ℚ≥0 := K + 1
  let C : ℚ≥0 := 4 * K * K
  have hHS : H ≤ 2 * S := by
    simpa [H, S] using harmonicMassNN_le_two_mul_squarefree N
  have htail : 2 * (P * H) ≤ q * S := by
    have h1 : 2 * (P * H) ≤ 4 * P * S := by
      calc
        2 * (P * H) = (2 * P) * H := by ring
        _ ≤ (2 * P) * (2 * S) := mul_le_mul_right hHS (2 * P)
        _ = 4 * P * S := by ring
    have h2 : 4 * P * S ≤ q * S := by
      apply mul_le_mul_left
      simpa [P, q] using hprime
    exact h1.trans h2
  have hbase' : q * S ≤ q * (1 + C * M) + P * H := by
    simp only [nsmul_eq_mul] at hbase
    dsimp [q, S, C, M, P, H]
    push_cast at hbase ⊢
    convert hbase using 1 <;> ring
  have hq : (0 : ℚ≥0) < q := by simp [q]
  have hSM : S ≤ 2 * (1 + C * M) := by
    have hmul : q * S ≤ q * (2 * (1 + C * M)) := by
      qify at hbase' htail ⊢
      nlinarith
    exact (mul_le_mul_iff_of_pos_left hq).mp (by
      convert hmul using 1 <;> ring)
  calc
    harmonicMassNN N = H := rfl
    _ ≤ 2 * S := hHS
    _ ≤ 2 * (2 * (1 + C * M)) := mul_le_mul_right hSM 2
    _ = 4 + (16 * K * K) • reciprocalMassNN A := by
      simp [C, M, nsmul_eq_mul]
      ring

end Erdos538
