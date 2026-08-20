import ErdosProblems.Erdos720.Random
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Finset
open MeasureTheory ProbabilityTheory unitInterval
open scoped SimpleGraph Topology ENNReal

noncomputable section

namespace Erdos720

lemma markov_quarter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞} {N : ℝ≥0∞}
    (hX : AEMeasurable X μ)
    (hEX : ∫⁻ ω, X ω ∂μ ≤ N / 8) :
    μ {ω | N / 2 < X ω} ≤ (1 / 4 : ℝ≥0∞) := by
  by_cases hN0 : N = 0
  · subst hN0
    have hint : ∫⁻ ω, X ω ∂μ = 0 := by
      simpa using le_antisymm hEX (by simp)
    have hX0 : X =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hX).1 hint
    have hnull : μ {ω | 0 < X ω} = 0 := by
      simpa [pos_iff_ne_zero] using (MeasureTheory.ae_iff.mp hX0)
    have hnull' : μ {ω | 0 / 2 < X ω} = 0 := by
      simpa using hnull
    rw [hnull']
    simp
  · by_cases hNtop : N = ∞
    · subst hNtop
      have hhalf : (∞ : ℝ≥0∞) / 2 = ∞ := by
        simpa using (ENNReal.top_div_coe : (∞ : ℝ≥0∞) / (2 : ℕ) = ∞)
      have hempty : {ω | (∞ : ℝ≥0∞) / 2 < X ω} = ∅ := by
        ext ω
        rw [hhalf]
        simp
      rw [hempty]
      simp
    · have hhalf_ne_zero : N / 2 ≠ 0 := by
        exact ENNReal.div_ne_zero.2 ⟨hN0, by simp⟩
      have hhalf_ne_top : N / 2 ≠ ∞ := ENNReal.div_ne_top hNtop (by simp)
      have hmarkov : μ {ω | N / 2 ≤ X ω} ≤ (∫⁻ ω, X ω ∂μ) / (N / 2) :=
        meas_ge_le_lintegral_div hX hhalf_ne_zero hhalf_ne_top
      have hsubset : {ω | N / 2 < X ω} ⊆ {ω | N / 2 ≤ X ω} := by
        intro ω hω
        simpa only [Set.mem_ofPred_eq] using hω.le
      refine (measure_mono hsubset).trans ?_
      refine hmarkov.trans ?_
      calc
        (∫⁻ ω, X ω ∂μ) / (N / 2) ≤ (N / 8) / (N / 2) :=
          ENNReal.div_le_div_right hEX _
        _ = (1 / 4 : ℝ≥0∞) := by
          calc
            (N / 8) / (N / 2) = ((1 / 8 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞)) := by
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                (ENNReal.mul_div_mul_left
                  (a := (1 / 8 : ℝ≥0∞)) (b := (1 / 2 : ℝ≥0∞)) (c := N) hN0 hNtop)
            _ = (1 / 4 : ℝ≥0∞) := by
              rw [ENNReal.div_eq_inv_mul]
              simp
              simpa [mul_comm] using
                (show ((8 : ℝ≥0∞)⁻¹ * 2) = (1 / 4 : ℝ≥0∞) by
                  rw [← ENNReal.div_eq_inv_mul]
                  simpa using congrArg (fun x : NNReal => (x : ℝ≥0∞))
                    (show ((2 : NNReal) / 8) = (1 / 4 : NNReal) by norm_num))

lemma positive_nat_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Y : Ω → ℕ}
    (hY : AEMeasurable (fun ω => (Y ω : ℝ≥0∞)) μ)
    (hEY : ∫⁻ ω, (Y ω : ℝ≥0∞) ∂μ < 1 / 4) :
    μ {ω | 0 < Y ω} < (1 / 4 : ℝ≥0∞) := by
  have hle : μ {ω | 0 < Y ω} ≤ ∫⁻ ω, (Y ω : ℝ≥0∞) ∂μ := by
    refine MeasureTheory.meas_le_lintegral₀ hY ?_
    intro ω hω
    exact_mod_cast Nat.succ_le_iff.2 hω
  exact lt_of_le_of_lt hle hEY

lemma measure_union_lt_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A B : Set Ω} (hA : μ A ≤ (1 / 4 : ℝ≥0∞)) (hB : μ B < (1 / 4 : ℝ≥0∞)) :
    μ (A ∪ B) < 1 := by
  calc
    μ (A ∪ B) ≤ μ A + μ B := measure_union_le _ _
    _ ≤ (1 / 4 : ℝ≥0∞) + μ B := by gcongr
    _ < (1 / 4 : ℝ≥0∞) + 1 / 4 := by
          exact ENNReal.add_lt_add_left (by simp) hB
    _ < 1 := by
          have htr :
              (((1 / 4 : ℝ≥0∞) + 1 / 4).toReal) < (1 : ℝ≥0∞).toReal := by
            norm_num [ENNReal.toReal_add]
          exact (ENNReal.toReal_lt_toReal (by simp) (by simp)).1 htr

lemma hole_real_bound (k : ℕ) (hk : 16 ≤ k) :
    (Nat.choose (7 * k) k : ℝ) ^ 2 *
        (1 - (16 : ℝ) / k) ^ (k * k) < 1 / 4 := by
  have hkpos : 0 < k := by omega
  have hbase_nonneg : 0 ≤ 1 - (16 : ℝ) / k := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hkpos : (0 : ℝ) < k)]
    exact_mod_cast hk
  have hblock : (1 - (16 : ℝ) / k) ^ k ≤ Real.exp (-16) := by
    exact Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hk)
  have hexp : Real.exp (-16) < (1 / 2 : ℝ) ^ 16 := by
    have h1 : Real.exp (-1) < (1 / 2 : ℝ) := Real.exp_neg_one_lt_half
    have hp := pow_lt_pow_left₀ h1 (Real.exp_pos (-1)).le (by norm_num : 16 ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  have hhole : (1 - (16 : ℝ) / k) ^ (k * k) < ((1 / 2 : ℝ) ^ 16) ^ k := by
    rw [pow_mul]
    exact pow_lt_pow_left₀ (lt_of_le_of_lt hblock hexp)
      (pow_nonneg hbase_nonneg k) hkpos.ne'
  have hchooseNat : Nat.choose (7 * k) k ≤ 2 ^ (7 * k) := Nat.choose_le_two_pow _ _
  have hchoose : (Nat.choose (7 * k) k : ℝ) ≤ (128 : ℝ) ^ k := by
    have hc : (Nat.choose (7 * k) k : ℝ) ≤ ((2 ^ (7 * k) : ℕ) : ℝ) := by
      exact_mod_cast hchooseNat
    calc
      (Nat.choose (7 * k) k : ℝ) ≤ ((2 ^ (7 * k) : ℕ) : ℝ) := hc
      _ = (128 : ℝ) ^ k := by norm_num [pow_mul]
  have hchoose_sq : (Nat.choose (7 * k) k : ℝ) ^ 2 ≤ (16384 : ℝ) ^ k := by
    calc
      (Nat.choose (7 * k) k : ℝ) ^ 2 ≤ ((128 : ℝ) ^ k) ^ 2 := by
        gcongr
      _ = (16384 : ℝ) ^ k := by
        rw [pow_two, ← mul_pow]
        norm_num
  calc
    (Nat.choose (7 * k) k : ℝ) ^ 2 * (1 - (16 : ℝ) / k) ^ (k * k)
        < (16384 : ℝ) ^ k * (((1 / 2 : ℝ) ^ 16) ^ k) := by
          exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hchoose_sq (pow_nonneg hbase_nonneg _))
            (mul_lt_mul_of_pos_left hhole (pow_pos (by norm_num) _))
    _ = (1 / 4 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num
    _ ≤ 1 / 4 := by
      exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)

/-- The sparse no-hole graph used in both Ramsey arguments. -/
lemma exists_sparse_noHole_graph (k : ℕ) (hk : 16 ≤ k) :
    ∃ H : SimpleGraph (Fin (7 * k)),
      Nat.card H.edgeSet ≤ 3136 * k ∧
      ∀ A B : Finset (Fin (7 * k)), A.card = k → B.card = k → Disjoint A B →
        ∃ a ∈ A, ∃ b ∈ B, H.Adj a b := by
  classical
  have hkpos : 0 < k := by omega
  let p : I := ⟨(16 : ℝ) / k, by positivity, by
    rw [div_le_one (by exact_mod_cast hkpos : (0 : ℝ) < k)]
    exact_mod_cast hk⟩
  let μ : Measure (Set (Sym2 (Fin (7 * k)))) :=
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin (7 * k)))), p)
  have hp_real : ((toNNReal p : NNReal) : ℝ) = (16 : ℝ) / k := by
    simp [p]
  have hs_real : ((toNNReal (σ p) : NNReal) : ℝ) = 1 - (16 : ℝ) / k := by
    have hsum : ((toNNReal (σ p) : NNReal) : ℝ) + (16 : ℝ) / k = 1 := by
      simpa [p] using congrArg (fun x : NNReal ↦ (x : ℝ)) (unitInterval.toNNReal_symm_add p)
    linarith
  have hedge_real :
      (Nat.choose (7 * k) 2 : ℝ) * ((16 : ℝ) / k) ≤ (784 * k : ℕ) := by
    have hcNat : Nat.choose (7 * k) 2 ≤ (7 * k) ^ 2 := Nat.choose_le_pow _ _
    have hc : (Nat.choose (7 * k) 2 : ℝ) ≤ ((7 * k : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hcNat
    calc
      (Nat.choose (7 * k) 2 : ℝ) * ((16 : ℝ) / k)
          ≤ (((7 * k : ℕ) : ℝ) ^ 2) * ((16 : ℝ) / k) := by
            gcongr
      _ = (784 * k : ℕ) := by
        norm_num [Nat.cast_mul]
        field_simp
        ring
  have hEX :
      ∫⁻ ω, (randomEdgeCount (7 * k) ω : ℝ≥0∞) ∂μ ≤
        (6272 * k : ℕ) / 8 := by
    rw [show μ = setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin (7 * k)))), p) from rfl,
      randomEdgeCount_lintegral_eq]
    have hp_enn : ((toNNReal p : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal ((16 : ℝ) / k) := by
      rw [ENNReal.coe_nnreal_eq]
      simpa [hp_real]
    rw [← ENNReal.ofReal_natCast, hp_enn,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Nat.choose (7 * k) 2 : ℝ))]
    have hright : ENNReal.ofReal ((784 * k : ℕ) : ℝ) =
        ((6272 * k : ℕ) : ℝ≥0∞) / 8 := by
      rw [Nat.cast_mul]
      norm_num only [Nat.cast_ofNat]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 784)]
      norm_num only [ENNReal.ofReal_ofNat, Nat.cast_ofNat, ENNReal.ofReal_natCast]
      have hcast : ((6272 * k : ℕ) : ℝ≥0∞) =
          (6272 : ℝ≥0∞) * (k : ℝ≥0∞) := by exact_mod_cast (Nat.cast_mul 6272 k)
      rw [hcast]
      change (784 : ℝ≥0∞) * (k : ℝ≥0∞) =
        ((6272 : ℝ≥0∞) * (k : ℝ≥0∞)) / 8
      have hc : (784 : ℝ≥0∞) = 6272 * (8 : ℝ≥0∞)⁻¹ := by
        have hnn : (784 : NNReal) = 6272 * (8 : NNReal)⁻¹ := by norm_num
        simpa using congrArg (fun x : NNReal ↦ (x : ℝ≥0∞)) hnn
      rw [div_eq_mul_inv]
      calc
        (784 : ℝ≥0∞) * k = k * 784 := mul_comm _ _
        _ = k * (6272 * (8 : ℝ≥0∞)⁻¹) := by rw [hc]
        _ = 6272 * k * (8 : ℝ≥0∞)⁻¹ := by ac_rfl
    rw [← hright]
    exact ENNReal.ofReal_le_ofReal hedge_real
  have hEY :
      ∫⁻ ω, (holeCount (7 * k) k ω : ℝ≥0∞) ∂μ < 1 / 4 := by
    refine lt_of_le_of_lt (by simpa [μ] using holeCount_lintegral_le (7 * k) k p) ?_
    have hs_enn : ((toNNReal (σ p) : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal (1 - (16 : ℝ) / k) := by
      rw [ENNReal.coe_nnreal_eq]
      simpa [hs_real]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity) 2,
      hs_enn, ← ENNReal.ofReal_pow (by
        rw [sub_nonneg, div_le_one (by exact_mod_cast hkpos : (0 : ℝ) < k)]
        exact_mod_cast hk) (k * k),
      ← ENNReal.ofReal_mul (sq_nonneg (Nat.choose (7 * k) k : ℝ))]
    have hbound := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)).2
      (hole_real_bound k hk)
    simpa using hbound
  have hEdgeMeas : AEMeasurable
      (fun ω ↦ (randomEdgeCount (7 * k) ω : ℝ≥0∞)) μ :=
    (measurable_of_countable _).aemeasurable
  have hHoleMeas : AEMeasurable
      (fun ω ↦ (holeCount (7 * k) k ω : ℝ≥0∞)) μ :=
    (measurable_of_countable _).aemeasurable
  let BadEdge : Set (Set (Sym2 (Fin (7 * k)))) :=
    {ω | ((6272 * k : ℕ) : ℝ≥0∞) / 2 < randomEdgeCount (7 * k) ω}
  let BadHole : Set (Set (Sym2 (Fin (7 * k)))) :=
    {ω | 0 < holeCount (7 * k) k ω}
  have hBadEdge : μ BadEdge ≤ (1 / 4 : ℝ≥0∞) := by
    simpa [BadEdge] using markov_quarter μ hEdgeMeas hEX
  have hBadHole : μ BadHole < (1 / 4 : ℝ≥0∞) := by
    simpa [BadHole] using positive_nat_markov μ hHoleMeas hEY
  have hUnionLt : μ (BadEdge ∪ BadHole) < 1 :=
    measure_union_lt_one μ hBadEdge hBadHole
  have hUnionMeas : MeasurableSet (BadEdge ∪ BadHole) :=
    (Set.to_countable _).measurableSet
  let Good : Set (Set (Sym2 (Fin (7 * k)))) := (BadEdge ∪ BadHole)ᶜ
  have hGood_ne_zero : μ Good ≠ 0 := by
    intro hzero
    have hsum : μ (BadEdge ∪ BadHole) + μ Good = 1 := by
      simpa [μ, Good] using (measure_add_measure_compl (μ := μ) hUnionMeas)
    rw [hzero, add_zero] at hsum
    exact (not_lt_of_ge hsum.ge) hUnionLt
  obtain ⟨ω, hω⟩ := MeasureTheory.nonempty_of_measure_ne_zero hGood_ne_zero
  have hωnot : ω ∉ BadEdge ∪ BadHole := by simpa [Good] using hω
  have hedge_enn : (randomEdgeCount (7 * k) ω : ℝ≥0∞) ≤
      ((3136 * k : ℕ) : ℝ≥0∞) := by
    have hle : (randomEdgeCount (7 * k) ω : ℝ≥0∞) ≤
        ((6272 * k : ℕ) : ℝ≥0∞) / 2 := by
      exact le_of_not_gt (fun h ↦ hωnot (Or.inl h))
    convert hle using 1
    have hcast1 : ((3136 * k : ℕ) : ℝ≥0∞) =
        (3136 : ℝ≥0∞) * (k : ℝ≥0∞) := by exact_mod_cast (Nat.cast_mul 3136 k)
    have hcast2 : ((6272 * k : ℕ) : ℝ≥0∞) =
        (6272 : ℝ≥0∞) * (k : ℝ≥0∞) := by exact_mod_cast (Nat.cast_mul 6272 k)
    rw [hcast1, hcast2]
    change (3136 : ℝ≥0∞) * (k : ℝ≥0∞) =
      ((6272 : ℝ≥0∞) * (k : ℝ≥0∞)) / 2
    have hc : (3136 : ℝ≥0∞) = 6272 * (2 : ℝ≥0∞)⁻¹ := by
      have hnn : (3136 : NNReal) = 6272 * (2 : NNReal)⁻¹ := by norm_num
      simpa using congrArg (fun x : NNReal ↦ (x : ℝ≥0∞)) hnn
    rw [div_eq_mul_inv]
    calc
      (3136 : ℝ≥0∞) * k = k * 3136 := mul_comm _ _
      _ = k * (6272 * (2 : ℝ≥0∞)⁻¹) := by rw [hc]
      _ = 6272 * k * (2 : ℝ≥0∞)⁻¹ := by ac_rfl
  have hedge_nat : randomEdgeCount (7 * k) ω ≤ 3136 * k := by exact_mod_cast hedge_enn
  have hhole_zero : holeCount (7 * k) k ω = 0 := by
    exact Nat.eq_zero_of_not_pos (fun h ↦ hωnot (Or.inr h))
  let H : SimpleGraph (Fin (7 * k)) := SimpleGraph.fromEdgeSet ω
  refine ⟨H, ?_, ?_⟩
  · simpa [H, randomEdgeCount_eq_card_edgeSet] using hedge_nat
  · intro A B hA hB hAB
    obtain ⟨a, ha, b, hb, he⟩ :=
      (holeCount_eq_zero_iff (7 * k) k ω).1 hhole_zero A B hA hB hAB
    have hne : a ≠ b := by
      simpa using crossEdgeFinset_subset_diagCompl hAB
        (mem_crossEdgeFinset_iff.mpr ⟨a, ha, b, hb, rfl⟩)
    exact ⟨a, ha, b, hb, by simpa [H, SimpleGraph.fromEdgeSet_adj] using And.intro he hne⟩

end Erdos720
