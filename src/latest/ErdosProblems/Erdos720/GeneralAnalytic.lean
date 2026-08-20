import ErdosProblems.Erdos720.CycleRamsey
import ErdosProblems.Erdos720.Analytic

open Filter Finset
open MeasureTheory ProbabilityTheory unitInterval
open scoped SimpleGraph Topology ENNReal

noncomputable section

namespace Erdos720

open SimpleGraph

lemma hole_real_bound_linear (C N k : ℕ) (hC : 1 ≤ C)
    (hk : 2 * C + 2 ≤ k) (hN : N ≤ C * k) :
    (Nat.choose N k : ℝ) ^ 2 *
        (1 - ((2 * C + 2 : ℕ) : ℝ) / k) ^ (k * k) < 1 / 4 := by
  have hkpos : 0 < k := by omega
  have hAk : 2 * C + 2 ≤ k := hk
  have hbase_nonneg : 0 ≤ 1 - ((2 * C + 2 : ℕ) : ℝ) / k := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hkpos : (0 : ℝ) < k)]
    exact_mod_cast hAk
  have hblock :
      (1 - ((2 * C + 2 : ℕ) : ℝ) / k) ^ k ≤
        Real.exp (-((2 * C + 2 : ℕ) : ℝ)) := by
    exact Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hAk)
  have hApos : 0 < 2 * C + 2 := by omega
  have hexp : Real.exp (-((2 * C + 2 : ℕ) : ℝ)) <
      (1 / 2 : ℝ) ^ (2 * C + 2) := by
    have h1 : Real.exp (-1) < (1 / 2 : ℝ) := Real.exp_neg_one_lt_half
    have hp := pow_lt_pow_left₀ h1 (Real.exp_pos (-1)).le hApos.ne'
    rw [← Real.exp_nat_mul] at hp
    have heq : -((2 * C + 2 : ℕ) : ℝ) =
        ((2 * C + 2 : ℕ) : ℝ) * (-1) := by ring
    rw [heq]
    exact hp
  have hhole :
      (1 - ((2 * C + 2 : ℕ) : ℝ) / k) ^ (k * k) <
        (((1 / 2 : ℝ) ^ (2 * C + 2)) ^ k) := by
    rw [pow_mul]
    exact pow_lt_pow_left₀ (lt_of_le_of_lt hblock hexp)
      (pow_nonneg hbase_nonneg k) hkpos.ne'
  have hchooseNat : Nat.choose N k ≤ 2 ^ (C * k) := by
    exact (Nat.choose_le_two_pow N k).trans (Nat.pow_le_pow_right (by omega) hN)
  have hchoose : (Nat.choose N k : ℝ) ≤ (2 : ℝ) ^ (C * k) := by
    exact_mod_cast hchooseNat
  have hchoose_sq : (Nat.choose N k : ℝ) ^ 2 ≤
      ((2 : ℝ) ^ (2 * C)) ^ k := by
    calc
      (Nat.choose N k : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (C * k)) ^ 2 := by gcongr
      _ = ((2 : ℝ) ^ (2 * C)) ^ k := by
        simp only [← pow_mul]
        congr 1
        ac_rfl
  have hbase : (2 : ℝ) ^ (2 * C) * (1 / 2 : ℝ) ^ (2 * C + 2) = 1 / 4 := by
    rw [pow_add, one_div, inv_pow]
    have hpne : (2 : ℝ) ^ (2 * C) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [← mul_assoc, mul_inv_cancel₀ hpne]
    norm_num
  calc
    (Nat.choose N k : ℝ) ^ 2 *
          (1 - ((2 * C + 2 : ℕ) : ℝ) / k) ^ (k * k)
        < ((2 : ℝ) ^ (2 * C)) ^ k *
            (((1 / 2 : ℝ) ^ (2 * C + 2)) ^ k) := by
          exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hchoose_sq (pow_nonneg hbase_nonneg _))
            (mul_lt_mul_of_pos_left hhole (pow_pos (by positivity) _))
    _ = (1 / 4 : ℝ) ^ k := by rw [← mul_pow, hbase]
    _ ≤ 1 / 4 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)

/-- A parameterized first-moment construction of a sparse graph with no
empty `k`-by-`k` bipartite hole. -/
lemma exists_sparse_noHole_graph_linear (C N k : ℕ) (hC : 1 ≤ C)
    (hk : 2 * C + 2 ≤ k) (hN : N ≤ C * k) :
    ∃ H : SimpleGraph (Fin N),
      Nat.card H.edgeSet ≤ 4 * ((2 * C + 2) * C * C) * k ∧
      ∀ X Y : Finset (Fin N), X.card = k → Y.card = k → Disjoint X Y →
        ∃ x ∈ X, ∃ y ∈ Y, H.Adj x y := by
  classical
  have hkpos : 0 < k := by omega
  let p : I := ⟨((2 * C + 2 : ℕ) : ℝ) / k, by positivity, by
    rw [div_le_one (by exact_mod_cast hkpos : (0 : ℝ) < k)]
    exact_mod_cast hk⟩
  let μ : Measure (Set (Sym2 (Fin N))) :=
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
  have hp_real : ((toNNReal p : NNReal) : ℝ) = ((2 * C + 2 : ℕ) : ℝ) / k := by
    simp [p]
  have hs_real : ((toNNReal (σ p) : NNReal) : ℝ) =
      1 - ((2 * C + 2 : ℕ) : ℝ) / k := by
    have hsum : ((toNNReal (σ p) : NNReal) : ℝ) +
        ((2 * C + 2 : ℕ) : ℝ) / k = 1 := by
      simpa [p] using congrArg (fun x : NNReal ↦ (x : ℝ)) (unitInterval.toNNReal_symm_add p)
    linarith
  let E : ℕ := (2 * C + 2) * C * C * k
  have hedge_real :
      (Nat.choose N 2 : ℝ) * (((2 * C + 2 : ℕ) : ℝ) / k) ≤ E := by
    have hcNat : Nat.choose N 2 ≤ N ^ 2 := Nat.choose_le_pow _ _
    have hc : (Nat.choose N 2 : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcNat
    have hNr : (N : ℝ) ≤ C * k := by exact_mod_cast hN
    calc
      (Nat.choose N 2 : ℝ) * (((2 * C + 2 : ℕ) : ℝ) / k)
          ≤ (N : ℝ) ^ 2 * (((2 * C + 2 : ℕ) : ℝ) / k) := by
            gcongr
      _ ≤ ((C : ℝ) * k) ^ 2 * (((2 * C + 2 : ℕ) : ℝ) / k) := by
            gcongr
      _ = E := by
        dsimp [E]
        push_cast
        field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast hkpos.ne']
  have hEX0 :
      ∫⁻ ω, (randomEdgeCount N ω : ℝ≥0∞) ∂μ ≤ (E : ℝ≥0∞) := by
    rw [show μ = setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) from rfl,
      randomEdgeCount_lintegral_eq]
    have hp_enn : ((toNNReal p : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal (((2 * C + 2 : ℕ) : ℝ) / k) := by
      rw [ENNReal.coe_nnreal_eq]
      simpa [hp_real]
    rw [← ENNReal.ofReal_natCast, hp_enn,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Nat.choose N 2 : ℝ))]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hedge_real
  have hscale8 : (8 : ℝ≥0∞) * (E : ℝ≥0∞) / 8 = (E : ℝ≥0∞) := by
    rw [div_eq_mul_inv]
    have hc : (8 : ℝ≥0∞) * (8 : ℝ≥0∞)⁻¹ = 1 := by
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      (8 : ℝ≥0∞) * E * (8 : ℝ≥0∞)⁻¹ = E * (8 * (8 : ℝ≥0∞)⁻¹) := by ac_rfl
      _ = E := by rw [hc, mul_one]
  have hEX :
      ∫⁻ ω, (randomEdgeCount N ω : ℝ≥0∞) ∂μ ≤
        ((8 : ℝ≥0∞) * (E : ℝ≥0∞)) / 8 := by
    rwa [hscale8]
  have hEY :
      ∫⁻ ω, (holeCount N k ω : ℝ≥0∞) ∂μ < 1 / 4 := by
    refine lt_of_le_of_lt (by simpa [μ] using holeCount_lintegral_le N k p) ?_
    have hs_enn : ((toNNReal (σ p) : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal (1 - ((2 * C + 2 : ℕ) : ℝ) / k) := by
      rw [ENNReal.coe_nnreal_eq]
      simpa [hs_real]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity) 2,
      hs_enn, ← ENNReal.ofReal_pow (by
        rw [sub_nonneg, div_le_one (by exact_mod_cast hkpos : (0 : ℝ) < k)]
        exact_mod_cast hk) (k * k),
      ← ENNReal.ofReal_mul (sq_nonneg (Nat.choose N k : ℝ))]
    have hbound := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)).2
      (hole_real_bound_linear C N k hC hk hN)
    simpa using hbound
  have hEdgeMeas : AEMeasurable
      (fun ω ↦ (randomEdgeCount N ω : ℝ≥0∞)) μ :=
    (measurable_of_countable _).aemeasurable
  have hHoleMeas : AEMeasurable
      (fun ω ↦ (holeCount N k ω : ℝ≥0∞)) μ :=
    (measurable_of_countable _).aemeasurable
  let BadEdge : Set (Set (Sym2 (Fin N))) :=
    {ω | ((8 : ℝ≥0∞) * (E : ℝ≥0∞)) / 2 < randomEdgeCount N ω}
  let BadHole : Set (Set (Sym2 (Fin N))) := {ω | 0 < holeCount N k ω}
  have hBadEdge : μ BadEdge ≤ (1 / 4 : ℝ≥0∞) := by
    simpa [BadEdge] using markov_quarter μ hEdgeMeas hEX
  have hBadHole : μ BadHole < (1 / 4 : ℝ≥0∞) := by
    simpa [BadHole] using positive_nat_markov μ hHoleMeas hEY
  have hUnionLt : μ (BadEdge ∪ BadHole) < 1 :=
    measure_union_lt_one μ hBadEdge hBadHole
  have hUnionMeas : MeasurableSet (BadEdge ∪ BadHole) :=
    (Set.to_countable _).measurableSet
  let Good : Set (Set (Sym2 (Fin N))) := (BadEdge ∪ BadHole)ᶜ
  have hGood_ne_zero : μ Good ≠ 0 := by
    intro hzero
    have hsum : μ (BadEdge ∪ BadHole) + μ Good = 1 := by
      simpa [μ, Good] using (measure_add_measure_compl (μ := μ) hUnionMeas)
    rw [hzero, add_zero] at hsum
    exact (not_lt_of_ge hsum.ge) hUnionLt
  obtain ⟨ω, hω⟩ := MeasureTheory.nonempty_of_measure_ne_zero hGood_ne_zero
  have hωnot : ω ∉ BadEdge ∪ BadHole := by simpa [Good] using hω
  have hscale2 : (8 : ℝ≥0∞) * (E : ℝ≥0∞) / 2 =
      (4 : ℝ≥0∞) * (E : ℝ≥0∞) := by
    rw [div_eq_mul_inv]
    have hc : (8 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 4 := by
      have hc2 : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      calc
        (8 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ =
            ((4 : ℝ≥0∞) * 2) * (2 : ℝ≥0∞)⁻¹ := by norm_num
        _ = 4 * ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) := by rw [mul_assoc]
        _ = 4 := by rw [hc2, mul_one]
    calc
      (8 : ℝ≥0∞) * E * (2 : ℝ≥0∞)⁻¹ = E * (8 * (2 : ℝ≥0∞)⁻¹) := by ac_rfl
      _ = 4 * E := by rw [hc]; ac_rfl
  have hedge_enn : (randomEdgeCount N ω : ℝ≥0∞) ≤
      ((4 * E : ℕ) : ℝ≥0∞) := by
    have hle : (randomEdgeCount N ω : ℝ≥0∞) ≤
        ((8 : ℝ≥0∞) * (E : ℝ≥0∞)) / 2 :=
      le_of_not_gt (fun h ↦ hωnot (Or.inl h))
    rw [hscale2] at hle
    exact_mod_cast hle
  have hedge_nat : randomEdgeCount N ω ≤ 4 * E := by exact_mod_cast hedge_enn
  have hhole_zero : holeCount N k ω = 0 :=
    Nat.eq_zero_of_not_pos (fun h ↦ hωnot (Or.inr h))
  let H : SimpleGraph (Fin N) := SimpleGraph.fromEdgeSet ω
  refine ⟨H, ?_, ?_⟩
  · simpa [H, E, randomEdgeCount_eq_card_edgeSet, mul_assoc] using hedge_nat
  · intro X Y hX hY hXY
    obtain ⟨x, hx, y, hy, he⟩ :=
      (holeCount_eq_zero_iff N k ω).1 hhole_zero X Y hX hY hXY
    have hne : x ≠ y := by
      simpa using crossEdgeFinset_subset_diagCompl hXY
        (mem_crossEdgeFinset_iff.mpr ⟨x, hx, y, hy, rfl⟩)
    exact ⟨x, hx, y, hy, by simpa [H, SimpleGraph.fromEdgeSet_adj] using And.intro he hne⟩

end Erdos720
