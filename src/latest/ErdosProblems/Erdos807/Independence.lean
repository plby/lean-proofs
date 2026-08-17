import ErdosProblems.Erdos807.Probability
import ErdosProblems.Erdos807.Parameters

/-!
# Independence-number estimates for Erdős Problem 807

This file proves the first-moment estimate for independent sets in the
uniform labelled random graph.  The threshold is deliberately taken to be
`ceil (2.001 log₂ n)`: the small margin above the sharp leading constant `2`
is enough to make the first-moment bound tend to zero.
-/

open Filter Finset
open scoped Topology ENNReal

noncomputable section

namespace Erdos807

/-- A finite set of vertices is independent exactly when the graph avoids all
edge coordinates internal to that set. -/
lemma isIndepSet_iff_avoids_internalEdges {n : ℕ}
    (S : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    G.IsIndepSet (S : Set (Fin n)) ↔
      RandomGraph.Avoids (Erdos565.RandomGraph.internalEdges S) G := by
  rw [RandomGraph.Avoids, Finset.disjoint_left]
  constructor
  · intro hInd e heS heG
    rw [Erdos565.RandomGraph.internalEdges] at heS
    rcases Finset.mem_image.mp heS with ⟨f, _hf, rfl⟩
    rcases f with ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | _ p q =>
      have hpq : (p : Fin n) ≠ q := by
        simpa [Sym2.mk_isDiag_iff] using hz
      have hadj : G.Adj p q := by
        rw [RandomGraph.mem_edges] at heG
        change s((p : Fin n), (q : Fin n)) ∈ G.edgeSet at heG
        exact (SimpleGraph.mem_edgeSet G).mp heG
      exact hInd p.property q.property hpq hadj
  · intro hAvoid u hu v hv huv huvG
    let e : Erdos565.RandomGraph.Edge (Fin n) :=
      ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff]⟩
    have heS : e ∈ Erdos565.RandomGraph.internalEdges S := by
      rw [Erdos565.RandomGraph.internalEdges]
      let f : Erdos565.RandomGraph.Edge S :=
        ⟨s(⟨u, hu⟩, ⟨v, hv⟩), by simpa [Sym2.mk_isDiag_iff] using huv⟩
      apply Finset.mem_image.mpr
      refine ⟨f, Finset.mem_univ f, ?_⟩
      apply Subtype.ext
      change Sym2.map Subtype.val s(⟨u, hu⟩, ⟨v, hv⟩) = s(u, v)
      rw [Sym2.map_mk]
    have heG : e ∈ RandomGraph.edges G := by
      rw [RandomGraph.mem_edges]
      exact (SimpleGraph.mem_edgeSet G).mpr huvG
    exact (hAvoid heS) heG

/-- Having independence number at least `t` is equivalent to containing an
independent `t`-element vertex set. -/
lemma indepNum_ge_iff_exists_indepSet {n t : ℕ} (G : SimpleGraph (Fin n)) :
    t ≤ G.indepNum ↔
      ∃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
        G.IsIndepSet (S : Set (Fin n)) := by
  constructor
  · intro ht
    obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (hS.2 ▸ ht)
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hTcard⟩, ?_⟩
    exact hS.1.mono (fun _ hx ↦ hTS hx)
  · rintro ⟨S, hS, hInd⟩
    rw [← (Finset.mem_powersetCard.mp hS).2]
    exact hInd.card_le_indepNum

/-- The exact first-moment/union-bound estimate for the uniform random graph:
there are `n.choose t` possible `t`-sets and every one is independent with
probability `2 ^ (-(t.choose 2))`.
-/
theorem probability_indepNum_ge (n t : ℕ) :
    RandomGraph.probability n (fun G : SimpleGraph (Fin n) ↦ t ≤ G.indepNum) ≤
      (n.choose t : ℝ) * (1 / 2 : ℝ) ^ t.choose 2 := by
  let subsets := (Finset.univ : Finset (Fin n)).powersetCard t
  calc
    RandomGraph.probability n (fun G : SimpleGraph (Fin n) ↦ t ≤ G.indepNum) =
        RandomGraph.probability n (fun G ↦ ∃ S ∈ subsets,
          RandomGraph.Avoids (Erdos565.RandomGraph.internalEdges S) G) := by
      congr 1
      funext G
      apply propext
      rw [indepNum_ge_iff_exists_indepSet]
      apply exists_congr
      intro S
      apply and_congr_right
      intro _hS
      exact isIndepSet_iff_avoids_internalEdges S G
    _ ≤ ∑ S ∈ subsets,
        RandomGraph.probability n
          (RandomGraph.Avoids (Erdos565.RandomGraph.internalEdges S)) :=
      RandomGraph.probability_exists_le_sum subsets _
    _ = ∑ _S ∈ subsets, (1 / 2 : ℝ) ^ t.choose 2 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [RandomGraph.probability_avoids,
        Erdos565.RandomGraph.card_internalEdges]
      rw [(Finset.mem_powersetCard.mp hS).2]
    _ = (n.choose t : ℝ) * (1 / 2 : ℝ) ^ t.choose 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]

/-- The explicit independence-number threshold used below. -/
def independenceThreshold (n : ℕ) : ℕ :=
  Nat.ceil ((2001 / 1000 : ℝ) * Real.logb 2 n)

/-- The real first-moment bound for an independent set of size
`independenceThreshold n`. -/
def independenceFirstMomentBound (n : ℕ) : ℝ :=
  (n.choose (independenceThreshold n) : ℝ) *
    (1 / 2 : ℝ) ^ (independenceThreshold n).choose 2

/-- The exponent obtained after bounding `n.choose r` by `n ^ r` and writing
both factors as real powers of `2`. -/
private def independenceExponent (n : ℕ) : ℝ :=
  independenceThreshold n * Real.logb 2 n -
    independenceThreshold n * (independenceThreshold n - 1) / 2

private theorem independenceExponent_tendsto_atBot :
    Tendsto independenceExponent atTop atBot := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.logb 2 n) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  rw [tendsto_atTop_atBot]
  intro b
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (hlog.eventually_gt_atTop (|b| + 2000000))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hL := hN n hn
  have hceil :
      (2001 / 1000 : ℝ) * Real.logb 2 n ≤
        (independenceThreshold n : ℝ) := by
    exact Nat.le_ceil ((2001 / 1000 : ℝ) * Real.logb 2 n)
  dsimp [independenceExponent]
  cases abs_cases b <;> nlinarith

private theorem independenceFirstMomentBound_le_rpow (n : ℕ) (hn : 1 < n) :
    independenceFirstMomentBound n ≤ (2 : ℝ) ^ independenceExponent n := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hthreshold : 0 < independenceThreshold n := by
    exact Nat.ceil_pos.mpr (mul_pos (by norm_num)
      (Real.logb_pos (by norm_num) hnreal))
  have hbinom :
      (n.choose (independenceThreshold n) : ℝ) ≤
        (2 : ℝ) ^
          ((independenceThreshold n : ℝ) * Real.logb 2 n) := by
    have hpow :
        (n.choose (independenceThreshold n) : ℝ) ≤
          (n : ℝ) ^ independenceThreshold n := by
      exact_mod_cast Nat.choose_le_pow n (independenceThreshold n)
    convert hpow using 1
    rw [mul_comm, Real.rpow_mul] <;> norm_num [hn.le]
    rw [Real.rpow_logb] <;> norm_cast
    linarith
  have hhalf :
      (1 / 2 : ℝ) ^ (independenceThreshold n).choose 2 ≤
        (2 : ℝ) ^
          (-(independenceThreshold n * (independenceThreshold n - 1) / 2 : ℝ)) := by
    norm_num [Nat.choose_two_right]
    rw [Real.rpow_neg] <;> norm_num
    rw [← Real.inv_rpow] <;> norm_num
    rw [← Real.rpow_natCast]
    rw [Nat.cast_div] <;> norm_num
    · rw [Nat.cast_pred hthreshold]
    · exact even_iff_two_dvd.mp (Nat.even_mul_pred_self _)
  calc
    independenceFirstMomentBound n ≤
        (2 : ℝ) ^ ((independenceThreshold n : ℝ) * Real.logb 2 n) *
          (2 : ℝ) ^
            (-(independenceThreshold n * (independenceThreshold n - 1) / 2 : ℝ)) := by
      exact mul_le_mul hbinom hhalf (by positivity) (by positivity)
    _ = (2 : ℝ) ^ independenceExponent n := by
      rw [← Real.rpow_add]
      · apply congrArg (fun x : ℝ ↦ (2 : ℝ) ^ x)
        unfold independenceExponent
        ring
      · norm_num

/-- The first-moment upper bound at the explicit `2.001 log₂ n` threshold
tends to zero. -/
theorem independenceFirstMomentBound_tendsto_zero :
    Tendsto independenceFirstMomentBound atTop (nhds 0) := by
  have hrpow :
      Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ independenceExponent n) atTop (nhds 0) := by
    simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.tendsto_exp_comp_nhds_zero.mpr
      ((Tendsto.const_mul_atBot (by positivity) independenceExponent_tendsto_atBot))
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact independenceFirstMomentBound_le_rpow n hn
  · exact hrpow

/-- At the explicit threshold, the bad-event probability is bounded by the
first moment. -/
theorem probability_indepNum_ge_threshold (n : ℕ) :
    RandomGraph.probability n
        (fun G : SimpleGraph (Fin n) ↦ independenceThreshold n ≤ G.indepNum) ≤
      independenceFirstMomentBound n := by
  exact probability_indepNum_ge n (independenceThreshold n)

/-- The probability that the independence number reaches the threshold tends
to zero. -/
theorem probability_indepNum_ge_threshold_tendsto_zero :
    Tendsto (fun n ↦ RandomGraph.probability n
      (fun G : SimpleGraph (Fin n) ↦ independenceThreshold n ≤ G.indepNum))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ RandomGraph.probability_nonneg n _
  · exact Eventually.of_forall probability_indepNum_ge_threshold
  · exact independenceFirstMomentBound_tendsto_zero

/-- With high probability, the independence number is strictly below the
integer threshold. -/
theorem indepNum_lt_threshold_almostSurely :
    RandomGraph.AlmostSurely
      (fun n G ↦ G.indepNum < independenceThreshold n) := by
  rw [RandomGraph.almostSurely_iff_compl_tendsto_zero]
  simpa only [not_lt] using probability_indepNum_ge_threshold_tendsto_zero

/-- Falling below the ceiling threshold implies the desired real-valued
`2.001 log₂ n` bound, with no rounding loss. -/
theorem indepNum_lt_threshold_le {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.indepNum < independenceThreshold n) :
    (G.indepNum : ℝ) < (2001 / 1000 : ℝ) * Real.logb 2 n := by
  exact Nat.lt_ceil.mp hG

/-- Explicit asymptotically-almost-sure upper bound
`alpha(G) < 2.001 log₂ n`. -/
theorem indepNum_lt_two_point_zero_zero_one_logb_almostSurely :
    RandomGraph.AlmostSurely (fun n G ↦
      (G.indepNum : ℝ) < (2001 / 1000 : ℝ) * Real.logb 2 n) := by
  exact indepNum_lt_threshold_almostSurely.mono
    (Eventually.of_forall fun _n _G hG ↦ indepNum_lt_threshold_le hG)

/-- The real binary logarithm is strictly below the successor of its natural
floor, expressed in the `logParameter` vocabulary used by the structured
construction. -/
theorem logb_lt_logParameter_add_one (n : ℕ) :
    Real.logb 2 n < (logParameter n : ℝ) + 1 := by
  change Real.logb 2 (n : ℝ) < (Nat.log 2 n : ℝ) + 1
  rw [← Real.natFloor_logb_natCast]
  exact Nat.lt_floor_add_one (Real.logb 2 (n : ℝ))

/-- The same whp independence estimate in the integer dyadic-parameter
vocabulary used by the rest of the Problem 807 development. -/
theorem indepNum_lt_two_point_zero_zero_one_logParameter_almostSurely :
    RandomGraph.AlmostSurely (fun n G ↦
      (G.indepNum : ℝ) <
        (2001 / 1000 : ℝ) * ((logParameter n : ℝ) + 1)) := by
  exact indepNum_lt_two_point_zero_zero_one_logb_almostSurely.mono
    (Eventually.of_forall fun n _G hG ↦
      hG.trans (mul_lt_mul_of_pos_left (logb_lt_logParameter_add_one n) (by norm_num)))

end Erdos807
