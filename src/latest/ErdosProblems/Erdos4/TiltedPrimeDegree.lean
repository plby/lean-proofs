import ErdosProblems.Erdos4.TiltedCappedEdges
import ErdosProblems.Erdos4.TiltedExactNormalizer
import ErdosProblems.Erdos4.TiltedPinnedNormalizer
import ErdosProblems.Erdos4.TiltedConditionedWeights
import ErdosProblems.Erdos4.FGKMTInitialDegreeConcentration

/-! Rooted degree concentration and cap loss for the exact prime-edge law. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem subsetWeight_erase (ν : FiniteLaw (Finset V)) (v : V) (E W : Finset V)
    (hq : survival ν {v} ≠ 0) (hvE : v ∈ E) (hvW : v ∈ W) :
    eventWeight (conditionSurvival ν {v}) (fun W => E.erase v ⊆ W) W =
      survival ν {v} * eventWeight ν (fun W => E ⊆ W) W := by
  classical
  have hprob : (conditionSurvival ν {v}).prob (fun W => E.erase v ⊆ W) =
      survival ν E / survival ν {v} := by
    change survival (conditionSurvival ν {v}) (E.erase v) = _
    rw [conditional_survival ν {v} _ hq, Finset.singleton_union, Finset.insert_erase hvE]
  have hsub : E.erase v ⊆ W ↔ E ⊆ W := Finset.erase_subset_iff_of_mem hvW
  by_cases hE : E ⊆ W
  · simp only [eventWeight, hsub, if_pos hE, hprob, survival, one_div_div]
    ring
  · simp only [eventWeight, hsub, if_neg hE, mul_zero]

theorem exactRawDegree_incidence (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (v : V) (W : Finset V) (hq : survival ν {v} ≠ 0)
    (hd : vertexDegree μ v ≠ 0) (hvW : v ∈ W) :
    (survival ν {v} / vertexDegree μ v) * exactRawDegree ν μ v W =
      eventNormalizer (conditionSurvival ν {v}) (erasedIncidence μ v) (fun E W => E ⊆ W) W := by
  classical
  have hsingle (i : I) : (μ i).mean (fun E => if v ∈ E then
      eventWeight (conditionSurvival ν {v}) (fun W => E.erase v ⊆ W) W else 0) =
        survival ν {v} * edgeRawIncidence ν (μ i) v W := by
    calc
      _ = (μ i).mean (fun E => survival ν {v} *
          (if v ∈ E then eventWeight ν (fun W => E ⊆ W) W else 0)) := by
        apply (μ i).mean_congr
        intro E
        by_cases hvE : v ∈ E
        · simp only [if_pos hvE, subsetWeight_erase ν v E W hq hvE hvW]
        · simp only [if_neg hvE, mul_zero]
      _ = _ := (μ i).mean_const_mul _ _
  change _ = (erasedIncidence μ v).mean (fun E =>
    eventWeight (conditionSurvival ν {v}) (fun W => E ⊆ W) W)
  rw [erasedIncidence_mean μ v hd]
  simp only [hsingle, ← Finset.mul_sum, exactRawDegree]
  ring

open Classical in
theorem edgeLostIncidence_eq_mean (ν μ : FiniteLaw (Finset V)) (v : V) (W : Finset V) :
    edgeLostIncidence ν μ v W = μ.mean (fun E => if v ∈ E then
      (if 2 < eventNormalizer ν μ (fun E W => E ⊆ W) W then
        eventWeight ν (fun W => E ⊆ W) W else 0) else 0) := by
  by_cases hcap : 2 < eventNormalizer ν μ (fun E W => E ⊆ W) W
  · simp only [edgeLostIncidence, if_pos hcap, edgeRawIncidence]
  · simp only [edgeLostIncidence, if_neg hcap, ite_self, FiniteLaw.mean_const]

theorem root_edge_cap_mean (ν μ : FiniteLaw (Finset V)) (v : V)
    (hq : survival ν {v} ≠ 0)
    (hpos : ∀ E, 0 < μ.weight E → survival ν E ≠ 0) :
    survival ν {v} * (conditionSurvival ν {v}).mean (edgeLostIncidence ν μ v) =
      μ.mean (fun E => if v ∈ E then (conditionSurvival ν E).prob
        (fun W => 2 < eventNormalizer ν μ (fun E W => E ⊆ W) W) else 0) := by
  classical
  let bad : Finset V → Prop := fun W => 2 < eventNormalizer ν μ (fun E W => E ⊆ W) W
  have heq : (edgeLostIncidence ν μ v) = (fun W => μ.mean (fun E => if v ∈ E then
      (if bad W then eventWeight ν (fun W => E ⊆ W) W else 0) else 0)) :=
    funext (edgeLostIncidence_eq_mean ν μ v)
  rw [heq, mean_swap, ← FiniteLaw.mean_const_mul]
  apply μ.mean_congr_support
  intro E hE
  by_cases hvE : v ∈ E
  · simp only [if_pos hvE]
    have hsupport : ∀ W, ¬({v} : Finset V) ⊆ W →
        (if bad W then eventWeight ν (fun W => E ⊆ W) W else 0) = 0 := by
      intro W hW
      have hEW : ¬E ⊆ W := fun hh => hW (Finset.singleton_subset_iff.mpr (hh hvE))
      simp only [eventWeight, if_neg hEW, ite_self]
    have hm := condition_mean_mul_eq ν (fun W => ({v} : Finset V) ⊆ W) ∅ hq
      (fun W => if bad W then eventWeight ν (fun W => E ⊆ W) W else 0) hsupport
    change survival ν {v} * (conditionSurvival ν {v}).mean _ = _ at hm
    rw [hm, mean_eventWeight_on_event]
    exact (FiniteLaw.condition_prob ν (fun W => E ⊆ W) bad ∅ (hpos E hE)).symm
  · simp only [if_neg hvE, FiniteLaw.mean_const, mul_zero]

theorem exactLostDegree_root_mean_le (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (v : V) (hq : survival ν {v} ≠ 0) (hd : 0 < vertexDegree μ v) {η : ℝ} (_hη : 0 ≤ η)
    (hpos : ∀ i E, 0 < (μ i).weight E → survival ν E ≠ 0)
    (hcap : ∀ i E, 0 < (μ i).weight E → v ∈ E →
      (conditionSurvival ν E).prob (fun W => 2 < eventNormalizer ν (μ i) (fun E W => E ⊆ W) W) ≤ η) :
    (conditionSurvival ν {v}).mean (fun W =>
      (survival ν {v} / vertexDegree μ v) * exactLostDegree ν μ v W) ≤ η := by
  classical
  have heach (i : I) : survival ν {v} * (conditionSurvival ν {v}).mean (edgeLostIncidence ν (μ i) v) ≤
      η * (μ i).prob (fun E => v ∈ E) := by
    rw [root_edge_cap_mean ν (μ i) v hq (hpos i), FiniteLaw.prob_eq_mean, ← FiniteLaw.mean_const_mul]
    apply (μ i).mean_mono_support
    intro E hE
    by_cases hvE : v ∈ E
    · simpa only [if_pos hvE, mul_one] using hcap i E hE hvE
    · simp only [if_neg hvE, mul_zero]
      exact le_rfl
  calc
    _ = (∑ i, survival ν {v} * (conditionSurvival ν {v}).mean (edgeLostIncidence ν (μ i) v)) /
        vertexDegree μ v := by
      rw [FiniteLaw.mean_const_mul]
      unfold exactLostDegree
      rw [FiniteLaw.mean_finset_sum, ← Finset.mul_sum]
      ring
    _ ≤ (∑ i, η * (μ i).prob (fun E => v ∈ E)) / vertexDegree μ v :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => heach i)) hd.le
    _ = η := by rw [← Finset.mul_sum]; change η * vertexDegree μ v / vertexDegree μ v = η; field_simp

theorem pinned_normalizer_cap_probability (ν μ : FiniteLaw (Finset V)) {σ ε δ : ℝ} {r : ℕ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδ : 0 ≤ δ)
    (hacc : SurvivalAccurate ν (fun _ => σ) (3 * r) ε)
    (hsize : ∀ E, 0 < μ.weight E → E.card ≤ r)
    (hsparse : ∀ v, μ.prob (fun E => v ∈ E) ≤ δ)
    (T : Finset V) (hT : T.card ≤ r) :
    (conditionSurvival ν T).prob (fun W => 2 < eventNormalizer ν μ (fun E W => E ⊆ W) W) ≤
      24 * ε + 12 * r * δ / σ ^ (3 * r) := by
  have hsub : (conditionSurvival ν T).prob (fun W => 2 < eventNormalizer ν μ (fun E W => E ⊆ W) W) ≤
      (conditionSurvival ν T).prob (fun W => 1 ≤ |eventNormalizer ν μ (fun E W => E ⊆ W) W - 1|) := by
    apply FiniteLaw.prob_mono
    intro W hW
    have hh := le_abs_self (eventNormalizer ν μ (fun E W => E ⊆ W) W - 1)
    linarith
  have htail := (conditionSurvival ν T).chebyshev
    (eventNormalizer ν μ (fun E W => E ⊆ W)) 1 (by norm_num : (0 : ℝ) < 1)
  simp only [one_pow, div_one] at htail
  exact (hsub.trans htail).trans (pinned_subsetNormalizer_variance ν μ hσ hσ1 hε0 hε hδ hacc hsize hsparse T hT)

theorem capped_degree_lower_tail (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V)) (v : V)
    (hq : 0 < survival ν {v}) (hd : 0 < vertexDegree μ v)
    (hdegree : 32 * survival ν {v} ≤ vertexDegree μ v) {A η : ℝ}
    (hvar : (conditionSurvival ν {v}).mean (fun W =>
      ((survival ν {v} / vertexDegree μ v) * exactRawDegree ν μ v W - 1) ^ 2) ≤ A)
    (hloss : (conditionSurvival ν {v}).mean (fun W =>
      (survival ν {v} / vertexDegree μ v) * exactLostDegree ν μ v W) ≤ η) :
    (conditionSurvival ν {v}).prob (fun W => vertexDegree (fun i => cappedEdgeLaw ν (μ i) W) v < 4) ≤
      4 * A + 4 * η := by
  have hloss0 (W : Finset V) :
      0 ≤ (survival ν {v} / vertexDegree μ v) * exactLostDegree ν μ v W :=
    mul_nonneg (div_nonneg hq.le hd.le)
      (Finset.sum_nonneg (fun i _ => edgeLostIncidence_nonneg ν (μ i) v W))
  have htail := (conditionSurvival ν {v}).retained_degree_lower_tail
    (fun W => (survival ν {v} / vertexDegree μ v) * exactRawDegree ν μ v W)
    (fun W => (survival ν {v} / vertexDegree μ v) * exactLostDegree ν μ v W) hloss0
    (by norm_num : (0 : ℝ) < 1) hvar (by simpa only [mul_one] using hloss)
  simp only [one_pow, div_one] at htail
  apply le_trans (FiniteLaw.prob_mono _ ?_) htail
  intro W hW
  rw [cappedEdgeLaw_degree] at hW
  have hdiff : exactRawDegree ν μ v W - exactLostDegree ν μ v W < 8 := by linarith
  have hscale : (survival ν {v} / vertexDegree μ v) * 8 ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hh := mul_lt_mul_of_pos_left hdiff (div_pos hq hd)
  nlinarith

theorem capped_prime_degree_error (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V)) (v : V)
    {r : ℕ} {σ ε δ : ℝ} (hr : 1 ≤ r) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16) (hδ : 0 ≤ δ)
    (hacc : SurvivalAccurate ν (fun _ => σ) (3 * r) ε)
    (hsize : ∀ i E, 0 < (μ i).weight E → E.card ≤ r)
    (hsparse : ∀ i v, (μ i).prob (fun E => v ∈ E) ≤ δ)
    (hpair : ∀ w, w ≠ v → pairDegree μ v w ≤ δ)
    (hq : survival ν {v} = σ) (hdegree : 32 * σ ≤ vertexDegree μ v) :
    (conditionSurvival ν {v}).prob (fun W => vertexDegree (fun i => cappedEdgeLaw ν (μ i) W) v < 4) ≤
      224 * ε + 64 * r * δ / σ ^ (3 * r) := by
  have hd : 0 < vertexDegree μ v := (by positivity : 0 < 32 * σ).trans_le hdegree
  have hqpos : 0 < survival ν {v} := hq ▸ hσ
  have hvar := rooted_incidence_variance ν μ v hr hσ hσ1 hε0 hε hδ hacc hsize hd hpair
  have hvar' : (conditionSurvival ν {v}).mean (fun W =>
      ((survival ν {v} / vertexDegree μ v) * exactRawDegree ν μ v W - 1) ^ 2) ≤
        32 * ε + 4 * r * δ / (vertexDegree μ v * σ ^ r) := by
    apply le_of_eq_of_le _ hvar
    apply (conditionSurvival ν {v}).mean_congr_support
    intro W hW
    have hvW : v ∈ W := conditionSurvival_support ν {v} W hqpos.ne' hW (Finset.mem_singleton_self v)
    rw [exactRawDegree_incidence ν μ v W hqpos.ne' hd.ne' hvW]
  have hcap0 : 0 ≤ 24 * ε + 12 * r * δ / σ ^ (3 * r) := by positivity
  have hloss := exactLostDegree_root_mean_le ν μ v hqpos.ne' hd hcap0
    (fun i E hE => (survival_pos_of_accurate ν (fun _ => σ) (fun _ => hσ)
      (by linarith : ε < 1) hacc (by have hh := hsize i E hE; omega)).ne')
    (fun i E hE _ => pinned_normalizer_cap_probability ν (μ i) hσ hσ1 hε0
      (by linarith : ε ≤ 1 / 4) hδ hacc (hsize i) (hsparse i) E (hsize i E hE))
  have ht := capped_degree_lower_tail ν μ v hqpos hd (by simpa only [hq] using hdegree) hvar' hloss
  have hden : σ ^ (3 * r) ≤ vertexDegree μ v * σ ^ r := by
    calc
      _ ≤ σ ^ (r + 1) := pow_le_pow_of_le_one hσ.le hσ1 (by omega)
      _ = σ * σ ^ r := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : σ ≤ vertexDegree μ v) (by positivity)
  have hfrac : 4 * r * δ / (vertexDegree μ v * σ ^ r) ≤ 4 * r * δ / σ ^ (3 * r) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  apply ht.trans
  calc
    _ ≤ 4 * (32 * ε + 4 * r * δ / σ ^ (3 * r)) +
        4 * (24 * ε + 12 * r * δ / σ ^ (3 * r)) := by gcongr
    _ = _ := by ring

end Erdos4.Tilted
