import ErdosProblems.Erdos4.TiltedPrimeDegree
import ErdosProblems.Erdos4.FGKMTGrowingPrimeCovering

/-! Expected exceptional-prime counts and a covering valid at every sieve outcome. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

open Classical in
noncomputable def primeBadSet (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (bad : Finset V) (W : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∈ W ∧
    (v ∈ bad ∨ vertexDegree (fun i => cappedEdgeLaw ν (μ i) W) v < 4))

theorem primeBadSet_subset (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (bad W : Finset V) : primeBadSet ν μ bad W ⊆ W := by
  intro v hv
  exact (Finset.mem_filter.mp hv).2.1

theorem mean_primeBadSet_le (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (bad : Finset V) {σ η : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η)
    (hsingle : ∀ v, survival ν {v} = σ)
    (hbad : ∀ v, v ∉ bad → (conditionSurvival ν {v}).prob
      (fun W => vertexDegree (fun i => cappedEdgeLaw ν (μ i) W) v < 4) ≤ η) :
    ν.mean (fun W => ((primeBadSet ν μ bad W).card : ℝ)) ≤
      σ * ((bad.card : ℝ) + η * Fintype.card V) := by
  classical
  let E : V → Finset V → Prop := fun v W =>
    v ∈ bad ∨ vertexDegree (fun i => cappedEdgeLaw ν (μ i) W) v < 4
  have hq (v : V) : ν.prob (fun W => v ∈ W ∧ E v W) =
      σ * (conditionSurvival ν {v}).prob (E v) := by
    have hp : ν.prob (fun W => ({v} : Finset V) ⊆ W) = σ := hsingle v
    rw [conditionSurvival, FiniteLaw.condition_prob ν (fun W => ({v} : Finset V) ⊆ W)
      (E v) ∅ (hp.trans_ne hσ.ne'), hp]
    have heq : (fun W => ({v} : Finset V) ⊆ W ∧ E v W) = (fun W => v ∈ W ∧ E v W) := by
      funext W
      exact propext (by simp only [Finset.singleton_subset_iff])
    rw [heq]
    field_simp
  have hper (v : V) : (conditionSurvival ν {v}).prob (E v) ≤ (if v ∈ bad then (1 : ℝ) else 0) + η := by
    by_cases hv : v ∈ bad
    · rw [if_pos hv]
      exact ((conditionSurvival ν {v}).prob_le_one _).trans (by linarith)
    · rw [if_neg hv, zero_add]
      have heq : E v = (fun W => vertexDegree (fun i => cappedEdgeLaw ν (μ i) W) v < 4) := by
        funext W
        exact propext (by simp only [E, hv, false_or])
      rw [heq]
      exact hbad v hv
  unfold primeBadSet
  rw [FiniteLaw.mean_filter_card]
  change (∑ v, ν.prob (fun W => v ∈ W ∧ E v W)) ≤ _
  simp_rw [hq]
  calc
    _ ≤ ∑ v, σ * ((if v ∈ bad then (1 : ℝ) else 0) + η) :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hper v) hσ.le)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole]
      have heq : Finset.univ.filter (fun v : V => v ∈ bad) = bad := by ext v; simp
      rw [heq]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm η]

theorem mean_survivor_card (ν : FiniteLaw (Finset V)) {σ : ℝ}
    (hsingle : ∀ v, survival ν {v} = σ) :
    ν.mean (fun W => (W.card : ℝ)) = σ * Fintype.card V := by
  classical
  have heq (W : Finset V) : Finset.univ.filter (fun v => v ∈ W) = W := by ext v; simp
  have hh := ν.mean_filter_card (fun W (v : V) => v ∈ W)
  simp only [heq] at hh
  rw [hh]
  have hp (v : V) : ν.prob (fun W => v ∈ W) = σ := by
    have h := hsingle v
    unfold survival at h
    simpa only [Finset.singleton_subset_iff] using h
  simp only [hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm σ]

noncomputable def primeCoverCost (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (bad : Finset V) (κ : ℝ) (W : Finset V) : ℝ :=
  (primeBadSet ν μ bad W).card + 2 * κ * W.card

theorem primeCoverCost_nonneg (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (bad : Finset V) {κ : ℝ} (hκ : 0 ≤ κ) (W : Finset V) : 0 ≤ primeCoverCost ν μ bad κ W := by
  unfold primeCoverCost
  positivity

theorem mean_primeCoverCost_le (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (bad : Finset V) {σ η κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (_hκ : 0 ≤ κ)
    (hsingle : ∀ v, survival ν {v} = σ)
    (hbad : ∀ v, v ∉ bad → (conditionSurvival ν {v}).prob
      (fun W => vertexDegree (fun i => cappedEdgeLaw ν (μ i) W) v < 4) ≤ η) :
    ν.mean (primeCoverCost ν μ bad κ) ≤
      σ * ((bad.card : ℝ) + η * Fintype.card V) + 2 * κ * (σ * Fintype.card V) := by
  unfold primeCoverCost
  rw [FiniteLaw.mean_add, FiniteLaw.mean_const_mul, mean_survivor_card ν hsingle]
  exact add_le_add (mean_primeBadSet_le ν μ bad hσ hη hsingle hbad) le_rfl

theorem source_cover_with_bad_vertices (sources targets : Finset ℕ)
    (μ : sources → FiniteLaw (Finset targets)) (W bad : Finset targets)
    (hbad : bad ⊆ W) {m r : ℕ} (hr : 1 ≤ r) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hεδ : ε ≤ δ)
    (hdegree : ∀ v ∈ W \ bad, 4 ≤ vertexDegree μ v)
    (hmarginal : ∀ i v, (μ i).prob (fun E => v ∈ E) ≤ ε)
    (hsquare : (sources.card : ℝ) * ε ^ 2 ≤ δ ^ 2)
    (hpair : ∀ v w, v ≠ w → pairDegree μ v w ≤ δ)
    (hlegal : ∀ i E, 0 < (μ i).weight E → E.card ≤ r ∧
      ∃ b : ZMod i.val, ∀ v ∈ E, (v.val : ZMod i.val) = b)
    (hpartition : (m : ℝ) * targets.card * Real.exp (-((1 / 2 : ℝ) ^ m) / (6 * ε)) < 1)
    (hsparse : δ ≤ coveringThreshold r (2 * r) ((1 / 2 : ℝ) ^ m)
      (-Real.log (1 / 2 : ℝ)) ^ (4 * 8 ^ m)) :
    ∃ b : ∀ p : sources, ZMod p.val,
      ((sourceSurvivors sources targets W b).card : ℝ) ≤
        (bad.card : ℝ) + 2 * W.card * (1 / 2 : ℝ) ^ m := by
  classical
  let G := W \ bad
  let laws : sources → FiniteLaw (Finset G) := fun i => (μ i).restrictVertices G
  have hGcard : (Fintype.card G : ℝ) ≤ targets.card := by
    simp only [Fintype.card_coe]
    exact_mod_cast (show G.card ≤ targets.card by simpa only [Fintype.card_coe] using Finset.card_le_univ G)
  have hpart : (m : ℝ) * Fintype.card G * Real.exp (-((1 / 2 : ℝ) ^ m) / (6 * ε)) < 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGcard (Nat.cast_nonneg m))
      (Real.exp_nonneg _)).trans_lt hpartition
  have hνdegree : ∀ v : G, 4 ≤ vertexDegree laws v := by
    intro v
    simp only [vertexDegree, laws, FiniteLaw.restrictVertices_vertex]
    exact hdegree v.val v.property
  have hνlegal : ∀ i E, 0 < (laws i).weight E → E.card ≤ r ∧
      ∃ b : ZMod i.val, ∀ v ∈ E, (v.val.val : ZMod i.val) = b := by
    intro i E hE
    obtain ⟨F, hF, hFE⟩ := FiniteLaw.restrictVertices_support (μ i) G E hE
    obtain ⟨hsize, b, hb⟩ := hlegal i F hF
    refine ⟨?_, b, ?_⟩
    · rw [← hFE]
      exact (restrictedVertexEdge_card_le G F).trans hsize
    · intro v hv
      exact hb v.val ((mem_restrictedVertexEdge G F v).mp (hFE ▸ hv))
  obtain ⟨choice, hchoice, hcard⟩ := source_covering (m := m) (r := r) laws hr hε hδ hεδ
    hνdegree (fun i E hE => (hνlegal i E hE).1)
    (fun i v => by simpa only [laws, FiniteLaw.restrictVertices_vertex] using hmarginal i v.val)
    (by simpa only [Fintype.card_coe] using hsquare)
    (fun v w hvw => by
      simp only [pairDegree, laws, FiniteLaw.restrictVertices_pair]
      exact hpair v.val w.val (fun hh => hvw (Subtype.ext hh))) hpart hsparse
  have hresidue : ∀ p : sources, ∃ b : ZMod p.val,
      ∀ v ∈ choice p, (v.val.val : ZMod p.val) = b := by
    intro p
    rcases hchoice p with hz | ⟨E, hE, hsub⟩
    · exact ⟨0, by simp [hz]⟩
    · obtain ⟨b, hb⟩ := (hνlegal p E hE).2
      exact ⟨b, fun v hv => hb v (hsub hv)⟩
  choose b hb using hresidue
  have hdiff : W \ G = bad := by
    ext v
    simp only [G, Finset.mem_sdiff]
    constructor
    · rintro ⟨hvW, hv⟩
      by_contra hvbad
      exact hv ⟨hvW, hvbad⟩
    · intro hv
      exact ⟨hbad hv, fun hh => hh.2 hv⟩
  refine ⟨b, ?_⟩
  have hh : ((sourceSurvivors sources targets W b).card : ℝ) ≤
      ((W \ G).card : ℝ) + ((Finset.univ \ Finset.univ.biUnion choice).card : ℝ) := by
    exact_mod_cast sourceSurvivors_card_le sources targets W G choice b hb
  rw [hdiff] at hh
  apply hh.trans
  apply add_le_add le_rfl
  apply hcard.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hcount : (Fintype.card G : ℝ) ≤ (W.card : ℝ) := by
    simpa only [Fintype.card_coe] using
      (Nat.cast_le.mpr (Finset.card_le_card (Finset.sdiff_subset : G ⊆ W)) : (G.card : ℝ) ≤ W.card)
  exact mul_le_mul_of_nonneg_left hcount (by norm_num)

end Erdos4.Tilted
