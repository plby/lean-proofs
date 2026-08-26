import ErdosProblems.Erdos547.StrictReducedDegrees

/-!
# Uniform cluster and order thresholds
-/

namespace Erdos547

theorem exists_embedding_cluster_lower {a : ℝ} (k : EmbeddingConstants a) (ha : 0 < a) :
    ∃ l : ℕ, 1 ≤ l ∧ 32 ≤ a * l ∧ 8 ≤ k.slack * k.treeEta * l := by
  obtain ⟨l, hl⟩ := exists_nat_ge (max 1 (max (32 / a) (8 / (k.slack * k.treeEta))))
  have hone : (1 : ℝ) ≤ l := (le_max_left _ _).trans hl
  have ha' : 32 / a ≤ l := ((le_max_left _ _).trans (le_max_right _ _)).trans hl
  have hk' : 8 / (k.slack * k.treeEta) ≤ l :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hl
  refine ⟨l, by exact_mod_cast hone, ?_, ?_⟩
  · have hh := (div_le_iff₀ ha).mp ha'
    nlinarith only [hh]
  · have hh := (div_le_iff₀ (mul_pos k.slack_pos k.treeEta_pos)).mp hk'
    nlinarith only [hh]

theorem exists_embedding_order_threshold {a : ℝ} (k : EmbeddingConstants a)
    (ha : 0 < a) (B : ℝ) (hB : 0 < B) (K nCoat nReg : ℕ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ nCoat ≤ n₀ ∧ 4 * nReg ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → 8 ≤ a * n ∧
        ∀ m : ℝ, (n : ℝ) ≤ 8 * B * m → (K : ℝ) ≤ k.epsilon * m ∧ 2 ≤ k.beta * m := by
  let bound : ℝ := 8 / a + 8 * B * ((K : ℝ) / k.epsilon + 2 / k.beta)
  let n₀ := max nCoat (max (4 * nReg) (max 1 (Nat.ceil bound)))
  have hCoat : nCoat ≤ n₀ := le_max_left _ _
  have hReg : 4 * nReg ≤ n₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hone : 1 ≤ n₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hceil : Nat.ceil bound ≤ n₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨n₀, hone, hCoat, hReg, ?_⟩
  intro n hn
  have hbound : bound ≤ (n : ℝ) := (Nat.le_ceil bound).trans (by exact_mod_cast hceil.trans hn)
  have hfrac : 0 ≤ 8 / a := div_nonneg (by norm_num) ha.le
  have hseed : 0 ≤ (K : ℝ) / k.epsilon := div_nonneg (by positivity) k.epsilon_pos.le
  have hres : 0 ≤ 2 / k.beta := div_nonneg (by norm_num) k.beta_pos.le
  have hsprod := mul_nonneg (show 0 ≤ 8 * B by positivity) hseed
  have hrprod := mul_nonneg (show 0 ≤ 8 * B by positivity) hres
  have hage : 8 / a ≤ (n : ℝ) := by dsimp only [bound] at hbound; nlinarith only [hbound, hsprod, hrprod]
  constructor
  · have hh := (div_le_iff₀ ha).mp hage
    nlinarith only [hh]
  · intro m hm
    have hseedn : 8 * B * ((K : ℝ) / k.epsilon) ≤ (n : ℝ) := by
      dsimp only [bound] at hbound
      nlinarith only [hbound, hfrac, hrprod]
    have hresn : 8 * B * (2 / k.beta) ≤ (n : ℝ) := by
      dsimp only [bound] at hbound
      nlinarith only [hbound, hfrac, hsprod]
    have hseedm : (K : ℝ) / k.epsilon ≤ m :=
      (mul_le_mul_iff_of_pos_left (show 0 < 8 * B by positivity)).mp (hseedn.trans hm)
    have hresm : 2 / k.beta ≤ m :=
      (mul_le_mul_iff_of_pos_left (show 0 < 8 * B by positivity)).mp (hresn.trans hm)
    constructor
    · have hh := (div_le_iff₀ k.epsilon_pos).mp hseedm
      nlinarith only [hh]
    · have hh := (div_le_iff₀ k.beta_pos).mp hresm
      nlinarith only [hh]

namespace EquitableRegularPartition

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}

theorem order_le_cluster_scale (R : EquitableRegularPartition G ε)
    (hε : ε ≤ 1 / 2) (n B : ℝ) (hhost : n / 4 ≤ Fintype.card V)
    (hB : (R.clusters.card : ℝ) ≤ B) : n ≤ 8 * B * R.clusterSize := by
  classical
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (R.clusters.biUnion id))
  rw [Finset.card_univ, R.cluster_volume] at hcard
  have hcardR : ((Finset.univ \ R.clusters.biUnion id).card : ℝ) +
      R.clusterSize * R.clusters.card = Fintype.card V := by exact_mod_cast hcard
  have hεN := mul_le_mul_of_nonneg_right hε (show 0 ≤ (Fintype.card V : ℝ) by positivity)
  have ht := mul_le_mul_of_nonneg_left hB (show 0 ≤ (R.clusterSize : ℝ) by positivity)
  nlinarith only [hcardR, R.discarded_bound, hεN, ht, hhost]

end EquitableRegularPartition

end Erdos547

#print axioms Erdos547.exists_embedding_order_threshold
#print axioms Erdos547.EquitableRegularPartition.order_le_cluster_scale
