import Arxiv.Arxiv2411_18291.ColourCollisionCounts

/-! # First moments and upper tails for marked colour collisions -/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype V] [DecidableEq V] {F : Finset W} {k : ℕ}
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

omit [MeasurableSingletonClass (Equiv.Perm V)] in
theorem distinct_block_pair_probability_le (G : Hypergraph V k) {t : ℝ}
    (hpair : ∀ a < k, ∀ P : IntersectingBlockPair V k k a,
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        {σ | P.val.1 ∈ mapGraph σ.toEmbedding G ∧ P.val.2 ∈ mapGraph σ.toEmbedding G} ≤ t)
    (P Q : Block V k) (hne : P ≠ Q) :
    (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
      {σ | P ∈ mapGraph σ.toEmbedding G ∧ Q ∈ mapGraph σ.toEmbedding G} ≤ t := by
  have hcard : (P.val ∩ Q.val).card < k := by
    by_contra hh
    have heq : P.val ∩ Q.val = P.val := eq_of_subset_of_card_le inter_subset_left
      (by rw [P.property]; omega)
    have hsub : P.val ⊆ Q.val := heq ▸ inter_subset_right
    exact hne (Subtype.ext (eq_of_subset_of_card_le hsub (by rw [P.property, Q.property])))
  exact hpair _ hcard ⟨(P, Q), rfl⟩

theorem markedColourCollisionCount_mean_le (φ : F ↪ V) (E : Hypergraph W k)
    (T : Finset (EmbeddingExtension φ)) (G : Hypergraph V k) (e d : E) (hne : e ≠ d)
    {t : ℝ} (hpair : ∀ P Q : Block V k, P ≠ Q →
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        {σ | P ∈ mapGraph σ.toEmbedding G ∧ Q ∈ mapGraph σ.toEmbedding G} ≤ t) :
    (∫ ω, markedColourCollisionCount φ E T G e d ω ∂RandomPermutation.probability E V) ≤
      (T.card : ℝ) * t * density G ^ (E.card - 1) := by
  classical
  have hpoint (f : EmbeddingExtension φ) :
      (∏ i : E, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        (markedColourCollisionEvent E G e d f i)) ≤ t * density G ^ (E.card - 1) := by
    have hspecial : (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        (markedColourCollisionEvent E G e d f e) ≤ t := by
      have hneq : mapBlock f.val e.val ≠ mapBlock f.val d.val :=
        fun hh => hne (Subtype.ext (mapBlock_injective f.val hh))
      simpa [markedColourCollisionEvent, extensionColourEvent, Set.ofPred_and] using
        hpair (mapBlock f.val e.val) (mapBlock f.val d.val) hneq
    have hrest : (∏ i ∈ (univ : Finset E).erase e,
        (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
          (markedColourCollisionEvent E G e d f i)) = density G ^ (E.card - 1) := by
      calc
        _ = ∏ _i ∈ (univ : Finset E).erase e, density G := by
          apply prod_congr rfl
          intro i hi
          rw [markedColourCollisionEvent, if_neg (mem_erase.mp hi).1]
          exact uniform_permuted_family_probability (mapBlock f.val i.val) G
        _ = _ := by
          simp only [prod_const, card_erase_of_mem (mem_univ e), card_univ, Fintype.card_coe]
    rw [← mul_prod_erase _ _ (mem_univ e), hrest]
    exact mul_le_mul_of_nonneg_right hspecial (pow_nonneg (density_nonneg G) _)
  unfold markedColourCollisionCount
  rw [RandomPermutation.eventCount_mean]
  calc
    _ ≤ ∑ _f ∈ T, t * density G ^ (E.card - 1) := sum_le_sum fun f _ => hpoint f
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

theorem colourCollisionCount_integrable (φ : F ↪ V) (E : Hypergraph W k)
    (T : Finset (EmbeddingExtension φ)) (G : Hypergraph V k) :
    Integrable (colourCollisionCount φ E T G) (RandomPermutation.probability E V) := by
  classical
  unfold colourCollisionCount
  exact integrable_finsetSum univ fun e _ => integrable_finsetSum (univ.erase e) fun d _ =>
    RandomPermutation.eventCount_integrable univ T (markedColourCollisionEvent E G e d)

theorem colourCollisionCount_mean_le (φ : F ↪ V) (E : Hypergraph W k)
    (T : Finset (EmbeddingExtension φ)) (G : Hypergraph V k)
    (hpair : ∀ P Q : Block V k, P ≠ Q →
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        {σ | P ∈ mapGraph σ.toEmbedding G ∧ Q ∈ mapGraph σ.toEmbedding G} ≤ 2 * density G ^ 2) :
    (∫ ω, colourCollisionCount φ E T G ω ∂RandomPermutation.probability E V) ≤
      2 * (E.card : ℝ) ^ 2 * T.card * density G ^ (E.card + 1) := by
  classical
  have hmark (e d : E) (hne : e ≠ d) :
      (∫ ω, markedColourCollisionCount φ E T G e d ω ∂RandomPermutation.probability E V) ≤
        2 * T.card * density G ^ (E.card + 1) := by
    have hE : 1 ≤ E.card := Nat.succ_le_of_lt (card_pos.mpr ⟨e.val, e.property⟩)
    refine (markedColourCollisionCount_mean_le φ E T G e d hne hpair).trans_eq ?_
    calc
      _ = 2 * T.card * (density G ^ 2 * density G ^ (E.card - 1)) := by ring
      _ = _ := by rw [← pow_add, show 2 + (E.card - 1) = E.card + 1 by omega]
  have hint (e d : E) : Integrable (markedColourCollisionCount φ E T G e d)
      (RandomPermutation.probability E V) :=
    RandomPermutation.eventCount_integrable univ T (markedColourCollisionEvent E G e d)
  unfold colourCollisionCount
  rw [integral_finsetSum univ (fun e _ =>
    integrable_finsetSum (univ.erase e) (fun d _ => hint e d))]
  simp_rw [integral_finsetSum _ (fun d _ => hint _ d)]
  calc
    _ ≤ ∑ e : E, ∑ _d ∈ univ.erase e, 2 * T.card * density G ^ (E.card + 1) :=
      sum_le_sum fun e _ => sum_le_sum fun d hd => hmark e d (Ne.symm (mem_erase.mp hd).1)
    _ ≤ ∑ _e : E, ∑ _d : E, 2 * T.card * density G ^ (E.card + 1) := by
      apply sum_le_sum
      intro e _
      apply sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      intro _ _ _
      have hp := density_nonneg G
      positivity
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

theorem colourCollisionCount_upper_tail_le (φ : F ↪ V) (E : Hypergraph W k)
    (T : Finset (EmbeddingExtension φ)) (G : Hypergraph V k)
    (hpair : ∀ P Q : Block V k, P ≠ Q →
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        {σ | P ∈ mapGraph σ.toEmbedding G ∧ Q ∈ mapGraph σ.toEmbedding G} ≤ 2 * density G ^ 2)
    {a : ℝ} (ha : 0 < a) :
    (RandomPermutation.probability E V).real {ω | a ≤ colourCollisionCount φ E T G ω} ≤
      (2 * (E.card : ℝ) ^ 2 * T.card * density G ^ (E.card + 1)) / a := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => colourCollisionCount_nonneg φ E T G ω)
    (colourCollisionCount_integrable φ E T G) a
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  exact hmark.trans (colourCollisionCount_mean_le φ E T G hpair)

end Arxiv2411_18291
