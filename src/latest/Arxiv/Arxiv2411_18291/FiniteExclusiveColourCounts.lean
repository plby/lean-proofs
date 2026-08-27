import Arxiv.Arxiv2411_18291.ColourCollisionMoments
import Arxiv.Arxiv2411_18291.ExclusiveColourNumerics
import Arxiv.Arxiv2411_18291.FiniteColouredExtensions
import Arxiv.Arxiv2411_18291.ExplicitBoostSize

/-! # Finite probability bounds after removing ambiguous edge colours -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] {q r n h : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
variable [MeasurableSingletonClass (Equiv.Perm (Fin n))]

theorem good_edge_distinct_pair_probability_le_two_paper_threshold
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (P Q : Block (Fin n) (r + 1)) (hne : P ≠ Q) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
      {σ | P ∈ mapGraph σ.toEmbedding G ∧ Q ∈ mapGraph σ.toEmbedding G} ≤ 2 * density G ^ 2 := by
  have hh : 1 ≤ h := (Nat.succ_le_of_lt (Nat.choose_pos hqr.le)).trans hqh
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  obtain ⟨_, hpd, hpair⟩ := good_edge_colour_estimates_paper_threshold hqr hn hqh
    K G hT hd hGK hloss
  let t := (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * density K ^ 2
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hp := colour_joint_power_bound_paper_threshold hqr hn hh hH
    (density G) (density K) t (density_nonneg K) ht0 hpd le_rfl 1 hh
  simp only [pow_one, Nat.mul_one] at hp
  have he : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith only [paperAlpha_pos hqr])
  have ht : t ≤ 2 * density G ^ 2 := hp.trans
    (mul_le_mul_of_nonneg_right (by linarith only [he]) (sq_nonneg _))
  exact (distinct_block_pair_probability_le G hpair P Q hne).trans ht

theorem colourCollisionCount_upper_tail_paper_threshold
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (φ : F ↪ Fin n) (E : Hypergraph W (r + 1))
    (hE : E.card ≤ q.choose (r + 1)) (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card) :
    (RandomPermutation.probability E (Fin n)).real
      {ω | density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) / 64 ≤
        colourCollisionCount φ E univ G ω} ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := by
  classical
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hG : 0 < density G := (by positivity : (0 : ℝ) <
    (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1))).trans_le
      (good_reference_density_lower_paper_threshold hqr hn K G hd hGK hloss)
  have hGupper : density G ≤ 2 * (n : ℝ) ^ (-paperAlpha q (r + 1)) :=
    (density_mono hGK).trans (paper_host_density_bounds hqr hn K hd).2
  let a := density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) / 64
  have ha : 0 < a := by dsimp only [a]; positivity
  have hc : ((univ : Finset (EmbeddingExtension φ)).card : ℝ) ≤
      (n : ℝ) ^ (Fintype.card W - F.card) := by
    exact_mod_cast (by simpa only [card_univ, Fintype.card_fin] using
      card_embeddingExtension_upper φ)
  have hprob := colourCollisionCount_upper_tail_le φ E univ G
    (good_edge_distinct_pair_probability_le_two_paper_threshold hqr hn hqh hH
      K G hT hd hGK hloss) ha
  have hratio : (2 * (E.card : ℝ) ^ 2 * (univ : Finset (EmbeddingExtension φ)).card *
      density G ^ (E.card + 1)) / a ≤ 128 * (E.card : ℝ) ^ 2 * density G := by
    apply (div_le_iff₀ ha).mpr
    calc
      _ ≤ 2 * (E.card : ℝ) ^ 2 * (n : ℝ) ^ (Fintype.card W - F.card) *
          density G ^ (E.card + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity))
          (pow_nonneg hG.le _)
      _ = _ := by dsimp only [a]; rw [pow_succ]; ring
  have hE2 : (E.card : ℝ) ^ 2 ≤ (q.choose (r + 1) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hE) _
  calc
    _ ≤ 128 * (E.card : ℝ) ^ 2 * density G := hprob.trans hratio
    _ ≤ 128 * (q.choose (r + 1) : ℝ) ^ 2 *
        (2 * (n : ℝ) ^ (-paperAlpha q (r + 1))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hE2 (by norm_num)) hGupper hG.le (by positivity)
    _ = 256 * (q.choose (r + 1) : ℝ) ^ 2 * (n : ℝ) ^ (-paperAlpha q (r + 1)) := by ring
    _ ≤ _ := exclusive_colour_collision_coefficient_paper_threshold hqr hn

theorem exclusiveColourExtensions_lower_tail_paper_threshold
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (φ : F ↪ Fin n) (E : Hypergraph W (r + 1))
    (hE : E.card ≤ q.choose (r + 1))
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hroot : ∀ e ∈ E, ¬e.val ⊆ F)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card) :
    (RandomPermutation.probability E (Fin n)).real
      {ω | (exclusiveColourExtensions φ E ω G).card ≤
        (35 / 64 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card)} ≤
          33 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := by
  classical
  have hnsize := paper_small_carrier_completion_size hqr hn hw
  have hsize : (3 / 4 : ℝ) * (n : ℝ) ^ (Fintype.card W - F.card) ≤
      (univ : Finset (EmbeddingExtension φ)).card := by
    simpa only [card_univ, Fintype.card_fin] using card_embeddingExtension_three_quarters φ
      (by simpa only [Fintype.card_fin] using hnsize)
  let X := extensionColourCount φ univ (fun e : E => e.val) univ G
  let m : ℝ := Fintype.card (EmbeddingExtension φ) * density G ^ E.card
  let a := density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) / 64
  have hX : (RandomPermutation.probability E (Fin n)).real {ω | X ω ≤ 3 * m / 4} ≤
      32 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := by
    have hh := coloured_extension_lower_tail_three_quarters_paper_threshold hqr hn hqh hH F hw
      univ (fun e : E => e.val)
      (by simpa only [card_univ, Fintype.card_coe] using hE.trans hqh)
      (fun e _ => block_root_inter_card_lt e.val (hroot e.val e.property))
      K G hT hd hGK hloss φ univ hsize
    simpa only [card_univ, Fintype.card_coe, X, m] using hh
  have hB : (RandomPermutation.probability E (Fin n)).real
      {ω | a ≤ colourCollisionCount φ E univ G ω} ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) :=
    colourCollisionCount_upper_tail_paper_threshold hqr hn hqh hH F φ E hE
      K G hT hd hGK hloss
  have hsub : {ω | (exclusiveColourExtensions φ E ω G).card ≤
      (35 / 64 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card)} ⊆
      {ω | X ω ≤ 3 * m / 4} ∪ {ω | a ≤ colourCollisionCount φ E univ G ω} := by
    intro ω hy
    by_cases hx : X ω ≤ 3 * m / 4
    · exact Or.inl hx
    · by_cases hc : a ≤ colourCollisionCount φ E univ G ω
      · exact Or.inr hc
      · exfalso
        have hxs := lt_of_not_ge hx
        have hcs := lt_of_not_ge hc
        have hactual := extensionColourCount_le_exclusive_add_collisions φ E G ω
        have hsize' := mul_le_mul_of_nonneg_right hsize (pow_nonneg (density_nonneg G) E.card)
        rw [card_univ] at hsize'
        change X ω ≤ (exclusiveColourExtensions φ E ω G).card +
          colourCollisionCount φ E univ G ω at hactual
        dsimp only [a, m] at hxs hcs
        change (exclusiveColourExtensions φ E ω G).card ≤
          (35 / 64 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) at hy
        nlinarith only [hy, hxs, hcs, hactual, hsize']
  calc
    _ ≤ (RandomPermutation.probability E (Fin n)).real
        ({ω | X ω ≤ 3 * m / 4} ∪ {ω | a ≤ colourCollisionCount φ E univ G ω}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (RandomPermutation.probability E (Fin n)).real {ω | X ω ≤ 3 * m / 4} +
        (RandomPermutation.probability E (Fin n)).real
          {ω | a ≤ colourCollisionCount φ E univ G ω} := measureReal_union_le _ _
    _ ≤ 32 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) +
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := add_le_add hX hB
    _ = _ := by ring

end Arxiv2411_18291
