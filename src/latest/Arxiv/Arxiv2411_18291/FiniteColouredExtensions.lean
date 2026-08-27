import Arxiv.Arxiv2411_18291.LinearColourPowers
import Arxiv.Arxiv2411_18291.FiniteColourCollisions
import Arxiv.Arxiv2411_18291.FiniteColourTrials
import Arxiv.Arxiv2411_18291.FiniteGoodEdgeColours
import Arxiv.Arxiv2411_18291.UniformColouredExtensions

/-! # Finite colour experiments and simultaneous success for all roots -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {I W : Type*} [Fintype W] [DecidableEq W] {q r n h : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
variable [MeasurableSingletonClass (Equiv.Perm (Fin n))]

theorem coloured_extension_lower_tail_of_estimates_paper_threshold {k : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (s : Finset I) (Q : I → Block W k) (hs : s.card ≤ h)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r + 1)
    (D : Finset (Block (Fin n) k)) {a β d : ℝ} (hd : 0 ≤ d)
    (hgap : a + 2 * β * s.card + paperAlpha q (r + 1) / 24 ≤ 39 / 40)
    (hpbase : (1 / 4 : ℝ) * (n : ℝ) ^ (-β) ≤ density D)
    (hpd : (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * d ≤ density D)
    (hpair : ∀ j < r + 1, ∀ P : IntersectingBlockPair (Fin n) k k j,
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
        {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤
        (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * d ^ 2)
    (φ : F ↪ Fin n) (T : Finset (EmbeddingExtension φ))
    (hsize : ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤ T.card) :
    (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q T D ω ≤ (T.card : ℝ) * density D ^ s.card / 2} ≤
      8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hTpos : (0 : ℝ) < T.card := (by positivity : (0 : ℝ) <
    ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) * (n : ℝ) ^ (Fintype.card W - F.card)).trans_le hsize
  have hp : 0 < density D :=
    (by positivity : (0 : ℝ) < (1 / 4 : ℝ) * (n : ℝ) ^ (-β)).trans_le hpbase
  let t := (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * d ^ 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hpower := colour_joint_power_bound_paper_threshold hqr hn hh hH
    (density D) d t hd ht hpd le_rfl s.card hs
  have hcollision := colour_collision_bound_at_exponents_paper_threshold hqr hn hh hH
    ((Nat.sub_le (Fintype.card W) F.card).trans hw) hs hgap
      (T.card : ℝ) (density D) hsize hpbase
  exact extensionColourCount_lower_tail_le s Q T D (r + 1)
    (card_pos.mp (by exact_mod_cast hTpos)) hp ht hroot hpair hpower
    (by simpa only [Fintype.card_fin] using hcollision)

omit [Fintype W] [DecidableEq W] in
theorem uniform_coloured_extensions_failure_bound {k L : ℕ}
    (F : Finset W) (s : Finset I) (Q : I → Block W k)
    (D : Finset (Block (Fin n) k))
    (T : (φ : F ↪ Fin n) → Finset (EmbeddingExtension φ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ φ, (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q (T φ) D ω ≤
        ((T φ).card : ℝ) * density D ^ s.card / 2} ≤ δ) :
    (IndependentTrials.probability (RandomPermutation.probability I (Fin n)) L).real
      {ω | ¬ ∀ φ : F ↪ Fin n, ∃ j,
        ((T φ).card : ℝ) * density D ^ s.card / 2 <
          extensionColourCount φ s Q (T φ) D (ω j)} ≤ (n : ℝ) ^ F.card * δ ^ L := by
  classical
  let B (φ : F ↪ Fin n) : Set (RandomPermutation.Sample I (Fin n)) :=
    {ω | extensionColourCount φ s Q (T φ) D ω ≤ ((T φ).card : ℝ) * density D ^ s.card / 2}
  have hB (φ : F ↪ Fin n) : MeasurableSet (B φ) :=
    measurableSet_le (RandomPermutation.eventCount_measurable s (T φ)
      (fun f i => extensionColourEvent (Q i) f D)) measurable_const
  have hcard : ((univ : Finset (F ↪ Fin n)).card : ℝ) ≤ (n : ℝ) ^ F.card := by
    have hh : (univ : Finset (F ↪ Fin n)).card ≤ n ^ F.card := by
      simpa only [card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
        Fintype.card_coe] using Nat.descFactorial_le_pow n F.card
    exact_mod_cast hh
  have hbad : {ω : Fin L → RandomPermutation.Sample I (Fin n) |
      ¬ ∀ φ : F ↪ Fin n, ∃ j,
        ((T φ).card : ℝ) * density D ^ s.card / 2 <
          extensionColourCount φ s Q (T φ) D (ω j)} =
      ⋃ φ ∈ (univ : Finset (F ↪ Fin n)), IndependentTrials.allBad L (B φ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, not_forall, not_exists, not_lt, Set.mem_iUnion,
      mem_univ, exists_const, IndependentTrials.allBad, B]
  rw [hbad]
  exact (IndependentTrials.probability_some_allBad_le
    (RandomPermutation.probability I (Fin n)) L univ B
      (fun φ _ => hB φ) (fun φ _ => hprob φ)).trans
        (mul_le_mul_of_nonneg_right hcard (pow_nonneg hδ _))

omit [Fintype W] [DecidableEq W] in
theorem uniform_coloured_extensions_failure_paper_threshold {k : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (F : Finset W) (s : Finset I) (Q : I → Block W k)
    (D : Finset (Block (Fin n) k))
    (T : (φ : F ↪ Fin n) → Finset (EmbeddingExtension φ))
    (hprob : ∀ φ, (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q (T φ) D ω ≤
        ((T φ).card : ℝ) * density D ^ s.card / 2} ≤
          8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) :
    (IndependentTrials.probability (RandomPermutation.probability I (Fin n))
      (paperColourTrialCount q (r + 1) F.card)).real
        {ω | ¬ ∀ φ : F ↪ Fin n, ∃ j,
          ((T φ).card : ℝ) * density D ^ s.card / 2 <
            extensionColourCount φ s Q (T φ) D (ω j)} ≤ (n : ℝ) ^ (-1 : ℝ) :=
  (uniform_coloured_extensions_failure_bound F s Q D T (by positivity) hprob).trans
    (colour_trial_union_bound_le_paper_threshold hqr hn F.card)

omit [Fintype W] [DecidableEq W] in
theorem uniform_coloured_extensions_failure_square_paper_threshold {k : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (F : Finset W) (hF : 1 ≤ F.card) (s : Finset I) (Q : I → Block W k)
    (D : Finset (Block (Fin n) k))
    (T : (φ : F ↪ Fin n) → Finset (EmbeddingExtension φ))
    (hprob : ∀ φ, (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q (T φ) D ω ≤
        ((T φ).card : ℝ) * density D ^ s.card / 2} ≤
          8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) :
    (IndependentTrials.probability (RandomPermutation.probability I (Fin n))
      (paperColourTrialCount q (r + 1) F.card)).real
        {ω | ¬ ∀ φ : F ↪ Fin n, ∃ j,
          ((T φ).card : ℝ) * density D ^ s.card / 2 <
            extensionColourCount φ s Q (T φ) D (ω j)} ≤ (n : ℝ) ^ (-2 : ℝ) :=
  (uniform_coloured_extensions_failure_bound F s Q D T (by positivity) hprob).trans
    (colour_trial_union_bound_square_paper_threshold hqr hn hF)

omit [Fintype W] [DecidableEq W] in
theorem uniform_coloured_extensions_of_tail_paper_threshold {k : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (F : Finset W) (s : Finset I) (Q : I → Block W k)
    (D : Finset (Block (Fin n) k))
    (T : (φ : F ↪ Fin n) → Finset (EmbeddingExtension φ))
    (hprob : ∀ φ, (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q (T φ) D ω ≤
        ((T φ).card : ℝ) * density D ^ s.card / 2} ≤
          8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) :
    ∃ ω : Fin (paperColourTrialCount q (r + 1) F.card) → RandomPermutation.Sample I (Fin n),
      ∀ φ : F ↪ Fin n, ∃ j,
        ((T φ).card : ℝ) * density D ^ s.card / 2 < extensionColourCount φ s Q (T φ) D (ω j) := by
  classical
  let B (φ : F ↪ Fin n) : Set (RandomPermutation.Sample I (Fin n)) :=
    {ω | extensionColourCount φ s Q (T φ) D ω ≤ ((T φ).card : ℝ) * density D ^ s.card / 2}
  have hB (φ : F ↪ Fin n) : MeasurableSet (B φ) :=
    measurableSet_le (RandomPermutation.eventCount_measurable s (T φ)
      (fun f i => extensionColourEvent (Q i) f D)) measurable_const
  have hcard : ((univ : Finset (F ↪ Fin n)).card : ℝ) ≤ (n : ℝ) ^ F.card := by
    have hh : (univ : Finset (F ↪ Fin n)).card ≤ n ^ F.card := by
      simpa only [card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
        Fintype.card_coe] using Nat.descFactorial_le_pow n F.card
    exact_mod_cast hh
  have hbudget : ((univ : Finset (F ↪ Fin n)).card : ℝ) *
      (8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^
        paperColourTrialCount q (r + 1) F.card < 1 :=
    (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_lt
      (colour_trial_union_bound_paper_threshold hqr hn F.card)
  obtain ⟨ω, hω⟩ := IndependentTrials.exists_trials_avoiding_each
    (RandomPermutation.probability I (Fin n)) (paperColourTrialCount q (r + 1) F.card)
    univ B (fun φ _ => hB φ) (fun φ _ => hprob φ) hbudget
  refine ⟨ω, fun φ => ?_⟩
  obtain ⟨j, hj⟩ := hω φ (mem_univ φ)
  exact ⟨j, lt_of_not_ge hj⟩

theorem coloured_extension_lower_tail_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (s : Finset I) (Q : I → Block W (r + 1)) (hs : s.card ≤ h)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r + 1)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (φ : F ↪ Fin n) (T : Finset (EmbeddingExtension φ))
    (hsize : (3 / 4 : ℝ) * (n : ℝ) ^ (Fintype.card W - F.card) ≤ T.card) :
    (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q T G ω ≤ (T.card : ℝ) * density G ^ s.card / 2} ≤
      8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := by
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr.le)).trans hqh
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  obtain ⟨hdG, hpd, hpair⟩ := good_edge_colour_estimates_paper_threshold hqr hn hqh
    K G hT hd hGK hloss
  have hTpos : (0 : ℝ) < T.card :=
    (by positivity : (0 : ℝ) < (3 / 4 : ℝ) *
      (n : ℝ) ^ (Fintype.card W - F.card)).trans_le hsize
  have hp : 0 < density G := (by positivity :
    (0 : ℝ) < (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1))).trans_le hdG
  let t := (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * density K ^ 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hpower := colour_joint_power_bound_paper_threshold hqr hn hh hH
    (density G) (density K) t (density_nonneg K) ht hpd le_rfl s.card hs
  have hpbase : (1 / 4 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density G := by
    have hnα := Real.rpow_nonneg hn0.le (-paperAlpha q (r + 1))
    linarith only [hdG, hnα]
  have hcollision := colour_collision_bound_paper_threshold hqr hn hh hH
    ((Nat.sub_le (Fintype.card W) F.card).trans hw) hs (T.card : ℝ) (density G) hsize hpbase
  exact extensionColourCount_lower_tail_le s Q T G (r + 1)
    (card_pos.mp (by exact_mod_cast hTpos)) hp ht hroot hpair hpower
    (by simpa only [Fintype.card_fin] using hcollision)

theorem coloured_extension_lower_tail_three_quarters_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (s : Finset I) (Q : I → Block W (r + 1)) (hs : s.card ≤ h)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r + 1)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (φ : F ↪ Fin n) (T : Finset (EmbeddingExtension φ))
    (hsize : (3 / 4 : ℝ) * (n : ℝ) ^ (Fintype.card W - F.card) ≤ T.card) :
    (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q T G ω ≤ 3 * ((T.card : ℝ) * density G ^ s.card) / 4} ≤
      32 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := by
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr.le)).trans hqh
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  obtain ⟨hdG, hpd, hpair⟩ := good_edge_colour_estimates_paper_threshold hqr hn hqh
    K G hT hd hGK hloss
  have hTpos : (0 : ℝ) < T.card :=
    (by positivity : (0 : ℝ) < (3 / 4 : ℝ) *
      (n : ℝ) ^ (Fintype.card W - F.card)).trans_le hsize
  have hp : 0 < density G := (by positivity :
    (0 : ℝ) < (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1))).trans_le hdG
  let t := (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * density K ^ 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hpower := colour_joint_power_bound_paper_threshold hqr hn hh hH
    (density G) (density K) t (density_nonneg K) ht hpd le_rfl s.card hs
  have hpbase : (1 / 4 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density G := by
    have hnα := Real.rpow_nonneg hn0.le (-paperAlpha q (r + 1))
    linarith only [hdG, hnα]
  have hcollision := colour_collision_bound_paper_threshold hqr hn hh hH
    ((Nat.sub_le (Fintype.card W) F.card).trans hw) hs (T.card : ℝ) (density G) hsize hpbase
  exact extensionColourCount_lower_tail_three_quarters_le s Q T G (r + 1)
    (card_pos.mp (by exact_mod_cast hTpos)) hp ht hroot hpair hpower
    (by simpa only [Fintype.card_fin] using hcollision)

theorem uniform_coloured_extensions_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (s : Finset I) (Q : I → Block W (r + 1)) (hs : s.card ≤ h)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r + 1)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (T : (φ : F ↪ Fin n) → Finset (EmbeddingExtension φ))
    (hsize : ∀ φ, (3 / 4 : ℝ) * (n : ℝ) ^ (Fintype.card W - F.card) ≤ (T φ).card) :
    ∃ ω : Fin (paperColourTrialCount q (r + 1) F.card) → RandomPermutation.Sample I (Fin n),
      ∀ φ : F ↪ Fin n, ∃ j,
        ((T φ).card : ℝ) * density G ^ s.card / 2 < extensionColourCount φ s Q (T φ) G (ω j) := by
  exact uniform_coloured_extensions_of_tail_paper_threshold hqr hn F s Q G T
    (fun φ => coloured_extension_lower_tail_paper_threshold hqr hn hqh hH F hw s Q hs hroot
      K G hT hd hGK hloss φ (T φ) (hsize φ))

end Arxiv2411_18291
