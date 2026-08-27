import ErdosProblems.Erdos4.FGKMTInitialEdgeConcentration

/-! Support, size, residue, marginal, and pair bounds for the initial translated edge laws. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical RandomResidueSieve

namespace FiniteLaw

theorem exists_pos_of_prob_pos {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (E : Ω → Prop) (hE : 0 < μ.prob E) : ∃ o, E o ∧ 0 < μ.weight o := by
  unfold prob at hE
  obtain ⟨o, _, ho⟩ := (Finset.sum_pos_iff_of_nonneg (fun o _ => by
    split_ifs
    · exact μ.nonneg o
    · exact le_refl 0)).mp hE
  by_cases he : E o
  · exact ⟨o, he, by simpa only [if_pos he] using ho⟩
  · simp only [if_neg he, lt_self_iff_false] at ho

end FiniteLaw

theorem sum_le_of_unique_positive {I : Type*} [Fintype I] (f : I → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (hf0 : ∀ i, 0 ≤ f i) (hf : ∀ i, f i ≤ a)
    (hunique : ∀ i j, 0 < f i → 0 < f j → i = j) : ∑ i, f i ≤ a := by
  by_cases hex : ∃ i, 0 < f i
  · obtain ⟨i, hi⟩ := hex
    calc
      _ = f i := Finset.sum_eq_single i
        (fun j _ hji => le_antisymm (le_of_not_gt (fun hj => hji (hunique j i hj hi))) (hf0 j))
        (fun hi => False.elim (hi (Finset.mem_univ i)))
      _ ≤ a := hf i
  · have hz : ∀ i, f i = 0 := fun i =>
      le_antisymm (le_of_not_gt (fun hi => hex ⟨i, hi⟩)) (hf0 i)
    simpa only [hz, Finset.sum_const_zero] using ha

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] {k Y : ℕ}

theorem translatedInitialEdgeLaw_support (h : Fin k → ℕ) (hY : 1 ≤ Y)
    (targets : Finset ℕ) (μ : FiniteLaw (TranslatedCenter Y)) (p : ℕ)
    (a : ∀ l, ZMod (ell l)) (e : Finset targets)
    (he : 0 < (translatedInitialEdgeLaw ell h hY targets μ p a).weight e) :
    e = ∅ ∨ ∃ n : TranslatedCenter Y,
      Survives ell a (translatedSites h p n.val) ∧ 0 < μ.weight n ∧
        initialTargetEdge h p Y targets n.val = e :=
  initialEdgeLaw_support μ _ _ (UnitFourier.unitDensity_pos ell) k
    (firstTranslatedCenter hY) e he

theorem translatedInitialEdgeLaw_card_le (h : Fin k → ℕ) (hY : 1 ≤ Y)
    (targets : Finset ℕ) (μ : FiniteLaw (TranslatedCenter Y)) (p : ℕ)
    (a : ∀ l, ZMod (ell l)) (e : Finset targets)
    (he : 0 < (translatedInitialEdgeLaw ell h hY targets μ p a).weight e) : e.card ≤ k := by
  rcases translatedInitialEdgeLaw_support ell h hY targets μ p a e he with hempty | ⟨n, _, _, hn⟩
  · simp only [hempty, Finset.card_empty, Nat.zero_le]
  · rw [← hn]
    exact initialTargetEdge_card_le h p Y targets n.val

theorem translatedInitialEdgeLaw_residue (h : Fin k → ℕ) (hY : 1 ≤ Y)
    (targets : Finset ℕ) (μ : FiniteLaw (TranslatedCenter Y)) (p : ℕ)
    (a : ∀ l, ZMod (ell l)) (e : Finset targets)
    (he : 0 < (translatedInitialEdgeLaw ell h hY targets μ p a).weight e) :
    ∃ b : ZMod p, ∀ q ∈ e, (q.val : ZMod p) = b := by
  rcases translatedInitialEdgeLaw_support ell h hY targets μ p a e he with hempty | ⟨n, _, _, hn⟩
  · exact ⟨0, by simp [hempty]⟩
  · refine ⟨(n.val : ZMod p) - (Y : ZMod p), ?_⟩
    intro q hq
    exact initialTargetEdge_residue h p Y targets n.val q (hn ▸ hq)

theorem translatedInitialEdgeLaw_survives (h : Fin k → ℕ) (hY : 1 ≤ Y)
    (targets : Finset ℕ) (μ : FiniteLaw (TranslatedCenter Y)) (p : ℕ)
    (a : ∀ l, ZMod (ell l)) (e : Finset targets)
    (he : 0 < (translatedInitialEdgeLaw ell h hY targets μ p a).weight e)
    (q : targets) (hq : q ∈ e) : Survives ell a {q.val + Y} := by
  rcases translatedInitialEdgeLaw_support ell h hY targets μ p a e he with hempty | ⟨n, hS, _, hn⟩
  · exfalso
    simpa [hempty] using hq
  · exact initialTargetEdge_survives ell h p Y targets n.val a hS q (hn ▸ hq)

theorem translatedInitialEdgeLaw_marginal_le (h : Fin k → ℕ) (hh : Function.Injective h)
    (hY : 1 ≤ Y) (targets : Finset ℕ) (μ : FiniteLaw (TranslatedCenter Y))
    {p : ℕ} (hp : 0 < p) (hshift : ∀ i, h i * p ≤ Y)
    (a : ∀ l, ZMod (ell l)) (q : targets) (hq0 : 1 ≤ q.val) (hqY : q.val ≤ Y)
    {α : ℝ} (hatom : ∀ n, μ.weight n ≤ α) :
    (translatedInitialEdgeLaw ell h hY targets μ p a).prob (fun e => q ∈ e) ≤
      2 * (k : ℝ) * α / UnitFourier.unitDensity ell ^ k := by
  have hpinned : μ.prob (fun n => q ∈ initialTargetEdge h p Y targets n.val) ≤ (k : ℝ) * α := by
    have heq := μ.prob_congr_iff
      (fun n => q ∈ initialTargetEdge h p Y targets n.val)
      (fun n => q.val ∈ translatedEdge h p Y n.val) (fun n => by
        rw [mem_initialTargetEdge, mem_translatedEdge_iff_sites h p Y n.val hq0 hqY])
    rw [heq]
    exact translatedCenter_incidence_le h hh hp hq0 hqY hshift μ hatom
  calc
    _ ≤ 2 * μ.prob (fun n => q ∈ initialTargetEdge h p Y targets n.val) /
        UnitFourier.unitDensity ell ^ k :=
      initialEdgeLaw_event_le μ _ _ (UnitFourier.unitDensity_pos ell) k
        (firstTranslatedCenter hY) (fun e => q ∈ e) (by simp)
    _ ≤ _ := div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hpinned (by norm_num)).trans_eq (by ring))
      (pow_nonneg (UnitFourier.unitDensity_pos ell).le k)

theorem translatedInitialEdgeLaw_pair_source_unique (h : Fin k → ℕ) (hh : Function.Injective h)
    (hY : 1 ≤ Y) (targets : Finset ℕ) (μ μ' : FiniteLaw (TranslatedCenter Y))
    {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hbound : ∀ i, h i < p)
    (a : ∀ l, ZMod (ell l)) (q r : targets) (hqr : q ≠ r)
    (hpair : 0 < (translatedInitialEdgeLaw ell h hY targets μ p a).prob
      (fun e => q ∈ e ∧ r ∈ e))
    (hpair' : 0 < (translatedInitialEdgeLaw ell h hY targets μ' p' a).prob
      (fun e => q ∈ e ∧ r ∈ e)) : p = p' := by
  by_contra hne
  obtain ⟨e, he, hepos⟩ := FiniteLaw.exists_pos_of_prob_pos _ _ hpair
  obtain ⟨e', he', hepos'⟩ := FiniteLaw.exists_pos_of_prob_pos _ _ hpair'
  rcases translatedInitialEdgeLaw_support ell h hY targets μ p a e hepos with hempty | ⟨n, _, _, hn⟩
  · simpa [hempty] using he
  rcases translatedInitialEdgeLaw_support ell h hY targets μ' p' a e' hepos' with hempty | ⟨n', _, _, hn'⟩
  · simpa [hempty] using he'
  letI : Fact p.Prime := ⟨hp⟩
  have hsame := translatedSites_common_point_unique h hp hp' (Ne.symm hne)
    (natCast_shifts_injective h hh hbound)
    ((mem_initialTargetEdge h p Y targets n.val q).mp (hn ▸ he.1))
    ((mem_initialTargetEdge h p Y targets n.val r).mp (hn ▸ he.2))
    ((mem_initialTargetEdge h p' Y targets n'.val q).mp (hn' ▸ he'.1))
    ((mem_initialTargetEdge h p' Y targets n'.val r).mp (hn' ▸ he'.2))
  exact hqr (Subtype.ext (Nat.add_right_cancel hsame))

theorem translatedInitialEdgeLaw_pair_sum_le (h : Fin k → ℕ) (hh : Function.Injective h)
    (hY : 1 ≤ Y) (sources targets : Finset ℕ) (μ : ℕ → FiniteLaw (TranslatedCenter Y))
    (hs : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p)
    (a : ∀ l, ZMod (ell l)) (q r : targets) (hqr : q ≠ r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmarg : ∀ p ∈ sources,
      (translatedInitialEdgeLaw ell h hY targets (μ p) p a).prob (fun e => q ∈ e) ≤ δ) :
    (∑ p : sources, (translatedInitialEdgeLaw ell h hY targets (μ p) p a).prob
      (fun e => q ∈ e ∧ r ∈ e)) ≤ δ := by
  apply sum_le_of_unique_positive _ hδ
  · intro p
    exact FiniteLaw.prob_nonneg _ _
  · intro p
    exact (FiniteLaw.prob_mono _ (fun e he => he.1)).trans (hmarg p p.property)
  · intro p p' hp hp'
    apply Subtype.ext
    exact translatedInitialEdgeLaw_pair_source_unique ell h hh hY targets (μ p) (μ p')
      (hs p p.property).1 (hs p' p'.property).1 (hs p p.property).2 a q r hqr hp hp'

end Erdos4.FGKMT
