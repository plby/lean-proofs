import StackExchange.Puzzling139335.LoopVariation.Defs

/-!
# Finiteness of cyclic truncated variation

Opening the closing chord of a finite cycle at the common endpoint of a loop
costs at most one truncation penalty. Consequently the concrete cyclic score
set is bounded by the already finite interval-variation supremum plus `ε`.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

variable {α X : Type*} [PseudoMetricSpace X]

/-- Inserting the common endpoint into the closing chord costs at most `ε`. -/
theorem cycleScore_le_adjoin_endpoints {ε : ℝ} (hε : 0 ≤ ε)
    (f : α → X) (xs : List α) {a b : α} (hclose : f a = f b) :
    cycleScore ε f xs ≤ chainScore ε f (a :: xs ++ [b]) + ε := by
  cases xs with
  | nil =>
      simpa only [cycleScore, List.nil_append, List.singleton_append, chainScore, add_zero] using
        add_nonneg (chord_nonneg ε (f a) (f b)) hε
  | cons x xs =>
      have h := chainScore_append_le_insert hε f (x :: xs) [x] b
      simpa only [cycleScore, List.cons_append, chainScore, add_zero, zero_add, ← hclose,
        add_comm, add_left_comm, add_assoc] using h

/-- Any bound for the concrete cyclic scores also bounds the interval variation. -/
theorem variationOn_le_loopVariationOn [LE α] {ε : ℝ} {f : α → X} {s : Set α}
    (hb : BddAbove (cycleScoresOn ε f s)) :
    variationOn ε f s ≤ loopVariationOn ε f s := by
  apply csSup_le (scoresOn_nonempty ε f s)
  rintro _ ⟨xs, hxs, rfl⟩
  exact (chainScore_le_cycleScore ε f xs).trans (cycleScore_le_loopVariationOn hb hxs)

section LinearOrder

variable [LinearOrder α]

/-- A cyclic score is at most the opened-interval variation plus one penalty. -/
theorem cycleScore_le_variationOn_add {ε : ℝ} {f : α → X} {a b : α}
    (hε : 0 ≤ ε) (hab : a ≤ b) (hclose : f a = f b)
    (hb : BddAbove (scoresOn ε f (Icc a b))) {xs : List α}
    (hxs : IsChainOn (Icc a b) xs) :
    cycleScore ε f xs ≤ variationOn ε f (Icc a b) + ε := by
  have hcut := cycleScore_le_adjoin_endpoints hε f xs hclose
  have hbound := chainScore_le_variationOn hb (hxs.adjoin_endpoints hab)
  linarith

/-- Opening a loop at its basepoint increases the error by at most one penalty. -/
theorem loopVariationOn_le_variationOn_add {ε : ℝ} {f : α → X} {a b : α}
    (hε : 0 ≤ ε) (hab : a ≤ b) (hclose : f a = f b)
    (hb : BddAbove (scoresOn ε f (Icc a b))) :
    loopVariationOn ε f (Icc a b) ≤ variationOn ε f (Icc a b) + ε := by
  apply csSup_le (cycleScoresOn_nonempty ε f (Icc a b))
  rintro _ ⟨xs, hxs, rfl⟩
  exact cycleScore_le_variationOn_add hε hab hclose hb hxs

end LinearOrder

/-- Continuity and a positive resolution give an actual finite upper bound on
all cyclic scores. No length, area, or rectifiability assumption is used. -/
theorem bddAbove_cycleScoresOn_Icc {f : ℝ → X} {a b ε : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hclose : f a = f b)
    (hε : 0 < ε) : BddAbove (cycleScoresOn ε f (Icc a b)) := by
  refine ⟨variationOn ε f (Icc a b) + ε, ?_⟩
  rintro _ ⟨xs, hxs, rfl⟩
  exact cycleScore_le_variationOn_add hε.le hab hclose
    (bddAbove_scoresOn_Icc hab hf hε) hxs

/-- Cyclic variation differs from the variation of the opened parameter interval
by a number between zero and `ε`. -/
theorem loopVariationOn_Icc_bounds {f : ℝ → X} {a b ε : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hclose : f a = f b)
    (hε : 0 < ε) :
    variationOn ε f (Icc a b) ≤ loopVariationOn ε f (Icc a b) ∧
      loopVariationOn ε f (Icc a b) ≤ variationOn ε f (Icc a b) + ε :=
  ⟨variationOn_le_loopVariationOn (bddAbove_cycleScoresOn_Icc hab hf hclose hε),
    loopVariationOn_le_variationOn_add hε.le hab hclose
      (bddAbove_scoresOn_Icc hab hf hε)⟩

/-- Any two sampled loop points give a lower bound by their truncated chord. -/
theorem chord_le_loopVariationOn_Icc {f : ℝ → X} {a b u v ε : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hclose : f a = f b)
    (hε : 0 < ε) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    chord ε (f u) (f v) ≤ loopVariationOn ε f (Icc a b) := by
  have hb := bddAbove_cycleScoresOn_Icc hab hf hclose hε
  have hordered (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      chord ε (f u) (f v) ≤ loopVariationOn ε f (Icc a b) := by
    have hchain : IsChainOn (Icc a b) [u, v] := by
      constructor
      · simp [huv]
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact hu
        · exact hv
    have h := (chainScore_le_cycleScore ε f [u, v]).trans
      (cycleScore_le_loopVariationOn hb hchain)
    simpa only [chainScore, add_zero] using h
  rcases le_total u v with huv | hvu
  · exact hordered u v hu hv huv
  · simpa only [chord_symm ε (f v) (f u)] using hordered v u hv hu hvu

/-- A fixed pair of distinct loop points provides a uniform positive lower
bound for all sufficiently small positive resolutions. -/
theorem exists_positive_lower_bound {f : ℝ → X} {a b u v : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hclose : f a = f b)
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (hd : 0 < dist (f u) (f v)) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      η ≤ loopVariationOn ε f (Icc a b) := by
  refine ⟨dist (f u) (f v) / 2, by positivity, ?_⟩
  intro ε hε hsmall
  have hchord := chord_le_loopVariationOn_Icc hab hf hclose hε hu hv
  have hmax : dist (f u) (f v) - ε ≤ chord ε (f u) (f v) := le_max_left _ _
  linarith

/-- Every nondegenerate simple loop has a positive small-resolution lower bound. -/
theorem exists_positive_lower_bound_of_injOn_Ico
    {Y : Type*} [MetricSpace Y] {f : ℝ → Y} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) (hclose : f a = f b)
    (hinj : InjOn f (Ico a b)) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      η ≤ loopVariationOn ε f (Icc a b) := by
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  have hm : (a + b) / 2 ∈ Ico a b := ⟨by linarith, by linarith⟩
  have hne : f a ≠ f ((a + b) / 2) := by
    intro heq
    have hparam := hinj ha hm heq
    linarith
  exact exists_positive_lower_bound hab.le hf hclose ⟨le_rfl, hab.le⟩
    ⟨hm.1, hm.2.le⟩ (dist_pos.mpr hne)

end

end Puzzling139335.LoopVariation
