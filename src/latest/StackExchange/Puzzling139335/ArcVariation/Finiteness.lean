import StackExchange.Puzzling139335.ArcVariation.Defs
import Mathlib.Topology.Instances.Real.Lemmas

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

/-- Uniform continuity makes every penalized chord bounded by a fixed multiple
of its parameter span.  This is not a Lipschitz assumption on the curve. -/
theorem exists_chord_le_mul_sub {f : ℝ → X} {a b ε : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      chord ε (f u) (f v) ≤ K * (v - u) := by
  obtain ⟨M, hM⟩ := Metric.isBounded_iff.mp
    (isCompact_Icc.image_of_continuousOn hf).isBounded
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  let D : ℝ := max M 0
  have hD : 0 ≤ D := le_max_right _ _
  have hK : 0 ≤ D / δ := div_nonneg hD hδ.le
  refine ⟨D / δ, hK, ?_⟩
  intro u hu v hv huv
  by_cases huvδ : v - u < δ
  · have huv_dist : dist u v < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huv)]
      linarith
    have hchord : chord ε (f u) (f v) = 0 := by
      exact max_eq_right (sub_nonpos.mpr (hsmall u hu v hv huv_dist).le)
    rw [hchord]
    exact mul_nonneg hK (sub_nonneg.mpr huv)
  · have hlarge : δ ≤ v - u := le_of_not_gt huvδ
    have hdist : dist (f u) (f v) ≤ D :=
      (hM (mem_image_of_mem f hu) (mem_image_of_mem f hv)).trans (le_max_left _ _)
    calc
      chord ε (f u) (f v) ≤ D :=
        max_le (by dsimp [D] at *; linarith) hD
      _ = (D / δ) * δ := (div_mul_cancel₀ D hδ.ne').symm
      _ ≤ (D / δ) * (v - u) := mul_le_mul_of_nonneg_left hlarge hK

/-- The chord estimate telescopes along every concrete monotone list. -/
theorem chainScore_cons_le_mul_sub {f : ℝ → X} {a b ε K : ℝ}
    (hK : 0 ≤ K)
    (hchord : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      chord ε (f u) (f v) ≤ K * (v - u)) :
    ∀ (xs : List ℝ) (x : ℝ), IsChainOn (Icc a b) (x :: xs) →
      chainScore ε f (x :: xs) ≤ K * (b - x) := by
  intro xs
  induction xs with
  | nil =>
      intro x hx
      exact mul_nonneg hK (sub_nonneg.mpr (hx.2 x (by simp)).2)
  | cons y ys ih =>
      intro x hx
      have hxmem : x ∈ Icc a b := hx.2 x (by simp)
      have hymem : y ∈ Icc a b := hx.2 y (by simp)
      have hxy : x ≤ y := (List.pairwise_cons.mp hx.1).1 y (by simp)
      have htail : IsChainOn (Icc a b) (y :: ys) := by
        refine ⟨(List.pairwise_cons.mp hx.1).2, ?_⟩
        intro t ht
        exact hx.2 t (List.mem_cons_of_mem x ht)
      calc
        chainScore ε f (x :: y :: ys)
            = chord ε (f x) (f y) + chainScore ε f (y :: ys) := rfl
        _ ≤ K * (y - x) + K * (b - y) :=
          add_le_add (hchord x hxmem y hymem hxy) (ih y htail)
        _ = K * (b - x) := by ring

theorem chainScore_le_mul_interval {f : ℝ → X} {a b ε K : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hchord : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      chord ε (f u) (f v) ≤ K * (v - u))
    {xs : List ℝ} (hxs : IsChainOn (Icc a b) xs) :
    chainScore ε f xs ≤ K * (b - a) := by
  cases xs with
  | nil => exact mul_nonneg hK (sub_nonneg.mpr hab)
  | cons x xs =>
      calc
        chainScore ε f (x :: xs) ≤ K * (b - x) :=
          chainScore_cons_le_mul_sub hK hchord xs x hxs
        _ ≤ K * (b - a) := mul_le_mul_of_nonneg_left
          (sub_le_sub_left (hxs.2 x (by simp)).1 b) hK

/-- Positive-resolution variation of every continuous compact-interval map is
finite: the concrete score set has a real upper bound.  Injectivity is not needed. -/
theorem bddAbove_scoresOn_Icc {f : ℝ → X} {a b ε : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hε : 0 < ε) :
    BddAbove (scoresOn ε f (Icc a b)) := by
  obtain ⟨K, hK, hchord⟩ := exists_chord_le_mul_sub hf hε
  refine ⟨K * (b - a), ?_⟩
  rintro r ⟨xs, hxs, rfl⟩
  exact chainScore_le_mul_interval hab hK hchord hxs

theorem variationOn_Icc_nonneg {f : ℝ → X} {a b ε : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hε : 0 < ε) :
    0 ≤ variationOn ε f (Icc a b) :=
  variationOn_nonneg (bddAbove_scoresOn_Icc hab hf hε)

/-- A single endpoint chord gives a lower bound that remains positive at
resolutions below the endpoint distance. -/
theorem chord_le_variationOn_Icc {f : ℝ → X} {a b ε : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hε : 0 < ε) :
    chord ε (f a) (f b) ≤ variationOn ε f (Icc a b) := by
  have hc : IsChainOn (Icc a b) [a, b] := by
    simp [IsChainOn, hab]
  simpa [chainScore] using
    chainScore_le_variationOn (bddAbove_scoresOn_Icc hab hf hε) hc

theorem variationOn_Icc_pos {f : ℝ → X} {a b ε : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hε : 0 < ε)
    (hsmall : ε < dist (f a) (f b)) :
    0 < variationOn ε f (Icc a b) := by
  exact lt_of_lt_of_le (sub_pos.mpr hsmall)
    ((le_max_left _ _).trans (chord_le_variationOn_Icc hab hf hε))

/-- A nondegenerate arc has a positive lower bound at every sufficiently
fine positive resolution, even if its ordinary length is infinite. -/
theorem exists_positive_lower_bound {f : ℝ → X} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hends : 0 < dist (f a) (f b)) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      η ≤ variationOn ε f (Icc a b) := by
  refine ⟨dist (f a) (f b) / 2, by positivity, ?_⟩
  intro ε hε hsmall
  calc
    dist (f a) (f b) / 2 ≤ dist (f a) (f b) - ε := by linarith
    _ ≤ chord ε (f a) (f b) := le_max_left _ _
    _ ≤ variationOn ε f (Icc a b) := chord_le_variationOn_Icc hab hf hε

/-- The preceding lower bound applies to every continuously parametrized
injective nondegenerate metric arc. -/
theorem exists_positive_lower_bound_of_injOn {Y : Type*} [MetricSpace Y]
    {f : ℝ → Y} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hinj : InjOn f (Icc a b)) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      η ≤ variationOn ε f (Icc a b) := by
  have hne : f a ≠ f b := by
    intro h
    exact hab.ne (hinj ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ h)
  exact exists_positive_lower_bound hab.le hf (dist_pos.mpr hne)

end

end Puzzling139335.ArcVariation
