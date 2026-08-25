import StackExchange.Puzzling139335.ArcVariation.Finiteness
import StackExchange.Puzzling139335.ArcVariation.Concatenation
import StackExchange.Puzzling139335.ArcVariation.Concatenation.EndpointPartitions
import StackExchange.Puzzling139335.ArcVariation.Concatenation.ThreePieces
import StackExchange.Puzzling139335.ArcVariation.Invariance
import StackExchange.Puzzling139335.ArcVariation.Invariance.Parametrization

/-!
# Finite-resolution variation of metric arcs

This module supplies the concrete metric-arc part of the finite-resolution
argument. A positive resolution makes the score supremum bounded for every
continuous map of a compact real interval, even when ordinary variation is
infinite. Cutting the interval once changes the sum by at most one resolution.
The score sets are invariant under codomain isometries and under monotone
surjective parameter changes; real interval reversal is also proved.

These statements are generic in the metric codomain and apply, in particular,
to `EuclideanSpace ℝ (Fin 2)`. They do not assume any of the required variation
properties as a class or an axiom. The separate topological argument identifying
the antipodal endpoints of a central two-piece Jordan cut is not asserted here.
-/

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

/-- The finite-resolution concatenation bounds with every boundedness premise
discharged from continuity and positivity of the resolution. -/
theorem variationOn_Icc_concatenation_of_continuousOn
    {f : ℝ → X} {a b c ε : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : ContinuousOn f (Icc a b)) (hε : 0 < ε) :
    variationOn ε f (Icc a c) + variationOn ε f (Icc c b) ≤
        variationOn ε f (Icc a b) ∧
      variationOn ε f (Icc a b) ≤
        variationOn ε f (Icc a c) + variationOn ε f (Icc c b) + ε := by
  have hleft : ContinuousOn f (Icc a c) :=
    hf.mono (fun _ hx => ⟨hx.1, hx.2.trans hcb⟩)
  have hright : ContinuousOn f (Icc c b) :=
    hf.mono (fun _ hx => ⟨hac.trans hx.1, hx.2⟩)
  exact variationOn_concatenation hε.le hac hcb
    (bddAbove_scoresOn_Icc (hac.trans hcb) hf hε)
    (bddAbove_scoresOn_Icc hac hleft hε)
    (bddAbove_scoresOn_Icc hcb hright hε)

/-- Two prescribed cuts give an error of at most `2 * ε`. -/
theorem variationOn_Icc_three_piece_of_continuousOn
    {f : ℝ → X} {a b c d ε : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hf : ContinuousOn f (Icc a d)) (hε : 0 < ε) :
    variationOn ε f (Icc a b) + variationOn ε f (Icc b c) +
        variationOn ε f (Icc c d) ≤ variationOn ε f (Icc a d) ∧
      variationOn ε f (Icc a d) ≤
        variationOn ε f (Icc a b) + variationOn ε f (Icc b c) +
          variationOn ε f (Icc c d) + 2 * ε := by
  have hfirst := variationOn_Icc_concatenation_of_continuousOn
    hab (hbc.trans hcd) hf hε
  have hrest : ContinuousOn f (Icc b d) :=
    hf.mono (fun _ hx => ⟨hab.trans hx.1, hx.2⟩)
  have hsecond := variationOn_Icc_concatenation_of_continuousOn hbc hcd hrest hε
  constructor <;> linarith [hfirst.1, hfirst.2, hsecond.1, hsecond.2]

/-- The concrete score set for the standard arc parameter interval is bounded. -/
theorem bddAbove_scoresOn_unitInterval {f : ℝ → X} {ε : ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hε : 0 < ε) :
    BddAbove (scoresOn ε f (Icc (0 : ℝ) 1)) :=
  bddAbove_scoresOn_Icc zero_le_one hf hε

/-- Thus the score supremum is exactly the usual endpoint-partition supremum
for every positive-resolution continuous compact-interval curve. -/
theorem endpoint_partition_sup_eq_of_continuousOn
    {f : ℝ → X} {a b ε : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hε : 0 < ε) :
    sSup (endpointScores ε f a b) = variationOn ε f (Icc a b) :=
  sSup_endpointScores_eq_variationOn hab (bddAbove_scoresOn_Icc hab hf hε)

/-- Congruent arc images have equal finite-resolution variation, even when the
two continuous injective parametrizations start at different endpoints. -/
theorem variationOn_eq_of_isometry_image_eq
    {E F : Type*} [MetricSpace E] [MetricSpace F]
    {f : ℝ → E} {g : ℝ → F} {a b c d : ℝ} (ε : ℝ)
    {e : E → F} (he : Isometry e)
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b))
    (hg : ContinuousOn g (Icc c d)) (hgi : InjOn g (Icc c d))
    (himage : e '' (f '' Icc a b) = g '' Icc c d) :
    variationOn ε f (Icc a b) = variationOn ε g (Icc c d) := by
  have hecont : ContinuousOn (e ∘ f) (Icc a b) := he.continuous.comp_continuousOn hf
  have heinj : InjOn (e ∘ f) (Icc a b) := by
    intro x hx y hy hxy
    exact hfi hx hy (he.injective hxy)
  have hcompimage : (e ∘ f) '' Icc a b = g '' Icc c d := by
    simpa only [Set.image_image, Function.comp_def] using himage
  rw [← variationOn_comp_isometry he ε f (Icc a b)]
  exact variationOn_eq_of_continuousOn_injOn_image_eq_Icc ε
    hecont heinj hg hgi hcompimage

end

end Puzzling139335.ArcVariation
