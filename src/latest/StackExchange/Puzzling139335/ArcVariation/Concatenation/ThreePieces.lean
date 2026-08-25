import StackExchange.Puzzling139335.ArcVariation.Concatenation

/-!
# Two cuts in finite-resolution variation

Applying the concrete one-cut estimate twice gives an error of at most `2 * ε`.
-/

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {α X : Type*} [LinearOrder α] [PseudoMetricSpace X]

/-- Three consecutive restrictions have total variation at most the whole
variation, and the excess whole variation is at most two penalties. -/
theorem variationOn_three_pieces {ε : ℝ} {f : α → X} {a b c d : α}
    (hε : 0 ≤ ε) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hwhole : BddAbove (scoresOn ε f (Icc a d)))
    (hfirst : BddAbove (scoresOn ε f (Icc a b)))
    (hmiddle : BddAbove (scoresOn ε f (Icc b c)))
    (hlast : BddAbove (scoresOn ε f (Icc c d))) :
    variationOn ε f (Icc a b) + variationOn ε f (Icc b c) +
        variationOn ε f (Icc c d) ≤ variationOn ε f (Icc a d) ∧
      variationOn ε f (Icc a d) ≤
        variationOn ε f (Icc a b) + variationOn ε f (Icc b c) +
          variationOn ε f (Icc c d) + 2 * ε := by
  have hprefix : BddAbove (scoresOn ε f (Icc a c)) := by
    apply hwhole.mono
    rintro _ ⟨xs, hxs, rfl⟩
    refine ⟨xs, ⟨hxs.1, ?_⟩, rfl⟩
    intro t ht
    exact ⟨(hxs.2 t ht).1, (hxs.2 t ht).2.trans hcd⟩
  have h₁ := variationOn_concatenation hε hab hbc hprefix hfirst hmiddle
  have h₂ := variationOn_concatenation hε (hab.trans hbc) hcd hwhole hprefix hlast
  constructor
  · linarith [h₁.1, h₂.1]
  · linarith [h₁.2, h₂.2]

end

end Puzzling139335.ArcVariation
