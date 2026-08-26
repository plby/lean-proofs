import ErdosProblems.Erdos633b.GroupTwoUnconditionalNecessity
import ErdosProblems.Erdos633b.CaseSixUnconditional
import ErdosProblems.Erdos633b.CaseSevenUnconditional

/-! Every one of the six explicit non-reptiling angle shapes has
unconditional nonsquare necessity, with all geometric labelings allowed. -/

namespace Erdos633b.Tiling

theorem groupOne_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hs : GroupOneShape d.tile T) : EightCases T := by
  rcases hs.2 with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact d.caseSix_necessary_unconditional hn h0 h1 h2
  · exact d.caseSeven_necessary_unconditional hn h0 h1 h2

theorem six_shapes_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hs : SixAngleShapes d.tile T) : EightCases T := by
  obtain ⟨e, f, hs⟩ := hs
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  apply eightCases_of_reindex T f
  rcases hs with hs | hs
  · exact d'.groupOne_necessary_unconditional hn hs
  · exact d'.groupTwo_necessary_unconditional hn hs

theorem not_six_shapes_of_counterexample {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) : ¬ SixAngleShapes d.tile T :=
  fun hs => hnot (d.six_shapes_necessary_unconditional hn hs)

end Erdos633b.Tiling
