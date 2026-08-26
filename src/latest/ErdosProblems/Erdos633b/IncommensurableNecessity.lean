import ErdosProblems.Erdos633b.CaseSixRationality
import ErdosProblems.Erdos633b.CaseFiveRationality
import ErdosProblems.Erdos633b.CaseEightRationality
import ErdosProblems.Erdos633b.GroupTwoSixtyRationality
import ErdosProblems.Erdos633b.GroupTwoDoubleRationality
import ErdosProblems.Erdos633b.SixShapeNecessity
import ErdosProblems.Erdos633b.Sufficiency

/-! Complete eight-case equivalence for incommensurable outer triangles.
All side-rationality inputs are proved from actual tilings. The separate
commensurable-angle rigidity branch is not assumed or asserted here. -/

namespace Erdos633b
namespace Tiling

theorem six_shapes_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (hshape : SixAngleShapes d.tile T) : EightCases T := by
  obtain ⟨e, f, hshape⟩ := hshape
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  have hirrU : ¬ ∀ i, IsRational (U.angle i / Real.pi) := by
    intro h
    apply hirr
    intro i
    simpa only [U, Triangle.angle_reindex, Equiv.symm_apply_apply] using h (f i)
  change GroupOneShape d'.tile U ∨ GroupTwoShape d'.tile U at hshape
  apply eightCases_of_reindex T f
  change EightCases U
  rcases hshape with ⟨_, hshape⟩ | ⟨_, hshape⟩
  · rcases hshape with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact d'.caseSix_necessary hirrU h0 h1 h2
    · exact d'.caseSeven_necessary_of_outer_incommensurable hn hirrU h0 h1 h2
  · rcases hshape with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact d'.caseFive_necessary hirrU h0 h1 h2
    · exact d'.caseEight_necessary hirrU h0 h1 h2
    · exact d'.groupTwoSixty_necessary hirrU h0 h1 h2
    · exact d'.groupTwoDouble_necessary hirrU h0 h1 h2

theorem incommensurable_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) : EightCases T := by
  by_cases hscalene : Function.Injective T.angle
  · rcases d.incommensurable_scalene_angle_classification hirr hscalene with hrep | hshape
    · exact d.reptiling_necessary hn hrep
    · exact d.six_shapes_necessary hn hirr hshape
  · exact eightCases_of_not_injective_angles T hscalene

end Tiling

theorem hasNonsquareTiling_iff_eightCases_of_incommensurable (T : Triangle)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) :
    HasNonsquareTiling T ↔ EightCases T := by
  constructor
  · rintro ⟨n, hn, ⟨d⟩⟩
    exact d.incommensurable_necessary hn hirr
  · exact eightCases_sufficient T

theorem onlySquareTilings_iff_not_eightCases_of_incommensurable (T : Triangle)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) :
    OnlySquareTilings T ↔ ¬ EightCases T := by
  rw [onlySquareTilings_iff_not_hasNonsquareTiling,
    hasNonsquareTiling_iff_eightCases_of_incommensurable T hirr]

end Erdos633b
