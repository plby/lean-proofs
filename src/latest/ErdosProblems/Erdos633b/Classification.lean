import ErdosProblems.Erdos633b.FiniteCaseNecessity
import ErdosProblems.Erdos633b.Sufficiency

/-! Complete eight-case classification for actual finite congruent-triangle tilings. -/

namespace Erdos633b
namespace Tiling

/-- Every actual nonsquare congruent-triangle dissection has an eight-case outer triangle. -/
theorem eightCases_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) : EightCases T := by
  by_contra hnot
  obtain ⟨e, f, p, hp, hw, ha⟩ := d.counterexample_finite_angle_pairs hn hnot
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  exact hnot (eightCases_of_reindex T f (d'.finite_angle_pair_necessary p hp hw ha))

end Tiling

/-- The full necessary-and-sufficient eight-case classification, with no angle hypotheses. -/
theorem hasNonsquareTiling_iff_eightCases (T : Triangle) :
    HasNonsquareTiling T ↔ EightCases T := by
  constructor
  · rintro ⟨n, hn, ⟨d⟩⟩
    exact d.eightCases_necessary hn
  · exact eightCases_sufficient T

/-- Exactly the triangles outside the eight cases have only square congruent dissections. -/
theorem onlySquareTilings_iff_not_eightCases (T : Triangle) :
    OnlySquareTilings T ↔ ¬ EightCases T := by
  rw [onlySquareTilings_iff_not_hasNonsquareTiling, hasNonsquareTiling_iff_eightCases T]

end Erdos633b
