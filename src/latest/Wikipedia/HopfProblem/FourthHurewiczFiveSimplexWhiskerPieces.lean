import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerGeometry

/-!
# The literal three pieces of native whiskering

The clamped times here are exactly the ones in Mathlib's path and
generalized-loop concatenations. No reparametrization or homotopy is
needed to compare the formulas.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

/-- The rectangle track has precisely the native nested-concatenation formula. -/
theorem whiskerTrack_concat (s : I) :
    whiskerTrack s =
      if (s : ℝ) ≤ 1 / 2 then
        (0, Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)))
      else
        let t := Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)
        if (t : ℝ) ≤ 1 / 2 then
          (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)), 1)
        else
          (1, σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))) := rfl

/-- The actual cube map, with its two arms and its middle in original coordinates. -/
theorem whiskerMap_concat (n : ℕ) (u : Fin (n + 1) → I) (s : I) :
    whiskerMap n (u, s) =
      if (s : ℝ) ≤ 1 / 2 then
        Fin.cons 0 (Fin.snoc (Fin.init u)
          (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)) * u (Fin.last n)))
      else
        let t := Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)
        if (t : ℝ) ≤ 1 / 2 then
          Fin.cons (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) u
        else
          Fin.cons 1 (Fin.snoc (Fin.init u)
            (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) * u (Fin.last n))) := by
  rw [whiskerMap_apply, whiskerTrack_concat]
  dsimp only
  split_ifs
  · rfl
  · simp only [one_mul, Fin.snoc_init_self]
  · rfl

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
