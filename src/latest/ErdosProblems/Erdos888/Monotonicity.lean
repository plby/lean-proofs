import ErdosProblems.Erdos888.SquarefreeReduction

/-!
# Erdős Problem 888: monotonicity in the ambient interval

These lemmas permit estimates proved at powers of two to be transported to
arbitrary parameters.
-/

namespace Erdos888

/-- Enlarging the ambient interval preserves admissibility. -/
theorem RequiredCondition.mono {A : Finset ℕ} {m n : ℕ}
    (hA : RequiredCondition A m) (hmn : m ≤ n) :
    RequiredCondition A n := by
  refine ⟨?_, hA.2⟩
  intro a ha
  have ha' := Finset.mem_Ioc.mp (hA.1 ha)
  exact Finset.mem_Ioc.mpr ⟨ha'.1, ha'.2.trans hmn⟩

/-- Attainable cardinalities remain attainable when the ambient interval is
enlarged. -/
theorem p_mono_left {m n k : ℕ} (hmn : m ≤ n) (hk : p m k) : p n k := by
  obtain ⟨A, hA, hcard⟩ := hk
  exact ⟨A, hA.mono hmn, hcard⟩

/-- The unrestricted extremal cardinality is monotone. -/
theorem monotone_extremalSize : Monotone extremalSize := by
  intro m n hmn
  exact le_extremalSize_of_p (p_mono_left hmn (p_extremalSize m))

/-- Squarefree attainable cardinalities also persist after enlarging the
ambient interval. -/
theorem squarefreeP_mono_left {m n k : ℕ} (hmn : m ≤ n)
    (hk : squarefreeP m k) : squarefreeP n k := by
  obtain ⟨A, hA, hsf, hcard⟩ := hk
  exact ⟨A, hA.mono hmn, hsf, hcard⟩

/-- The squarefree extremal cardinality is monotone. -/
theorem monotone_squarefreeExtremalSize : Monotone squarefreeExtremalSize := by
  intro m n hmn
  obtain ⟨A, hA, hsf, hcard⟩ := squarefreeP_squarefreeExtremalSize m
  rw [← hcard]
  exact card_le_squarefreeExtremalSize (hA.mono hmn) hsf

end Erdos888
