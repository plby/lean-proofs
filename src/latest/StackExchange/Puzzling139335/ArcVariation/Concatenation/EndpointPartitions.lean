import StackExchange.Puzzling139335.ArcVariation.Concatenation

/-!
# Endpoint partitions give the same finite-resolution variation

The definition of `variationOn` permits increasing chains to omit interval
endpoints.  Here the competing supremum is defined using concrete chains that
begin at `a` and end at `b`, and the two suprema are proved equal by adjoining
those endpoints.
-/

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {α X : Type*} [LinearOrder α] [PseudoMetricSpace X]

/-- Scores of weakly increasing endpoint partitions of `[a,b]`. -/
def endpointScores (ε : ℝ) (f : α → X) (a b : α) : Set ℝ :=
  {r | ∃ xs, IsChainOn (Icc a b) (a :: xs ++ [b]) ∧
    r = chainScore ε f (a :: xs ++ [b])}

/-- Adjoining both endpoints to an interval chain preserves the chain property. -/
theorem IsChainOn.adjoin_endpoints {a b : α} {xs : List α}
    (hab : a ≤ b) (hxs : IsChainOn (Icc a b) xs) :
    IsChainOn (Icc a b) (a :: xs ++ [b]) := by
  have ha : IsChainOn (Icc a a) [a] := by simp [IsChainOn]
  have hb : IsChainOn (Icc b b) [b] := by simp [IsChainOn]
  have hfirst := ha.append_Icc le_rfl hab hxs
  simpa only [List.singleton_append, List.cons_append, List.nil_append] using
    hfirst.append_Icc hab le_rfl hb

omit [LinearOrder α] in
/-- The two new endpoint chords have nonnegative score. -/
theorem chainScore_le_adjoin_endpoints (ε : ℝ) (f : α → X)
    (xs : List α) (a b : α) :
    chainScore ε f xs ≤ chainScore ε f (a :: xs ++ [b]) := by
  have hright := chainScore_add_le_append ε f xs [b]
  have hleft := chainScore_add_le_append ε f [a] (xs ++ [b])
  simp only [chainScore, zero_add, add_zero, List.singleton_append] at hright hleft
  exact hright.trans hleft

/-- Every endpoint partition is one of the chains in the original definition. -/
theorem endpointScores_subset_scoresOn (ε : ℝ) (f : α → X) (a b : α) :
    endpointScores ε f a b ⊆ scoresOn ε f (Icc a b) := by
  rintro _ ⟨xs, hxs, rfl⟩
  exact ⟨a :: xs ++ [b], hxs, rfl⟩

theorem endpointScores_nonempty (ε : ℝ) (f : α → X) {a b : α} (hab : a ≤ b) :
    (endpointScores ε f a b).Nonempty := by
  have hempty : IsChainOn (Icc a b) [] := by simp [IsChainOn]
  exact ⟨chainScore ε f [a, b], [], hempty.adjoin_endpoints hab, rfl⟩

theorem endpointScores_bddAbove {ε : ℝ} {f : α → X} {a b : α}
    (hb : BddAbove (scoresOn ε f (Icc a b))) :
    BddAbove (endpointScores ε f a b) :=
  hb.mono (endpointScores_subset_scoresOn ε f a b)

/-- The endpoint-partition supremum is exactly the finite-chain supremum used
to define `variationOn`.  No continuity is needed once boundedness is supplied. -/
theorem sSup_endpointScores_eq_variationOn {ε : ℝ} {f : α → X} {a b : α}
    (hab : a ≤ b) (hb : BddAbove (scoresOn ε f (Icc a b))) :
    sSup (endpointScores ε f a b) = variationOn ε f (Icc a b) := by
  apply le_antisymm
  · apply csSup_le (endpointScores_nonempty ε f hab)
    rintro _ ⟨xs, hxs, rfl⟩
    exact chainScore_le_variationOn hb hxs
  · apply csSup_le (scoresOn_nonempty ε f (Icc a b))
    rintro _ ⟨xs, hxs, rfl⟩
    refine (chainScore_le_adjoin_endpoints ε f xs a b).trans ?_
    exact le_csSup (endpointScores_bddAbove hb)
      ⟨xs, hxs.adjoin_endpoints hab, rfl⟩

end

end Puzzling139335.ArcVariation
