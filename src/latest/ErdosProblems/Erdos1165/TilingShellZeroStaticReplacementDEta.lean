/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroDEtaTerminal

/-!
# `D_η` transport under a static shell-zero replacement

The moved carrier is a fixed set of canonical domino bases.  On it, the
source is in `V₂(I₁)` and the replacement is in `V₂(I₁) ∪ V₂(I₀)`.  Off it,
the two endpoint local times agree.  These pathwise facts preserve the exact
`V₁` set and enlarge the `D_η` classification to `Dtilde_η`.
-/

namespace Erdos1165.TilingShellZeroStaticReplacementDEta

open HLOZShellZeroReplacementWindows LazyDecomposition
open TilingLazyDecomposition TilingShellZeroSourcePartition
open HLOZThetaSourceBalance

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem not_vOne_of_sourceVTwo
    {t : DominoTiling} {m w : ℕ} {s : WalkPath} {n : ℕ} {b : Point}
    (hVTwo : tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n b) :
    ¬tilingVOneAt t m s n b := by
  have hbaseLt := (mem_shellZeroSourceTotalWindow.mp hVTwo.2).2
  have hpartnerLt : localTime s n (tilingPartner t b) < m :=
    lt_of_le_of_lt hVTwo.1 hbaseLt
  unfold tilingVOneAt
  omega

private theorem not_vOne_of_replacementVTwo
    {t : DominoTiling} {m w : ℕ} {s : WalkPath} {n : ℕ} {b : Point}
    (hVTwo : tilingVTwoAt t (shellZeroReplacementTotalWindow m w) s n b) :
    ¬tilingVOneAt t m s n b := by
  have hbaseGt : m < localTime s n b := by
    have hwindow :=
      (mem_shellZeroReplacementTotalWindow.mp hVTwo.2).1
    omega
  unfold tilingVOneAt
  omega

private theorem tilingVOneAt_iff_of_endpoint_eq
    {t : DominoTiling} {m : ℕ}
    {s s' : WalkPath} {n n' : ℕ} {b : Point}
    (hbase : localTime s' n' b = localTime s n b)
    (hpartner : localTime s' n' (tilingPartner t b) =
      localTime s n (tilingPartner t b)) :
    tilingVOneAt t m s' n' b ↔ tilingVOneAt t m s n b := by
  unfold tilingVOneAt
  rw [hbase, hpartner]

private theorem mem_visitedTilingBases_of_vOneAt
    {t : DominoTiling} {m : ℕ} {s : WalkPath} {n : ℕ} {b : Point}
    (hm : 0 < m) (hbase : tilingBase t b = b)
    (hVOne : tilingVOneAt t m s n b) :
    b ∈ visitedTilingBases t s n := by
  rw [visitedTilingBases, Finset.mem_image]
  rcases hVOne with hleft | hright
  · refine ⟨b, ?_, hbase⟩
    apply (mem_visitedSites_iff_localTime_pos s n b).2
    omega
  · refine ⟨tilingPartner t b, ?_, ?_⟩
    · apply (mem_visitedSites_iff_localTime_pos s n
        (tilingPartner t b)).2
      omega
    · rw [tilingBase_partner, hbase]

/-- The literal `V₁` Finset is unchanged by a static replacement. -/
theorem tilingVOneBases_eq_of_staticReplacement
    {t : DominoTiling} {m w : ℕ}
    {s s' : WalkPath} {n n' : ℕ} (S : Finset Point)
    (hm : 0 < m)
    (hsource : ∀ b ∈ S,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n b)
    (hreplacement : ∀ b ∈ S,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w) s' n' b ∨
        tilingVTwoAt t (shellZeroReplacementTotalWindow m w) s' n' b)
    (hbase : ∀ b, IsTilingBase t b → b ∉ S →
      localTime s' n' b = localTime s n b)
    (hpartner : ∀ b, IsTilingBase t b → b ∉ S →
      localTime s' n' (tilingPartner t b) =
        localTime s n (tilingPartner t b)) :
    tilingVOneBases t m s' n' = tilingVOneBases t m s n := by
  classical
  ext b
  simp only [tilingVOneBases, Finset.mem_filter]
  constructor
  · rintro ⟨hbVisited', hbVOne'⟩
    have hbIsBase := isTilingBase_of_mem_visitedTilingBases hbVisited'
    have hbNotS : b ∉ S := by
      intro hbS
      rcases hreplacement b hbS with hbSource | hbReplacement
      · exact not_vOne_of_sourceVTwo hbSource hbVOne'
      · exact not_vOne_of_replacementVTwo hbReplacement hbVOne'
    have hbVOne : tilingVOneAt t m s n b :=
      (tilingVOneAt_iff_of_endpoint_eq
        (hbase b hbIsBase hbNotS) (hpartner b hbIsBase hbNotS)).mp hbVOne'
    have hbFix : tilingBase t b = b := by
      rcases Finset.mem_image.mp hbVisited' with ⟨y, _hy, rfl⟩
      exact TilingSpatialInsertionFiber.tilingBase_idem t y
    exact ⟨mem_visitedTilingBases_of_vOneAt hm hbFix hbVOne, hbVOne⟩
  · rintro ⟨hbVisited, hbVOne⟩
    have hbIsBase := isTilingBase_of_mem_visitedTilingBases hbVisited
    have hbNotS : b ∉ S := by
      intro hbS
      exact not_vOne_of_sourceVTwo (hsource b hbS) hbVOne
    have hbVOne' : tilingVOneAt t m s' n' b :=
      (tilingVOneAt_iff_of_endpoint_eq
        (hbase b hbIsBase hbNotS) (hpartner b hbIsBase hbNotS)).mpr hbVOne
    have hbFix : tilingBase t b = b := by
      rcases Finset.mem_image.mp hbVisited with ⟨y, _hy, rfl⟩
      exact TilingSpatialInsertionFiber.tilingBase_idem t y
    exact ⟨mem_visitedTilingBases_of_vOneAt hm hbFix hbVOne', hbVOne'⟩

/-- Static endpoint transport turns the source `D_η` classification into
the replacement `Dtilde_η` classification.  The two terminal clauses are
kept explicit here because the caller obtains them from the common physical
prefix endpoint after reconstructing the replacement clock. -/
theorem tilingDtildeEtaAt_of_staticReplacement
    {t : DominoTiling} {m k w low : ℕ}
    {s s' : WalkPath} {n n' : ℕ} (S : Finset Point)
    (hm : 0 < m)
    (hD : tilingDEtaAt t m k w low s n)
    (hsource : ∀ b ∈ S,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n b)
    (hreplacement : ∀ b ∈ S,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w) s' n' b ∨
        tilingVTwoAt t (shellZeroReplacementTotalWindow m w) s' n' b)
    (hbase : ∀ b, IsTilingBase t b → b ∉ S →
      localTime s' n' b = localTime s n b)
    (hpartner : ∀ b, IsTilingBase t b → b ∉ S →
      localTime s' n' (tilingPartner t b) =
        localTime s n (tilingPartner t b))
    (hterminal : localTime s' n' (s' n') = m)
    (hterminalVOne : tilingVOneAt t m s' n' (tilingBase t (s' n'))) :
    tilingDtildeEtaAt t m k w low s' n' := by
  refine ⟨?_, ?_, hterminal, hterminalVOne⟩
  · rw [tilingVOneBases_eq_of_staticReplacement S hm hsource hreplacement
      hbase hpartner]
    exact hD.1
  · intro b hbIsBase
    by_cases hbS : b ∈ S
    · rcases hreplacement b hbS with hbSource | hbReplacement
      · exact Or.inr (Or.inl hbSource)
      · exact Or.inr (Or.inr (Or.inl hbReplacement))
    · have hbaseEq := hbase b hbIsBase hbS
      have hpartnerEq := hpartner b hbIsBase hbS
      rcases hD.2.1 b hbIsBase with hbVOne | hbVTwo | hbVThree
      · left
        exact (tilingVOneAt_iff_of_endpoint_eq hbaseEq hpartnerEq).mpr hbVOne
      · right; left
        unfold tilingVTwoAt at hbVTwo ⊢
        simpa only [hbaseEq, hpartnerEq] using hbVTwo
      · right; right; right
        unfold tilingVThreeAt at hbVThree ⊢
        simpa only [hbaseEq, hpartnerEq] using hbVThree

end

end Erdos1165.TilingShellZeroStaticReplacementDEta
