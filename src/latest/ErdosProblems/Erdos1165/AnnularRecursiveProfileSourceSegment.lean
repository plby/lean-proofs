/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileSourceRecovery
import ErdosProblems.Erdos1165.AnnularLiteralNestedProfileTailUpper

/-!
# Consecutive recursive-profile data from a successful stopped path

The recursive source parser is phrased in terms of an
`ActualProfileSegmentData`.  This file constructs that data canonically from
one fixed successful profile.  In particular, no extra completion premise is
needed at the padded asymmetric interface: completion of every prescribed
gap follows from the common global outer-exit time.
-/

namespace Erdos1165.AnnularRecursiveProfileSourceSegment

open AnnularLiteralNestedProfileTailUpper AnnularProfileClocks
open AnnularProfileLiteralAtoms AnnularRecursiveProfileActualParser
open AppendixFirstMoment ProfileListExponent ProfileSmallBall ThickPoint

noncomputable section

/-- Removing the first scale from a nonterminal profile segment leaves the
segment beginning at the next scale. -/
theorem profileSegmentValues_succ
    {n k : ℕ} (hk : k < n) (m : Profile n) :
    profileSegmentValues m k =
      profileAtScale m k :: profileSegmentValues m (k + 1) := by
  unfold profileSegmentValues
  have hlen : n + 1 - k = (n + 1 - (k + 1)) + 1 := by omega
  rw [hlen, List.ofFn_succ]
  congr 1
  rw [List.ofFn_inj]
  funext i
  congr 1
  simp only [Fin.val_succ]
  omega

/-- The terminal profile segment consists of the value at scale `n`. -/
theorem profileSegmentValues_self (m : Profile n) :
    profileSegmentValues m n = [profileAtScale m n] := by
  unfold profileSegmentValues
  simp

/-- At an internal scale, the completed-count clock is the corresponding
entry of a fixed successful profile. -/
theorem profileCompletedCount_eq_profileAtScale
    {omega : StepPath} {n horizon k : ℕ} {x : Point} {profileDelta : ℝ}
    {m : Profile n} (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hfixed : FixedSuccessfulProfile n profileDelta m
      (excursionProfile (trajectory omega) n horizon x)) :
    profileCompletedCount (trajectory omega) n horizon x k =
      profileAtScale m k := by
  let i : Fin (n - 1) := ⟨k - 2, by omega⟩
  have hscale : scaleIndex i = k := by
    unfold scaleIndex
    dsimp only [i]
    omega
  have hcount := fixedProfile_count_eq hfixed i
  calc
    profileCompletedCount (trajectory omega) n horizon x k = m i := by
      simpa only [hscale] using hcount
    _ = profileAtScale m k := by
      rw [← profileAtScale_scaleIndex m i, hscale]

/-- Every prescribed gap at an arbitrary internal scale is complete before
the common global exit. -/
theorem profileGapExit_le_of_fixedSuccessfulProfile
    {omega : StepPath} {n horizon k : ℕ} {x : Point} {profileDelta : ℝ}
    {m : Profile n} (hn : 2 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n profileDelta m
      (excursionProfile (trajectory omega) n horizon x))
    (j : Fin (profileAtScale m k)) :
    profileGapExitTime (trajectory omega) n horizon x k j ≤ horizon := by
  let i : Fin (n - 1) := ⟨k - 2, by omega⟩
  have hscale : scaleIndex i = k := by
    unfold scaleIndex
    dsimp only [i]
    omega
  let j' : Fin (m i) := ⟨j, by
    simpa only [← profileAtScale_scaleIndex m i, hscale] using j.isLt⟩
  have hcomplete := fixedProfile_gapExit_le (s := trajectory omega)
    (Nat.one_le_of_lt hn) hexit hx
    (Proposition13Assembly.adjacent_trajectory_succ omega) hfixed i j'
  simpa only [hscale, j'] using hcomplete

/-- Every prescribed gap at a retained internal scale is complete as soon as
the actual completed-count clock agrees with the prescribed profile entry.
Unlike `profileGapExit_le_of_fixedSuccessfulProfile`, this lemma does not ask
for the level-one successful condition or for any profile coordinates below
`k`. -/
theorem profileGapExit_le_of_profileCompletedCount_eq
    {omega : StepPath} {n horizon k : ℕ} {x : Point}
    {m : Profile n} (hn : 2 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hcount : profileCompletedCount (trajectory omega) n horizon x k =
      profileAtScale m k)
    (j : Fin (profileAtScale m k)) :
    profileGapExitTime (trajectory omega) n horizon x k j ≤ horizon := by
  apply profileGapExitTime_le_of_globalExit (Nat.one_le_of_lt hn)
    (by omega) hkn hexit hx
      (Proposition13Assembly.adjacent_trajectory_succ omega)
  apply profileInnerHitTime_le_horizon_of_lt_count
  rw [hcount]
  exact j.isLt

/-- Canonical recursive parser input for a constrained profile tail when no
condition is imposed on the earlier profile coordinates.  This is the
arbitrary-start form needed when a short asymmetric buffer erases the first
one or two annular generations. -/
def actualProfileSegmentDataOfTailCounts
    {omega : StepPath} {n horizon : ℕ} {x : Point} {profileDelta : ℝ}
    {m : Profile n} (hn : 2 ≤ n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hm : IsConstrainedProfile profileDelta m) (hdelta : profileDelta ≤ 1)
    (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hcounts : ∀ r, k ≤ r → r ≤ n →
      profileCompletedCount (trajectory omega) n horizon x r =
        profileAtScale m r) :
    ActualProfileSegmentData omega n horizon x k
      (profileSegmentValues m k) := by
      by_cases hkn' : k = n
      · subst k
        rw [profileSegmentValues_self]
        apply ActualProfileSegmentData.singleton
        · let i : Fin (n - 1) := ⟨n - 2, by omega⟩
          have hscale : scaleIndex i = n := by
            unfold scaleIndex
            dsimp only [i]
            omega
          have htwo := constrainedProfile_entry_two_le hdelta hm i
          simpa only [← profileAtScale_scaleIndex m i, hscale] using
            (show 0 < m i by omega)
        · exact hcounts n le_rfl le_rfl
        · intro i hi
          exact profileGapExit_le_of_profileCompletedCount_eq hn
            (by omega) le_rfl hexit hx (hcounts n le_rfl le_rfl) ⟨i, hi⟩
      · rw [profileSegmentValues_succ (lt_of_le_of_ne hkn hkn')]
        let tailData := actualProfileSegmentDataOfTailCounts hn hexit hx
          hm hdelta (k + 1) (by omega) (by omega)
          (fun r hkr hrn ↦ hcounts r (by omega) hrn)
        cases htail : profileSegmentValues m (k + 1) with
        | nil =>
            have hlen := profileSegmentValues_length m (k + 1)
            rw [htail] at hlen
            simp only [List.length_nil] at hlen
            omega
        | cons b rest =>
            apply ActualProfileSegmentData.cons
            · let i : Fin (n - 1) := ⟨k - 2, by omega⟩
              have hscale : scaleIndex i = k := by
                unfold scaleIndex
                dsimp only [i]
                omega
              have htwo := constrainedProfile_entry_two_le hdelta hm i
              simpa only [← profileAtScale_scaleIndex m i, hscale] using
                (show 0 < m i by omega)
            · exact hcounts k le_rfl hkn
            · intro i hi
              exact profileGapExit_le_of_profileCompletedCount_eq hn hk2 hkn
                hexit hx (hcounts k le_rfl hkn) ⟨i, hi⟩
            · simpa only [htail] using tailData
termination_by n + 1 - k

/-- Canonical consecutive parser input for every segment `k,...,n` of a
fixed successful profile. -/
def actualProfileSegmentDataOfFixedSuccessful
    {omega : StepPath} {n horizon : ℕ} {x : Point} {profileDelta : ℝ}
    {m : Profile n} (hn : 2 ≤ n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hm : IsConstrainedProfile profileDelta m) (hdelta : profileDelta ≤ 1)
    (hfixed : FixedSuccessfulProfile n profileDelta m
      (excursionProfile (trajectory omega) n horizon x))
    (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    ActualProfileSegmentData omega n horizon x k
      (profileSegmentValues m k) := by
      by_cases hkn' : k = n
      · subst k
        rw [profileSegmentValues_self]
        apply ActualProfileSegmentData.singleton
        · let i : Fin (n - 1) := ⟨n - 2, by omega⟩
          have hscale : scaleIndex i = n := by
            unfold scaleIndex
            dsimp only [i]
            omega
          have htwo := constrainedProfile_entry_two_le hdelta hm i
          simpa only [← profileAtScale_scaleIndex m i, hscale] using
            (show 0 < m i by omega)
        · exact profileCompletedCount_eq_profileAtScale
            (by omega) le_rfl hfixed
        · intro i hi
          exact profileGapExit_le_of_fixedSuccessfulProfile hn
            (by omega) le_rfl hexit hx hfixed ⟨i, hi⟩
      · rw [profileSegmentValues_succ (lt_of_le_of_ne hkn hkn')]
        let tailData := actualProfileSegmentDataOfFixedSuccessful hn hexit hx
          hm hdelta hfixed (k + 1) (by omega) (by omega)
        cases htail : profileSegmentValues m (k + 1) with
        | nil =>
            have hlen := profileSegmentValues_length m (k + 1)
            rw [htail] at hlen
            simp only [List.length_nil] at hlen
            omega
        | cons b rest =>
            apply ActualProfileSegmentData.cons
            · let i : Fin (n - 1) := ⟨k - 2, by omega⟩
              have hscale : scaleIndex i = k := by
                unfold scaleIndex
                dsimp only [i]
                omega
              have htwo := constrainedProfile_entry_two_le hdelta hm i
              simpa only [← profileAtScale_scaleIndex m i, hscale] using
                (show 0 < m i by omega)
            · exact profileCompletedCount_eq_profileAtScale hk2 hkn hfixed
            · intro i hi
              exact profileGapExit_le_of_fixedSuccessfulProfile hn hk2 hkn
                hexit hx hfixed ⟨i, hi⟩
            · simpa only [htail] using tailData
termination_by n + 1 - k

/-- Successful stopped paths carry a canonical recursive source segment for
the profile actually read from their clocks. -/
def actualProfileSegmentDataOfSuccessfulPoint
    {omega : StepPath} {n horizon k : ℕ} {x : Point} {profileDelta : ℝ}
    (hn : 2 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hdelta : profileDelta ≤ 1)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hsuccess : SuccessfulPoint (trajectory omega) n horizon profileDelta x) :
    ActualProfileSegmentData omega n horizon x k
      (profileSegmentValues
        (internalProfile (excursionProfile (trajectory omega) n horizon x))
        k) :=
  actualProfileSegmentDataOfFixedSuccessful hn hexit hsuccess.1
    (internalProfile_isConstrained hsuccess.2)
    hdelta
    (fixedSuccessfulProfile_internalProfile hsuccess.2) k hk2 hkn

end

end Erdos1165.AnnularRecursiveProfileSourceSegment
