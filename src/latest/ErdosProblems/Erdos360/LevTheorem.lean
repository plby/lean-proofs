import ErdosProblems.Erdos360.LevIncrement
import ErdosProblems.Erdos360.LevSeed
import ErdosProblems.Erdos360.FiniteSourceAssembly

/-!
# Lev's theorem for Erdős 360

This file connects the sharp multiple-summand increment to the indexed
prefix estimate used by Lev's odd-family seed theorem.  It then packages the
seed theorem as the high-multiplicity principle consumed by the finite source
assembly.
-/

open scoped BigOperators Pointwise

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- The sharp increment telescopes over pools listed in nondecreasing order
of the diameters of their subset-sum sets. -/
theorem hasLevSharpPrefixTheorem_of_two_le
    {n0 : ℕ} (hn0 : 2 ≤ n0) : HasLevSharpPrefixTheorem n0 := by
  intro parts
  induction parts using List.reverseRecOn with
  | nil =>
      intro _hsorted _hparts
      simp [levIteratedSubsetSum]
  | append_singleton front P ih =>
      intro hsorted hparts
      have hsortedParts := List.pairwise_append.mp hsorted
      have hfrontSorted :
          front.Pairwise (fun Q R ↦ levPoolMass Q ≤ levPoolMass R) :=
        hsortedParts.1
      have hfrontP : ∀ Q ∈ front, levPoolMass Q ≤ levPoolMass P := by
        intro Q hQ
        exact hsortedParts.2.2 Q hQ P (by simp)
      have hP := hparts P (by simp)
      have hfrontParts : ∀ Q ∈ front,
          n0 ≤ Q.subsetSum.card ∧
            ¬ ContainedInNontrivialAP Q.subsetSum := by
        intro Q hQ
        exact hparts Q (by simp [hQ])
      have hprefix := ih hfrontSorted hfrontParts
      have hv : 0 < levPoolMass P := by
        have hupper := card_subsetSum_le_levPoolMass_add_one P
        omega
      have hearlier : ∀ A ∈ front.map Finset.subsetSum,
          0 ∈ A ∧ A ⊆ Finset.Icc 0 (levPoolMass P) ∧ n0 ≤ A.card := by
        intro A hA
        obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hA
        refine ⟨Finset.zero_mem_subsetSum, ?_, (hfrontParts Q hQ).1⟩
        intro s hs
        have hsI := Finset.mem_Icc.mp (subsetSum_subset_Icc_levPoolMass Q hs)
        exact Finset.mem_Icc.mpr ⟨hsI.1, hsI.2.trans (hfrontP Q hQ)⟩
      have hincrement := lev_multi_increment_uniform_sharp
        (parts := front.map Finset.subsetSum) (B := P.subsetSum)
        (v := levPoolMass P) (n₀ := n0) hn0 hv hearlier
        Finset.zero_mem_subsetSum (levPoolMass_mem_subsetSum P)
        (subsetSum_subset_Icc_levPoolMass P) hP.1 hP.2
      rw [levFinsetSum_subsetSums] at hincrement
      have hincrement' :
          (levIteratedSubsetSum front).card +
              (min (levPoolMass P - 1)
                ((front.length + 1) * (n0 - 2)) + 1) ≤
            (levIteratedSubsetSum (front ++ [P])).card := by
        rw [← levIteratedSubsetSum_singleton P,
          ← levIteratedSubsetSum_append front [P]] at hincrement
        simpa only [List.length_map] using hincrement
      have hfrontSum :
          (∑ i ∈ Finset.Icc 1 front.length,
              (min (levPoolMass ((front ++ [P]).getD (i - 1) ∅) - 1)
                (i * (n0 - 2)) + 1)) =
            ∑ i ∈ Finset.Icc 1 front.length,
              (min (levPoolMass (front.getD (i - 1) ∅) - 1)
                (i * (n0 - 2)) + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiI := Finset.mem_Icc.mp hi
        rw [List.getD_append front [P] ∅ (i - 1) (by omega)]
      have hlast : (front ++ [P]).getD front.length ∅ = P := by
        rw [List.getD_append_right front [P] ∅ front.length le_rfl]
        simp
      simp only [List.length_append, List.length_singleton]
      rw [Finset.sum_Icc_succ_top (by omega), hfrontSum]
      have hlastIndex : front.length + 1 - 1 = front.length := by omega
      rw [hlastIndex, hlast]
      calc
        1 +
              ((∑ i ∈ Finset.Icc 1 front.length,
                  (min (levPoolMass (front.getD (i - 1) ∅) - 1)
                    (i * (n0 - 2)) + 1)) +
                (min (levPoolMass P - 1)
                  ((front.length + 1) * (n0 - 2)) + 1)) =
            (1 + ∑ i ∈ Finset.Icc 1 front.length,
              (min (levPoolMass (front.getD (i - 1) ∅) - 1)
                (i * (n0 - 2)) + 1)) +
              (min (levPoolMass P - 1)
                ((front.length + 1) * (n0 - 2)) + 1) := by omega
        _ ≤ (levIteratedSubsetSum front).card +
              (min (levPoolMass P - 1)
                ((front.length + 1) * (n0 - 2)) + 1) :=
          Nat.add_le_add_right hprefix _
        _ ≤ (levIteratedSubsetSum (front ++ [P])).card := hincrement'

/-- Lev's exact odd-family seed theorem, with no remaining additive input. -/
theorem hasCFPLevSeedTheorem (n0 : ℕ) (hn0 : 3 ≤ n0) :
    HasCFPLevSeedTheorem n0 :=
  hasCFPLevSeedTheorem_of_sharpPrefix
    (hasLevSharpPrefixTheorem_of_two_le (by omega))

/-- The high-multiplicity interval principle required by the finite source
assembly, obtained from the sharp increment through Lev's seed theorem. -/
theorem cfpLevHighMultiplicityPrinciple :
    CFPLevHighMultiplicityPrinciple := by
  intro parts ell nzero diameter hfamily hnzero hmultiplicity
  have hlength : parts.length = ell := hfamily.1
  have hfamily' :
      IsCFPLevFamily parts parts.length nzero diameter := by
    simpa only [hlength] using hfamily
  have hmultiplicity' :
      2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ parts.length := by
    simpa only [hlength] using hmultiplicity
  have hinterval := hasCFPLevInterval_of_high_multiplicity_of_seedTheorem
    hfamily' hnzero hmultiplicity'
    (hasCFPLevSeedTheorem nzero hnzero)
  simpa only [hlength] using hinterval

end Erdos360
