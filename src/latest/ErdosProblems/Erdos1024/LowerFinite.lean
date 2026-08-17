/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.LowerRestriction

/-!
# The finite Phelps--Rödl lower-bound engine

The theorem in this file has no asymptotic notation.  Given explicit natural
parameters satisfying two displayed real inequalities, it produces an
independent set larger than the proposed threshold.
-/

namespace Erdos1024
namespace Lower

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem exists_independent_gt_of_parameters {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H)
    {K A B T : ℕ} [NeZero K] (hB : 0 < B)
    (hA : A ≤ Fintype.card V) {L : ℝ} (hL : 0 < L)
    (hscore : L ≤
      (Fintype.card V : ℝ) / K -
        (((Fintype.card V) ^ 3 : ℕ) : ℝ) / (K : ℝ) ^ 6 -
        (Fintype.card V : ℝ) *
          (((Fintype.card V + 1 : ℕ) : ℝ) ^ (A + 1) *
            Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
              ((K : ℝ) * B) - (T : ℝ) / B)))
    (hweighted : ((8 * (A * (B * 4 ^ B) + T) : ℕ) : ℝ) < B * L) :
    ∃ I : Finset V, Independent H I ∧ A < I.card := by
  classical
  by_contra hnone
  push Not at hnone
  have hcard : ∀ Z ∈ independentSets H, Z.card ≤ A := by
    intro Z hZ
    exact hnone Z (mem_independentSets.mp hZ)
  obtain ⟨omega, -, hYcard, hYtri, hYext⟩ :=
    exists_large_pruned_sample h3 hlin hB hA hcard hL hscore
      (K := K) (T := T)
  let Y : Finset V := prunedSet H omega
  let G : System Y := restrictSystem H Y
  have h3G : ThreeUniform G := restrict_threeUniform h3 Y
  have hlinG : Linear G := restrict_linear hlin Y
  have htriG : TriangleFree G := by
    exact restrict_triangleFree hYtri
  have hcardG : ∀ I : Finset Y, Independent G I → I.card ≤ A := by
    intro I hI
    rw [independent_restrict_iff] at hI
    rw [← card_valMap Y I]
    exact hnone (valMap Y I) hI
  have hextG : ∀ I : Finset Y, Independent G I →
      totalTruncatedExtension G B I ≤ T := by
    intro I hI
    have hmapInd : Independent H (valMap Y I) := independent_restrict_iff.mp hI
    have hsample :
        ∑ v ∈ Y \ valMap Y I, truncatedExtension H B v (valMap Y I) < T := by
      exact hYext (valMap Y I) hmapInd
    exact (totalTruncatedExtension_restrict_le h3 B I).trans
      (Nat.le_of_lt hsample)
  have hweightNat := weighted_numeric_consequence h3G hlinG htriG
    hB hcardG hextG
  have hweight : ((B * Fintype.card Y : ℕ) : ℝ) ≤
      ((8 * (A * (B * 4 ^ B) + T) : ℕ) : ℝ) := by
    exact_mod_cast hweightNat
  have hYcard' : L ≤ (Fintype.card Y : ℝ) := by
    simpa [Y] using hYcard
  have hBL : (B : ℝ) * L ≤ B * Fintype.card Y := by
    gcongr
  have hcast : ((B * Fintype.card Y : ℕ) : ℝ) =
      (B : ℝ) * Fintype.card Y := by norm_num
  rw [hcast] at hweight
  exact (not_lt_of_ge (hBL.trans hweight)) hweighted

end Lower
end Erdos1024

#print axioms Erdos1024.Lower.exists_independent_gt_of_parameters
