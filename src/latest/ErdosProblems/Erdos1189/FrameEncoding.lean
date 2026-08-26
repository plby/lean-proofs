/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Representing an arithmetic generalized frame and its remainder by finite choices.
Informal source: BBMST Section 7.2.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameRemainder
import ErdosProblems.Erdos1189.FiniteFamilyEncoding
import ErdosProblems.Erdos1189.CompressedRanks

namespace Erdos1189

open Finset

lemma frameAllowedModuli_compressedRank {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (i : PrimeCoordinate N) (T : ℕ) :
    frameAllowedModuli (compressedRank rank) i T = frameAllowedModuli rank i T := by
  unfold frameAllowedModuli frameExponentBound
  rw [rankPrefix_compressedRank]

lemma largeFrameUnion_eq_subtype {N : ℕ} {H : ℕ → Grid.Box (@coordinateSize N)}
    {D : Finset ℕ} {δ : ℝ} (frame : Grid.GeneralizedFrame H D δ) (T : ℕ) :
    (univ.biUnion (fun i : largeCoordinates N T => frame.families i)) =
      largeFrameUnion frame T := by
  ext d
  simp only [largeFrameUnion, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.property, hi⟩
  · rintro ⟨i, hi, hd⟩
    exact ⟨⟨i, hi⟩, hd⟩

lemma frame_mem_family_encoding {N : ℕ} {D : Finset ℕ} {residue : ℕ → ℕ} {δ : ℝ}
    (frame : Grid.GeneralizedFrame (fun d => congruenceBox N d (residue d)) D δ)
    (hδ : 0 < δ) (hN : N ≠ 0) (hD : ∀ d ∈ D, d ∣ N) {T : ℕ}
    (hT : 1 / δ ≤ (T : ℝ)) :
    D ∈ familyUnionUniverse
      (fun i : largeCoordinates N T => frameAllowedModuli (compressedRank frame.rank) i T)
      (fun i => (frame.families i).card) (boundedProfileModuli N N.factorization)
      (D \ largeFrameUnion frame T).card := by
  classical
  have h := mem_familyUnionUniverse
    (fun i : largeCoordinates N T => frameAllowedModuli (compressedRank frame.rank) i T)
    (fun i => (frame.families i).card) (boundedProfileModuli N N.factorization)
    (D \ largeFrameUnion frame T).card (fun i => frame.families i) (D \ largeFrameUnion frame T)
    (fun i => ⟨by
      rw [frameAllowedModuli_compressedRank]
      exact frame_family_subset_allowed frame hδ hN hD hT i, rfl⟩)
    (fun d hd => mem_boundedProfileModuli hN (hD d (mem_sdiff.mp hd).1)
      (fun p => (Nat.factorization_le_iff_dvd
        (ne_zero_of_dvd_ne_zero hN (hD d (mem_sdiff.mp hd).1)) hN).mpr
          (hD d (mem_sdiff.mp hd).1) p)) rfl
  rwa [largeFrameUnion_eq_subtype, union_sdiff_of_subset (largeFrameUnion_subset frame T)] at h

end Erdos1189
