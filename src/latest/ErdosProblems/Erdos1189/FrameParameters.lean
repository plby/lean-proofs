/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite parameters for generalized frame encodings.
Informal source: BBMST equation (30).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameEncoding

namespace Erdos1189

open Finset

lemma card_primeCoordinate_le (N : ℕ) :
    Fintype.card (PrimeCoordinate N) ≤ simpsonWeight N := by
  rw [← sum_coordinateSize, ← card_univ, card_eq_sum_ones]
  apply sum_le_sum
  intro i _
  have hp := (Nat.prime_of_mem_primeFactors i.1.property).two_le
  change 2 ≤ coordinateSize i at hp
  omega

abbrev FrameCode (N T k : ℕ) :=
  (PrimeCoordinate N → Fin (k + 1)) × (largeCoordinates N T → Fin (k + 1)) × Fin (k + 1)

lemma card_frameCode_le {N T k : ℕ} (hW : simpsonWeight N ≤ k) :
    Fintype.card (FrameCode N T k) ≤ (k + 1) ^ (2 * k + 1) := by
  have hdim := (card_primeCoordinate_le N).trans hW
  have hlarge : Fintype.card (largeCoordinates N T) ≤ k := by
    exact (Fintype.card_subtype_le _).trans hdim
  simp only [FrameCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  calc
    _ = (k + 1) ^ (Fintype.card (PrimeCoordinate N) +
        Fintype.card (largeCoordinates N T) + 1) := by
      rw [pow_succ, pow_add]
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

noncomputable def validFrameCodes (N T k : ℕ) (η : ℝ) : Finset (FrameCode N T k) := by
  classical
  exact univ.filter (fun c => Function.Injective (fun i => (c.1 i).val) ∧
    (∀ i, (c.2.1 i).val ≤ coordinateSize i.val - 1) ∧
    (largeCoordinateWeight N T : ℝ) + c.2.2.val ≤ k + η * simpsonWeight N)

noncomputable def frameCodeUniverse {N T k : ℕ} (c : FrameCode N T k) :
    Finset (Finset ℕ) :=
  familyUnionUniverse (fun i : largeCoordinates N T =>
    frameAllowedModuli (fun j => (c.1 j).val) i T)
    (fun i => (c.2.1 i).val) (boundedProfileModuli N N.factorization) c.2.2.val

noncomputable def frameUniverse (N T k : ℕ) (η : ℝ) : Finset (Finset ℕ) :=
  (validFrameCodes N T k η).biUnion frameCodeUniverse

lemma mem_frameUniverse {N T k : ℕ} {D : Finset ℕ} {residue : ℕ → ℕ} {δ η : ℝ}
    (frame : Grid.GeneralizedFrame (fun d => congruenceBox N d (residue d)) D δ)
    (hδ : 0 < δ) (hN : N ≠ 0) (hD : ∀ d ∈ D, d ∣ N)
    (hT : 1 / δ ≤ (T : ℝ)) (hk : D.card = k) (hW : simpsonWeight N ≤ k)
    (hsize : (1 - η) * simpsonWeight N ≤ ∑ i, ((frame.families i).card : ℝ)) :
    D ∈ frameUniverse N T k η := by
  classical
  let r : PrimeCoordinate N → Fin (k + 1) := fun i =>
    ⟨compressedRank frame.rank i,
      (compressedRank_lt_card frame.rank i).trans_le (by
        have := (card_primeCoordinate_le N).trans hW
        omega)⟩
  let sizes : largeCoordinates N T → Fin (k + 1) := fun i =>
    ⟨(frame.families i).card, by
      have := card_le_card (frame.subset i)
      omega⟩
  let x : Fin (k + 1) := ⟨(D \ largeFrameUnion frame T).card, by
    have := card_le_card (sdiff_subset (s := D) (t := largeFrameUnion frame T))
    omega⟩
  let c : FrameCode N T k := (r, sizes, x)
  apply mem_biUnion.mpr
  refine ⟨c, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
  · refine ⟨compressedRank_injective frame.rank frame.rank_injective,
      fun i => frame.card_le i, ?_⟩
    have h := largeFrame_remainder_budget frame hT hsize
    simpa only [hk] using h
  · exact frame_mem_family_encoding frame hδ hN hD hT

end Erdos1189
