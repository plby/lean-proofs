/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PotentialKernel
import ErdosProblems.Erdos1165.BinomialGaussian

/-!
# Exact off-diagonal endpoint probabilities

The diagonal encoding of a planar step from `FourierReturn.lean` identifies
the two diagonal coordinates with independent Boolean sign sums.  This file
counts the corresponding finite fibers at every pair of Boolean weights.
In particular, at the parity-compatible point

`(d + e, d - e)`

after `2n` steps, the endpoint probability is the product of the two
centered symmetric-binomial masses at offsets `d` and `e`.
-/

open scoped BigOperators

namespace Erdos1165
namespace EndpointDiagonal

open BinomialGaussian PotentialKernel

/-! ## Boolean words of prescribed weight -/

/-- Boolean words of length `N` with exactly `k` positive signs. -/
def WeightedWords (N k : ℕ) :=
  {f : Fin N → Bool // (truePositions f).card = k}

noncomputable def weightedWordsEquivPowerset (N k : ℕ) :
    WeightedWords N k ≃
      {s : Finset (Fin N) // s ∈ Finset.univ.powersetCard k} where
  toFun f := ⟨boolWordEquivFinset N f.1, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, f.property⟩⟩
  invFun s := ⟨(boolWordEquivFinset N).symm s.1, by
    have hs := (Finset.mem_powersetCard.mp s.property).2
    change (truePositions ((boolWordEquivFinset N).symm s.1)).card = k
    rw [show truePositions ((boolWordEquivFinset N).symm s.1) = s.1 from
      (boolWordEquivFinset N).apply_symm_apply s.1]
    exact hs⟩
  left_inv f := by
    apply Subtype.ext
    exact (boolWordEquivFinset N).symm_apply_apply f.1
  right_inv s := by
    apply Subtype.ext
    exact (boolWordEquivFinset N).apply_symm_apply s.1

noncomputable instance (N k : ℕ) : Fintype (WeightedWords N k) := by
  unfold WeightedWords
  infer_instance

lemma card_weightedWords (N k : ℕ) :
    Fintype.card (WeightedWords N k) = N.choose k := by
  rw [Fintype.card_congr (weightedWordsEquivPowerset N k)]
  simp

/-! ## The exact two-weight fiber -/

/-- The planar endpoint belonging to diagonal Boolean weights `k` and `l`
in a word of length `N`. -/
def pointOfWeights (N k l : ℕ) : Point :=
  ((k : ℤ) + l - N, (k : ℤ) - l)

@[simp] lemma diagonalMap_pointOfWeights (N k l : ℕ) :
    diagonalMap (pointOfWeights N k l) =
      (2 * (k : ℤ) - N, 2 * (l : ℤ) - N) := by
  ext <;> simp [diagonalMap, pointOfWeights] <;> ring

lemma diagonalMap_blockDisplacement (u : Fin N → Direction) :
    diagonalMap (blockDisplacement u) =
      (∑ i, boolSign ((blockBitsEquiv N u).1 i),
        ∑ i, boolSign ((blockBitsEquiv N u).2 i)) := by
  rw [blockDisplacement, map_sum]
  simp only [diagonalMap_directionVector, blockBitsEquiv]
  apply Prod.ext
  · exact Prod.fst_sum
  · exact Prod.snd_sum

lemma blockDisplacement_eq_pointOfWeights_iff
    (u : Fin N → Direction) (k l : ℕ) :
    blockDisplacement u = pointOfWeights N k l ↔
      (truePositions (blockBitsEquiv N u).1).card = k ∧
        (truePositions (blockBitsEquiv N u).2).card = l := by
  have hdiag := diagonalMap_blockDisplacement u
  constructor
  · intro hu
    rw [hu, diagonalMap_pointOfWeights] at hdiag
    have h₁ : (∑ i, boolSign ((blockBitsEquiv N u).1 i)) =
        2 * (k : ℤ) - N := by
      simpa using congrArg Prod.fst hdiag.symm
    have h₂ : (∑ i, boolSign ((blockBitsEquiv N u).2 i)) =
        2 * (l : ℤ) - N := by
      simpa using congrArg Prod.snd hdiag.symm
    rw [sum_boolSign_eq] at h₁ h₂
    constructor <;> exact_mod_cast (show _ = _ by omega)
  · rintro ⟨h₁, h₂⟩
    apply diagonalMap_injective
    rw [diagonalMap_pointOfWeights, diagonalMap_blockDisplacement]
    apply Prod.ext <;> simp only
    · rw [sum_boolSign_eq, h₁]
    · rw [sum_boolSign_eq, h₂]

/-- Direction words in a fixed endpoint fiber are independently prescribed
Boolean-weight words in the two diagonal coordinates. -/
noncomputable def endpointFiberEquiv (N k l : ℕ) :
    {u : Fin N → Direction // blockDisplacement u = pointOfWeights N k l} ≃
      WeightedWords N k × WeightedWords N l where
  toFun u := by
    have hu := (blockDisplacement_eq_pointOfWeights_iff u.1 k l).mp u.property
    exact ⟨⟨(blockBitsEquiv N u.1).1, hu.1⟩,
      ⟨(blockBitsEquiv N u.1).2, hu.2⟩⟩
  invFun p := by
    refine ⟨(blockBitsEquiv N).symm (p.1.1, p.2.1), ?_⟩
    apply (blockDisplacement_eq_pointOfWeights_iff _ k l).mpr
    simpa using And.intro p.1.2 p.2.2
  left_inv u := by
    apply Subtype.ext
    exact (blockBitsEquiv N).symm_apply_apply u
  right_inv p := by
    rcases p with ⟨a, b⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((blockBitsEquiv N).apply_symm_apply (a.1, b.1))
    · exact congrArg Prod.snd ((blockBitsEquiv N).apply_symm_apply (a.1, b.1))

theorem card_endpointBlocks_pointOfWeights (N k l : ℕ) :
    (endpointBlocks N (pointOfWeights N k l)).card =
      N.choose k * N.choose l := by
  let e : ↥(endpointBlocks N (pointOfWeights N k l)) ≃
      {u : Fin N → Direction // blockDisplacement u = pointOfWeights N k l} :=
    { toFun := fun u ↦ ⟨u.1, mem_endpointBlocks.mp u.2⟩
      invFun := fun u ↦ ⟨u.1, mem_endpointBlocks.mpr u.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (endpointBlocks N (pointOfWeights N k l)).card =
        Fintype.card ↥(endpointBlocks N (pointOfWeights N k l)) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        {u : Fin N → Direction // blockDisplacement u = pointOfWeights N k l} :=
      Fintype.card_congr e
    _ = Fintype.card (WeightedWords N k × WeightedWords N l) :=
      Fintype.card_congr (endpointFiberEquiv N k l)
    _ = N.choose k * N.choose l := by
      rw [Fintype.card_prod, card_weightedWords, card_weightedWords]

/-- Exact factorization of every endpoint whose two diagonal weights are
specified.  The formula remains valid for `k` or `l` outside the support,
because `Nat.choose` and the endpoint fiber then both vanish. -/
theorem endpointProbability_pointOfWeights (N k l : ℕ) :
    endpointProbability N (pointOfWeights N k l) =
      symBinomialMass N k * symBinomialMass N l := by
  rw [endpointProbability, card_endpointBlocks_pointOfWeights]
  unfold symBinomialMass
  push_cast
  rw [show (4 : ℝ) ^ N = (2 : ℝ) ^ N * (2 : ℝ) ^ N by
    rw [← mul_pow]
    norm_num]
  field_simp

/-! ## Centered even-time formula and obstructions -/

/-- The lattice point with nonnegative diagonal offsets `2d` and `2e`. -/
def positiveDiagonalPoint (d e : ℕ) : Point :=
  ((d : ℤ) + e, (d : ℤ) - e)

lemma pointOfWeights_centered (n d e : ℕ) :
    pointOfWeights (2 * n) (n + d) (n + e) = positiveDiagonalPoint d e := by
  ext <;> simp [pointOfWeights, positiveDiagonalPoint] <;> omega

/-- The exact off-diagonal formula in the form consumed by the Gaussian
estimates in `BinomialGaussian.lean`. -/
theorem endpointProbability_even_positiveDiagonal (n d e : ℕ) :
    endpointProbability (2 * n) (positiveDiagonalPoint d e) =
      evenSymmetricMass n d * evenSymmetricMass n e := by
  rw [← pointOfWeights_centered n d e,
    endpointProbability_pointOfWeights, evenSymmetricMass, evenSymmetricMass]

/-- The Boolean weight realizing the signed diagonal displacement `2a` in
`2n` sign steps. -/
def weightOfSignedOffset (n : ℕ) (a : ℤ) : ℕ :=
  if 0 ≤ a then n + a.natAbs else n - a.natAbs

lemma pointOfWeights_signedOffsets {n : ℕ} {a b : ℤ}
    (ha : a.natAbs ≤ n) (hb : b.natAbs ≤ n) :
    pointOfWeights (2 * n) (weightOfSignedOffset n a) (weightOfSignedOffset n b) =
      (a + b, a - b) := by
  by_cases ha0 : 0 ≤ a <;> by_cases hb0 : 0 ≤ b
  · have ha' : (a.natAbs : ℤ) = a := by
      rw [Int.natCast_natAbs, abs_of_nonneg ha0]
    have hb' : (b.natAbs : ℤ) = b := by
      rw [Int.natCast_natAbs, abs_of_nonneg hb0]
    simp only [weightOfSignedOffset, if_pos ha0, if_pos hb0]
    ext <;> simp [pointOfWeights, ha', hb'] <;> omega
  · have ha' : (a.natAbs : ℤ) = a := by
      rw [Int.natCast_natAbs, abs_of_nonneg ha0]
    have hb' : (b.natAbs : ℤ) = -b := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge hb0)]
    simp only [weightOfSignedOffset, if_pos ha0, if_neg hb0]
    ext <;> simp [pointOfWeights, Nat.cast_sub hb, ha', hb'] <;> omega
  · have ha' : (a.natAbs : ℤ) = -a := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge ha0)]
    have hb' : (b.natAbs : ℤ) = b := by
      rw [Int.natCast_natAbs, abs_of_nonneg hb0]
    simp only [weightOfSignedOffset, if_neg ha0, if_pos hb0]
    ext <;> simp [pointOfWeights, Nat.cast_sub ha, ha', hb'] <;> omega
  · have ha' : (a.natAbs : ℤ) = -a := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge ha0)]
    have hb' : (b.natAbs : ℤ) = -b := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge hb0)]
    simp only [weightOfSignedOffset, if_neg ha0, if_neg hb0]
    ext <;> simp [pointOfWeights, Nat.cast_sub ha, Nat.cast_sub hb, ha', hb'] <;> omega

lemma symBinomialMass_weightOfSignedOffset {n : ℕ} (a : ℤ)
    (ha : a.natAbs ≤ n) :
    symBinomialMass (2 * n) (weightOfSignedOffset n a) =
      evenSymmetricMass n a.natAbs := by
  by_cases ha0 : 0 ≤ a
  · simp [weightOfSignedOffset, ha0, evenSymmetricMass]
  · simp only [weightOfSignedOffset, if_neg ha0]
    exact evenSymmetricMass_sub_eq_add ha

/-- Sign-uniform form of the even-time endpoint formula.  The hypotheses are
exactly the support restrictions in the two diagonal coordinates. -/
theorem endpointProbability_even_signedDiagonal {n : ℕ} (a b : ℤ)
    (ha : a.natAbs ≤ n) (hb : b.natAbs ≤ n) :
    endpointProbability (2 * n) (a + b, a - b) =
      evenSymmetricMass n a.natAbs * evenSymmetricMass n b.natAbs := by
  rw [← pointOfWeights_signedOffsets ha hb, endpointProbability_pointOfWeights,
    symBinomialMass_weightOfSignedOffset a ha,
    symBinomialMass_weightOfSignedOffset b hb]

/-- Absolute half-displacement in the first diagonal coordinate. -/
def firstDiagonalOffset (x : Point) : ℕ := (x.1 + x.2).natAbs / 2

/-- Absolute half-displacement in the second diagonal coordinate. -/
def secondDiagonalOffset (x : Point) : ℕ := (x.1 - x.2).natAbs / 2

lemma natAbs_add_self_div_two (a : ℤ) : (a + a).natAbs / 2 = a.natAbs := by
  rw [show a + a = 2 * a by ring, Int.natAbs_mul]
  simp

lemma endpointProbability_even_of_diagonalCoordinates {n : ℕ} {x : Point}
    (a b : ℤ) (h₁ : x.1 + x.2 = a + a) (h₂ : x.1 - x.2 = b + b)
    (ha : a.natAbs ≤ n) (hb : b.natAbs ≤ n) :
    endpointProbability (2 * n) x =
      evenSymmetricMass n a.natAbs * evenSymmetricMass n b.natAbs := by
  have hx : x = (a + b, a - b) := by
    apply Prod.ext <;> simp only
    · omega
    · omega
  rw [hx]
  exact endpointProbability_even_signedDiagonal a b ha hb

/-- Exact endpoint formula for an arbitrary parity-compatible point.  At an
even time it suffices to assume parity of the first diagonal coordinate;
parity of the second then follows automatically. -/
theorem endpointProbability_even_of_even {n : ℕ} {x : Point}
    (hparity : Even (x.1 + x.2))
    (hfirst : firstDiagonalOffset x ≤ n)
    (hsecond : secondDiagonalOffset x ≤ n) :
    endpointProbability (2 * n) x =
      evenSymmetricMass n (firstDiagonalOffset x) *
        evenSymmetricMass n (secondDiagonalOffset x) := by
  obtain ⟨a, ha⟩ := hparity
  let b : ℤ := x.1 - a
  have hb : x.1 - x.2 = b + b := by
    dsimp [b]
    omega
  have hfirst_eq : firstDiagonalOffset x = a.natAbs := by
    rw [firstDiagonalOffset, ha, natAbs_add_self_div_two]
  have hsecond_eq : secondDiagonalOffset x = b.natAbs := by
    rw [secondDiagonalOffset, hb, natAbs_add_self_div_two]
  rw [hfirst_eq] at hfirst
  rw [hsecond_eq] at hsecond
  rw [hfirst_eq, hsecond_eq]
  exact endpointProbability_even_of_diagonalCoordinates a b ha hb hfirst hsecond

/-- At an even time the sum of the two Cartesian coordinates must be even. -/
theorem endpointBlocks_even_eq_empty_of_not_even {n : ℕ} {x : Point}
    (hx : ¬ Even (x.1 + x.2)) : endpointBlocks (2 * n) x = ∅ := by
  ext u
  constructor
  · intro hu
    have hdisp := mem_endpointBlocks.mp hu
    have hdiag := diagonalMap_blockDisplacement u
    have hsum : x.1 + x.2 =
        2 * ((truePositions (blockBitsEquiv (2 * n) u).1).card : ℤ) - 2 * n := by
      rw [hdisp] at hdiag
      have := congrArg Prod.fst hdiag
      rw [sum_boolSign_eq] at this
      simpa [diagonalMap] using this
    exfalso
    apply hx
    refine ⟨((truePositions (blockBitsEquiv (2 * n) u).1).card : ℤ) - n, ?_⟩
    omega
  · simp

theorem endpointProbability_even_eq_zero_of_not_even {n : ℕ} {x : Point}
    (hx : ¬ Even (x.1 + x.2)) : endpointProbability (2 * n) x = 0 := by
  rw [endpointProbability, endpointBlocks_even_eq_empty_of_not_even hx]
  simp

/-- If either diagonal coordinate is larger than the time horizon in
absolute value, the endpoint is outside the finite support. -/
theorem endpointBlocks_even_eq_empty_of_diagonal_lt {n : ℕ} {x : Point}
    (hx : 2 * (n : ℤ) < |x.1 + x.2| ∨ 2 * (n : ℤ) < |x.1 - x.2|) :
    endpointBlocks (2 * n) x = ∅ := by
  ext u
  constructor
  · intro hu
    have hdisp := mem_endpointBlocks.mp hu
    have hdiag := diagonalMap_blockDisplacement u
    rw [hdisp] at hdiag
    have h₁ : x.1 + x.2 =
        2 * ((truePositions (blockBitsEquiv (2 * n) u).1).card : ℤ) - 2 * n := by
      have := congrArg Prod.fst hdiag
      rw [sum_boolSign_eq] at this
      simpa [diagonalMap] using this
    have h₂ : x.1 - x.2 =
        2 * ((truePositions (blockBitsEquiv (2 * n) u).2).card : ℤ) - 2 * n := by
      have := congrArg Prod.snd hdiag
      rw [sum_boolSign_eq ((blockBitsEquiv (2 * n) u).2)] at this
      simpa [diagonalMap] using this
    have hw₁ : (truePositions (blockBitsEquiv (2 * n) u).1).card ≤ 2 * n :=
      by
        simpa [truePositions] using
          (Finset.univ.card_filter_le
            (fun i : Fin (2 * n) ↦ (blockBitsEquiv (2 * n) u).1 i = true))
    have hw₂ : (truePositions (blockBitsEquiv (2 * n) u).2).card ≤ 2 * n :=
      by
        simpa [truePositions] using
          (Finset.univ.card_filter_le
            (fun i : Fin (2 * n) ↦ (blockBitsEquiv (2 * n) u).2 i = true))
    have hw₁' :
        ((truePositions (blockBitsEquiv (2 * n) u).1).card : ℤ) ≤ 2 * (n : ℤ) := by
      exact_mod_cast hw₁
    have hw₂' :
        ((truePositions (blockBitsEquiv (2 * n) u).2).card : ℤ) ≤ 2 * (n : ℤ) := by
      exact_mod_cast hw₂
    have habs₁ :
        |2 * ((truePositions (blockBitsEquiv (2 * n) u).1).card : ℤ) - 2 * n| ≤
          2 * (n : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    have habs₂ :
        |2 * ((truePositions (blockBitsEquiv (2 * n) u).2).card : ℤ) - 2 * n| ≤
          2 * (n : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    exfalso
    rcases hx with hx | hx
    · rw [h₁] at hx
      omega
    · rw [h₂] at hx
      omega
  · simp

theorem endpointProbability_even_eq_zero_of_diagonal_lt {n : ℕ} {x : Point}
    (hx : 2 * (n : ℤ) < |x.1 + x.2| ∨ 2 * (n : ℤ) < |x.1 - x.2|) :
    endpointProbability (2 * n) x = 0 := by
  rw [endpointProbability, endpointBlocks_even_eq_empty_of_diagonal_lt hx]
  simp

/-- Offset-based form of the support obstruction. -/
theorem endpointProbability_even_eq_zero_of_offset_lt {n : ℕ} {x : Point}
    (hx : n < firstDiagonalOffset x ∨ n < secondDiagonalOffset x) :
    endpointProbability (2 * n) x = 0 := by
  apply endpointProbability_even_eq_zero_of_diagonal_lt
  rcases hx with hx | hx
  · left
    have hnat : 2 * n < (x.1 + x.2).natAbs := by
      unfold firstDiagonalOffset at hx
      omega
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  · right
    have hnat : 2 * n < (x.1 - x.2).natAbs := by
      unfold secondDiagonalOffset at hx
      omega
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat

/-- Complete exact classification at even times: parity and the two support
bounds are the only obstructions; on the support the two diagonal binomial
masses factor. -/
theorem endpointProbability_even_formula (n : ℕ) (x : Point) :
    endpointProbability (2 * n) x =
      if Even (x.1 + x.2) ∧ firstDiagonalOffset x ≤ n ∧ secondDiagonalOffset x ≤ n then
        evenSymmetricMass n (firstDiagonalOffset x) *
          evenSymmetricMass n (secondDiagonalOffset x)
      else 0 := by
  by_cases hparity : Even (x.1 + x.2)
  · by_cases hfirst : firstDiagonalOffset x ≤ n
    · by_cases hsecond : secondDiagonalOffset x ≤ n
      · rw [if_pos ⟨hparity, hfirst, hsecond⟩]
        exact endpointProbability_even_of_even hparity hfirst hsecond
      · rw [if_neg (fun h ↦ hsecond h.2.2)]
        exact endpointProbability_even_eq_zero_of_offset_lt (Or.inr (Nat.lt_of_not_ge hsecond))
    · rw [if_neg (fun h ↦ hfirst h.2.1)]
      exact endpointProbability_even_eq_zero_of_offset_lt (Or.inl (Nat.lt_of_not_ge hfirst))
  · rw [if_neg (fun h ↦ hparity h.1)]
    exact endpointProbability_even_eq_zero_of_not_even hparity

end EndpointDiagonal
end Erdos1165
