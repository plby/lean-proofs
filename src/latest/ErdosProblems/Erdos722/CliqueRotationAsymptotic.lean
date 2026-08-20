/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.RotationAsymptotic
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Random rotations of unsaturated cliques

The edge-rotation estimates are sufficient for the three rainbow focusing
properties in the short proof.  Property (iv) additionally needs whole
monochromatic cliques.  This file develops the two incidence estimates for
the family of two-cap unsaturated cliques: a global lower bound and a local
upper bound through every proper face.
-/

namespace Erdos722.CliqueRotationAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.IntegralGenerators
open Erdos722.Rotations
open Erdos722.GeneratorAsymptotic
open Erdos722.RotationAsymptotic

noncomputable section

/-- A uniform local lower bound through every surviving edge gives a global
lower bound for the unsaturated-clique family. -/
theorem card_Kstar_mul_goodLower_le_unsaturated_mul_choose
    {N n q r faceCap edgeCap threshold faceCliqueCap edgeCliqueCap L : ℕ}
    (D : TwoCapPrunedData N n q r faceCap edgeCap threshold
      faceCliqueCap edgeCliqueCap)
    (hgood : ∀ e ∈ D.Kstar, L ≤
      ((twoCapUnsaturatedCliques n q r faceCap edgeCap
        D.K D.selected).filter fun Q ↦ e ⊆ Q).card) :
    D.Kstar.card * L ≤
      (twoCapUnsaturatedCliques n q r faceCap edgeCap
        D.K D.selected).card * Nat.choose q r := by
  let U := twoCapUnsaturatedCliques n q r faceCap edgeCap D.K D.selected
  apply Erdos722.Reserve.card_mul_le_card_mul_of_relation
    D.Kstar U (fun e Q ↦ e ⊆ Q) L (Nat.choose q r)
  · intro e he
    simpa [U] using hgood e he
  · intro Q hQ
    have hQcard : Q.card = q :=
      (mem_cliquesIn.mp (mem_twoCapUnsaturatedCliques.mp hQ).1).1
    have hsub : (D.Kstar.filter fun e ↦ e ⊆ Q) ⊆
        Q.powersetCard r := by
      intro e he
      have hedata := Finset.mem_filter.mp he
      exact Finset.mem_powersetCard.mpr
        ⟨hedata.2, D.uniform e (D.Kstar_subset hedata.1)⟩
    exact (Finset.card_le_card hsub).trans (by
      rw [Finset.card_powersetCard, hQcard])

/-- A `q`-uniform family with at most `D` members through every
`(r-1)`-face has at most the stated number of members through a fixed
`j`-face.  This elementary lifting is what preserves the full sparse-clique
density at every `j < r`. -/
theorem card_filter_subset_le_choose_mul_faceDegree
    {n q r j D : ℕ} (hjq : r - 1 ≤ q) (hj : j < r)
    {U : Finset (Finset (Fin n))}
    (hU : ∀ Q ∈ U, Q.card = q)
    (hface : ∀ f : Finset (Fin n), f.card = r - 1 →
      (U.filter fun Q ↦ f ⊆ Q).card ≤ D)
    {I : Finset (Fin n)} (hI : I.card = j) :
    (U.filter fun Q ↦ I ⊆ Q).card ≤
      Nat.choose (n - j) (r - 1 - j) * D := by
  classical
  let faces := ((Finset.univ : Finset (Fin n)).powersetCard (r - 1)).filter
    fun f ↦ I ⊆ f
  let through : Finset (Fin n) → Finset (Finset (Fin n)) :=
    fun f ↦ U.filter fun Q ↦ f ⊆ Q
  have hcover : (U.filter fun Q ↦ I ⊆ Q) ⊆ faces.biUnion through := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    have hIQ : I ⊆ Q := hQdata.2
    have hdiffcard : (Q \ I).card = q - j := by
      rw [Finset.card_sdiff_of_subset hIQ, hU Q hQdata.1, hI]
    have hneed : r - 1 - j ≤ (Q \ I).card := by
      rw [hdiffcard]
      omega
    obtain ⟨t, htSub, htCard⟩ := Finset.exists_subset_card_eq hneed
    let f := I ∪ t
    have htDisjoint : Disjoint I t := by
      rw [Finset.disjoint_left]
      intro x hxI hxt
      exact (Finset.mem_sdiff.mp (htSub hxt)).2 hxI
    have hfcard : f.card = r - 1 := by
      dsimp [f]
      rw [Finset.card_union_of_disjoint htDisjoint, hI, htCard]
      omega
    have hfQ : f ⊆ Q := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hIQ hx
      · exact (Finset.mem_sdiff.mp (htSub hx)).1
    apply Finset.mem_biUnion.mpr
    refine ⟨f, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ f, hfcard⟩, Finset.subset_union_left⟩
    · exact Finset.mem_filter.mpr ⟨hQdata.1, hfQ⟩
  calc
    (U.filter fun Q ↦ I ⊆ Q).card ≤ (faces.biUnion through).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ f ∈ faces, (through f).card := Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ faces, D := by
      apply Finset.sum_le_sum
      intro f hf
      apply hface f
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hf).1).2
    _ = faces.card * D := by simp
    _ = Nat.choose (n - j) (r - 1 - j) * D := by
      have hfaces : faces =
          ((Finset.univ : Finset (Fin n)).powersetCard (r - 1)).filter
            (I ⊆ ·) := rfl
      rw [hfaces, Finset.card_filter_powersetCard_subset I Finset.univ
        (r - 1) (Finset.subset_univ I) (by omega), hI]
      simp

/-- Specialization of the preceding bound to the unsaturated family in a
typical pruned generator. -/
theorem card_unsaturated_filter_subset_le
    {N n q r d threshold faceCliqueCap edgeCliqueCap j : ℕ}
    (hr : 1 < r) (hrq : r < q)
    (D : TwoCapPrunedData N n q r
      (generatorFaceCap d n) (generatorEdgeCap d n)
      threshold faceCliqueCap edgeCliqueCap)
    (hface : ∀ f : Finset (Fin n), f.card = r - 1 →
      ((cliquesIn n q r D.K).filter fun Q ↦ f ⊆ Q).card ≤
        generatorFaceCliqueCap q r d n)
    {I : Finset (Fin n)} (hI : I.card = j) (hj : j < r) :
    ((twoCapUnsaturatedCliques n q r
      (generatorFaceCap d n) (generatorEdgeCap d n)
      D.K D.selected).filter fun Q ↦ I ⊆ Q).card ≤
      Nat.choose (n - j) (r - 1 - j) * generatorFaceCliqueCap q r d n := by
  apply card_filter_subset_le_choose_mul_faceDegree
    (q := q) (r := r) (j := j) (by omega) hj
  · intro Q hQ
    exact (mem_cliquesIn.mp (mem_twoCapUnsaturatedCliques.mp hQ).1).1
  · intro f hf
    have hsub :
        ((twoCapUnsaturatedCliques n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          D.K D.selected).filter fun Q ↦ f ⊆ Q) ⊆
        ((cliquesIn n q r D.K).filter fun Q ↦ f ⊆ Q) := by
      intro Q hQ
      have hQdata := Finset.mem_filter.mp hQ
      exact Finset.mem_filter.mpr
        ⟨(mem_twoCapUnsaturatedCliques.mp hQdata.1).1, hQdata.2⟩
    exact (Finset.card_le_card hsub).trans (hface f hf)
  · exact hI

/-- A direct local-degree bound gives the corresponding ordered
intersection-pair estimate. -/
theorem card_orderedIntersectionPairs_le_of_intersectionDegree
    {n q j D : ℕ} {U : Finset (Finset (Fin n))}
    (hU : ∀ Q ∈ U, Q.card = q)
    (hdegree : ∀ I : Finset (Fin n), I.card = j →
      (U.filter fun Q ↦ I ⊆ Q).card ≤ D) :
    (orderedIntersectionPairs U j).card ≤
      U.card * (Nat.choose q j * D) := by
  classical
  let P := orderedIntersectionPairs U j
  have hmaps : (P : Set (Finset (Fin n) × Finset (Fin n))).MapsTo
      Prod.fst U := by
    intro p hp
    exact (mem_orderedIntersectionPairs.mp hp).1
  rw [show (orderedIntersectionPairs U j).card = P.card by rfl,
    Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    (∑ Q ∈ U, (P.filter fun p ↦ p.1 = Q).card) ≤
        ∑ _Q ∈ U, Nat.choose q j * D := by
      apply Finset.sum_le_sum
      intro Q hQ
      let R := Q.powersetCard j
      let fibre := P.filter fun p ↦ p.1 = Q
      let pairInter : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) :=
        fun p ↦ p.1 ∩ p.2
      have hfibreMaps : (fibre : Set (Finset (Fin n) × Finset (Fin n))).MapsTo
          pairInter R := by
        intro p hp
        have hpdata := Finset.mem_filter.mp hp
        have hpair := mem_orderedIntersectionPairs.mp hpdata.1
        apply Finset.mem_powersetCard.mpr
        refine ⟨?_, hpair.2.2⟩
        simpa [pairInter, hpdata.2] using
          (Finset.inter_subset_left : p.1 ∩ p.2 ⊆ p.1)
      rw [show (P.filter fun p ↦ p.1 = Q).card = fibre.card by rfl,
        Finset.card_eq_sum_card_fiberwise hfibreMaps]
      calc
        (∑ I ∈ R, (fibre.filter fun p ↦ pairInter p = I).card) ≤
            ∑ _I ∈ R, D := by
          apply Finset.sum_le_sum
          intro I hI
          have hsub : (fibre.filter fun p ↦ pairInter p = I).image Prod.snd ⊆
              U.filter fun Q' ↦ I ⊆ Q' := by
            intro Q' hQ'
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hQ'
            have hpdata := Finset.mem_filter.mp hp
            have hpFibre := Finset.mem_filter.mp hpdata.1
            have hpair := mem_orderedIntersectionPairs.mp hpFibre.1
            apply Finset.mem_filter.mpr
            refine ⟨hpair.2.1, ?_⟩
            rw [← hpdata.2]
            exact Finset.inter_subset_right
          have himage : (fibre.filter fun p ↦ pairInter p = I).card =
              ((fibre.filter fun p ↦ pairInter p = I).image Prod.snd).card := by
            rw [Finset.card_image_iff.mpr]
            intro a ha b hb hab
            have haFirst := (Finset.mem_filter.mp
              (Finset.mem_filter.mp ha).1).2
            have hbFirst := (Finset.mem_filter.mp
              (Finset.mem_filter.mp hb).1).2
            exact Prod.ext (haFirst.trans hbFirst.symm) hab
          rw [himage]
          exact (Finset.card_le_card hsub).trans
            (hdegree I (Finset.mem_powersetCard.mp hI).2)
        _ = R.card * D := by simp
        _ = Nat.choose q j * D := by
          simp [R, hU Q hQ]
    _ = U.card * (Nat.choose q j * D) := by simp

/-- A coarse constant for all proper-intersection correlations of the
unsaturated `q`-clique family. -/
def cliqueRotationPairConstant (q r : ℕ) : ℕ :=
  (4 * r * Nat.choose q r) * 4 ^ (q - r + 1) *
    (2 ^ (r - 1) * Nat.factorial (r - 1)) * 16 *
    (2 * 16 ^ (q - r) * (2 ^ q) ^ (q - r)) *
    (2 ^ q * Nat.factorial q)

lemma cliqueRotationPairConstant_pos
    {q r : ℕ} (hr : 0 < r) (hrq : r < q) :
    0 < cliqueRotationPairConstant q r := by
  have hchoose : 0 < Nat.choose q r := Nat.choose_pos hrq.le
  simp only [cliqueRotationPairConstant]
  positivity

/-- The global lower-density factors and the local upper-density factors
have identical powers of `n`; the fixed losses are absorbed in
`cliqueRotationPairConstant`. -/
theorem eventually_cliqueRotation_pair_scale
    (q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ j < r,
        (4 * r * Nat.choose q r) *
            (Nat.choose (n - j) (r - 1 - j) *
              generatorFaceCliqueCap q r d n) * Nat.choose n q ≤
          cliqueRotationPairConstant q r *
            (Nat.choose n (r - 1) * generatorDegreeLower d n *
              generatorCliqueLower q r d n) *
            Nat.choose (n - q) (q - j) := by
  let K := Nat.choose q r
  let C₁ := 2 ^ (r - 1) * Nat.factorial (r - 1)
  let C₂ := 2 * 16 ^ (q - r) * (2 ^ q) ^ (q - r)
  let C₃ := 2 ^ q * Nat.factorial q
  let faceExp : ℝ := ((d * (q - r + 1) - K : ℕ) : ℝ) / d
  let degreeExp : ℝ := ((d - 1 : ℕ) : ℝ) / d
  let cliqueExp : ℝ :=
    ((d * (q - r) - (K - 1) : ℕ) : ℝ) / d
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.choose_pos hrq.le
  have hd : 0 < d := hKpos.trans hqd
  have hdOne : 1 < d := by omega
  have hfaceSub : K ≤ d * (q - r + 1) := by
    have hKd : K ≤ d := hqd.le
    exact hKd.trans (Nat.le_mul_of_pos_right d (by omega))
  have hcliqueSub : K - 1 ≤ d * (q - r) := by
    have hKd : K - 1 ≤ d := by omega
    exact hKd.trans (Nat.le_mul_of_pos_right d (by omega))
  have hdegree := eventually_rpow_div_sixteen_le_generatorDegreeLower hdOne
  have hclique := eventually_generatorCliqueLower_lower q r d
    (by omega) hrq hqd
  filter_upwards [hdegree, hclique,
      eventually_ge_atTop (max (2 * (r - 1)) (2 * (q + q)))] with
      n hdegree hclique hnlarge
  intro j hj
  have hnRnat : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnRnat
  have hjle : j ≤ q := by omega
  have hbin₁Nat := Erdos722.BinomialBounds.pow_le_factorial_mul_choose_sub
    n 0 (r - 1) (by omega : 2 * (0 + (r - 1)) ≤ n)
  have hbin₁ : (n : ℝ) ^ (r - 1) / C₁ ≤ Nat.choose n (r - 1) := by
    have hcast : (n : ℝ) ^ (r - 1) ≤
        (C₁ : ℝ) * Nat.choose n (r - 1) := by
      exact_mod_cast (by simpa [C₁] using hbin₁Nat)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < C₁)).2 (by
      simpa [mul_comm] using hcast)
  have hbin₃Nat := Erdos722.BinomialBounds.pow_le_factorial_mul_choose_sub
    n q (q - j) (by omega : 2 * (q + (q - j)) ≤ n)
  have hC₃small :
      2 ^ (q - j) * Nat.factorial (q - j) ≤ C₃ := by
    dsimp [C₃]
    exact Nat.mul_le_mul
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le q j))
      (Nat.factorial_le (Nat.sub_le q j))
  have hbin₃ : (n : ℝ) ^ (q - j) / C₃ ≤
      Nat.choose (n - q) (q - j) := by
    have hraw : (n : ℝ) ^ (q - j) ≤
        ((2 ^ (q - j) * Nat.factorial (q - j) : ℕ) : ℝ) *
          Nat.choose (n - q) (q - j) := by
      exact_mod_cast hbin₃Nat
    have hcastC :
        ((2 ^ (q - j) * Nat.factorial (q - j) : ℕ) : ℝ) ≤ C₃ := by
      exact_mod_cast hC₃small
    have hscaled : (n : ℝ) ^ (q - j) ≤
        (C₃ : ℝ) * Nat.choose (n - q) (q - j) :=
      hraw.trans (by gcongr)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < C₃)).2 (by
      simpa [mul_comm] using hscaled)
  have hface := generatorFaceCliqueCap_cast_le hnRnat hdOne
    (by omega : 0 < r) hrq hqd
  have hchooseSmall : (Nat.choose (n - j) (r - 1 - j) : ℝ) ≤
      (n : ℝ) ^ (r - 1 - j) := by
    exact (Nat.cast_le.mpr (Nat.choose_le_pow (n - j)
      (r - 1 - j))).trans (by
        exact_mod_cast Nat.pow_le_pow_left (Nat.sub_le n j) _)
  have hchooseQ : (Nat.choose n q : ℝ) ≤ (n : ℝ) ^ q := by
    exact_mod_cast Nat.choose_le_pow n q
  have hupper :
      (((4 * r * K) *
          (Nat.choose (n - j) (r - 1 - j) *
            generatorFaceCliqueCap q r d n) * Nat.choose n q : ℕ) : ℝ) ≤
        ((4 : ℝ) * r * K * 4 ^ (q - r + 1)) *
          ((n : ℝ) ^ (r - 1 - j) *
            (n : ℝ) ^ faceExp * (n : ℝ) ^ q) := by
    push_cast
    calc
      (4 : ℝ) * r * K *
          (Nat.choose (n - j) (r - 1 - j) *
            generatorFaceCliqueCap q r d n) * Nat.choose n q ≤
        (4 : ℝ) * r * K *
          ((n : ℝ) ^ (r - 1 - j) *
            ((4 : ℝ) ^ (q - r + 1) * (n : ℝ) ^ faceExp)) *
              (n : ℝ) ^ q := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left
              (mul_le_mul hchooseSmall (by simpa [faceExp, K] using hface)
                (by positivity) (by positivity)) (by positivity))
            hchooseQ (by positivity) (by positivity)
      _ = ((4 : ℝ) * r * K * 4 ^ (q - r + 1)) *
          ((n : ℝ) ^ (r - 1 - j) *
            (n : ℝ) ^ faceExp * (n : ℝ) ^ q) := by
        ring
  have hlower :
      ((n : ℝ) ^ (r - 1) / C₁) *
          ((n : ℝ) ^ degreeExp / 16) *
          ((n : ℝ) ^ cliqueExp / C₂) *
          ((n : ℝ) ^ (q - j) / C₃) ≤
        (Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n *
          generatorCliqueLower q r d n * Nat.choose (n - q) (q - j) := by
    exact mul_le_mul
      (mul_le_mul
        (mul_le_mul hbin₁ (by simpa [degreeExp] using hdegree)
          (by positivity) (by positivity))
        (by simpa [cliqueExp, C₂, K] using hclique)
        (by positivity) (by positivity))
      hbin₃ (by positivity) (by positivity)
  have hexponents :
      ((n : ℝ) ^ (r - 1 - j) * (n : ℝ) ^ faceExp *
          (n : ℝ) ^ q) =
        (n : ℝ) ^ (r - 1) * (n : ℝ) ^ degreeExp *
          (n : ℝ) ^ cliqueExp * (n : ℝ) ^ (q - j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_add hnR, ← Real.rpow_add hnR,
      ← Real.rpow_add hnR, ← Real.rpow_add hnR,
      ← Real.rpow_add hnR]
    congr 1
    dsimp [faceExp, degreeExp, cliqueExp, K]
    have hcastR : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - (1 : ℝ) := by
      rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ r)]
      norm_num
    have hcastRj : (((r - 1 - j : ℕ) : ℝ)) =
        (r : ℝ) - (1 : ℝ) - (j : ℝ) := by
      rw [Nat.cast_sub (by omega : j ≤ r - 1),
        Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num
    have hcastFace :
        (((d * (q - r + 1) - Nat.choose q r : ℕ) : ℝ)) =
          ((d * (q - r + 1) : ℕ) : ℝ) - Nat.choose q r := by
      exact Nat.cast_sub (by simpa [K] using hfaceSub)
    have hcastDegree : (((d - 1 : ℕ) : ℝ)) =
        (d : ℝ) - (1 : ℝ) := by
      rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ d)]
      norm_num
    have hcastK : (((Nat.choose q r - 1 : ℕ) : ℝ)) =
        (Nat.choose q r : ℝ) - (1 : ℝ) := by
      rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ Nat.choose q r)]
      norm_num
    have hcastClique :
        (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ)) =
          ((d * (q - r) : ℕ) : ℝ) -
            ((Nat.choose q r - 1 : ℕ) : ℝ) := by
      exact Nat.cast_sub (by simpa [K] using hcliqueSub)
    have hcastQj : (((q - j : ℕ) : ℝ)) = (q : ℝ) - j := by
      exact Nat.cast_sub hjle
    rw [hcastRj, hcastR, hcastFace, hcastDegree, hcastClique, hcastK,
      hcastQj]
    push_cast
    field_simp
    ring
  have hconstant :
      ((4 : ℝ) * r * K * 4 ^ (q - r + 1)) *
          ((n : ℝ) ^ (r - 1 - j) *
            (n : ℝ) ^ faceExp * (n : ℝ) ^ q) ≤
        (cliqueRotationPairConstant q r : ℝ) *
          ((Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n *
            generatorCliqueLower q r d n) *
          Nat.choose (n - q) (q - j) := by
    rw [hexponents]
    have hdenpos : (0 : ℝ) < (C₁ : ℝ) * 16 * C₂ * C₃ := by
      positivity
    have hlower' :
        ((n : ℝ) ^ (r - 1) * (n : ℝ) ^ degreeExp *
          (n : ℝ) ^ cliqueExp * (n : ℝ) ^ (q - j)) /
            ((C₁ : ℝ) * 16 * C₂ * C₃) ≤
          (Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n *
            generatorCliqueLower q r d n * Nat.choose (n - q) (q - j) := by
      convert hlower using 1 <;> field_simp <;> ring
    calc
      ((4 : ℝ) * r * K * 4 ^ (q - r + 1)) *
          ((n : ℝ) ^ (r - 1) * (n : ℝ) ^ degreeExp *
            (n : ℝ) ^ cliqueExp * (n : ℝ) ^ (q - j)) =
        (cliqueRotationPairConstant q r : ℝ) *
          (((n : ℝ) ^ (r - 1) * (n : ℝ) ^ degreeExp *
            (n : ℝ) ^ cliqueExp * (n : ℝ) ^ (q - j)) /
              ((C₁ : ℝ) * 16 * C₂ * C₃)) := by
        dsimp [cliqueRotationPairConstant, C₁, C₂, C₃, K]
        push_cast
        field_simp
      _ ≤ _ := by
        have hmul := mul_le_mul_of_nonneg_left hlower'
          (show (0 : ℝ) ≤ cliqueRotationPairConstant q r by positivity)
        simpa [mul_assoc] using hmul
  exact_mod_cast hupper.trans hconstant

/-- Incidence upper bounds, a global mass lower bound, and the matching
scalar inequality imply the normalized pair-correlation estimate used by
the rotation second moment. -/
theorem orderedIntersectionPairs_ratio_of_mass_and_scale
    {n q j A C D R : ℕ} {U : Finset (Finset (Fin n))}
    (hC : 0 < C)
    (hpair : (orderedIntersectionPairs U j).card ≤
      U.card * (Nat.choose q j * D))
    (hmass : A ≤ C * U.card)
    (hscale : C * D * Nat.choose n q ≤
      R * A * Nat.choose (n - q) (q - j))
    (hj : j ≤ q) :
    (orderedIntersectionPairs U j).card * Nat.choose n q ^ 2 ≤
      R * U.card ^ 2 *
        (orderedIntersectionPairs (uniformEdges n q) j).card := by
  apply Nat.le_of_mul_le_mul_left _ hC
  calc
    C * ((orderedIntersectionPairs U j).card * Nat.choose n q ^ 2) ≤
        C * ((U.card * (Nat.choose q j * D)) * Nat.choose n q ^ 2) := by
      gcongr
    _ = (U.card * Nat.choose q j * Nat.choose n q) *
          (C * D * Nat.choose n q) := by ring
    _ ≤ (U.card * Nat.choose q j * Nat.choose n q) *
          (R * A * Nat.choose (n - q) (q - j)) := by gcongr
    _ ≤ (U.card * Nat.choose q j * Nat.choose n q) *
          (R * (C * U.card) * Nat.choose (n - q) (q - j)) := by gcongr
    _ = C * (R * U.card ^ 2 *
          (Nat.choose n q *
            (Nat.choose q j * Nat.choose (n - q) (q - j)))) := by ring
    _ = C * (R * U.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n q) j).card) := by
      rw [card_orderedIntersectionPairs_uniform (n := n) hj]

/-- The two-cap unsaturated cliques in every sufficiently large pruned
generator have uniformly bounded proper-intersection correlations. -/
theorem eventually_prunedGenerator_unsaturated_pair_ratio
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∀ j < r,
        let U := twoCapUnsaturatedCliques n q r
          (generatorFaceCap d n) (generatorEdgeCap d n) D.K D.selected
        (orderedIntersectionPairs U j).card * Nat.choose n q ^ 2 ≤
          cliqueRotationPairConstant q r * U.card ^ 2 *
            (orderedIntersectionPairs (uniformEdges n q) j).card := by
  have hscale := eventually_cliqueRotation_pair_scale q r d hr hrq hqd
  have hthreshold := eventually_two_mul_generatorPruneThreshold_le_cliqueLower
    q r d (by omega) hrq hqd
  filter_upwards [hscale, hthreshold,
      eventually_ge_atTop (2 * (Nat.choose q r * (r - 1)))] with
      n hscale hthreshold hnlarge
  intro hn ω D htyp hDK hmass j hj
  let U := twoCapUnsaturatedCliques n q r
    (generatorFaceCap d n) (generatorEdgeCap d n) D.K D.selected
  let L := generatorCliqueLower q r d n
  let T := generatorPruneThreshold q r d n
  let A := Nat.choose n (r - 1) * generatorDegreeLower d n * L
  let C := 4 * r * Nat.choose q r
  let Dj := Nat.choose (n - j) (r - 1 - j) *
    generatorFaceCliqueCap q r d n
  have hface : ∀ f : Finset (Fin n), f.card = r - 1 →
      ((cliquesIn n q r D.K).filter fun Q ↦ f ⊆ Q).card ≤
        generatorFaceCliqueCap q r d n := by
    intro f hf
    have h := card_cliques_through_face_typicalUpper_le hr hrq
      (reserveProbabilityIcc n d hn) ω htyp hf
    simpa [hDK, generatorFaceCliqueCap_eq q r d hn] using h
  have hlocal : ∀ e ∈ D.Kstar, L - T ≤
      (U.filter fun Q ↦ e ⊆ Q).card := by
    intro e he
    have heSample : e ∈ sampledEdges n r ω := by
      simpa [← hDK] using D.Kstar_subset he
    have htotal : L ≤
        ((cliquesIn n q r D.K).filter fun Q ↦ e ⊆ Q).card := by
      simpa [L, hDK] using generatorCliqueLower_le_cliques_through_edge
        hn hr hrq hqd hnlarge ω htyp heSample
    exact (Nat.sub_le_sub_right htotal T).trans (by
      simpa [U, T] using D.good_lower e he)
  have hUg : D.Kstar.card * (L - T) ≤
      U.card * Nat.choose q r := by
    simpa [U] using
      card_Kstar_mul_goodLower_le_unsaturated_mul_choose D hlocal
  have hchoose : Nat.choose r (r - 1) = r := by
    rw [← Nat.choose_symm (by omega : r - 1 ≤ r)]
    simp [show r - (r - 1) = 1 by omega]
  have hmass' : A ≤ C * U.card := by
    have hhalf : L ≤ 2 * (L - T) := by
      dsimp [L, T]
      omega
    rw [hchoose] at hmass
    have hmassNat : Nat.choose n (r - 1) * generatorDegreeLower d n ≤
        2 * D.Kstar.card * r := by
      simpa [uniformEdges] using hmass
    calc
      A ≤ (2 * D.Kstar.card * r) * L := by
        dsimp [A]
        exact Nat.mul_le_mul_right L hmassNat
      _ ≤ (2 * D.Kstar.card * r) * (2 * (L - T)) := by gcongr
      _ = 4 * r * (D.Kstar.card * (L - T)) := by ring
      _ ≤ 4 * r * (U.card * Nat.choose q r) := by gcongr
      _ = C * U.card := by
        dsimp [C]
        ring
  have hUuniform : ∀ Q ∈ U, Q.card = q := by
    intro Q hQ
    exact (mem_cliquesIn.mp
      (mem_twoCapUnsaturatedCliques.mp (by simpa [U] using hQ)).1).1
  have hdegree : ∀ I : Finset (Fin n), I.card = j →
      (U.filter fun Q ↦ I ⊆ Q).card ≤ Dj := by
    intro I hI
    simpa [U, Dj] using card_unsaturated_filter_subset_le
      hr hrq D hface hI hj
  have hpair : (orderedIntersectionPairs U j).card ≤
      U.card * (Nat.choose q j * Dj) :=
    card_orderedIntersectionPairs_le_of_intersectionDegree hUuniform hdegree
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by omega) (by omega)) (Nat.choose_pos hrq.le)
  have hscalar : C * Dj * Nat.choose n q ≤
      cliqueRotationPairConstant q r * A * Nat.choose (n - q) (q - j) := by
    simpa [C, Dj, A] using hscale j hj
  simpa [U] using orderedIntersectionPairs_ratio_of_mass_and_scale
    hC hpair hmass' hscalar (by omega : j ≤ q)

/-- The global unsaturated-clique mass beats the one-power exceptional
embedding loss when the total number of clique constraints times
`choose q r` is smaller than the sampling denominator. -/
theorem eventually_rooted_unsaturated_expected_lower
    {v m q r d : ℕ} (root : Finset (Fin v))
    (hroot : root.card < v) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) (hmd : m * Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (U : Finset (Finset (Fin n))),
      Nat.choose n (r - 1) * generatorDegreeLower d n *
          generatorCliqueLower q r d n ≤
        (4 * r * Nat.choose q r) * U.card →
      ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
        ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) *
            Nat.choose n q ^ m ≤
          (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
            U.card ^ m := by
  let s := v - root.card
  let K := Nat.choose q r
  let degreeExp : ℝ := ((d - 1 : ℕ) : ℝ) / d
  let cliqueExp : ℝ :=
    ((d * (q - r) - (K - 1) : ℕ) : ℝ) / d
  let densityExp : ℝ := ((d * q - K : ℕ) : ℝ) / d
  let leftExp : ℝ := (s - 1 : ℕ) + q * m
  let rightExp : ℝ := s + densityExp * m
  let Cchoose : ℕ := 2 ^ (r - 1) * Nat.factorial (r - 1)
  let Cclique : ℕ :=
    2 * 16 ^ (q - r) * (2 ^ q) ^ (q - r)
  let Cmass : ℕ := 4 * r * K
  let Cfamily : ℕ := Cmass * Cchoose * 16 * Cclique
  let Ctotal : ℝ :=
    (s ^ 2 : ℕ) * (2 ^ s : ℕ) * (Cfamily : ℝ) ^ m
  have hs : 0 < s := by dsimp [s]; omega
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.choose_pos hrq.le
  have hd : 0 < d := hKpos.trans hqd
  have hdOne : 1 < d := by omega
  have hcliqueSub : K - 1 ≤ d * (q - r) := by
    have hKd : K - 1 ≤ d := by omega
    exact hKd.trans (Nat.le_mul_of_pos_right d (by omega))
  have hdensitySub : K ≤ d * q := by
    exact hqd.le.trans (Nat.le_mul_of_pos_right d (by omega))
  have hgap : leftExp < rightExp := by
    have hsone : 1 ≤ s := by omega
    have hmdR : (m * K : ℕ) < d := hmd
    change (((s - 1 : ℕ) : ℝ) + (q : ℝ) * m) <
      (s : ℝ) + (((d * q - K : ℕ) : ℝ) / d) * m
    rw [Nat.cast_sub hsone, Nat.cast_sub hdensitySub]
    push_cast
    have hmdReal : (m : ℝ) * K < d := by
      exact_mod_cast hmdR
    field_simp
    nlinarith [hmdReal]
  have hdom := eventually_const_mul_rpow_le_rpow hgap
    (show 0 ≤ Ctotal by positivity)
  have hdegree := eventually_rpow_div_sixteen_le_generatorDegreeLower hdOne
  have hclique := eventually_generatorCliqueLower_lower q r d
    (by omega) hrq hqd
  filter_upwards [hdom, hdegree, hclique,
      eventually_ge_atTop (max (2 * v) (2 * (r - 1)))] with
      n hdom hdegree hclique hnlarge
  intro U hmass request
  have hnTwoV : 2 * v ≤ n := (le_max_left _ _).trans hnlarge
  have hnChoose : 2 * (r - 1) ≤ n := (le_max_right _ _).trans hnlarge
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hbaseline :=
    Erdos722.LocalDecoderAsymptotic.descFactorial_sub_cast_lower
      (n := n) (r := root.card) (s := s) (by
        have hrs : root.card + s = v := by dsimp [s]; omega
        simpa [hrs] using hnTwoV)
  have hcandidate : (n : ℝ) ^ s / (2 : ℝ) ^ s ≤
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card :=
    hbaseline.trans (by
      exact_mod_cast
        (Erdos722.RootedEmbedding.descFactorial_le_card_rootedEmbeddings
          root request))
  have hchooseNat :=
    Erdos722.BinomialBounds.pow_le_factorial_mul_choose_sub
      n 0 (r - 1) (by omega : 2 * (0 + (r - 1)) ≤ n)
  have hchoose : (n : ℝ) ^ (r - 1) / Cchoose ≤
      Nat.choose n (r - 1) := by
    have hreal : (n : ℝ) ^ (r - 1) ≤
        (Cchoose : ℝ) * Nat.choose n (r - 1) := by
      exact_mod_cast (by simpa [Cchoose] using hchooseNat)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < Cchoose)).2 (by
      simpa [mul_comm] using hreal)
  have hfamilyPower :
      (n : ℝ) ^ densityExp =
        (n : ℝ) ^ (r - 1) * (n : ℝ) ^ degreeExp *
          (n : ℝ) ^ cliqueExp := by
    have hexp : densityExp =
        ((r - 1 : ℕ) : ℝ) + degreeExp + cliqueExp := by
      dsimp [densityExp, degreeExp, cliqueExp, K]
      have hcastR : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ r)]
        norm_num
      have hcastDegree : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ d)]
        norm_num
      have hcastK : (((K - 1 : ℕ) : ℝ)) = (K : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ K)]
        norm_num
      have hcastClique : (((d * (q - r) - (K - 1) : ℕ) : ℝ)) =
          ((d * (q - r) : ℕ) : ℝ) - ((K - 1 : ℕ) : ℝ) :=
        Nat.cast_sub hcliqueSub
      have hcastDensity : (((d * q - K : ℕ) : ℝ)) =
          ((d * q : ℕ) : ℝ) - (K : ℝ) :=
        Nat.cast_sub hdensitySub
      have hcastQr : (((q - r : ℕ) : ℝ)) = (q : ℝ) - r :=
        Nat.cast_sub hrq.le
      rw [hcastR, hcastDegree, hcastClique, hcastK, hcastDensity]
      push_cast
      rw [hcastQr]
      field_simp
      ring
    rw [hexp, Real.rpow_add hnR, Real.rpow_add hnR,
      Real.rpow_natCast]
  have hfamily : (n : ℝ) ^ densityExp / Cfamily ≤ U.card := by
    have hprod :
        ((n : ℝ) ^ (r - 1) / Cchoose) *
            ((n : ℝ) ^ degreeExp / 16) *
            ((n : ℝ) ^ cliqueExp / Cclique) ≤
          (Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n *
            generatorCliqueLower q r d n := by
      exact mul_le_mul
        (mul_le_mul hchoose (by simpa [degreeExp] using hdegree)
          (by positivity) (by positivity))
        (by simpa [cliqueExp, Cclique, K] using hclique)
        (by positivity) (by positivity)
    have hmassR :
        (Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n *
            generatorCliqueLower q r d n ≤
          (Cmass : ℝ) * U.card := by
      exact_mod_cast (by simpa [Cmass, K] using hmass)
    calc
      (n : ℝ) ^ densityExp / Cfamily =
          (((n : ℝ) ^ (r - 1) / Cchoose) *
            ((n : ℝ) ^ degreeExp / 16) *
            ((n : ℝ) ^ cliqueExp / Cclique)) / Cmass := by
        rw [hfamilyPower]
        dsimp [Cfamily]
        push_cast
        field_simp
      _ ≤ ((Nat.choose n (r - 1) : ℝ) *
          generatorDegreeLower d n * generatorCliqueLower q r d n) /
            Cmass := by gcongr
      _ ≤ U.card := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < Cmass)).2
        simpa [mul_comm] using hmassR
  have hleft :
      ((((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) *
          Nat.choose n q ^ m : ℕ) : ℝ) ≤
        (s ^ 2 : ℕ) * (n : ℝ) ^ leftExp := by
    push_cast
    have hvsub : v - (root.card + 1) = s - 1 := by dsimp [s]; omega
    rw [hvsub]
    change (s : ℝ) ^ 2 * (n : ℝ) ^ (s - 1) *
        (Nat.choose n q : ℝ) ^ m ≤
      (s : ℝ) ^ 2 * (n : ℝ) ^ leftExp
    calc
      (s : ℝ) ^ 2 * (n : ℝ) ^ (s - 1) *
          (Nat.choose n q : ℝ) ^ m ≤
        (s : ℝ) ^ 2 * (n : ℝ) ^ (s - 1) *
          ((n : ℝ) ^ q) ^ m := by
        gcongr
        exact_mod_cast Nat.choose_le_pow n q
      _ = (s : ℝ) ^ 2 * (n : ℝ) ^ leftExp := by
        have hexp : leftExp = ((((s - 1) + q * m : ℕ) : ℕ) : ℝ) := by
          push_cast
          simp [leftExp]
        rw [hexp, Real.rpow_natCast, pow_add, pow_mul]
        ring
  have hright :
      (n : ℝ) ^ rightExp /
          ((2 : ℝ) ^ s * (Cfamily : ℝ) ^ m) ≤
        ((Erdos722.RootedEmbedding.rootedEmbeddings root request).card : ℝ) *
          (U.card : ℝ) ^ m := by
    calc
      (n : ℝ) ^ rightExp /
          ((2 : ℝ) ^ s * (Cfamily : ℝ) ^ m) =
        ((n : ℝ) ^ s / (2 : ℝ) ^ s) *
          (((n : ℝ) ^ densityExp / Cfamily) ^ m) := by
        rw [show rightExp = (s : ℕ) + densityExp * m by rfl,
          Real.rpow_add hnR, Real.rpow_natCast,
          Real.rpow_mul hnR.le, Real.rpow_natCast, div_pow]
        ring
      _ ≤ ((Erdos722.RootedEmbedding.rootedEmbeddings root request).card : ℝ) *
          (U.card : ℝ) ^ m := by gcongr
  have hmiddle :
      (s ^ 2 : ℕ) * (n : ℝ) ^ leftExp ≤
        (n : ℝ) ^ rightExp /
          ((2 : ℝ) ^ s * (Cfamily : ℝ) ^ m) := by
    have hden : (0 : ℝ) < (2 : ℝ) ^ s * (Cfamily : ℝ) ^ m := by
      positivity
    apply (le_div_iff₀ hden).2
    have hdom' :
        ((s ^ 2 : ℕ) * (2 ^ s : ℕ) * (Cfamily : ℝ) ^ m) *
            (n : ℝ) ^ leftExp ≤ (n : ℝ) ^ rightExp := by
      simpa [Ctotal] using hdom
    calc
      ((s ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ leftExp *
          ((2 : ℝ) ^ s * (Cfamily : ℝ) ^ m) =
        ((s ^ 2 : ℕ) * (2 ^ s : ℕ) * (Cfamily : ℝ) ^ m) *
          (n : ℝ) ^ leftExp := by
        push_cast
        ring
      _ ≤ _ := hdom'
  exact_mod_cast hleft.trans (hmiddle.trans hright)

/-- Tensor the unsaturated-clique pair bound over independently rotated
clique coordinates.  Only the actual intersections with the fixed root
need have size below `r`. -/
theorem rootedUnsaturatedRotationSuccess_inter_ratio
    {v n m q r c : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {U : Finset (Finset (Fin n))}
    (hU : ∀ Q ∈ U, Q.card = q)
    (hpair : ∀ j < r,
      (orderedIntersectionPairs U j).card * Nat.choose n q ^ 2 ≤
        c * U.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n q) j).card)
    {blocks : Fin m → Finset (Fin v)}
    (hblocks : ∀ i, (blocks i).card = q)
    (hproper : ∀ i, (blocks i ∩ root).card < r)
    {φ ψ : Fin v ↪ Fin n}
    (hφ : Erdos722.RootedEmbedding.ExtendsRequest root request φ)
    (hψ : Erdos722.RootedEmbedding.ExtendsRequest root request ψ)
    (hdisj : RootedOutsideDisjoint root φ ψ) :
    Fintype.card (Fin m → Equiv.Perm (Fin n)) *
        (rootedRotationSuccess U blocks φ ∩
          rootedRotationSuccess U blocks ψ).card ≤
      c ^ m * (rootedRotationSuccess U blocks φ).card *
        (rootedRotationSuccess U blocks ψ).card := by
  apply card_rainbowHitSamples_inter_ratio_of_coordinate
  intro i
  apply card_pairHitPermutations_ratio_of_orderedPair_ratio hU
  · exact (Erdos722.RootedEmbedding.card_mapEdge φ (blocks i)).trans
      (hblocks i)
  · exact (Erdos722.RootedEmbedding.card_mapEdge ψ (blocks i)).trans
      (hblocks i)
  · have hinter := card_mapEdge_inter_mapEdge_of_rootedOutsideDisjoint
      (S := blocks i) hφ hψ hdisj
    have hratio := hpair ((blocks i ∩ root).card) (hproper i)
    simpa [rootedRotationSuccess, mappedTargets, hinter] using hratio

/-- Exact global mass consequence used both by the clique first moment and
by positivity of every rotation event. -/
theorem prunedGenerator_unsaturated_mass
    {N n q r d : ℕ} (hn : 0 < n) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (ω : {e // e ∈ uniformEdges n r} → Bool)
    (D : TwoCapPrunedData N n q r
      (generatorFaceCap d n) (generatorEdgeCap d n)
      (generatorPruneThreshold q r d n)
      (generatorFaceCliqueCap q r d n)
      (generatorEdgeCliqueCap q r d n))
    (htyp : ∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots (reserveProbabilityIcc n d hn))
    (hDK : D.K = sampledEdges n r ω)
    (hmass : (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
      2 * D.Kstar.card * Nat.choose r (r - 1))
    (hnlarge : 2 * (Nat.choose q r * (r - 1)) ≤ n)
    (hthreshold : 2 * generatorPruneThreshold q r d n ≤
      generatorCliqueLower q r d n) :
    Nat.choose n (r - 1) * generatorDegreeLower d n *
        generatorCliqueLower q r d n ≤
      (4 * r * Nat.choose q r) *
        (twoCapUnsaturatedCliques n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          D.K D.selected).card := by
  let U := twoCapUnsaturatedCliques n q r
    (generatorFaceCap d n) (generatorEdgeCap d n) D.K D.selected
  let L := generatorCliqueLower q r d n
  let T := generatorPruneThreshold q r d n
  have hlocal : ∀ e ∈ D.Kstar, L - T ≤
      (U.filter fun Q ↦ e ⊆ Q).card := by
    intro e he
    have heSample : e ∈ sampledEdges n r ω := by
      simpa [← hDK] using D.Kstar_subset he
    have htotal : L ≤
        ((cliquesIn n q r D.K).filter fun Q ↦ e ⊆ Q).card := by
      simpa [L, hDK] using generatorCliqueLower_le_cliques_through_edge
        hn hr hrq hqd hnlarge ω htyp heSample
    exact (Nat.sub_le_sub_right htotal T).trans (by
      simpa [U, T] using D.good_lower e he)
  have hUg : D.Kstar.card * (L - T) ≤ U.card * Nat.choose q r := by
    simpa [U] using
      card_Kstar_mul_goodLower_le_unsaturated_mul_choose D hlocal
  have hchoose : Nat.choose r (r - 1) = r := by
    rw [← Nat.choose_symm (by omega : r - 1 ≤ r)]
    simp [show r - (r - 1) = 1 by omega]
  rw [hchoose] at hmass
  have hmassNat : Nat.choose n (r - 1) * generatorDegreeLower d n ≤
      2 * D.Kstar.card * r := by
    simpa [uniformEdges] using hmass
  have hhalf : L ≤ 2 * (L - T) := by
    dsimp [L, T]
    omega
  calc
    Nat.choose n (r - 1) * generatorDegreeLower d n * L ≤
        (2 * D.Kstar.card * r) * L := Nat.mul_le_mul_right L hmassNat
    _ ≤ (2 * D.Kstar.card * r) * (2 * (L - T)) := by gcongr
    _ = 4 * r * (D.Kstar.card * (L - T)) := by ring
    _ ≤ 4 * r * (U.card * Nat.choose q r) := by gcongr
    _ = (4 * r * Nat.choose q r) * U.card := by ring

/-- Uniform constant-factor failure bound for rooted patterns whose
constraints are entire monochromatic unsaturated cliques. -/
theorem eventually_prunedGenerator_rootedUnsaturatedRotation_failure
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {v m : ℕ} (root : Finset (Fin v)) (hroot : root.card < v)
    (hmd : m * Nat.choose q r < d)
    (blocks : Fin m → Finset (Fin v))
    (hblocks : ∀ i, (blocks i).card = q)
    (hproper : ∀ i, (blocks i ∩ root).card < r) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
        let U := twoCapUnsaturatedCliques n q r
          (generatorFaceCap d n) (generatorEdgeCap d n) D.K D.selected
        let R := cliqueRotationPairConstant q r ^ m + 1
        R * ((rotationSamples n m).filter fun σ ↦
          Erdos722.Probability.finiteSuccessCount
            (Erdos722.RootedEmbedding.rootedEmbeddings root request)
            (rootedRotationSuccess U blocks) σ = 0).card ≤
          (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  have hpair := eventually_prunedGenerator_unsaturated_pair_ratio
    N q r d hr hrq hqd
  have hexpected := eventually_rooted_unsaturated_expected_lower
    root hroot hr hrq hqd hmd
  have hexceptional :=
    eventually_rootedExceptionalPartners_lt_rootedEmbeddings root hroot
  have hKpos : 0 < Nat.choose q r := Nat.choose_pos hrq.le
  have hdOne : 1 < d := by omega
  have hdegree := eventually_rpow_div_sixteen_le_generatorDegreeLower
    hdOne
  have hclique := eventually_generatorCliqueLower_lower q r d
    (by omega) hrq hqd
  have hthreshold := eventually_two_mul_generatorPruneThreshold_le_cliqueLower
    q r d (by omega) hrq hqd
  filter_upwards [hpair, hexpected, hexceptional, hdegree, hclique,
      hthreshold,
      eventually_ge_atTop
        (max (max (2 * v) q) (2 * (Nat.choose q r * (r - 1))))] with
      n hpair hexpected hexceptional hdegree hclique hthreshold hnlarge
  intro hn ω D htyp hDK hmass request
  let U := twoCapUnsaturatedCliques n q r
    (generatorFaceCap d n) (generatorEdgeCap d n) D.K D.selected
  have hnTwoV : 2 * v ≤ n :=
    ((le_max_left (2 * v) q).trans
      (le_max_left (max (2 * v) q) _)).trans hnlarge
  have hnq : q ≤ n :=
    ((le_max_right (2 * v) q).trans
      (le_max_left (max (2 * v) q) _)).trans hnlarge
  have hnGen : 2 * (Nat.choose q r * (r - 1)) ≤ n :=
    (le_max_right _ _).trans hnlarge
  have hUuniform : ∀ Q ∈ U, Q.card = q := by
    intro Q hQ
    exact (mem_cliquesIn.mp
      (mem_twoCapUnsaturatedCliques.mp (by simpa [U] using hQ)).1).1
  have hmassU : Nat.choose n (r - 1) * generatorDegreeLower d n *
      generatorCliqueLower q r d n ≤
        (4 * r * Nat.choose q r) * U.card := by
    simpa [U] using prunedGenerator_unsaturated_mass hn hr hrq hqd ω D
      htyp hDK hmass hnGen hthreshold
  have hdegreePos : 0 < generatorDegreeLower d n := by
    have hstrict : (0 : ℝ) <
        (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 16 := by positivity
    have : (0 : ℝ) < generatorDegreeLower d n := hstrict.trans_le hdegree
    exact_mod_cast this
  have hcliquePos : 0 < generatorCliqueLower q r d n := by
    have hstrict : (0 : ℝ) <
        (n : ℝ) ^
          (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
            (2 * (16 : ℝ) ^ (q - r) * (2 ^ q : ℝ) ^ (q - r)) := by
      positivity
    have : (0 : ℝ) < generatorCliqueLower q r d n :=
      hstrict.trans_le hclique
    exact_mod_cast this
  have hchoosePos : 0 < Nat.choose n (r - 1) :=
    Nat.choose_pos (by omega)
  have hUpos : 0 < U.card := by
    have hleft : 0 < Nat.choose n (r - 1) * generatorDegreeLower d n *
        generatorCliqueLower q r d n := by positivity
    have hright : 0 < (4 * r * Nat.choose q r) * U.card :=
      hleft.trans_le hmassU
    exact Nat.pos_of_mul_pos_left hright
  have hcandidates : 0 <
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card := by
    have hdesc : 0 < (n - root.card).descFactorial (v - root.card) :=
      Nat.descFactorial_pos.mpr (by omega)
    exact hdesc.trans_le
      (Erdos722.RootedEmbedding.descFactorial_le_card_rootedEmbeddings
        root request)
  obtain ⟨φ₀, φ₁, hφ₀, hφ₁, hdisj⟩ :=
    exists_rootedOutsideDisjoint_of_exceptional_lt root request hcandidates
      (hexceptional request)
  have hApos : 0 < (rootedRotationSuccess U blocks φ₀).card :=
    rootedRotationSuccess_card_pos hUuniform hUpos hblocks φ₀
  have hpairU : ∀ j < r,
      (orderedIntersectionPairs U j).card * Nat.choose n q ^ 2 ≤
        cliqueRotationPairConstant q r * U.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n q) j).card := by
    simpa [U] using hpair hn ω D htyp hDK hmass
  have hcorr :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (rootedRotationSuccess U blocks φ₀ ∩
            rootedRotationSuccess U blocks φ₁).card ≤
        cliqueRotationPairConstant q r ^ m *
          (rootedRotationSuccess U blocks φ₀).card *
          (rootedRotationSuccess U blocks φ₁).card :=
    rootedUnsaturatedRotationSuccess_inter_ratio hUuniform hpairU
      hblocks hproper hφ₀ hφ₁ hdisj
  have hexpectedU :
      ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) *
          Nat.choose n q ^ m ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          U.card ^ m := hexpected U hmassU request
  have hexception :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          (rootedRotationSuccess U blocks φ₀).card :=
    rootedRotation_exceptional_of_expected_lower request hUuniform hblocks
      φ₀ hexpectedU
  simpa [U] using rootedRotationFailures_paley_of_correlation
    hUuniform hblocks hφ₀ hφ₁ hdisj hApos hcorr hexception

/-- Amplified clique form: one deterministic family of colour groups
covers every request for the fixed rooted pattern by monochromatic
unsaturated cliques. -/
theorem eventually_exists_prunedGenerator_rootedUnsaturatedRotationCover
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {v m : ℕ} (root : Finset (Fin v)) (hroot : root.card < v)
    (hmd : m * Nat.choose q r < d)
    (blocks : Fin m → Finset (Fin v))
    (hblocks : ∀ i, (blocks i).card = q)
    (hproper : ∀ i, (blocks i ∩ root).card < r) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      let U := twoCapUnsaturatedCliques n q r
        (generatorFaceCap d n) (generatorEdgeCap d n) D.K D.selected
      ∃ choice : Fin (generatorEdgeCap d n) →
          (Fin m → Equiv.Perm (Fin n)),
        ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
          ∃ t : Fin (generatorEdgeCap d n), ∃ φ : Fin v ↪ Fin n,
            Erdos722.RootedEmbedding.ExtendsRequest root request φ ∧
            ∀ i, rotateEdge (choice t i).symm
              (Erdos722.RootedEmbedding.mapEdge φ (blocks i)) ∈ U := by
  let R := cliqueRotationPairConstant q r ^ m + 1
  have hR : 1 < R := by
    dsimp [R]
    have hc : 0 < cliqueRotationPairConstant q r :=
      cliqueRotationPairConstant_pos (by omega) hrq
    have : 0 < cliqueRotationPairConstant q r ^ m := pow_pos hc _
    omega
  have hfailure :=
    eventually_prunedGenerator_rootedUnsaturatedRotation_failure
      N q r d hr hrq hqd root hroot hmd blocks hblocks hproper
  have hunion := eventually_rotation_amplification_union_bound v d R
    (by have := (Nat.choose_pos hrq.le).trans hqd; omega) hR
  filter_upwards [hfailure, hunion] with n hfailure hunion
  intro hn ω D htyp hDK hmass
  let U := twoCapUnsaturatedCliques n q r
    (generatorFaceCap d n) (generatorEdgeCap d n) D.K D.selected
  apply exists_amplified_rootedRotationCover_of_scaled_bad
    (r := q) (R := R) (g := generatorEdgeCap d n) U blocks (by omega)
  · intro request
    have hf := hfailure hn ω D htyp hDK hmass request
    have hRsub : R - 1 = cliqueRotationPairConstant q r ^ m := by
      dsimp [R]
    rw [hRsub]
    simpa [R, U, Fintype.card_fun] using hf
  · exact hunion root

end

end Erdos722.CliqueRotationAsymptotic
