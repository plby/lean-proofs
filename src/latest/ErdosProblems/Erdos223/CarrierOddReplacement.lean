/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos223.CarrierOdd
import ErdosProblems.Erdos223.Lenz
import ErdosProblems.Erdos223.DiameterUnionDecomp

open scoped BigOperators EuclideanGeometry RealInnerProductSpace

namespace Erdos223.CarrierOdd

noncomputable section

/-! ## A quarter-equator replacement block -/

def quarterParameter {k : ℕ} (_hk : 2 ≤ k) (a : Fin k) : ℝ :=
  (a : ℝ) / ((k - 1 : ℕ) : ℝ)

lemma quarterParameter_nonneg {k : ℕ} (hk : 2 ≤ k) (a : Fin k) :
    0 ≤ quarterParameter hk a := by
  unfold quarterParameter
  positivity

lemma quarterParameter_le_one {k : ℕ} (hk : 2 ≤ k) (a : Fin k) :
    quarterParameter hk a ≤ 1 := by
  unfold quarterParameter
  have hkpred : 0 < k - 1 := by omega
  rw [div_le_one (by exact_mod_cast hkpred : (0 : ℝ) < (k - 1 : ℕ))]
  exact_mod_cast Nat.le_pred_of_lt a.isLt

lemma quarterParameter_sq_le_one {k : ℕ} (hk : 2 ≤ k) (a : Fin k) :
    quarterParameter hk a ^ 2 ≤ 1 := by
  have h0 := quarterParameter_nonneg hk a
  have h1 := quarterParameter_le_one hk a
  nlinarith

lemma quarterParameter_injective {k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (quarterParameter hk) := by
  intro a b hab
  unfold quarterParameter at hab
  have hkpred : 0 < k - 1 := by omega
  have hden : (((k - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hkpred.ne'
  apply Fin.ext
  exact_mod_cast (div_left_inj' hden).mp hab

/-- Equator point in the closed first quadrant of component `r`. -/
def quarterEquatorPoint {p k : ℕ} (hk : 2 ≤ k) (r : Fin p)
    (a : Fin k) : Point (2 * p + 1) :=
  EuclideanSpace.single (planeFirst p r)
      (Lenz.firstCoordinate (quarterParameter hk a)) +
    EuclideanSpace.single (planeSecond p r)
      (Lenz.secondCoordinate (quarterParameter hk a))

lemma quarterEquatorPoint_apply_second {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (a : Fin k) :
    quarterEquatorPoint hk r a (planeSecond p r) =
      Lenz.secondCoordinate (quarterParameter hk a) := by
  simp [quarterEquatorPoint, planeFirst_ne_planeSecond]

lemma quarterEquatorPoint_injective {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : Function.Injective (quarterEquatorPoint hk r) := by
  intro a b hab
  have hcoord := congrArg
    (fun z : Point (2 * p + 1) ↦ z (planeSecond p r)) hab
  rw [quarterEquatorPoint_apply_second, quarterEquatorPoint_apply_second] at hcoord
  exact quarterParameter_injective hk
    (Lenz.secondCoordinate_injective hcoord)

lemma inner_quarterEquatorPoint_self {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (a : Fin k) :
    inner ℝ (quarterEquatorPoint hk r a) (quarterEquatorPoint hk r a) = 1 / 2 := by
  have hcoord := Lenz.coordinates_sq_add (quarterParameter_sq_le_one hk a)
  simp only [quarterEquatorPoint, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply,
    starRingEnd_apply, star_trivial] at ⊢
  rw [if_neg (planeFirst_ne_planeSecond p r r),
    if_neg (planeFirst_ne_planeSecond p r r).symm]
  norm_num at ⊢
  simpa [pow_two] using hcoord

lemma quarterEquatorPoint_onEquator {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (a : Fin k) : OnEquator r (quarterEquatorPoint hk r a) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j hjf hjs hja
    simp [quarterEquatorPoint, hjf, hjs]
  · have hnormSq : ‖quarterEquatorPoint hk r a‖ ^ 2 = (1 : ℝ) / 2 := by
      rw [← real_inner_self_eq_norm_sq]
      exact inner_quarterEquatorPoint_self hk r a
    have htargetSq : (1 / Real.sqrt (2 : ℝ)) ^ 2 = (1 : ℝ) / 2 := by
      have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
      rw [div_pow, one_pow, hs]
    have hn := norm_nonneg (quarterEquatorPoint hk r a)
    have ht : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
    nlinarith
  · simp [quarterEquatorPoint, planeFirst_ne_axisIndex,
      planeSecond_ne_axisIndex]

lemma inner_quarterEquatorPoint_nonneg {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (a b : Fin k) :
    0 ≤ inner ℝ (quarterEquatorPoint hk r a) (quarterEquatorPoint hk r b) := by
  simp only [quarterEquatorPoint, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply,
    starRingEnd_apply, star_trivial]
  rw [if_neg (planeFirst_ne_planeSecond p r r),
    if_neg (planeFirst_ne_planeSecond p r r).symm]
  norm_num
  exact add_nonneg
    (mul_nonneg (Lenz.firstCoordinate_nonneg _) (Lenz.firstCoordinate_nonneg _))
    (mul_nonneg
      (Lenz.secondCoordinate_nonneg (quarterParameter_nonneg hk a))
      (Lenz.secondCoordinate_nonneg (quarterParameter_nonneg hk b)))

lemma dist_quarterEquatorPoint_le_one {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (a b : Fin k) :
    dist (quarterEquatorPoint hk r a) (quarterEquatorPoint hk r b) ≤ 1 := by
  have hsq : dist (quarterEquatorPoint hk r a)
      (quarterEquatorPoint hk r b) ^ 2 =
      1 - 2 * inner ℝ (quarterEquatorPoint hk r a)
        (quarterEquatorPoint hk r b) := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [inner_quarterEquatorPoint_self, inner_quarterEquatorPoint_self,
      real_inner_comm (quarterEquatorPoint hk r b) (quarterEquatorPoint hk r a)]
    ring
  have hi := inner_quarterEquatorPoint_nonneg hk r a b
  have hd : 0 ≤ dist (quarterEquatorPoint hk r a)
      (quarterEquatorPoint hk r b) := dist_nonneg
  nlinarith

def quarterFirst {k : ℕ} (hk : 2 ≤ k) : Fin k := ⟨0, by omega⟩

def quarterLast {k : ℕ} (hk : 2 ≤ k) : Fin k :=
  ⟨k - 1, Nat.sub_lt (by omega) (by omega)⟩

@[simp] lemma quarterParameter_first {k : ℕ} (hk : 2 ≤ k) :
    quarterParameter hk (quarterFirst hk) = 0 := by
  simp [quarterParameter, quarterFirst]

@[simp] lemma quarterParameter_last {k : ℕ} (hk : 2 ≤ k) :
    quarterParameter hk (quarterLast hk) = 1 := by
  simp only [quarterParameter, quarterLast]
  have hkpred : 0 < k - 1 := by omega
  exact div_self (by exact_mod_cast hkpred.ne' : ((k - 1 : ℕ) : ℝ) ≠ 0)

lemma dist_quarterEquatorPoint_first_last {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) :
    dist (quarterEquatorPoint hk r (quarterFirst hk))
      (quarterEquatorPoint hk r (quarterLast hk)) = 1 := by
  have hinner : inner ℝ
      (quarterEquatorPoint hk r (quarterFirst hk))
      (quarterEquatorPoint hk r (quarterLast hk)) = 0 := by
    simp only [quarterEquatorPoint, inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_left, PiLp.single_apply,
      starRingEnd_apply, star_trivial]
    rw [if_neg (planeFirst_ne_planeSecond p r r),
      if_neg (planeFirst_ne_planeSecond p r r).symm]
    norm_num [Lenz.firstCoordinate, Lenz.secondCoordinate]
  have hsq : dist (quarterEquatorPoint hk r (quarterFirst hk))
      (quarterEquatorPoint hk r (quarterLast hk)) ^ 2 = 1 := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [inner_quarterEquatorPoint_self, inner_quarterEquatorPoint_self,
      hinner, real_inner_comm]
    rw [hinner]
    ring
  have hd : 0 ≤ dist (quarterEquatorPoint hk r (quarterFirst hk))
      (quarterEquatorPoint hk r (quarterLast hk)) := dist_nonneg
  nlinarith

def quarterEquatorFinset {p k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    Finset (Point (2 * p + 1)) := by
  classical
  exact Finset.univ.image (quarterEquatorPoint hk r)

@[simp] lemma card_quarterEquatorFinset {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : (quarterEquatorFinset hk r).card = k := by
  rw [quarterEquatorFinset, Finset.card_image_of_injective _
    (quarterEquatorPoint_injective hk r)]
  simp

lemma mem_quarterEquatorFinset {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (a : Fin k) :
    quarterEquatorPoint hk r a ∈ quarterEquatorFinset hk r := by
  simp [quarterEquatorFinset]

lemma positivePole_not_mem_quarterEquatorFinset {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : positivePole p ∉ quarterEquatorFinset hk r := by
  intro h
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
  have hz := (quarterEquatorPoint_onEquator hk r a).2
  rw [ha, positivePole_axis] at hz
  have hp : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  linarith

lemma negativePole_not_mem_quarterEquatorFinset {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : negativePole p ∉ quarterEquatorFinset hk r := by
  intro h
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
  have hz := (quarterEquatorPoint_onEquator hk r a).2
  rw [ha, negativePole_axis] at hz
  have hp : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  linarith

lemma dist_positivePole_quarterEquatorPoint {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (a : Fin k) :
    dist (positivePole p) (quarterEquatorPoint hk r a) = 1 := by
  have hinner : inner ℝ (positivePole p) (quarterEquatorPoint hk r a) = 0 := by
    simp only [positivePole, quarterEquatorPoint, inner_add_right,
      EuclideanSpace.inner_single_left, PiLp.single_apply,
      starRingEnd_apply, star_trivial]
    rw [if_neg (planeFirst_ne_axisIndex p r).symm,
      if_neg (planeSecond_ne_axisIndex p r).symm]
    norm_num
  have hpinner : inner ℝ (positivePole p) (positivePole p) = 1 / 2 := by
    rw [real_inner_self_eq_norm_sq, (positivePole_onSphere r).2]
    have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
    rw [div_pow, one_pow, hs]
  have hsq : dist (positivePole p) (quarterEquatorPoint hk r a) ^ 2 = 1 := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [hpinner, inner_quarterEquatorPoint_self, hinner, real_inner_comm]
    rw [hinner]
    ring
  have hd : 0 ≤ dist (positivePole p) (quarterEquatorPoint hk r a) := dist_nonneg
  nlinarith

lemma dist_negativePole_quarterEquatorPoint {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (a : Fin k) :
    dist (negativePole p) (quarterEquatorPoint hk r a) = 1 := by
  have hinner : inner ℝ (negativePole p) (quarterEquatorPoint hk r a) = 0 := by
    simp only [negativePole, quarterEquatorPoint, inner_add_right,
      EuclideanSpace.inner_single_left, PiLp.single_apply,
      starRingEnd_apply, star_trivial]
    rw [if_neg (planeFirst_ne_axisIndex p r).symm,
      if_neg (planeSecond_ne_axisIndex p r).symm]
    norm_num
  have hpinner : inner ℝ (negativePole p) (negativePole p) = 1 / 2 := by
    rw [real_inner_self_eq_norm_sq, (negativePole_onSphere r).2]
    have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
    rw [div_pow, one_pow, hs]
  have hsq : dist (negativePole p) (quarterEquatorPoint hk r a) ^ 2 = 1 := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [hpinner, inner_quarterEquatorPoint_self, hinner, real_inner_comm]
    rw [hinner]
    ring
  have hd : 0 ≤ dist (negativePole p) (quarterEquatorPoint hk r a) := dist_nonneg
  nlinarith

def positiveReplacementBlock {p k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    Finset (Point (2 * p + 1)) :=
  insert (positivePole p) (quarterEquatorFinset hk r)

def negativeReplacementBlock {p k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    Finset (Point (2 * p + 1)) :=
  insert (negativePole p) (quarterEquatorFinset hk r)

@[simp] lemma card_positiveReplacementBlock {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : (positiveReplacementBlock hk r).card = k + 1 := by
  rw [positiveReplacementBlock,
    Finset.card_insert_of_notMem (positivePole_not_mem_quarterEquatorFinset hk r),
    card_quarterEquatorFinset]

@[simp] lemma card_negativeReplacementBlock {p k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : (negativeReplacementBlock hk r).card = k + 1 := by
  rw [negativeReplacementBlock,
    Finset.card_insert_of_notMem (negativePole_not_mem_quarterEquatorFinset hk r),
    card_quarterEquatorFinset]

lemma positiveReplacementBlock_pairwise_dist_le_one {p k : ℕ}
    (hk : 2 ≤ k) (r : Fin p) :
    ∀ x ∈ positiveReplacementBlock hk r,
      ∀ y ∈ positiveReplacementBlock hk r, dist x y ≤ 1 := by
  intro x hx y hy
  simp only [positiveReplacementBlock, Finset.mem_insert] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · simp
  · rw [quarterEquatorFinset] at hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    exact (dist_positivePole_quarterEquatorPoint hk r a).le
  · rw [quarterEquatorFinset] at hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    simpa [dist_comm] using (dist_positivePole_quarterEquatorPoint hk r a).le
  · rw [quarterEquatorFinset] at hx hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
    exact dist_quarterEquatorPoint_le_one hk r a b

lemma negativeReplacementBlock_pairwise_dist_le_one {p k : ℕ}
    (hk : 2 ≤ k) (r : Fin p) :
    ∀ x ∈ negativeReplacementBlock hk r,
      ∀ y ∈ negativeReplacementBlock hk r, dist x y ≤ 1 := by
  intro x hx y hy
  simp only [negativeReplacementBlock, Finset.mem_insert] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · simp
  · rw [quarterEquatorFinset] at hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    exact (dist_negativePole_quarterEquatorPoint hk r a).le
  · rw [quarterEquatorFinset] at hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    simpa [dist_comm] using (dist_negativePole_quarterEquatorPoint hk r a).le
  · rw [quarterEquatorFinset] at hx hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
    exact dist_quarterEquatorPoint_le_one hk r a b

lemma positiveReplacementBlock_isDiameterOne {p k : ℕ}
    (hk : 2 ≤ k) (r : Fin p) :
    IsDiameterOne (positiveReplacementBlock hk r) := by
  rw [isDiameterOne_iff]
  refine ⟨positiveReplacementBlock_pairwise_dist_le_one hk r, ?_⟩
  refine ⟨positivePole p, by simp [positiveReplacementBlock],
    quarterEquatorPoint hk r (quarterFirst hk), ?_, ?_⟩
  · simp [positiveReplacementBlock, mem_quarterEquatorFinset]
  · exact dist_positivePole_quarterEquatorPoint hk r (quarterFirst hk)

lemma negativeReplacementBlock_isDiameterOne {p k : ℕ}
    (hk : 2 ≤ k) (r : Fin p) :
    IsDiameterOne (negativeReplacementBlock hk r) := by
  rw [isDiameterOne_iff]
  refine ⟨negativeReplacementBlock_pairwise_dist_le_one hk r, ?_⟩
  refine ⟨negativePole p, by simp [negativeReplacementBlock],
    quarterEquatorPoint hk r (quarterFirst hk), ?_, ?_⟩
  · simp [negativeReplacementBlock, mem_quarterEquatorFinset]
  · exact dist_negativePole_quarterEquatorPoint hk r (quarterFirst hk)

inductive PoleSign where
  | positive
  | negative
deriving DecidableEq

def PoleSign.pole (s : PoleSign) (p : ℕ) : Point (2 * p + 1) :=
  match s with
  | .positive => positivePole p
  | .negative => negativePole p

def PoleSign.replacementBlock {p k : ℕ} (s : PoleSign)
    (hk : 2 ≤ k) (r : Fin p) : Finset (Point (2 * p + 1)) :=
  match s with
  | .positive => positiveReplacementBlock hk r
  | .negative => negativeReplacementBlock hk r

@[simp] lemma PoleSign.card_replacementBlock {p k : ℕ} (s : PoleSign)
    (hk : 2 ≤ k) (r : Fin p) : (s.replacementBlock hk r).card = k + 1 := by
  cases s <;> simp [PoleSign.replacementBlock]

lemma PoleSign.replacementBlock_isDiameterOne {p k : ℕ} (s : PoleSign)
    (hk : 2 ≤ k) (r : Fin p) : IsDiameterOne (s.replacementBlock hk r) := by
  cases s
  · exact positiveReplacementBlock_isDiameterOne hk r
  · exact negativeReplacementBlock_isDiameterOne hk r

lemma PoleSign.pole_mem_replacementBlock {p k : ℕ} (s : PoleSign)
    (hk : 2 ≤ k) (r : Fin p) : s.pole p ∈ s.replacementBlock hk r := by
  cases s <;> simp [PoleSign.pole, PoleSign.replacementBlock,
    positiveReplacementBlock, negativeReplacementBlock]

lemma PoleSign.mem_replacementBlock_iff {p k : ℕ} (s : PoleSign)
    (hk : 2 ≤ k) (r : Fin p) {z : Point (2 * p + 1)} :
    z ∈ s.replacementBlock hk r ↔
      z = s.pole p ∨ z ∈ quarterEquatorFinset hk r := by
  cases s <;> simp [PoleSign.pole, PoleSign.replacementBlock,
    positiveReplacementBlock, negativeReplacementBlock]

lemma PoleSign.dist_pole_quarterEquatorPoint {p k : ℕ} (s : PoleSign)
    (hk : 2 ≤ k) (r : Fin p) (a : Fin k) :
    dist (s.pole p) (quarterEquatorPoint hk r a) = 1 := by
  cases s
  · exact dist_positivePole_quarterEquatorPoint hk r a
  · exact dist_negativePole_quarterEquatorPoint hk r a

lemma one_le_diameterPairCount_quarterEquatorFinset {p k : ℕ}
    (hk : 2 ≤ k) (r : Fin p) :
    1 ≤ diameterPairCount (quarterEquatorFinset hk r) := by
  let x : {z // z ∈ quarterEquatorFinset hk r} :=
    ⟨quarterEquatorPoint hk r (quarterFirst hk),
      mem_quarterEquatorFinset hk r (quarterFirst hk)⟩
  let y : {z // z ∈ quarterEquatorFinset hk r} :=
    ⟨quarterEquatorPoint hk r (quarterLast hk),
      mem_quarterEquatorFinset hk r (quarterLast hk)⟩
  rw [diameterPairCount, Finset.one_le_card]
  refine ⟨s(x, y), SimpleGraph.mem_edgeFinset.mpr ?_⟩
  exact dist_quarterEquatorPoint_first_last hk r

lemma PoleSign.card_cross_pole_quarterEquator {p k : ℕ} (s : PoleSign)
    (hk : 2 ≤ k) (r : Fin p) :
    ((({s.pole p} : Finset (Point (2 * p + 1))).product
      (quarterEquatorFinset hk r)).filter
      fun e ↦ dist e.1 e.2 = 1).card = k := by
  have hfilter : ((({s.pole p} : Finset (Point (2 * p + 1))).product
      (quarterEquatorFinset hk r)).filter
      fun e ↦ dist e.1 e.2 = 1) =
      ({s.pole p} : Finset (Point (2 * p + 1))).product
        (quarterEquatorFinset hk r) := by
    apply Finset.filter_eq_self.mpr
    intro e he
    have hp := Finset.mem_product.mp he
    have he1 : e.1 = s.pole p := Finset.mem_singleton.mp hp.1
    rw [quarterEquatorFinset] at hp
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hp.2
    rw [he1, ← ha]
    exact s.dist_pole_quarterEquatorPoint hk r a
  rw [hfilter]
  exact (Finset.card_product _ _).trans (by simp)

lemma PoleSign.diameterPairCount_replacementBlock_ge {p k : ℕ}
    (s : PoleSign) (hk : 2 ≤ k) (r : Fin p) :
    k + 1 ≤ diameterPairCount (s.replacementBlock hk r) := by
  have hdisj : Disjoint ({s.pole p} : Finset (Point (2 * p + 1)))
      (quarterEquatorFinset hk r) := by
    rw [Finset.disjoint_left]
    intro z hzp hzeq
    have hz : z = s.pole p := Finset.mem_singleton.mp hzp
    subst z
    cases s
    · exact positivePole_not_mem_quarterEquatorFinset hk r hzeq
    · exact negativePole_not_mem_quarterEquatorFinset hk r hzeq
  have hblock : s.replacementBlock hk r =
      {s.pole p} ∪ quarterEquatorFinset hk r := by
    cases s <;> rfl
  rw [hblock, diameterPairCount_union_of_disjoint _ _ hdisj]
  have heq := one_le_diameterPairCount_quarterEquatorFinset hk r
  have hcross := s.card_cross_pole_quarterEquator hk r
  have hsingle : diameterPairCount ({s.pole p} : Finset (Point (2 * p + 1))) = 0 := by
    simpa using diameterPairCount_le_choose ({s.pole p} : Finset (Point (2 * p + 1)))
  rw [hsingle, zero_add, hcross]
  omega
namespace Assignment

variable {d p : ℕ} {A : Finset (Point d)} (Q : Assignment (p := p) A)

def outsideAssigned (r : Fin p) : Finset {x : Point d // x ∈ A} := by
  classical
  exact Finset.univ.filter fun x ↦ Q.part x ≠ r

def outsidePoints (r : Fin p) : Finset (Point d) := by
  classical
  exact (Q.outsideAssigned r).map
    ⟨Subtype.val, Subtype.val_injective⟩

def partPoints (r : Fin p) : Finset (Point d) := by
  classical
  exact (AssignmentIntegration.partFinset Q r).map
    ⟨Subtype.val, Subtype.val_injective⟩

def localInsideCount (r : Fin p) : ℕ := diameterPairCount (Q.partPoints r)

def outsideOffAssigned (r : Fin p) : Finset {x : Point d // x ∈ A} := by
  classical
  exact (Q.outsideAssigned r).filter fun x ↦
    x.1 ∉ Q.carrier.equator (Q.part x)

def outsideOffCount (r : Fin p) : ℕ := (Q.outsideOffAssigned r).card

def outsideEquatorAssigned (r : Fin p) : Finset {x : Point d // x ∈ A} := by
  classical
  exact (Q.outsideAssigned r).filter fun x ↦
    x.1 ∈ Q.carrier.equator (Q.part x)

@[simp] lemma mem_outsideAssigned_iff (r : Fin p)
    {x : {x : Point d // x ∈ A}} :
    x ∈ Q.outsideAssigned r ↔ Q.part x ≠ r := by
  simp [outsideAssigned]

lemma mem_outsidePoints_iff (r : Fin p) {x : Point d} :
    x ∈ Q.outsidePoints r ↔
      ∃ hx : x ∈ A, Q.part ⟨x, hx⟩ ≠ r := by
  classical
  simp only [outsidePoints, Finset.mem_map, mem_outsideAssigned_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hpart⟩
    exact ⟨⟨x, hx⟩, hpart, rfl⟩

lemma card_outsidePoints_add_partCard (r : Fin p) :
    (Q.outsidePoints r).card + AssignmentIntegration.partCard Q r = A.card := by
  classical
  rw [outsidePoints, Finset.card_map]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset {x : Point d // x ∈ A}))
    (p := fun x ↦ Q.part x ≠ r)
  simpa [outsideAssigned, AssignmentIntegration.partCard,
    AssignmentIntegration.partFinset] using h

@[simp] lemma card_partPoints (r : Fin p) :
    (Q.partPoints r).card = AssignmentIntegration.partCard Q r := by
  simp [partPoints, AssignmentIntegration.partCard]

lemma partPoints_disjoint_outsidePoints (r : Fin p) :
    Disjoint (Q.partPoints r) (Q.outsidePoints r) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxpart hxout
  obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hxpart
  obtain ⟨b, hb, hbx⟩ := Finset.mem_map.mp hxout
  have hapart : Q.part a = r :=
    (AssignmentIntegration.mem_partFinset_iff Q).mp ha
  have hbpart : Q.part b ≠ r := (Q.mem_outsideAssigned_iff r).mp hb
  have hab : a = b := Subtype.ext (hax.trans hbx.symm)
  subst b
  exact hbpart hapart

lemma partPoints_union_outsidePoints (r : Fin p) :
    Q.partPoints r ∪ Q.outsidePoints r = A := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, -, hax⟩ := Finset.mem_map.mp hx
      simpa [← hax] using a.2
    · obtain ⟨a, -, hax⟩ := Finset.mem_map.mp hx
      simpa [← hax] using a.2
  · intro hxA
    let a : {z : Point d // z ∈ A} := ⟨x, hxA⟩
    by_cases ha : Q.part a = r
    · apply Finset.mem_union_left
      exact Finset.mem_map.mpr ⟨a,
        (AssignmentIntegration.mem_partFinset_iff Q).2 ha, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_map.mpr ⟨a, (Q.mem_outsideAssigned_iff r).2 ha, rfl⟩

def assignedOldCrossPairs (r : Fin p) :
    Finset ({x : Point d // x ∈ A} × {x : Point d // x ∈ A}) := by
  classical
  exact ((AssignmentIntegration.partFinset Q r).product
    (Q.outsideAssigned r)).filter fun e ↦ dist e.1.1 e.2.1 = 1

def assignedMissingOldCrossPairs (r : Fin p) :
    Finset ({x : Point d // x ∈ A} × {x : Point d // x ∈ A}) := by
  classical
  exact ((AssignmentIntegration.partFinset Q r).product
    (Q.outsideAssigned r)).filter fun e ↦ dist e.1.1 e.2.1 ≠ 1

lemma assignedMissingOldCrossPairs_eq_product_off (r : Fin p) :
    Q.assignedMissingOldCrossPairs r =
      (Q.offPoints r).product (Q.outsideOffAssigned r) := by
  classical
  ext e
  constructor
  · intro he
    have he' := Finset.mem_filter.mp he
    have hp := Finset.mem_product.mp he'.1
    have hxpart : Q.part e.1 = r :=
      (AssignmentIntegration.mem_partFinset_iff Q).mp hp.1
    have hypart : Q.part e.2 ≠ r := (Q.mem_outsideAssigned_iff r).mp hp.2
    have hxsphere : e.1.1 ∈ Q.carrier.sphere r := by
      simpa [hxpart] using Q.mem_sphere e.1
    have hysphere : e.2.1 ∈ Q.carrier.sphere (Q.part e.2) := Q.mem_sphere e.2
    have hiff := Q.carrier.dist_eq_one_iff_mem_equator_of_mem_spheres
      (show r ≠ Q.part e.2 by exact hypart.symm) hxsphere hysphere
    have hxnot : e.1.1 ∉ Q.carrier.equator r := by
      intro hx
      exact he'.2 (hiff.2 (Or.inl hx))
    have hynot : e.2.1 ∉ Q.carrier.equator (Q.part e.2) := by
      intro hy
      exact he'.2 (hiff.2 (Or.inr hy))
    exact Finset.mem_product.mpr ⟨Q.mem_offPoints_iff.mpr ⟨hxpart, hxnot⟩,
      Finset.mem_filter.mpr ⟨hp.2, hynot⟩⟩
  · intro he
    have hp := Finset.mem_product.mp he
    have hxoff := Q.mem_offPoints_iff.mp hp.1
    have hyout := Finset.mem_filter.mp hp.2
    have hypart : Q.part e.2 ≠ r := (Q.mem_outsideAssigned_iff r).mp hyout.1
    rw [assignedMissingOldCrossPairs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨
      (AssignmentIntegration.mem_partFinset_iff Q).2 hxoff.1, hyout.1⟩, ?_⟩
    intro hd
    have hxsphere : e.1.1 ∈ Q.carrier.sphere r := by
      simpa [hxoff.1] using Q.mem_sphere e.1
    have hysphere : e.2.1 ∈ Q.carrier.sphere (Q.part e.2) := Q.mem_sphere e.2
    rcases (Q.carrier.dist_eq_one_iff_mem_equator_of_mem_spheres
      (show r ≠ Q.part e.2 by exact hypart.symm) hxsphere hysphere).1 hd with
      hxeq | hyeq
    · exact hxoff.2 hxeq
    · exact hyout.2 hyeq

lemma card_assignedOldCrossPairs_add_missing (r : Fin p) :
    (Q.assignedOldCrossPairs r).card +
        Q.offCount r * Q.outsideOffCount r =
      AssignmentIntegration.partCard Q r * (Q.outsidePoints r).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (AssignmentIntegration.partFinset Q r).product (Q.outsideAssigned r))
    (p := fun e ↦ dist e.1.1 e.2.1 = 1)
  have hmissing : (Q.assignedMissingOldCrossPairs r).card =
      Q.offCount r * Q.outsideOffCount r := by
    rw [Q.assignedMissingOldCrossPairs_eq_product_off r]
    exact Finset.card_product _ _
  have htotal : ((AssignmentIntegration.partFinset Q r).product
      (Q.outsideAssigned r)).card =
      AssignmentIntegration.partCard Q r * (Q.outsidePoints r).card := by
    calc
      ((AssignmentIntegration.partFinset Q r).product
          (Q.outsideAssigned r)).card =
          (AssignmentIntegration.partFinset Q r).card *
            (Q.outsideAssigned r).card := Finset.card_product _ _
      _ = AssignmentIntegration.partCard Q r * (Q.outsidePoints r).card := by
        rw [show (AssignmentIntegration.partFinset Q r).card =
          AssignmentIntegration.partCard Q r by rfl]
        rw [show (Q.outsideAssigned r).card = (Q.outsidePoints r).card by
          simp [outsidePoints]]
  change (Q.assignedOldCrossPairs r).card + _ = _
  rw [← hmissing, ← htotal]
  simpa [assignedOldCrossPairs, assignedMissingOldCrossPairs] using hsplit

lemma card_ambient_old_cross_filter_eq_assignedOldCrossPairs (r : Fin p) :
    (((Q.partPoints r).product (Q.outsidePoints r)).filter
      fun e ↦ dist e.1 e.2 = 1).card =
      (Q.assignedOldCrossPairs r).card := by
  classical
  symm
  refine Finset.card_bij (fun e _ ↦ (e.1.1, e.2.1)) ?_ ?_ ?_
  · intro e he
    have he' := Finset.mem_filter.mp he
    have hp := Finset.mem_product.mp he'.1
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, he'.2⟩
    · exact Finset.mem_map.mpr ⟨e.1, hp.1, rfl⟩
    · exact Finset.mem_map.mpr ⟨e.2, hp.2, rfl⟩
  · intro e he f hf hef
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hef))
      (Subtype.ext (congrArg Prod.snd hef))
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hp := Finset.mem_product.mp hq'.1
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_map.mp hp.1
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_map.mp hp.2
    let e : {x : Point d // x ∈ A} × {x : Point d // x ∈ A} := (x, y)
    refine ⟨e, ?_, ?_⟩
    · rw [assignedOldCrossPairs, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
      have hxval : x.1 = q.1 := by simpa using hxeq
      have hyval : y.1 = q.2 := by simpa using hyeq
      rw [hxval, hyval]
      exact hq'.2
    · apply Prod.ext
      · simpa using hxeq
      · simpa using hyeq

lemma old_edge_decomposition (r : Fin p) :
    diameterPairCount A = Q.localInsideCount r +
      (Q.assignedOldCrossPairs r).card +
      diameterPairCount (Q.outsidePoints r) := by
  have hdecomp := diameterPairCount_union_of_disjoint
    (Q.partPoints r) (Q.outsidePoints r) (Q.partPoints_disjoint_outsidePoints r)
  rw [Q.partPoints_union_outsidePoints r] at hdecomp
  rw [Q.card_ambient_old_cross_filter_eq_assignedOldCrossPairs r] at hdecomp
  simpa [localInsideCount] using hdecomp

lemma outsideOffCount_eq_otherOffTotal (r : Fin p) :
    Q.outsideOffCount r = otherOffTotal Q.offCount r := by
  classical
  let F : Fin p → ℕ := fun i ↦
    ((Q.outsideOffAssigned r).filter fun x ↦ Q.part x = i).card
  have hfiber := Finset.sum_fiberwise (Q.outsideOffAssigned r) Q.part
    (fun _ ↦ (1 : ℕ))
  have hfiber' : ∑ i : Fin p, F i = Q.outsideOffCount r := by
    simpa [F, outsideOffCount] using hfiber
  have hFr : F r = 0 := by
    rw [show F r = ((Q.outsideOffAssigned r).filter
      fun x ↦ Q.part x = r).card by rfl, Finset.card_eq_zero]
    ext x
    simp [outsideOffAssigned, outsideAssigned]
    tauto
  have hFi (i : Fin p) (hir : i ≠ r) : F i = Q.offCount i := by
    dsimp [F]
    rw [offCount]
    congr 1
    ext x
    simp [outsideOffAssigned, outsideAssigned, offPoints, hir]
    constructor
    · rintro ⟨⟨hxr, heq⟩, hpi⟩
      exact ⟨hpi, by simpa [hpi] using heq⟩
    · rintro ⟨hpi, heq⟩
      refine ⟨⟨?_, ?_⟩, hpi⟩
      · intro hpr
        exact hir (hpi.symm.trans hpr)
      · simpa [hpi] using heq
  rw [← hfiber', otherOffTotal]
  calc
    ∑ i : Fin p, F i = ∑ i ∈ Finset.univ.erase r, F i := by
      rw [← Finset.sum_erase_add _ F (Finset.mem_univ r), hFr, add_zero]
    _ = ∑ i ∈ Finset.univ.erase r, Q.offCount i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hFi i (Finset.ne_of_mem_erase hi)

lemma old_edge_decomposition_add_cross_defect_from (r : Fin p) :
    diameterPairCount A + Q.offCount r * otherOffTotal Q.offCount r =
      diameterPairCount (Q.outsidePoints r) + Q.localInsideCount r +
        AssignmentIntegration.partCard Q r * (Q.outsidePoints r).card := by
  have hedge := Q.old_edge_decomposition r
  have hcross := Q.card_assignedOldCrossPairs_add_missing r
  rw [← Q.outsideOffCount_eq_otherOffTotal r]
  omega

lemma card_outsideEquatorAssigned_add_off (r : Fin p) :
    (Q.outsideEquatorAssigned r).card + Q.outsideOffCount r =
      (Q.outsideAssigned r).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Q.outsideAssigned r)
    (p := fun x ↦ x.1 ∈ Q.carrier.equator (Q.part x))
  simpa [outsideEquatorAssigned, outsideOffCount, outsideOffAssigned] using h

def replacementCrossPairs (s : PoleSign) {k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : Finset ({x : Point d // x ∈ A} × Point (2 * p + 1)) := by
  classical
  exact ((Q.outsideAssigned r).product (s.replacementBlock hk r)).filter
    fun e ↦ dist e.1.1 (Q.carrier.place e.2) = 1

def equatorReplacementCrossPairs {k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : Finset ({x : Point d // x ∈ A} × Point (2 * p + 1)) :=
  (Q.outsideAssigned r).product (quarterEquatorFinset hk r)

def poleReplacementCrossPairs (s : PoleSign) (r : Fin p) :
    Finset ({x : Point d // x ∈ A} × Point (2 * p + 1)) :=
  (Q.outsideEquatorAssigned r).product {s.pole p}

lemma replacementCrossPairs_eq_union
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    Q.replacementCrossPairs s hk r =
      Q.equatorReplacementCrossPairs hk r ∪
        Q.poleReplacementCrossPairs s r := by
  classical
  ext e
  rcases e with ⟨x, z⟩
  rw [replacementCrossPairs, equatorReplacementCrossPairs,
    poleReplacementCrossPairs]
  simp only [Finset.mem_filter, Finset.mem_union]
  have hm₁ : (x, z) ∈ (Q.outsideAssigned r).product
      (s.replacementBlock hk r) ↔
      x ∈ Q.outsideAssigned r ∧ z ∈ s.replacementBlock hk r := by simp
  have hm₂ : (x, z) ∈ (Q.outsideAssigned r).product
      (quarterEquatorFinset hk r) ↔
      x ∈ Q.outsideAssigned r ∧ z ∈ quarterEquatorFinset hk r := by simp
  have hm₃ : (x, z) ∈ (Q.outsideEquatorAssigned r).product {s.pole p} ↔
      x ∈ Q.outsideEquatorAssigned r ∧ z = s.pole p := by
    constructor
    · intro h
      have h' := Finset.mem_product.mp h
      exact ⟨h'.1, Finset.mem_singleton.mp h'.2⟩
    · rintro ⟨hx, hz⟩
      exact Finset.mem_product.mpr ⟨hx, Finset.mem_singleton.mpr hz⟩
  rw [hm₁, hm₂, hm₃]
  change ((x ∈ Q.outsideAssigned r ∧ z ∈ s.replacementBlock hk r) ∧
      dist x.1 (Q.carrier.place z) = 1) ↔
    (x ∈ Q.outsideAssigned r ∧ z ∈ quarterEquatorFinset hk r) ∨
      (x ∈ Q.outsideEquatorAssigned r ∧ z = s.pole p)
  have classify (hxout : x ∈ Q.outsideAssigned r)
      (hz : z ∈ s.replacementBlock hk r) :
      dist x.1 (Q.carrier.place z) = 1 ↔
        z ∈ quarterEquatorFinset hk r ∨
          (x ∈ Q.outsideEquatorAssigned r ∧ z = s.pole p) := by
    have hxpart : Q.part x ≠ r := (Q.mem_outsideAssigned_iff r).mp hxout
    rcases (s.mem_replacementBlock_iff hk r).mp hz with rfl | hzeq
    · have hpsphere : Q.carrier.place (s.pole p) ∈ Q.carrier.sphere r := by
        cases s
        · exact ⟨positivePole p, positivePole_onSphere r, rfl⟩
        · exact ⟨negativePole p, negativePole_onSphere r, rfl⟩
      have hpnot : Q.carrier.place (s.pole p) ∉ Q.carrier.equator r := by
        intro hp
        obtain ⟨w, hw, hwp⟩ := hp
        have hw' : w = s.pole p := Q.carrier.place_injective hwp
        subst w
        cases s
        · exact positivePole_not_onEquator r hw
        · exact negativePole_not_onEquator r hw
      have hpcanon : s.pole p ∉ quarterEquatorFinset hk r := by
        cases s
        · exact positivePole_not_mem_quarterEquatorFinset hk r
        · exact negativePole_not_mem_quarterEquatorFinset hk r
      have hxsphere : x.1 ∈ Q.carrier.sphere (Q.part x) := Q.mem_sphere x
      have hiff := Q.carrier.dist_eq_one_iff_mem_equator_of_mem_spheres
        (show r ≠ Q.part x by exact hxpart.symm) hpsphere hxsphere
      constructor
      · intro hd
        have hd' : dist (Q.carrier.place (s.pole p)) x.1 = 1 := by
          simpa [dist_comm] using hd
        rcases hiff.mp hd' with hpeq | hxeq
        · exact (hpnot hpeq).elim
        · exact Or.inr ⟨by simpa [outsideEquatorAssigned, hxout] using hxeq, rfl⟩
      · rintro (hpq | ⟨hxeq, -⟩)
        · exact (hpcanon hpq).elim
        · have hxeq' : x.1 ∈ Q.carrier.equator (Q.part x) :=
            (Finset.mem_filter.mp hxeq).2
          simpa [dist_comm] using hiff.mpr (Or.inr hxeq')
    · rw [quarterEquatorFinset] at hzeq
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hzeq
      have hqe : Q.carrier.place (quarterEquatorPoint hk r a) ∈
          Q.carrier.equator r :=
        ⟨quarterEquatorPoint hk r a, quarterEquatorPoint_onEquator hk r a, rfl⟩
      have hxsphere : x.1 ∈ Q.carrier.sphere (Q.part x) := Q.mem_sphere x
      have hd := Q.carrier.dist_eq_one_of_mem_equator_mem_sphere
        (show r ≠ Q.part x by exact hxpart.symm) hqe hxsphere
      rw [dist_comm] at hd
      simp [mem_quarterEquatorFinset hk r a, hd]
  constructor
  · rintro ⟨⟨hxout, hz⟩, hdist⟩
    rcases (classify hxout hz).mp hdist with hzeq | ⟨hxeq, hzp⟩
    · exact Or.inl ⟨hxout, hzeq⟩
    · exact Or.inr ⟨hxeq, hzp⟩
  · rintro (hbase | hpole)
    · refine ⟨⟨hbase.1, ?_⟩, ?_⟩
      · exact (s.mem_replacementBlock_iff hk r).2 (Or.inr hbase.2)
      · exact (classify hbase.1
          ((s.mem_replacementBlock_iff hk r).2 (Or.inr hbase.2))).2
          (Or.inl hbase.2)
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact (Finset.mem_filter.mp hpole.1).1
      · simpa [hpole.2] using s.pole_mem_replacementBlock hk r
      · apply (classify (Finset.mem_filter.mp hpole.1).1
          (by simpa [hpole.2] using s.pole_mem_replacementBlock hk r)).2
        exact Or.inr ⟨hpole.1, hpole.2⟩

lemma equatorReplacementCrossPairs_disjoint_pole
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    Disjoint (Q.equatorReplacementCrossPairs hk r)
      (Q.poleReplacementCrossPairs s r) := by
  classical
  rw [Finset.disjoint_left]
  intro e heq hpole
  have heq' := Finset.mem_product.mp heq
  have hpole' := Finset.mem_product.mp hpole
  have hz : e.2 = s.pole p := Finset.mem_singleton.mp hpole'.2
  rw [hz] at heq'
  cases s
  · exact positivePole_not_mem_quarterEquatorFinset hk r heq'.2
  · exact negativePole_not_mem_quarterEquatorFinset hk r heq'.2

lemma card_replacementCrossPairs_add_off
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    (Q.replacementCrossPairs s hk r).card + Q.outsideOffCount r =
      (k + 1) * (Q.outsidePoints r).card := by
  have hsplit := Q.card_outsideEquatorAssigned_add_off r
  have hbase : (Q.equatorReplacementCrossPairs hk r).card =
      (Q.outsideAssigned r).card * k := by
    rw [equatorReplacementCrossPairs]
    exact (Finset.card_product _ _).trans (by rw [card_quarterEquatorFinset])
  have hpole : (Q.poleReplacementCrossPairs s r).card =
      (Q.outsideEquatorAssigned r).card := by
    rw [poleReplacementCrossPairs]
    simpa using Finset.card_product (Q.outsideEquatorAssigned r) {s.pole p}
  have hcross : (Q.replacementCrossPairs s hk r).card =
      (Q.equatorReplacementCrossPairs hk r).card +
        (Q.poleReplacementCrossPairs s r).card := by
    rw [Q.replacementCrossPairs_eq_union s hk r,
      Finset.card_union_of_disjoint
        (Q.equatorReplacementCrossPairs_disjoint_pole s hk r)]
  have houtcard : (Q.outsideAssigned r).card = (Q.outsidePoints r).card := by
    simp [outsidePoints]
  calc
    (Q.replacementCrossPairs s hk r).card + Q.outsideOffCount r =
        ((Q.equatorReplacementCrossPairs hk r).card +
          (Q.poleReplacementCrossPairs s r).card) + Q.outsideOffCount r := by
            rw [hcross]
    _ = ((Q.outsideAssigned r).card * k +
          (Q.outsideEquatorAssigned r).card) + Q.outsideOffCount r := by
            rw [hbase, hpole]
    _ = (k + 1) * (Q.outsidePoints r).card := by
      rw [← houtcard]
      rw [Nat.add_assoc, hsplit]
      ring

def ambientReplacementBlock (s : PoleSign) {k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : Finset (Point d) :=
  (s.replacementBlock hk r).map
    ⟨Q.carrier.place, Q.carrier.place_injective⟩

lemma card_ambient_cross_filter_eq_replacementCrossPairs
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    (((Q.outsidePoints r).product (Q.ambientReplacementBlock s hk r)).filter
      fun e ↦ dist e.1 e.2 = 1).card =
      (Q.replacementCrossPairs s hk r).card := by
  classical
  symm
  refine Finset.card_bij (fun e _ ↦ (e.1.1, Q.carrier.place e.2)) ?_ ?_ ?_
  · intro e he
    have he' := Finset.mem_filter.mp he
    have heprod := Finset.mem_product.mp he'.1
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, he'.2⟩
    · exact Finset.mem_map.mpr ⟨e.1, heprod.1, rfl⟩
    · exact Finset.mem_map.mpr ⟨e.2, heprod.2, rfl⟩
  · intro e he f hf hef
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hef)
    · exact Q.carrier.place_injective (congrArg Prod.snd hef)
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqprod := Finset.mem_product.mp hq'.1
    obtain ⟨x, hxout, hxeq⟩ := Finset.mem_map.mp hqprod.1
    obtain ⟨z, hzblock, hzeq⟩ := Finset.mem_map.mp hqprod.2
    let e : {x : Point d // x ∈ A} × Point (2 * p + 1) := (x, z)
    refine ⟨e, ?_, ?_⟩
    · rw [replacementCrossPairs, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨hxout, hzblock⟩, ?_⟩
      change dist x.1 (Q.carrier.place z) = 1
      have hxval : x.1 = q.1 := by simpa using hxeq
      have hzval : Q.carrier.place z = q.2 := by simpa using hzeq
      rw [hxval, hzval]
      exact hq'.2
    · apply Prod.ext
      · exact hxeq
      · exact hzeq

@[simp] lemma card_ambientReplacementBlock (s : PoleSign) {k : ℕ}
    (hk : 2 ≤ k) (r : Fin p) :
    (Q.ambientReplacementBlock s hk r).card = k + 1 := by
  simp [ambientReplacementBlock]

lemma mem_ambientReplacementBlock_iff (s : PoleSign) {k : ℕ}
    (hk : 2 ≤ k) (r : Fin p) {x : Point d} :
    x ∈ Q.ambientReplacementBlock s hk r ↔
      ∃ z ∈ s.replacementBlock hk r, Q.carrier.place z = x := by
  simp [ambientReplacementBlock]

lemma diameterPairCount_ambientReplacementBlock
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    diameterPairCount (Q.ambientReplacementBlock s hk r) =
      diameterPairCount (s.replacementBlock hk r) := by
  let e : {z : Point (2 * p + 1) // z ∈ s.replacementBlock hk r} ≃
      {x : Point d // x ∈ Q.ambientReplacementBlock s hk r} :=
    { toFun := fun z ↦ ⟨Q.carrier.place z.1,
          (Q.mem_ambientReplacementBlock_iff s hk r).2 ⟨z.1, z.2, rfl⟩⟩
      invFun := fun x ↦ ⟨Q.carrier.unplace x.1, by
        obtain ⟨z, hz, hzx⟩ :=
          (Q.mem_ambientReplacementBlock_iff s hk r).1 x.2
        have hz' : z = Q.carrier.unplace x.1 := by
          apply Q.carrier.place_injective
          simpa using hzx
        simpa [hz'] using hz⟩
      left_inv := fun z ↦ by ext; simp
      right_inv := fun x ↦ by ext; simp }
  let iso : diameterGraph (s.replacementBlock hk r) ≃g
      diameterGraph (Q.ambientReplacementBlock s hk r) :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        change dist (Q.carrier.place x.1) (Q.carrier.place y.1) = 1 ↔
          dist x.1 y.1 = 1
        rw [Q.carrier.dist_place] }
  exact iso.card_edgeFinset_eq.symm

lemma diameterPairCount_ambientReplacementBlock_ge
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    k + 1 ≤ diameterPairCount (Q.ambientReplacementBlock s hk r) := by
  rw [Q.diameterPairCount_ambientReplacementBlock s hk r]
  exact s.diameterPairCount_replacementBlock_ge hk r

def NoPoles : Prop :=
  Q.carrier.place (positivePole p) ∉ A ∧
    Q.carrier.place (negativePole p) ∉ A

lemma pole_not_mem_of_noPoles (s : PoleSign) (hno : Q.NoPoles) :
    Q.carrier.place (s.pole p) ∉ A := by
  cases s
  · exact hno.1
  · exact hno.2

lemma place_quarterEquatorPoint_ne_outside
    {k : ℕ} (hk : 2 ≤ k) (r : Fin p) (a : Fin k)
    {x : Point d} (hx : x ∈ Q.outsidePoints r) :
    Q.carrier.place (quarterEquatorPoint hk r a) ≠ x := by
  intro heq
  obtain ⟨hxA, hxpart⟩ := (Q.mem_outsidePoints_iff r).mp hx
  let xA : {x : Point d // x ∈ A} := ⟨x, hxA⟩
  have hxsphere : x ∈ Q.carrier.sphere (Q.part xA) := Q.mem_sphere xA
  have hqe : Q.carrier.place (quarterEquatorPoint hk r a) ∈
      Q.carrier.equator r :=
    ⟨quarterEquatorPoint hk r a, quarterEquatorPoint_onEquator hk r a, rfl⟩
  have hdist := Q.carrier.dist_eq_one_of_mem_equator_mem_sphere
    (show r ≠ Q.part xA by simpa [xA] using hxpart.symm) hqe hxsphere
  rw [heq] at hdist
  simpa using hdist

lemma outsidePoints_disjoint_ambientReplacementBlock
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p)
    (hno : Q.NoPoles) :
    Disjoint (Q.outsidePoints r) (Q.ambientReplacementBlock s hk r) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxout hxblock
  obtain ⟨z, hz, rfl⟩ := (Q.mem_ambientReplacementBlock_iff s hk r).mp hxblock
  rcases (s.mem_replacementBlock_iff hk r).mp hz with rfl | hzeq
  · obtain ⟨hxA, -⟩ := (Q.mem_outsidePoints_iff r).mp hxout
    exact Q.pole_not_mem_of_noPoles s hno hxA
  · rw [quarterEquatorFinset] at hzeq
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hzeq
    exact Q.place_quarterEquatorPoint_ne_outside hk r a hxout rfl

def replacementSet (s : PoleSign) {k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) : Finset (Point d) :=
  Q.outsidePoints r ∪ Q.ambientReplacementBlock s hk r

lemma card_replacementSet (s : PoleSign) {k : ℕ} (hk : 2 ≤ k)
    (r : Fin p) (hno : Q.NoPoles) :
    (Q.replacementSet s hk r).card + AssignmentIntegration.partCard Q r =
      A.card + (k + 1) := by
  have hcard := Q.card_outsidePoints_add_partCard r
  rw [replacementSet, Finset.card_union_of_disjoint
    (Q.outsidePoints_disjoint_ambientReplacementBlock s hk r hno),
    Q.card_ambientReplacementBlock]
  omega

lemma ambientReplacementBlock_pairwise_dist_le_one
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p) :
    ∀ x ∈ Q.ambientReplacementBlock s hk r,
      ∀ y ∈ Q.ambientReplacementBlock s hk r, dist x y ≤ 1 := by
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := (Q.mem_ambientReplacementBlock_iff s hk r).mp hx
  obtain ⟨w, hw, rfl⟩ := (Q.mem_ambientReplacementBlock_iff s hk r).mp hy
  rw [Q.carrier.dist_place]
  exact (isDiameterOne_iff.mp (s.replacementBlock_isDiameterOne hk r)).1 z hz w hw

lemma dist_ambientReplacementBlock_outside_le_one
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p)
    (hsafe : ∀ x : {x : Point d // x ∈ A}, Q.part x ≠ r →
      dist (Q.carrier.place (s.pole p)) x.1 ≤ 1)
    {y x : Point d} (hy : y ∈ Q.ambientReplacementBlock s hk r)
    (hx : x ∈ Q.outsidePoints r) : dist y x ≤ 1 := by
  obtain ⟨z, hz, rfl⟩ := (Q.mem_ambientReplacementBlock_iff s hk r).mp hy
  obtain ⟨hxA, hxpart⟩ := (Q.mem_outsidePoints_iff r).mp hx
  let xA : {x : Point d // x ∈ A} := ⟨x, hxA⟩
  rcases (s.mem_replacementBlock_iff hk r).mp hz with rfl | hzeq
  · exact hsafe xA (by simpa [xA] using hxpart)
  · rw [quarterEquatorFinset] at hzeq
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hzeq
    have hqe : Q.carrier.place (quarterEquatorPoint hk r a) ∈
        Q.carrier.equator r :=
      ⟨quarterEquatorPoint hk r a, quarterEquatorPoint_onEquator hk r a, rfl⟩
    have hxsphere : x ∈ Q.carrier.sphere (Q.part xA) := Q.mem_sphere xA
    exact (Q.carrier.dist_eq_one_of_mem_equator_mem_sphere
      (show r ≠ Q.part xA by simpa [xA] using hxpart.symm) hqe hxsphere).le

lemma replacementSet_pairwise_dist_le_one
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (hsafe : ∀ x : {x : Point d // x ∈ A}, Q.part x ≠ r →
      dist (Q.carrier.place (s.pole p)) x.1 ≤ 1) :
    ∀ x ∈ Q.replacementSet s hk r,
      ∀ y ∈ Q.replacementSet s hk r, dist x y ≤ 1 := by
  intro x hx y hy
  rw [replacementSet] at hx hy
  rcases Finset.mem_union.mp hx with hxout | hxblock <;>
    rcases Finset.mem_union.mp hy with hyout | hyblock
  · obtain ⟨hxA, -⟩ := (Q.mem_outsidePoints_iff r).mp hxout
    obtain ⟨hyA, -⟩ := (Q.mem_outsidePoints_iff r).mp hyout
    exact hdiam x hxA y hyA
  · simpa [dist_comm] using
      Q.dist_ambientReplacementBlock_outside_le_one s hk r hsafe hyblock hxout
  · exact Q.dist_ambientReplacementBlock_outside_le_one s hk r hsafe hxblock hyout
  · exact Q.ambientReplacementBlock_pairwise_dist_le_one s hk r x hxblock y hyblock

lemma replacementSet_isDiameterOne
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (hsafe : ∀ x : {x : Point d // x ∈ A}, Q.part x ≠ r →
      dist (Q.carrier.place (s.pole p)) x.1 ≤ 1) :
    IsDiameterOne (Q.replacementSet s hk r) := by
  rw [isDiameterOne_iff]
  refine ⟨Q.replacementSet_pairwise_dist_le_one s hk r hdiam hsafe, ?_⟩
  let q := quarterEquatorPoint hk r (quarterFirst hk)
  refine ⟨Q.carrier.place (s.pole p), ?_, Q.carrier.place q, ?_, ?_⟩
  · rw [replacementSet, Finset.mem_union]
    exact Or.inr ((Q.mem_ambientReplacementBlock_iff s hk r).2
      ⟨s.pole p, s.pole_mem_replacementBlock hk r, rfl⟩)
  · rw [replacementSet, Finset.mem_union]
    apply Or.inr
    rw [Q.mem_ambientReplacementBlock_iff]
    refine ⟨q, ?_, rfl⟩
    rw [s.mem_replacementBlock_iff]
    exact Or.inr (mem_quarterEquatorFinset hk r (quarterFirst hk))
  · rw [Q.carrier.dist_place]
    exact s.dist_pole_quarterEquatorPoint hk r (quarterFirst hk)

lemma diameterPairCount_replacementSet_lower
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p)
    (hno : Q.NoPoles) :
    diameterPairCount (Q.outsidePoints r) +
        (Q.replacementCrossPairs s hk r).card + (k + 1) ≤
      diameterPairCount (Q.replacementSet s hk r) := by
  have hdecomp := diameterPairCount_union_of_disjoint
    (Q.outsidePoints r) (Q.ambientReplacementBlock s hk r)
    (Q.outsidePoints_disjoint_ambientReplacementBlock s hk r hno)
  have hcross := Q.card_ambient_cross_filter_eq_replacementCrossPairs s hk r
  have hlocal := Q.diameterPairCount_ambientReplacementBlock_ge s hk r
  rw [← replacementSet] at hdecomp
  rw [hcross] at hdecomp
  omega

lemma diameterPairCount_replacementSet_gain
    (s : PoleSign) {k : ℕ} (hk : 2 ≤ k) (r : Fin p)
    (hno : Q.NoPoles) (hr : 0 < Q.offCount r)
    (hcard : k + 1 = AssignmentIntegration.partCard Q r)
    (hinside : Q.localInsideCount r ≤ AssignmentIntegration.partCard Q r) :
    diameterPairCount A +
        (AssignmentIntegration.partCard Q r - Q.localInsideCount r) +
        (Q.offCount r - 1) * otherOffTotal Q.offCount r ≤
      diameterPairCount (Q.replacementSet s hk r) := by
  have hold := Q.old_edge_decomposition_add_cross_defect_from r
  have hnew := Q.diameterPairCount_replacementSet_lower s hk r hno
  have hcross := Q.card_replacementCrossPairs_add_off s hk r
  rw [Q.outsideOffCount_eq_otherOffTotal r, hcard] at hcross
  have hoffmul : Q.offCount r * otherOffTotal Q.offCount r =
      otherOffTotal Q.offCount r +
        (Q.offCount r - 1) * otherOffTotal Q.offCount r := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    rw [ht, Nat.succ_eq_add_one, Nat.add_one_sub_one, Nat.add_mul, one_mul]
    omega
  rw [hcard] at hnew
  omega

/-- Signed version used by the replacement-block construction. -/
theorem exists_safePoleSign_outside
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (r : Fin p) (hr : 0 < Q.offCount r) :
    ∃ s : PoleSign,
      ∀ x : {x : Point d // x ∈ A}, Q.part x ≠ r →
        dist (Q.carrier.place (s.pole p)) x.1 ≤ 1 := by
  rcases Q.exists_common_axis_sign_outside hdiam r hr with hpos | hneg
  · refine ⟨PoleSign.positive, ?_⟩
    intro x hxr
    have hx := dist_positivePole_le_one_of_onSphere_of_axis_nonneg
      (r := r) (i := Q.part x) hxr.symm (Q.unplace_onSphere x) (hpos x hxr)
    calc
      dist (Q.carrier.place (PoleSign.positive.pole p)) x.1 =
          dist (Q.carrier.place (positivePole p)) x.1 := by rfl
      _ = dist (positivePole p) (Q.carrier.unplace x.1) := by
        rw [← Q.carrier.dist_place]
        simp
      _ ≤ 1 := hx
  · refine ⟨PoleSign.negative, ?_⟩
    intro x hxr
    have hx := dist_negativePole_le_one_of_onSphere_of_axis_nonpos
      (r := r) (i := Q.part x) hxr.symm (Q.unplace_onSphere x) (hneg x hxr)
    calc
      dist (Q.carrier.place (PoleSign.negative.pole p)) x.1 =
          dist (Q.carrier.place (negativePole p)) x.1 := by rfl
      _ = dist (negativePole p) (Q.carrier.unplace x.1) := by
        rw [← Q.carrier.dist_place]
        simp
      _ ≤ 1 := hx

/-- The actual same-cardinality, diameter-one no-pole replacement set.
The edge-count gain is handled separately below. -/
theorem exists_replacementSet_same_card_isDiameterOne
    (hA : IsDiameterOne A) (hno : Q.NoPoles)
    (r : Fin p) (hr : 0 < Q.offCount r)
    (hsize : 3 ≤ AssignmentIntegration.partCard Q r) :
    ∃ A' : Finset (Point d), A'.card = A.card ∧ IsDiameterOne A' := by
  let k := AssignmentIntegration.partCard Q r - 1
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkcard : k + 1 = AssignmentIntegration.partCard Q r := by
    dsimp [k]
    omega
  have hdiam := (isDiameterOne_iff.mp hA).1
  obtain ⟨s, hsafe⟩ := Q.exists_safePoleSign_outside hdiam r hr
  refine ⟨Q.replacementSet s hk r, ?_,
    Q.replacementSet_isDiameterOne s hk r hdiam hsafe⟩
  have hcard := Q.card_replacementSet s hk r hno
  omega

/-- The corrected no-pole replacement principle, with the exact edge gain.

The new block has the old part's cardinality, consists of a safe common pole
and points on the component equator, and gains at least the old local deficit
plus `(offCount r - 1) * otherOffTotal`. -/
theorem exists_replacementSet_with_gain
    (hA : IsDiameterOne A) (hno : Q.NoPoles)
    (r : Fin p) (hr : 0 < Q.offCount r)
    (hsize : 3 ≤ AssignmentIntegration.partCard Q r)
    (hinside : Q.localInsideCount r ≤ AssignmentIntegration.partCard Q r) :
    ∃ A' : Finset (Point d),
      A'.card = A.card ∧ IsDiameterOne A' ∧
        diameterPairCount A +
            (AssignmentIntegration.partCard Q r - Q.localInsideCount r) +
            (Q.offCount r - 1) * otherOffTotal Q.offCount r ≤
          diameterPairCount A' := by
  let k := AssignmentIntegration.partCard Q r - 1
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkcard : k + 1 = AssignmentIntegration.partCard Q r := by
    dsimp [k]
    omega
  have hdiam := (isDiameterOne_iff.mp hA).1
  obtain ⟨s, hsafe⟩ := Q.exists_safePoleSign_outside hdiam r hr
  refine ⟨Q.replacementSet s hk r, ?_,
    Q.replacementSet_isDiameterOne s hk r hdiam hsafe,
    Q.diameterPairCount_replacementSet_gain s hk r hno hr hkcard hinside⟩
  have hcard := Q.card_replacementSet s hk r hno
  omega

/-- Uniform form of `exists_replacementSet_with_gain`, suitable for the
finite numerical no-pole classifier. -/
theorem noPole_replacementGeometry
    (hA : IsDiameterOne A) (hno : Q.NoPoles)
    (hlocal : ∀ r : Fin p,
      Q.localInsideCount r ≤ AssignmentIntegration.partCard Q r) :
    ∀ r : Fin p, 0 < Q.offCount r →
      3 ≤ AssignmentIntegration.partCard Q r →
      ∃ A' : Finset (Point d),
        A'.card = A.card ∧ IsDiameterOne A' ∧
          diameterPairCount A +
              (AssignmentIntegration.partCard Q r - Q.localInsideCount r) +
              (Q.offCount r - 1) * otherOffTotal Q.offCount r ≤
            diameterPairCount A' := by
  intro r hr hsize
  exact Q.exists_replacementSet_with_gain hA hno r hr hsize (hlocal r)
end Assignment

namespace AssignmentIntegration

/-- The stable-partition classifier with the geometric no-pole replacement
hypothesis discharged by `Assignment.exists_replacementSet_with_gain`. -/
theorem Assignment.isStrongCarrierSet_of_extremal_noPoles
    {d p : ℕ} {A : Finset (Point d)}
    (Q : Assignment (p := p) A) (hp : 0 < p)
    {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hagrees : AgreesOnRetained Q P)
    (hlarge : ∀ _i : Fin p,
      (3 : ℝ) + epsilon * A.card < (A.card : ℝ) / p)
    (hA : IsDiameterOne A) (hno : Q.NoPoles)
    (hedges : diameterPairCount A + crossDefect Q.offCount =
      pairProductSum (partCard Q) (partCard Q) +
        ∑ i, Q.localInsideCount i)
    (hinside : ∀ i, Q.localInsideCount i ≤ partCard Q i)
    (hlocalSmall : ∀ i, Q.offCount i ≤ 1 → Q.localInsideCount i ≤ 3)
    (hAextremal : diameterPairCount A = f d A.card)
    (hlower : turanNumber p A.card + ceilQuot A.card p + (p - 1) ≤
      diameterPairCount A)
    (hcorrection : 3 * p < ceilQuot A.card p + (p - 1)) :
    IsStrongCarrierSet (p := p) A := by
  apply Assignment.isStrongCarrierSet_of_extremal_noPole_replacements
    Q hp P hagrees hlarge Q.localInsideCount hedges hinside hlocalSmall
      hAextremal _ hlower hcorrection
  intro r hr hsize
  exact Q.exists_replacementSet_with_gain hA hno r (by omega) hsize (hinside r)

/-- Large-cardinality form of
`Assignment.isStrongCarrierSet_of_extremal_noPoles`. -/
theorem Assignment.isStrongCarrierSet_of_extremal_noPoles_of_large
    {d p : ℕ} {A : Finset (Point d)}
    (Q : Assignment (p := p) A) (hp : 0 < p)
    {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hagrees : AgreesOnRetained Q P)
    (hlarge : ∀ _i : Fin p,
      (3 : ℝ) + epsilon * A.card < (A.card : ℝ) / p)
    (hA : IsDiameterOne A) (hno : Q.NoPoles)
    (hedges : diameterPairCount A + crossDefect Q.offCount =
      pairProductSum (partCard Q) (partCard Q) +
        ∑ i, Q.localInsideCount i)
    (hinside : ∀ i, Q.localInsideCount i ≤ partCard Q i)
    (hlocalSmall : ∀ i, Q.offCount i ≤ 1 → Q.localInsideCount i ≤ 3)
    (hAextremal : diameterPairCount A = f d A.card)
    (hlower : turanNumber p A.card + ceilQuot A.card p + (p - 1) ≤
      diameterPairCount A)
    (hn : p * (2 * p + 1) < A.card) :
    IsStrongCarrierSet (p := p) A := by
  apply Assignment.isStrongCarrierSet_of_extremal_noPoles
    Q hp P hagrees hlarge hA hno hedges hinside hlocalSmall hAextremal hlower
  exact three_mul_lt_ceilQuot_add_pred_of_large hp hn

end AssignmentIntegration

end

end Erdos223.CarrierOdd

#print axioms Erdos223.CarrierOdd.Assignment.exists_replacementSet_with_gain
#print axioms Erdos223.CarrierOdd.Assignment.noPole_replacementGeometry
#print axioms Erdos223.CarrierOdd.AssignmentIntegration.Assignment.isStrongCarrierSet_of_extremal_noPoles_of_large
