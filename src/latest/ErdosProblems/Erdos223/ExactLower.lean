/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos223.Lenz
import ErdosProblems.Erdos223.LenzOptimization
import ErdosProblems.Erdos223.FourLowerConstruction
import ErdosProblems.Erdos223.FiveLowerConstruction
import ErdosProblems.Erdos223.OddCosphericalConstruction

/-!
# Exact lower constructions for Erdős Problem 223

This file supplies the endpoint-enhanced Lenz configurations used for the
lower halves of Swanepoel's eventual exact formula.  The points in every
circle carrier lie in a closed quadrant of the circle of radius `1 / √2`.
The two endpoints of that quadrant give one internal diameter, while all
cross-carrier pairs remain diameters.

The odd-dimensional construction uses the spare coordinate for a pole.  In
the distinguished carrier, the pole is orthogonal to every equatorial point;
this gives exactly the linear correction occurring in the odd formula.
-/

open scoped BigOperators

namespace Erdos223

noncomputable section

namespace ExactLower

/-! ## A reusable dimension-five join bound -/

/-- A cospherical diameter-one block in three dimensions and a centered
circle block in two dimensions combine orthogonally to give a genuine
diameter-one configuration in five dimensions.  This is the order-theoretic
wrapper around `FiveLowerConstruction.combined_exact_count_le`; the concrete
Swanepoel blocks are supplied below. -/
theorem five_lower_of_blocks
    {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {r s : ℝ}
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hcircle : ∀ y ∈ B, dist y 0 = s)
    (hradii : r ^ 2 + s ^ 2 = 1) (hs : 0 < s)
    (hA : IsDiameterOne A) (hB : IsDiameterOne B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) :
    diameterPairCount A + A.card * B.card + diameterPairCount B ≤
      f 5 (A.card + B.card) := by
  apply (FiveLowerConstruction.combined_exact_count_le hsphere hcircle hradii hs).trans
  apply diameterPairCount_le_f
  · exact FiveLowerConstruction.card_combinedConfiguration hcircle hs
  · exact FiveLowerConstruction.isDiameterOne_combinedConfiguration
      hsphere hcircle hradii hA hB hAn hBn

/-- The exact five-dimensional Lenz construction.  The three nonzero
residue classes use two balanced local blocks.  When `n` is divisible by
four, Swanepoel's odd cospherical `2m-2` construction supplies the larger
three-dimensional block and a large-radius circle supplies the remaining
internal diameter. -/
theorem five_exact_lower {n : ℕ} (hn : 16 ≤ n) :
    turanNumber 2 n + n ≤ f 5 n := by
  by_cases hmod : n % 4 = 0
  · apply FiveLowerConstruction.five_exact_lower_of_mod_zero_of_odd_sphere hn hmod
    have hm : 7 ≤ n / 2 + 1 := by omega
    have hodd : Odd (n / 2 + 1) := ⟨n / 4, by omega⟩
    exact OddCosphericalConstruction.exists_odd_cospherical_configuration
      (n / 2 + 1) hm hodd
  · exact FiveLowerConstruction.five_exact_lower_of_mod_ne_zero (by omega) hmod

/-! ## The exact four-dimensional construction -/

/-- The variable-radius two-circle construction attains the exact
four-dimensional Lenz value.  The four residue classes select respectively
the splits `(2k+1,2k-1)`, `(2k+1,2k)`, `(2k+1,2k+1)`, and
`(2k+1,2k+2)`. -/
theorem four_exact_lower {n : ℕ} (hn : 8 ≤ n) :
    turanNumber 2 n + ceilQuot n 2 + fourCorrection n ≤ f 4 n :=
  Erdos223.four_exact_lower hn

/-! ## A closed-quadrant parametrization with two designated endpoints -/

/-- The first two levels in each residue class are sent to the two endpoints
of a quadrant.  Later vertices use distinct parameters strictly between the
endpoints. -/
def parameter {n : ℕ} (p : ℕ) (v : Fin n) : ℝ :=
  if (v : ℕ) < p then 0
  else if (v : ℕ) < 2 * p then 1
  else ((v : ℕ) + 1 : ℝ) / (n + 1 : ℝ)

lemma parameter_nonneg {n : ℕ} (p : ℕ) (v : Fin n) :
    0 ≤ parameter p v := by
  unfold parameter
  split_ifs
  · norm_num
  · norm_num
  · positivity

lemma parameter_le_one {n : ℕ} (p : ℕ) (v : Fin n) :
    parameter p v ≤ 1 := by
  unfold parameter
  split_ifs
  · norm_num
  · norm_num
  · rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
    exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt v.isLt) 1

lemma parameter_sq_le_one {n : ℕ} (p : ℕ) (v : Fin n) :
    parameter p v ^ 2 ≤ 1 := by
  have h0 := parameter_nonneg p v
  have h1 := parameter_le_one p v
  nlinarith [sq_nonneg (parameter p v - 1)]

lemma parameter_eq_zero_of_val_lt {n p : ℕ} {v : Fin n} (hv : (v : ℕ) < p) :
    parameter p v = 0 := by simp [parameter, hv]

lemma parameter_eq_one_of_level_one {n p : ℕ} {v : Fin n}
    (hpv : p ≤ (v : ℕ)) (hv : (v : ℕ) < 2 * p) :
    parameter p v = 1 := by simp [parameter, not_lt.mpr hpv, hv]

lemma parameter_pos_of_two_mul_le_val {n p : ℕ} {v : Fin n}
    (hv : 2 * p ≤ (v : ℕ)) : 0 < parameter p v := by
  simp [parameter, not_lt.mpr (le_trans (Nat.le_mul_of_pos_left p (by omega)) hv),
    not_lt.mpr hv]
  positivity

lemma parameter_lt_one_of_two_mul_le_val {n p : ℕ} {v : Fin n}
    (hv : 2 * p ≤ (v : ℕ)) : parameter p v < 1 := by
  simp [parameter, not_lt.mpr (le_trans (Nat.le_mul_of_pos_left p (by omega)) hv),
    not_lt.mpr hv]
  rw [div_lt_one (by positivity : (0 : ℝ) < n + 1)]
  exact_mod_cast Nat.add_lt_add_right v.isLt 1

lemma parameter_injective_of_mod_eq {n p : ℕ} (hp : 0 < p) {v w : Fin n}
    (hmod : (v : ℕ) % p = (w : ℕ) % p)
    (hpar : parameter p v = parameter p w) : v = w := by
  by_cases hv0 : (v : ℕ) < p
  · have hpv : parameter p v = 0 := parameter_eq_zero_of_val_lt hv0
    have hpw : parameter p w = 0 := hpar.symm.trans hpv
    have hw0 : (w : ℕ) < p := by
      by_contra hw0
      by_cases hw1 : (w : ℕ) < 2 * p
      · rw [parameter_eq_one_of_level_one (not_lt.mp hw0) hw1] at hpw
        norm_num at hpw
      · exact (parameter_pos_of_two_mul_le_val (not_lt.mp hw1)).ne' hpw
    apply Fin.ext
    rwa [Nat.mod_eq_of_lt hv0, Nat.mod_eq_of_lt hw0] at hmod
  · by_cases hv1 : (v : ℕ) < 2 * p
    · have hpv : p ≤ (v : ℕ) := not_lt.mp hv0
      have hpv' : parameter p v = 1 := parameter_eq_one_of_level_one hpv hv1
      have hpw' : parameter p w = 1 := hpar.symm.trans hpv'
      have hw0 : ¬ (w : ℕ) < p := by
        intro hw0
        rw [parameter_eq_zero_of_val_lt hw0] at hpw'
        norm_num at hpw'
      have hw1 : (w : ℕ) < 2 * p := by
        by_contra hw1
        exact (parameter_lt_one_of_two_mul_le_val (not_lt.mp hw1)).ne hpw'
      apply Fin.ext
      have hvsub : (v : ℕ) - p < p := by omega
      have hwsub : (w : ℕ) - p < p := by omega
      rw [Nat.mod_eq_sub_mod hpv, Nat.mod_eq_of_lt hvsub,
        Nat.mod_eq_sub_mod (not_lt.mp hw0), Nat.mod_eq_of_lt hwsub] at hmod
      omega
    · have hv2 : 2 * p ≤ (v : ℕ) := not_lt.mp hv1
      have hw0 : ¬ (w : ℕ) < p := by
        intro hw0
        have := parameter_pos_of_two_mul_le_val hv2
        rw [hpar, parameter_eq_zero_of_val_lt hw0] at this
        norm_num at this
      have hw1 : ¬ (w : ℕ) < 2 * p := by
        intro hw1
        have := parameter_lt_one_of_two_mul_le_val hv2
        rw [hpar, parameter_eq_one_of_level_one (not_lt.mp hw0) hw1] at this
        norm_num at this
      have hden : (n + 1 : ℝ) ≠ 0 := by positivity
      have hfrac : ((v : ℕ) + 1 : ℝ) / (n + 1 : ℝ) =
          ((w : ℕ) + 1 : ℝ) / (n + 1 : ℝ) := by
        simpa [parameter, hv0, hv1, hw0, hw1] using hpar
      have hcast : ((v : ℕ) + 1 : ℝ) = ((w : ℕ) + 1 : ℝ) :=
        (div_left_inj' hden).mp hfrac
      apply Fin.ext
      have hnat : (v : ℕ) + 1 = (w : ℕ) + 1 := by exact_mod_cast hcast
      omega

/-! ## Even-dimensional endpoint-enhanced carriers -/

/-- The endpoint-enhanced point in the coordinate plane selected by its
residue class. -/
def evenPoint {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) (v : Fin n) :
    Point d :=
  EuclideanSpace.single (Lenz.evenIndex hdp (Lenz.part hp v))
      (Lenz.firstCoordinate (parameter p v)) +
    EuclideanSpace.single (Lenz.oddIndex hdp (Lenz.part hp v))
      (Lenz.secondCoordinate (parameter p v))

lemma evenPoint_apply_odd {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v : Fin n) :
    evenPoint hdp hp v (Lenz.oddIndex hdp (Lenz.part hp v)) =
      Lenz.secondCoordinate (parameter p v) := by
  simp [evenPoint, Lenz.oddIndex_ne_evenIndex]

lemma inner_evenPoint_evenPoint_same_part {d n p : ℕ}
    (hdp : 2 * p ≤ d) (hp : 0 < p) {v w : Fin n}
    (hpart : Lenz.part hp v = Lenz.part hp w) :
    inner ℝ (evenPoint hdp hp v) (evenPoint hdp hp w) =
      Lenz.firstCoordinate (parameter p v) * Lenz.firstCoordinate (parameter p w) +
        Lenz.secondCoordinate (parameter p v) * Lenz.secondCoordinate (parameter p w) := by
  simp [evenPoint, hpart, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, Lenz.evenIndex_ne_oddIndex,
    Lenz.oddIndex_ne_evenIndex]

lemma inner_evenPoint_evenPoint_of_ne_part {d n p : ℕ}
    (hdp : 2 * p ≤ d) (hp : 0 < p) {v w : Fin n}
    (hpart : Lenz.part hp v ≠ Lenz.part hp w) :
    inner ℝ (evenPoint hdp hp v) (evenPoint hdp hp w) = 0 := by
  have hee : Lenz.evenIndex hdp (Lenz.part hp v) ≠
      Lenz.evenIndex hdp (Lenz.part hp w) :=
    fun h ↦ hpart (Lenz.evenIndex_injective hdp h)
  have hoo : Lenz.oddIndex hdp (Lenz.part hp v) ≠
      Lenz.oddIndex hdp (Lenz.part hp w) :=
    fun h ↦ hpart (Lenz.oddIndex_injective hdp h)
  simp [evenPoint, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, hee, hoo,
    Lenz.evenIndex_ne_oddIndex, Lenz.oddIndex_ne_evenIndex]

lemma inner_evenPoint_self {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v : Fin n) : inner ℝ (evenPoint hdp hp v) (evenPoint hdp hp v) = 1 / 2 := by
  rw [inner_evenPoint_evenPoint_same_part hdp hp rfl]
  simpa [pow_two] using Lenz.coordinates_sq_add (parameter_sq_le_one p v)

lemma dist_evenPoint_sq {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v w : Fin n) :
    dist (evenPoint hdp hp v) (evenPoint hdp hp w) ^ 2 =
      1 - 2 * inner ℝ (evenPoint hdp hp v) (evenPoint hdp hp w) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [inner_evenPoint_self hdp hp v, inner_evenPoint_self hdp hp w]
  rw [show inner ℝ (evenPoint hdp hp w) (evenPoint hdp hp v) =
      inner ℝ (evenPoint hdp hp v) (evenPoint hdp hp w) from real_inner_comm _ _]
  ring

lemma inner_evenPoint_nonneg {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v w : Fin n) : 0 ≤ inner ℝ (evenPoint hdp hp v) (evenPoint hdp hp w) := by
  by_cases hpart : Lenz.part hp v = Lenz.part hp w
  · rw [inner_evenPoint_evenPoint_same_part hdp hp hpart]
    exact add_nonneg
      (mul_nonneg (Lenz.firstCoordinate_nonneg _) (Lenz.firstCoordinate_nonneg _))
      (mul_nonneg (Lenz.secondCoordinate_nonneg (parameter_nonneg _ _))
        (Lenz.secondCoordinate_nonneg (parameter_nonneg _ _)))
  · rw [inner_evenPoint_evenPoint_of_ne_part hdp hp hpart]

lemma dist_evenPoint_le_one {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v w : Fin n) : dist (evenPoint hdp hp v) (evenPoint hdp hp w) ≤ 1 := by
  have hsq := dist_evenPoint_sq hdp hp v w
  have hi := inner_evenPoint_nonneg hdp hp v w
  have hd : 0 ≤ dist (evenPoint hdp hp v) (evenPoint hdp hp w) := dist_nonneg
  nlinarith

lemma dist_evenPoint_eq_one_of_ne_part {d n p : ℕ}
    (hdp : 2 * p ≤ d) (hp : 0 < p) {v w : Fin n}
    (hpart : Lenz.part hp v ≠ Lenz.part hp w) :
    dist (evenPoint hdp hp v) (evenPoint hdp hp w) = 1 := by
  have hsq := dist_evenPoint_sq hdp hp v w
  rw [inner_evenPoint_evenPoint_of_ne_part hdp hp hpart] at hsq
  have hd : 0 ≤ dist (evenPoint hdp hp v) (evenPoint hdp hp w) := dist_nonneg
  nlinarith

lemma dist_evenPoint_eq_one_of_parameters_zero_one {d n p : ℕ}
    (hdp : 2 * p ≤ d) (hp : 0 < p) {v w : Fin n}
    (hpart : Lenz.part hp v = Lenz.part hp w)
    (hv : parameter p v = 0) (hw : parameter p w = 1) :
    dist (evenPoint hdp hp v) (evenPoint hdp hp w) = 1 := by
  have hsq := dist_evenPoint_sq hdp hp v w
  rw [inner_evenPoint_evenPoint_same_part hdp hp hpart, hv, hw] at hsq
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  simp [Lenz.firstCoordinate, Lenz.secondCoordinate, hsqrt] at hsq
  rcases hsq with h | h
  · exact h
  · have hd : 0 ≤ dist (evenPoint hdp hp v) (evenPoint hdp hp w) := dist_nonneg
    linarith

lemma evenPoint_injective {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    Function.Injective (@evenPoint d n p hdp hp) := by
  intro v w hvw
  have hinner : inner ℝ (evenPoint hdp hp v) (evenPoint hdp hp w) = 1 / 2 := by
    rw [hvw]
    exact inner_evenPoint_self hdp hp w
  have hpart : Lenz.part hp v = Lenz.part hp w := by
    by_contra hne
    rw [inner_evenPoint_evenPoint_of_ne_part hdp hp hne] at hinner
    norm_num at hinner
  have hcoord := congrArg
    (fun z : Point d ↦ z (Lenz.oddIndex hdp (Lenz.part hp v))) hvw
  rw [evenPoint_apply_odd hdp hp v] at hcoord
  rw [hpart, evenPoint_apply_odd hdp hp w] at hcoord
  apply parameter_injective_of_mod_eq hp
  · simpa [Lenz.part, Fin.ext_iff] using congrArg Fin.val hpart
  · exact Lenz.secondCoordinate_injective hcoord

/-- The enhanced even Lenz configuration. -/
def evenConfiguration {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    Finset (Point d) :=
  Finset.univ.image (fun v : Fin n ↦ evenPoint hdp hp v)

lemma card_evenConfiguration {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    (evenConfiguration (n := n) hdp hp).card = n := by
  rw [evenConfiguration,
    Finset.card_image_iff.mpr (evenPoint_injective hdp hp).injOn]
  simp

lemma mem_evenConfiguration {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v : Fin n) : evenPoint hdp hp v ∈ evenConfiguration (n := n) hdp hp := by
  simp [evenConfiguration]

lemma isDiameterOne_evenConfiguration {d n p : ℕ}
    (hdp : 2 * p ≤ d) (hp : 0 < p) (hp2 : 2 ≤ p) (hn : 2 * p ≤ n) :
    IsDiameterOne (evenConfiguration (n := n) hdp hp) := by
  rw [isDiameterOne_iff]
  refine ⟨?_, ?_⟩
  · simp only [evenConfiguration, Finset.mem_image, Finset.mem_univ, true_and]
    rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩
    exact dist_evenPoint_le_one hdp hp v w
  · let v : Fin n := ⟨0, by omega⟩
    let w : Fin n := ⟨1, by omega⟩
    refine ⟨evenPoint hdp hp v, mem_evenConfiguration hdp hp v,
      evenPoint hdp hp w, mem_evenConfiguration hdp hp w, ?_⟩
    apply dist_evenPoint_eq_one_of_ne_part hdp hp
    rw [Lenz.part_ne_iff hp]
    dsimp [v, w]
    rw [Nat.mod_eq_of_lt (by omega : 1 < p)]
    norm_num

/-! ## Counting the cross edges and one internal edge per circle -/

def firstVertex {n p : ℕ} (hn : 2 * p ≤ n) (i : Fin p) : Fin n :=
  ⟨i, by omega⟩

def secondVertex {n p : ℕ} (hn : 2 * p ≤ n) (i : Fin p) : Fin n :=
  ⟨p + i, by omega⟩

lemma firstVertex_val {n p : ℕ} (hn : 2 * p ≤ n) (i : Fin p) :
    (firstVertex hn i : ℕ) = i := rfl

lemma secondVertex_val {n p : ℕ} (hn : 2 * p ≤ n) (i : Fin p) :
    (secondVertex hn i : ℕ) = p + i := rfl

lemma firstVertex_ne_secondVertex {n p : ℕ} (hn : 2 * p ≤ n) (i : Fin p) :
    firstVertex hn i ≠ secondVertex hn i := by
  intro h
  have := congrArg Fin.val h
  dsimp [firstVertex, secondVertex] at this
  omega

def evenVertexEmbedding {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    Fin n ↪ {x // x ∈ evenConfiguration (n := n) hdp hp} where
  toFun v := ⟨evenPoint hdp hp v, mem_evenConfiguration hdp hp v⟩
  inj' _ _ h := evenPoint_injective hdp hp (Subtype.ext_iff.mp h)

def evenCountDomain (n p : ℕ) : Finset (Sym2 (Fin n) ⊕ Fin p) :=
  (SimpleGraph.turanGraph n p).edgeFinset.disjSum Finset.univ

lemma card_evenCountDomain (n p : ℕ) :
    (evenCountDomain n p).card = turanNumber p n + p := by
  simp [evenCountDomain, turanNumber]

def evenCountMap {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (hn : 2 * p ≤ n) :
    Sym2 (Fin n) ⊕ Fin p →
      Sym2 {x // x ∈ evenConfiguration (n := n) hdp hp}
  | .inl e => Sym2.map (evenVertexEmbedding hdp hp) e
  | .inr i => s(evenVertexEmbedding hdp hp (firstVertex hn i),
      evenVertexEmbedding hdp hp (secondVertex hn i))

-- The injection needed below is only required on the disjoint counting domain.
lemma evenCountMap_injOn {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (hn : 2 * p ≤ n) :
    Set.InjOn (evenCountMap hdp hp hn) (evenCountDomain n p) := by
  intro a ha b hb hab
  cases a with
  | inl e =>
      cases b with
      | inl f =>
          congr 1
          exact Sym2.map.injective (evenVertexEmbedding hdp hp).injective hab
      | inr j =>
          exfalso
          have he : e ∈ (SimpleGraph.turanGraph n p).edgeFinset := by
            simpa [evenCountDomain] using ha
          have hpre : e = s(firstVertex hn j, secondVertex hn j) := by
            apply Sym2.map.injective (evenVertexEmbedding hdp hp).injective
            simpa [evenCountMap, Sym2.map_mk] using hab
          rw [SimpleGraph.mem_edgeFinset] at he
          rw [hpre, SimpleGraph.mem_edgeSet] at he
          have hne : ((firstVertex hn j : Fin n) : ℕ) % p ≠
              ((secondVertex hn j : Fin n) : ℕ) % p := he
          apply hne
          simp [firstVertex, secondVertex, Nat.add_mod]
  | inr i =>
      cases b with
      | inl f =>
          exfalso
          have hf : f ∈ (SimpleGraph.turanGraph n p).edgeFinset := by
            simpa [evenCountDomain] using hb
          have hpre : s(firstVertex hn i, secondVertex hn i) = f := by
            apply Sym2.map.injective (evenVertexEmbedding hdp hp).injective
            simpa [evenCountMap, Sym2.map_mk] using hab
          rw [SimpleGraph.mem_edgeFinset] at hf
          rw [← hpre, SimpleGraph.mem_edgeSet] at hf
          have hne : ((firstVertex hn i : Fin n) : ℕ) % p ≠
              ((secondVertex hn i : Fin n) : ℕ) % p := hf
          apply hne
          simp [firstVertex, secondVertex, Nat.add_mod]
      | inr j =>
          congr 1
          have hpre : s(firstVertex hn i, secondVertex hn i) =
              s(firstVertex hn j, secondVertex hn j) := by
            apply Sym2.map.injective (evenVertexEmbedding hdp hp).injective
            simpa [evenCountMap, Sym2.map_mk] using hab
          rw [Sym2.eq_iff] at hpre
          rcases hpre with h | h
          · apply Fin.ext
            have hval := congrArg Fin.val h.1
            simpa [firstVertex] using hval
          · have hval := congrArg Fin.val h.1
            dsimp [firstVertex, secondVertex] at hval
            omega

lemma evenCountMap_mem_diameterEdge {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (hn : 2 * p ≤ n) {z : Sym2 (Fin n) ⊕ Fin p} (hz : z ∈ evenCountDomain n p) :
    evenCountMap hdp hp hn z ∈
      (diameterGraph (evenConfiguration (n := n) hdp hp)).edgeFinset := by
  cases z with
  | inl e =>
      have he : e ∈ (SimpleGraph.turanGraph n p).edgeFinset := by
        simpa [evenCountDomain] using hz
      rw [SimpleGraph.mem_edgeFinset] at he
      rw [SimpleGraph.mem_edgeFinset]
      change Sym2.map (evenVertexEmbedding hdp hp) e ∈
        (diameterGraph (evenConfiguration (n := n) hdp hp)).edgeSet
      induction e using Sym2.inductionOn with
      | _ v w =>
          rw [SimpleGraph.mem_edgeSet] at he
          change dist (evenPoint hdp hp v) (evenPoint hdp hp w) = 1
          apply dist_evenPoint_eq_one_of_ne_part hdp hp
          rw [Lenz.part_ne_iff hp]
          exact he
  | inr i =>
      rw [SimpleGraph.mem_edgeFinset]
      change (diameterGraph (evenConfiguration (n := n) hdp hp)).Adj
        (evenVertexEmbedding hdp hp (firstVertex hn i))
        (evenVertexEmbedding hdp hp (secondVertex hn i))
      change dist (evenPoint hdp hp (firstVertex hn i))
        (evenPoint hdp hp (secondVertex hn i)) = 1
      apply dist_evenPoint_eq_one_of_parameters_zero_one hdp hp
      · apply Fin.ext
        simp [Lenz.part, firstVertex, secondVertex, Nat.add_mod]
      · apply parameter_eq_zero_of_val_lt
        simp [firstVertex]
      · apply parameter_eq_one_of_level_one
        · simp [secondVertex]
        · simp [secondVertex]
          omega

lemma even_exact_count_le_diameterPairCount {d n p : ℕ}
    (hdp : 2 * p ≤ d) (hp : 0 < p) (hn : 2 * p ≤ n) :
    turanNumber p n + p ≤
      diameterPairCount (evenConfiguration (n := n) hdp hp) := by
  rw [diameterPairCount, ← card_evenCountDomain n p]
  exact Finset.card_le_card_of_injOn (evenCountMap hdp hp hn)
    (fun _ hz ↦ evenCountMap_mem_diameterEdge hdp hp hn hz)
    (evenCountMap_injOn hdp hp hn)

/-- Exact construction lower bound in even dimensions at least six. -/
theorem even_exact_lower {d n : ℕ} (hd : 6 ≤ d) (heven : Even d)
    (hn : 2 * (d / 2) ≤ n) :
    turanNumber (d / 2) n + d / 2 ≤ f d n := by
  have hdp : 2 * (d / 2) ≤ d := by
    have := Nat.div_mul_le_self d 2
    omega
  have hp : 0 < d / 2 := by omega
  have hp2 : 2 ≤ d / 2 := by omega
  apply (even_exact_count_le_diameterPairCount hdp hp hn).trans
  exact diameterPairCount_le_f
    (card_evenConfiguration hdp hp)
    (isDiameterOne_evenConfiguration hdp hp hp2 hn)

/-! ## Odd-dimensional carriers: one pole and an equatorial quadrant -/

def shiftFin {n : ℕ} (p : ℕ) (v : Fin n) : Fin n :=
  ⟨(v : ℕ) - p, lt_of_le_of_lt (Nat.sub_le _ _) v.isLt⟩

/-- In the distinguished residue-zero carrier, deleting the pole shifts the
two designated equatorial endpoints down by one level. -/
def oddParameter {n : ℕ} (p : ℕ) (v : Fin n) : ℝ :=
  if (v : ℕ) % p = 0 then parameter p (shiftFin p v) else parameter p v

lemma oddParameter_nonneg {n : ℕ} (p : ℕ) (v : Fin n) :
    0 ≤ oddParameter p v := by
  simp only [oddParameter]
  split_ifs <;> apply parameter_nonneg

lemma oddParameter_sq_le_one {n : ℕ} (p : ℕ) (v : Fin n) :
    oddParameter p v ^ 2 ≤ 1 := by
  simp only [oddParameter]
  split_ifs <;> apply parameter_sq_le_one

lemma le_val_of_mod_eq_zero_of_ne_zero {n p : ℕ} (hp : 0 < p) {v : Fin n}
    (hmod : (v : ℕ) % p = 0) (hv : (v : ℕ) ≠ 0) : p ≤ (v : ℕ) := by
  by_contra h
  have hvval : (v : ℕ) = 0 := by
    rw [Nat.mod_eq_of_lt (not_le.mp h)] at hmod
    exact hmod
  exact hv hvval

lemma oddParameter_injective_of_same_part_of_ne_zero {n p : ℕ} (hp : 0 < p)
    {v w : Fin n} (hmod : (v : ℕ) % p = (w : ℕ) % p)
    (hv : (v : ℕ) ≠ 0) (hw : (w : ℕ) ≠ 0)
    (hpar : oddParameter p v = oddParameter p w) : v = w := by
  by_cases hz : (v : ℕ) % p = 0
  · have hzw : (w : ℕ) % p = 0 := hmod ▸ hz
    have hpv := le_val_of_mod_eq_zero_of_ne_zero hp hz hv
    have hpw := le_val_of_mod_eq_zero_of_ne_zero hp hzw hw
    have hshiftmod : ((shiftFin p v : Fin n) : ℕ) % p =
        ((shiftFin p w : Fin n) : ℕ) % p := by
      dsimp [shiftFin]
      rw [← Nat.mod_eq_sub_mod hpv, ← Nat.mod_eq_sub_mod hpw, hz, hzw]
    have hshiftpar : parameter p (shiftFin p v) = parameter p (shiftFin p w) := by
      simpa [oddParameter, hz, hzw] using hpar
    have hshift := parameter_injective_of_mod_eq hp hshiftmod hshiftpar
    apply Fin.ext
    have hval := congrArg Fin.val hshift
    dsimp [shiftFin] at hval
    omega
  · have hzw : (w : ℕ) % p ≠ 0 := by
      intro h
      exact hz (hmod.trans h)
    exact parameter_injective_of_mod_eq hp hmod (by
      simpa [oddParameter, hz, hzw] using hpar)

def extraIndex {d p : ℕ} (hdp : 2 * p + 1 ≤ d) : Fin d :=
  ⟨2 * p, hdp⟩

lemma extraIndex_ne_evenIndex {d p : ℕ} (hdp : 2 * p + 1 ≤ d) (i : Fin p) :
    extraIndex hdp ≠ Lenz.evenIndex (by omega : 2 * p ≤ d) i := by
  intro h
  have := congrArg Fin.val h
  dsimp [extraIndex, Lenz.evenIndex] at this
  omega

lemma extraIndex_ne_oddIndex {d p : ℕ} (hdp : 2 * p + 1 ≤ d) (i : Fin p) :
    extraIndex hdp ≠ Lenz.oddIndex (by omega : 2 * p ≤ d) i := by
  intro h
  have := congrArg Fin.val h
  dsimp [extraIndex, Lenz.oddIndex] at this
  omega

def oddPoint {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) (v : Fin n) :
    Point d :=
  if (v : ℕ) = 0 then
    EuclideanSpace.single (extraIndex hdp) (Lenz.secondCoordinate 1)
  else
    EuclideanSpace.single (Lenz.evenIndex (by omega : 2 * p ≤ d) (Lenz.part hp v))
        (Lenz.firstCoordinate (oddParameter p v)) +
      EuclideanSpace.single (Lenz.oddIndex (by omega : 2 * p ≤ d) (Lenz.part hp v))
        (Lenz.secondCoordinate (oddParameter p v))

lemma oddPoint_apply_extra {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (v : Fin n) :
    oddPoint hdp hp v (extraIndex hdp) =
      if (v : ℕ) = 0 then Lenz.secondCoordinate 1 else 0 := by
  by_cases hv : (v : ℕ) = 0
  · simp [oddPoint, hv]
  · simp [oddPoint, hv, extraIndex_ne_evenIndex, extraIndex_ne_oddIndex]

lemma oddPoint_apply_odd_of_ne_zero {d n p : ℕ} (hdp : 2 * p + 1 ≤ d)
    (hp : 0 < p) {v : Fin n} (hv : (v : ℕ) ≠ 0) :
    oddPoint hdp hp v
        (Lenz.oddIndex (by omega : 2 * p ≤ d) (Lenz.part hp v)) =
      Lenz.secondCoordinate (oddParameter p v) := by
  simp [oddPoint, hv, Lenz.oddIndex_ne_evenIndex]

lemma inner_oddPoint_same_part_of_ne_zero {d n p : ℕ}
    (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) {v w : Fin n}
    (hv : (v : ℕ) ≠ 0) (hw : (w : ℕ) ≠ 0)
    (hpart : Lenz.part hp v = Lenz.part hp w) :
    inner ℝ (oddPoint hdp hp v) (oddPoint hdp hp w) =
      Lenz.firstCoordinate (oddParameter p v) * Lenz.firstCoordinate (oddParameter p w) +
        Lenz.secondCoordinate (oddParameter p v) * Lenz.secondCoordinate (oddParameter p w) := by
  simp [oddPoint, hv, hw, hpart, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, Lenz.evenIndex_ne_oddIndex,
    Lenz.oddIndex_ne_evenIndex]

lemma inner_oddPoint_self {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (v : Fin n) : inner ℝ (oddPoint hdp hp v) (oddPoint hdp hp v) = 1 / 2 := by
  by_cases hv : (v : ℕ) = 0
  ·
    simp [oddPoint, hv, Lenz.secondCoordinate]
  · rw [inner_oddPoint_same_part_of_ne_zero hdp hp hv hv rfl]
    simpa [pow_two] using Lenz.coordinates_sq_add (oddParameter_sq_le_one p v)

lemma inner_oddPoint_of_ne_part {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    {v w : Fin n} (hpart : Lenz.part hp v ≠ Lenz.part hp w) :
    inner ℝ (oddPoint hdp hp v) (oddPoint hdp hp w) = 0 := by
  have hvw : v ≠ w := fun h ↦ hpart (h ▸ rfl)
  by_cases hv : (v : ℕ) = 0
  · have hw : (w : ℕ) ≠ 0 := by
      intro hw
      exact hvw (Fin.ext (hv.trans hw.symm))
    simp [oddPoint, hv, hw, extraIndex_ne_evenIndex, extraIndex_ne_oddIndex,
      inner_add_left, inner_add_right, EuclideanSpace.inner_single_left]
  · by_cases hw : (w : ℕ) = 0
    ·
      simp [oddPoint, hv, hw, extraIndex_ne_evenIndex, extraIndex_ne_oddIndex,
        inner_add_left, inner_add_right, EuclideanSpace.inner_single_left]
    · have hee : Lenz.evenIndex (by omega : 2 * p ≤ d) (Lenz.part hp v) ≠
          Lenz.evenIndex (by omega : 2 * p ≤ d) (Lenz.part hp w) :=
        fun h ↦ hpart (Lenz.evenIndex_injective (by omega : 2 * p ≤ d) h)
      have hoo : Lenz.oddIndex (by omega : 2 * p ≤ d) (Lenz.part hp v) ≠
          Lenz.oddIndex (by omega : 2 * p ≤ d) (Lenz.part hp w) :=
        fun h ↦ hpart (Lenz.oddIndex_injective (by omega : 2 * p ≤ d) h)
      simp [oddPoint, hv, hw, inner_add_left, inner_add_right,
        EuclideanSpace.inner_single_left, hee, hoo,
        Lenz.evenIndex_ne_oddIndex, Lenz.oddIndex_ne_evenIndex]

lemma inner_oddPoint_nonneg {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (v w : Fin n) : 0 ≤ inner ℝ (oddPoint hdp hp v) (oddPoint hdp hp w) := by
  by_cases hv : (v : ℕ) = 0
  · by_cases hw : (w : ℕ) = 0
    · have hvw : v = w := Fin.ext (hv.trans hw.symm)
      subst w
      rw [inner_oddPoint_self]
      norm_num
    · simp [oddPoint, hv, hw, extraIndex_ne_evenIndex, extraIndex_ne_oddIndex,
        inner_add_left, inner_add_right, EuclideanSpace.inner_single_left]
  · by_cases hw : (w : ℕ) = 0
    ·
      simp [oddPoint, hv, hw, extraIndex_ne_evenIndex, extraIndex_ne_oddIndex,
        inner_add_left, inner_add_right, EuclideanSpace.inner_single_left]
    · by_cases hpart : Lenz.part hp v = Lenz.part hp w
      · simp [oddPoint, hv, hw, hpart, inner_add_left, inner_add_right,
          EuclideanSpace.inner_single_left, Lenz.evenIndex_ne_oddIndex,
          Lenz.oddIndex_ne_evenIndex]
        exact add_nonneg
          (mul_nonneg (Lenz.firstCoordinate_nonneg _) (Lenz.firstCoordinate_nonneg _))
          (mul_nonneg (Lenz.secondCoordinate_nonneg (oddParameter_nonneg _ _))
            (Lenz.secondCoordinate_nonneg (oddParameter_nonneg _ _)))
      · rw [inner_oddPoint_of_ne_part hdp hp hpart]

lemma dist_oddPoint_sq {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (v w : Fin n) :
    dist (oddPoint hdp hp v) (oddPoint hdp hp w) ^ 2 =
      1 - 2 * inner ℝ (oddPoint hdp hp v) (oddPoint hdp hp w) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [inner_oddPoint_self hdp hp v, inner_oddPoint_self hdp hp w]
  rw [show inner ℝ (oddPoint hdp hp w) (oddPoint hdp hp v) =
      inner ℝ (oddPoint hdp hp v) (oddPoint hdp hp w) from real_inner_comm _ _]
  ring

lemma dist_oddPoint_le_one {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (v w : Fin n) : dist (oddPoint hdp hp v) (oddPoint hdp hp w) ≤ 1 := by
  have hsq := dist_oddPoint_sq hdp hp v w
  have hi := inner_oddPoint_nonneg hdp hp v w
  have hd : 0 ≤ dist (oddPoint hdp hp v) (oddPoint hdp hp w) := dist_nonneg
  nlinarith

lemma dist_oddPoint_eq_one_of_inner_zero {d n p : ℕ}
    (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) {v w : Fin n}
    (hinner : inner ℝ (oddPoint hdp hp v) (oddPoint hdp hp w) = 0) :
    dist (oddPoint hdp hp v) (oddPoint hdp hp w) = 1 := by
  have hsq := dist_oddPoint_sq hdp hp v w
  rw [hinner] at hsq
  have hd : 0 ≤ dist (oddPoint hdp hp v) (oddPoint hdp hp w) := dist_nonneg
  nlinarith

lemma oddPoint_injective {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) :
    Function.Injective (@oddPoint d n p hdp hp) := by
  intro v w hvw
  by_cases hv : (v : ℕ) = 0
  · by_cases hw : (w : ℕ) = 0
    · exact Fin.ext (hv.trans hw.symm)
    · have hc := congrArg (fun z : Point d ↦ z (extraIndex hdp)) hvw
      rw [oddPoint_apply_extra hdp hp v, oddPoint_apply_extra hdp hp w] at hc
      simp [hv, hw, Lenz.secondCoordinate] at hc
  · by_cases hw : (w : ℕ) = 0
    ·
      have hc := congrArg (fun z : Point d ↦ z (extraIndex hdp)) hvw
      rw [oddPoint_apply_extra hdp hp v, oddPoint_apply_extra hdp hp w] at hc
      simp [hv, hw, Lenz.secondCoordinate] at hc
      have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      exact (hsqrt hc.symm).elim
    · have hinner : inner ℝ (oddPoint hdp hp v) (oddPoint hdp hp w) = 1 / 2 := by
        rw [hvw]
        exact inner_oddPoint_self hdp hp w
      have hpart : Lenz.part hp v = Lenz.part hp w := by
        by_contra hne
        rw [inner_oddPoint_of_ne_part hdp hp hne] at hinner
        norm_num at hinner
      have hc := congrArg
        (fun z : Point d ↦ z
          (Lenz.oddIndex (by omega : 2 * p ≤ d) (Lenz.part hp v))) hvw
      rw [oddPoint_apply_odd_of_ne_zero hdp hp hv] at hc
      rw [hpart, oddPoint_apply_odd_of_ne_zero hdp hp hw] at hc
      apply oddParameter_injective_of_same_part_of_ne_zero hp
      · simpa [Lenz.part, Fin.ext_iff] using congrArg Fin.val hpart
      · exact hv
      · exact hw
      · exact Lenz.secondCoordinate_injective hc

def oddConfiguration {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) :
    Finset (Point d) := Finset.univ.image (fun v : Fin n ↦ oddPoint hdp hp v)

lemma card_oddConfiguration {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) :
    (oddConfiguration (n := n) hdp hp).card = n := by
  rw [oddConfiguration, Finset.card_image_iff.mpr (oddPoint_injective hdp hp).injOn]
  simp

lemma mem_oddConfiguration {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (v : Fin n) : oddPoint hdp hp v ∈ oddConfiguration (n := n) hdp hp := by
  simp [oddConfiguration]

lemma isDiameterOne_oddConfiguration {d n p : ℕ}
    (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) (hp2 : 2 ≤ p) (hn : 2 ≤ n) :
    IsDiameterOne (oddConfiguration (n := n) hdp hp) := by
  rw [isDiameterOne_iff]
  refine ⟨?_, ?_⟩
  · simp only [oddConfiguration, Finset.mem_image, Finset.mem_univ, true_and]
    rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩
    exact dist_oddPoint_le_one hdp hp v w
  · let v : Fin n := ⟨0, by omega⟩
    let w : Fin n := ⟨1, by omega⟩
    refine ⟨oddPoint hdp hp v, mem_oddConfiguration hdp hp v,
      oddPoint hdp hp w, mem_oddConfiguration hdp hp w, ?_⟩
    apply dist_oddPoint_eq_one_of_inner_zero hdp hp
    apply inner_oddPoint_of_ne_part hdp hp
    rw [Lenz.part_ne_iff hp]
    dsimp [v, w]
    rw [Nat.mod_eq_of_lt (by omega : 1 < p)]
    norm_num

lemma dist_oddPoint_eq_one_of_parameters_zero_one {d n p : ℕ}
    (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) {v w : Fin n}
    (hv0 : (v : ℕ) ≠ 0) (hw0 : (w : ℕ) ≠ 0)
    (hpart : Lenz.part hp v = Lenz.part hp w)
    (hv : oddParameter p v = 0) (hw : oddParameter p w = 1) :
    dist (oddPoint hdp hp v) (oddPoint hdp hp w) = 1 := by
  apply dist_oddPoint_eq_one_of_inner_zero hdp hp
  rw [inner_oddPoint_same_part_of_ne_zero hdp hp hv0 hw0 hpart, hv, hw]
  simp [Lenz.firstCoordinate, Lenz.secondCoordinate]

def poleVertex {n : ℕ} (hn : 0 < n) : Fin n := ⟨0, hn⟩

def oddFirstVertex {n p : ℕ} (hn : 3 * p ≤ n) (i : Fin p) : Fin n :=
  if hi : (i : ℕ) = 0 then ⟨p, by omega⟩ else ⟨i, by omega⟩

def oddSecondVertex {n p : ℕ} (hn : 3 * p ≤ n) (i : Fin p) : Fin n :=
  if hi : (i : ℕ) = 0 then ⟨2 * p, by omega⟩ else ⟨p + i, by omega⟩

lemma oddFirstVertex_ne_zero {n p : ℕ} (hp : 0 < p) (hn : 3 * p ≤ n)
    (i : Fin p) : ((oddFirstVertex hn i : Fin n) : ℕ) ≠ 0 := by
  by_cases hi : (i : ℕ) = 0
  · simp [oddFirstVertex, hi, hp.ne']
  · simp [oddFirstVertex, hi]

lemma oddSecondVertex_ne_zero {n p : ℕ} (hp : 0 < p) (hn : 3 * p ≤ n)
    (i : Fin p) : ((oddSecondVertex hn i : Fin n) : ℕ) ≠ 0 := by
  by_cases hi : (i : ℕ) = 0
  · simp [oddSecondVertex, hi, hp.ne']
  · simp [oddSecondVertex, hi]

lemma oddFirstSecond_same_part {n p : ℕ} (hp : 0 < p) (hn : 3 * p ≤ n)
    (i : Fin p) : Lenz.part hp (oddFirstVertex hn i) =
      Lenz.part hp (oddSecondVertex hn i) := by
  apply Fin.ext
  simp [Lenz.part, oddFirstVertex, oddSecondVertex]
  split_ifs <;> simp [Nat.add_mod]

lemma oddParameter_oddFirstVertex {n p : ℕ} (hp : 0 < p) (hn : 3 * p ≤ n)
    (i : Fin p) : oddParameter p (oddFirstVertex hn i) = 0 := by
  by_cases hi : (i : ℕ) = 0
  · have hmod : (p : ℕ) % p = 0 := Nat.mod_self p
    simp [oddFirstVertex, oddParameter, hi, hmod, shiftFin, parameter, hp.ne']
  · have himod : (i : ℕ) % p = i := Nat.mod_eq_of_lt i.isLt
    simp [oddFirstVertex, oddParameter, hi, himod, parameter]

lemma oddParameter_oddSecondVertex {n p : ℕ} (hp : 0 < p) (hn : 3 * p ≤ n)
    (i : Fin p) : oddParameter p (oddSecondVertex hn i) = 1 := by
  by_cases hi : (i : ℕ) = 0
  · have hmod : (2 * p : ℕ) % p = 0 := by simp
    have hsub : 2 * p - p = p := by omega
    simp [oddSecondVertex, oddParameter, hi, hmod, shiftFin, parameter, hsub, hp]
  · have himod : (p + (i : ℕ)) % p = i := by simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
    simp [oddSecondVertex, oddParameter, hi, himod, parameter]
    omega

def starCount (n p : ℕ) : ℕ := (n - 1) / p

lemma starCount_add_one {n p : ℕ} (hn : 0 < n) (hp : 0 < p) :
    starCount n p + 1 = ceilQuot n p := by
  rw [ceilQuot_eq_succ_pred_div hn hp]
  rfl

def starVertex {n p : ℕ} (hp : 0 < p) (k : Fin (starCount n p)) : Fin n := by
  refine ⟨p * ((k : ℕ) + 1), ?_⟩
  have hk : (k : ℕ) + 1 ≤ starCount n p := k.isLt
  change (k : ℕ) + 1 ≤ (n - 1) / p at hk
  have hmul : ((k : ℕ) + 1) * p ≤ n - 1 :=
    (Nat.le_div_iff_mul_le hp).mp hk
  rw [Nat.mul_comm]
  have hprod : 0 < ((k : ℕ) + 1) * p := Nat.mul_pos (by omega) hp
  have hn : 0 < n := by omega
  exact hmul.trans_lt (Nat.sub_lt hn (by omega))

lemma starVertex_ne_zero {n p : ℕ} (hp : 0 < p) (k : Fin (starCount n p)) :
    ((starVertex hp k : Fin n) : ℕ) ≠ 0 := by
  dsimp [starVertex]
  positivity

lemma starVertex_mod {n p : ℕ} (hp : 0 < p) (k : Fin (starCount n p)) :
    ((starVertex hp k : Fin n) : ℕ) % p = 0 := by
  simp [starVertex]

lemma starVertex_injective {n p : ℕ} (hp : 0 < p) :
    Function.Injective (@starVertex n p hp) := by
  intro i j h
  have hv := congrArg Fin.val h
  dsimp [starVertex] at hv
  apply Fin.ext
  nlinarith

lemma dist_pole_starVertex {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (hn : 0 < n) (k : Fin (starCount n p)) :
    dist (oddPoint hdp hp (poleVertex hn)) (oddPoint hdp hp (starVertex hp k)) = 1 := by
  apply dist_oddPoint_eq_one_of_inner_zero hdp hp
  have hk0 := starVertex_ne_zero hp k
  simp [oddPoint, poleVertex, hk0, extraIndex_ne_evenIndex, extraIndex_ne_oddIndex,
    inner_add_left, inner_add_right, EuclideanSpace.inner_single_left]

def oddVertexEmbedding {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) :
    Fin n ↪ {x // x ∈ oddConfiguration (n := n) hdp hp} where
  toFun v := ⟨oddPoint hdp hp v, mem_oddConfiguration hdp hp v⟩
  inj' _ _ h := oddPoint_injective hdp hp (Subtype.ext_iff.mp h)

def oddCountDomain (n p : ℕ) :
    Finset (Sym2 (Fin n) ⊕ (Fin p ⊕ Fin (starCount n p))) :=
  (SimpleGraph.turanGraph n p).edgeFinset.disjSum
    (Finset.univ.disjSum Finset.univ)

lemma card_oddCountDomain (n p : ℕ) :
    (oddCountDomain n p).card = turanNumber p n + (p + starCount n p) := by
  simp [oddCountDomain, turanNumber]

def oddCountMap {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (hn : 3 * p ≤ n) :
    Sym2 (Fin n) ⊕ (Fin p ⊕ Fin (starCount n p)) →
      Sym2 {x // x ∈ oddConfiguration (n := n) hdp hp}
  | .inl e => Sym2.map (oddVertexEmbedding hdp hp) e
  | .inr (.inl i) => s(oddVertexEmbedding hdp hp (oddFirstVertex hn i),
      oddVertexEmbedding hdp hp (oddSecondVertex hn i))
  | .inr (.inr k) => s(oddVertexEmbedding hdp hp (poleVertex (by omega)),
      oddVertexEmbedding hdp hp (starVertex hp k))

lemma not_turan_edge_of_mod_eq {n p : ℕ} {v w : Fin n}
    (hmod : (v : ℕ) % p = (w : ℕ) % p) :
    s(v, w) ∉ (SimpleGraph.turanGraph n p).edgeFinset := by
  intro h
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h
  exact h hmod

lemma oddSpecialEdge_injective {n p : ℕ} (hp : 0 < p) (hn : 3 * p ≤ n) :
    Function.Injective (fun i : Fin p ↦
      s(oddFirstVertex hn i, oddSecondVertex hn i)) := by
  intro i j h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · by_cases hi : (i : ℕ) = 0
    · by_cases hj : (j : ℕ) = 0
      · exact Fin.ext (hi.trans hj.symm)
      · have hv := congrArg Fin.val h.1
        simp [oddFirstVertex, hi, hj] at hv
        omega
    · by_cases hj : (j : ℕ) = 0
      · have hv := congrArg Fin.val h.1
        simp [oddFirstVertex, hi, hj] at hv
        omega
      · have hv := congrArg Fin.val h.1
        apply Fin.ext
        simpa [oddFirstVertex, hi, hj] using hv
  · have hv := congrArg Fin.val h.1
    by_cases hi : (i : ℕ) = 0 <;> by_cases hj : (j : ℕ) = 0 <;>
      simp [oddFirstVertex, oddSecondVertex, hi, hj] at hv <;> omega

lemma oddSpecialEdge_ne_starEdge {n p : ℕ} (hp : 0 < p) (hn : 3 * p ≤ n)
    (i : Fin p) (k : Fin (starCount n p)) :
    s(oddFirstVertex hn i, oddSecondVertex hn i) ≠
      s(poleVertex (by omega : 0 < n), starVertex hp k) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have hv := congrArg Fin.val h.1
    exact oddFirstVertex_ne_zero hp hn i (by simpa [poleVertex] using hv)
  · have hv := congrArg Fin.val h.2
    exact oddSecondVertex_ne_zero hp hn i (by simpa [poleVertex] using hv)

lemma oddCountMap_injOn {d n p : ℕ} (hdp : 2 * p + 1 ≤ d) (hp : 0 < p)
    (hn : 3 * p ≤ n) :
    Set.InjOn (oddCountMap hdp hp hn) (oddCountDomain n p) := by
  intro a ha b hb hab
  cases a with
  | inl e =>
      cases b with
      | inl f =>
          congr 1
          exact Sym2.map.injective (oddVertexEmbedding hdp hp).injective hab
      | inr r =>
          exfalso
          have he : e ∈ (SimpleGraph.turanGraph n p).edgeFinset := by
            simpa [oddCountDomain] using ha
          cases r with
          | inl j =>
              have hpre : e = s(oddFirstVertex hn j, oddSecondVertex hn j) := by
                apply Sym2.map.injective (oddVertexEmbedding hdp hp).injective
                simpa [oddCountMap, Sym2.map_mk] using hab
              apply (not_turan_edge_of_mod_eq (p := p) ?_) (hpre ▸ he)
              exact congrArg Fin.val (oddFirstSecond_same_part hp hn j)
          | inr k =>
              have hpre : e = s(poleVertex (by omega : 0 < n), starVertex hp k) := by
                apply Sym2.map.injective (oddVertexEmbedding hdp hp).injective
                simpa [oddCountMap, Sym2.map_mk] using hab
              apply (not_turan_edge_of_mod_eq (p := p) ?_) (hpre ▸ he)
              simp [poleVertex, starVertex_mod hp k]
  | inr r =>
      cases b with
      | inl f =>
          exfalso
          have hf : f ∈ (SimpleGraph.turanGraph n p).edgeFinset := by
            simpa [oddCountDomain] using hb
          cases r with
          | inl i =>
              have hpre : s(oddFirstVertex hn i, oddSecondVertex hn i) = f := by
                apply Sym2.map.injective (oddVertexEmbedding hdp hp).injective
                simpa [oddCountMap, Sym2.map_mk] using hab
              apply (not_turan_edge_of_mod_eq (p := p) ?_) (hpre.symm ▸ hf)
              exact congrArg Fin.val (oddFirstSecond_same_part hp hn i)
          | inr k =>
              have hpre : s(poleVertex (by omega : 0 < n), starVertex hp k) = f := by
                apply Sym2.map.injective (oddVertexEmbedding hdp hp).injective
                simpa [oddCountMap, Sym2.map_mk] using hab
              apply (not_turan_edge_of_mod_eq (p := p) ?_) (hpre.symm ▸ hf)
              simp [poleVertex, starVertex_mod hp k]
      | inr s =>
          cases r with
          | inl i =>
              cases s with
              | inl j =>
                  congr 2
                  apply oddSpecialEdge_injective hp hn
                  apply Sym2.map.injective (oddVertexEmbedding hdp hp).injective
                  simpa [oddCountMap, Sym2.map_mk] using hab
              | inr k =>
                  exfalso
                  apply oddSpecialEdge_ne_starEdge hp hn i k
                  apply Sym2.map.injective (oddVertexEmbedding hdp hp).injective
                  simpa [oddCountMap, Sym2.map_mk] using hab
          | inr k =>
              cases s with
              | inl j =>
                  exfalso
                  apply oddSpecialEdge_ne_starEdge hp hn j k
                  apply Sym2.map.injective (oddVertexEmbedding hdp hp).injective
                  simpa [oddCountMap, Sym2.map_mk] using hab.symm
              | inr l =>
                  congr 2
                  have hpre : s(poleVertex (by omega : 0 < n), starVertex hp k) =
                      s(poleVertex (by omega : 0 < n), starVertex hp l) := by
                    apply Sym2.map.injective (oddVertexEmbedding hdp hp).injective
                    simpa [oddCountMap, Sym2.map_mk] using hab
                  rw [Sym2.congr_right] at hpre
                  exact starVertex_injective hp hpre

lemma oddCountMap_mem_diameterEdge {d n p : ℕ} (hdp : 2 * p + 1 ≤ d)
    (hp : 0 < p) (hn : 3 * p ≤ n)
    {z : Sym2 (Fin n) ⊕ (Fin p ⊕ Fin (starCount n p))}
    (hz : z ∈ oddCountDomain n p) :
    oddCountMap hdp hp hn z ∈
      (diameterGraph (oddConfiguration (n := n) hdp hp)).edgeFinset := by
  cases z with
  | inl e =>
      have he : e ∈ (SimpleGraph.turanGraph n p).edgeFinset := by
        simpa [oddCountDomain] using hz
      rw [SimpleGraph.mem_edgeFinset] at he ⊢
      change Sym2.map (oddVertexEmbedding hdp hp) e ∈
        (diameterGraph (oddConfiguration (n := n) hdp hp)).edgeSet
      induction e using Sym2.inductionOn with
      | _ v w =>
          rw [SimpleGraph.mem_edgeSet] at he
          change dist (oddPoint hdp hp v) (oddPoint hdp hp w) = 1
          apply dist_oddPoint_eq_one_of_inner_zero hdp hp
          apply inner_oddPoint_of_ne_part hdp hp
          rw [Lenz.part_ne_iff hp]
          exact he
  | inr r =>
      rw [SimpleGraph.mem_edgeFinset]
      cases r with
      | inl i =>
          change dist (oddPoint hdp hp (oddFirstVertex hn i))
            (oddPoint hdp hp (oddSecondVertex hn i)) = 1
          apply dist_oddPoint_eq_one_of_parameters_zero_one hdp hp
          · exact oddFirstVertex_ne_zero hp hn i
          · exact oddSecondVertex_ne_zero hp hn i
          · exact oddFirstSecond_same_part hp hn i
          · exact oddParameter_oddFirstVertex hp hn i
          · exact oddParameter_oddSecondVertex hp hn i
      | inr k =>
          change dist (oddPoint hdp hp (poleVertex (by omega : 0 < n)))
            (oddPoint hdp hp (starVertex hp k)) = 1
          exact dist_pole_starVertex hdp hp (by omega) k

lemma odd_exact_count_le_diameterPairCount {d n p : ℕ}
    (hdp : 2 * p + 1 ≤ d) (hp : 0 < p) (hn : 3 * p ≤ n) :
    turanNumber p n + ceilQuot n p + (p - 1) ≤
      diameterPairCount (oddConfiguration (n := n) hdp hp) := by
  have hn0 : 0 < n := by omega
  have hceil := starCount_add_one hn0 hp
  rw [diameterPairCount]
  calc
    turanNumber p n + ceilQuot n p + (p - 1) =
        (oddCountDomain n p).card := by
          rw [card_oddCountDomain, ← hceil]
          omega
    _ ≤ (diameterGraph (oddConfiguration (n := n) hdp hp)).edgeFinset.card :=
      Finset.card_le_card_of_injOn (oddCountMap hdp hp hn)
        (fun _ hz ↦ oddCountMap_mem_diameterEdge hdp hp hn hz)
        (oddCountMap_injOn hdp hp hn)

/-- Exact construction lower bound in odd dimensions at least seven. -/
theorem odd_exact_lower {d n : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hn : 3 * (d / 2) ≤ n) :
    turanNumber (d / 2) n + ceilQuot n (d / 2) + (d / 2 - 1) ≤ f d n := by
  have hdp : 2 * (d / 2) + 1 ≤ d := by
    obtain ⟨k, rfl⟩ := hodd
    omega
  have hp : 0 < d / 2 := by omega
  have hp2 : 2 ≤ d / 2 := by omega
  apply (odd_exact_count_le_diameterPairCount hdp hp hn).trans
  exact diameterPairCount_le_f
    (card_oddConfiguration hdp hp)
    (isDiameterOne_oddConfiguration hdp hp hp2 (by omega))

end ExactLower

end

end Erdos223
