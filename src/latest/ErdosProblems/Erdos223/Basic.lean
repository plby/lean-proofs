/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 223: basic definitions

This file contains the finite metric model used throughout the formalization.
The extremal function is defined as a genuine finite maximum of the numbers of
unordered diameter pairs in diameter-one point sets.
-/

open Metric
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223

/-- Euclidean `d`-space, used as the ambient space in Problem 223. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A finite point set has diameter one. -/
def IsDiameterOne {d : ℕ} (A : Finset (Point d)) : Prop :=
  Metric.diam (↑A : Set (Point d)) = 1

/-- The diameter graph of a diameter-one point set.  Its vertices are the
points of `A`, and its edges are exactly the unordered pairs at distance one. -/
noncomputable def diameterGraph {d : ℕ} (A : Finset (Point d)) :
    SimpleGraph {x // x ∈ A} where
  Adj x y := dist (x : Point d) (y : Point d) = 1
  symm.symm := by
    intro x y h
    simpa [dist_comm] using h
  loopless.irrefl := by
    intro x h
    simpa using h

noncomputable instance diameterGraph.instDecidableRelAdj {d : ℕ}
    (A : Finset (Point d)) : DecidableRel (diameterGraph A).Adj :=
  Classical.decRel _

/-- The number of unordered pairs of points of `A` at distance one. -/
noncomputable def diameterPairCount {d : ℕ} (A : Finset (Point d)) : ℕ :=
  (diameterGraph A).edgeFinset.card

@[simp]
theorem diameterGraph_adj {d : ℕ} (A : Finset (Point d))
    (x y : {x // x ∈ A}) :
    (diameterGraph A).Adj x y ↔ dist (x : Point d) (y : Point d) = 1 :=
  Iff.rfl

/-- No point set has more unordered unit-distance pairs than it has unordered
pairs in total. -/
theorem diameterPairCount_le_choose {d : ℕ} (A : Finset (Point d)) :
    diameterPairCount A ≤ A.card.choose 2 := by
  classical
  simpa [diameterPairCount] using (diameterGraph A).card_edgeFinset_le_card_choose_two

/-- The attainable diameter-pair counts for fixed dimension and cardinality. -/
def attainableCounts (d n : ℕ) : Set ℕ :=
  {m | ∃ A : Finset (Point d),
    A.card = n ∧ IsDiameterOne A ∧ diameterPairCount A = m}

/-- The extremal function in Erdős Problem 223.  The value is zero when the
parameter pair admits no diameter-one configuration. -/
noncomputable def f (d n : ℕ) : ℕ :=
  sSup (attainableCounts d n)

/-- Attainable counts are bounded by the total number of pairs. -/
theorem attainableCounts_bddAbove (d n : ℕ) :
    BddAbove (attainableCounts d n) := by
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨A, hAcard, -, rfl⟩
  simpa [hAcard] using diameterPairCount_le_choose A

/-- Every diameter-one configuration gives a lower bound for `f`. -/
theorem diameterPairCount_le_f {d n : ℕ} {A : Finset (Point d)}
    (hAcard : A.card = n) (hA : IsDiameterOne A) :
    diameterPairCount A ≤ f d n := by
  apply le_csSup (attainableCounts_bddAbove d n)
  exact ⟨A, hAcard, hA, rfl⟩

/-- Construction-oriented lower-bound interface for the extremal function. -/
theorem le_f_of_exists {d n k : ℕ}
    (h : ∃ A : Finset (Point d),
      A.card = n ∧ IsDiameterOne A ∧ k ≤ diameterPairCount A) :
    k ≤ f d n := by
  obtain ⟨A, hAcard, hA, hk⟩ := h
  exact hk.trans (diameterPairCount_le_f hAcard hA)

/-- The extremal number is at most the total number of unordered pairs. -/
theorem f_le_choose (d n : ℕ) : f d n ≤ n.choose 2 := by
  rw [f]
  by_cases h : (attainableCounts d n).Nonempty
  · apply csSup_le h
    rintro m ⟨A, hAcard, -, rfl⟩
    simpa [hAcard] using diameterPairCount_le_choose A
  · rw [Set.not_nonempty_iff_eq_empty.mp h, csSup_empty]
    exact Nat.zero_le _

/-! ## The diameter-one criterion -/

/-- On a finite point set, diameter one is equivalent to all pairwise
distances being at most one and one pair attaining one. -/
theorem isDiameterOne_iff {d : ℕ} {A : Finset (Point d)} :
    IsDiameterOne A ↔
      (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) ∧
        ∃ x ∈ A, ∃ y ∈ A, dist x y = 1 := by
  constructor
  · intro hA
    change Metric.diam (↑A : Set (Point d)) = 1 at hA
    have hbounded : Bornology.IsBounded (↑A : Set (Point d)) :=
      A.finite_toSet.isBounded
    refine ⟨fun x hx y hy ↦ ?_, ?_⟩
    · exact (Metric.dist_le_diam_of_mem hbounded hx hy).trans_eq hA
    · by_contra hno
      push_neg at hno
      have hAne : A.Nonempty := by
        by_contra hempty
        have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
        subst A
        simpa [IsDiameterOne] using hA
      let D : Finset ℝ := (A.product A).image fun p ↦ dist p.1 p.2
      have hDne : D.Nonempty := by
        obtain ⟨x, hx⟩ := hAne
        exact ⟨dist x x, Finset.mem_image.mpr
          ⟨(x, x), Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩⟩
      let M : ℝ := D.max' hDne
      have hMmem : M ∈ D := Finset.max'_mem D hDne
      obtain ⟨p, hp, hpdist⟩ := Finset.mem_image.mp hMmem
      have hpA : p.1 ∈ A ∧ p.2 ∈ A := Finset.mem_product.mp hp
      have hMle : M ≤ 1 := by
        rw [← hpdist]
        exact Metric.dist_le_diam_of_mem hbounded hpA.1 hpA.2 |>.trans_eq hA
      have hMne : M ≠ 1 := by
        rw [← hpdist]
        exact hno p.1 hpA.1 p.2 hpA.2
      have hMlt : M < 1 := lt_of_le_of_ne hMle hMne
      have hdistM : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ M := by
        intro x hx y hy
        exact Finset.le_max' D _ (Finset.mem_image.mpr
          ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)
      have hMnonneg : 0 ≤ M := by
        obtain ⟨x, hx⟩ := hAne
        exact dist_nonneg.trans (hdistM x hx x hx)
      have hdiamle : Metric.diam (↑A : Set (Point d)) ≤ M :=
        Metric.diam_le_of_forall_dist_le hMnonneg hdistM
      exact (show ¬(1 : ℝ) ≤ M from not_le_of_gt hMlt) (hA ▸ hdiamle)
  · rintro ⟨hle, x, hx, y, hy, hxy⟩
    apply le_antisymm
    · exact Metric.diam_le_of_forall_dist_le zero_le_one hle
    · have hbounded : Bornology.IsBounded (↑A : Set (Point d)) :=
        A.finite_toSet.isBounded
      simpa [hxy] using Metric.dist_le_diam_of_mem hbounded hx hy

theorem IsDiameterOne.dist_le {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A) {x y : Point d} (hx : x ∈ A) (hy : y ∈ A) :
    dist x y ≤ 1 :=
  (isDiameterOne_iff.mp hA).1 x hx y hy

theorem IsDiameterOne.exists_dist_eq_one {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A) :
    ∃ x ∈ A, ∃ y ∈ A, dist x y = 1 :=
  (isDiameterOne_iff.mp hA).2

/-! ## A canonical diameter-one configuration -/

private noncomputable def linePoint {d n : ℕ} (hd : 0 < d) (hn : 1 < n)
    (i : Fin n) : Point d :=
  EuclideanSpace.single ⟨0, hd⟩ ((i : ℝ) / ((n - 1 : ℕ) : ℝ))

private theorem linePoint_injective {d n : ℕ} (hd : 0 < d) (hn : 1 < n) :
    Function.Injective (linePoint hd hn) := by
  intro i j hij
  have hcoord := congrArg (fun z : Point d ↦ z ⟨0, hd⟩) hij
  simp only [linePoint, PiLp.single_apply, if_pos] at hcoord
  have hden : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hn
  have hcast : (i : ℝ) = (j : ℝ) := (div_left_inj' hden).mp hcoord
  exact Fin.ext (by exact_mod_cast hcast)

private noncomputable def linePointEmbedding {d n : ℕ} (hd : 0 < d) (hn : 1 < n) :
    Fin n ↪ Point d where
  toFun := linePoint hd hn
  inj' := linePoint_injective hd hn

/-- `n` evenly spaced points on a coordinate segment of length one. -/
noncomputable def segmentConfiguration {d n : ℕ} (hd : 0 < d) (hn : 1 < n) :
    Finset (Point d) :=
  Finset.univ.map (linePointEmbedding hd hn)

@[simp]
theorem card_segmentConfiguration {d n : ℕ} (hd : 0 < d) (hn : 1 < n) :
    (segmentConfiguration hd hn).card = n := by
  simp [segmentConfiguration]

private theorem linePoint_dist_le_one {d n : ℕ} (hd : 0 < d) (hn : 1 < n)
    (i j : Fin n) : dist (linePoint hd hn i) (linePoint hd hn j) ≤ 1 := by
  rw [show dist (linePoint hd hn i) (linePoint hd hn j) =
      dist ((i : ℝ) / ((n - 1 : ℕ) : ℝ))
        ((j : ℝ) / ((n - 1 : ℕ) : ℝ)) by
    simp [linePoint]]
  rw [Real.dist_eq]
  have hnsub : 0 < (((n - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_iff_lt.mpr hn
  have hi0 : 0 ≤ (i : ℝ) := by positivity
  have hj0 : 0 ≤ (j : ℝ) := by positivity
  have hi : (i : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_pred_of_lt i.isLt
  have hj : (j : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_pred_of_lt j.isLt
  rw [div_sub_div_same, abs_div, abs_of_pos hnsub]
  apply (div_le_one hnsub).mpr
  rw [abs_le]
  constructor <;> linarith

private theorem linePoint_endpoints_dist {d n : ℕ} (hd : 0 < d) (hn : 1 < n) :
    dist (linePoint hd hn ⟨0, Nat.zero_lt_of_lt hn⟩)
      (linePoint hd hn ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt hn) zero_lt_one⟩) = 1 := by
  rw [show dist (linePoint hd hn ⟨0, Nat.zero_lt_of_lt hn⟩)
      (linePoint hd hn ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt hn) zero_lt_one⟩) =
      dist ((0 : ℝ) / ((n - 1 : ℕ) : ℝ))
        (((n - 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) by
    simp [linePoint]]
  have hden : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hn
  simp [hden]

/-- The canonical coordinate-segment configuration has diameter one. -/
theorem isDiameterOne_segmentConfiguration {d n : ℕ}
    (hd : 0 < d) (hn : 1 < n) :
    IsDiameterOne (segmentConfiguration hd hn) := by
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
    exact linePoint_dist_le_one hd hn i j
  · let i : Fin n := ⟨0, Nat.zero_lt_of_lt hn⟩
    let j : Fin n := ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt hn) zero_lt_one⟩
    refine ⟨linePoint hd hn i, ?_, linePoint hd hn j, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
    · exact linePoint_endpoints_dist hd hn

/-- Diameter-one configurations exist in every positive dimension for every
cardinality at least two. -/
theorem attainableCounts_nonempty (d n : ℕ) (hd : 0 < d) (hn : 1 < n) :
    (attainableCounts d n).Nonempty := by
  let A := segmentConfiguration hd hn
  exact ⟨diameterPairCount A, A, card_segmentConfiguration hd hn,
    isDiameterOne_segmentConfiguration hd hn, rfl⟩

/-- The finite maximum defining `f` is attained. -/
theorem exists_diameterPairCount_eq_f (d n : ℕ) (hd : 0 < d) (hn : 1 < n) :
    ∃ A : Finset (Point d),
      A.card = n ∧ IsDiameterOne A ∧ diameterPairCount A = f d n := by
  exact Nat.sSup_mem (attainableCounts_nonempty d n hd hn)
    (attainableCounts_bddAbove d n)

/-- Universal upper-bound interface: it suffices to bound all diameter-one
configurations of the prescribed cardinality. -/
theorem f_le_of_forall {d n B : ℕ} (hd : 0 < d) (hn : 1 < n)
    (h : ∀ A : Finset (Point d),
      A.card = n → IsDiameterOne A → diameterPairCount A ≤ B) :
    f d n ≤ B := by
  obtain ⟨A, hAcard, hA, hcount⟩ := exists_diameterPairCount_eq_f d n hd hn
  rw [← hcount]
  exact h A hAcard hA

/-! ## Two-point configurations -/

/-- A two-point diameter-one configuration has exactly one diameter pair. -/
theorem diameterPairCount_eq_one_of_card_eq_two {d : ℕ}
    {A : Finset (Point d)} (hAcard : A.card = 2) (hA : IsDiameterOne A) :
    diameterPairCount A = 1 := by
  apply Nat.le_antisymm
  · simpa [hAcard] using diameterPairCount_le_choose A
  · obtain ⟨x, hx, y, hy, hxy⟩ := hA.exists_dist_eq_one
    have hxy_ne : x ≠ y := by
      intro h
      subst y
      simpa using hxy
    let xs : {z // z ∈ A} := ⟨x, hx⟩
    let ys : {z // z ∈ A} := ⟨y, hy⟩
    have hadj : (diameterGraph A).Adj xs ys := by
      exact hxy
    have hedge : s(xs, ys) ∈ (diameterGraph A).edgeFinset := by
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hadj
    exact Finset.card_pos.mpr ⟨s(xs, ys), hedge⟩

/-- The exact two-point value in every positive dimension. -/
theorem f_two (d : ℕ) (hd : 0 < d) : f d 2 = 1 := by
  apply Nat.le_antisymm
  · apply f_le_of_forall (d := d) (n := 2) (B := 1) hd (by norm_num)
    intro A hAcard hA
    exact (diameterPairCount_eq_one_of_card_eq_two hAcard hA).le
  · let A := segmentConfiguration hd (show 1 < 2 by norm_num)
    have hcount : diameterPairCount A = 1 :=
      diameterPairCount_eq_one_of_card_eq_two
        (card_segmentConfiguration hd (by norm_num))
        (isDiameterOne_segmentConfiguration hd (by norm_num))
    exact hcount ▸ diameterPairCount_le_f
      (card_segmentConfiguration hd (by norm_num))
      (isDiameterOne_segmentConfiguration hd (by norm_num))

end Erdos223
