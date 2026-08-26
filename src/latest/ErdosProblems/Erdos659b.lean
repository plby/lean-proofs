/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is an alternative Lean formalization of a solution to Erdős Problem 659.
https://www.erdosproblems.com/forum/thread/659

Formalization status:
- Unconditional; checked at default computational limits

Informal authors:
- Benjamin Grayzel
- Adam Sheffer
- Pieter Moree
- Robert Osburn
- Desmond Weisenberg
- Gemini

Statement authors:
- Formal Conjectures authors

Formal authors:
- Aristotle
- Boris Alexeev
- Codex

URLs:
- https://adamsheffer.wordpress.com/2014/07/16/point-sets-with-few-distinct-distances/
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos659.md
-/
/-
We formalized the solution to the Erdős problem concerning distances and points.
We defined the lattice `L` and the point sets `P_m`.
We proved that `P_m` satisfies the local constraint (every 4 points determine at least 3 distances)
by reducing it to the absence of squares, equilateral triangles, and golden ratio distances in `L`,
which we verified.
The squared Euclidean distances in `P_m` are positive integers represented by
`x^2 + 2y^2`. The companion `Erdos659b.Counting` module proves their counting
function is `O(X / sqrt(log X))`, using the Halberstam–Richert mean-value bound
and the Euler product of the quadratic character modulo eight. This upper
bound suffices; Bernays' full asymptotic theorem is not assumed.

Perucca's classification theorem is proved as `PeruccaClassificationStatement_proof`.
-/

import ErdosProblems.Erdos659.Geometry
import ErdosProblems.Erdos659b.Counting

open Filter Asymptotics EuclideanGeometry Finset Real
open scoped Real

namespace Erdos659b

open Erdos659

/-- The number of distinct distances between unequal pairs of points. -/
noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  (points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2).card

private theorem distinctDistances_eq (points : Finset ℝ²) :
    distinctDistances points = Erdos659.distinctDistances points := rfl

/-- The distance-count estimate with zero excluded, so only the upper-bound
counting theorem for positive represented values is needed. -/
lemma distinctDistances_euc_bound_values (m : ℕ) :
    (distinctDistances'_euc (P m)).card ≤ (Counting.values (3 * m ^ 2)).card := by
  classical
  have hsub : distinctDistances'_euc (P m) ⊆
      (Counting.values (3 * m ^ 2)).image (fun n : ℕ => Real.sqrt n) := by
    intro d hd
    have hdpos := distinctDistances_euc_pos hd
    rcases mem_distinctDistances_euc.mp hd with ⟨p, hp, q, hq, hne, rfl⟩
    obtain ⟨u, v, hu, hv, heq⟩ := P_dist_sq_form m p q hp hq
    let n := u.natAbs ^ 2 + 2 * v.natAbs ^ 2
    have hni : (n : ℤ) = u ^ 2 + 2 * v ^ 2 := by
      simp [n, sq_abs]
    have hncast : (n : ℝ) = (dist_euc p q) ^ 2 := by
      rw [heq]
      exact_mod_cast hni
    have hnpos : 0 < n := by
      by_contra hn
      have hnzero : n = 0 := by omega
      rw [hnzero, Nat.cast_zero] at hncast
      nlinarith only [hncast, hdpos]
    have huN : u.natAbs ≤ m := by
      rw [← Int.natCast_natAbs] at hu
      exact_mod_cast hu.le
    have hvN : v.natAbs ≤ m := by
      rw [← Int.natCast_natAbs] at hv
      exact_mod_cast hv.le
    have hnle : n ≤ 3 * m ^ 2 := by
      dsimp [n]
      nlinarith only [Nat.pow_le_pow_left huN 2, Nat.pow_le_pow_left hvN 2]
    apply Finset.mem_image.mpr
    refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnpos, hnle⟩,
      u.natAbs, v.natAbs, rfl⟩, ?_⟩
    rw [hncast, Real.sqrt_sq hdpos.le]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma distinctDistances_euc_mono {S T : Finset (ℝ × ℝ)} (h : S ⊆ T) :
    distinctDistances'_euc S ⊆ distinctDistances'_euc T := by
  intro d hd
  rcases mem_distinctDistances_euc.mp hd with ⟨p, hp, q, hq, hne, he⟩
  exact mem_distinctDistances_euc.mpr ⟨p, h hp, q, h hq, hne, he⟩

/-- Existence follows from the unconditional upper bound for `x² + 2y²`;
no asymptotic equivalence for binary quadratic forms is assumed. -/
theorem main_theorem (h_perucca : PeruccaClassificationStatement) :
    ∃ (P : ℕ → Finset (ℝ × ℝ)),
      (∀ n, (P n).card = n) ∧
      (∀ n, n ≥ 4 → ∀ S, S ⊆ P n → S.card = 4 →
        (distinctDistances'_euc S).card ≥ 3) ∧
      (Asymptotics.IsBigO Filter.atTop (fun n => ((distinctDistances'_euc (P n)).card : ℝ))
        (fun n => (n : ℝ) / Real.sqrt (Real.log n))) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := Counting.exists_count_le
  refine ⟨P_seq, fun n => (P_seq_spec n).1, ?_, ?_⟩
  · intro n _ S hS hcard
    exact P_local_constraint (m_of_n n) h_perucca S
      (hS.trans (P_seq_spec n).2) hcard
  · apply Asymptotics.IsBigO.of_bound (12 * C)
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn
    have hscale : 3 * (m_of_n n) ^ 2 ≤ 12 * n := by
      dsimp [m_of_n]
      nlinarith only [Nat.sqrt_le' n, Nat.sqrt_le_self n, hn]
    have hvalues : Counting.values (3 * (m_of_n n) ^ 2) ⊆ Counting.values (12 * n) := by
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hk, hrep⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hscale⟩, hrep⟩
    have hcount : (distinctDistances'_euc (P_seq n)).card ≤
        (Counting.values (12 * n)).card :=
      (Finset.card_le_card (distinctDistances_euc_mono (P_seq_spec n).2)).trans
        ((distinctDistances_euc_bound_values (m_of_n n)).trans (Finset.card_le_card hvalues))
    have hlog : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr (Real.log_pos hnR)
    have hroot : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (12 * n : ℕ)) := by
      apply Real.sqrt_le_sqrt
      apply Real.log_le_log (by positivity)
      norm_num
      linarith
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
    calc
      ((distinctDistances'_euc (P_seq n)).card : ℝ) ≤ (Counting.values (12 * n)).card :=
        Nat.cast_le.mpr hcount
      _ ≤ C * (12 * n : ℕ) / Real.sqrt (Real.log (12 * n : ℕ)) := hC _ (by omega)
      _ ≤ C * (12 * n : ℕ) / Real.sqrt (Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hlog hroot
      _ = (12 * C) * ((n : ℝ) / Real.sqrt (Real.log (n : ℝ))) := by push_cast; ring

/--
Is there a set of $n$ points in $\mathbb{R}^2$ such that every subset of $4$ points determines at
least $3$ distances, yet the total number of distinct distances is $\ll \frac{n}{\sqrt{\log n}}$?
-/
theorem erdos_659 : ∃ A : ℕ → Finset ℝ²,
   (∀ n, #(A n) = n ∧ ∀ S ⊆ A n, #S = 4 → 3 ≤ distinctDistances S) ∧
    (fun n ↦ distinctDistances (A n)) ≪ fun n ↦ n / sqrt (log n) := by
  obtain ⟨P, hP_card, hP_local, hP_bigO⟩ :=
    main_theorem PeruccaClassificationStatement_proof
  refine ⟨fun n => (P n).image toEuclideanPoint, ?_, ?_⟩
  · intro n
    constructor
    · rw [Finset.card_image_of_injective _ toEuclideanPoint_injective, hP_card n]
    · intro S hS hS_card
      have hA_card : ((P n).image toEuclideanPoint).card = n := by
        rw [Finset.card_image_of_injective _ toEuclideanPoint_injective, hP_card n]
      have hn : n ≥ 4 := by
        have hle := Finset.card_le_card hS
        rw [hA_card, hS_card] at hle
        omega
      let S' : Finset (ℝ × ℝ) := (P n).filter (fun p => toEuclideanPoint p ∈ S)
      have hS'_subset : S' ⊆ P n := by
        intro p hp
        exact (Finset.mem_filter.mp hp).1
      have hS_image : S'.image toEuclideanPoint = S := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
          exact (Finset.mem_filter.mp hp).2
        · intro hx
          have hxA : x ∈ (P n).image toEuclideanPoint := hS hx
          rcases Finset.mem_image.mp hxA with ⟨p, hp, rfl⟩
          exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hx⟩, rfl⟩
      have hS'_card : S'.card = 4 := by
        rw [← hS_card, ← hS_image,
          Finset.card_image_of_injective _ toEuclideanPoint_injective]
      have hdist := hP_local n hn S' hS'_subset hS'_card
      rw [distinctDistances_eq, ← hS_image, distinctDistances_image_toEuclideanPoint]
      exact hdist
  · simpa only [distinctDistances_eq, distinctDistances_image_toEuclideanPoint] using hP_bigO

#print axioms erdos_659
-- 'Erdos659b.erdos_659' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos659b
