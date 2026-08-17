/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization of the negative resolution of Erdős Problem 664.

The construction is the random half-line construction of Alon, Kalai,
Matoušek, and Meshulam.  We use the affine part of a Desarguesian projective
plane; this has the same linear-size, codegree-one, and incidence-regularity
properties needed by the argument.
-/

import ErdosProblems.Erdos664.Analysis

namespace Erdos664

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- For every proposed uniform intersection bound, the random half-line
construction supplies a counterexample. -/
theorem counterexampleAt (K : ℕ) : CounterexampleAt K := by
  let u := K + 1
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 (eventually_error_sum_lt_one u)
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (max Q 2)
  have hQq : Q ≤ q := (le_max_left Q 2).trans hq
  have hq2 : 2 ≤ q := (le_max_right Q 2).trans hq
  have herr := hQ q hQq
  letI : Fact (Nat.Prime q) := ⟨hprime⟩
  letI : DecidableEq (ZMod q) := Classical.decEq (ZMod q)
  let P := ZMod q × ZMod q
  let L := AffineLine (ZMod q)
  let A₀ : L → Finset P := affineLinePoints
  let μ : Measure (L → P → Bool) := fairMatrixMeasure L P
  let E₁ : Set (L → P → Bool) :=
    {ω | ∃ l, (#(selectedSet A₀ ω l) : ℝ) ≤ (2 / 5 : ℝ) * #(A₀ l)}
  let E₂ : Set (L → P → Bool) :=
    {ω | ∃ p, (selectedDegree A₀ ω p : ℝ) ≤
      (1 / 4 : ℝ) * #(incidenceSet A₀ p)}
  let E₃ : Set (L → P → Bool) :=
    {ω | HasSmallTransversal A₀ (4 * q * u) ω}
  have hE₁ : μ.real E₁ ≤
      (((q : ℝ) ^ 2 + q) * Real.exp (-(q : ℝ) / 50)) := by
    calc
      μ.real E₁ ≤ ∑ l : L, Real.exp (-(#(A₀ l) : ℝ) / 50) := by
        exact fairMatrix_exists_small_selectedSet A₀
      _ = _ := by
        simp [A₀, L, P, card_affineLinePoints, card_affineLineType, ZMod.card,
          pow_two]
  have hE₂ : μ.real E₂ ≤
      ((q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 8)) := by
    have hinc (p : P) : #(incidenceSet A₀ p) = q + 1 := by
      calc
        #(incidenceSet A₀ p) = #(affineLinesThrough p) := by
          congr 1
          ext l
          simp only [incidenceSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (mem_affineLinesThrough_iff p l).symm
        _ = q + 1 := by rw [card_affineLinesThrough, ZMod.card]
    calc
      μ.real E₂ ≤ ∑ p : P, Real.exp (-(#(incidenceSet A₀ p) : ℝ) / 8) := by
        simpa [μ, E₂] using fairMatrix_exists_small_selectedDegree A₀
      _ = (q : ℝ) ^ 2 * Real.exp (-((q : ℝ) + 1) / 8) := by
        simp_rw [hinc]
        simp [P, ZMod.card, pow_two]
      _ ≤ (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 8) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_le_exp.mpr
          linarith
        · positivity
  have hE₃ : μ.real E₃ ≤
      ((q : ℝ) ^ 2) ^ (4 * q * u) *
        Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) *
          (((q : ℝ) ^ 2 + q) / 2)) := by
    simpa [μ, E₃, A₀, L, P, card_affinePointType, card_affineLineType,
      ZMod.card, pow_two] using
        (fairMatrix_affine_hasSmallTransversal_bound (F := ZMod q) u)
  have hbad : μ.real ((E₁ ∪ E₂) ∪ E₃) < 1 := by
    calc
      μ.real ((E₁ ∪ E₂) ∪ E₃) ≤ μ.real (E₁ ∪ E₂) + μ.real E₃ :=
        measureReal_union_le _ _
      _ ≤ (μ.real E₁ + μ.real E₂) + μ.real E₃ := by
        gcongr
        exact measureReal_union_le _ _
      _ ≤ (((q : ℝ) ^ 2 + q) * Real.exp (-(q : ℝ) / 50)) +
          ((q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 8)) +
          ((q : ℝ) ^ 2) ^ (4 * q * u) *
            Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) *
              (((q : ℝ) ^ 2 + q) / 2)) := by linarith
      _ < 1 := herr
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ (E₁ ∪ E₂) ∪ E₃ := by
    by_contra hn
    have hall : ∀ ω, ω ∈ (E₁ ∪ E₂) ∪ E₃ := by
      intro ω
      by_contra hnot
      exact hn ⟨ω, hnot⟩
    have heq : (E₁ ∪ E₂) ∪ E₃ = Set.univ := Set.eq_univ_of_forall hall
    rw [heq] at hbad
    simpa [μ] using hbad
  have hgood₁ : ∀ l : L,
      (2 / 5 : ℝ) * #(A₀ l) < #(selectedSet A₀ ω l) := by
    intro l
    apply lt_of_not_ge
    intro hle
    exact hω (Or.inl (Or.inl ⟨l, hle⟩))
  have hgood₂ : ∀ p : P,
      (1 / 4 : ℝ) * #(incidenceSet A₀ p) < selectedDegree A₀ ω p := by
    intro p
    apply lt_of_not_ge
    intro hle
    exact hω (Or.inl (Or.inr ⟨p, hle⟩))
  have hgood₃ : ¬HasSmallTransversal A₀ (4 * q * u) ω := by
    intro h
    exact hω (Or.inr h)
  let n := Fintype.card P
  let m := Fintype.card L
  let eP : P ≃ Fin n := Fintype.equivFin P
  let eL : L ≃ Fin m := Fintype.equivFin L
  let A : Fin m → Finset (Fin n) := fun i =>
    (selectedSet A₀ ω (eL.symm i)).map eP.toEmbedding
  refine ⟨n, m, A, ?_, ?_, ?_⟩
  · intro i
    have hn : n = q ^ 2 := by simp [n, P, ZMod.card, pow_two]
    have hsqrt : Real.sqrt (n : ℝ) = q := by
      rw [hn]
      push_cast
      rw [Real.sqrt_sq_eq_abs]
      simp
    rw [hsqrt]
    have hbase : #(A₀ (eL.symm i)) = q := by
      change #(affineLinePoints (eL.symm i)) = q
      rw [card_affineLinePoints, ZMod.card]
    have hi := hgood₁ (eL.symm i)
    rw [hbase] at hi
    simpa [A] using hi
  · intro i j hij
    have hlines : eL.symm i ≠ eL.symm j := by
      intro h
      apply hij
      exact eL.symm.injective h
    let S := selectedSet A₀ ω (eL.symm i)
    let T := selectedSet A₀ ω (eL.symm j)
    have hmap : S.map eP.toEmbedding ∩ T.map eP.toEmbedding =
        (S ∩ T).map eP.toEmbedding := by
      ext x
      simp
    rw [show A i = S.map eP.toEmbedding by rfl,
      show A j = T.map eP.toEmbedding by rfl, hmap, Finset.card_map]
    rw [Finset.card_le_one_iff]
    intro p r hp hr
    have hbase := affineLinePoints_inter_card_le_one hlines
    rw [Finset.card_le_one_iff] at hbase
    apply hbase
    · have hp' : p ∈ selectedSet A₀ ω (eL.symm i) ∩
          selectedSet A₀ ω (eL.symm j) := by simpa [S, T] using hp
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hp').1).1,
          (Finset.mem_filter.mp (Finset.mem_inter.mp hp').2).1⟩
    · have hr' : r ∈ selectedSet A₀ ω (eL.symm i) ∩
          selectedSet A₀ ω (eL.symm j) := by simpa [S, T] using hr
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hr').1).1,
          (Finset.mem_filter.mp (Finset.mem_inter.mp hr').2).1⟩
  · intro B hB
    let C : Finset P := B.map eP.symm.toEmbedding
    have hC : ∀ l : L, (C ∩ selectedSet A₀ ω l).Nonempty := by
      intro l
      obtain ⟨x, hx⟩ := hB (eL l)
      obtain ⟨hxB, hxA⟩ := Finset.mem_inter.mp hx
      refine ⟨eP.symm x, ?_⟩
      rw [Finset.mem_inter]
      constructor
      · simp [C, hxB]
      · simpa [A] using hxA
    have hdeg : ∀ p : P,
        (1 / 4 : ℝ) * (q + 1) < selectedDegree A₀ ω p := by
      intro p
      have hinc : #(incidenceSet A₀ p) = q + 1 := by
        calc
          #(incidenceSet A₀ p) = #(affineLinesThrough p) := by
            congr 1
            ext l
            simp only [incidenceSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact (mem_affineLinesThrough_iff p l).symm
          _ = q + 1 := by rw [card_affineLinesThrough, ZMod.card]
      simpa [hinc] using hgood₂ p
    obtain ⟨l, hl⟩ := native_intersection_unbounded (F := ZMod q) K ω
      (by simpa [P, A₀, ZMod.card] using hdeg)
      (by simpa [A₀, u] using hgood₃) C hC
    refine ⟨eL l, ?_⟩
    have hmap :
        (C ∩ selectedSet A₀ ω l).map eP.toEmbedding = B ∩ A (eL l) := by
      ext x
      simp [C, A]
    rw [← hmap, Finset.card_map]
    exact hl

/-- Counterexamples exist against every proposed constant intersection bound. -/
theorem erdos_664_counterexamples : ∀ K : ℕ, CounterexampleAt K := counterexampleAt

/-- Negative resolution of Erdős Problem 664 at the fixed constant `2/5 < 1`. -/
theorem erdos_664 : ¬∃ K : ℕ, HasUniformTransversalBound (2 / 5 : ℝ) K := by
  rintro ⟨K, hK⟩
  obtain ⟨n, m, A, hsize, hlinear, hunbounded⟩ := counterexampleAt K
  obtain ⟨B, hhit, hbound⟩ := hK n m A hsize hlinear
  obtain ⟨i, hi⟩ := hunbounded B hhit
  exact (Nat.not_lt_of_ge (hbound i)) hi

#print axioms erdos_664

end Erdos664
