/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# A zonotope rounding lemma

This file proves the elementary probabilistic-rounding lemma used in the
zonotope argument of Conlon--Fox--Pham and Pham--Zakharov.  The proof is
deterministic: at each generator we choose the endpoint whose squared-error
energy is at most the corresponding convex average.
-/

open scoped BigOperators

namespace Erdos186.Zonotope

set_option autoImplicit false

/-- The sum of the squared coordinates of a finite-dimensional real vector. -/
def energy {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

/-- A one-generator rounding step.  One of the two endpoint choices increases
the squared-error energy by at most `c * (1-c)` times the generator energy. -/
lemma one_step_rounding {d : ℕ} (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (e v : Fin d → ℝ) :
    energy (fun i ↦ e i + c * v i) ≤ energy e + c * (1 - c) * energy v ∨
      energy (fun i ↦ e i - (1 - c) * v i) ≤
        energy e + c * (1 - c) * energy v := by
  let E₀ := energy (fun i ↦ e i + c * v i)
  let E₁ := energy (fun i ↦ e i - (1 - c) * v i)
  let E := energy e + c * (1 - c) * energy v
  have havg : (1 - c) * E₀ + c * E₁ = E := by
    simp only [E₀, E₁, E, energy, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rcases le_total E₀ E₁ with hle | hle
  · left
    change E₀ ≤ E
    rw [← havg]
    nlinarith [mul_nonneg hc₀ (sub_nonneg.mpr hle)]
  · right
    change E₁ ≤ E
    rw [← havg]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc₁) (sub_nonneg.mpr hle)]

/-- The squared error of rounding the coefficients on `s` to the indicator of
the subset `t`. -/
def roundingError {d : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → Fin d → ℝ) (t : Finset ι) : ℝ :=
  energy fun i ↦ (∑ a ∈ s, c a * v a i) - ∑ a ∈ t, v a i

/-- Independent rounding in squared-error form.  This is the usual
expectation bound, proved here by conditional-expectation induction and hence
without a probability-space API. -/
theorem exists_rounding_energy {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) (v : ι → Fin d → ℝ)
    (hc : ∀ a ∈ s, 0 ≤ c a ∧ c a ≤ 1) :
    ∃ t : Finset ι, t ⊆ s ∧
      roundingError s c v t ≤
        ∑ a ∈ s, c a * (1 - c a) * energy (v a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨∅, Finset.Subset.rfl, ?_⟩
      simp [roundingError, energy]
  | @insert a s ha ih =>
      have hca := hc a (Finset.mem_insert_self a s)
      have hcs : ∀ b ∈ s, 0 ≤ c b ∧ c b ≤ 1 := by
        intro b hb
        exact hc b (Finset.mem_insert_of_mem hb)
      obtain ⟨t, hts, ht⟩ := ih hcs
      let e : Fin d → ℝ := fun i ↦
        (∑ b ∈ s, c b * v b i) - ∑ b ∈ t, v b i
      rcases one_step_rounding (c a) hca.1 hca.2 e (v a) with hzero | hone
      · refine ⟨t, ?_, ?_⟩
        · exact hts.trans (Finset.subset_insert a s)
        · calc
            roundingError (insert a s) c v t =
                energy (fun i ↦ e i + c a * v a i) := by
              unfold roundingError
              congr 1
              funext i
              rw [Finset.sum_insert ha]
              dsimp only [e]
              ring
            _ ≤ energy e + c a * (1 - c a) * energy (v a) := hzero
            _ ≤ ∑ b ∈ insert a s, c b * (1 - c b) * energy (v b) := by
              rw [Finset.sum_insert ha]
              change roundingError s c v t + _ ≤ _
              linarith
      · refine ⟨insert a t, ?_, ?_⟩
        · exact Finset.insert_subset (Finset.mem_insert_self a s)
            (hts.trans (Finset.subset_insert a s))
        · have hat : a ∉ t := fun hat ↦ ha (hts hat)
          calc
            roundingError (insert a s) c v (insert a t) =
                energy (fun i ↦ e i - (1 - c a) * v a i) := by
              unfold roundingError
              congr 1
              funext i
              rw [Finset.sum_insert ha, Finset.sum_insert hat]
              dsimp only [e]
              ring
            _ ≤ energy e + c a * (1 - c a) * energy (v a) := hone
            _ ≤ ∑ b ∈ insert a s, c b * (1 - c b) * energy (v b) := by
              rw [Finset.sum_insert ha]
              change roundingError s c v t + _ ≤ _
              linarith

/-- Coordinatewise form of `exists_rounding_energy`.  If every coordinate of
every generator has absolute value at most `width`, then the rounded subset
sum is within `sqrt (d * |s|) * width` in every coordinate. -/
theorem exists_subset_sum_approximation {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) (v : ι → Fin d → ℝ) (width : ℝ)
    (hc : ∀ a ∈ s, 0 ≤ c a ∧ c a ≤ 1) (hwidth : 0 ≤ width)
    (hv : ∀ a ∈ s, ∀ i, |v a i| ≤ width) :
    ∃ t : Finset ι, t ⊆ s ∧ ∀ i,
      |(∑ a ∈ s, c a * v a i) - ∑ a ∈ t, v a i| ≤
        Real.sqrt (((d * s.card : ℕ) : ℝ)) * width := by
  classical
  obtain ⟨t, hts, ht⟩ := exists_rounding_energy s c v hc
  refine ⟨t, hts, ?_⟩
  have henergy (a : ι) (ha : a ∈ s) :
      energy (v a) ≤ (d : ℝ) * width ^ 2 := by
    unfold energy
    calc
      (∑ i, (v a i) ^ 2) ≤ ∑ _i : Fin d, width ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hsquare := (sq_le_sq₀ (abs_nonneg (v a i)) hwidth).2 (hv a ha i)
        simpa only [sq_abs] using hsquare
      _ = (d : ℝ) * width ^ 2 := by simp
  have htotal :
      (∑ a ∈ s, c a * (1 - c a) * energy (v a)) ≤
        (((d * s.card : ℕ) : ℝ)) * width ^ 2 := by
    calc
      (∑ a ∈ s, c a * (1 - c a) * energy (v a)) ≤
          ∑ _a ∈ s, (d : ℝ) * width ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hca := hc a ha
        have hfactor_nonneg : 0 ≤ c a * (1 - c a) :=
          mul_nonneg hca.1 (sub_nonneg.mpr hca.2)
        have hfactor_le : c a * (1 - c a) ≤ 1 := by
          nlinarith [hca.1, hca.2, sq_nonneg (c a)]
        calc
          c a * (1 - c a) * energy (v a) ≤ energy (v a) := by
            apply mul_le_of_le_one_left
            · unfold energy
              exact Finset.sum_nonneg fun i hi ↦ sq_nonneg (v a i)
            · exact hfactor_le
          _ ≤ (d : ℝ) * width ^ 2 := henergy a ha
      _ = (((d * s.card : ℕ) : ℝ)) * width ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        push_cast
        ring
  intro i
  let err : ℝ := (∑ a ∈ s, c a * v a i) - ∑ a ∈ t, v a i
  have herr_energy : err ^ 2 ≤ roundingError s c v t := by
    unfold roundingError energy
    exact Finset.single_le_sum (fun j hj ↦ sq_nonneg
      ((∑ a ∈ s, c a * v a j) - ∑ a ∈ t, v a j)) (Finset.mem_univ i)
  have herr_sq : err ^ 2 ≤ (((d * s.card : ℕ) : ℝ)) * width ^ 2 :=
    herr_energy.trans (ht.trans htotal)
  change |err| ≤ Real.sqrt (((d * s.card : ℕ) : ℝ)) * width
  apply (sq_le_sq₀ (abs_nonneg err)
    (mul_nonneg (Real.sqrt_nonneg _) hwidth)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (d * s.card))]
  exact herr_sq

/-- A point of the zonotope generated by the integer vectors in `A`. -/
def IsZonotopePoint {d : ℕ} (A : Finset (Fin d → ℤ)) (x : Fin d → ℝ) : Prop :=
  ∃ c : (Fin d → ℤ) → ℝ,
    (∀ a ∈ A, 0 ≤ c a ∧ c a ≤ 1) ∧
      ∀ i, x i = ∑ a ∈ A, c a * (a i : ℝ)

/-- **Zonotope rounding lemma.**  A point in the zonotope generated by a
finite set `A` of integer vectors lying in an axis box of half-width `width`
has a subset-sum approximant with coordinate error at most
`sqrt (d * |A|) * width`. -/
theorem zonotope_rounding {d : ℕ} (A : Finset (Fin d → ℤ))
    (x : Fin d → ℝ) (width : ℝ) (hx : IsZonotopePoint A x)
    (hwidth : 0 ≤ width)
    (hA : ∀ a ∈ A, ∀ i, |(a i : ℝ)| ≤ width) :
    ∃ B : Finset (Fin d → ℤ), B ⊆ A ∧ ∀ i,
      |x i - ∑ a ∈ B, (a i : ℝ)| ≤
        Real.sqrt (((d * A.card : ℕ) : ℝ)) * width := by
  classical
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨B, hBA, hB⟩ := exists_subset_sum_approximation A c
    (fun a i ↦ (a i : ℝ)) width hc hwidth hA
  refine ⟨B, hBA, ?_⟩
  intro i
  rw [hxc i]
  exact hB i

end Erdos186.Zonotope
