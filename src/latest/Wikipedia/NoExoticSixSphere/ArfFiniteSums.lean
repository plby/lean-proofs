import Wikipedia.NoExoticSixSphere.ArfPlanes
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite orthogonal sums in the Arf calculation

The Gauss sum of a finite family of independent quadratic planes factors
into the plane Gauss sums. This gives the usual sum of pairwise products
whenever actual symplectic coordinates are provided.
-/

open scoped BigOperators

namespace NoExoticSixSphere.Arf

theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → F₂) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, sign_add, ih]

theorem gaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, Fintype (V i)]
    (q : ∀ i, V i → F₂) :
    gaussSum (fun x : ∀ i, V i ↦ ∑ i, q i (x i)) = ∏ i, gaussSum (q i) := by
  classical
  simp only [gaussSum, sign_sum]
  exact (Fintype.prod_sum (fun i x ↦ sign (q i x))).symm

theorem gaussSum_planes {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → F₂) :
    gaussSum (QuadraticMap.pi (fun i ↦ plane (a i) (b i))) =
      (2 : ℤ) ^ Fintype.card ι * sign (∑ i, a i * b i) := by
  have he : ⇑(QuadraticMap.pi (fun i ↦ plane (a i) (b i))) =
      fun x : ι → F₂ × F₂ ↦ ∑ i, plane (a i) (b i) (x i) :=
    funext (QuadraticMap.pi_apply _)
  rw [he, gaussSum_pi]
  simp_rw [gaussSum_plane]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, sign_sum]

theorem signParity_pos_mul_sign (z : ℤ) (hz : 0 < z) (a : F₂) :
    signParity (z * sign a) = a := by
  fin_cases a
  · change signParity (z * 1) = 0
    simp [signParity, not_lt_of_gt hz]
  · change signParity (z * (-1)) = 1
    simp [signParity, hz]

variable {V : Type*} [AddCommGroup V] [Module F₂ V]

theorem quadratic_sum_of_orthogonal (q : QuadraticForm F₂ V) {ι : Type*}
    (s : Finset ι) (v : ι → V)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → q.polarBilin (v i) (v j) = 0) :
    q (∑ i ∈ s, v i) = ∑ i ∈ s, q (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hrest : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → q.polarBilin (v j) (v k) = 0 :=
        fun j hj k hk hjk ↦ horth j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk
      have hp : q.polarBilin (v i) (∑ j ∈ s, v j) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
          (ne_of_mem_of_not_mem hj hi).symm
      rw [Finset.sum_insert hi, Finset.sum_insert hi, QuadraticMap.map_add q,
        ih hrest]
      change q (v i) + ∑ j ∈ s, q (v j) + q.polarBilin (v i) (∑ j ∈ s, v j) = _
      rw [hp, add_zero]

theorem quadratic_plane_formula (q : QuadraticForm F₂ (F₂ × F₂))
    (hcross : q.polarBilin (1, 0) (0, 1) = 1) (p : F₂ × F₂) :
    q p = plane (q (1, 0)) (q (0, 1)) p := by
  have hp : p = p.1 • (1, 0) + p.2 • (0, 1) := by ext <;> simp
  have hc : QuadraticMap.polar q (1, 0) (0, 1) = 1 := hcross
  conv_lhs => rw [hp, QuadraticMap.map_add q, q.map_smul, q.map_smul,
    q.polar_smul_left, q.polar_smul_right, hc]
  simp only [plane_apply, smul_eq_mul]
  ring

end NoExoticSixSphere.Arf
