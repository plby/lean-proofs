import Wikipedia.NoExoticSixSphere.GramSchmidtIsometry
import Mathlib.Order.Interval.Finset.Fin

/-!
# Ordered Gram--Schmidt with a genuinely orthogonal leading column

Prepending a vector orthogonal to every original column leaves the
remaining ordered Gram--Schmidt columns unchanged. This is not a claim
that arbitrary source-column permutations commute with normalization.
-/

noncomputable section

open InnerProductSpace

namespace NoExoticSixSphere

theorem sum_Iio_fin_succ {A : Type*} [AddCommMonoid A] {n : ℕ}
    (f : Fin (n + 1) → A) (i : Fin n) :
    ∑ j ∈ Finset.Iio i.succ, f j = f 0 + ∑ j ∈ Finset.Iio i, f j.succ := by
  have he : Finset.Iio i.succ = insert 0 ((Finset.Iio i).map (Fin.succEmb n)) := by
    rw [Fin.map_succEmb_Iio]
    ext j
    simp only [Finset.mem_Iio, Finset.mem_insert, Finset.mem_Ioo,
      Fin.lt_def, Fin.ext_iff, Fin.val_zero, Fin.val_succ]
    omega
  have hz : (0 : Fin (n + 1)) ∉ (Finset.Iio i).map (Fin.succEmb n) := by
    rw [Fin.map_succEmb_Iio]
    simp
  rw [he, Finset.sum_insert hz, Finset.sum_map]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ}

theorem gramSchmidt_fin_cons_zero (z : E) (v : Fin n → E) :
    gramSchmidt ℝ (Fin.cons z v) 0 = z := by
  change gramSchmidt ℝ (Fin.cons z v) (⊥ : Fin (n + 1)) = z
  rw [gramSchmidt_bot]
  rfl

theorem gramSchmidt_fin_cons_succ (z : E) (v : Fin n → E)
    (hz : ∀ j, inner ℝ z (v j) = 0) (i : Fin n) :
    gramSchmidt ℝ (Fin.cons z v) i.succ = gramSchmidt ℝ v i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hL := eq_sub_of_add_eq (gramSchmidt_def'' ℝ (Fin.cons z v) i.succ).symm
    have hR := eq_sub_of_add_eq (gramSchmidt_def'' ℝ v i).symm
    rw [hL, hR, sum_Iio_fin_succ]
    simp only [Fin.cons_succ, gramSchmidt_fin_cons_zero, hz, zero_div, zero_smul, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_Iio.mp hj)]

theorem gramSchmidtNormed_fin_cons_zero (z : E) (v : Fin n → E) :
    gramSchmidtNormed ℝ (Fin.cons z v) 0 = ‖z‖⁻¹ • z := by
  simp only [gramSchmidtNormed, gramSchmidt_fin_cons_zero]
  rfl

theorem gramSchmidtNormed_fin_cons_succ (z : E) (v : Fin n → E)
    (hz : ∀ j, inner ℝ z (v j) = 0) (i : Fin n) :
    gramSchmidtNormed ℝ (Fin.cons z v) i.succ = gramSchmidtNormed ℝ v i := by
  simp only [gramSchmidtNormed, gramSchmidt_fin_cons_succ z v hz]

end NoExoticSixSphere
