import ErdosProblems.Erdos587.SqrtPhaseBounds

/-! Integral quadratic energies for a rectangularly scaled plane lattice. -/

namespace Erdos587

def latticeSizeSq (H J : ℕ) (p : ℤ × ℤ) : ℕ :=
  J ^ 2 * p.1.natAbs ^ 2 + H ^ 2 * p.2.natAbs ^ 2

noncomputable def latticeScaledSq (H J : ℝ) (p : ℤ × ℤ) : ℝ :=
  ((p.1 : ℝ) / H) ^ 2 + ((p.2 : ℝ) / J) ^ 2

noncomputable def latticeScaledInner (H J : ℝ) (p q : ℤ × ℤ) : ℝ :=
  ((p.1 : ℝ) / H) * ((q.1 : ℝ) / H) + ((p.2 : ℝ) / J) * ((q.2 : ℝ) / J)

lemma latticeSizeSq_cast (H J : ℕ) (p : ℤ × ℤ) :
    (latticeSizeSq H J p : ℝ) = (J : ℝ) ^ 2 * (p.1 : ℝ) ^ 2 + (H : ℝ) ^ 2 * (p.2 : ℝ) ^ 2 := by
  simp only [latticeSizeSq, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_natAbs, Int.cast_abs, sq_abs]

lemma latticeSizeSq_scaled {H J : ℕ} (hH : 0 < H) (hJ : 0 < J) (p : ℤ × ℤ) :
    (latticeSizeSq H J p : ℝ) = (H : ℝ) ^ 2 * (J : ℝ) ^ 2 * latticeScaledSq H J p := by
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  rw [latticeSizeSq_cast]
  unfold latticeScaledSq
  field_simp

lemma latticeScaledSq_nonneg (H J : ℝ) (p : ℤ × ℤ) : 0 ≤ latticeScaledSq H J p := by
  unfold latticeScaledSq
  positivity

lemma latticeScaledSq_pos {H J : ℝ} (hH : H ≠ 0) (hJ : J ≠ 0)
    {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < latticeScaledSq H J p := by
  have hcoord : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hp
    ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> tauto
  rcases hcoord with hx | hy
  · have hxR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hx
    have hh : 0 < ((p.1 : ℝ) / H) ^ 2 := sq_pos_of_ne_zero (div_ne_zero hxR hH)
    unfold latticeScaledSq
    linarith [sq_nonneg ((p.2 : ℝ) / J)]
  · have hyR : (p.2 : ℝ) ≠ 0 := by exact_mod_cast hy
    have hh : 0 < ((p.2 : ℝ) / J) ^ 2 := sq_pos_of_ne_zero (div_ne_zero hyR hJ)
    unfold latticeScaledSq
    linarith [sq_nonneg ((p.1 : ℝ) / H)]

end Erdos587
