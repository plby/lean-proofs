import ErdosProblems.Erdos587.CongruenceBasisImage

/-! Reversing signed image steps turns a centered lattice box into a positive-step rectangle. -/

namespace Erdos587

def signedBoxCoefficient (A : ℤ) (ell x : ℕ) : ℤ :=
  if 0 ≤ A then (x : ℤ) - ell else (ell : ℤ) - x

lemma signedBoxCoefficient_mul (A : ℤ) (ell x : ℕ) :
    signedBoxCoefficient A ell x * A = |A| * ((x : ℤ) - ell) := by
  by_cases hA : 0 ≤ A
  · simp only [signedBoxCoefficient, if_pos hA, abs_of_nonneg hA]
    ring
  · simp only [signedBoxCoefficient, if_neg hA, abs_of_neg (lt_of_not_ge hA)]
    ring

lemma signedBoxCoefficient_bound (A : ℤ) {ell x : ℕ} (hx : x ≤ 2 * ell) :
    |signedBoxCoefficient A ell x| ≤ ell := by
  rw [abs_le]
  unfold signedBoxCoefficient
  split_ifs <;> constructor <;> omega

lemma signedBoxCoefficient_injective (A : ℤ) (ell : ℕ) :
    Function.Injective (signedBoxCoefficient A ell) := by
  intro x y hxy
  unfold signedBoxCoefficient at hxy
  split_ifs at hxy <;> omega

theorem latticeCombination_injective {p q : ℤ × ℤ} (hdet : latticeDet p q ≠ 0)
    {m n m' n' : ℤ} (heq : latticeCombination m n p q = latticeCombination m' n' p q) :
    m = m' ∧ n = n' := by
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  dsimp only [latticeCombination] at hx hy
  have hm : (m - m') * latticeDet p q = 0 := by
    unfold latticeDet
    linear_combination q.2 * hx - q.1 * hy
  have hn : (n - n') * latticeDet p q = 0 := by
    unfold latticeDet
    linear_combination p.1 * hy - p.2 * hx
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_right hdet)⟩

def latticeBoxBase (g u v t : ℤ) (p q z : ℤ × ℤ) (ell₁ ell₂ : ℕ) : ℤ :=
  (t + latticeLinear u v z) / g -
    (ell₁ : ℤ) * |latticeLinear u v p / g| - (ell₂ : ℤ) * |latticeLinear u v q / g|

def positiveLatticeBoxPoint (g u v : ℤ) (p q z : ℤ × ℤ) (ell₁ ell₂ x y : ℕ) : ℤ × ℤ :=
  z + latticeCombination (signedBoxCoefficient (latticeLinear u v p / g) ell₁ x)
    (signedBoxCoefficient (latticeLinear u v q / g) ell₂ y) p q

theorem lattice_box_image_identity {g u v t : ℤ} {p q z : ℤ × ℤ}
    (hbasis : IsCongruenceBasis g u v p q) (hz : g ∣ t + latticeLinear u v z)
    (ell₁ ell₂ x y : ℕ) :
    g * (latticeBoxBase g u v t p q z ell₁ ell₂ +
      |latticeLinear u v p / g| * x + |latticeLinear u v q / g| * y) =
      t + latticeLinear u v (positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y) := by
  let A := latticeLinear u v p / g
  let B := latticeLinear u v q / g
  have hp : g * A = latticeLinear u v p := Int.mul_ediv_cancel' hbasis.first_mem
  have hq : g * B = latticeLinear u v q := Int.mul_ediv_cancel' hbasis.second_mem
  have hc := Int.mul_ediv_cancel' hz
  have hm := signedBoxCoefficient_mul A ell₁ x
  have hn := signedBoxCoefficient_mul B ell₂ y
  unfold positiveLatticeBoxPoint latticeBoxBase
  rw [latticeLinear_add, latticeLinear_combination]
  change g * ((t + latticeLinear u v z) / g - (ell₁ : ℤ) * |A| - (ell₂ : ℤ) * |B| +
      |A| * x + |B| * y) = t + (latticeLinear u v z +
      (signedBoxCoefficient A ell₁ x * latticeLinear u v p +
        signedBoxCoefficient B ell₂ y * latticeLinear u v q))
  rw [← hp, ← hq]
  calc
    _ = g * ((t + latticeLinear u v z) / g) +
        g * (|A| * ((x : ℤ) - ell₁)) + g * (|B| * ((y : ℤ) - ell₂)) := by ring
    _ = _ := by rw [hc, ← hm, ← hn]; ring

lemma positiveLatticeBoxPoint_injective {g u v : ℤ} {p q z : ℤ × ℤ}
    (hdet : latticeDet p q ≠ 0) (ell₁ ell₂ : ℕ) {x y x' y' : ℕ}
    (heq : positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y =
      positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x' y') : x = x' ∧ y = y' := by
  unfold positiveLatticeBoxPoint at heq
  have hh := latticeCombination_injective hdet (add_left_cancel heq)
  exact ⟨signedBoxCoefficient_injective _ _ hh.1, signedBoxCoefficient_injective _ _ hh.2⟩

end Erdos587
