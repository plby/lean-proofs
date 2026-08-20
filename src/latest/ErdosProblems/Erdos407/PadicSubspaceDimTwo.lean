/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.PadicSubspaceDefs

/-!
# An elementary two-dimensional special case of the three-place inequality

The general two-dimensional statement for unrelated nonsingular bases at the
three places is the rational p-adic Roth theorem.  This file proves the
elementary place-independent integral-basis case.  It includes, in particular,
using the same two forms chosen from `X`, `Y`, and `X + Y` at all three places.

The key point is that the product of the Archimedean, `2`-adic, and `3`-adic
norms of a nonzero integer is at least one.  Consequently a solution on which
neither form vanishes has box height at most one; the two vanishing loci are
already proper rational hyperplanes.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators

/-- The restricted three-place norm product of a nonzero integer is at least
one.  The omitted local factors, at primes other than `2` and `3`, account for
the inequality. -/
theorem one_le_normProduct23_int {z : ℤ} (hz : z ≠ 0) :
    1 ≤ PadicProduct.normProduct23 (z : ℚ) := by
  let n : ℕ := z.natAbs
  let a : ℕ := padicValNat 2 n
  let b : ℕ := padicValNat 3 n
  have hn : n ≠ 0 := by simpa [n] using hz
  have h2 : 2 ^ a ∣ n := by
    simpa [a] using (pow_padicValNat_dvd (p := 2) (n := n))
  have h3 : 3 ^ b ∣ n := by
    simpa [b] using (pow_padicValNat_dvd (p := 3) (n := n))
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) :=
    (by norm_num : Nat.Coprime 2 3).pow a b
  have hdvd : 2 ^ a * 3 ^ b ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd h2 h3
  have hleN : 2 ^ a * 3 ^ b ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hleQ : ((2 ^ a * 3 ^ b : ℕ) : ℚ) ≤ n := by
    exact_mod_cast hleN
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [PadicProduct.normProduct23, PadicProduct.archNorm,
    padicNorm.eq_zpow_of_nonzero hzQ, padicNorm.eq_zpow_of_nonzero hzQ,
    padicValRat.of_int, padicValRat.of_int]
  change 1 ≤ |(z : ℚ)| * (2 : ℚ) ^ (-(a : ℤ)) * (3 : ℚ) ^ (-(b : ℤ))
  rw [show |(z : ℚ)| = (n : ℚ) by simp [n], zpow_neg, zpow_neg,
    zpow_natCast, zpow_natCast]
  have hden : (0 : ℚ) < (2 ^ a * 3 ^ b : ℕ) := by positivity
  rw [inv_eq_one_div, inv_eq_one_div]
  calc
    1 ≤ (n : ℚ) / ((2 ^ a * 3 ^ b : ℕ) : ℚ) :=
      (one_le_div hden).2 hleQ
    _ = (n : ℚ) * (1 / (2 : ℚ) ^ a) * (1 / (3 : ℚ) ^ b) := by
      push_cast
      field_simp

/-! ## Place-independent integral bases -/

/-- The rational linear form with a prescribed row of integral
coefficients. -/
def integralLinearForm (a : Fin 2 → ℤ) : RatLinearForm 2 where
  toFun y := ∑ j, (a j : ℚ) * y j
  map_add' y z := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  map_smul' q y := by
    simp only [Pi.smul_apply, smul_eq_mul]
    change (∑ j, (a j : ℚ) * (q * y j)) = q * ∑ j, (a j : ℚ) * y j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] theorem integralLinearForm_apply (a : Fin 2 → ℤ) (y : Fin 2 → ℚ) :
    integralLinearForm a y = ∑ j, (a j : ℚ) * y j :=
  rfl

/-- Integral evaluation of an integral row on an integral vector. -/
def integralFormValue (a : Fin 2 → ℤ) (x : Fin 2 → ℤ) : ℤ :=
  ∑ j, a j * x j

@[simp] theorem integralLinearForm_intCastVec
    (a : Fin 2 → ℤ) (x : Fin 2 → ℤ) :
    integralLinearForm a (intCastVec x) = (integralFormValue a x : ℚ) := by
  simp [integralLinearForm, integralFormValue, intCastVec]

/-- A pair of integral forms, with the same pair used at each of the three
places. -/
def constantIntegralFamily (A : Fin 2 → Fin 2 → ℤ) :
    Place23 → Fin 2 → RatLinearForm 2 :=
  fun _ i => integralLinearForm (A i)

private theorem prod_placeNorm_eq_normProduct23 (q : ℚ) :
    (∏ v : Place23, placeNorm v q) = PadicProduct.normProduct23 q := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [placeNorm, PadicProduct.normProduct23, PadicProduct.archNorm]
  ring

theorem localFormProduct_constantIntegralFamily
    (A : Fin 2 → Fin 2 → ℤ) (x : Fin 2 → ℤ) :
    localFormProduct (constantIntegralFamily A) (intCastVec x) =
      ∏ i, PadicProduct.normProduct23 (integralFormValue (A i) x : ℚ) := by
  unfold localFormProduct
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp only [constantIntegralFamily, integralLinearForm_intCastVec]
  exact prod_placeNorm_eq_normProduct23 _

private theorem constantIntegralFamily_row_ne_zero
    {A : Fin 2 → Fin 2 → ℤ}
    (hA : IsNonsingularFamily (constantIntegralFamily A)) (i : Fin 2) :
    (fun j => (A i j : ℚ)) ≠ 0 := by
  intro hrow
  have hform : integralLinearForm (A i) = 0 := by
    apply LinearMap.ext
    intro y
    change (∑ j, (A i j : ℚ) * y j) = 0
    apply Finset.sum_eq_zero
    intro j _
    have hj : (A i j : ℚ) = 0 := by simpa using congrFun hrow j
    simp [hj]
  exact (hA Place23.infinite).ne_zero i hform

private theorem zeroValues_haveFiniteHyperplaneCover
    {A : Fin 2 → Fin 2 → ℤ}
    (hA : IsNonsingularFamily (constantIntegralFamily A)) :
    HasFiniteHyperplaneCover
      {x : Fin 2 → ℤ | ∃ i, integralFormValue (A i) x = 0} := by
  classical
  let row : Fin 2 → Fin 2 → ℚ := fun i j => (A i j : ℚ)
  refine ⟨Finset.univ.image row, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hb
    exact constantIntegralFamily_row_ne_zero hA i
  · intro x hx
    obtain ⟨i, hi⟩ := hx
    refine ⟨row i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    simpa [OnHyperplane, row, integralFormValue] using congrArg ((↑) : ℤ → ℚ) hi

/-- A fully axiom-free two-dimensional finite-cover theorem for the strong
exponent in the place-independent integral-basis case.  Thus the local bases
are rational and nonsingular, but (unlike the full p-adic Subspace Theorem)
they are required to be the same integral basis at `infinity`, `2`, and `3`.

Away from the two kernel hyperplanes, every solution has box height at most
one. -/
theorem finiteCover_dimTwo_constantIntegralFamily
    {A : Fin 2 → Fin 2 → ℤ}
    (hA : IsNonsingularFamily (constantIntegralFamily A)) :
    HasFiniteHyperplaneCover
      (primitiveStrongSolutions (constantIntegralFamily A)) := by
  let Z : Set (Fin 2 → ℤ) :=
    {x | ∃ i, integralFormValue (A i) x = 0}
  let K : Set (Fin 2 → ℤ) :=
    {x | x ≠ 0 ∧ boxHeight x ≤ 1}
  have hZ : HasFiniteHyperplaneCover Z :=
    zeroValues_haveFiniteHyperplaneCover hA
  have hK : HasFiniteHyperplaneCover K :=
    bounded_hasFiniteHyperplaneCover (n := 2) (H := 1) (by omega)
  apply (hZ.union hK).mono
  intro x hx
  by_cases hz : ∃ i, integralFormValue (A i) x = 0
  · exact Or.inl hz
  · right
    refine ⟨hx.2.1, ?_⟩
    push Not at hz
    have hprod :
        1 ≤ localFormProduct (constantIntegralFamily A) (intCastVec x) := by
      rw [localFormProduct_constantIntegralFamily]
      exact Finset.one_le_prod fun i _ => one_le_normProduct23_int (hz i)
    have hheightQ : (boxHeight x : ℚ) ≤ 1 := by
      have hnonneg : (0 : ℚ) ≤ boxHeight x := by positivity
      have hleMul : (boxHeight x : ℚ) ≤
          localFormProduct (constantIntegralFamily A) (intCastVec x) * boxHeight x := by
        simpa using mul_le_mul_of_nonneg_right hprod hnonneg
      exact hleMul.trans hx.2.2
    exact_mod_cast hheightQ

/-! The coordinate basis is a concrete assumption-free instance. -/

/-- The `2 × 2` identity matrix, viewed as a pair of integral rows. -/
def coordinateMatrixTwo : Fin 2 → Fin 2 → ℤ :=
  fun i j => if i = j then 1 else 0

private theorem integralLinearForm_coordinateMatrixTwo (i : Fin 2) :
    integralLinearForm (coordinateMatrixTwo i) =
      GeneralPosition.coordinateForm i := by
  apply LinearMap.ext
  intro y
  simp [integralLinearForm, coordinateMatrixTwo,
    GeneralPosition.coordinateForm]

theorem coordinateMatrixTwo_nonsingular :
    IsNonsingularFamily (constantIntegralFamily coordinateMatrixTwo) := by
  intro v
  let e : Fin 2 → {j : GeneralPosition.FormIndex 2 // j ≠ none} :=
    fun i => ⟨some i, by simp⟩
  have he : Function.Injective e := by
    intro i j hij
    simpa [e] using congrArg Subtype.val hij
  have hli :=
    (GeneralPosition.coordSumForm_omit_linearIndependent 2 none).comp e he
  have hcoord : LinearIndependent ℚ
      (fun i : Fin 2 => GeneralPosition.coordinateForm i) := by
    simpa [e, Function.comp_def] using hli
  have heq : constantIntegralFamily coordinateMatrixTwo v =
      fun i : Fin 2 => GeneralPosition.coordinateForm i := by
    funext i
    exact integralLinearForm_coordinateMatrixTwo i
  rw [heq]
  exact hcoord

/-- For the coordinate basis at all three places, the primitive strong
solutions have a finite proper-hyperplane cover. -/
theorem finiteCover_dimTwo_coordinateFamily :
    HasFiniteHyperplaneCover
      (primitiveStrongSolutions
        (constantIntegralFamily coordinateMatrixTwo)) :=
  finiteCover_dimTwo_constantIntegralFamily coordinateMatrixTwo_nonsingular

#print axioms finiteCover_dimTwo_constantIntegralFamily
#print axioms finiteCover_dimTwo_coordinateFamily

end Erdos407.PadicSubspace
