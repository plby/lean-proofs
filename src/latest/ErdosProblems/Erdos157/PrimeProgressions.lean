import ErdosProblems.Erdos157.PrimePolynomialEstimate
import ErdosProblems.Erdos157.CharacterOrthogonality

/-! Elementary prime distribution in polynomial residue classes with odd unit group. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

noncomputable def primeProgressionCount (g : K[X]) (n : ℕ) (a : AdjoinRoot g) : ℕ :=
  Nat.card {p : PrimeDegree K n // AdjoinRoot.mk g p.1.1 = a}

theorem natCard_adjoinRoot (g : K[X]) (hg : g.Monic) :
    Nat.card (AdjoinRoot g) = Fintype.card K ^ g.natDegree := by
  calc
    _ = Nat.card (Fin g.natDegree → K) :=
      Nat.card_congr (AdjoinRoot.powerBasisAux' hg).equivFun.toEquiv
    _ = _ := by simp [Nat.card_eq_fintype_card]

theorem natCard_adjoinRoot_units_le (g : K[X]) (hg : g.Monic) :
    Nat.card (AdjoinRoot g)ˣ ≤ Fintype.card K ^ g.natDegree := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  rw [← natCard_adjoinRoot g hg]
  exact Nat.card_le_card_of_injective Units.val Units.val_injective

omit [DecidableEq K] [Fintype K] in
theorem isUnit_mk_of_isCoprime (g f : K[X]) (h : IsCoprime g f) :
    IsUnit (AdjoinRoot.mk g f) := by
  obtain ⟨b, c, hbc⟩ := h
  refine isUnit_iff_exists_inv'.mpr ⟨AdjoinRoot.mk g c, ?_⟩
  have hm := congrArg (AdjoinRoot.mk g) hbc
  simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] using hm

theorem isUnit_primeResidue (g : K[X]) (hg : g.Monic) {n : ℕ}
    (hn : g.natDegree < n) (p : PrimeDegree K n) : IsUnit (AdjoinRoot.mk g p.1.1) := by
  apply isUnit_mk_of_isCoprime
  apply IsCoprime.symm
  apply p.2.coprime_iff_not_dvd.mpr
  intro hdvd
  have hle := Polynomial.natDegree_le_of_dvd hdvd hg.ne_zero
  rw [p.1.natDegree] at hle
  omega

/-- An explicit residue-class error; no square-root cancellation is required. -/
theorem abs_primeProgression_count_error_le (g : K[X]) (hg : g.Monic)
    (hodd : Odd (Nat.card (AdjoinRoot g)ˣ)) (n : ℕ) (hn : g.natDegree < n)
    (a : (AdjoinRoot g)ˣ) :
    |(n : ℝ) * (Nat.card (AdjoinRoot g)ˣ : ℝ) * primeProgressionCount g n ↑a -
      (Fintype.card K : ℝ) ^ n| ≤
      (Nat.card (AdjoinRoot g)ˣ : ℝ) *
        ((g.natDegree : ℝ) * (Fintype.card K : ℝ) ^ n *
          Real.exp (-(n : ℝ) / (100 * (g.natDegree : ℝ))) +
        2 * (n : ℝ) * (n / 2 + 1 : ℕ) * (Fintype.card K : ℝ) ^ (n / 2)) := by
  classical
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  let : Fintype (AdjoinRoot g)ˣ := Fintype.ofFinite _
  let φ : ℝ := Nat.card (AdjoinRoot g)ˣ
  let q : ℝ := Fintype.card K
  let P : ℝ := (n : ℝ) * (n / 2 + 1 : ℕ) * q ^ (n / 2)
  let D : ℝ := (g.natDegree : ℝ) * q ^ n *
    Real.exp (-(n : ℝ) / (100 * (g.natDegree : ℝ)))
  have hφ : 1 ≤ φ := by
    dsimp only [φ]
    exact_mod_cast (Nat.succ_le_of_lt (Nat.card_pos (α := (AdjoinRoot g)ˣ)))
  have hP : 0 ≤ P := by dsimp only [P, q]; positivity
  have hD : 0 ≤ D := by dsimp only [D, q]; positivity
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have hf := character_fiber_error_le (fun p : PrimeDegree K n => AdjoinRoot.mk g p.1.1)
    (isUnit_primeResidue g hg hn) a (n : ℝ) (D + P) (by positivity) (by positivity)
    (fun χ hχ => norm_nat_mul_primeCharacterSum_le g hg χ hχ
      (character_sq_ne_one (by simpa only [Nat.card_eq_fintype_card] using hodd) χ hχ) n hnpos)
  change |(n : ℝ) * (φ * primeProgressionCount g n ↑a - Fintype.card (PrimeDegree K n))| ≤
    φ * (D + P) at hf
  have hp := abs_primeDegree_count_error_le (K := K) n hnpos
  change |(n : ℝ) * Fintype.card (PrimeDegree K n) - q ^ n| ≤ P at hp
  have hsplit : (n : ℝ) * φ * primeProgressionCount g n ↑a - q ^ n =
      (n : ℝ) * (φ * primeProgressionCount g n ↑a - Fintype.card (PrimeDegree K n)) +
        ((n : ℝ) * Fintype.card (PrimeDegree K n) - q ^ n) := by ring
  change |(n : ℝ) * φ * primeProgressionCount g n ↑a - q ^ n| ≤ _
  rw [hsplit]
  calc
    _ ≤ |(n : ℝ) * (φ * primeProgressionCount g n ↑a - Fintype.card (PrimeDegree K n))| +
        |(n : ℝ) * Fintype.card (PrimeDegree K n) - q ^ n| := abs_add_le _ _
    _ ≤ φ * (D + P) + P := add_le_add hf hp
    _ ≤ φ * (D + 2 * P) := by nlinarith
    _ = _ := by dsimp only [D, P, φ, q]; ring

end Erdos157.Elementary.PolynomialCharacters
