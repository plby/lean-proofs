import ErdosProblems.Erdos1141.StepanovParameters
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Quadratic character sums of polynomials with a simple root

The two-sided estimate follows by applying the residue-fiber estimate both
to `f` and to a nonsquare scalar multiple of `f`.
-/

namespace Pollack17.Stepanov

open Polynomial
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def residueFiber (f : (ZMod p)[X]) : Finset (ZMod p) :=
  Finset.univ.filter fun x => quadraticChar (ZMod p) (f.eval x) = 1

noncomputable def zeroFiber (f : (ZMod p)[X]) : Finset (ZMod p) :=
  Finset.univ.filter fun x => f.eval x = 0

noncomputable def polynomialCharacterSum (f : (ZMod p)[X]) : ℝ :=
  ∑ x : ZMod p, (quadraticChar (ZMod p) (f.eval x) : ℝ)

theorem polynomialCharacterSum_eq_fibers (f : (ZMod p)[X]) :
    polynomialCharacterSum f = 2 * (residueFiber f).card + (zeroFiber f).card - p := by
  classical
  have hpoint (x : ZMod p) : (quadraticChar (ZMod p) (f.eval x) : ℝ) =
      2 * (if quadraticChar (ZMod p) (f.eval x) = 1 then (1 : ℝ) else 0) +
        (if f.eval x = 0 then 1 else 0) - 1 := by
    by_cases hx : f.eval x = 0
    · simp [hx]
    · rcases quadraticChar_dichotomy hx with h | h <;> norm_num [h, hx]
  have hres : (∑ x : ZMod p,
      if quadraticChar (ZMod p) (f.eval x) = 1 then (1 : ℝ) else 0) = (residueFiber f).card := by
    simp [residueFiber]
  have hzero : (∑ x : ZMod p, if f.eval x = 0 then (1 : ℝ) else 0) = (zeroFiber f).card := by
    simp [zeroFiber]
  simp only [polynomialCharacterSum, hpoint, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hres, hzero]
  simp

theorem zeroFiber_card_le {f : (ZMod p)[X]} (hf : f ≠ 0) :
    (zeroFiber f).card ≤ f.natDegree := by
  classical
  have hsubset : zeroFiber f ⊆ f.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
    exact (Finset.mem_filter.mp hx).2
  exact ((Finset.card_le_card hsubset).trans (Multiset.toFinset_card_le _)).trans
    (Polynomial.card_roots' f)

theorem residueFiber_spec (f : (ZMod p)[X]) (hp2 : p ≠ 2)
    {x : ZMod p} (hx : x ∈ residueFiber f) :
    x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = 1 := by
  have hchar := (Finset.mem_filter.mp hx).2
  have hfx : f.eval x ≠ 0 := by
    intro hzero
    simp [hzero] at hchar
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hpow := quadraticChar_eq_pow_of_char_ne_two' hF (f.eval x)
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hhalf : p / 2 = (p - 1) / 2 := by
    have := Nat.odd_iff.mp hodd
    omega
  refine ⟨?_, hfx, ?_⟩
  · simp
  · simpa only [hchar, Int.cast_one, ZMod.card, hhalf] using hpow.symm

theorem polynomialCharacterSum_le_of_small_square {B : ℕ}
    (f : (ZMod p)[X]) {x₀ : ZMod p} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hp2 : p ≠ 2) (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p) :
    polynomialCharacterSum f ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) + f.natDegree := by
  have hcount := quadratic_fiber_card_bound_small_square f hf hroot hB hsmall
    (residueFiber f) (fun _ hx => residueFiber_spec f hp2 hx)
  have hcountR : (2 : ℝ) * (2 * B - 1 : ℕ) * (residueFiber f).card ≤
      (p : ℝ) * (2 * B - 1 : ℕ) + (p : ℝ) * (f.natDegree + 2) := by
    exact_mod_cast hcount
  have hzeros : ((zeroFiber f).card : ℝ) ≤ f.natDegree := by exact_mod_cast zeroFiber_card_le hf
  have hDpos : (0 : ℝ) < (2 * B - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * B - 1 by omega)
  have hquot : (2 : ℝ) * (residueFiber f).card - p ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) := by
    apply (le_div_iff₀ hDpos).mpr
    nlinarith
  rw [polynomialCharacterSum_eq_fibers]
  linarith

theorem abs_polynomialCharacterSum_le_of_small_square {B : ℕ}
    (f : (ZMod p)[X]) {x₀ : ZMod p} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hp2 : p ≠ 2) (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p) :
    |polynomialCharacterSum f| ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) + f.natDegree := by
  have hu := polynomialCharacterSum_le_of_small_square f hf hroot hp2 hB hsmall
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero] at ha
  let g := C a * f
  have hg : g ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr ha0) hf
  have hgroot : g.rootMultiplicity x₀ = 1 := by
    rw [Polynomial.rootMultiplicity_mul hg, Polynomial.rootMultiplicity_C, hroot, zero_add]
  have hgdegree : g.natDegree = f.natDegree := by
    rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr ha0) hf, natDegree_C, zero_add]
  have hl := polynomialCharacterSum_le_of_small_square g hg hgroot hp2 hB
    (by simpa only [hgdegree] using hsmall)
  have hsum : polynomialCharacterSum g = -polynomialCharacterSum f := by
    simp [polynomialCharacterSum, g, map_mul, ha, Finset.sum_neg_distrib]
  rw [hgdegree, hsum] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

theorem abs_polynomialCharacterSum_le_card (f : (ZMod p)[X]) :
    |polynomialCharacterSum f| ≤ p := by
  have hpoint (x : ZMod p) : |(quadraticChar (ZMod p) (f.eval x) : ℝ)| ≤ 1 := by
    rcases quadraticChar_isQuadratic (ZMod p) (f.eval x) with h | h | h <;> norm_num [h]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun x _ => hpoint x)).trans_eq (by simp))

end Pollack17.Stepanov
