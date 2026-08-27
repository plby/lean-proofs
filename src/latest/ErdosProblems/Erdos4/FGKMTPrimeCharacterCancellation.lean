import ErdosProblems.Erdos4.FGKMTWeightedDistribution
import ErdosProblems.Erdos4.ChebyshevIntervals
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-! Prime progression discrepancy controls nonprincipal character sums on every source interval. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical BoundedGaps.Maynard

noncomputable def primeCharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℕ) : ℂ :=
  ∑ p ∈ Nat.primesLE x, χ (p : ZMod q)

theorem primeCountUpTo_eq_zmod_fiber {q : ℕ} [NeZero q] (x : ℕ) (a : ZMod q) :
    primeCountUpTo x q a.val = ((Nat.primesLE x).filter (fun (p : ℕ) => (p : ZMod q) = a)).card := by
  unfold primeCountUpTo
  congr 1
  ext n
  have hc : (n : ZMod q) = a ↔ n % q = a.val % q := by
    simpa only [ZMod.natCast_zmod_val] using ZMod.natCast_eq_natCast_iff' n a.val q
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE, hc]
  constructor
  · rintro ⟨hn, hprime, hmod⟩
    exact ⟨⟨by omega, hprime⟩, hmod⟩
  · rintro ⟨⟨hn, hprime⟩, hmod⟩
    exact ⟨by omega, hprime, hmod⟩

theorem primeCharacterSum_eq_residues {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℕ) :
    primeCharacterSum χ x = ∑ a : ZMod q, χ a * (primeCountUpTo x q a.val : ℂ) := by
  rw [primeCharacterSum, ← Finset.sum_fiberwise' (Nat.primesLE x) (fun n : ℕ => (n : ZMod q)) χ]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_const, nsmul_eq_mul, ← primeCountUpTo_eq_zmod_fiber]
  ring

theorem primeCharacterSum_eq_centered {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) :
    primeCharacterSum χ x = ∑ a : ZMod q, χ a *
      ((primeCountUpTo x q a.val : ℂ) - (primeCountTotal x : ℂ) / (q.totient : ℂ)) := by
  rw [primeCharacterSum_eq_residues]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    MulChar.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

theorem norm_primeCharacterSum_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) :
    ‖primeCharacterSum χ x‖ ≤ (q : ℝ) * maxProgressionDiscrepancy x q := by
  have hpoint (a : ZMod q) :
      ‖χ a * ((primeCountUpTo x q a.val : ℂ) - (primeCountTotal x : ℂ) / (q.totient : ℂ))‖ ≤
        maxProgressionDiscrepancy x q := by
    by_cases ha : IsUnit a
    · have hacop : a.val.Coprime q := (ZMod.isUnit_iff_coprime a.val q).mp (by
        simpa only [ZMod.natCast_zmod_val] using ha)
      have hres : a.val ∈ coprimeResidues q :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.val_lt, hacop⟩
      have hd := progressionDiscrepancy_le_max (x := x) (NeZero.pos q) hres
      have heq : (primeCountUpTo x q a.val : ℂ) - (primeCountTotal x : ℂ) / (q.totient : ℂ) =
          (((primeCountUpTo x q a.val : ℝ) - (primeCountTotal x : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) := by
        push_cast <;> rfl
      have hnorm : ‖(primeCountUpTo x q a.val : ℂ) - (primeCountTotal x : ℂ) / (q.totient : ℂ)‖ ≤
          maxProgressionDiscrepancy x q := by
        rw [heq, Complex.norm_real, Real.norm_eq_abs]
        exact hd
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (χ.norm_le_one a) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hnorm)
    · rw [χ.map_nonunit ha, zero_mul, norm_zero]
      exact maxProgressionDiscrepancy_nonneg x q
  rw [primeCharacterSum_eq_centered χ hχ]
  calc
    _ ≤ ∑ a : ZMod q,
        ‖χ a * ((primeCountUpTo x q a.val : ℂ) - (primeCountTotal x : ℂ) / (q.totient : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, maxProgressionDiscrepancy x q := Finset.sum_le_sum (fun a _ => hpoint a)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

theorem primeCharacterSum_interval {q : ℕ} (χ : DirichletCharacter ℂ q)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ p ∈ ChebyshevIntervals.primeInterval a b, χ (p : ZMod q)) =
      primeCharacterSum χ b - primeCharacterSum χ a := by
  have hh := Finset.sum_sdiff (f := fun p : ℕ => χ (p : ZMod q)) (Nat.primesLE_mono hab)
  exact eq_sub_iff_add_eq.mpr hh

theorem norm_primeCharacterInterval_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {a b x : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hbx : b ≤ x) :
    ‖∑ p ∈ ChebyshevIntervals.primeInterval a b, χ (p : ZMod q)‖ ≤
      2 * (q : ℝ) * primeDiscrepancyUpTo x q := by
  rw [primeCharacterSum_interval χ hab]
  have hbnd (y : ℕ) (hy : 2 ≤ y) (hyx : y ≤ x) :
      ‖primeCharacterSum χ y‖ ≤ (q : ℝ) * primeDiscrepancyUpTo x q :=
    (norm_primeCharacterSum_le χ hχ y).trans
      (mul_le_mul_of_nonneg_left (maxProgressionDiscrepancy_le_primeDiscrepancyUpTo hy hyx)
        (Nat.cast_nonneg q))
  exact (norm_sub_le _ _).trans
    ((add_le_add (hbnd b (ha.trans hab) hbx) (hbnd a ha (hab.trans hbx))).trans_eq (by ring))

theorem primeDiscrepancyUpTo_le_excised {x Q B q : ℕ} (hq0 : 1 ≤ q) (hqQ : q ≤ Q)
    (hqB : q.Coprime B) : primeDiscrepancyUpTo x q ≤ excisedPrimeSum x Q B := by
  have hh := excisedPrimeSum_subset (x := x) (Q := Q) (B := B) {q}
    (by intro n hn; have heq := Finset.mem_singleton.mp hn; subst n; exact Finset.mem_Icc.mpr ⟨hq0, hqQ⟩)
    (by intro n hn; have heq := Finset.mem_singleton.mp hn; subst n; exact hqB)
  simpa only [Finset.sum_singleton] using hh

theorem norm_primeCharacterInterval_le_excised {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {a b x Q B : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hbx : b ≤ x) (hqQ : q ≤ Q) (hqB : q.Coprime B) :
    ‖∑ p ∈ ChebyshevIntervals.primeInterval a b, χ (p : ZMod q)‖ ≤
      2 * (q : ℝ) * excisedPrimeSum x Q B :=
  (norm_primeCharacterInterval_le χ hχ ha hab hbx).trans
    (mul_le_mul_of_nonneg_left (primeDiscrepancyUpTo_le_excised (NeZero.pos q) hqQ hqB)
      (by positivity))

end Erdos4.FGKMT
