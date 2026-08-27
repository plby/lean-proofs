import ErdosProblems.Erdos4.FGKMTTranslatedWeights
import Mathlib.Data.ZMod.QuotientRing

/-! Exact translated-mask counts, locally and over the small CRT product. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductCharacterEncoding

section Local

variable {ell k : ℕ} [Fact ell.Prime]

def TranslatedLocalGood (h : Fin k → ZMod ell) (Y p x : ZMod ell) : Prop :=
  ∀ i, x - Y + h i * p ≠ 0

theorem translatedLocalGood_iff (h : Fin k → ZMod ell) (Y p x : ZMod ell) (hp : p ≠ 0) :
    TranslatedLocalGood h Y p x ↔ SmallPrimeGood h ((x - Y) / p) := by
  unfold TranslatedLocalGood SmallPrimeGood
  apply forall_congr'
  intro i
  have heq : x - Y + h i * p = ((x - Y) / p + h i) * p := by field_simp [hp]
  rw [heq, mul_ne_zero_iff]
  exact ⟨And.left, fun hh => ⟨hh, hp⟩⟩

theorem sum_translatedLocalGood (h : Fin k → ZMod ell) (Y p : ZMod ell) (hp : p ≠ 0) :
    (∑ x : ZMod ell, if (∀ i, x - Y + h i * p ≠ 0) then (1 : ℝ) else 0) =
      (smallPrimeGoodStates h).card := by
  let e : ZMod ell ≃ ZMod ell :=
    { toFun := fun x => (x - Y) / p
      invFun := fun x => x * p + Y
      left_inv := by intro x; dsimp only; rw [div_mul_cancel₀ _ hp]; ring
      right_inv := by intro x; dsimp only; rw [add_sub_cancel_right, mul_div_cancel_right₀ _ hp] }
  calc
    _ = ∑ x : ZMod ell, if SmallPrimeGood h x then (1 : ℝ) else 0 := by
      apply Fintype.sum_equiv e
      intro x
      change (if (∀ i, x - Y + h i * p ≠ 0) then (1 : ℝ) else 0) =
        if SmallPrimeGood h ((x - Y) / p) then 1 else 0
      have hpred := translatedLocalGood_iff h Y p x hp
      by_cases hx : ∀ i, x - Y + h i * p ≠ 0
      · simp only [if_pos hx, if_pos (hpred.mp hx)]
      · have hh : ¬ SmallPrimeGood h ((x - Y) / p) := fun hh => hx (hpred.mpr hh)
        simp only [if_neg hx, if_neg hh]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [smallPrimeGoodStates]

end Local

theorem sum_range_natCast_zmod {M : ℕ} [NeZero M] (hM : 0 < M) (f : ZMod M → ℝ) :
    (∑ n ∈ Finset.range M, f (n : ZMod M)) = ∑ x : ZMod M, f x := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ZMod M))
  · intro n _
    exact Finset.mem_univ _
  · intro n hn m hm heq
    exact ((ZMod.natCast_eq_natCast_iff n m M).mp heq).eq_of_lt_of_lt
      (Finset.mem_range.mp hn) (Finset.mem_range.mp hm)
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
  · intro n _
    rfl

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem product_residue_sum
    (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (g : ∀ l, ZMod (ell l) → ℝ) :
    (∑ n ∈ Finset.range (modulus ell), ∏ l, g l (n : ZMod (ell l))) =
      ∏ l, ∑ x : ZMod (ell l), g l x := by
  let f : ZMod (modulus ell) → ℝ := fun x =>
    ∏ l, g l (ZMod.castHom (local_dvd_modulus ell l) (ZMod (ell l)) x)
  have hM : 0 < modulus ell := Finset.prod_pos (fun l _ => (Fact.out : (ell l).Prime).pos)
  letI : NeZero (modulus ell) := ⟨hM.ne'⟩
  have hn : ∀ n : ℕ, (∏ l, g l (n : ZMod (ell l))) = f (n : ZMod (modulus ell)) := by
    intro n
    simp only [f, map_natCast]
  calc
    _ = ∑ n ∈ Finset.range (modulus ell), f (n : ZMod (modulus ell)) :=
      Finset.sum_congr rfl (fun n _ => hn n)
    _ = ∑ x : ZMod (modulus ell), f x := sum_range_natCast_zmod hM f
    _ = ∑ x : ∀ l, ZMod (ell l), ∏ l, g l (x l) := by
      apply Fintype.sum_equiv (ZMod.prodEquivPi ell hcop).toEquiv
      intro x
      change (∏ l, g l (ZMod.castHom (local_dvd_modulus ell l) (ZMod (ell l)) x)) =
        ∏ l, g l (ZMod.prodEquivPi ell hcop x l)
      simp only [ZMod.prodEquivPi_apply]
    _ = _ := (Fintype.prod_sum g).symm

theorem smallProductDensity_mul_modulus (h : ∀ l, Fin k → ZMod (ell l)) :
    smallProductDensity ell h * (modulus ell : ℝ) =
      ∏ l, ((smallPrimeGoodStates (h l)).card : ℝ) := by
  unfold smallProductDensity smallPresieveDensity modulus
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  exact div_mul_cancel₀ _ (by exact_mod_cast (Fact.out : (ell l).Prime).ne_zero)

theorem translatedSmallMask_sum
    (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (h : Fin k → ℕ) (Y p : ℕ) (hp : ∀ l, (p : ZMod (ell l)) ≠ 0) :
    (∑ n ∈ Finset.range (modulus ell), translatedSmallMask ell h Y p n) =
      smallProductDensity ell (fun l i => (h i : ZMod (ell l))) * (modulus ell : ℝ) := by
  calc
    _ = ∏ l, ∑ x : ZMod (ell l),
        if (∀ i, x - Y + (h i : ZMod (ell l)) * p ≠ 0) then (1 : ℝ) else 0 := by
      unfold translatedSmallMask
      exact product_residue_sum ell hcop
        (fun l x => if (∀ i, x - Y + (h i : ZMod (ell l)) * p ≠ 0) then (1 : ℝ) else 0)
    _ = ∏ l, ((smallPrimeGoodStates (fun i => (h i : ZMod (ell l)))).card : ℝ) := by
      apply Finset.prod_congr rfl
      intro l _
      exact sum_translatedLocalGood (fun i => (h i : ZMod (ell l))) (Y : ZMod (ell l))
        (p : ZMod (ell l)) (hp l)
    _ = _ := (smallProductDensity_mul_modulus ell (fun l i => (h i : ZMod (ell l)))).symm

end Erdos4.FGKMT
