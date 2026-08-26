import ErdosProblems.Erdos394.RootBoxVariance

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary linear bounds for small finite Euler products
-/

open Nat Finset

namespace Erdos394

/-- If every nonnegative local increment is at most `e` and
`2 |S| e ≤ 1`, then the product is bounded by its linear majorant. -/
theorem prod_one_add_le_linear
    {α : Type*} [DecidableEq α] (S : Finset α) (g : α → ℝ) (e : ℝ)
    (he : 0 ≤ e) (hg0 : ∀ a ∈ S, 0 ≤ g a)
    (hge : ∀ a ∈ S, g a ≤ e)
    (hsmall : 2 * (S.card : ℝ) * e ≤ 1) :
    ∏ a ∈ S, (1 + g a) ≤ 1 + 2 * (S.card : ℝ) * e := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hcard : ((insert a S).card : ℝ) = (S.card : ℝ) + 1 := by
        simp [ha]
      have hsmallS : 2 * (S.card : ℝ) * e ≤ 1 := by
        rw [hcard] at hsmall
        nlinarith
      have ih' := ih (fun x hx ↦ hg0 x (Finset.mem_insert_of_mem hx))
        (fun x hx ↦ hge x (Finset.mem_insert_of_mem hx)) hsmallS
      have hga0 := hg0 a (Finset.mem_insert_self a S)
      have hgae := hge a (Finset.mem_insert_self a S)
      have hfac0 : 0 ≤ 1 + g a := by linarith
      have h1e0 : 0 ≤ 1 + e := by linarith
      have hprod0 : 0 ≤ ∏ x ∈ S, (1 + g x) := by
        apply Finset.prod_nonneg
        intro x hx
        have := hg0 x (Finset.mem_insert_of_mem hx)
        linarith
      have hlin0 : 0 ≤ 1 + 2 * (S.card : ℝ) * e := by positivity
      have hcross : 0 ≤ e * (1 - 2 * (S.card : ℝ) * e) := by
        exact mul_nonneg he (by linarith)
      rw [Finset.prod_insert ha, hcard]
      calc
        (1 + g a) * ∏ x ∈ S, (1 + g x) ≤
            (1 + e) * (1 + 2 * (S.card : ℝ) * e) := by
          exact mul_le_mul (by linarith) ih' hprod0 h1e0
        _ ≤ 1 + 2 * ((S.card : ℝ) + 1) * e := by
          nlinarith

/-- Under the same hypothesis the product is at most two. -/
theorem prod_one_add_le_two
    {α : Type*} [DecidableEq α] (S : Finset α) (g : α → ℝ) (e : ℝ)
    (he : 0 ≤ e) (hg0 : ∀ a ∈ S, 0 ≤ g a)
    (hge : ∀ a ∈ S, g a ≤ e)
    (hsmall : 2 * (S.card : ℝ) * e ≤ 1) :
    ∏ a ∈ S, (1 + g a) ≤ 2 := by
  have hlin := prod_one_add_le_linear S g e he hg0 hge hsmall
  linarith

/-- A simple minimum-prime condition makes the corrected area product differ
from one by at most `K^{-|P|}`. -/
theorem rootBoxAreaCorrection_le
    (P : Finset ℕ) (K : ℕ) (hK : 1 < K) (hP : 0 < P.card)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsize : ∀ p ∈ P,
      2 * P.card * K ^ P.card ≤ p - 1) :
    rootBoxAreaCorrection P K ≤
      1 + 1 / ((K ^ P.card : ℕ) : ℝ) := by
  let r : ℝ := P.card
  let R : ℝ := (K ^ P.card : ℕ)
  let e : ℝ := 1 / (2 * r * R)
  let g : ℕ → ℝ := fun p ↦
    ((K * K - 1 : ℕ) : ℝ) /
      (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast hP
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast (pow_pos (by omega : 0 < K) P.card)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hg0 : ∀ p ∈ P, 0 ≤ g p := by
    intro p hp
    dsimp [g]
    positivity
  have hge : ∀ p ∈ P, g p ≤ e := by
    intro p hp
    have hp2 := (hprime p hp).two_le
    have hp1pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < p - 1 by omega)
    have hKKpos : (0 : ℝ) < ((K * K : ℕ) : ℝ) := by positivity
    have hden1 : (0 : ℝ) <
        ((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) := mul_pos hKKpos hp1pos
    have hden2 : (0 : ℝ) < 2 * r * R := by positivity
    apply (div_le_div_iff₀ hden1 hden2).mpr
    have hc : ((K * K - 1 : ℕ) : ℝ) ≤ ((K * K : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_le (K * K) 1)
    have hsizeR : 2 * r * R ≤ ((p - 1 : ℕ) : ℝ) := by
      dsimp [r, R]
      exact_mod_cast hsize p hp
    calc
      ((K * K - 1 : ℕ) : ℝ) * (2 * r * R) ≤
          ((K * K : ℕ) : ℝ) * (2 * r * R) :=
        mul_le_mul_of_nonneg_right hc hden2.le
      _ ≤ ((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsizeR hKKpos.le
      _ = 1 * (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) := by ring
  have hsmall : 2 * (P.card : ℝ) * e ≤ 1 := by
    dsimp [e, r]
    have hR1 : (1 : ℝ) ≤ R := by
      dsimp [R]
      exact_mod_cast (show 1 ≤ K ^ P.card by
        have : 0 < K ^ P.card := pow_pos (by omega) _
        omega)
    field_simp
    nlinarith
  have hprod := prod_one_add_le_linear P g e he hg0 hge hsmall
  unfold rootBoxAreaCorrection
  change (∏ p ∈ P, (1 + g p)) ≤ _
  calc
    (∏ p ∈ P, (1 + g p)) ≤ 1 + 2 * (P.card : ℝ) * e := hprod
    _ = 1 + 1 / R := by
      dsimp [e, r]
      field_simp
    _ = 1 + 1 / ((K ^ P.card : ℕ) : ℝ) := by rfl

/-- A minimum-prime condition bounds the rational-boundary Euler correction
by two. -/
theorem rootBoxRationalCorrection_le_two
    (P : Finset ℕ) (K : ℕ) (hK : 1 < K) (hP : 0 < P.card)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsize : ∀ p ∈ P, 4 * P.card * K ≤ p - 1) :
    rootBoxRationalCorrection P K ≤ 2 := by
  let r : ℝ := P.card
  let e : ℝ := 1 / (2 * r)
  let g : ℕ → ℝ := fun p ↦
    (2 * (K * K - 1 : ℕ) : ℝ) /
      ((K : ℝ) * ((p : ℝ) - 1))
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast hP
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hg0 : ∀ p ∈ P, 0 ≤ g p := by
    intro p hp
    dsimp [g]
    have hpR : (1 : ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
    positivity
  have hge : ∀ p ∈ P, g p ≤ e := by
    intro p hp
    have hp1 : 1 ≤ p := (hprime p hp).one_le
    have hp1R : (0 : ℝ) < (p : ℝ) - 1 := by
      have hpSub : 0 < p - 1 := by
        have := (hprime p hp).one_lt
        omega
      have hpSubR : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
        exact_mod_cast hpSub
      norm_num only [Nat.cast_sub hp1, Nat.cast_one] at hpSubR
      exact hpSubR
    have hden1 : (0 : ℝ) < (K : ℝ) * ((p : ℝ) - 1) :=
      mul_pos hKR hp1R
    have hden2 : (0 : ℝ) < 2 * r := by positivity
    apply (div_le_div_iff₀ hden1 hden2).mpr
    have hc : ((K * K - 1 : ℕ) : ℝ) ≤ (K : ℝ) * (K : ℝ) := by
      have hcNat : K * K - 1 ≤ K * K := Nat.sub_le _ _
      exact_mod_cast hcNat
    have hnum : 2 * ((K * K - 1 : ℕ) : ℝ) ≤
        2 * (K : ℝ) * (K : ℝ) := by
      nlinarith
    have hsizeR : 4 * r * (K : ℝ) ≤ (p : ℝ) - 1 := by
      have hs : ((4 * P.card * K : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
        exact_mod_cast hsize p hp
      rw [Nat.cast_sub hp1] at hs
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hs
      simpa [r] using hs
    calc
      (2 * ((K * K - 1 : ℕ) : ℝ)) * (2 * r) ≤
          (2 * (K : ℝ) * (K : ℝ)) * (2 * r) :=
        mul_le_mul_of_nonneg_right hnum hden2.le
      _ = (K : ℝ) * (4 * r * (K : ℝ)) := by ring
      _ ≤ (K : ℝ) * ((p : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hsizeR hKR.le
      _ = 1 * ((K : ℝ) * ((p : ℝ) - 1)) := by ring
  have hsmall : 2 * (P.card : ℝ) * e ≤ 1 := by
    dsimp [e, r]
    field_simp
    norm_num
  have hprod := prod_one_add_le_two P g e he hg0 hge hsmall
  unfold rootBoxRationalCorrection
  exact hprod

/-- Choosing `Z` linearly larger than the number of primes and `K²` bounds
the non-rational correction by two. -/
theorem rootBoxNonrationalCorrection_le_two
    (P : Finset ℕ) (K Z : ℕ) (hP : 0 < P.card) (hZ : 1 ≤ Z)
    (hZsize : 8 * P.card * (K * K - 1) ≤ Z) :
    rootBoxNonrationalCorrection P K Z ≤ 2 := by
  let r : ℝ := P.card
  let e : ℝ := 1 / (2 * r)
  let g : ℕ → ℝ := fun _p ↦
    4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast hP
  have hZR : (0 : ℝ) < Z := by exact_mod_cast (Nat.zero_lt_of_lt hZ)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hg0 : ∀ p ∈ P, 0 ≤ g p := by
    intro p hp
    dsimp [g]
    positivity
  have hge : ∀ p ∈ P, g p ≤ e := by
    intro p hp
    have hden2 : (0 : ℝ) < 2 * r := by positivity
    apply (div_le_div_iff₀ hZR hden2).mpr
    have hs : ((8 * P.card * (K * K - 1) : ℕ) : ℝ) ≤ (Z : ℝ) := by
      exact_mod_cast hZsize
    dsimp [r]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hs ⊢
    nlinarith
  have hsmall : 2 * (P.card : ℝ) * e ≤ 1 := by
    dsimp [e, r]
    field_simp
    norm_num
  have hprod := prod_one_add_le_two P g e he hg0 hge hsmall
  unfold rootBoxNonrationalCorrection
  exact hprod

/-- The same choice of `Z` also bounds the additive-constant correction by
two. -/
theorem rootBoxConstantCorrection_le_two
    (P : Finset ℕ) (K Z : ℕ) (hP : 0 < P.card) (hZ : 1 ≤ Z)
    (hZsize : 8 * P.card * (K * K - 1) ≤ Z) :
    rootBoxConstantCorrection P K Z ≤ 2 := by
  let r : ℝ := P.card
  let e : ℝ := 1 / (2 * r)
  let g : ℕ → ℝ := fun _p ↦
    4 * ((K * K - 1 : ℕ) : ℝ) / ((Z * Z : ℕ) : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast hP
  have hZZnat : 0 < Z * Z := Nat.mul_pos
    (Nat.zero_lt_of_lt hZ) (Nat.zero_lt_of_lt hZ)
  have hZZR : (0 : ℝ) < ((Z * Z : ℕ) : ℝ) := by exact_mod_cast hZZnat
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hg0 : ∀ p ∈ P, 0 ≤ g p := by
    intro p hp
    dsimp [g]
    positivity
  have hge : ∀ p ∈ P, g p ≤ e := by
    intro p hp
    have hden2 : (0 : ℝ) < 2 * r := by positivity
    apply (div_le_div_iff₀ hZZR hden2).mpr
    have hZZle : Z ≤ Z * Z := by
      nth_rewrite 1 [← Nat.mul_one Z]
      exact Nat.mul_le_mul_left Z hZ
    have hsizeZZ : 8 * P.card * (K * K - 1) ≤ Z * Z :=
      (hZsize.trans hZZle)
    have hs : ((8 * P.card * (K * K - 1) : ℕ) : ℝ) ≤
        ((Z * Z : ℕ) : ℝ) := by exact_mod_cast hsizeZZ
    dsimp [r]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hs ⊢
    nlinarith
  have hsmall : 2 * (P.card : ℝ) * e ≤ 1 := by
    dsimp [e, r]
    field_simp
    norm_num
  have hprod := prod_one_add_le_two P g e he hg0 hge hsmall
  unfold rootBoxConstantCorrection
  exact hprod

/-- Arithmetic size hypotheses imply the explicit no-hit tail without any
remaining abstract Euler-correction assumptions. -/
theorem normalized_rootBoxTupleNoHitSet_le_of_sizes
    (P : Finset ℕ) (K Y Z : ℕ) (hK : 1 < K) (hY : 0 < Y)
    (hZ : 1 ≤ Z) (hP : 0 < P.card)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (hareaSize : ∀ p ∈ P,
      2 * P.card * K ^ P.card ≤ p - 1)
    (hratSize : ∀ p ∈ P, 4 * P.card * K ≤ p - 1)
    (hZsize : 8 * P.card * (K * K - 1) ≤ Z) :
    ((rootBoxTupleNoHitSet P K Y hprime).card : ℝ) /
        (primeUnitCount P : ℝ) ≤
      1 / ((K ^ P.card : ℕ) : ℝ) +
      (((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) + 160 * (K : ℝ)) + 2) /
        rootBoxMainParameter P K Y +
      88 / (rootBoxMainParameter P K Y) ^ 2 := by
  exact normalized_rootBoxTupleNoHitSet_le P K Y Z hK hY hZ hprime
    hKp hK2p hlarge hZp hZ2p
    (rootBoxAreaCorrection_le P K hK hP hprime hareaSize)
    (rootBoxRationalCorrection_le_two P K hK hP hprime hratSize)
    (rootBoxNonrationalCorrection_le_two P K Z hP hZ hZsize)
    (rootBoxConstantCorrection_le_two P K Z hP hZ hZsize)

end Erdos394
