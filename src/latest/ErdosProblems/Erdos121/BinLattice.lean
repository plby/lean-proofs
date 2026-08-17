import ErdosProblems.Erdos121.K5

/-! # Integer bin lattices for the `K₅` construction -/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

def k5BinRow (b : Fin 10 → ℕ) : Fin 5 → ℕ :=
  ![b 0 + b 1 + b 2 + b 3,
    b 0 + b 4 + b 5 + b 6,
    b 1 + b 4 + b 7 + b 8,
    b 2 + b 5 + b 7 + b 9,
    b 3 + b 6 + b 8 + b 9]

def k5BinRowInt (b : Fin 10 → ℤ) : Fin 5 → ℤ :=
  ![b 0 + b 1 + b 2 + b 3,
    b 0 + b 4 + b 5 + b 6,
    b 1 + b 4 + b 7 + b 8,
    b 2 + b 5 + b 7 + b 9,
    b 3 + b 6 + b 8 + b 9]

def k5FreeBins (U : ℕ) (t : Fin 5 → ℕ) : Fin 5 → ℤ :=
  let Q := U / 1000
  ![(180 * Q + 2 * t 0 : ℕ),
    (220 * Q + 2 * t 1 : ℕ),
    (260 * Q + 2 * t 2 : ℕ),
    (300 * Q + 2 * t 3 : ℕ),
    (140 * Q + 2 * t 4 : ℕ)]

def k5SolvedBinsInt (s : Fin 5 → ℕ) (x : Fin 5 → ℤ) : Fin 10 → ℤ :=
  let f := x 0
  let g := x 1
  let h := x 2
  let i := x 3
  let j := x 4
  let c := (s 3 : ℤ) - f - h - j
  let d := (s 4 : ℤ) - g - i - j
  let T := (s 0 : ℤ) - c - d
  let S1 := (s 1 : ℤ) - f - g
  let S2 := (s 2 : ℤ) - h - i
  let a := (T + S1 - S2) / 2
  let b := (T - S1 + S2) / 2
  let e := (-T + S1 + S2) / 2
  ![a, b, c, d, e, f, g, h, i, j]

def k5SolvedBins (U : ℕ) (s : Fin 5 → ℕ) (t : Fin 5 → ℕ) : Fin 10 → ℕ :=
  fun e => (k5SolvedBinsInt s (k5FreeBins U t) e).toNat

def k5ParameterBox (U : ℕ) : Finset (Fin 5 → ℕ) :=
  Fintype.piFinset fun _ : Fin 5 => Finset.range (U / 100000000 + 1)

def k5BaseCoefficient : Fin 10 → ℕ :=
  ![200, 40, 420, 340, 400, 180, 220, 260, 300, 140]

lemma k5BaseCoefficient_ge (e : Fin 10) : 40 ≤ k5BaseCoefficient e := by
  fin_cases e <;> decide

lemma k5BaseCoefficient_separated {e f : Fin 10} (hef : e ≠ f) :
    k5BaseCoefficient e + 20 ≤ k5BaseCoefficient f ∨
      k5BaseCoefficient f + 20 ≤ k5BaseCoefficient e := by
  fin_cases e <;> fin_cases f <;> simp_all [k5BaseCoefficient]

lemma mem_k5ParameterBox {U : ℕ} {t : Fin 5 → ℕ} :
    t ∈ k5ParameterBox U ↔ ∀ i, t i ≤ U / 100000000 := by
  rw [k5ParameterBox, Fintype.mem_piFinset]
  constructor
  · intro h i
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (h i))
  · intro h i
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (h i))

lemma k5SolvedBinsInt_bounds {U : ℕ} (hU : 1000000000 ≤ U)
    {s : Fin 5 → ℕ} (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U) {t : Fin 5 → ℕ}
    (ht : t ∈ k5ParameterBox U) (e : Fin 10) :
    (U : ℤ) / 100 ≤ k5SolvedBinsInt s (k5FreeBins U t) e ∧
      k5SolvedBinsInt s (k5FreeBins U t) e ≤ (U : ℤ) / 2 := by
  have ht' := mem_k5ParameterBox.mp ht
  have hs0l := hsLower 0
  have hs1l := hsLower 1
  have hs2l := hsLower 2
  have hs3l := hsLower 3
  have hs4l := hsLower 4
  have hs0u := hsUpper 0
  have hs1u := hsUpper 1
  have hs2u := hsUpper 2
  have hs3u := hsUpper 3
  have hs4u := hsUpper 4
  have ht0 := ht' 0
  have ht1 := ht' 1
  have ht2 := ht' 2
  have ht3 := ht' 3
  have ht4 := ht' 4
  fin_cases e <;>
    simp [k5SolvedBinsInt, k5FreeBins] <;>
    omega

lemma k5SolvedBinsInt_close_base {U : ℕ} (hU : 1000000000 ≤ U)
    {s : Fin 5 → ℕ} (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U) {t : Fin 5 → ℕ}
    (ht : t ∈ k5ParameterBox U) (e : Fin 10) :
    (k5BaseCoefficient e * (U / 1000) : ℕ) - U / 200 ≤
        k5SolvedBinsInt s (k5FreeBins U t) e ∧
      k5SolvedBinsInt s (k5FreeBins U t) e ≤
        (k5BaseCoefficient e * (U / 1000) : ℕ) + U / 200 := by
  have ht' := mem_k5ParameterBox.mp ht
  have hs0l := hsLower 0
  have hs1l := hsLower 1
  have hs2l := hsLower 2
  have hs3l := hsLower 3
  have hs4l := hsLower 4
  have hs0u := hsUpper 0
  have hs1u := hsUpper 1
  have hs2u := hsUpper 2
  have hs3u := hsUpper 3
  have hs4u := hsUpper 4
  have ht0 := ht' 0
  have ht1 := ht' 1
  have ht2 := ht' 2
  have ht3 := ht' 3
  have ht4 := ht' 4
  fin_cases e <;>
    simp [k5BaseCoefficient, k5SolvedBinsInt, k5FreeBins] <;>
    omega

lemma k5SolvedBinsInt_nonneg {U : ℕ} (hU : 1000000000 ≤ U)
    {s : Fin 5 → ℕ} (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U) {t : Fin 5 → ℕ}
    (ht : t ∈ k5ParameterBox U) (e : Fin 10) :
    0 ≤ k5SolvedBinsInt s (k5FreeBins U t) e := by
  have h := (k5SolvedBinsInt_bounds hU hsLower hsUpper ht e).1
  omega

lemma k5SolvedBinsInt_row_bounds (s : Fin 5 → ℕ) (x : Fin 5 → ℤ)
    (v : Fin 5) :
    (s v : ℤ) - 2 ≤ k5BinRowInt (k5SolvedBinsInt s x) v ∧
      k5BinRowInt (k5SolvedBinsInt s x) v ≤ (s v : ℤ) := by
  fin_cases v <;>
    simp [k5BinRowInt, k5SolvedBinsInt] <;>
    omega

lemma k5SolvedBins_row_bounds {U : ℕ} (hU : 1000000000 ≤ U)
    {s : Fin 5 → ℕ} (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U) {t : Fin 5 → ℕ}
    (ht : t ∈ k5ParameterBox U) (v : Fin 5) :
    s v - 2 ≤ k5BinRow (k5SolvedBins U s t) v ∧
      k5BinRow (k5SolvedBins U s t) v ≤ s v := by
  have hn : ∀ e : Fin 10,
      0 ≤ k5SolvedBinsInt s (k5FreeBins U t) e :=
    k5SolvedBinsInt_nonneg hU hsLower hsUpper ht
  have hcast : (k5BinRow (k5SolvedBins U s t) v : ℤ) =
      k5BinRowInt (k5SolvedBinsInt s (k5FreeBins U t)) v := by
    fin_cases v <;>
      simp [k5BinRow, k5BinRowInt, k5SolvedBins, Int.toNat_of_nonneg, hn]
  have hi := k5SolvedBinsInt_row_bounds s (k5FreeBins U t) v
  have hs2 : 2 ≤ s v := by
    have hl := hsLower v
    omega
  constructor
  · have hlow : ((s v - 2 : ℕ) : ℤ) ≤
        (k5BinRow (k5SolvedBins U s t) v : ℕ) := by
      rw [hcast, Int.ofNat_sub hs2]
      exact hi.1
    exact_mod_cast hlow
  · have hupp : (k5BinRow (k5SolvedBins U s t) v : ℤ) ≤ (s v : ℤ) := by
      rw [hcast]
      exact hi.2
    exact_mod_cast hupp

lemma k5SolvedBins_separated {U : ℕ} (hU : 1000000000 ≤ U)
    {s : Fin 5 → ℕ} (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U) {t : Fin 5 → ℕ}
    (ht : t ∈ k5ParameterBox U) {e f : Fin 10} (hef : e ≠ f) :
    k5SolvedBins U s t e + 1 < k5SolvedBins U s t f ∨
      k5SolvedBins U s t f + 1 < k5SolvedBins U s t e := by
  have he := k5SolvedBinsInt_close_base hU hsLower hsUpper ht e
  have hf := k5SolvedBinsInt_close_base hU hsLower hsUpper ht f
  have hne := k5SolvedBinsInt_nonneg hU hsLower hsUpper ht e
  have hnf := k5SolvedBinsInt_nonneg hU hsLower hsUpper ht f
  have heq : (k5SolvedBins U s t e : ℤ) =
      k5SolvedBinsInt s (k5FreeBins U t) e := by
    simp [k5SolvedBins, Int.toNat_of_nonneg hne]
  have hfq : (k5SolvedBins U s t f : ℤ) =
      k5SolvedBinsInt s (k5FreeBins U t) f := by
    simp [k5SolvedBins, Int.toNat_of_nonneg hnf]
  rw [← heq] at he
  rw [← hfq] at hf
  have hgap : 2 * (U / 200) + 1 < 20 * (U / 1000) := by omega
  have hcoefE : 20 ≤ k5BaseCoefficient e :=
    (by norm_num : 20 ≤ 40).trans (k5BaseCoefficient_ge e)
  have hcoefF : 20 ≤ k5BaseCoefficient f :=
    (by norm_num : 20 ≤ 40).trans (k5BaseCoefficient_ge f)
  have hcoefMulE := Nat.mul_le_mul_right (U / 1000) hcoefE
  have hcoefMulF := Nat.mul_le_mul_right (U / 1000) hcoefF
  rcases k5BaseCoefficient_separated hef with hsep | hsep
  · left
    have hmul := Nat.mul_le_mul_right (U / 1000) hsep
    rw [Nat.add_mul] at hmul
    omega
  · right
    have hmul := Nat.mul_le_mul_right (U / 1000) hsep
    rw [Nat.add_mul] at hmul
    omega

end Erdos121
