/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Basic

/-!
# The binary density Hales--Jewett theorem

For the alphabet `Fin 2`, a combinatorial-line-free family is an antichain in
the Boolean lattice.  Sperner's theorem therefore bounds it by the middle
binomial coefficient.  An elementary squared central-binomial estimate then
shows that this bound has density tending to zero.
-/

namespace Erdos171

open Finset Set Function

/-- The support of a binary word: the coordinates carrying the letter `1`. -/
def binarySupport {n : ℕ} (x : Word 2 n) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ x i = 1)

@[simp] theorem mem_binarySupport {n : ℕ} {x : Word 2 n} {i : Fin n} :
    i ∈ binarySupport x ↔ x i = 1 := by
  simp [binarySupport]

theorem binarySupport_injective (n : ℕ) :
    Function.Injective (@binarySupport n) := by
  intro x y h
  funext i
  have hi : (x i = 1) ↔ (y i = 1) := by
    simpa only [mem_binarySupport] using Finset.ext_iff.mp h i
  apply Fin.ext
  omega

theorem binarySupport_subset_iff {n : ℕ} {x y : Word 2 n} :
    binarySupport x ⊆ binarySupport y ↔ ∀ i, x i ≤ y i := by
  constructor
  · intro h i
    have hi : x i = 1 → y i = 1 := by
      simpa only [mem_binarySupport] using @h i
    exact Fin.le_iff_val_le_val.mpr (by omega)
  · intro h i hi
    rw [mem_binarySupport] at hi ⊢
    have := h i
    apply Fin.ext
    omega

/-- Two binary words form an oriented combinatorial line when they are
distinct and coordinatewise ordered. -/
def BinaryLine {n : ℕ} (x y : Word 2 n) : Prop :=
  x ≠ y ∧ ∀ i, x i ≤ y i

theorem binaryLine_iff_support_ssubset {n : ℕ} {x y : Word 2 n} :
    BinaryLine x y ↔ binarySupport x ⊂ binarySupport y := by
  rw [BinaryLine, Finset.ssubset_iff_subset_ne, binarySupport_subset_iff]
  constructor
  · rintro ⟨hne, hle⟩
    exact ⟨hle, fun h ↦ hne ((binarySupport_injective n) h)⟩
  · rintro ⟨hle, hne⟩
    exact ⟨fun h ↦ hne (congrArg binarySupport h), hle⟩

/-- The proper Mathlib combinatorial line determined by an oriented pair of
binary words.  A coordinate is a wildcard exactly where the endpoints differ. -/
def lineOfBinaryLine {n : ℕ} (x y : Word 2 n) (h : BinaryLine x y) :
    Combinatorics.Line (Fin 2) (Fin n) where
  idxFun i := if x i = y i then some (x i) else none
  proper := by
    by_contra! hall
    apply h.1
    funext i
    simpa using hall i

@[simp] theorem lineOfBinaryLine_zero {n : ℕ} (x y : Word 2 n)
    (h : BinaryLine x y) : lineOfBinaryLine x y h 0 = x := by
  funext i
  by_cases hi : x i = y i
  · simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
  · have hle := h.2 i
    apply Fin.ext
    simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
    omega

@[simp] theorem lineOfBinaryLine_one {n : ℕ} (x y : Word 2 n)
    (h : BinaryLine x y) : lineOfBinaryLine x y h 1 = y := by
  funext i
  by_cases hi : x i = y i
  · simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
  · have hle := h.2 i
    apply Fin.ext
    simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
    omega

/-- An oriented binary pair in a set supplies a proper `Combinatorics.Line`. -/
theorem containsLine_of_binaryLine {n : ℕ} {A : Set (Word 2 n)}
    {x y : Word 2 n} (hx : x ∈ A) (hy : y ∈ A) (hxy : BinaryLine x y) :
    ContainsLine A := by
  refine ⟨lineOfBinaryLine x y hxy, ?_⟩
  rintro _ ⟨a, rfl⟩
  fin_cases a
  · simpa using hx
  · simpa using hy

/-- The endpoints `0` and `1` of every proper binary line form an oriented
binary pair. -/
theorem binaryLine_zero_one (l : Combinatorics.Line (Fin 2) (Fin n)) :
    BinaryLine (l 0) (l 1) := by
  constructor
  · exact l.parameter_injective.ne (by decide)
  · intro i
    cases hi : l.idxFun i with
    | none => simp [Combinatorics.Line.coe_apply, hi]
    | some a => simp [Combinatorics.Line.coe_apply, hi]

theorem antichain_image_binarySupport {n : ℕ} (A : Finset (Word 2 n))
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ BinaryLine x y) :
    IsAntichain (· ⊆ ·)
      ((A.image binarySupport : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
  intro s hs t ht hne hst
  simp only [Finset.mem_coe, Finset.mem_image] at hs ht
  obtain ⟨x, hxA, rfl⟩ := hs
  obtain ⟨y, hyA, hy⟩ := ht
  subst hy
  apply hA x hxA y hyA
  rw [binaryLine_iff_support_ssubset, Finset.ssubset_iff_subset_ne]
  exact ⟨hst, hne⟩

/-- Sperner's sharp upper bound for a binary line-free family. -/
theorem binary_line_free_card_le_choose {n : ℕ} (A : Finset (Word 2 n))
    (hA : ¬ ContainsLine (A : Set (Word 2 n))) :
    A.card ≤ n.choose (n / 2) := by
  have hpair : ∀ x ∈ A, ∀ y ∈ A, ¬ BinaryLine x y := by
    intro x hx y hy hxy
    exact hA (containsLine_of_binaryLine hx hy hxy)
  have hanti := antichain_image_binarySupport A hpair
  have hs := hanti.sperner
  rw [Finset.card_image_of_injective A (binarySupport_injective n)] at hs
  simpa using hs

/-- A convenient squared estimate for the central binomial coefficient. -/
theorem centralBinom_sq_bound : ∀ m : ℕ,
    (m + 1) * (Nat.centralBinom m) ^ 2 ≤ 16 ^ m := by
  intro m
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ m ih =>
      have hrec := Nat.succ_mul_centralBinom_succ m
      have hpoly : (m + 2) * (2 * (2 * m + 1)) ^ 2 ≤ 16 * (m + 1) ^ 3 := by
        nlinarith
      have hmul :
          (m + 2) * (m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2 ≤
            16 * (m + 1) ^ 2 * 16 ^ m := by
        calc
          (m + 2) * (m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2
              = (m + 2) * (2 * (2 * m + 1)) ^ 2 * (Nat.centralBinom m) ^ 2 := by
                  have hrec_sq := congrArg (fun z : ℕ ↦ z ^ 2) hrec
                  nlinarith
          _ ≤ 16 * (m + 1) ^ 3 * (Nat.centralBinom m) ^ 2 := by gcongr
          _ = 16 * (m + 1) ^ 2 * ((m + 1) * (Nat.centralBinom m) ^ 2) := by ring
          _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := by gcongr
      have hpos : 0 < (m + 1) ^ 2 := by positivity
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      rw [pow_succ]
      convert hmul using 1 <;> ring

/-- Uniform (even and odd dimension) squared upper bound for the middle
binomial coefficient. -/
theorem choose_middle_sq_bound (n : ℕ) :
    (n / 2 + 1) * (n.choose (n / 2)) ^ 2 ≤ 2 ^ (2 * n) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simpa [Nat.centralBinom, pow_mul] using centralBinom_sq_bound m
  · have hchoose : (2 * m + 1).choose m ≤ 2 * Nat.centralBinom m := by
      cases m with
      | zero => norm_num [Nat.centralBinom]
      | succ k =>
          rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
            Nat.choose_succ_succ' (2 * (k + 1)) k]
          rw [two_mul]
          simpa [two_mul] using
            Nat.add_le_add (Nat.choose_le_centralBinom k (k + 1))
              (Nat.choose_le_centralBinom (k + 1) (k + 1))
    calc
      ((2 * m + 1) / 2 + 1) * ((2 * m + 1).choose ((2 * m + 1) / 2)) ^ 2
          ≤ (m + 1) * (2 * Nat.centralBinom m) ^ 2 := by
              rw [show (2 * m + 1) / 2 = m by omega]
              exact Nat.mul_le_mul_left (m + 1) (Nat.pow_le_pow_left hchoose 2)
      _ = 4 * ((m + 1) * (Nat.centralBinom m) ^ 2) := by ring
      _ ≤ 4 * 16 ^ m := by gcongr; exact centralBinom_sq_bound m
      _ = 2 ^ (2 * (2 * m + 1)) := by
        rw [show 4 = 2 ^ 2 by norm_num, show 16 = 2 ^ 4 by norm_num,
          ← pow_mul, ← pow_add]
        congr 1
        omega

/-- The density Hales--Jewett theorem for the binary alphabet, for finite
families.  The proof gives the explicit threshold `2 * M` for any natural
`M > (ε²)⁻¹`. -/
theorem exists_containsLine_of_dense_binary_finset (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Word 2 n),
      eps * (2 : ℝ) ^ n ≤ A.card → ContainsLine (A : Set (Word 2 n)) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (eps ^ 2)⁻¹ < M := exists_nat_gt ((eps ^ 2)⁻¹)
  refine ⟨2 * M, ?_⟩
  intro n hn A hdense
  by_contra hfree
  have hcard := binary_line_free_card_le_choose A hfree
  have hcardR : (A.card : ℝ) ≤ n.choose (n / 2) := by exact_mod_cast hcard
  have hdense' : eps * (2 : ℝ) ^ n ≤ n.choose (n / 2) := hdense.trans hcardR
  have hsq : (eps * (2 : ℝ) ^ n) ^ 2 ≤ ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hdense'
  have hbound :
      (((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2) ≤
        ((2 : ℝ) ^ n) ^ 2 := by
    have hb := choose_middle_sq_bound n
    have hbR :
        (((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2) ≤
          (2 : ℝ) ^ (2 * n) := by
      exact_mod_cast hb
    simpa [pow_two, ← pow_add, two_mul] using hbR
  have hcombined :
      (((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2) * ((2 : ℝ) ^ n) ^ 2 ≤
        ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2) * ((2 : ℝ) ^ n) ^ 2 =
          ((n / 2 + 1 : ℕ) : ℝ) * (eps * (2 : ℝ) ^ n) ^ 2 := by ring
      _ ≤ ((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 := by
        gcongr
      _ ≤ ((2 : ℝ) ^ n) ^ 2 := hbound
  have hcoef : ((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2 ≤ 1 := by
    have hq : 0 < ((2 : ℝ) ^ n) ^ 2 := by positivity
    exact le_of_mul_le_mul_right (by simpa using hcombined) hq
  have hMdiv : M ≤ n / 2 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hMcast : (M : ℝ) ≤ ((n / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hMdiv.trans (by omega))
  have hepssq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hMinv : (eps ^ 2)⁻¹ * eps ^ 2 = 1 := by
    field_simp
  have hlarge : 1 < ((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2 := by
    have := mul_lt_mul_of_pos_right (hM.trans_le hMcast) hepssq
    nlinarith
  exact (not_lt_of_ge hcoef) hlarge

/-- Set-valued form of the binary density Hales--Jewett theorem. -/
theorem exists_containsLine_of_dense_binary (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Set (Word 2 n),
      eps * (2 : ℝ) ^ n ≤ A.ncard → ContainsLine A := by
  obtain ⟨N, hN⟩ := exists_containsLine_of_dense_binary_finset eps heps
  refine ⟨N, ?_⟩
  intro n hn A hdense
  let hfin : A.Finite := Set.toFinite A
  let s := hfin.toFinset
  have hsCard : s.card = A.ncard := by
    exact (Set.ncard_eq_toFinset_card A hfin).symm
  have hsLine : ContainsLine (s : Set (Word 2 n)) :=
    hN n hn s (by simpa [hsCard] using hdense)
  simpa [s, Set.Finite.coe_toFinset] using hsLine

end Erdos171
