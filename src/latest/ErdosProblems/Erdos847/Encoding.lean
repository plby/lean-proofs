/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The ternary-word encoding used for Erdős 847

This file isolates the elementary encoding layer needed by the RRS construction.
Words in `Fin m → Fin 3` are read as base-six integers.  Base six is large enough
that a three-term arithmetic progression of encoded words has no carries, so it
is exactly a coordinatewise midpoint.  For three-letter words this means that
each coordinate is constant, `0,1,2`, or `2,1,0`.
-/

namespace Erdos847Encoding

open Set

/-- A word of length `m` over the three-letter alphabet. -/
abbrev Word (m : ℕ) := Fin m → Fin 3

/-- Interpret a ternary word using place values `6^i`.

This is the specialization to alphabet size three of the Hales--Jewett encoding
used in the formalization of Erdős 966.
-/
noncomputable def encode (m : ℕ) (v : Word m) : ℕ :=
  ∑ i : Fin m, (v i).val * 6 ^ (i : ℕ)

/-- The coordinate condition forced by a three-term arithmetic progression of
encoded words.  The word `v` is the coordinatewise midpoint of `u` and `w`.
-/
def IsWeakQuasiLine {m : ℕ} (u v w : Word m) : Prop :=
  ∀ i, (u i : ℕ) + (w i : ℕ) = 2 * (v i : ℕ)

/-- A nonconstant coordinatewise midpoint triple. -/
def IsQuasiLine {m : ℕ} (u v w : Word m) : Prop :=
  u ≠ w ∧ IsWeakQuasiLine u v w

/-- A set of words is quasiline-free if every coordinatewise midpoint triple in
the set is constant. -/
def QuasiLineFree {m : ℕ} (S : Set (Word m)) : Prop :=
  ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → ∀ ⦃w⦄, w ∈ S →
    IsWeakQuasiLine u v w → u = w

/-- The base-six word encoding is injective. -/
theorem encode_injective (m : ℕ) : Function.Injective (encode m) := by
  intro v w hvw
  have h_eq : ∀ i, v i = w i := by
    induction m with
    | zero => simp
    | succ m ih =>
        have h0 : v 0 = w 0 := by
          have hmod := congrArg (· % 6) hvw
          unfold encode at hmod
          simp only [Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
            mul_one, Fin.val_succ] at hmod
          simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul] at hmod
          simp [Nat.add_mod] at hmod
          apply Fin.ext
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
          exact hmod
        have htail :
            encode m (fun i ↦ v i.succ) = encode m (fun i ↦ w i.succ) := by
          unfold encode at hvw ⊢
          simp only [Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
            mul_one, Fin.val_succ] at hvw
          simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul] at hvw
          rw [h0] at hvw
          exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 6) (Nat.add_left_cancel hvw)
        exact fun i ↦ Fin.cases h0 (ih htail) i
  funext i
  exact h_eq i

/-- Classification of midpoints in the alphabet `{0,1,2}`. -/
theorem fin3_midpoint_iff (x y z : Fin 3) :
    (x : ℕ) + (z : ℕ) = 2 * (y : ℕ) ↔
      (x = y ∧ y = z) ∨
      (x = 0 ∧ y = 1 ∧ z = 2) ∨
      (x = 2 ∧ y = 1 ∧ z = 0) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- A weak quasiline is equivalently coordinatewise constant, forward, or
reverse.  The orientation is allowed to vary between coordinates. -/
theorem isWeakQuasiLine_iff {m : ℕ} (u v w : Word m) :
    IsWeakQuasiLine u v w ↔
      ∀ i,
        (u i = v i ∧ v i = w i) ∨
        (u i = 0 ∧ v i = 1 ∧ w i = 2) ∨
        (u i = 2 ∧ v i = 1 ∧ w i = 0) := by
  simp only [IsWeakQuasiLine, fin3_midpoint_iff]

/-- Carry-free reflection: an arithmetic midpoint of encoded words is a
coordinatewise midpoint. -/
theorem encode_reflects_midpoint {m : ℕ} (u v w : Word m)
    (h : encode m u + encode m w = 2 * encode m v) :
    IsWeakQuasiLine u v w := by
  unfold IsWeakQuasiLine
  unfold encode at h
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
        mul_one, Fin.val_succ] at h
      have hfirst : (u 0).val + (w 0).val = 2 * (v 0).val := by
        have hmod := congrArg (· % 6) h
        simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul] at hmod
        simp [Nat.add_mod, Nat.mul_mod] at hmod
        simpa [Nat.mod_eq_of_lt (by omega : (u 0).val + (w 0).val < 6),
          Nat.mod_eq_of_lt (by omega : 2 * (v 0).val < 6)] using hmod
      have htail :
          (∑ i : Fin m, (u i.succ).val * 6 ^ (i : ℕ)) +
              ∑ i : Fin m, (w i.succ).val * 6 ^ (i : ℕ) =
            2 * ∑ i : Fin m, (v i.succ).val * 6 ^ (i : ℕ) := by
        simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul] at h
        omega
      exact fun i ↦ Fin.cases hfirst
        (ih (fun j ↦ u j.succ) (fun j ↦ v j.succ) (fun j ↦ w j.succ) htail) i

/-- Consequently every nonconstant encoded 3-AP comes from a quasiline. -/
theorem encode_reflects_nonconstant_threeAP {m : ℕ} (u v w : Word m)
    (h : encode m u + encode m w = 2 * encode m v)
    (hne : encode m u ≠ encode m w) :
    IsQuasiLine u v w := by
  refine ⟨?_, encode_reflects_midpoint u v w h⟩
  intro huw
  exact hne (congrArg (encode m) huw)

/-- The preceding reflection written in the explicit coordinate form used in
combinatorial arguments. -/
theorem encode_reflects_nonconstant_threeAP_coordinates {m : ℕ}
    (u v w : Word m)
    (h : encode m u + encode m w = 2 * encode m v)
    (hne : encode m u ≠ encode m w) :
    u ≠ w ∧
      ∀ i,
        (u i = v i ∧ v i = w i) ∨
        (u i = 0 ∧ v i = 1 ∧ w i = 2) ∨
        (u i = 2 ∧ v i = 1 ∧ w i = 0) := by
  rw [← isWeakQuasiLine_iff]
  exact encode_reflects_nonconstant_threeAP u v w h hne

private def optionBase : Option (Fin 3) → ℕ
  | none => 0
  | some x => (x : ℕ)

private def optionMask : Option (Fin 3) → ℕ
  | none => 1
  | some _ => 0

private noncomputable def lineBase {m : ℕ}
    (L : Combinatorics.Line (Fin 3) (Fin m)) : ℕ :=
  ∑ i : Fin m, optionBase (L.idxFun i) * 6 ^ (i : ℕ)

private noncomputable def lineStep {m : ℕ}
    (L : Combinatorics.Line (Fin 3) (Fin m)) : ℕ :=
  ∑ i : Fin m, optionMask (L.idxFun i) * 6 ^ (i : ℕ)

private theorem encode_line_affine {m : ℕ}
    (L : Combinatorics.Line (Fin 3) (Fin m)) (x : Fin 3) :
    encode m (L x) = lineBase L + (x : ℕ) * lineStep L := by
  unfold encode lineBase lineStep
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hidx : L.idxFun i <;>
    simp [Combinatorics.Line.coe_apply, hidx, optionBase, optionMask]

private theorem lineStep_pos {m : ℕ}
    (L : Combinatorics.Line (Fin 3) (Fin m)) : 0 < lineStep L := by
  rcases L.proper with ⟨i, hi⟩
  have hle : 6 ^ (i : ℕ) ≤ lineStep L := by
    unfold lineStep
    have := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin m ↦ optionMask (L.idxFun j) * 6 ^ (j : ℕ))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    simpa [hi, optionMask] using this
  exact lt_of_lt_of_le (by positivity) hle

/-- A combinatorial line gives a genuine (positive-step) three-term arithmetic
progression after encoding. -/
theorem encode_line_to_AP {m : ℕ}
    (L : Combinatorics.Line (Fin 3) (Fin m)) :
    ∃ a d : ℕ, 0 < d ∧
      encode m (L 0) = a ∧
      encode m (L 1) = a + d ∧
      encode m (L 2) = a + 2 * d := by
  refine ⟨lineBase L, lineStep L, lineStep_pos L, ?_, ?_, ?_⟩
  · simpa using encode_line_affine L (0 : Fin 3)
  · simpa using encode_line_affine L (1 : Fin 3)
  · simpa using encode_line_affine L (2 : Fin 3)

/-- In particular, the endpoints of the encoded image of a combinatorial line
are distinct and its middle point is their arithmetic mean. -/
theorem encode_line_is_nonconstant_threeAP {m : ℕ}
    (L : Combinatorics.Line (Fin 3) (Fin m)) :
    encode m (L 0) + encode m (L 2) =
        encode m (L 1) + encode m (L 1) ∧
      encode m (L 0) ≠ encode m (L 2) := by
  rcases encode_line_to_AP L with ⟨a, d, hd, h0, h1, h2⟩
  constructor
  · omega
  · omega

/-- A combinatorial line is a quasiline (in fact all its varying coordinates
have the forward orientation). -/
theorem line_isQuasiLine {m : ℕ}
    (L : Combinatorics.Line (Fin 3) (Fin m)) :
    IsQuasiLine (L 0) (L 1) (L 2) := by
  have hAP := encode_line_is_nonconstant_threeAP L
  apply encode_reflects_nonconstant_threeAP (L 0) (L 1) (L 2)
  · simpa [two_mul] using hAP.1
  · exact hAP.2

/-- The set-level transport lemma: deleting all quasilines in word space is
enough to delete all nontrivial three-term arithmetic progressions after the
base-six encoding. -/
theorem threeAPFree_image_encode {m : ℕ} {S : Set (Word m)}
    (hS : QuasiLineFree S) :
    ThreeAPFree (encode m '' S) := by
  rw [threeAPFree_iff_eq_right]
  rintro a ⟨u, hu, rfl⟩ b ⟨v, hv, rfl⟩ c ⟨w, hw, rfl⟩ habc
  apply congrArg (encode m)
  exact hS hu hv hw (encode_reflects_midpoint u v w (by simpa [two_mul] using habc))

/-- Finset form of `threeAPFree_image_encode`. -/
theorem threeAPFree_finset_image_encode {m : ℕ} {S : Finset (Word m)}
    (hS : QuasiLineFree (S : Set (Word m))) :
    ThreeAPFree ((S.image (encode m) : Finset ℕ) : Set ℕ) := by
  rw [show ((S.image (encode m) : Finset ℕ) : Set ℕ) =
      encode m '' (S : Set (Word m)) by ext; simp]
  exact threeAPFree_image_encode hS

end Erdos847Encoding
