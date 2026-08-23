/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.Chang
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Combinatorics.Pigeonhole

/-!
# Quantitative cardinality of cyclic Bohr sets

The proof discretizes the principal arguments of the defining characters.
Two group elements with the same argument bins differ by an element of the
Bohr set.  Pigeonhole then supplies a large fiber.
-/

namespace Erdos721

open AddChar Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

/-- Unit complex numbers are Lipschitz in their principal arguments. -/
lemma norm_sub_le_abs_arg_sub_of_norm_eq_one {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z - w‖ ≤ |z.arg - w.arg| := by
  have hzexp : Complex.exp (z.arg * Complex.I) = z := by
    calc
      Complex.exp (z.arg * Complex.I) =
          ‖z‖ * Complex.exp (z.arg * Complex.I) := by simp [hz]
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  have hwexp : Complex.exp (w.arg * Complex.I) = w := by
    calc
      Complex.exp (w.arg * Complex.I) =
          ‖w‖ * Complex.exp (w.arg * Complex.I) := by simp [hw]
      _ = w := Complex.norm_mul_exp_arg_mul_I w
  calc
    ‖z - w‖ =
        ‖Complex.exp (z.arg * Complex.I) - Complex.exp (w.arg * Complex.I)‖ := by
      rw [hzexp, hwexp]
    _ =
        ‖Complex.exp (w.arg * Complex.I) *
          (Complex.exp ((z.arg - w.arg) * Complex.I) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    _ = ‖Complex.exp ((z.arg - w.arg) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp]
      simp
    _ ≤ |z.arg - w.arg| := by
      simpa [mul_comm, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := z.arg - w.arg))

/-- The argument coordinate, rescaled from `(-π,π]` to `[0,m]`. -/
noncomputable def scaledArg (m : ℕ) (z : ℂ) : ℝ :=
  (z.arg + Real.pi) * m / (2 * Real.pi)

lemma scaledArg_nonneg (m : ℕ) (z : ℂ) : 0 ≤ scaledArg m z := by
  unfold scaledArg
  have hz : 0 ≤ z.arg + Real.pi := by linarith [Complex.neg_pi_lt_arg z]
  positivity

lemma scaledArg_le (m : ℕ) (z : ℂ) : scaledArg m z ≤ m := by
  unfold scaledArg
  have hz : z.arg + Real.pi ≤ 2 * Real.pi := by
    linarith [Complex.arg_le_pi z]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [div_le_iff₀ hpi]
  nlinarith

/-- The principal-argument bin among `m+1` possible bins.  The extra endpoint
bin handles the value `arg z = π`. -/
noncomputable def argBin (m : ℕ) (z : ℂ) : Fin (m + 1) :=
  ⟨⌊scaledArg m z⌋₊, by
    rw [Nat.floor_lt' (Nat.add_one_ne_zero m)]
    exact (scaledArg_le m z).trans_lt (by exact_mod_cast Nat.lt_succ_self m)⟩

lemma abs_scaledArg_sub_lt_one_of_argBin_eq {m : ℕ} {z w : ℂ}
    (hbin : argBin m z = argBin m w) :
    |scaledArg m z - scaledArg m w| < 1 := by
  have hfloor : ⌊scaledArg m z⌋₊ = ⌊scaledArg m w⌋₊ :=
    congrArg Fin.val hbin
  have hfloorR : (⌊scaledArg m z⌋₊ : ℝ) = ⌊scaledArg m w⌋₊ := by
    exact_mod_cast hfloor
  have hzlow : (⌊scaledArg m z⌋₊ : ℝ) ≤ scaledArg m z :=
    Nat.floor_le (scaledArg_nonneg m z)
  have hwlow : (⌊scaledArg m w⌋₊ : ℝ) ≤ scaledArg m w :=
    Nat.floor_le (scaledArg_nonneg m w)
  have hzup : scaledArg m z < (⌊scaledArg m z⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hwup : scaledArg m w < (⌊scaledArg m w⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [abs_lt]
  constructor <;> nlinarith

/-- Equal nontrivial argument bins force nearby principal arguments. -/
lemma abs_arg_sub_lt_of_argBin_eq {m : ℕ} (hm : 0 < m) {z w : ℂ}
    (hbin : argBin m z = argBin m w) :
    |z.arg - w.arg| < 2 * Real.pi / m := by
  have h := abs_scaledArg_sub_lt_one_of_argBin_eq hbin
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : 0 < 2 * Real.pi := by positivity
  have hscale :
      |scaledArg m z - scaledArg m w| =
        |z.arg - w.arg| * (m : ℝ) / (2 * Real.pi) := by
    have heq : scaledArg m z - scaledArg m w =
        (z.arg - w.arg) * (m : ℝ) / (2 * Real.pi) := by
      unfold scaledArg
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hmR, abs_of_pos hpi]
  rw [hscale] at h
  rw [lt_div_iff₀ hmR]
  exact (div_lt_one hpi).mp h

/-- The argument-bin code of a group element across all defining
frequencies of a Bohr set. -/
noncomputable def argumentCode (B : Set N) (m : ℕ) (x : ZMod N) :
    (r : ↥B.frequencies) → Fin (m + 1) :=
  fun r ↦ argBin m (character r.1 x)

@[simp] lemma card_argumentCodeSpace (B : Set N) (m : ℕ) :
    Fintype.card ((r : ↥B.frequencies) → Fin (m + 1)) =
      (m + 1) ^ B.rank := by
  simp [Set.rank]

/-- Chord distance between a quotient character and one equals the chord
distance between its two numerator values. -/
lemma norm_one_sub_character_sub (r x y : ZMod N) :
    ‖1 - character r (x - y)‖ = ‖character r x - character r y‖ := by
  have hy : character r y ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_character]; norm_num)
  rw [AddChar.map_sub_eq_div, one_sub_div hy, norm_div, norm_character]
  simp [norm_sub_rev]

/-- Equal codes imply that the difference lies in the Bohr set, provided the
bin width is at most its radius. -/
lemma sub_mem_of_argumentCode_eq (B : Set N) {m : ℕ} (hm : 0 < m)
    (hwidth : 2 * Real.pi / m ≤ B.radius) {x y : ZMod N}
    (hcode : argumentCode B m x = argumentCode B m y) :
    x - y ∈ B := by
  rw [Set.mem_iff]
  intro r hr
  have hbin : argBin m (character r x) = argBin m (character r y) := by
    exact congrFun hcode ⟨r, hr⟩
  calc
    ‖1 - character r (x - y)‖ = ‖character r x - character r y‖ :=
      norm_one_sub_character_sub r x y
    _ ≤ |(character r x).arg - (character r y).arg| :=
      norm_sub_le_abs_arg_sub_of_norm_eq_one (norm_character r x) (norm_character r y)
    _ ≤ 2 * Real.pi / m := (abs_arg_sub_lt_of_argBin_eq hm hbin).le
    _ ≤ B.radius := hwidth

/-- Quantitative pigeonhole lower bound for a cyclic Bohr set. -/
theorem natDiv_codeCard_le_card_carrier (B : Set N) {m : ℕ} (hm : 0 < m)
    (hwidth : 2 * Real.pi / m ≤ B.radius) :
    N / (m + 1) ^ B.rank ≤ B.carrier.card := by
  let Q := (r : ↥B.frequencies) → Fin (m + 1)
  let code : ZMod N → Q := argumentCode B m
  have hQ : Fintype.card Q = (m + 1) ^ B.rank := by
    simpa [Q] using card_argumentCodeSpace B m
  have hpigeon : Fintype.card Q * (N / Fintype.card Q) ≤
      Fintype.card (ZMod N) := by
    rw [ZMod.card]
    exact Nat.mul_div_le N (Fintype.card Q)
  obtain ⟨q, hq⟩ :=
    Fintype.exists_le_card_fiber_of_mul_le_card (f := code) hpigeon
  let S : Finset (ZMod N) := Finset.univ.filter fun x ↦ code x = q
  have hScard : N / Fintype.card Q ≤ S.card := by
    simpa [S] using hq
  by_cases hzero : N / Fintype.card Q = 0
  · rw [hQ] at hzero
    rw [hzero]
    exact Nat.zero_le _
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le
    (Nat.pos_of_ne_zero hzero) hScard)
  obtain ⟨x₀, hx₀⟩ := hSnonempty
  let e : ZMod N ↪ ZMod N := (Equiv.subRight x₀).toEmbedding
  have hmap : S.map e ⊆ B.carrier := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨x, hxS, rfl⟩ := hz
    have hcodex : code x = q := by simpa [S] using hxS
    have hcodex₀ : code x₀ = q := by simpa [S] using hx₀
    exact sub_mem_of_argumentCode_eq B hm hwidth (hcodex.trans hcodex₀.symm)
  calc
    N / (m + 1) ^ B.rank = N / Fintype.card Q := by rw [hQ]
    _ ≤ S.card := hScard
    _ = (S.map e).card := (Finset.card_map e).symm
    _ ≤ B.carrier.card := Finset.card_le_card hmap

/-! ## Radius-independent relative doubling -/

/-- Membership in a chord Bohr set bounds the principal argument of every
defining character by twice the radius. -/
lemma abs_arg_character_le_two_radius (B : Set N) {x r : ZMod N}
    (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    |(character r x).arg| ≤ 2 * B.radius := by
  have hnorm := Set.mem_iff.mp hx r hr
  have hangle := Complex.angle_le_mul_norm_sub
    (norm_character r x) (by norm_num : ‖(1 : ℂ)‖ = 1)
  calc
    |(character r x).arg| = InnerProductGeometry.angle (character r x) 1 :=
      (Complex.angle_one_right (norm_ne_zero_iff.mp (by
        rw [norm_character]
        norm_num))).symm
    _ ≤ Real.pi / 2 * ‖character r x - 1‖ := hangle
    _ = Real.pi / 2 * ‖1 - character r x‖ := by rw [norm_sub_rev]
    _ ≤ Real.pi / 2 * B.radius :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ 2 * B.radius := by
      apply mul_le_mul_of_nonneg_right _ B.radius_nonneg
      linarith [Real.pi_lt_four]

/-- Argument coordinate normalized to the interval `[0,8]` for elements of a
Bohr set. -/
noncomputable def localScaledArg (B : Set N) (z : ℂ) : ℝ :=
  2 * (z.arg + 2 * B.radius) / B.radius

lemma localScaledArg_nonneg (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    0 ≤ localScaledArg B (character r x) := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  have hsum : 0 ≤ (character r x).arg + 2 * B.radius := by linarith [harg.1]
  exact div_nonneg (mul_nonneg (by norm_num) hsum) hB.le

lemma localScaledArg_le_eight (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    localScaledArg B (character r x) ≤ 8 := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  rw [div_le_iff₀ hB]
  linarith

/-- One of nine local argument bins. -/
noncomputable def localArgBin (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) (r : ↥B.frequencies) : Fin 9 :=
  ⟨⌊localScaledArg B (character r.1 x.1)⌋₊, by
    rw [Nat.floor_lt' (by norm_num : (9 : ℕ) ≠ 0)]
    exact (localScaledArg_le_eight B hB x.2 r.2).trans_lt (by norm_num)⟩

/-- The nine-bin code on the elements of a Bohr set. -/
noncomputable def localArgumentCode (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) : (r : ↥B.frequencies) → Fin 9 :=
  fun r ↦ localArgBin B hB x r

@[simp] lemma card_localArgumentCodeSpace (B : Set N) :
    Fintype.card ((r : ↥B.frequencies) → Fin 9) = 9 ^ B.rank := by
  simp [Set.rank]

lemma abs_localScaledArg_sub_lt_one_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |localScaledArg B (character r.1 x.1) -
      localScaledArg B (character r.1 y.1)| < 1 := by
  have hfloor :
      ⌊localScaledArg B (character r.1 x.1)⌋₊ =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ :=
    congrArg Fin.val hbin
  have hfloorR :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ := by
    exact_mod_cast hfloor
  have hxlow :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 x.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB x.2 r.2)
  have hylow :
      (⌊localScaledArg B (character r.1 y.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 y.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB y.2 r.2)
  have hxup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 x.1))
  have hyup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 y.1))
  rw [abs_lt]
  constructor <;> nlinarith

lemma abs_arg_sub_lt_half_radius_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |(character r.1 x.1).arg - (character r.1 y.1).arg| < B.radius / 2 := by
  have h := abs_localScaledArg_sub_lt_one_of_localArgBin_eq B hB hbin
  have hscale :
      |localScaledArg B (character r.1 x.1) -
        localScaledArg B (character r.1 y.1)| =
      2 * |(character r.1 x.1).arg - (character r.1 y.1).arg| / B.radius := by
    have heq :
        localScaledArg B (character r.1 x.1) -
          localScaledArg B (character r.1 y.1) =
        2 * ((character r.1 x.1).arg - (character r.1 y.1).arg) /
          B.radius := by
      unfold localScaledArg
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hB]
    norm_num
  rw [hscale] at h
  rw [div_lt_iff₀ hB] at h
  linarith

/-- Equal local codes differ by an element of the half-radius dilate. -/
lemma sub_mem_half_dilate_of_localArgumentCode_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    (hcode : localArgumentCode B hB x = localArgumentCode B hB y) :
    x.1 - y.1 ∈ B.dilate (1 / 2 : ℝ) := by
  rw [Set.mem_iff]
  intro r hr
  have hbin : localArgBin B hB x ⟨r, hr⟩ =
      localArgBin B hB y ⟨r, hr⟩ := congrFun hcode ⟨r, hr⟩
  calc
    ‖1 - character r (x.1 - y.1)‖ =
        ‖character r x.1 - character r y.1‖ :=
      norm_one_sub_character_sub r x.1 y.1
    _ ≤ |(character r x.1).arg - (character r y.1).arg| :=
      norm_sub_le_abs_arg_sub_of_norm_eq_one
        (norm_character r x.1) (norm_character r y.1)
    _ ≤ B.radius / 2 :=
      (abs_arg_sub_lt_half_radius_of_localArgBin_eq B hB hbin).le
    _ = (B.dilate (1 / 2 : ℝ)).radius := by
      simp [div_eq_mul_inv, mul_comm]

/-- Radius-independent relative doubling: every Bohr set is covered, in the
cardinality sense, by at most `9^rank` translates of its half-radius dilate. -/
theorem card_carrier_le_nine_pow_rank_mul_card_half
    (B : Set N) (hB : 0 < B.radius) :
    B.carrier.card ≤ 9 ^ B.rank * (B.dilate (1 / 2 : ℝ)).carrier.card := by
  let Q := (r : ↥B.frequencies) → Fin 9
  let code : ↥B.carrier → Q := localArgumentCode B hB
  have hQ : Fintype.card Q = 9 ^ B.rank := by
    simpa [Q] using card_localArgumentCodeSpace B
  have hmain : Fintype.card ↥B.carrier ≤
      Fintype.card Q * (B.dilate (1 / 2 : ℝ)).carrier.card := by
    by_contra hbound
    rw [not_le] at hbound
    obtain ⟨q, hq⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := code) hbound
    let S : Finset ↥B.carrier := Finset.univ.filter fun x ↦ code x = q
    have hScard : (B.dilate (1 / 2 : ℝ)).carrier.card < S.card := by
      simpa [S] using hq
    have hSnonempty : S.Nonempty := Finset.card_pos.mp
      (lt_of_le_of_lt (Nat.zero_le _) hScard)
    obtain ⟨x₀, hx₀⟩ := hSnonempty
    let e : ↥B.carrier ↪ ZMod N :=
      ⟨fun x ↦ x.1 - x₀.1, by
        intro x y hxy
        apply Subtype.ext
        exact (Equiv.subRight x₀.1).injective hxy⟩
    have hmap : S.map e ⊆ (B.dilate (1 / 2 : ℝ)).carrier := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨x, hxS, rfl⟩ := hz
      have hcodex : code x = q := by simpa [S] using hxS
      have hcodex₀ : code x₀ = q := by simpa [S] using hx₀
      exact sub_mem_half_dilate_of_localArgumentCode_eq B hB
        (hcodex.trans hcodex₀.symm)
    have hle : S.card ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := by
      calc
        S.card = (S.map e).card := (Finset.card_map e).symm
        _ ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := Finset.card_le_card hmap
    omega
  rw [hQ] at hmain
  have hcardcoe : Fintype.card ↥B.carrier = B.carrier.card :=
    Fintype.card_coe B.carrier
  rw [hcardcoe] at hmain
  exact hmain

end CyclicBohr
end Erdos721
