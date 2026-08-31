/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 13.
https://www.erdosproblems.com/forum/thread/13

Informal authors:
- Borys Bedert

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos13.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/13.lean
-/
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

import Mathlib
import ErdosProblems.Erdos13.Erdos13Additive

/-!
# Erdős Problem 13

We formalize Bedert's resolution of the finite property-P problem.  The
mathematical proof and a dependency-by-dependency formalization plan are in
`tex/13.tex` at the repository root.

Reference: B. Bedert, *On a problem of Erdős and Sárközy about sequences
with no term dividing the sum of two larger terms*, arXiv:2301.07065.
-/

open Finset Nat
open scoped Pointwise

namespace Erdos13

/-- A finite set has property P if none of its elements divides a sum of two
strictly larger elements of the set. -/
def IsForbiddenTripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < min b c → ¬a ∣ b + c

namespace IsForbiddenTripleFree

lemma mono {A B : Finset ℕ} (hA : IsForbiddenTripleFree A) (hBA : B ⊆ A) :
    IsForbiddenTripleFree B := by
  intro a ha b hb c hc hlt
  exact hA a (hBA ha) b (hBA hb) c (hBA hc) hlt

lemma not_dvd_add {A : Finset ℕ} (hA : IsForbiddenTripleFree A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) : ¬a ∣ b + c := by
  exact hA a ha b hb c hc (by simpa [lt_min_iff] using And.intro hab hac)

lemma not_dvd_two_mul {A : Finset ℕ} (hA : IsForbiddenTripleFree A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) : ¬a ∣ 2 * b := by
  simpa [two_mul] using hA.not_dvd_add ha hb hb hab hab

lemma not_dvd_of_lt {A : Finset ℕ} (hA : IsForbiddenTripleFree A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) : ¬a ∣ b := by
  intro hdvd
  exact hA.not_dvd_two_mul ha hb hab (hdvd.mul_left 2)

lemma not_mem_mul_left {A : Finset ℕ} (hA : IsForbiddenTripleFree A)
    {a k : ℕ} (ha : a ∈ A) (ha_pos : 0 < a) (hk : 2 ≤ k) : k * a ∉ A := by
  intro hka
  have ha_lt : a < k * a := by
    nlinarith
  exact hA.not_dvd_of_lt ha hka ha_lt (dvd_mul_left a k)

lemma pos_of_mem {A : Finset ℕ} (_hA : IsForbiddenTripleFree A)
    (hsub : A ⊆ Icc 1 N) {a : ℕ} (ha : a ∈ A) : 0 < a := by
  have := (mem_Icc.mp (hsub ha)).1
  omega

lemma map_div {A : Finset ℕ} (hA : IsForbiddenTripleFree A) {k : ℕ} (hk : 0 < k)
    (hdiv : ∀ a ∈ A, k ∣ a) :
    IsForbiddenTripleFree (A.image (fun a ↦ a / k)) := by
  intro a ha b hb c hc hlt
  simp only [mem_image] at ha hb hc
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hc
  intro hdvd
  have ha_eq : k * (a' / k) = a' := by
    simpa [mul_comm] using Nat.mul_div_cancel' (hdiv a' ha')
  have hb_eq : k * (b' / k) = b' := by
    simpa [mul_comm] using Nat.mul_div_cancel' (hdiv b' hb')
  have hc_eq : k * (c' / k) = c' := by
    simpa [mul_comm] using Nat.mul_div_cancel' (hdiv c' hc')
  have hlt' : a' < min b' c' := by
    rw [← ha_eq, ← hb_eq, ← hc_eq, min_mul_mul_left]
    exact (Nat.mul_lt_mul_left hk).2 hlt
  apply hA a' ha' b' hb' c' hc' hlt'
  obtain ⟨d, hd⟩ := hdvd
  refine ⟨d, ?_⟩
  have hkd := congrArg (fun x ↦ k * x) hd
  calc
    b' + c' = k * (a' / k * d) := by simpa [mul_add, hb_eq, hc_eq] using hkd
    _ = (k * (a' / k)) * d := by rw [mul_assoc]
    _ = a' * d := by rw [ha_eq]

end IsForbiddenTripleFree

namespace Bedert

/-! We use integer inequalities throughout.  Thus, for example,
`ratSection A N 2 3 1 1` is `A ∩ (2N/3,N]`; no rounding convention is hidden
in the notation. -/

/-- The part of `A` cut out by `p * N < q * x` and `s * x ≤ r * N`. -/
def ratSection (A : Finset ℕ) (N p q r s : ℕ) : Finset ℕ :=
  A.filter fun x ↦ p * N < q * x ∧ s * x ≤ r * N

/-- The elements of a finset in one residue class. -/
def residue (A : Finset ℕ) (r q : ℕ) : Finset ℕ :=
  A.filter fun x ↦ x % q = r % q

@[simp] lemma mem_ratSection {A : Finset ℕ} {N p q r s x : ℕ} :
    x ∈ ratSection A N p q r s ↔ x ∈ A ∧ p * N < q * x ∧ s * x ≤ r * N := by
  simp [ratSection]

@[simp] lemma mem_residue {A : Finset ℕ} {r q x : ℕ} :
    x ∈ residue A r q ↔ x ∈ A ∧ x % q = r % q := by
  simp [residue]

lemma ratSection_subset (A : Finset ℕ) (N p q r s : ℕ) :
    ratSection A N p q r s ⊆ A := by
  intro x hx
  exact (mem_ratSection.mp hx).1

lemma residue_subset (A : Finset ℕ) (r q : ℕ) : residue A r q ⊆ A := by
  intro x hx
  exact (mem_residue.mp hx).1

/-- Quotient by `q` is injective on a fixed residue class modulo a positive `q`. -/
lemma div_injOn_residue {S : Finset ℕ} {r q : ℕ} (_hq : 0 < q)
    (hS : ∀ x ∈ S, x % q = r % q) : Set.InjOn (fun x : ℕ ↦ x / q) S := by
  intro x hx y hy hxy
  change x / q = y / q at hxy
  have hmod : x % q = y % q := (hS x hx).trans (hS y hy).symm
  calc
    x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
    _ = q * (y / q) + y % q := by rw [hxy, hmod]
    _ = y := Nat.div_add_mod y q

/-- A fixed residue class has at most the obvious number of elements in an
integer interval.  This deliberately uses a slightly loose lower endpoint;
the loss is at most one and is convenient in every later application. -/
lemma card_residue_Icc_le {S : Finset ℕ} {L U r q : ℕ} (hq : 0 < q)
    (hS : S ⊆ Icc L U) (hres : ∀ x ∈ S, x % q = r % q) :
    S.card ≤ (U / q + 1) - (L / q) := by
  let f : ℕ → ℕ := fun x ↦ x / q
  have hinj : Set.InjOn f S := div_injOn_residue hq hres
  have himage : S.image f ⊆ Icc (L / q) (U / q) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxI := mem_Icc.mp (hS hx)
    exact mem_Icc.mpr ⟨Nat.div_le_div_right hxI.1, Nat.div_le_div_right hxI.2⟩
  calc
    S.card = (S.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Icc (L / q) (U / q)).card := card_le_card himage
    _ = (U / q + 1) - (L / q) := by simp

lemma card_Icc_le {S : Finset ℕ} {L U : ℕ} (hS : S ⊆ Icc L U) :
    S.card ≤ (U + 1) - L := by
  simpa using card_le_card hS

/-- Packing disjoint blocks of `q` consecutive integers after the members of
one residue class gives the sharp interval-capacity estimate. -/
lemma mul_card_fixed_zmod_le {S : Finset ℕ} {L U q : ℕ} (i : ZMod q)
    (hS : S ⊆ Icc L U) (hres : ∀ x ∈ S, (x : ZMod q) = i) :
    q * S.card ≤ (U + q) - L := by
  let f : ℕ × ℕ → ℕ := fun xt ↦ xt.1 + xt.2
  let P := S ×ˢ range q
  have hinj : Set.InjOn f P := by
    rintro ⟨x, t⟩ hxt ⟨y, u⟩ hyu heq
    have hxt' : x ∈ S ∧ t < q := by
      change (x, t) ∈ P at hxt
      simpa [P] using hxt
    have hyu' : y ∈ S ∧ u < q := by
      change (y, u) ∈ P at hyu
      simpa [P] using hyu
    have hz : (t : ZMod q) = (u : ZMod q) := by
      have hzsum := congrArg (fun n : ℕ ↦ (n : ZMod q)) heq
      simp only [f, Nat.cast_add] at hzsum
      rw [hres x hxt'.1, hres y hyu'.1] at hzsum
      exact add_left_cancel hzsum
    have htu : t = u := by
      have hzval := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hxt'.2, ZMod.val_natCast_of_lt hyu'.2] at hzval
      exact hzval
    subst u
    change x + t = y + t at heq
    have hxy := Nat.add_right_cancel heq
    subst y
    rfl
  have himage : P.image f ⊆ Ico L (U + q) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨⟨x, t⟩, hxt, rfl⟩ := hz
    simp only [P, mem_product, mem_range] at hxt
    have hx := mem_Icc.mp (hS hxt.1)
    apply mem_Ico.mpr
    change L ≤ x + t ∧ x + t < U + q
    omega
  calc
    q * S.card = P.card := by simp [P, mul_comm]
    _ = (P.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Ico L (U + q)).card := card_le_card himage
    _ = (U + q) - L := by simp

lemma card_add_card_le_of_disjoint_subsets {X Y U : Finset ℕ}
    (hXY : Disjoint X Y) (hX : X ⊆ U) (hY : Y ⊆ U) :
    X.card + Y.card ≤ U.card := by
  rw [← card_union_of_disjoint hXY]
  exact card_le_card (union_subset hX hY)

/-- The disjointness at the heart of Bedert's packing lemma.  Each element
of `k · B` is a multiple of a low element of `A`, whereas `S` consists of
sums of two high elements. -/
lemma mul_image_disjoint_sumset {A B H S : Finset ℕ} {k t : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hB : ∀ b ∈ B, ∃ a ∈ A, a ≤ t ∧ a ∣ k * b)
    (hH : ∀ x ∈ H, x ∈ A ∧ t < x)
    (hS : S ⊆ H + H) :
    Disjoint (B.image fun b ↦ k * b) S := by
  rw [Finset.disjoint_left]
  intro z hzB hzS
  simp only [Finset.mem_image] at hzB
  obtain ⟨b, hb, rfl⟩ := hzB
  obtain ⟨a, ha, hat, hadiv⟩ := hB b hb
  have hsum := hS hzS
  simp only [Finset.mem_add] at hsum
  obtain ⟨x, hx, y, hy, hxy⟩ := hsum
  have hxA := hH x hx
  have hyA := hH y hy
  apply hP.not_dvd_add ha hxA.1 hyA.1 (lt_of_le_of_lt hat hxA.2)
    (lt_of_le_of_lt hat hyA.2)
  rw [hxy]
  exact hadiv

/-- A cardinality form of the packing lemma, with the ambient residue-class
set supplied explicitly. -/
lemma packing {A B H S U : Finset ℕ} {k t : ℕ} (hk : 0 < k)
    (hP : IsForbiddenTripleFree A)
    (hB : ∀ b ∈ B, ∃ a ∈ A, a ≤ t ∧ a ∣ k * b)
    (hH : ∀ x ∈ H, x ∈ A ∧ t < x)
    (hSsum : S ⊆ H + H)
    (hBU : B.image (fun b ↦ k * b) ⊆ U) (hSU : S ⊆ U) :
    B.card + S.card ≤ U.card := by
  have hinj : Function.Injective (fun b : ℕ ↦ k * b) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  have hcard : (B.image fun b ↦ k * b).card = B.card := card_image_of_injective _ hinj
  rw [← hcard]
  exact card_add_card_le_of_disjoint_subsets
    (mul_image_disjoint_sumset hP hB hH hSsum) hBU hSU

/-- A fiber of a natural-number finset in `ZMod q`. -/
def zmodFiber (U : Finset ℕ) (i : ZMod q) : Finset ℕ :=
  U.filter fun x ↦ (x : ZMod q) = i

@[simp] lemma mem_zmodFiber {U : Finset ℕ} {i : ZMod q} {x : ℕ} :
    x ∈ zmodFiber U i ↔ x ∈ U ∧ (x : ZMod q) = i := by
  simp [zmodFiber]

lemma sum_card_zmodFiber (U : Finset ℕ) (q : ℕ) [NeZero q] :
    ∑ i : ZMod q, (zmodFiber U i).card = U.card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := U) (t := Finset.univ)
    (f := fun x : ℕ ↦ (x : ZMod q)) (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Bedert's dense-residue argument in its reusable, denominator-cleared
form.  `D` is any strict upper bound for `q` times the size of one fiber.
The hypothesis `D ≤ 2|U|` forces both fibers in the maximizing opposite
pair to be nonempty. -/
lemma dense_residue {U : Finset ℕ} {q D : ℕ} (hq : 0 < q) (a : ZMod q)
    (hcap : ∀ i : ZMod q, q * (zmodFiber U i).card < D)
    (hdense : D ≤ 2 * U.card) :
    2 * U.card ≤ q * ((zmodFiber (U + U) a).card + 1) := by
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let e : ZMod q ≃ ZMod q :=
    { toFun := fun i ↦ a - i
      invFun := fun i ↦ a - i
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  have hsum : ∑ i : ZMod q, (zmodFiber U i).card = U.card :=
    sum_card_zmodFiber U q
  have he_sum : ∑ i : ZMod q, (zmodFiber U (e i)).card = U.card := by
    calc
      ∑ i : ZMod q, (zmodFiber U (e i)).card =
          ∑ i : ZMod q, (zmodFiber U i).card :=
        e.sum_comp (fun i : ZMod q ↦ (zmodFiber U i).card)
      _ = U.card := hsum
  have hpair_sum :
      ∑ i : ZMod q, ((zmodFiber U i).card + (zmodFiber U (e i)).card) =
        2 * U.card := by
    rw [Finset.sum_add_distrib, hsum, he_sum, two_mul]
  have havg :
      ∃ i : ZMod q, 2 * U.card ≤
        q * ((zmodFiber U i).card + (zmodFiber U (e i)).card) := by
    have hnonempty : (Finset.univ : Finset (ZMod q)).Nonempty := Finset.univ_nonempty
    have hle :
        ∑ _i : ZMod q, 2 * U.card ≤
          ∑ i : ZMod q,
            q * ((zmodFiber U i).card + (zmodFiber U (e i)).card) := by
      have heq :
          ∑ _i : ZMod q, 2 * U.card =
            ∑ i : ZMod q,
              q * ((zmodFiber U i).card + (zmodFiber U (e i)).card) := by
        calc
          ∑ _i : ZMod q, 2 * U.card = q * (2 * U.card) := by
            simp [ZMod.card]
          _ = q * (∑ i : ZMod q,
              ((zmodFiber U i).card + (zmodFiber U (e i)).card)) := by rw [hpair_sum]
          _ = ∑ i : ZMod q,
              q * ((zmodFiber U i).card + (zmodFiber U (e i)).card) := by
            rw [Finset.mul_sum]
      exact heq.le
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hnonempty hle
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := havg
  have hFi : (zmodFiber U i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsmall := hcap (e i)
    simp only [hempty, Finset.card_empty, zero_add] at hi
    omega
  have hFe : (zmodFiber U (e i)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsmall := hcap i
    simp only [hempty, Finset.card_empty, add_zero] at hi
    omega
  have hadd_subset : zmodFiber U i + zmodFiber U (e i) ⊆ zmodFiber (U + U) a := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_zmodFiber.mp hx
    have hy' := mem_zmodFiber.mp hy
    apply mem_zmodFiber.mpr
    refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
    rw [Nat.cast_add, hx'.2, hy'.2]
    change i + (a - i) = a
    abel
  have hCD := cauchy_davenport_add_of_linearOrder_isCancelAdd hFi hFe
  have hpair_le :
      (zmodFiber U i).card + (zmodFiber U (e i)).card ≤
        (zmodFiber (U + U) a).card + 1 := by
    have hsumcard := card_le_card hadd_subset
    omega
  exact hi.trans (Nat.mul_le_mul_left q hpair_le)

/-- Bedert's Lemma 3, written without division: if `U` occupies an
`m`-term interval and `m + q ≤ 2|U|`, then every residue class in `U+U`
contains enough elements to satisfy this inequality. -/
lemma dense_residue_Icc {U : Finset ℕ} {k m q : ℕ} (hq : 0 < q)
    (hU : U ⊆ Icc (k + 1) (k + m)) (hdense : m + q ≤ 2 * U.card)
    (a : ZMod q) :
    2 * U.card ≤ q * ((zmodFiber (U + U) a).card + 1) := by
  apply dense_residue hq a (D := m + q) ?_ hdense
  intro i
  have hsub : zmodFiber U i ⊆ Icc (k + 1) (k + m) := by
    exact (filter_subset _ _).trans hU
  have hres : ∀ x ∈ zmodFiber U i, (x : ZMod q) = i := by
    intro x hx
    exact (mem_zmodFiber.mp hx).2
  have hcap := mul_card_fixed_zmod_le i hsub hres
  omega

/-! ### Power-window maps -/

lemma exists_pow_mul_gt {b L a : ℕ} (hb : 1 < b) (ha : 0 < a) :
    ∃ j : ℕ, L < b ^ j * a := by
  refine ⟨L, (Nat.lt_pow_self hb).trans_le ?_⟩
  calc
    b ^ L = b ^ L * 1 := by simp
    _ ≤ b ^ L * a := Nat.mul_le_mul_left _ ha

/-- The least exponent which moves `a` strictly above `L`.  The zero input
is assigned exponent zero; every use in the proof supplies positivity. -/
noncomputable def windowExp (b L a : ℕ) : ℕ :=
  if ha : 0 < a then
    Nat.find (exists_pow_mul_gt (b := b + 2) (L := L) (a := a)
      (by omega : 1 < b + 2) ha)
  else 0

/-- Multiply by the least power of `b+2` which moves a positive number
strictly above `L`.  The shifted base keeps the definition total while the
applications `b=0` and `b=1` give bases two and three. -/
noncomputable def moveToWindow (b L a : ℕ) : ℕ :=
  (b + 2) ^ windowExp b L a * a

lemma lt_moveToWindow {b L a : ℕ} (ha : 0 < a) : L < moveToWindow b L a := by
  rw [moveToWindow, windowExp, dif_pos ha]
  exact Nat.find_spec (exists_pow_mul_gt (b := b + 2) (L := L) (a := a)
    (by omega : 1 < b + 2) ha)

lemma windowExp_min {b L a j : ℕ} (ha : 0 < a) (hj : j < windowExp b L a) :
    (b + 2) ^ j * a ≤ L := by
  rw [windowExp, dif_pos ha] at hj
  exact Nat.le_of_not_gt (Nat.find_min
    (exists_pow_mul_gt (b := b + 2) (L := L) (a := a)
      (by omega : 1 < b + 2) ha) hj)

/-- Minimality gives the upper side of the power window. -/
lemma moveToWindow_le {b L a : ℕ} (ha : 0 < a) (haL : a ≤ (b + 2) * L) :
    moveToWindow b L a ≤ (b + 2) * L := by
  by_cases hj : windowExp b L a = 0
  · simpa [moveToWindow, hj] using haL
  · obtain ⟨j, hjrfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hprev : (b + 2) ^ j * a ≤ L := by
      apply windowExp_min ha
      omega
    rw [moveToWindow, hjrfl, pow_succ']
    nlinarith

lemma dvd_moveToWindow (b L a : ℕ) : a ∣ moveToWindow b L a := by
  exact dvd_mul_left a ((b + 2) ^ windowExp b L a)

/-- Different elements of a property-P set cannot collide after they are
moved into the same multiplicative window. -/
lemma moveToWindow_injOn {A : Finset ℕ} (hP : IsForbiddenTripleFree A)
    (hpos : ∀ a ∈ A, 0 < a) (b L : ℕ) :
    Set.InjOn (moveToWindow b L) A := by
  intro x hx y hy hxy
  have hbase : 0 < b + 2 := by omega
  have key {u v : ℕ} (hu : u ∈ A) (hv : v ∈ A)
      (huv : moveToWindow b L u = moveToWindow b L v)
      (hle : windowExp b L u ≤ windowExp b L v) : u = v := by
    let ju := windowExp b L u
    let jv := windowExp b L v
    have hfactor : u = (b + 2) ^ (jv - ju) * v := by
      have hpow : (b + 2) ^ jv = (b + 2) ^ ju * (b + 2) ^ (jv - ju) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      have heq : (b + 2) ^ ju * u =
          (b + 2) ^ ju * ((b + 2) ^ (jv - ju) * v) := by
        change moveToWindow b L u = _ at huv
        rw [moveToWindow, show windowExp b L u = ju from rfl,
          moveToWindow, show windowExp b L v = jv from rfl, hpow, mul_assoc] at huv
        exact huv
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hbase) heq
    by_cases hjeq : ju = jv
    · simpa [hjeq] using hfactor
    · have hjlt : ju < jv := lt_of_le_of_ne hle hjeq
      have hpow2 : 2 ≤ (b + 2) ^ (jv - ju) := by
        have hdiff : jv - ju ≠ 0 := Nat.sub_ne_zero_of_lt hjlt
        exact (Nat.one_lt_pow hdiff (by omega : 1 < b + 2))
      have hvpos := hpos v hv
      have hvu : v < u := by nlinarith
      exfalso
      apply hP.not_dvd_of_lt hv hu hvu
      refine ⟨(b + 2) ^ (jv - ju), ?_⟩
      simpa [mul_comm] using hfactor
  rcases le_total (windowExp b L x) (windowExp b L y) with hle | hle
  · exact key hx hy hxy hle
  · exact (key hy hx hxy.symm hle).symm

/- The paper repeatedly uses windows whose endpoints are rational multiples
of `N`.  Keeping the denominator in the defining inequality avoids every
rounding convention: `scaledMove 0 N 3 a`, for instance, is the least power
of two times `a` whose triple is strictly larger than `N`. -/

lemma exists_scaled_pow_gt {b T q a : ℕ} (hq : 0 < q) (ha : 0 < a) :
    ∃ j : ℕ, T < q * ((b + 2) ^ j * a) := by
  refine ⟨T, ?_⟩
  have hb : 1 < b + 2 := by omega
  have hp : T < (b + 2) ^ T := Nat.lt_pow_self hb
  have hqa : 1 ≤ q * a := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  calc
    T < (b + 2) ^ T := hp
    _ = (b + 2) ^ T * 1 := by simp
    _ ≤ (b + 2) ^ T * (q * a) := Nat.mul_le_mul_left _ hqa
    _ = q * ((b + 2) ^ T * a) := by ac_rfl

/-- Least exponent making `q * ((b+2)^j * a)` exceed `T`. -/
noncomputable def scaledWindowExp (b T q a : ℕ) : ℕ :=
  if hq : 0 < q then
    if ha : 0 < a then Nat.find (exists_scaled_pow_gt (b := b) (T := T) hq ha) else 0
  else 0

/-- Move a positive natural number into a denominator-cleared multiplicative
window by the least power of `b+2`. -/
noncomputable def scaledMove (b T q a : ℕ) : ℕ :=
  (b + 2) ^ scaledWindowExp b T q a * a

lemma lt_scaledMove {b T q a : ℕ} (hq : 0 < q) (ha : 0 < a) :
    T < q * scaledMove b T q a := by
  rw [scaledMove, scaledWindowExp, dif_pos hq, dif_pos ha]
  exact Nat.find_spec (exists_scaled_pow_gt (b := b) (T := T) hq ha)

lemma scaledWindowExp_min {b T q a j : ℕ} (hq : 0 < q) (ha : 0 < a)
    (hj : j < scaledWindowExp b T q a) :
    q * ((b + 2) ^ j * a) ≤ T := by
  rw [scaledWindowExp, dif_pos hq, dif_pos ha] at hj
  exact Nat.le_of_not_gt (Nat.find_min
    (exists_scaled_pow_gt (b := b) (T := T) hq ha) hj)

/-- The upper endpoint supplied by minimality.  This is the exact integral
form used to put the low part of `A` into `(N/3,2N/3]`. -/
lemma scaledMove_le {b T q a : ℕ} (hq : 0 < q) (ha : 0 < a)
    (haT : q * a ≤ (b + 2) * T) :
    q * scaledMove b T q a ≤ (b + 2) * T := by
  by_cases hj : scaledWindowExp b T q a = 0
  · simpa [scaledMove, hj] using haT
  · obtain ⟨j, hjrfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hprev : q * ((b + 2) ^ j * a) ≤ T := by
      apply scaledWindowExp_min hq ha
      omega
    rw [scaledMove, hjrfl, pow_succ']
    nlinarith

lemma dvd_scaledMove (b T q a : ℕ) : a ∣ scaledMove b T q a := by
  exact dvd_mul_left a ((b + 2) ^ scaledWindowExp b T q a)

lemma scaledMove_injOn {A : Finset ℕ} (hP : IsForbiddenTripleFree A)
    (hpos : ∀ a ∈ A, 0 < a) (b T q : ℕ) :
    Set.InjOn (scaledMove b T q) A := by
  intro x hx y hy hxy
  have hbase : 0 < b + 2 := by omega
  have key {u v : ℕ} (hu : u ∈ A) (hv : v ∈ A)
      (huv : scaledMove b T q u = scaledMove b T q v)
      (hle : scaledWindowExp b T q u ≤ scaledWindowExp b T q v) : u = v := by
    let ju := scaledWindowExp b T q u
    let jv := scaledWindowExp b T q v
    have hfactor : u = (b + 2) ^ (jv - ju) * v := by
      have hpow : (b + 2) ^ jv = (b + 2) ^ ju * (b + 2) ^ (jv - ju) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      have heq : (b + 2) ^ ju * u =
          (b + 2) ^ ju * ((b + 2) ^ (jv - ju) * v) := by
        change scaledMove b T q u = _ at huv
        rw [scaledMove, show scaledWindowExp b T q u = ju from rfl,
          scaledMove, show scaledWindowExp b T q v = jv from rfl, hpow, mul_assoc] at huv
        exact huv
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hbase) heq
    by_cases hjeq : ju = jv
    · simpa [hjeq] using hfactor
    · have hjlt : ju < jv := lt_of_le_of_ne hle hjeq
      have hpow2 : 2 ≤ (b + 2) ^ (jv - ju) := by
        have hdiff : jv - ju ≠ 0 := Nat.sub_ne_zero_of_lt hjlt
        exact Nat.one_lt_pow hdiff (by omega : 1 < b + 2)
      have hvu : v < u := by
        have hvpos := hpos v hv
        nlinarith
      exfalso
      apply hP.not_dvd_of_lt hv hu hvu
      refine ⟨(b + 2) ^ (jv - ju), ?_⟩
      simpa [mul_comm] using hfactor
  rcases le_total (scaledWindowExp b T q x) (scaledWindowExp b T q y) with hle | hle
  · exact key hx hy hxy hle
  · exact (key hy hx hxy.symm hle).symm

/-! ### The central-third image -/

/-- The part of `A` at or below `2N/3`, with denominators cleared. -/
def lowTwoThirds (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter fun a ↦ 3 * a ≤ 2 * N

/-- The part of `A` strictly above `2N/3`. -/
def highThird (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter fun a ↦ 2 * N < 3 * a

/-- Bedert's `B₁`: move the elements at or below `2N/3` by the least
power of two whose triple is larger than `N`. -/
noncomputable def centralImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (lowTwoThirds A N).image (scaledMove 0 N 3)

@[simp] lemma mem_lowTwoThirds {A : Finset ℕ} {N a : ℕ} :
    a ∈ lowTwoThirds A N ↔ a ∈ A ∧ 3 * a ≤ 2 * N := by
  simp [lowTwoThirds]

@[simp] lemma mem_highThird {A : Finset ℕ} {N a : ℕ} :
    a ∈ highThird A N ↔ a ∈ A ∧ 2 * N < 3 * a := by
  simp [highThird]

lemma low_union_high (A : Finset ℕ) (N : ℕ) :
    lowTwoThirds A N ∪ highThird A N = A := by
  ext a
  simp only [mem_union, mem_lowTwoThirds, mem_highThird]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro ha
    exact Or.imp (And.intro ha) (And.intro ha) (le_or_gt (3 * a) (2 * N))

lemma low_disjoint_high (A : Finset ℕ) (N : ℕ) :
    Disjoint (lowTwoThirds A N) (highThird A N) := by
  rw [Finset.disjoint_left]
  intro a haL haH
  have hL := (mem_lowTwoThirds.mp haL).2
  have hH := (mem_highThird.mp haH).2
  omega

lemma card_low_add_card_high (A : Finset ℕ) (N : ℕ) :
    (lowTwoThirds A N).card + (highThird A N).card = A.card := by
  rw [← card_union_of_disjoint (low_disjoint_high A N), low_union_high]

lemma centralImage_card {A : Finset ℕ} {N : ℕ} (hP : IsForbiddenTripleFree A)
    (hsub : A ⊆ Icc 1 N) :
    (centralImage A N).card = (lowTwoThirds A N).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono (filter_subset _ _))
  intro a ha
  exact hP.pos_of_mem hsub ((filter_subset _ _) ha)

lemma card_centralImage_add_high {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (centralImage A N).card + (highThird A N).card = A.card := by
  rw [centralImage_card hP hsub, card_low_add_card_high]

lemma centralImage_mem_iff {A : Finset ℕ} {N b : ℕ} :
    b ∈ centralImage A N ↔
      ∃ a ∈ A, 3 * a ≤ 2 * N ∧ scaledMove 0 N 3 a = b := by
  simp only [centralImage, mem_image, mem_lowTwoThirds]
  constructor
  · rintro ⟨a, ⟨ha, haN⟩, rfl⟩
    exact ⟨a, ha, haN, rfl⟩
  · rintro ⟨a, ha, haN, rfl⟩
    exact ⟨a, ⟨ha, haN⟩, rfl⟩

lemma centralImage_subset_window {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    centralImage A N ⊆ ratSection (Icc 1 N) N 1 3 2 3 := by
  intro b hb
  obtain ⟨a, haA, haN, rfl⟩ := centralImage_mem_iff.mp hb
  have ha : 0 < a := hP.pos_of_mem hsub haA
  have hlo : N < 3 * scaledMove 0 N 3 a := lt_scaledMove (by omega) ha
  have hhi : 3 * scaledMove 0 N 3 a ≤ 2 * N := by
    simpa using scaledMove_le (b := 0) (T := N) (q := 3) (a := a)
      (by omega) ha haN
  apply mem_ratSection.mpr
  refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_, hhi⟩
  · have hpos : 0 < scaledMove 0 N 3 a := by
      simp only [scaledMove]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) ha
    omega
  · omega
  · simpa using hlo

/-- Every central-image element is a multiple of its originating low
property-P element. -/
lemma centralImage_has_low_divisor {A : Finset ℕ} {N b : ℕ}
    (hb : b ∈ centralImage A N) :
    ∃ a ∈ A, 3 * a ≤ 2 * N ∧ a ∣ b := by
  obtain ⟨a, ha, haN, rfl⟩ := centralImage_mem_iff.mp hb
  exact ⟨a, ha, haN, dvd_scaledMove 0 N 3 a⟩

/-! ### Arithmetic progressions and common residue classes -/

/-- A finite arithmetic progression in `ℕ`, parametrized by its number of
terms. -/
def natAP (a d len : ℕ) : Finset ℕ :=
  (range len).image fun j ↦ a + d * j

@[simp] lemma mem_natAP {a d len x : ℕ} :
    x ∈ natAP a d len ↔ ∃ j < len, a + d * j = x := by
  simp [natAP]

lemma card_natAP {a d len : ℕ} (hd : 0 < d) : (natAP a d len).card = len := by
  have hinj : Set.InjOn (fun j : ℕ ↦ a + d * j) (range len) := by
    intro i hi j hj hij
    exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel hij)
  rw [natAP, card_image_iff.mpr hinj]
  simp

lemma natAP_nonempty {a d len : ℕ} (hlen : 0 < len) : (natAP a d len).Nonempty := by
  refine ⟨a, ?_⟩
  exact mem_natAP.mpr ⟨0, hlen, by simp⟩

/-- Every interval of at least `x` consecutive naturals contains a multiple
of the positive integer `x`. -/
lemma exists_dvd_mem_natAP_one {a len x : ℕ} (hx : 0 < x) (hxl : x ≤ len) :
    ∃ y ∈ natAP a 1 len, x ∣ y := by
  by_cases hxa : x ∣ a
  · exact ⟨a, mem_natAP.mpr ⟨0, by omega, by simp⟩, hxa⟩
  · let r := a % x
    let j := x - r
    have hrlt : r < x := by
      exact Nat.mod_lt _ hx
    have hrpos : 0 < r := by
      have hrne : r ≠ 0 := by
        intro hr
        apply hxa
        exact Nat.dvd_of_mod_eq_zero hr
      omega
    have hjlt : j < len := by
      dsimp [j]
      omega
    refine ⟨a + j, mem_natAP.mpr ⟨j, hjlt, by simp⟩, ?_⟩
    refine ⟨a / x + 1, ?_⟩
    have hdiv := Nat.div_add_mod a x
    change a + j = x * (a / x + 1)
    dsimp [j, r]
    rw [Nat.mul_add, Nat.mul_one]
    omega

lemma natAP_subset_Icc {a d len L U : ℕ} (hL : L ≤ a)
    (hU : a + d * (len - 1) ≤ U) : natAP a d len ⊆ Icc L U := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hx
  apply mem_Icc.mpr
  constructor
  · omega
  · by_cases hlen : len = 0
    · omega
    · have hj' : j ≤ len - 1 := by omega
      exact (Nat.add_le_add_left (Nat.mul_le_mul_left d hj') a).trans hU

/-- All members of `U` occupy one residue class modulo `d`.  The `ZMod`
form is chosen because translating a set or cancelling a fixed summand is
then literal additive cancellation. -/
def InOneResidue (U : Finset ℕ) (d : ℕ) : Prop :=
  ∃ r : ZMod d, ∀ x ∈ U, (x : ZMod d) = r

lemma inOneResidue_mono {U V : Finset ℕ} {d : ℕ}
    (hU : InOneResidue U d) (hVU : V ⊆ U) : InOneResidue V d := by
  obtain ⟨r, hr⟩ := hU
  exact ⟨r, fun x hx ↦ hr x (hVU hx)⟩

lemma inOneResidue_add_left {S T : Finset ℕ} {d : ℕ} (hT : T.Nonempty)
    (hST : InOneResidue (S + T) d) : InOneResidue S d := by
  obtain ⟨t, ht⟩ := hT
  obtain ⟨r, hr⟩ := hST
  refine ⟨r - (t : ZMod d), ?_⟩
  intro x hx
  have hxt := hr (x + t) (Finset.add_mem_add hx ht)
  push_cast at hxt
  rw [← hxt]
  abel

lemma inOneResidue_add_right {S T : Finset ℕ} {d : ℕ} (hS : S.Nonempty)
    (hST : InOneResidue (S + T) d) : InOneResidue T d := by
  rw [add_comm] at hST
  exact inOneResidue_add_left hS hST

lemma natAP_inOneResidue (a d len : ℕ) : InOneResidue (natAP a d len) d := by
  refine ⟨(a : ZMod d), ?_⟩
  intro x hx
  obtain ⟨j, -, rfl⟩ := mem_natAP.mp hx
  simp

/-- The structural alternative used from Bardaji--Grynkiewicz: a long
progression in the sumset, with its step also a common modulus of the whole
sumset. -/
def HasLongSumAP (S T : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ natAP a d (S.card + T.card - 1) ⊆ S + T ∧
    InOneResidue (S + T) d

lemma hasLongSumAP_comm {S T : Finset ℕ} :
    HasLongSumAP S T ↔ HasLongSumAP T S := by
  simp only [HasLongSumAP, add_comm (a := S.card), add_comm (a := S)]

/-- The exact cardinal alternative in the form used throughout Bedert's
proof. -/
def BGAlternative (S T : Finset ℕ) : Prop :=
  S.card + T.card + min S.card T.card ≤ (S + T).card + 3 ∨ HasLongSumAP S T

/-- The strict Bardaji--Grynkiewicz alternative, transferred from the
normalized additive theorem proved in `Erdos13Additive`. -/
lemma bgAlternative_of_nonempty {S T : Finset ℕ}
    (hS : S.Nonempty) (hT : T.Nonempty) : BGAlternative S T := by
  rcases Erdos13Additive.growth_or_long_AP hS hT with hgrowth | hstruct
  · exact Or.inl hgrowth
  · right
    obtain ⟨a, d, hd, hQ, hres⟩ := hstruct
    refine ⟨a, d, hd, ?_, ?_⟩
    · simpa only [natAP, Erdos13Additive.natAP] using hQ
    · simpa only [InOneResidue, Erdos13Additive.InOneResidue] using hres

lemma bgAlternative_self (S : Finset ℕ) : BGAlternative S S := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · left
    simp
  · exact bgAlternative_of_nonempty hS hS

/-! ### The minimum-element estimate -/

/-- Members of `A` in the first full interval above `s`. -/
def firstBlock (A : Finset ℕ) (s : ℕ) : Finset ℕ :=
  A.filter fun x ↦ s < x ∧ x ≤ 2 * s

@[simp] lemma mem_firstBlock {A : Finset ℕ} {s x : ℕ} :
    x ∈ firstBlock A s ↔ x ∈ A ∧ s < x ∧ x ≤ 2 * s := by
  simp [firstBlock]

/-- Reduction modulo `s` is injective on `(s,2s]`. -/
lemma zmod_cast_injOn_firstBlock {A : Finset ℕ} {s : ℕ} (_hs : 0 < s) :
    Set.InjOn (fun x : ℕ ↦ (x : ZMod s)) (firstBlock A s) := by
  intro x hx y hy hxy
  have hxI := (mem_firstBlock.mp hx).2
  have hyI := (mem_firstBlock.mp hy).2
  have hmod : x ≡ y [MOD s] := by
    exact (ZMod.natCast_eq_natCast_iff x y s).mp hxy
  rcases le_total x y with hle | hle
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod
    have hst : s * t < s := by omega
    have ht0 : t = 0 := by
      by_contra ht0
      have : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
      nlinarith
    simpa [ht0] using ht.symm
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
    have hst : s * t < s := by omega
    have ht0 : t = 0 := by
      by_contra ht0
      have : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
      nlinarith
    simpa [ht0] using ht

/-- If `s` is the least member of a property-P set, at most half of the
residue classes can occur in `(s,2s]`: a class and its negative cannot both
occur. -/
lemma two_mul_card_firstBlock_le {A : Finset ℕ} {s : ℕ}
    (hP : IsForbiddenTripleFree A) (hsA : s ∈ A) (hs : 0 < s) :
    2 * (firstBlock A s).card ≤ s := by
  let _ : NeZero s := ⟨Nat.ne_of_gt hs⟩
  let R : Finset (ZMod s) := (firstBlock A s).image fun x : ℕ ↦ (x : ZMod s)
  let negR : Finset (ZMod s) := R.image fun r ↦ -r
  have hcardR : R.card = (firstBlock A s).card := by
    apply card_image_iff.mpr
    exact zmod_cast_injOn_firstBlock hs
  have hcardNeg : negR.card = R.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact neg_injective hxy
  have hdisj : Disjoint R negR := by
    rw [Finset.disjoint_left]
    intro r hrR hrNeg
    simp only [negR, Finset.mem_image] at hrNeg
    obtain ⟨q, hqR, hqr⟩ := hrNeg
    simp only [R, Finset.mem_image] at hrR hqR
    obtain ⟨x, hx, hxr⟩ := hrR
    obtain ⟨y, hy, hyq⟩ := hqR
    have hcast : ((x + y : ℕ) : ZMod s) = 0 := by
      rw [Nat.cast_add, hxr, hyq, ← hqr]
      simp
    have hdvd : s ∣ x + y := by
      exact (ZMod.natCast_eq_zero_iff (x + y) s).mp hcast
    have hx' := mem_firstBlock.mp hx
    have hy' := mem_firstBlock.mp hy
    exact hP.not_dvd_add hsA hx'.1 hy'.1 hx'.2.1 hy'.2.1 hdvd
  have hunion : (R ∪ negR).card ≤ s := by
    calc
      (R ∪ negR).card ≤ (Finset.univ : Finset (ZMod s)).card := by
        exact card_le_card (subset_univ _)
      _ = s := by simp [ZMod.card]
  rw [card_union_of_disjoint hdisj, hcardNeg, hcardR] at hunion
  omega

/-- A property-P set with least element `s` is controlled by the first
block above `s` and the completely trivial tail above `2s`. -/
lemma card_le_of_least {A : Finset ℕ} {N s : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsA : s ∈ A) (hleast : ∀ x ∈ A, s ≤ x) :
    2 * A.card ≤ 2 + s + 2 * (N - 2 * s) := by
  let T := A.filter fun x ↦ 2 * s < x
  have hdecomp : A = {s} ∪ firstBlock A s ∪ T := by
    ext x
    simp only [mem_union, mem_singleton, mem_firstBlock, T, mem_filter]
    constructor
    · intro hx
      rcases lt_trichotomy x s with hxs | hxs | hxs
      · exact False.elim (by have := hleast x hx; omega)
      · exact Or.inl (Or.inl hxs)
      · by_cases hx2 : x ≤ 2 * s
        · exact Or.inl (Or.inr ⟨hx, hxs, hx2⟩)
        · exact Or.inr ⟨hx, by omega⟩
    · rintro ((rfl | h) | h)
      · exact hsA
      · exact h.1
      · exact h.1
  have hcard : A.card ≤ 1 + (firstBlock A s).card + T.card := by
    have h₁ := card_union_le ({s} : Finset ℕ) (firstBlock A s)
    have h₂ := card_union_le ({s} ∪ firstBlock A s) T
    simp only [card_singleton] at h₁
    calc
      A.card = ({s} ∪ firstBlock A s ∪ T).card := congrArg card hdecomp
      _ ≤ ({s} ∪ firstBlock A s).card + T.card := h₂
      _ ≤ 1 + (firstBlock A s).card + T.card := Nat.add_le_add_right h₁ _
  have hspos : 0 < s := by
    exact (mem_Icc.mp (hsub hsA)).1
  have hfirst := two_mul_card_firstBlock_le hP hsA hspos
  have hTsub : T ⊆ Icc (2 * s + 1) N := by
    intro x hx
    simp only [T, mem_filter] at hx
    exact mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hsub hx.1)).2⟩
  have hTcard := card_Icc_le hTsub
  omega

/-- Once the least element is just past `4N/9`, the elementary opposite
residue pairing already gives the required one-third estimate. -/
lemma three_mul_card_le_of_large_least {A : Finset ℕ} {N s : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsA : s ∈ A) (hleast : ∀ x ∈ A, s ≤ x)
    (hslarge : 4 * N + 9 < 9 * s) :
    3 * A.card ≤ N + 3 := by
  by_cases htop : 2 * N < 3 * s
  · have hAI : A ⊆ Icc s N := by
      intro x hx
      exact mem_Icc.mpr ⟨hleast x hx, (mem_Icc.mp (hsub hx)).2⟩
    have hc := card_Icc_le hAI
    omega
  · have hbasic := card_le_of_least hP hsub hsA hleast
    by_cases hmid : 2 * s ≤ N
    · omega
    · omega

/-! ### The large-top-third branch -/

/-- A sufficiently large subset of the top third cannot occupy one residue
class modulo an integer greater than one. -/
lemma commonDifference_eq_one_of_large_high {H : Finset ℕ} {N d : ℕ}
    (hH : H ⊆ Icc (2 * N / 3 + 1) N)
    (hlarge : 2 * N + 12 ≤ 9 * H.card) (hd : 0 < d)
    (hres : InOneResidue H d) : d = 1 := by
  obtain ⟨r, hr⟩ := hres
  have hcap := mul_card_fixed_zmod_le r hH hr
  have hHne : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    simp only [hzero, card_empty, mul_zero] at hlarge
    omega
  have hcardpos : 0 < H.card := card_pos.mpr hHne
  obtain ⟨x, hx⟩ := hHne
  have hL : 2 * N / 3 + 1 ≤ N := (mem_Icc.mp (hH hx)).1.trans (mem_Icc.mp (hH hx)).2
  by_contra hd1
  have hd2 : 2 ≤ d := by omega
  obtain ⟨k, hk⟩ : ∃ k, H.card = k + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
  rw [hk] at hcap hlarge
  have hspan : d * k ≤ N - (2 * N / 3 + 1) := by
    have hrhs : (N + d) - (2 * N / 3 + 1) =
        (N - (2 * N / 3 + 1)) + d := by omega
    rw [hrhs, Nat.mul_add, Nat.mul_one] at hcap
    omega
  have htwo : 2 * k ≤ N - (2 * N / 3 + 1) := by
    exact (Nat.mul_le_mul_right k hd2).trans hspan
  omega

/-- A long unit-step progression in the high-high sumset excludes every
central-or-lower member of `A` whose value is no larger than the progression
length. -/
lemma not_mem_of_le_long_high_sumAP {A H : Finset ℕ} {N a len q : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hH : ∀ x ∈ H, x ∈ A ∧ 2 * N < 3 * x)
    (hQ : natAP q 1 len ⊆ H + H)
    (ha : a ∈ A) (hapos : 0 < a) (halen : a ≤ len) (haN : 3 * a ≤ 2 * N) : False := by
  obtain ⟨y, hyQ, hay⟩ := exists_dvd_mem_natAP_one hapos halen
  have hy := hQ hyQ
  simp only [Finset.mem_add] at hy
  obtain ⟨b, hb, c, hc, rfl⟩ := hy
  have hb' := hH b hb
  have hc' := hH c hc
  apply hP.not_dvd_add ha hb'.1 hc'.1
  · omega
  · omega
  · exact hay

lemma highThird_subset_interval {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Icc 1 N) :
    highThird A N ⊆ Icc (2 * N / 3 + 1) N := by
  intro x hx
  have hx' := mem_highThird.mp hx
  exact mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hsub hx'.1)).2⟩

lemma three_mul_card_highThird_le {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Icc 1 N) :
    3 * (highThird A N).card ≤ N + 2 := by
  have hc := card_Icc_le (highThird_subset_interval hsub)
  omega

lemma three_mul_card_high_sum_le {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Icc 1 N) :
    3 * (highThird A N + highThird A N).card ≤ 2 * N + 2 := by
  have hsumsub : highThird A N + highThird A N ⊆
      Icc (4 * N / 3 + 1) (2 * N) := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_highThird.mp hx
    have hy' := mem_highThird.mp hy
    have hxN := (mem_Icc.mp (hsub hx'.1)).2
    have hyN := (mem_Icc.mp (hsub hy'.1)).2
    apply mem_Icc.mpr
    constructor <;> omega
  have hc := card_Icc_le hsumsub
  omega

/-- Bedert's first case, isolated from the additive-combinatorial theorem.
The only structural input is `BGAlternative H H`. -/
lemma caseOne_of_BG {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hlarge : 2 * N + 12 ≤ 9 * (highThird A N).card)
    (hBG : BGAlternative (highThird A N) (highThird A N)) :
    3 * A.card ≤ N + 3 := by
  let H := highThird A N
  change 2 * N + 12 ≤ 9 * H.card at hlarge
  have hHI : H ⊆ Icc (2 * N / 3 + 1) N := highThird_subset_interval hsub
  have hHne : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    simp only [H, hzero, card_empty, mul_zero] at hlarge
    omega
  have hHcardpos : 0 < H.card := card_pos.mpr hHne
  have hHmem : ∀ x ∈ H, x ∈ A ∧ 2 * N < 3 * x := by
    intro x hx
    exact mem_highThird.mp hx
  rcases hBG with hgrowth | hstruct
  · have hsum := three_mul_card_high_sum_le hsub
    change H.card + H.card + min H.card H.card ≤ (H + H).card + 3 at hgrowth
    simp only [min_self] at hgrowth
    change 3 * (H + H).card ≤ 2 * N + 2 at hsum
    omega
  · obtain ⟨q, d, hd, hQ, hresSum⟩ := hstruct
    have hresH : InOneResidue H d := inOneResidue_add_left hHne hresSum
    have hd1 : d = 1 := commonDifference_eq_one_of_large_high hHI hlarge hd hresH
    subst d
    have hAne : A.Nonempty := by
      obtain ⟨x, hx⟩ := hHne
      exact ⟨x, (hHmem x hx).1⟩
    let s := A.min' hAne
    have hsA : s ∈ A := A.min'_mem hAne
    have hleast : ∀ x ∈ A, s ≤ x := by
      intro x hx
      exact A.min'_le x hx
    have hspos : 0 < s := (mem_Icc.mp (hsub hsA)).1
    have htopcard := three_mul_card_highThird_le hsub
    have hN : 6 ≤ N := by
      change 3 * H.card ≤ N + 2 at htopcard
      omega
    have hslarge : 4 * N + 9 < 9 * s := by
      by_contra hnot
      have hsupper : 9 * s ≤ 4 * N + 9 := by omega
      have hscentral : 3 * s ≤ 2 * N := by
        by_contra hnotcentral
        omega
      have hlen : s ≤ H.card + H.card - 1 := by
        have hlenlarge : 4 * N + 9 < 9 * (H.card + H.card - 1) := by
          omega
        omega
      exact not_mem_of_le_long_high_sumAP hP hHmem hQ hsA hspos hlen hscentral
    exact three_mul_card_le_of_large_least hP hsub hsA hleast hslarge

lemma caseOne {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hlarge : 2 * N + 12 ≤ 9 * (highThird A N).card) :
    3 * A.card ≤ N + 3 :=
  caseOne_of_BG hP hsub hlarge (bgAlternative_self _)

/-! ### Uniform packing estimate for the medium case -/

/-- This is inequalities (6) and (7) of Bedert at once.  A piece of the
central image whose `k`-fold dilate lies in one residue class of the
high-high sum interval satisfies the displayed denominator-cleared bound. -/
lemma medium_packing_bound {A B₀ : Finset ℕ} {N k : ℕ} {r : ZMod 12}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hk : 0 < k) (hB₀ : B₀ ⊆ centralImage A N)
    (hmulI : ∀ b ∈ B₀, k * b ∈ Icc (4 * N / 3 + 1) (2 * N))
    (hmulR : ∀ b ∈ B₀, ((k * b : ℕ) : ZMod 12) = r) :
    3 * (highThird A N).card + 18 * B₀.card ≤ N + 36 := by
  let H := highThird A N
  let L := 4 * N / 3 + 1
  let S := zmodFiber (H + H) r
  let U := zmodFiber (Icc L (2 * N)) r
  change 3 * H.card + 18 * B₀.card ≤ N + 36
  have hHI : H ⊆ Icc (2 * N / 3 + 1) N := highThird_subset_interval hsub
  have hHinterval : H ⊆ Icc (2 * N / 3 + 1) (2 * N / 3 + (N - 2 * N / 3)) := by
    simpa [H, Nat.add_sub_of_le (by omega : 2 * N / 3 ≤ N)] using hHI
  have hdenseCond : (N - 2 * N / 3) + 12 ≤ 2 * H.card := by
    change N + 144 ≤ 6 * H.card at hmedium
    omega
  have hdense := dense_residue_Icc (q := 12) (by omega) hHinterval hdenseCond r
  have hB : ∀ b ∈ B₀, ∃ a ∈ A, a ≤ 2 * N / 3 ∧ a ∣ k * b := by
    intro b hb
    obtain ⟨a, haA, haN, hab⟩ := centralImage_has_low_divisor (hB₀ hb)
    exact ⟨a, haA, by omega, hab.mul_left k⟩
  have hHigh : ∀ x ∈ H, x ∈ A ∧ 2 * N / 3 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hSsum : S ⊆ H + H := by
    exact filter_subset _ _
  have hBU : B₀.image (fun b ↦ k * b) ⊆ U := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    apply mem_zmodFiber.mpr
    exact ⟨hmulI b hb, hmulR b hb⟩
  have hsumI : H + H ⊆ Icc L (2 * N) := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_highThird.mp hx
    have hy' := mem_highThird.mp hy
    have hxN := (mem_Icc.mp (hsub hx'.1)).2
    have hyN := (mem_Icc.mp (hsub hy'.1)).2
    apply mem_Icc.mpr
    constructor <;> omega
  have hSU : S ⊆ U := by
    intro z hz
    have hz' := mem_zmodFiber.mp hz
    exact mem_zmodFiber.mpr ⟨hsumI hz'.1, hz'.2⟩
  have hpack := packing hk hP hB hHigh hSsum hBU hSU
  have hUI : U ⊆ Icc L (2 * N) := (filter_subset _ _)
  have hUres : ∀ x ∈ U, (x : ZMod 12) = r := by
    intro x hx
    exact (mem_zmodFiber.mp hx).2
  have hcap := mul_card_fixed_zmod_le r hUI hUres
  change 2 * H.card ≤ 12 * (S.card + 1) at hdense
  change B₀.card + S.card ≤ U.card at hpack
  change 12 * U.card ≤ (2 * N + 12) - L at hcap
  have hL : 4 * N ≤ 3 * L := by
    dsimp [L]
    omega
  omega

/-- The left half of the central image, split modulo three. -/
noncomputable def centralLeft (A : Finset ℕ) (N i : ℕ) : Finset ℕ :=
  (centralImage A N).filter fun b ↦ 2 * b ≤ N ∧ b % 3 = i % 3

/-- The right half of the central image, split modulo four. -/
noncomputable def centralRight (A : Finset ℕ) (N i : ℕ) : Finset ℕ :=
  (centralImage A N).filter fun b ↦ N < 2 * b ∧ b % 4 = i % 4

@[simp] lemma mem_centralLeft {A : Finset ℕ} {N i b : ℕ} :
    b ∈ centralLeft A N i ↔
      b ∈ centralImage A N ∧ 2 * b ≤ N ∧ b % 3 = i % 3 := by
  simp [centralLeft]

@[simp] lemma mem_centralRight {A : Finset ℕ} {N i b : ℕ} :
    b ∈ centralRight A N i ↔
      b ∈ centralImage A N ∧ N < 2 * b ∧ b % 4 = i % 4 := by
  simp [centralRight]

lemma medium_left_bound {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card) :
    3 * (highThird A N).card + 18 * (centralLeft A N i).card ≤ N + 36 := by
  apply medium_packing_bound hP hsub hmedium (k := 4) (r := (4 * i : ZMod 12))
  · omega
  · exact filter_subset _ _
  · intro b hb
    have hb' := mem_centralLeft.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro b hb
    have hbmod := (mem_centralLeft.mp hb).2.2
    have hm : 4 * b ≡ 4 * i [MOD 12] := by
      have hbi : b ≡ i [MOD 3] := hbmod
      simpa using hbi.mul_left' 4
    simpa [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff (4 * b) (4 * i) 12).mpr hm

lemma medium_right_bound {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card) :
    3 * (highThird A N).card + 18 * (centralRight A N i).card ≤ N + 36 := by
  apply medium_packing_bound hP hsub hmedium (k := 3) (r := (3 * i : ZMod 12))
  · omega
  · exact filter_subset _ _
  · intro b hb
    have hb' := mem_centralRight.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro b hb
    have hbmod := (mem_centralRight.mp hb).2.2
    have hm : 3 * b ≡ 3 * i [MOD 12] := by
      have hbi : b ≡ i [MOD 4] := hbmod
      simpa using hbi.mul_left' 3
    simpa [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff (3 * b) (3 * i) 12).mpr hm

/-- The seven medium-case slices partition the central image. -/
lemma card_centralImage_eq_slices (A : Finset ℕ) (N : ℕ) :
    (centralImage A N).card =
      (centralLeft A N 0).card + (centralLeft A N 1).card +
      (centralLeft A N 2).card + (centralRight A N 0).card +
      (centralRight A N 1).card + (centralRight A N 2).card +
      (centralRight A N 3).card := by
  let B := centralImage A N
  let BL := B.filter fun b ↦ 2 * b ≤ N
  let BR := B.filter fun b ↦ N < 2 * b
  have hdisj : Disjoint BL BR := by
    rw [Finset.disjoint_left]
    intro b hbL hbR
    simp only [BL, BR, mem_filter] at hbL hbR
    omega
  have hunion : BL ∪ BR = B := by
    ext b
    simp only [BL, BR, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hb
      exact Or.imp (And.intro hb) (And.intro hb) (le_or_gt (2 * b) N)
  have hcard : B.card = BL.card + BR.card := by
    rw [← card_union_of_disjoint hdisj, hunion]
  have hmapL : (BL : Set ℕ).MapsTo (fun b ↦ b % 3) (range 3) := by
    intro b hb
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have hmapR : (BR : Set ℕ).MapsTo (fun b ↦ b % 4) (range 4) := by
    intro b hb
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have hfiberL := Finset.card_eq_sum_card_fiberwise hmapL
  have hfiberR := Finset.card_eq_sum_card_fiberwise hmapR
  have hsliceL (i : ℕ) (hi : i < 3) :
      BL.filter (fun b ↦ b % 3 = i) = centralLeft A N i := by
    ext b
    simp only [BL, B, mem_filter, mem_centralLeft]
    have himod : i % 3 = i := Nat.mod_eq_of_lt hi
    simp only [himod]
    tauto
  have hsliceR (i : ℕ) (hi : i < 4) :
      BR.filter (fun b ↦ b % 4 = i) = centralRight A N i := by
    ext b
    simp only [BR, B, mem_filter, mem_centralRight]
    have himod : i % 4 = i := Nat.mod_eq_of_lt hi
    simp only [himod]
    tauto
  simp only [sum_range_succ, sum_range_zero] at hfiberL hfiberR
  rw [hsliceL 0 (by omega), hsliceL 1 (by omega), hsliceL 2 (by omega)] at hfiberL
  rw [hsliceR 0 (by omega), hsliceR 1 (by omega), hsliceR 2 (by omega),
    hsliceR 3 (by omega)] at hfiberR
  change (centralImage A N).card = BL.card + BR.card at hcard
  omega

lemma medium_done_of_large_left_slice {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hslice : (centralImage A N).card + 12 ≤ 6 * (centralLeft A N i).card) :
    3 * A.card ≤ N := by
  have hp := medium_left_bound (i := i) hP hsub hmedium
  have hcard := card_centralImage_add_high hP hsub
  omega

lemma medium_done_of_large_right_slice {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hslice : (centralImage A N).card + 12 ≤ 6 * (centralRight A N i).card) :
    3 * A.card ≤ N := by
  have hp := medium_right_bound (i := i) hP hsub hmedium
  have hcard := card_centralImage_add_high hP hsub
  omega

/-- One parity fiber of a finset. -/
def parityPart (H : Finset ℕ) (r : ℕ) : Finset ℕ :=
  H.filter fun x ↦ x % 2 = r % 2

@[simp] lemma mem_parityPart {H : Finset ℕ} {r x : ℕ} :
    x ∈ parityPart H r ↔ x ∈ H ∧ x % 2 = r % 2 := by
  simp [parityPart]

lemma card_parity_parts (H : Finset ℕ) :
    (parityPart H 0).card + (parityPart H 1).card = H.card := by
  have hmap : (H : Set ℕ).MapsTo (fun x ↦ x % 2) (range 2) := by
    intro x hx
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  simp only [sum_range_succ, sum_range_zero] at hfiber
  have hzero : H.filter (fun x ↦ x % 2 = 0) = parityPart H 0 := by
    ext x
    simp [parityPart]
  have hone : H.filter (fun x ↦ x % 2 = 1) = parityPart H 1 := by
    ext x
    simp [parityPart]
  rw [hzero, hone] at hfiber
  omega

lemma exists_large_parityPart (H : Finset ℕ) :
    ∃ r < 2, H.card ≤ 2 * (parityPart H r).card := by
  have hc := card_parity_parts H
  rcases le_total (parityPart H 0).card (parityPart H 1).card with h | h
  · exact ⟨1, by omega, by omega⟩
  · exact ⟨0, by omega, by omega⟩

lemma parityPart_sum_even {H : Finset ℕ} {r z : ℕ}
    (hz : z ∈ parityPart H r + parityPart H r) : 2 ∣ z := by
  simp only [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  have hxmod := (mem_parityPart.mp hx).2
  have hymod := (mem_parityPart.mp hy).2
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hxmod, hymod]
  have hr : r % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases r % 2 <;> decide

/-- In the medium case, the structural progression in the self-sum of the
larger parity class necessarily has common difference two. -/
lemma medium_structural_step_eq_two {O : Finset ℕ} {N q d : ℕ}
    (hOI : O ⊆ Icc (2 * N / 3 + 1) N)
    (hOlarge : N + 144 ≤ 12 * O.card)
    (hd : 0 < d) (hres : InOneResidue (O + O) d)
    (hQ : natAP q d (O.card + O.card - 1) ⊆ O + O)
    (heven : ∀ z ∈ O + O, 2 ∣ z) : d = 2 := by
  have hOne : InOneResidue O d := by
    have hOneO : O.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hz
      simp only [hz, card_empty, mul_zero] at hOlarge
      omega
    exact inOneResidue_add_left hOneO hres
  obtain ⟨r, hr⟩ := hOne
  have hcap := mul_card_fixed_zmod_le r hOI hr
  have hOpos : 0 < O.card := by omega
  have hL : 2 * N / 3 + 1 ≤ N := by
    obtain ⟨x, hx⟩ := card_pos.mp hOpos
    exact (mem_Icc.mp (hOI hx)).1.trans (mem_Icc.mp (hOI hx)).2
  have hdle : d ≤ 3 := by
    by_contra hnot
    have hd4 : 4 ≤ d := by omega
    obtain ⟨k, hk⟩ : ∃ k, O.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hOpos)
    rw [hk] at hcap hOlarge
    have hrhs : (N + d) - (2 * N / 3 + 1) =
        (N - (2 * N / 3 + 1)) + d := by omega
    rw [hrhs, Nat.mul_add, Nat.mul_one] at hcap
    have hspan : d * k ≤ N - (2 * N / 3 + 1) := by omega
    have hfour : 4 * k ≤ N - (2 * N / 3 + 1) :=
      (Nat.mul_le_mul_right k hd4).trans hspan
    omega
  have hlen : 1 < O.card + O.card - 1 := by omega
  have hq : q ∈ O + O := hQ (mem_natAP.mpr ⟨0, by omega, by simp⟩)
  have hqd : q + d ∈ O + O := hQ (mem_natAP.mpr ⟨1, hlen, by simp⟩)
  have hed : 2 ∣ d := by
    have heq := heven q hq
    have heqd := heven (q + d) hqd
    rw [Nat.dvd_iff_mod_eq_zero] at heq heqd ⊢
    simpa [Nat.add_mod, heq] using heqd
  omega

/-! ### The packing alternative in the medium case -/

/-- Dilation of a natural-number finset. -/
def dilate (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x ↦ k * x

@[simp] lemma mem_dilate {k x : ℕ} {S : Finset ℕ} :
    x ∈ dilate k S ↔ ∃ y ∈ S, k * y = x := by
  simp [dilate]

lemma card_dilate {k : ℕ} (hk : 0 < k) (S : Finset ℕ) :
    (dilate k S).card = S.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  exact Nat.eq_of_mul_eq_mul_left hk hxy

lemma disjoint_of_zmod_ne {X Y : Finset ℕ} {q : ℕ} {r s : ZMod q}
    (hrs : r ≠ s) (hX : ∀ x ∈ X, (x : ZMod q) = r)
    (hY : ∀ y ∈ Y, (y : ZMod q) = s) : Disjoint X Y := by
  rw [Finset.disjoint_left]
  intro z hzX hzY
  exact hrs ((hX z hzX).symm.trans (hY z hzY))

/-- The four dilated slices used in (14) of Bedert's proof. -/
noncomputable def mediumPack (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  dilate 4 (centralLeft A N 0) ∪
  dilate 4 (centralLeft A N 1) ∪
  dilate 4 (centralLeft A N 2) ∪
  dilate 3 (centralRight A N 2)

lemma mediumPack_card (A : Finset ℕ) (N : ℕ) :
    (mediumPack A N).card =
      (centralLeft A N 0).card + (centralLeft A N 1).card +
      (centralLeft A N 2).card + (centralRight A N 2).card := by
  let D0 := dilate 4 (centralLeft A N 0)
  let D1 := dilate 4 (centralLeft A N 1)
  let D2 := dilate 4 (centralLeft A N 2)
  let D3 := dilate 3 (centralRight A N 2)
  have hresL (i : ℕ) (z : ℕ) (hz : z ∈ dilate 4 (centralLeft A N i)) :
      (z : ZMod 12) = (4 * i : ℕ) := by
    obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hbmod := (mem_centralLeft.mp hb).2.2
    have hm : 4 * b ≡ 4 * i [MOD 12] := by
      have hbi : b ≡ i [MOD 3] := hbmod
      simpa using hbi.mul_left' 4
    exact (ZMod.natCast_eq_natCast_iff (4 * b) (4 * i) 12).mpr hm
  have hresR (z : ℕ) (hz : z ∈ dilate 3 (centralRight A N 2)) :
      (z : ZMod 12) = (6 : ℕ) := by
    obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hbmod := (mem_centralRight.mp hb).2.2
    have hm : 3 * b ≡ 3 * 2 [MOD 12] := by
      have hbi : b ≡ 2 [MOD 4] := hbmod
      simpa using hbi.mul_left' 3
    exact (ZMod.natCast_eq_natCast_iff (3 * b) 6 12).mpr (by simpa using hm)
  have h01 : Disjoint D0 D1 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (0 : ZMod 12)) (s := (4 : ZMod 12))
    · decide
    · intro z hz; simpa [D0] using hresL 0 z hz
    · intro z hz; simpa [D1] using hresL 1 z hz
  have h02 : Disjoint D0 D2 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (0 : ZMod 12)) (s := (8 : ZMod 12))
    · decide
    · intro z hz; simpa [D0] using hresL 0 z hz
    · intro z hz; simpa [D2] using hresL 2 z hz
  have h12 : Disjoint D1 D2 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (4 : ZMod 12)) (s := (8 : ZMod 12))
    · decide
    · intro z hz; simpa [D1] using hresL 1 z hz
    · intro z hz; simpa [D2] using hresL 2 z hz
  have h03 : Disjoint D0 D3 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (0 : ZMod 12)) (s := (6 : ZMod 12))
    · decide
    · intro z hz; simpa [D0] using hresL 0 z hz
    · intro z hz; simpa [D3] using hresR z hz
  have h13 : Disjoint D1 D3 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (4 : ZMod 12)) (s := (6 : ZMod 12))
    · decide
    · intro z hz; simpa [D1] using hresL 1 z hz
    · intro z hz; simpa [D3] using hresR z hz
  have h23 : Disjoint D2 D3 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (8 : ZMod 12)) (s := (6 : ZMod 12))
    · decide
    · intro z hz; simpa [D2] using hresL 2 z hz
    · intro z hz; simpa [D3] using hresR z hz
  have h012 : Disjoint (D0 ∪ D1) D2 := by
    rw [Finset.disjoint_left]
    intro z hz hz2
    simp only [Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact (Finset.disjoint_left.mp h02) hz hz2
    · exact (Finset.disjoint_left.mp h12) hz hz2
  have h0123 : Disjoint (D0 ∪ D1 ∪ D2) D3 := by
    rw [Finset.disjoint_left]
    intro z hz hz3
    simp only [Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · exact (Finset.disjoint_left.mp h03) hz hz3
    · exact (Finset.disjoint_left.mp h13) hz hz3
    · exact (Finset.disjoint_left.mp h23) hz hz3
  change (D0 ∪ D1 ∪ D2 ∪ D3).card = _
  rw [card_union_of_disjoint h0123, card_union_of_disjoint h012,
    card_union_of_disjoint h01]
  simp [D0, D1, D2, D3, card_dilate]

lemma mediumPack_subset_even_interval {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    mediumPack A N ⊆ zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 2) := by
  intro z hz
  simp only [mediumPack, Finset.mem_union] at hz
  rcases hz with ((hz | hz) | hz) | hz
  · obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hb' := mem_centralLeft.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨2 * b, by omega⟩
  · obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hb' := mem_centralLeft.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨2 * b, by omega⟩
  · obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hb' := mem_centralLeft.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨2 * b, by omega⟩
  · obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hb' := mem_centralRight.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      rw [Nat.dvd_iff_mod_eq_zero]
      have hbmod : b % 4 = 2 := by simpa using hb'.2.2
      omega

lemma mediumPack_disjoint_sumset {A O : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (_hsub : A ⊆ Icc 1 N)
    (hO : O ⊆ highThird A N) : Disjoint (mediumPack A N) (O + O) := by
  have hHigh : ∀ x ∈ highThird A N, x ∈ A ∧ 2 * N / 3 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hSum : O + O ⊆ highThird A N + highThird A N := by
    exact Finset.add_subset_add hO hO
  have hB (k : ℕ) (B₀ : Finset ℕ) (hB₀ : B₀ ⊆ centralImage A N) :
      ∀ b ∈ B₀, ∃ a ∈ A, a ≤ 2 * N / 3 ∧ a ∣ k * b := by
    intro b hb
    obtain ⟨a, haA, haN, hab⟩ := centralImage_has_low_divisor (hB₀ hb)
    exact ⟨a, haA, by omega, hab.mul_left k⟩
  have hD0 := mul_image_disjoint_sumset hP
    (hB 4 (centralLeft A N 0) (filter_subset _ _)) hHigh hSum
  have hD1 := mul_image_disjoint_sumset hP
    (hB 4 (centralLeft A N 1) (filter_subset _ _)) hHigh hSum
  have hD2 := mul_image_disjoint_sumset hP
    (hB 4 (centralLeft A N 2) (filter_subset _ _)) hHigh hSum
  have hD3 := mul_image_disjoint_sumset hP
    (hB 3 (centralRight A N 2) (filter_subset _ _)) hHigh hSum
  rw [Finset.disjoint_left]
  intro z hz hzO
  simp only [mediumPack, Finset.mem_union] at hz
  rcases hz with ((hz | hz) | hz) | hz
  · exact (Finset.disjoint_left.mp hD0) hz hzO
  · exact (Finset.disjoint_left.mp hD1) hz hzO
  · exact (Finset.disjoint_left.mp hD2) hz hzO
  · exact (Finset.disjoint_left.mp hD3) hz hzO

lemma selfSum_subset_even_interval {A O : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) (hO : O ⊆ highThird A N)
    (heven : ∀ z ∈ O + O, 2 ∣ z) :
    O + O ⊆ zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 2) := by
  intro z hz
  simp only [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  have hx' := mem_highThird.mp (hO hx)
  have hy' := mem_highThird.mp (hO hy)
  have hxN := (mem_Icc.mp (hsub hx'.1)).2
  have hyN := (mem_Icc.mp (hsub hy'.1)).2
  apply mem_zmodFiber.mpr
  refine ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [ZMod.natCast_eq_zero_iff]
  exact heven (x + y) (Finset.add_mem_add hx hy)

/-- The growth alternative `|O+O| ≥ 3|O|-3` completes Case 2.  The
three omitted right slices are small, while four distinct dilates and the
self-sum pack into the even part of `(4N/3,2N]`. -/
lemma medium_done_of_sumset_growth {A O : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hO : O ⊆ highThird A N)
    (hOlarge : (highThird A N).card ≤ 2 * O.card)
    (heven : ∀ z ∈ O + O, 2 ∣ z)
    (hgrowth : 3 * O.card ≤ (O + O).card + 3)
    (hsmall0 : 6 * (centralRight A N 0).card < (centralImage A N).card + 12)
    (hsmall1 : 6 * (centralRight A N 1).card < (centralImage A N).card + 12)
    (hsmall3 : 6 * (centralRight A N 3).card < (centralImage A N).card + 12) :
    3 * A.card ≤ N := by
  let U := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 2)
  have hDU : mediumPack A N ⊆ U := mediumPack_subset_even_interval hP hsub
  have hOU : O + O ⊆ U := selfSum_subset_even_interval hsub hO heven
  have hdisj : Disjoint (mediumPack A N) (O + O) :=
    mediumPack_disjoint_sumset hP hsub hO
  have hcapacity := card_add_card_le_of_disjoint_subsets hdisj hDU hOU
  have hUI : U ⊆ Icc (4 * N / 3 + 1) (2 * N) := filter_subset _ _
  have hUres : ∀ z ∈ U, (z : ZMod 2) = (0 : ZMod 2) := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hUcap := mul_card_fixed_zmod_le (0 : ZMod 2) hUI hUres
  have hDcard := mediumPack_card A N
  have hpartition := card_centralImage_eq_slices A N
  have hAcard := card_centralImage_add_high hP hsub
  change (mediumPack A N).card + (O + O).card ≤ U.card at hcapacity
  change 2 * U.card ≤ (2 * N + 2) - (4 * N / 3 + 1) at hUcap
  omega

/-! ### Quotients extracted from a long progression -/

/-- Divide precisely those members of `S` which are divisible by `k`. -/
def quotientPart (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (S.filter fun z ↦ k ∣ z).image fun z ↦ z / k

@[simp] lemma mem_quotientPart {S : Finset ℕ} {k x : ℕ} :
    x ∈ quotientPart S k ↔ ∃ z ∈ S, k ∣ z ∧ z / k = x := by
  simp only [quotientPart, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨z, ⟨hzS, hkz⟩, hzx⟩
    exact ⟨z, hzS, hkz, hzx⟩
  · rintro ⟨z, hzS, hkz, hzx⟩
    exact ⟨z, ⟨hzS, hkz⟩, hzx⟩

lemma card_quotientPart {S : Finset ℕ} {k : ℕ} (_hk : 0 < k) :
    (quotientPart S k).card = (S.filter fun z ↦ k ∣ z).card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  change x ∈ S.filter (fun z ↦ k ∣ z) at hx
  change y ∈ S.filter (fun z ↦ k ∣ z) at hy
  have hxmul : k * (x / k) = x := Nat.mul_div_cancel' (Finset.mem_filter.mp hx).2
  have hymul : k * (y / k) = y := Nat.mul_div_cancel' (Finset.mem_filter.mp hy).2
  calc
    x = k * (x / k) := hxmul.symm
    _ = k * (y / k) := congrArg (fun z ↦ k * z) (by simpa using hxy)
    _ = y := hymul

lemma quotientPart_spec {S : Finset ℕ} {k x : ℕ} (hx : x ∈ quotientPart S k) :
    k * x ∈ S := by
  obtain ⟨z, hzS, hkz, rfl⟩ := mem_quotientPart.mp hx
  have heq : k * (z / k) = z := Nat.mul_div_cancel' hkz
  rwa [heq]

lemma quotientPart_subset_Icc {S : Finset ℕ} {k L U : ℕ} (hk : 0 < k)
    (hS : S ⊆ Icc (k * L + 1) (k * U)) : quotientPart S k ⊆ Icc (L + 1) U := by
  intro x hx
  obtain ⟨z, hzS, hkz, hzx⟩ := mem_quotientPart.mp hx
  have hzI := mem_Icc.mp (hS hzS)
  have hmul : k * x = z := by
    rw [← hzx]
    simpa [mul_comm] using Nat.mul_div_cancel' hkz
  apply mem_Icc.mpr
  constructor <;> nlinarith

/-- A general index injection into the divisible terms of a difference-two
progression.  It is the floor arithmetic behind the `1/2` and `1/3`
counts in Bedert's equation (10). -/
lemma div_terms_natAP_lower {q len k p e : ℕ} (hp : 0 < p) (he : e < p)
    (hbase : k ∣ q + 2 * e) (hstep : k ∣ 2 * p) :
    len / p ≤ ((natAP q 2 len).filter fun z ↦ k ∣ z).card := by
  let I := range (len / p)
  let f : ℕ → ℕ := fun t ↦ q + 2 * (e + p * t)
  have hinj : Set.InjOn f I := by
    intro x hx y hy hxy
    dsimp [f] at hxy
    have h₁ : e + p * x = e + p * y := Nat.eq_of_mul_eq_mul_left (by omega) <|
      Nat.add_left_cancel hxy
    have h₂ : p * x = p * y := Nat.add_left_cancel h₁
    exact Nat.eq_of_mul_eq_mul_left hp h₂
  have himage : I.image f ⊆ (natAP q 2 len).filter fun z ↦ k ∣ z := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have ht' : t < len / p := by simpa [I] using ht
    have hindex : e + p * t < len := by
      have hsucc : t + 1 ≤ len / p := by omega
      have hmul : p * (t + 1) ≤ p * (len / p) := Nat.mul_le_mul_left p hsucc
      have hdiv : p * (len / p) ≤ len := Nat.mul_div_le len p
      calc
        e + p * t < p + p * t := Nat.add_lt_add_right he (p * t)
        _ = p * (t + 1) := by ring
        _ ≤ len := hmul.trans hdiv
    apply Finset.mem_filter.mpr
    constructor
    · exact mem_natAP.mpr ⟨e + p * t, hindex, rfl⟩
    · obtain ⟨u, hu⟩ := hbase
      obtain ⟨v, hv⟩ := hstep
      refine ⟨u + v * t, ?_⟩
      dsimp [f]
      calc
        q + 2 * (e + p * t) = (q + 2 * e) + (2 * p) * t := by ring
        _ = k * u + (k * v) * t := by rw [hu, hv]
        _ = k * (u + v * t) := by ring
  calc
    len / p = I.card := by simp [I]
    _ = (I.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ _ := card_le_card himage

lemma exists_four_offset {q : ℕ} (hq : 2 ∣ q) :
    ∃ e < 2, 4 ∣ q + 2 * e := by
  rw [Nat.dvd_iff_mod_eq_zero] at hq
  have hq4 : q % 4 < 4 := Nat.mod_lt _ (by omega)
  have hrel : q % 2 = (q % 4) % 2 := by
    exact (Nat.mod_mod_of_dvd q (by omega : 2 ∣ 4)).symm
  interval_cases h : q % 4 <;> simp at hrel
  · exact ⟨0, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩
  · omega
  · exact ⟨1, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩
  · omega

lemma exists_three_offset (q : ℕ) : ∃ e < 3, 3 ∣ q + 2 * e := by
  have hq3 : q % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : q % 3
  · exact ⟨0, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩
  · exact ⟨1, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩
  · exact ⟨2, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩

lemma natAP_div_four_lower {q len : ℕ} (hq : 2 ∣ q) :
    len / 2 ≤ ((natAP q 2 len).filter fun z ↦ 4 ∣ z).card := by
  obtain ⟨e, he, hdiv⟩ := exists_four_offset hq
  exact div_terms_natAP_lower (by omega) he hdiv (by norm_num)

lemma natAP_div_three_lower (q len : ℕ) :
    len / 3 ≤ ((natAP q 2 len).filter fun z ↦ 3 ∣ z).card := by
  obtain ⟨e, he, hdiv⟩ := exists_three_offset q
  exact div_terms_natAP_lower (by omega) he hdiv (by norm_num)

lemma centralImage_disjoint_quotientPart {A H S : Finset ℕ} {N k : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hH : ∀ x ∈ H, x ∈ A ∧ 2 * N / 3 < x) (hS : S ⊆ H + H) :
    Disjoint (centralImage A N) (quotientPart S k) := by
  rw [Finset.disjoint_left]
  intro x hxB hxQ
  obtain ⟨a, haA, haN, hax⟩ := centralImage_has_low_divisor hxB
  have hkx : k * x ∈ S := quotientPart_spec hxQ
  have hsum := hS hkx
  simp only [Finset.mem_add] at hsum
  obtain ⟨b, hb, c, hc, hbc⟩ := hsum
  have hb' := hH b hb
  have hc' := hH c hc
  apply hP.not_dvd_add haA hb'.1 hc'.1 (by omega) (by omega)
  rw [hbc]
  exact hax.mul_left k

/-- The long difference-two progression alternative completes Case 2.
This is equations (8)--(12) of Bedert, with every floor loss retained as
an integer inequality. -/
lemma medium_done_of_long_AP {A O : Finset ℕ} {N q : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hupper : 9 * (highThird A N).card < 2 * N + 12)
    (hO : O ⊆ highThird A N)
    (hOlarge : (highThird A N).card ≤ 2 * O.card)
    (heven : ∀ z ∈ O + O, 2 ∣ z)
    (hQfull : natAP q 2 (O.card + O.card - 1) ⊆ O + O) :
    3 * A.card ≤ N + 6 := by
  let H := highThird A N
  let Q := natAP q 2 (H.card - 1)
  let Q3 := quotientPart Q 3
  let Q4 := quotientPart Q 4
  let Ap := Q3 ∪ Q4
  let R := zmodFiber (H + H) (3 : ZMod 6)
  let D := quotientPart R 3
  let C := Ap ∪ D
  change N + 144 ≤ 6 * H.card at hmedium
  change 9 * H.card < 2 * N + 12 at hupper
  change O ⊆ H at hO
  change H.card ≤ 2 * O.card at hOlarge
  have hHpos : 24 ≤ H.card := by
    omega
  have hQsub : Q ⊆ O + O := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
    apply hQfull
    apply mem_natAP.mpr
    exact ⟨j, by change j < H.card - 1 at hj; omega, rfl⟩
  have hHI : H ⊆ Icc (2 * N / 3 + 1) N := highThird_subset_interval hsub
  have hQHI : Q ⊆ H + H := hQsub.trans (Finset.add_subset_add hO hO)
  have hQI : Q ⊆ Icc (4 * N / 3 + 1) (2 * N) := by
    intro z hz
    have hsum := hQHI hz
    simp only [Finset.mem_add] at hsum
    obtain ⟨x, hx, y, hy, rfl⟩ := hsum
    have hxI := mem_Icc.mp (hHI hx)
    have hyI := mem_Icc.mp (hHI hy)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hqQ : q ∈ Q := by
    apply mem_natAP.mpr
    exact ⟨0, by omega, by simp⟩
  have hqeven : 2 ∣ q := heven q (hQsub hqQ)
  have hQcard : Q.card = H.card - 1 := by
    simpa [Q] using card_natAP (a := q) (d := 2) (len := H.card - 1) (by omega)
  have hQ4card : H.card ≤ 2 * Q4.card + 2 := by
    have h := natAP_div_four_lower (q := q) (len := H.card - 1) hqeven
    rw [← card_quotientPart (S := Q) (k := 4) (by omega)] at h
    change (H.card - 1) / 2 ≤ Q4.card at h
    omega
  have hQ3card : H.card ≤ 3 * Q3.card + 3 := by
    have h := natAP_div_three_lower q (H.card - 1)
    rw [← card_quotientPart (S := Q) (k := 3) (by omega)] at h
    change (H.card - 1) / 3 ≤ Q3.card at h
    omega
  have hQ34disj : Disjoint Q3 Q4 := by
    rw [Finset.disjoint_left]
    intro x hx3 hx4
    have h3x : 3 * x ∈ Q := quotientPart_spec hx3
    have h4x : 4 * x ∈ Q := quotientPart_spec hx4
    obtain ⟨j3, hj3, heq3⟩ := mem_natAP.mp h3x
    obtain ⟨j4, hj4, heq4⟩ := mem_natAP.mp h4x
    have hqI := mem_Icc.mp (hQI hqQ)
    have hfloor : 4 * N ≤ 3 * (4 * N / 3 + 1) := by omega
    change j3 < H.card - 1 at hj3
    change j4 < H.card - 1 at hj4
    change q + 2 * j3 = 3 * x at heq3
    change q + 2 * j4 = 4 * x at heq4
    omega
  have hApcard : Ap.card = Q3.card + Q4.card := by
    change (Q3 ∪ Q4).card = _
    exact card_union_of_disjoint hQ34disj
  have hHinterval : H ⊆ Icc (2 * N / 3 + 1)
      (2 * N / 3 + (N - 2 * N / 3)) := by
    simpa [H, Nat.add_sub_of_le (by omega : 2 * N / 3 ≤ N)] using hHI
  have hdenseCond : (N - 2 * N / 3) + 6 ≤ 2 * H.card := by
    change N + 144 ≤ 6 * H.card at hmedium
    omega
  have hRdense := dense_residue_Icc (q := 6) (by omega) hHinterval hdenseCond
    (3 : ZMod 6)
  have hDcard : D.card = R.card := by
    change (quotientPart R 3).card = R.card
    rw [card_quotientPart (S := R) (k := 3) (by omega)]
    apply congrArg Finset.card
    ext z
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.1
    · intro hzR
      refine ⟨hzR, ?_⟩
      have hmodZ := (mem_zmodFiber.mp hzR).2
      have hmod : z % 6 = 3 :=
        (ZMod.natCast_eq_natCast_iff z 3 6).mp hmodZ
      rw [Nat.dvd_iff_mod_eq_zero]
      have hrel : z % 3 = (z % 6) % 3 :=
        (Nat.mod_mod_of_dvd z (by omega : 3 ∣ 6)).symm
      omega
  have hDQ3 : Disjoint D Q3 := by
    rw [Finset.disjoint_left]
    intro x hxD hx3
    have h3D : 3 * x ∈ R := quotientPart_spec hxD
    have h3Q : 3 * x ∈ Q := quotientPart_spec hx3
    have hmodZ := (mem_zmodFiber.mp h3D).2
    have hmod : (3 * x) % 6 = 3 := by
      have hm := (ZMod.natCast_eq_natCast_iff (3 * x) 3 6).mp hmodZ
      exact hm
    have he : 2 ∣ 3 * x := heven (3 * x) (hQsub h3Q)
    rw [Nat.dvd_iff_mod_eq_zero] at he
    omega
  let K := Ap ∩ D
  have hKsubQ4 : K ⊆ Q4 := by
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    have hxAp : x ∈ Ap := hx'.1
    change x ∈ Q3 ∪ Q4 at hxAp
    simp only [Finset.mem_union] at hxAp
    rcases hxAp with hx3 | hx4
    · exact False.elim ((Finset.disjoint_left.mp hDQ3) hx'.2 hx3)
    · exact hx4
  have hKsubD : K ⊆ D := by
    exact fun _ hx ↦ (Finset.mem_inter.mp hx).2
  have hKI : K ⊆ zmodFiber (Icc (4 * N / 9 + 1) (N / 2)) (1 : ZMod 2) := by
    intro x hx
    have hx4 := hKsubQ4 hx
    have hxD := hKsubD hx
    have h4Q : 4 * x ∈ Q := quotientPart_spec hx4
    have h3R : 3 * x ∈ R := quotientPart_spec hxD
    have h4I := mem_Icc.mp (hQI h4Q)
    have h3sum := (mem_zmodFiber.mp h3R).1
    simp only [Finset.mem_add] at h3sum
    obtain ⟨u, hu, v, hv, huv⟩ := h3sum
    have huI := mem_Icc.mp (hHI hu)
    have hvI := mem_Icc.mp (hHI hv)
    have hmodZ := (mem_zmodFiber.mp h3R).2
    have hmod : (3 * x) % 6 = 3 :=
      (ZMod.natCast_eq_natCast_iff (3 * x) 3 6).mp hmodZ
    apply mem_zmodFiber.mpr
    constructor
    · apply mem_Icc.mpr
      constructor <;> omega
    · have hxmod : x % 2 = 1 := by omega
      exact (ZMod.natCast_eq_natCast_iff x 1 2).mpr hxmod
  have hKcap := mul_card_fixed_zmod_le (1 : ZMod 2)
    (hS := hKI.trans (filter_subset _ _)) (fun x hx ↦ (mem_zmodFiber.mp (hKI hx)).2)
  have hCcardEq : C.card + K.card = Ap.card + D.card := by
    simpa [C, K] using Finset.card_union_add_card_inter Ap D
  have hRsum : R ⊆ H + H := filter_subset _ _
  have hHigh : ∀ x ∈ H, x ∈ A ∧ 2 * N / 3 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hBdisjQ3 := centralImage_disjoint_quotientPart (k := 3) hP hHigh hQHI
  have hBdisjQ4 := centralImage_disjoint_quotientPart (k := 4) hP hHigh hQHI
  have hBdisjD := centralImage_disjoint_quotientPart (k := 3) hP hHigh hRsum
  have hBdisjC : Disjoint (centralImage A N) C := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    change x ∈ Ap ∪ D at hxC
    simp only [Finset.mem_union] at hxC
    rcases hxC with hxAp | hxD
    · change x ∈ Q3 ∪ Q4 at hxAp
      simp only [Finset.mem_union] at hxAp
      rcases hxAp with hx3 | hx4
      · exact (Finset.disjoint_left.mp hBdisjQ3) hxB hx3
      · exact (Finset.disjoint_left.mp hBdisjQ4) hxB hx4
    · exact (Finset.disjoint_left.mp hBdisjD) hxB hxD
  have hCI : C ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro x hxC
    change x ∈ Ap ∪ D at hxC
    simp only [Finset.mem_union] at hxC
    rcases hxC with hxAp | hxD
    · change x ∈ Q3 ∪ Q4 at hxAp
      simp only [Finset.mem_union] at hxAp
      rcases hxAp with hx3 | hx4
      · have h3I := mem_Icc.mp (hQI (quotientPart_spec hx3))
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · have h4I := mem_Icc.mp (hQI (quotientPart_spec hx4))
        exact mem_Icc.mpr ⟨by omega, by omega⟩
    · have h3R := quotientPart_spec hxD
      have h3sum := (mem_zmodFiber.mp h3R).1
      simp only [Finset.mem_add] at h3sum
      obtain ⟨u, hu, v, hv, huv⟩ := h3sum
      have huI := mem_Icc.mp (hHI hu)
      have hvI := mem_Icc.mp (hHI hv)
      exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hBI : centralImage A N ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro b hb
    have hb' := mem_ratSection.mp (centralImage_subset_window hP hsub hb)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcentralCapacity := card_add_card_le_of_disjoint_subsets hBdisjC hBI hCI
  have hCentralCard := card_Icc_le (S := Icc (N / 3 + 1) (2 * N / 3))
    (subset_rfl)
  have hAcard := card_centralImage_add_high hP hsub
  change (centralImage A N).card + H.card = A.card at hAcard
  change 2 * H.card ≤ 6 * (R.card + 1) at hRdense
  change 2 * K.card ≤ (N / 2 + 2) - (4 * N / 9 + 1) at hKcap
  change (centralImage A N).card + C.card ≤
    (Icc (N / 3 + 1) (2 * N / 3)).card at hcentralCapacity
  omega

/-- Complete Case 2 once the Bardaji--Grynkiewicz alternative is available
for the two parity fibers of the top third. -/
lemma caseTwo_of_BG {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hupper : 9 * (highThird A N).card < 2 * N + 12)
    (hBG : ∀ r < 2,
      BGAlternative (parityPart (highThird A N) r) (parityPart (highThird A N) r)) :
    3 * A.card ≤ N + 6 := by
  obtain ⟨r, hr, hrlarge⟩ := exists_large_parityPart (highThird A N)
  let O := parityPart (highThird A N) r
  have hO : O ⊆ highThird A N := filter_subset _ _
  have hOlarge : (highThird A N).card ≤ 2 * O.card := hrlarge
  have heven : ∀ z ∈ O + O, 2 ∣ z := by
    intro z hz
    exact parityPart_sum_even hz
  rcases hBG r hr with hgrowth | hstruct
  · have hgrowth' : 3 * O.card ≤ (O + O).card + 3 := by
      change O.card + O.card + min O.card O.card ≤ (O + O).card + 3 at hgrowth
      simp only [min_self] at hgrowth
      omega
    by_cases hlarge0 : (centralImage A N).card + 12 ≤
        6 * (centralRight A N 0).card
    · exact (medium_done_of_large_right_slice hP hsub hmedium hlarge0).trans
        (Nat.le_add_right N 6)
    by_cases hlarge1 : (centralImage A N).card + 12 ≤
        6 * (centralRight A N 1).card
    · exact (medium_done_of_large_right_slice hP hsub hmedium hlarge1).trans
        (Nat.le_add_right N 6)
    by_cases hlarge3 : (centralImage A N).card + 12 ≤
        6 * (centralRight A N 3).card
    · exact (medium_done_of_large_right_slice hP hsub hmedium hlarge3).trans
        (Nat.le_add_right N 6)
    exact (medium_done_of_sumset_growth hP hsub hmedium hO hOlarge heven hgrowth'
      (by omega) (by omega) (by omega)).trans (Nat.le_add_right N 6)
  · obtain ⟨q, d, hd, hQ, hres⟩ := hstruct
    have hOI : O ⊆ Icc (2 * N / 3 + 1) N :=
      hO.trans (highThird_subset_interval hsub)
    have hOmedium : N + 144 ≤ 12 * O.card := by omega
    have hd2 := medium_structural_step_eq_two hOI hOmedium hd hres hQ heven
    subst d
    exact medium_done_of_long_AP hP hsub hmedium hupper hO hOlarge heven hQ

lemma caseTwo {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hupper : 9 * (highThird A N).card < 2 * N + 12) :
    3 * A.card ≤ N + 6 :=
  caseTwo_of_BG hP hsub hmedium hupper fun _ _ ↦ bgAlternative_self _

/-! ### Strengthened-induction infrastructure for Case 3 -/

/-- Integer-cleared form of Bedert's strengthened induction statement,
with `δ = 1/300000`. -/
def StrongBound (C N : ℕ) (A : Finset ℕ) : Prop :=
  3 * A.card ≤ N + 2 ∨
    300000 * A.card ≤ 99999 * N + 300000 * C

/-- The additive-constant induction target needed for Problem 13 itself. -/
def CoarseBound (C N : ℕ) (A : Finset ℕ) : Prop :=
  3 * A.card ≤ N + C

/-- The part of `A` in the initial interval ending at `N-a`. -/
def initialPart (A : Finset ℕ) (N a : ℕ) : Finset ℕ :=
  A.filter fun x ↦ x ≤ N - a

/-- The terminal interval of length `a`. -/
def terminalPart (A : Finset ℕ) (N a : ℕ) : Finset ℕ :=
  A.filter fun x ↦ N - a < x

@[simp] lemma mem_initialPart {A : Finset ℕ} {N a x : ℕ} :
    x ∈ initialPart A N a ↔ x ∈ A ∧ x ≤ N - a := by
  simp [initialPart]

@[simp] lemma mem_terminalPart {A : Finset ℕ} {N a x : ℕ} :
    x ∈ terminalPart A N a ↔ x ∈ A ∧ N - a < x := by
  simp [terminalPart]

lemma card_initial_add_terminal (A : Finset ℕ) (N a : ℕ) :
    (initialPart A N a).card + (terminalPart A N a).card = A.card := by
  let P := initialPart A N a
  let T := terminalPart A N a
  have hdisj : Disjoint P T := by
    rw [Finset.disjoint_left]
    intro x hxP hxT
    have hp := mem_initialPart.mp hxP
    have ht := mem_terminalPart.mp hxT
    omega
  have hunion : P ∪ T = A := by
    ext x
    simp only [P, T, Finset.mem_union, mem_initialPart, mem_terminalPart]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      exact (le_or_gt x (N - a)).imp (And.intro hx) (And.intro hx)
  rw [← card_union_of_disjoint hdisj, hunion]

lemma initialPart_subset_Icc {A : Finset ℕ} {N a : ℕ}
    (hsub : A ⊆ Icc 1 N) : initialPart A N a ⊆ Icc 1 (N - a) := by
  intro x hx
  have hx' := mem_initialPart.mp hx
  exact mem_Icc.mpr ⟨(mem_Icc.mp (hsub hx'.1)).1, hx'.2⟩

lemma initialPart_property {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) : IsForbiddenTripleFree (initialPart A N a) :=
  hP.mono (filter_subset _ _)

/-- If the strengthened conclusion fails at `N`, every terminal interval
has density strictly larger than `1/3-δ`; this is Bedert's estimate (T). -/
lemma terminal_dense_of_not_strongBound {A : Finset ℕ} {N a C : ℕ}
    (ha : 0 < a) (haN : a ≤ N)
    (hfail : ¬ StrongBound C N A)
    (hind : StrongBound C (N - a) (initialPart A N a)) :
    99999 * a < 300000 * (terminalPart A N a).card := by
  by_contra hnot
  have htail : 300000 * (terminalPart A N a).card ≤ 99999 * a := by omega
  have hcard := card_initial_add_terminal A N a
  apply hfail
  rcases hind with hceil | hlinear
  · left
    have hscale : 300000 * (initialPart A N a).card ≤
        100000 * (N - a + 2) := by omega
    have hNa : N - a + a = N := Nat.sub_add_cancel haN
    omega
  · right
    have hNa : N - a + a = N := Nat.sub_add_cancel haN
    omega

/-- Failure of the additive-constant target makes every terminal interval
strictly denser than one third. -/
lemma terminal_dense_of_not_coarseBound {A : Finset ℕ} {N a C : ℕ}
    (_ha : 0 < a) (haN : a ≤ N)
    (hfail : ¬ CoarseBound C N A)
    (hind : CoarseBound C (N - a) (initialPart A N a)) :
    a < 3 * (terminalPart A N a).card := by
  by_contra hnot
  have htail : 3 * (terminalPart A N a).card ≤ a := by omega
  have hcard := card_initial_add_terminal A N a
  apply hfail
  change 3 * A.card ≤ N + C
  change 3 * (initialPart A N a).card ≤ N - a + C at hind
  have hNa : N - a + a = N := Nat.sub_add_cancel haN
  omega

/-- Elements divisible by `k` in an initial rational segment. -/
def divisibleInitial (A : Finset ℕ) (N k ell : ℕ) : Finset ℕ :=
  A.filter fun x ↦ k ∣ x ∧ ell * x ≤ N

@[simp] lemma mem_divisibleInitial {A : Finset ℕ} {N k ell x : ℕ} :
    x ∈ divisibleInitial A N k ell ↔ x ∈ A ∧ k ∣ x ∧ ell * x ≤ N := by
  simp [divisibleInitial]

lemma card_image_div_divisibleInitial {A : Finset ℕ} {N k ell : ℕ} (_hk : 0 < k) :
    ((divisibleInitial A N k ell).image fun x ↦ x / k).card =
      (divisibleInitial A N k ell).card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  change x ∈ divisibleInitial A N k ell at hx
  change y ∈ divisibleInitial A N k ell at hy
  have hxdiv := (mem_divisibleInitial.mp hx).2.1
  have hydiv := (mem_divisibleInitial.mp hy).2.1
  calc
    x = k * (x / k) := (Nat.mul_div_cancel' hxdiv).symm
    _ = k * (y / k) := congrArg (fun z ↦ k * z) (by simpa using hxy)
    _ = y := Nat.mul_div_cancel' hydiv

lemma image_div_divisibleInitial_subset {A : Finset ℕ} {N k ell : ℕ}
    (hk : 0 < k) (hell : 0 < ell) (hsub : A ⊆ Icc 1 N) :
    (divisibleInitial A N k ell).image (fun x ↦ x / k) ⊆
      Icc 1 (N / (k * ell)) := by
  intro y hy
  simp only [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx' := mem_divisibleInitial.mp hx
  have hxpos := (mem_Icc.mp (hsub hx'.1)).1
  have hxmul : k * (x / k) = x := Nat.mul_div_cancel' hx'.2.1
  apply mem_Icc.mpr
  constructor
  · have : 0 < x / k := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd hxpos hx'.2.1
      · exact hk
    omega
  · apply (Nat.le_div_iff_mul_le (by positivity : 0 < k * ell)).2
    calc
      x / k * (k * ell) = ell * (k * (x / k)) := by ring
      _ = ell * x := by rw [hxmul]
      _ ≤ N := hx'.2.2

lemma image_div_divisibleInitial_property {A : Finset ℕ} {N k ell : ℕ}
    (hk : 0 < k) (hP : IsForbiddenTripleFree A) :
    IsForbiddenTripleFree
      ((divisibleInitial A N k ell).image fun x ↦ x / k) := by
  apply (hP.mono (filter_subset _ _)).map_div hk
  intro x hx
  exact (mem_divisibleInitial.mp hx).2.1

/-- The induction estimate for multiples, corresponding to (M). -/
lemma divisibleInitial_card_bound {A : Finset ℕ} {N k ell C : ℕ}
    (hk : 0 < k) (_hell : 0 < ell) (_hP : IsForbiddenTripleFree A)
    (_hsub : A ⊆ Icc 1 N)
    (hind : StrongBound C (N / (k * ell))
      ((divisibleInitial A N k ell).image fun x ↦ x / k)) :
    3 * (divisibleInitial A N k ell).card ≤ N / (k * ell) + 3 * C + 2 := by
  let D := divisibleInitial A N k ell
  let Q := D.image fun x ↦ x / k
  have hcard : Q.card = D.card := card_image_div_divisibleInitial hk
  change 3 * D.card ≤ N / (k * ell) + 3 * C + 2
  rw [← hcard]
  rcases hind with hceil | hlinear
  · change 3 * Q.card ≤ N / (k * ell) + 2 at hceil
    omega
  · change 300000 * Q.card ≤ 99999 * (N / (k * ell)) + 300000 * C at hlinear
    omega

lemma divisibleInitial_card_bound_coarse {A : Finset ℕ} {N k ell C : ℕ}
    (hk : 0 < k) (_hell : 0 < ell) (_hP : IsForbiddenTripleFree A)
    (_hsub : A ⊆ Icc 1 N)
    (hind : CoarseBound C (N / (k * ell))
      ((divisibleInitial A N k ell).image fun x ↦ x / k)) :
    3 * (divisibleInitial A N k ell).card ≤ N / (k * ell) + C := by
  let D := divisibleInitial A N k ell
  let Q := D.image fun x ↦ x / k
  have hcard : Q.card = D.card := card_image_div_divisibleInitial hk
  change 3 * D.card ≤ N / (k * ell) + C
  rw [← hcard]
  exact hind

/-! ### The basic quotient packing in Case 3 -/

/-- `A ∩ (N/2,N]`. -/
def upperHalf (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ratSection A N 1 2 1 1

/-- `A ∩ (N/2,2N/3]`. -/
def middleSixth (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ratSection A N 1 2 2 3

/-- One residue class modulo three in the upper half. -/
def upperHalfResidue (A : Finset ℕ) (N r : ℕ) : Finset ℕ :=
  (upperHalf A N).filter fun x ↦ x % 3 = r % 3

@[simp] lemma mem_upperHalf {A : Finset ℕ} {N x : ℕ} :
    x ∈ upperHalf A N ↔ x ∈ A ∧ N < 2 * x ∧ x ≤ N := by
  simp [upperHalf]

@[simp] lemma mem_middleSixth {A : Finset ℕ} {N x : ℕ} :
    x ∈ middleSixth A N ↔ x ∈ A ∧ N < 2 * x ∧ 3 * x ≤ 2 * N := by
  simp [middleSixth]

@[simp] lemma mem_upperHalfResidue {A : Finset ℕ} {N r x : ℕ} :
    x ∈ upperHalfResidue A N r ↔
      x ∈ upperHalf A N ∧ x % 3 = r % 3 := by
  simp [upperHalfResidue]

lemma upperHalf_subset_interval {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Icc 1 N) :
    upperHalf A N ⊆ Icc (N / 2 + 1) N := by
  intro x hx
  have hx' := mem_upperHalf.mp hx
  exact mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hsub hx'.1)).2⟩

lemma terminalPart_half_eq_upperHalf {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    terminalPart A N ((N + 1) / 2) = upperHalf A N := by
  ext x
  simp only [mem_terminalPart, mem_upperHalf]
  constructor
  · rintro ⟨hx, htail⟩
    exact ⟨hx, by omega, (mem_Icc.mp (hsub hx)).2⟩
  · rintro ⟨hx, hlo, hhi⟩
    exact ⟨hx, by omega⟩

lemma terminalPart_third_eq_highThird (A : Finset ℕ) (N : ℕ) :
    terminalPart A N ((N + 2) / 3) = highThird A N := by
  ext x
  simp only [mem_terminalPart, mem_highThird]
  constructor
  · rintro ⟨hx, htail⟩
    exact ⟨hx, by omega⟩
  · rintro ⟨hx, hlo⟩
    exact ⟨hx, by omega⟩

lemma card_middleSixth_add_highThird {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    (middleSixth A N).card + (highThird A N).card = (upperHalf A N).card := by
  have hdisj : Disjoint (middleSixth A N) (highThird A N) := by
    rw [Finset.disjoint_left]
    intro x hxM hxH
    have hm := mem_middleSixth.mp hxM
    have hh := mem_highThird.mp hxH
    omega
  have hunion : middleSixth A N ∪ highThird A N = upperHalf A N := by
    ext x
    simp only [Finset.mem_union, mem_middleSixth, mem_highThird, mem_upperHalf]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.1, (mem_Icc.mp (hsub h.1)).2⟩
      · exact ⟨h.1, by omega, (mem_Icc.mp (hsub h.1)).2⟩
    · intro h
      by_cases hx : 3 * x ≤ 2 * N
      · exact Or.inl ⟨h.1, h.2.1, hx⟩
      · exact Or.inr ⟨h.1, by omega⟩
  rw [← card_union_of_disjoint hdisj, hunion]

lemma card_upperHalf_residues (A : Finset ℕ) (N : ℕ) :
    (upperHalfResidue A N 0).card + (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card = (upperHalf A N).card := by
  let V := upperHalf A N
  have hmap : (V : Set ℕ).MapsTo (fun x ↦ x % 3) (range 3) := by
    intro x hx
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  simp only [sum_range_succ, sum_range_zero] at hfiber
  have hs (i : ℕ) (hi : i < 3) :
      V.filter (fun x ↦ x % 3 = i) = upperHalfResidue A N i := by
    ext x
    have himod : i % 3 = i := Nat.mod_eq_of_lt hi
    simp [V, upperHalfResidue, himod]
  rw [hs 0 (by omega), hs 1 (by omega), hs 2 (by omega)] at hfiber
  change (upperHalf A N).card = 0 + (upperHalfResidue A N 0).card +
    (upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card at hfiber
  omega

/-- The sums from the upper half which are divisible by three, divided by
three (Bedert's `A'''`). -/
def thirdSumQuotient (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  quotientPart (zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)) 3

lemma thirdSumQuotient_card (A : Finset ℕ) (N : ℕ) :
    (thirdSumQuotient A N).card =
      (zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)).card := by
  let R := zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)
  change (quotientPart R 3).card = R.card
  rw [card_quotientPart (S := R) (k := 3) (by omega)]
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hz
    refine ⟨hz, ?_⟩
    have hz0 := (mem_zmodFiber.mp hz).2
    rw [ZMod.natCast_eq_zero_iff] at hz0
    exact hz0

lemma thirdSumQuotient_subset_central {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    thirdSumQuotient A N ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
  intro x hx
  have h3 := quotientPart_spec hx
  have hsum := (mem_zmodFiber.mp h3).1
  simp only [Finset.mem_add] at hsum
  obtain ⟨u, hu, v, hv, huv⟩ := hsum
  have hu' := mem_upperHalf.mp hu
  have hv' := mem_upperHalf.mp hv
  have huN := (mem_Icc.mp (hsub hu'.1)).2
  have hvN := (mem_Icc.mp (hsub hv'.1)).2
  exact mem_Icc.mpr ⟨by omega, by omega⟩

/-- Equation (18): the central power-of-two image and `A'''` are
disjoint.  The proof includes the exceptional possibility that the low
divisor is not smaller than both upper-half summands. -/
lemma centralImage_disjoint_thirdSumQuotient {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (centralImage A N) (thirdSumQuotient A N) := by
  rw [Finset.disjoint_left]
  intro b hbB hbQ
  obtain ⟨a, haA, haN, hab⟩ := centralImage_has_low_divisor hbB
  have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hbB)
  have hbpos : 0 < b := by omega
  have hapos : 0 < a := hP.pos_of_mem hsub haA
  have hab_le : a ≤ b := Nat.le_of_dvd hbpos hab
  have h3 := quotientPart_spec hbQ
  have hsum := (mem_zmodFiber.mp h3).1
  simp only [Finset.mem_add] at hsum
  obtain ⟨x, hx, y, hy, hxy⟩ := hsum
  have hx' := mem_upperHalf.mp hx
  have hy' := mem_upperHalf.mp hy
  have hxN := (mem_Icc.mp (hsub hx'.1)).2
  have hyN := (mem_Icc.mp (hsub hy'.1)).2
  by_cases hax : a < x
  · by_cases hay : a < y
    · apply hP.not_dvd_add haA hx'.1 hy'.1 hax hay
      rw [hxy]
      exact hab.mul_left 3
    · have : x > N := by omega
      omega
  · have : y > N := by omega
    omega

lemma caseThree_basic_packing {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (centralImage A N).card + (thirdSumQuotient A N).card ≤
      (Icc (N / 3 + 1) (2 * N / 3)).card := by
  apply card_add_card_le_of_disjoint_subsets
    (centralImage_disjoint_thirdSumQuotient hP hsub)
  · intro b hb
    have hb' := mem_ratSection.mp (centralImage_subset_window hP hsub hb)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · exact thirdSumQuotient_subset_central hsub

lemma upperHalf_sum_residue_zero_lower {A : Finset ℕ} {N : ℕ}
    (hV1 : (upperHalfResidue A N 1).Nonempty)
    (hV2 : (upperHalfResidue A N 2).Nonempty) :
    2 * (upperHalf A N).card ≤
      3 * ((zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)).card + 1) := by
  let V := upperHalf A N
  let V0 := upperHalfResidue A N 0
  let V1 := upperHalfResidue A N 1
  let V2 := upperHalfResidue A N 2
  let R := zmodFiber (V + V) (0 : ZMod 3)
  change 2 * V.card ≤ 3 * (R.card + 1)
  change V1.Nonempty at hV1
  change V2.Nonempty at hV2
  have hpart := card_upperHalf_residues A N
  change V0.card + V1.card + V2.card = V.card at hpart
  have h12sub : V1 + V2 ⊆ R := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hx'.1 hy'.1
    · have hxZ : (x : ZMod 3) = 1 := by
        apply (ZMod.natCast_eq_natCast_iff x 1 3).mpr
        change x % 3 = 1 % 3
        simpa using hx'.2
      have hyZ : (y : ZMod 3) = 2 := by
        apply (ZMod.natCast_eq_natCast_iff y 2 3).mpr
        change y % 3 = 2 % 3
        simpa using hy'.2
      push_cast
      rw [hxZ, hyZ]
      decide
  have h12cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hV1 hV2
  have h12 : V1.card + V2.card ≤ R.card + 1 := by
    change V1.card + V2.card - 1 ≤ (V1 + V2).card at h12cd
    have hsubcard : (V1 + V2).card ≤ R.card := card_le_card h12sub
    have hV1pos : 0 < V1.card := card_pos.mpr hV1
    have hV2pos : 0 < V2.card := card_pos.mpr hV2
    omega
  by_cases hzero : 3 * V0.card < V.card
  · omega
  · have hV0 : V0.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hV1pos : 0 < V1.card := card_pos.mpr hV1
      simp only [hempty, card_empty, mul_zero] at hzero hpart
      omega
    have h00sub : V0 + V0 ⊆ R := by
      intro z hz
      simp only [Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      have hx' := mem_upperHalfResidue.mp hx
      have hy' := mem_upperHalfResidue.mp hy
      apply mem_zmodFiber.mpr
      constructor
      · exact Finset.add_mem_add hx'.1 hy'.1
      · have hxZ : (x : ZMod 3) = 0 := by
          apply (ZMod.natCast_eq_natCast_iff x 0 3).mpr
          change x % 3 = 0 % 3
          simpa using hx'.2
        have hyZ : (y : ZMod 3) = 0 := by
          apply (ZMod.natCast_eq_natCast_iff y 0 3).mpr
          change y % 3 = 0 % 3
          simpa using hy'.2
        push_cast
        rw [hxZ, hyZ]
        rfl
    have h00cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hV0 hV0
    have h00 : 2 * V0.card ≤ R.card + 1 := by
      change V0.card + V0.card - 1 ≤ (V0 + V0).card at h00cd
      have hsubcard : (V0 + V0).card ≤ R.card := card_le_card h00sub
      have hV0pos : 0 < V0.card := card_pos.mpr hV0
      omega
    omega

lemma thirdSumQuotient_lower {A : Finset ℕ} {N : ℕ}
    (hV1 : (upperHalfResidue A N 1).Nonempty)
    (hV2 : (upperHalfResidue A N 2).Nonempty) :
    2 * (upperHalf A N).card ≤ 3 * ((thirdSumQuotient A N).card + 1) := by
  rw [thirdSumQuotient_card]
  exact upperHalf_sum_residue_zero_lower hV1 hV2

/-- If the middle sixth is larger than half the top third, equation (18)
already gives the ceiling branch of the induction. -/
lemma caseThree_of_large_middle {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV1 : (upperHalfResidue A N 1).Nonempty)
    (hV2 : (upperHalfResidue A N 2).Nonempty)
    (hmid : (highThird A N).card + 3 ≤ 2 * (middleSixth A N).card) :
    3 * A.card ≤ N + 2 := by
  have hVcard := card_middleSixth_add_highThird hsub
  have hD := thirdSumQuotient_lower hV1 hV2
  have hDH : (highThird A N).card ≤ (thirdSumQuotient A N).card := by
    omega
  have hpack := caseThree_basic_packing hP hsub
  have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
    simp
    omega
  have hAcard := card_centralImage_add_high hP hsub
  omega

/-! ### The modified half-window image (Bedert's Lemma 5) -/

def lowHalf (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter fun a ↦ 2 * a ≤ N

noncomputable def halfImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (lowHalf A N).image (scaledMove 0 N 4)

@[simp] lemma mem_lowHalf {A : Finset ℕ} {N a : ℕ} :
    a ∈ lowHalf A N ↔ a ∈ A ∧ 2 * a ≤ N := by
  simp [lowHalf]

lemma halfImage_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (halfImage A N).card = (lowHalf A N).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono (filter_subset _ _))
  intro a ha
  exact hP.pos_of_mem hsub ((mem_lowHalf.mp ha).1)

lemma halfImage_mem_iff {A : Finset ℕ} {N b : ℕ} :
    b ∈ halfImage A N ↔
      ∃ a ∈ A, 2 * a ≤ N ∧ scaledMove 0 N 4 a = b := by
  simp only [halfImage, Finset.mem_image, mem_lowHalf]
  constructor
  · rintro ⟨a, ⟨ha, haN⟩, rfl⟩
    exact ⟨a, ha, haN, rfl⟩
  · rintro ⟨a, ha, haN, rfl⟩
    exact ⟨a, ⟨ha, haN⟩, rfl⟩

lemma halfImage_subset_window {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    halfImage A N ⊆ Icc (N / 4 + 1) (N / 2) := by
  intro b hb
  obtain ⟨a, haA, haN, rfl⟩ := halfImage_mem_iff.mp hb
  have hapos := hP.pos_of_mem hsub haA
  have hlo := lt_scaledMove (b := 0) (T := N) (q := 4) (by omega) hapos
  have hup := scaledMove_le (b := 0) (T := N) (q := 4) (by omega) hapos (by omega)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma halfImage_has_low_divisor {A : Finset ℕ} {N b : ℕ} (hb : b ∈ halfImage A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ b := by
  obtain ⟨a, haA, haN, rfl⟩ := halfImage_mem_iff.mp hb
  exact ⟨a, haA, haN, dvd_scaledMove 0 N 4 a⟩

noncomputable def halfImageUpper (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (halfImage A N).filter fun b ↦ N < 3 * b

noncomputable def halfImageMovable (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (halfImage A N).filter fun b ↦ 3 * b ≤ N ∧ b % 4 = 2

noncomputable def halfImageLeftover (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (halfImage A N).filter fun b ↦ 3 * b ≤ N ∧ b % 4 ≠ 2

noncomputable def modifiedHalfImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  halfImageUpper A N ∪
    (halfImageMovable A N).image (fun b ↦ 3 * (b / 2))

@[simp] lemma mem_halfImageUpper {A : Finset ℕ} {N b : ℕ} :
    b ∈ halfImageUpper A N ↔ b ∈ halfImage A N ∧ N < 3 * b := by
  simp [halfImageUpper]

@[simp] lemma mem_halfImageMovable {A : Finset ℕ} {N b : ℕ} :
    b ∈ halfImageMovable A N ↔
      b ∈ halfImage A N ∧ 3 * b ≤ N ∧ b % 4 = 2 := by
  simp [halfImageMovable]

@[simp] lemma mem_halfImageLeftover {A : Finset ℕ} {N b : ℕ} :
    b ∈ halfImageLeftover A N ↔
      b ∈ halfImage A N ∧ 3 * b ≤ N ∧ b % 4 ≠ 2 := by
  simp [halfImageLeftover]

lemma halfImage_partition_card (A : Finset ℕ) (N : ℕ) :
    (halfImageUpper A N).card + (halfImageMovable A N).card +
      (halfImageLeftover A N).card = (halfImage A N).card := by
  let U := halfImageUpper A N
  let M := halfImageMovable A N
  let L := halfImageLeftover A N
  let B := halfImage A N
  have hUM : Disjoint U M := by
    rw [Finset.disjoint_left]
    intro b hbU hbM
    have hu := mem_halfImageUpper.mp hbU
    have hm := mem_halfImageMovable.mp hbM
    omega
  have hUL : Disjoint U L := by
    rw [Finset.disjoint_left]
    intro b hbU hbL
    have hu := mem_halfImageUpper.mp hbU
    have hl := mem_halfImageLeftover.mp hbL
    omega
  have hML : Disjoint M L := by
    rw [Finset.disjoint_left]
    intro b hbM hbL
    have hm := mem_halfImageMovable.mp hbM
    have hl := mem_halfImageLeftover.mp hbL
    exact hl.2.2 hm.2.2
  have hunion : U ∪ M ∪ L = B := by
    ext b
    simp only [U, M, L, B, Finset.mem_union, mem_halfImageUpper,
      mem_halfImageMovable, mem_halfImageLeftover]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hb
      by_cases h3 : N < 3 * b
      · exact Or.inl (Or.inl ⟨hb, h3⟩)
      · by_cases hm : b % 4 = 2
        · exact Or.inl (Or.inr ⟨hb, by omega, hm⟩)
        · exact Or.inr ⟨hb, by omega, hm⟩
  have hUML : Disjoint (U ∪ M) L := by
    rw [Finset.disjoint_left]
    intro b hb hbL
    simp only [Finset.mem_union] at hb
    rcases hb with hbU | hbM
    · exact (Finset.disjoint_left.mp hUL) hbU hbL
    · exact (Finset.disjoint_left.mp hML) hbM hbL
  change U.card + M.card + L.card = B.card
  rw [← hunion, card_union_of_disjoint hUML, card_union_of_disjoint hUM]

lemma card_movable_image (A : Finset ℕ) (N : ℕ) :
    ((halfImageMovable A N).image (fun b ↦ 3 * (b / 2))).card =
      (halfImageMovable A N).card := by
  apply card_image_iff.mpr
  intro x hx y hy hxy
  change x ∈ halfImageMovable A N at hx
  change y ∈ halfImageMovable A N at hy
  have hxmod := (mem_halfImageMovable.mp hx).2.2
  have hymod := (mem_halfImageMovable.mp hy).2.2
  change 3 * (x / 2) = 3 * (y / 2) at hxy
  have hdiv : x / 2 = y / 2 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
  have hx2 : 2 ∣ x := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hy2 : 2 ∣ y := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
  have hyeq : 2 * (y / 2) = y := Nat.mul_div_cancel' hy2
  omega

lemma scaledMove_eq_self_of_odd {T q a : ℕ} (hodd : scaledMove 0 T q a % 2 = 1) :
    scaledMove 0 T q a = a := by
  by_cases he : scaledWindowExp 0 T q a = 0
  · simp [scaledMove, he]
  · have hepos : 0 < scaledWindowExp 0 T q a := Nat.pos_of_ne_zero he
    have hpow : 2 ∣ 2 ^ scaledWindowExp 0 T q a := by
      exact dvd_pow_self 2 (Nat.ne_of_gt hepos)
    have hdiv : 2 ∣ scaledMove 0 T q a := by
      rw [scaledMove]
      exact dvd_mul_of_dvd_left hpow a
    rw [Nat.dvd_iff_mod_eq_zero] at hdiv
    omega

lemma modifiedHalfImage_disjoint {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (halfImageUpper A N)
      ((halfImageMovable A N).image fun b ↦ 3 * (b / 2)) := by
  rw [Finset.disjoint_left]
  intro z hzU hzM
  simp only [Finset.mem_image] at hzM
  obtain ⟨b, hbM, rfl⟩ := hzM
  have hbM' := mem_halfImageMovable.mp hbM
  obtain ⟨a, haA, haN, hab⟩ := halfImage_has_low_divisor hbM'.1
  have hbmod : b % 4 = 2 := hbM'.2.2
  have hbdiv2 : 2 ∣ b := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have htwice : 2 * (3 * (b / 2)) = 3 * b := by
    have hb : 2 * (b / 2) = b := Nat.mul_div_cancel' hbdiv2
    nlinarith
  obtain ⟨a', ha'A, ha'N, ha'z⟩ := halfImage_mem_iff.mp
    (mem_halfImageUpper.mp hzU).1
  have hzodd : (3 * (b / 2)) % 2 = 1 := by
    have hb4 : b / 2 % 2 = 1 := by omega
    omega
  have ha'odd : scaledMove 0 N 4 a' % 2 = 1 := by rw [ha'z]; exact hzodd
  have ha'eq : scaledMove 0 N 4 a' = a' := scaledMove_eq_self_of_odd ha'odd
  have hza' : 3 * (b / 2) = a' := by omega
  have hapos := hP.pos_of_mem hsub haA
  have ha'pos := hP.pos_of_mem hsub ha'A
  have haa' : a < a' := by
    have hab_le : a ≤ b := Nat.le_of_dvd (by omega) hab
    by_contra hnot
    have : a' ≤ a := by omega
    have hbound : 3 * b ≤ 2 * a := by omega
    have : b ≤ a := by nlinarith
    omega
  apply hP.not_dvd_two_mul haA ha'A haa'
  have hdiv3 : a ∣ 3 * b := hab.mul_left 3
  rw [← htwice, hza'] at hdiv3
  exact hdiv3

lemma modifiedHalfImage_card (A : Finset ℕ) (N : ℕ)
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (modifiedHalfImage A N).card =
      (halfImageUpper A N).card + (halfImageMovable A N).card := by
  rw [modifiedHalfImage, card_union_of_disjoint (modifiedHalfImage_disjoint hP hsub),
    card_movable_image]

lemma modifiedHalfImage_subset_window {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    modifiedHalfImage A N ⊆ Icc (N / 3 + 1) (N / 2) := by
  intro z hz
  simp only [modifiedHalfImage, Finset.mem_union] at hz
  rcases hz with hzU | hzM
  · have hz' := mem_halfImageUpper.mp hzU
    have hzI := mem_Icc.mp (halfImage_subset_window hP hsub hz'.1)
    exact mem_Icc.mpr ⟨by omega, hzI.2⟩
  · simp only [Finset.mem_image] at hzM
    obtain ⟨b, hb, rfl⟩ := hzM
    have hb' := mem_halfImageMovable.mp hb
    have hbI := mem_Icc.mp (halfImage_subset_window hP hsub hb'.1)
    have hbdiv : 2 ∣ b := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    have hbeq : 2 * (b / 2) = b := Nat.mul_div_cancel' hbdiv
    exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma halfImageLeftover_bound {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    16 * (halfImageLeftover A N).card ≤ N + 48 := by
  let L := halfImageLeftover A N
  let F (r : ZMod 4) := zmodFiber L r
  have hLI : L ⊆ Icc (N / 4 + 1) (N / 3) := by
    intro b hb
    have hb' := mem_halfImageLeftover.mp hb
    have hbI := mem_Icc.mp (halfImage_subset_window hP hsub hb'.1)
    exact mem_Icc.mpr ⟨hbI.1, by omega⟩
  have hFcap (r : ZMod 4) :
      4 * (F r).card ≤ (N / 3 + 4) - (N / 4 + 1) := by
    apply mul_card_fixed_zmod_le r
    · exact (filter_subset _ _).trans hLI
    · intro b hb
      exact (mem_zmodFiber.mp hb).2
  have hsum : ∑ r : ZMod 4, (F r).card = L.card := sum_card_zmodFiber L 4
  have hF2 : (F (2 : ZMod 4)).card = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    have hbF := mem_zmodFiber.mp hb
    have hbL := mem_halfImageLeftover.mp hbF.1
    have hm : b % 4 = 2 := by
      exact (ZMod.natCast_eq_natCast_iff b 2 4).mp hbF.2
    exact hbL.2.2 hm
  have hsumErase :
      (∑ r : ZMod 4, 4 * (F r).card) =
        ∑ r ∈ (Finset.univ.erase (2 : ZMod 4)), 4 * (F r).card := by
    have he := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod 4)))
      (f := fun r ↦ 4 * (F r).card) (Finset.mem_univ (2 : ZMod 4))
    rw [hF2] at he
    simpa using he.symm
  have heraseCard : (Finset.univ.erase (2 : ZMod 4)).card = 3 := by
    simp [ZMod.card]
  calc
    16 * L.card = 4 * (∑ r : ZMod 4, 4 * (F r).card) := by
      rw [← Finset.mul_sum, hsum]
      ring
    _ = 4 * (∑ r ∈ (Finset.univ.erase (2 : ZMod 4)), 4 * (F r).card) := by
      rw [hsumErase]
    _ ≤ 4 * (∑ _r ∈ (Finset.univ.erase (2 : ZMod 4)),
        ((N / 3 + 4) - (N / 4 + 1))) := by
      gcongr with r hr
      exact hFcap r
    _ = 12 * ((N / 3 + 4) - (N / 4 + 1)) := by
      rw [Finset.sum_const, heraseCard]
      simp
      ring
    _ ≤ N + 48 := by omega

lemma halfImage_card_le_modified_add {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    16 * (halfImage A N).card ≤ 16 * (modifiedHalfImage A N).card + N + 48 := by
  have hp := halfImage_partition_card A N
  have hz := modifiedHalfImage_card A N hP hsub
  have hl := halfImageLeftover_bound hP hsub
  omega

/-! ### The middle-sixth reserve -/

/-- One ordinary residue class modulo four. -/
def modFourPart (H : Finset ℕ) (r : ℕ) : Finset ℕ :=
  H.filter fun x ↦ x % 4 = r % 4

@[simp] lemma mem_modFourPart {H : Finset ℕ} {r x : ℕ} :
    x ∈ modFourPart H r ↔ x ∈ H ∧ x % 4 = r % 4 := by
  simp [modFourPart]

/-- The odd part is the disjoint union of the classes `1` and `3` modulo
four. -/
lemma card_modFour_one_add_three (H : Finset ℕ) :
    (modFourPart H 1).card + (modFourPart H 3).card =
      (parityPart H 1).card := by
  have hdisj : Disjoint (modFourPart H 1) (modFourPart H 3) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx3
    have h1 := (mem_modFourPart.mp hx1).2
    have h3 := (mem_modFourPart.mp hx3).2
    omega
  have hunion : modFourPart H 1 ∪ modFourPart H 3 = parityPart H 1 := by
    ext x
    simp only [Finset.mem_union, mem_modFourPart, mem_parityPart]
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, by omega⟩
      · exact ⟨hx.1, by omega⟩
    · intro hx
      have hmod : x % 4 < 4 := Nat.mod_lt _ (by omega)
      have hpar : x % 4 % 2 = 1 := by
        rw [Nat.mod_mod_of_dvd x (by omega : 2 ∣ 4)]
        exact hx.2
      interval_cases x % 4 <;> simp_all
  rw [← card_union_of_disjoint hdisj, hunion]

/-- Four times every member of the modified half image is a multiple of
an element of `A` lying in the lower half. -/
lemma modifiedHalfImage_has_low_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ modifiedHalfImage A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ 4 * z := by
  simp only [modifiedHalfImage, Finset.mem_union] at hz
  rcases hz with hzU | hzM
  · obtain ⟨a, ha, haN, haz⟩ :=
      halfImage_has_low_divisor (mem_halfImageUpper.mp hzU).1
    exact ⟨a, ha, haN, haz.mul_left 4⟩
  · simp only [Finset.mem_image] at hzM
    obtain ⟨b, hb, rfl⟩ := hzM
    obtain ⟨a, ha, haN, hab⟩ :=
      halfImage_has_low_divisor (mem_halfImageMovable.mp hb).1
    have hbmod := (mem_halfImageMovable.mp hb).2.2
    have hbdiv : 2 ∣ b := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    have hbeq : 2 * (b / 2) = b := Nat.mul_div_cancel' hbdiv
    refine ⟨a, ha, haN, ?_⟩
    have h6 : a ∣ 6 * b := hab.mul_left 6
    convert h6 using 1
    all_goals omega

/-- The divisible-by-four sums in the top-third self-sum. -/
def highFourSums (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  zmodFiber (highThird A N + highThird A N) (0 : ZMod 4)

/-- Bedert's packing inequality for the modified half image. -/
lemma modifiedHalfImage_pack {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    4 * ((modifiedHalfImage A N).card + (highFourSums A N).card) ≤
      2 * N + 4 - (4 * N / 3 + 1) := by
  let Z := modifiedHalfImage A N
  let H := highThird A N
  let S := highFourSums A N
  let U := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 4)
  have hB : ∀ z ∈ Z, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * z := by
    intro z hz
    obtain ⟨a, ha, haN, hadiv⟩ := modifiedHalfImage_has_low_divisor hz
    exact ⟨a, ha, by omega, hadiv⟩
  have hH : ∀ x ∈ H, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hSsum : S ⊆ H + H := filter_subset _ _
  have hZU : Z.image (fun z ↦ 4 * z) ⊆ U := by
    intro w hw
    simp only [Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hzI := mem_Icc.mp (modifiedHalfImage_subset_window hP hsub hz)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨z, rfl⟩
  have hsumI : H + H ⊆ Icc (4 * N / 3 + 1) (2 * N) := by
    intro w hw
    simp only [Finset.mem_add] at hw
    obtain ⟨x, hx, y, hy, rfl⟩ := hw
    have hx' := mem_highThird.mp hx
    have hy' := mem_highThird.mp hy
    have hxN := (mem_Icc.mp (hsub hx'.1)).2
    have hyN := (mem_Icc.mp (hsub hy'.1)).2
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hSU : S ⊆ U := by
    intro w hw
    have hw' := mem_zmodFiber.mp hw
    exact mem_zmodFiber.mpr ⟨hsumI hw'.1, hw'.2⟩
  have hpack := packing (k := 4) (t := N / 2) (by omega) hP hB hH hSsum hZU hSU
  have hUI : U ⊆ Icc (4 * N / 3 + 1) (2 * N) := filter_subset _ _
  have hUres : ∀ x ∈ U, (x : ZMod 4) = 0 := by
    intro x hx
    exact (mem_zmodFiber.mp hx).2
  have hcap := mul_card_fixed_zmod_le (0 : ZMod 4) hUI hUres
  change Z.card + S.card ≤ U.card at hpack
  change 4 * U.card ≤ (2 * N + 4) - (4 * N / 3 + 1) at hcap
  change 4 * (Z.card + S.card) ≤ _
  omega

/-- Doubling the even part of the top third injects it into the
divisible-by-four part of the top-third sumset. -/
lemma card_high_even_le_fourSums (A : Finset ℕ) (N : ℕ) :
    (parityPart (highThird A N) 0).card ≤ (highFourSums A N).card := by
  let E := parityPart (highThird A N) 0
  let S := highFourSums A N
  have himage : E.image (fun x ↦ 2 * x) ⊆ S := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hx' := mem_parityPart.mp hx
    apply mem_zmodFiber.mpr
    constructor
    · simpa [two_mul] using Finset.add_mem_add hx'.1 hx'.1
    · rw [ZMod.natCast_eq_zero_iff]
      have heven : 2 ∣ x := by rw [Nat.dvd_iff_mod_eq_zero]; simpa using hx'.2
      obtain ⟨k, rfl⟩ := heven
      exact ⟨k, by ring⟩
  have hcard : (E.image (fun x ↦ 2 * x)).card = E.card := by
    rw [Finset.card_image_of_injective]
    intro x y hxy
    change 2 * x = 2 * y at hxy
    omega
  rw [← hcard]
  exact card_le_card himage

/-- When both odd classes occur, their cross-sum supplies all but one of
the odd elements' contribution to the divisible-by-four sumset. -/
lemma card_high_odd_le_fourSums_add_one {A : Finset ℕ} {N : ℕ}
    (h1 : (modFourPart (highThird A N) 1).Nonempty)
    (h3 : (modFourPart (highThird A N) 3).Nonempty) :
    (parityPart (highThird A N) 1).card ≤
      (highFourSums A N).card + 1 := by
  let H1 := modFourPart (highThird A N) 1
  let H3 := modFourPart (highThird A N) 3
  let S := highFourSums A N
  have hadd : H1 + H3 ⊆ S := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_modFourPart.mp hx
    have hy' := mem_modFourPart.mp hy
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hx'.1 hy'.1
    · rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
        Nat.add_mod, hx'.2, hy'.2]
  have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd h1 h3
  have hsubcard := card_le_card hadd
  have hpart := card_modFour_one_add_three (highThird A N)
  change H1.card + H3.card - 1 ≤ (H1 + H3).card at hcd
  change H1.card + H3.card = (parityPart (highThird A N) 1).card at hpart
  change (H1 + H3).card ≤ S.card at hsubcard
  calc
    (parityPart (highThird A N) 1).card = H1.card + H3.card := hpart.symm
    _ ≤ S.card + 1 := by omega

/-- If one odd residue modulo four is absent from the top third, the whole
odd part occupies the other residue and has the trivial interval bound. -/
lemma card_high_odd_of_modFour_empty {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N)
    (hempty : ¬ (modFourPart (highThird A N) 1).Nonempty ∨
      ¬ (modFourPart (highThird A N) 3).Nonempty) :
    12 * (parityPart (highThird A N) 1).card ≤ N + 12 := by
  let H := highThird A N
  let O := parityPart H 1
  have hHI : H ⊆ Icc (2 * N / 3 + 1) N := highThird_subset_interval hsub
  rcases hempty with h1 | h3
  · have hOeq : O = modFourPart H 3 := by
      ext x
      simp only [O, mem_parityPart, mem_modFourPart]
      constructor
      · intro hx
        have hx4 : x % 4 < 4 := Nat.mod_lt _ (by omega)
        have hxpar : x % 4 % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd x (by omega : 2 ∣ 4)]
          exact hx.2
        have hxne : x % 4 ≠ 1 := by
          intro heq
          apply h1
          exact ⟨x, mem_modFourPart.mpr ⟨hx.1, by simpa using heq⟩⟩
        interval_cases x % 4 <;> simp_all
      · intro hx
        exact ⟨hx.1, by omega⟩
    have hres : ∀ x ∈ modFourPart H 3, (x : ZMod 4) = (3 : ZMod 4) := by
      intro x hx
      apply (ZMod.natCast_eq_natCast_iff' x 3 4).mpr
      simpa using (mem_modFourPart.mp hx).2
    have hcap := mul_card_fixed_zmod_le (3 : ZMod 4)
      ((filter_subset _ _).trans hHI) hres
    change 4 * (modFourPart H 3).card ≤ N + 4 - (2 * N / 3 + 1) at hcap
    change 12 * O.card ≤ N + 12
    rw [hOeq]
    omega
  · have hOeq : O = modFourPart H 1 := by
      ext x
      simp only [O, mem_parityPart, mem_modFourPart]
      constructor
      · intro hx
        have hx4 : x % 4 < 4 := Nat.mod_lt _ (by omega)
        have hxpar : x % 4 % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd x (by omega : 2 ∣ 4)]
          exact hx.2
        have hxne : x % 4 ≠ 3 := by
          intro heq
          apply h3
          exact ⟨x, mem_modFourPart.mpr ⟨hx.1, by simpa using heq⟩⟩
        interval_cases x % 4 <;> simp_all
      · intro hx
        exact ⟨hx.1, by omega⟩
    have hres : ∀ x ∈ modFourPart H 1, (x : ZMod 4) = (1 : ZMod 4) := by
      intro x hx
      apply (ZMod.natCast_eq_natCast_iff' x 1 4).mpr
      simpa using (mem_modFourPart.mp hx).2
    have hcap := mul_card_fixed_zmod_le (1 : ZMod 4)
      ((filter_subset _ _).trans hHI) hres
    change 4 * (modFourPart H 1).card ≤ N + 4 - (2 * N / 3 + 1) at hcap
    change 12 * O.card ≤ N + 12
    rw [hOeq]
    omega

/-- Equation (24) in the source, with floors absorbed into the explicit
constant. -/
lemma high_add_modifiedHalfImage_le {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hcase3 : 6 * (highThird A N).card < N + 144) :
    (highThird A N).card + (modifiedHalfImage A N).card ≤ N / 4 + 15 := by
  let H := highThird A N
  let Z := modifiedHalfImage A N
  let S := highFourSums A N
  let E := parityPart H 0
  let O := parityPart H 1
  have hpart := card_parity_parts H
  have hpack := modifiedHalfImage_pack hP hsub
  have heven := card_high_even_le_fourSums A N
  change 6 * H.card < N + 144 at hcase3
  change E.card + O.card = H.card at hpart
  change 4 * (Z.card + S.card) ≤ 2 * N + 4 - (4 * N / 3 + 1) at hpack
  change E.card ≤ S.card at heven
  have hpack12 : 12 * (Z.card + S.card) ≤ 2 * N + 11 := by
    omega
  by_cases h1 : (modFourPart H 1).Nonempty
  · by_cases h3 : (modFourPart H 3).Nonempty
    · have hodd := card_high_odd_le_fourSums_add_one h1 h3
      change O.card ≤ S.card + 1 at hodd
      change H.card + Z.card ≤ N / 4 + 15
      have htotal : 12 * (H.card + Z.card) ≤ 3 * N + 160 := by omega
      omega
    · have hodd := card_high_odd_of_modFour_empty hsub (Or.inr h3)
      change 12 * O.card ≤ N + 12 at hodd
      change H.card + Z.card ≤ N / 4 + 15
      omega
  · have hodd := card_high_odd_of_modFour_empty hsub (Or.inl h1)
    change 12 * O.card ≤ N + 12 at hodd
    change H.card + Z.card ≤ N / 4 + 15
    omega

/-- The lower and upper halves partition `A`. -/
lemma card_lowHalf_add_upperHalf {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    (lowHalf A N).card + (upperHalf A N).card = A.card := by
  have hdisj : Disjoint (lowHalf A N) (upperHalf A N) := by
    rw [Finset.disjoint_left]
    intro x hxL hxU
    have hl := mem_lowHalf.mp hxL
    have hu := mem_upperHalf.mp hxU
    omega
  have hunion : lowHalf A N ∪ upperHalf A N = A := by
    ext x
    simp only [Finset.mem_union, mem_lowHalf, mem_upperHalf]
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      have hxN := (mem_Icc.mp (hsub hx)).2
      by_cases hlow : 2 * x ≤ N
      · exact Or.inl ⟨hx, hlow⟩
      · exact Or.inr ⟨hx, by omega, hxN⟩
  rw [← card_union_of_disjoint hdisj, hunion]

/-- Bedert's middle-sixth reserve.  The constant `832` records all floor
losses from the preceding integer estimates. -/
lemma middleSixth_reserve {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hfail : ¬ StrongBound C N A) :
    N ≤ 48 * (middleSixth A N).card + 832 := by
  let X := lowHalf A N
  let Y := middleSixth A N
  let H := highThird A N
  let Z := modifiedHalfImage A N
  have hXV := card_lowHalf_add_upperHalf hsub
  have hYH := card_middleSixth_add_highThird hsub
  have hBX := halfImage_card hP hsub
  have hBZ := halfImage_card_le_modified_add hP hsub
  have hHZ := high_add_modifiedHalfImage_le hP hsub hcase3
  change X.card + (upperHalf A N).card = A.card at hXV
  change Y.card + H.card = (upperHalf A N).card at hYH
  change (halfImage A N).card = X.card at hBX
  change 16 * (halfImage A N).card ≤ 16 * Z.card + N + 48 at hBZ
  change H.card + Z.card ≤ N / 4 + 15 at hHZ
  have houtside : 16 * (X.card + H.card) ≤ 5 * N + 288 := by omega
  have hpartition : X.card + Y.card + H.card = A.card := by omega
  have hnotceil : N + 2 < 3 * A.card := by
    by_contra h
    apply hfail
    exact Or.inl (by omega)
  change N ≤ 48 * Y.card + 832
  omega

/-- The growth branch in Case 3.2.  A large zero residue class creates
enough divisible-by-three sums for the basic quotient packing to finish
the strengthened induction. -/
lemma caseThree_zero_growth {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hC : 1000 ≤ C)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (hgrowth : 3 * (upperHalfResidue A N 0).card ≤
      (upperHalfResidue A N 0 + upperHalfResidue A N 0).card + 3)
    (hfail : ¬ StrongBound C N A) : False := by
  let V := upperHalf A N
  let V0 := upperHalfResidue A N 0
  let R := zmodFiber (V + V) (0 : ZMod 3)
  let Q := thirdSumQuotient A N
  let B := centralImage A N
  let Y := middleSixth A N
  let H := highThird A N
  have h00 : V0 + V0 ⊆ R := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hx'.1 hy'.1
    · have hxZ : (x : ZMod 3) = 0 := by
        apply (ZMod.natCast_eq_zero_iff x 3).mpr
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using hx'.2
      have hyZ : (y : ZMod 3) = 0 := by
        apply (ZMod.natCast_eq_zero_iff y 3).mpr
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using hy'.2
      push_cast
      rw [hxZ, hyZ]
      rfl
  have hRlower : 3 * V0.card ≤ R.card + 3 := by
    change 3 * V0.card ≤ (V0 + V0).card + 3 at hgrowth
    have hc := card_le_card h00
    omega
  have hQcard := thirdSumQuotient_card A N
  change Q.card = R.card at hQcard
  change V.card ≤ 3 * V0.card at hdom
  have hVQ : V.card ≤ Q.card + 3 := by omega
  have hpack := caseThree_basic_packing hP hsub
  change B.card + Q.card ≤ (Icc (N / 3 + 1) (2 * N / 3)).card at hpack
  have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
    simp
    omega
  have hBH := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hBH
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  have hVcard : V.card = Y.card + H.card := hYH.symm
  have hAY : 3 * (A.card + Y.card) ≤ N + 11 := by omega
  have hreserve := middleSixth_reserve hP hsub hcase3 hfail
  change N ≤ 48 * Y.card + 832 at hreserve
  apply hfail
  right
  omega

/-- The same zero-residue growth calculation, retaining only the absolute
additive estimate needed by the final coarse induction. -/
lemma caseThree_zero_growth_coarse {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (hgrowth : 3 * (upperHalfResidue A N 0).card ≤
      (upperHalfResidue A N 0 + upperHalfResidue A N 0).card + 3) :
    3 * A.card ≤ N + 11 := by
  let V := upperHalf A N
  let V0 := upperHalfResidue A N 0
  let R := zmodFiber (V + V) (0 : ZMod 3)
  let Q := thirdSumQuotient A N
  let B := centralImage A N
  let Y := middleSixth A N
  let H := highThird A N
  have h00 : V0 + V0 ⊆ R := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hx'.1 hy'.1
    · have hxZ : (x : ZMod 3) = 0 := by
        apply (ZMod.natCast_eq_zero_iff x 3).mpr
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using hx'.2
      have hyZ : (y : ZMod 3) = 0 := by
        apply (ZMod.natCast_eq_zero_iff y 3).mpr
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using hy'.2
      push_cast
      rw [hxZ, hyZ]
      rfl
  have hRlower : 3 * V0.card ≤ R.card + 3 := by
    change 3 * V0.card ≤ (V0 + V0).card + 3 at hgrowth
    have hc := card_le_card h00
    omega
  have hQcard := thirdSumQuotient_card A N
  change Q.card = R.card at hQcard
  change V.card ≤ 3 * V0.card at hdom
  have hVQ : V.card ≤ Q.card + 3 := by omega
  have hpack := caseThree_basic_packing hP hsub
  change B.card + Q.card ≤ (Icc (N / 3 + 1) (2 * N / 3)).card at hpack
  have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
    simp
    omega
  have hBH := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hBH
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  omega

/-- In the nonzero-residue branch, sumset growth finishes as soon as the
two residue classes (including the smaller one once more) cover the top
third. -/
lemma caseThree_nonzero_growth {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hgrowth :
      (upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card +
        min (upperHalfResidue A N 1).card (upperHalfResidue A N 2).card ≤
          (upperHalfResidue A N 1 + upperHalfResidue A N 2).card + 3)
    (hcover : (highThird A N).card + 3 ≤
      (upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card +
        min (upperHalfResidue A N 1).card (upperHalfResidue A N 2).card) :
    3 * A.card ≤ N + 2 := by
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let R := zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)
  let Q := thirdSumQuotient A N
  let B := centralImage A N
  let H := highThird A N
  have h12 : V₁ + V₂ ⊆ R := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hx'.1 hy'.1
    · have hxZ : (x : ZMod 3) = 1 := by
        apply (ZMod.natCast_eq_natCast_iff x 1 3).mpr
        change x % 3 = 1 % 3
        simpa using hx'.2
      have hyZ : (y : ZMod 3) = 2 := by
        apply (ZMod.natCast_eq_natCast_iff y 2 3).mpr
        change y % 3 = 2 % 3
        simpa using hy'.2
      push_cast
      rw [hxZ, hyZ]
      decide
  have hRcard : (V₁ + V₂).card ≤ R.card := card_le_card h12
  have hQcard := thirdSumQuotient_card A N
  change Q.card = R.card at hQcard
  change V₁.card + V₂.card + min V₁.card V₂.card ≤
    (V₁ + V₂).card + 3 at hgrowth
  change H.card + 3 ≤
    V₁.card + V₂.card + min V₁.card V₂.card at hcover
  have hHQ : H.card ≤ Q.card := by omega
  have hpack := caseThree_basic_packing hP hsub
  change B.card + Q.card ≤ (Icc (N / 3 + 1) (2 * N / 3)).card at hpack
  have hBH := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hBH
  have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
    simp
    omega
  omega

/-- A dense subset of the upper half lying in one class modulo three has
the same residue-rich self-sums as a dense subset of a compressed interval.
The coprimality assumption lets a `q`-fiber and the fixed mod-three class
combine into one class modulo `3q`. -/
lemma dense_residue_upperHalf_fixed_three {U : Finset ℕ} {N q r : ℕ}
    (hq : 0 < q) (hcop : Nat.Coprime 3 q)
    (hU : U ⊆ Icc (N / 2 + 1) N)
    (hthree : ∀ x ∈ U, x % 3 = r % 3)
    (hdense : N / 6 + q + 1 ≤ 2 * U.card) (a : ZMod q) :
    2 * U.card ≤ q * ((zmodFiber (U + U) a).card + 1) := by
  apply dense_residue hq a (D := N / 6 + q + 1) ?_ hdense
  intro i
  let F := zmodFiber U i
  by_cases hF : F.Nonempty
  · obtain ⟨x, hxF⟩ := hF
    have hx := mem_zmodFiber.mp hxF
    have hFI : F ⊆ Icc (N / 2 + 1) N := (filter_subset _ _).trans hU
    have hres : ∀ y ∈ F, (y : ZMod (3 * q)) = (x : ZMod (3 * q)) := by
      intro y hyF
      have hy := mem_zmodFiber.mp hyF
      apply (ZMod.natCast_eq_natCast_iff y x (3 * q)).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      constructor
      · change y % 3 = x % 3
        rw [hthree y hy.1, hthree x hx.1]
      · exact (ZMod.natCast_eq_natCast_iff y x q).mp (hy.2.trans hx.2.symm)
    have hcap := mul_card_fixed_zmod_le (x : ZMod (3 * q)) hFI hres
    change 3 * q * F.card ≤ (N + 3 * q) - (N / 2 + 1) at hcap
    change q * F.card < N / 6 + q + 1
    have hL : N / 2 + 1 ≤ N + 3 * q := by omega
    have hraw := (Nat.le_sub_iff_add_le hL).mp hcap
    by_contra hn
    have hlower : N / 6 + q + 1 ≤ q * F.card := by omega
    have hlower3 := Nat.mul_le_mul_left 3 hlower
    have heq : 3 * (q * F.card) = 3 * q * F.card := by ring
    rw [heq] at hlower3
    omega
  · have hFe : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    simp [F, hFe]

/-- The power-of-two half-window image of lower-half elements not divisible
by three. -/
noncomputable def lowNonthreeImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ((lowHalf A N).filter fun x ↦ x % 3 ≠ 0).image (scaledMove 0 N 4)

noncomputable def lowNonthreeImagePart (A : Finset ℕ) (N r : ℕ) : Finset ℕ :=
  (lowNonthreeImage A N).filter fun x ↦ x % 3 = r % 3

@[simp] lemma mem_lowNonthreeImagePart {A : Finset ℕ} {N r x : ℕ} :
    x ∈ lowNonthreeImagePart A N r ↔
      x ∈ lowNonthreeImage A N ∧ x % 3 = r % 3 := by
  simp [lowNonthreeImagePart]

lemma card_lowNonthreeImage {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (lowNonthreeImage A N).card =
      ((lowHalf A N).filter fun x ↦ x % 3 ≠ 0).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono ((filter_subset _ _).trans (filter_subset _ _)))
  intro x hx
  exact hP.pos_of_mem hsub ((mem_lowHalf.mp (mem_filter.mp hx).1).1)

lemma lowNonthreeImage_subset_halfImage (A : Finset ℕ) (N : ℕ) :
    lowNonthreeImage A N ⊆ halfImage A N := by
  intro z hz
  simp only [lowNonthreeImage, halfImage, mem_image] at hz ⊢
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x, (mem_filter.mp hx).1, rfl⟩

lemma lowNonthreeImage_not_dvd_three {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ lowNonthreeImage A N) : ¬ 3 ∣ z := by
  simp only [lowNonthreeImage, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hx3 : ¬ 3 ∣ x := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact (mem_filter.mp hx).2
  intro hd
  rw [scaledMove] at hd
  rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp hd with hp | hxdiv
  · have : 3 ∣ 2 := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hp
    norm_num at this
  · exact hx3 hxdiv

lemma card_lowNonthreeImage_parts {A : Finset ℕ} {N : ℕ} :
    (lowNonthreeImagePart A N 1).card +
      (lowNonthreeImagePart A N 2).card = (lowNonthreeImage A N).card := by
  let C := lowNonthreeImage A N
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  have hdisj : Disjoint C₁ C₂ := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have h1 := (mem_lowNonthreeImagePart.mp hz1).2
    have h2 := (mem_lowNonthreeImagePart.mp hz2).2
    omega
  have hunion : C₁ ∪ C₂ = C := by
    ext z
    simp only [C₁, C₂, C, mem_union, mem_lowNonthreeImagePart]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      have hmod := Nat.mod_lt z (by omega : 0 < 3)
      have hn := lowNonthreeImage_not_dvd_three hz
      rw [Nat.dvd_iff_mod_eq_zero] at hn
      interval_cases z % 3 <;> simp_all
  rw [← card_union_of_disjoint hdisj, hunion]

lemma lowNonthreeImage_subset_interval {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    lowNonthreeImage A N ⊆ Icc (N / 4 + 1) (N / 2) :=
  (lowNonthreeImage_subset_halfImage A N).trans (halfImage_subset_window hP hsub)

/-- The modulus-four packing estimate used when one nonzero class modulo
three dominates the upper half. -/
lemma upperThreeClass_pack_four {A U B : Finset ℕ} {N r : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hU : U ⊆ upperHalf A N) (hthree : ∀ x ∈ U, x % 3 = r % 3)
    (hB : B ⊆ lowNonthreeImage A N)
    (hBthree : ∀ b ∈ B, b % 3 = (2 * r) % 3)
    (hdense : N / 6 + 5 ≤ 2 * U.card) :
    12 * B.card + 6 * U.card ≤ N + 24 := by
  let S := zmodFiber (U + U) (0 : ZMod 4)
  let e := 4 * ((2 * r) % 3)
  let W := zmodFiber (Icc (N + 1) (2 * N)) (e : ZMod 12)
  have hUI : U ⊆ Icc (N / 2 + 1) N := hU.trans (upperHalf_subset_interval hsub)
  have hd := dense_residue_upperHalf_fixed_three (q := 4) (r := r)
    (by omega) (by norm_num) hUI hthree hdense (0 : ZMod 4)
  have hBdiv : ∀ b ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * b := by
    intro b hb
    obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor
      (lowNonthreeImage_subset_halfImage A N (hB hb))
    exact ⟨a, ha, by omega, hab.mul_left 4⟩
  have hUH : ∀ x ∈ U, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_upperHalf.mp (hU hx)
    exact ⟨hx'.1, by omega⟩
  have hSsum : S ⊆ U + U := filter_subset _ _
  have hBW : B.image (fun b ↦ 4 * b) ⊆ W := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    have hbI := mem_Icc.mp (lowNonthreeImage_subset_interval hP hsub
      (hB hb))
    have hb3 := hBthree b hb
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (4 * b) e 12).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hSW : S ⊆ W := by
    intro z hz
    have hz' := mem_zmodFiber.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz'.1
    have hxI := mem_Icc.mp (hUI hx)
    have hyI := mem_Icc.mp (hUI hy)
    have hx3 := hthree x hx
    have hy3 := hthree y hy
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) e 12).mpr
      have h4 := (ZMod.natCast_eq_zero_iff (x + y) 4).mp hz'.2
      rw [Nat.dvd_iff_mod_eq_zero] at h4
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hp := packing (k := 4) (t := N / 2) (by omega) hP hBdiv hUH hSsum hBW hSW
  have hWI : W ⊆ Icc (N + 1) (2 * N) := filter_subset _ _
  have hWres : ∀ z ∈ W, (z : ZMod 12) = (e : ZMod 12) := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hcap := mul_card_fixed_zmod_le (e : ZMod 12) hWI hWres
  change 2 * U.card ≤ 4 * (S.card + 1) at hd
  change B.card + S.card ≤ W.card at hp
  change 12 * W.card ≤ (2 * N + 12) - (N + 1) at hcap
  omega

/-- The companion modulus-five packing estimate. -/
lemma upperThreeClass_pack_five {A U B : Finset ℕ} {N r : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hU : U ⊆ upperHalf A N) (hthree : ∀ x ∈ U, x % 3 = r % 3)
    (hB : B ⊆ lowNonthreeImage A N)
    (hBthree : ∀ b ∈ B, b % 3 = r % 3)
    (hdense : N / 6 + 6 ≤ 2 * U.card) :
    10 * B.card + 4 * U.card ≤ N + 30 := by
  let S := zmodFiber (U + U) (0 : ZMod 5)
  let e := 5 * (r % 3)
  let W := zmodFiber (Icc (N + 1) (5 * N / 2)) (e : ZMod 15)
  have hUI : U ⊆ Icc (N / 2 + 1) N := hU.trans (upperHalf_subset_interval hsub)
  have hd := dense_residue_upperHalf_fixed_three (q := 5) (r := r)
    (by omega) (by norm_num) hUI hthree hdense (0 : ZMod 5)
  have hBdiv : ∀ b ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 5 * b := by
    intro b hb
    obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor
      (lowNonthreeImage_subset_halfImage A N (hB hb))
    exact ⟨a, ha, by omega, hab.mul_left 5⟩
  have hUH : ∀ x ∈ U, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_upperHalf.mp (hU hx)
    exact ⟨hx'.1, by omega⟩
  have hSsum : S ⊆ U + U := filter_subset _ _
  have hBW : B.image (fun b ↦ 5 * b) ⊆ W := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    have hbI := mem_Icc.mp (lowNonthreeImage_subset_interval hP hsub
      (hB hb))
    have hb3 := hBthree b hb
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (5 * b) e 15).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 5)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hSW : S ⊆ W := by
    intro z hz
    have hz' := mem_zmodFiber.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz'.1
    have hxI := mem_Icc.mp (hUI hx)
    have hyI := mem_Icc.mp (hUI hy)
    have hx3 := hthree x hx
    have hy3 := hthree y hy
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) e 15).mpr
      have h5 := (ZMod.natCast_eq_zero_iff (x + y) 5).mp hz'.2
      rw [Nat.dvd_iff_mod_eq_zero] at h5
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 5)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hp := packing (k := 5) (t := N / 2) (by omega) hP hBdiv hUH hSsum hBW hSW
  have hWI : W ⊆ Icc (N + 1) (5 * N / 2) := filter_subset _ _
  have hWres : ∀ z ∈ W, (z : ZMod 15) = (e : ZMod 15) := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hcap := mul_card_fixed_zmod_le (e : ZMod 15) hWI hWres
  change 2 * U.card ≤ 5 * (S.card + 1) at hd
  change B.card + S.card ≤ W.card at hp
  change 15 * W.card ≤ (5 * N / 2 + 15) - (N + 1) at hcap
  omega

/-- If one nonzero residue class is absent in the nonzero-dominant branch,
the two coprime residue packings and induction on the multiples of three
give a linear saving. -/
lemma caseThree_nonzero_empty {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hempty : ¬ (upperHalfResidue A N 2).Nonempty)
    (hind : CoarseBound C (N / 3)
      ((divisibleInitial A N 3 1).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 1
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  have hV₂card : V₂.card = 0 := by
    exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hempty)
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  have hV₁dense4 : N / 6 + 5 ≤ 2 * V₁.card := by omega
  have hV₁dense5 : N / 6 + 6 ≤ 2 * V₁.card := by omega
  have hV₁sub : V₁ ⊆ V := filter_subset _ _
  have hV₁three : ∀ x ∈ V₁, x % 3 = 1 := by
    intro x hx
    have := (mem_upperHalfResidue.mp hx).2
    simpa using this
  have hp4 := upperThreeClass_pack_four (r := 1) hP hsub hV₁sub hV₁three
    (B := C₂) (fun _ hb ↦ (mem_lowNonthreeImagePart.mp hb).1)
    (fun _ hb ↦ by simpa using (mem_lowNonthreeImagePart.mp hb).2) hV₁dense4
  have hp5 := upperThreeClass_pack_five (r := 1) hP hsub hV₁sub hV₁three
    (B := C₁) (fun _ hb ↦ (mem_lowNonthreeImagePart.mp hb).1)
    (fun _ hb ↦ by simpa using (mem_lowNonthreeImagePart.mp hb).2) hV₁dense5
  change 12 * C₂.card + 6 * V₁.card ≤ N + 24 at hp4
  change 10 * C₁.card + 4 * V₁.card ≤ N + 30 at hp5
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    hV₁sub.trans (upperHalf_subset_interval hsub)
  have hV₁res : ∀ x ∈ V₁, (x : ZMod 3) = 1 := by
    intro x hx
    apply (ZMod.natCast_eq_natCast_iff' x 1 3).mpr
    simpa using hV₁three x hx
  have hV₁cap := mul_card_fixed_zmod_le (1 : ZMod 3) hV₁I hV₁res
  change 3 * V₁.card ≤ (N + 3) - (N / 2 + 1) at hV₁cap
  have hCparts := card_lowNonthreeImage_parts (A := A) (N := N)
  have hCcard := card_lowNonthreeImage hP hsub
  change C₁.card + C₂.card = (lowNonthreeImage A N).card at hCparts
  have hCcard' : (lowNonthreeImage A N).card = Lₙ.card := by
    simpa [Lₙ, L] using hCcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx0 hxn
      exact (mem_filter.mp hxn).2 (mem_filter.mp hx0).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases hmod : x % 3 = 0
        · exact Or.inl ⟨hx, hmod⟩
        · exact Or.inr ⟨hx, hmod⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxL.1, ?_, by have := (mem_Icc.mp (hsub hxL.1)).2; omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hx'.2
  have hV₀D : V₀ ⊆ D := by
    intro x hx
    have hx' := mem_upperHalfResidue.mp hx
    have hxV := mem_upperHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxV.1, ?_, by have := (mem_Icc.mp (hsub hxV.1)).2; omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa using hx'.2
  have hL₀V₀ : Disjoint L₀ V₀ := by
    rw [Finset.disjoint_left]
    intro x hxL hxV
    have hl := mem_lowHalf.mp (mem_filter.mp hxL).1
    have hv := mem_upperHalf.mp (mem_upperHalfResidue.mp hxV).1
    omega
  have hDcover : L₀.card + V₀.card ≤ D.card := by
    rw [← card_union_of_disjoint hL₀V₀]
    exact card_le_card (union_subset hL₀D hV₀D)
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  have hAcover : A.card ≤ D.card + C₁.card + C₂.card + V₁.card := by
    omega
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 1)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 3 + C at hDbound
  change 3 * A.card ≤ N + C
  omega

lemma caseThree_nonzero_empty_one {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hempty : ¬ (upperHalfResidue A N 1).Nonempty)
    (hind : CoarseBound C (N / 3)
      ((divisibleInitial A N 3 1).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 1
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  have hV₁card : V₁.card = 0 :=
    card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hempty)
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  have hV₂dense4 : N / 6 + 5 ≤ 2 * V₂.card := by omega
  have hV₂dense5 : N / 6 + 6 ≤ 2 * V₂.card := by omega
  have hV₂sub : V₂ ⊆ V := filter_subset _ _
  have hV₂three : ∀ x ∈ V₂, x % 3 = 2 % 3 := by
    intro x hx
    exact (mem_upperHalfResidue.mp hx).2
  have hp4 := upperThreeClass_pack_four (r := 2) hP hsub hV₂sub hV₂three
    (B := C₁) (fun _ hb ↦ (mem_lowNonthreeImagePart.mp hb).1)
    (fun _ hb ↦ by simpa using (mem_lowNonthreeImagePart.mp hb).2) hV₂dense4
  have hp5 := upperThreeClass_pack_five (r := 2) hP hsub hV₂sub hV₂three
    (B := C₂) (fun _ hb ↦ (mem_lowNonthreeImagePart.mp hb).1)
    (fun _ hb ↦ by simpa using (mem_lowNonthreeImagePart.mp hb).2) hV₂dense5
  change 12 * C₁.card + 6 * V₂.card ≤ N + 24 at hp4
  change 10 * C₂.card + 4 * V₂.card ≤ N + 30 at hp5
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    hV₂sub.trans (upperHalf_subset_interval hsub)
  have hV₂res : ∀ x ∈ V₂, (x : ZMod 3) = 2 := by
    intro x hx
    apply (ZMod.natCast_eq_natCast_iff' x 2 3).mpr
    exact hV₂three x hx
  have hV₂cap := mul_card_fixed_zmod_le (2 : ZMod 3) hV₂I hV₂res
  change 3 * V₂.card ≤ (N + 3) - (N / 2 + 1) at hV₂cap
  have hCparts := card_lowNonthreeImage_parts (A := A) (N := N)
  have hCcard := card_lowNonthreeImage hP hsub
  change C₁.card + C₂.card = (lowNonthreeImage A N).card at hCparts
  have hCcard' : (lowNonthreeImage A N).card = Lₙ.card := by
    simpa [Lₙ, L] using hCcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx0 hxn
      exact (mem_filter.mp hxn).2 (mem_filter.mp hx0).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases hmod : x % 3 = 0
        · exact Or.inl ⟨hx, hmod⟩
        · exact Or.inr ⟨hx, hmod⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxL.1, ?_, by have := (mem_Icc.mp (hsub hxL.1)).2; omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hx'.2
  have hV₀D : V₀ ⊆ D := by
    intro x hx
    have hx' := mem_upperHalfResidue.mp hx
    have hxV := mem_upperHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxV.1, ?_, by have := (mem_Icc.mp (hsub hxV.1)).2; omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa using hx'.2
  have hL₀V₀ : Disjoint L₀ V₀ := by
    rw [Finset.disjoint_left]
    intro x hxL hxV
    have hl := mem_lowHalf.mp (mem_filter.mp hxL).1
    have hv := mem_upperHalf.mp (mem_upperHalfResidue.mp hxV).1
    omega
  have hDcover : L₀.card + V₀.card ≤ D.card := by
    rw [← card_union_of_disjoint hL₀V₀]
    exact card_le_card (union_subset hL₀D hV₀D)
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  have hAcover : A.card ≤ D.card + C₁.card + C₂.card + V₂.card := by omega
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 1)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 3 + C at hDbound
  change 3 * A.card ≤ N + C
  omega

/-- The first term of a nonempty progression lying in `V₁ + V₂` is divisible
by three. -/
lemma nonzero_AP_start_dvd_three {A : Finset ℕ} {N a d : ℕ}
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (hQ : natAP a d ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    3 ∣ a := by
  have hlen : 0 < (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1 := by
    have h1 := card_pos.mpr hV₁
    have h2 := card_pos.mpr hV₂
    omega
  have ha : a ∈ upperHalfResidue A N 1 + upperHalfResidue A N 2 :=
    hQ (mem_natAP.mpr ⟨0, hlen, by simp⟩)
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp ha
  subst a
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have hx3 := (mem_upperHalfResidue.mp hx).2
  have hy3 := (mem_upperHalfResidue.mp hy).2
  omega

/-- In the structural nonzero-residue branch the common difference is one
of `3,6,9`. -/
lemma nonzero_structural_step {A : Finset ℕ} {N a d : ℕ}
    (hsub : A ⊆ Icc 1 N) (hN : 1000 ≤ N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hd : 0 < d)
    (hQ : natAP a d ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2)
    (hres : InOneResidue
      (upperHalfResidue A N 1 + upperHalfResidue A N 2) d) :
    d = 3 ∨ d = 6 ∨ d = 9 := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  have hV₁sub : V₁ ⊆ V := filter_subset _ _
  have hV₂sub : V₂ ⊆ V := filter_subset _ _
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    hV₁sub.trans (upperHalf_subset_interval hsub)
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    hV₂sub.trans (upperHalf_subset_interval hsub)
  have hres₁ : InOneResidue V₁ d := inOneResidue_add_left hV₂ hres
  have hres₂ : InOneResidue V₂ d := inOneResidue_add_right hV₁ hres
  obtain ⟨r₁, hr₁⟩ := hres₁
  obtain ⟨r₂, hr₂⟩ := hres₂
  have hcap₁ := mul_card_fixed_zmod_le r₁ hV₁I hr₁
  have hcap₂ := mul_card_fixed_zmod_le r₂ hV₂I hr₂
  change d * V₁.card ≤ (N + d) - (N / 2 + 1) at hcap₁
  change d * V₂.card ≤ (N + d) - (N / 2 + 1) at hcap₂
  change (N + 1) / 2 < 3 * V.card at htail
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hsumlarge : N / 9 + 1 ≤ V₁.card + V₂.card := by omega
  have hlen : 2 ≤ V₁.card + V₂.card - 1 := by
    have hp₁ : 0 < V₁.card := card_pos.mpr hV₁
    have hp₂ : 0 < V₂.card := card_pos.mpr hV₂
    omega
  have hlen0 : 0 < (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1 := by
    change 0 < V₁.card + V₂.card - 1
    omega
  have hlen1 : 1 < (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1 := by
    change 1 < V₁.card + V₂.card - 1
    omega
  have hqa : a ∈ V₁ + V₂ := hQ (mem_natAP.mpr ⟨0, hlen0, by simp⟩)
  have hqad : a + d ∈ V₁ + V₂ := by
    apply hQ
    exact mem_natAP.mpr ⟨1, hlen1, by simp⟩
  have hthreeSum : ∀ z ∈ V₁ + V₂, 3 ∣ z := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx3 := (mem_upperHalfResidue.mp hx).2
    have hy3 := (mem_upperHalfResidue.mp hy).2
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
    omega
  have h3a := hthreeSum a hqa
  have h3ad := hthreeSum (a + d) hqad
  have h3d : 3 ∣ d := by
    obtain ⟨ka, hka⟩ := h3a
    obtain ⟨kad, hkad⟩ := h3ad
    refine ⟨kad - ka, ?_⟩
    omega
  have hdlt : d < 12 := by
    by_contra hnot
    have hd12 : 12 ≤ d := by omega
    obtain ⟨k₁, hk₁⟩ : ∃ k, V₁.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr hV₁)
    obtain ⟨k₂, hk₂⟩ : ∃ k, V₂.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr hV₂)
    have hL : N / 2 + 1 ≤ N := by omega
    have hspan₁ : d * k₁ ≤ N - (N / 2 + 1) := by
      rw [hk₁, Nat.mul_add, Nat.mul_one] at hcap₁
      have heq : (N + d) - (N / 2 + 1) = N - (N / 2 + 1) + d := by omega
      rw [heq] at hcap₁
      omega
    have hspan₂ : d * k₂ ≤ N - (N / 2 + 1) := by
      rw [hk₂, Nat.mul_add, Nat.mul_one] at hcap₂
      have heq : (N + d) - (N / 2 + 1) = N - (N / 2 + 1) + d := by omega
      rw [heq] at hcap₂
      omega
    have hmul₁ : 12 * k₁ ≤ d * k₁ := Nat.mul_le_mul_right k₁ hd12
    have hmul₂ : 12 * k₂ ≤ d * k₂ := Nat.mul_le_mul_right k₂ hd12
    rw [hk₁, hk₂] at hsumlarge
    omega
  obtain ⟨k, hk⟩ := h3d
  have hklt : k < 4 := by nlinarith
  interval_cases k <;> omega

/-- Move lower-half nonmultiples of three into the upper half by powers of
two. -/
noncomputable def upperNonthreeImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ((lowHalf A N).filter fun x ↦ x % 3 ≠ 0).image (scaledMove 0 N 2)

lemma card_upperNonthreeImage {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (upperNonthreeImage A N).card =
      ((lowHalf A N).filter fun x ↦ x % 3 ≠ 0).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono ((filter_subset _ _).trans (filter_subset _ _)))
  intro x hx
  exact hP.pos_of_mem hsub ((mem_lowHalf.mp (mem_filter.mp hx).1).1)

lemma upperNonthreeImage_subset_interval {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    upperNonthreeImage A N ⊆ Icc (N / 2 + 1) N := by
  intro z hz
  simp only [upperNonthreeImage, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hxL := mem_lowHalf.mp (mem_filter.mp hx).1
  have hxpos := hP.pos_of_mem hsub hxL.1
  have hlo := lt_scaledMove (b := 0) (T := N) (q := 2) (by omega) hxpos
  have hhi := scaledMove_le (b := 0) (T := N) (q := 2) (by omega) hxpos (by omega)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma upperNonthreeImage_even {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hz : z ∈ upperNonthreeImage A N) : z % 2 = 0 := by
  simp only [upperNonthreeImage, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hxL := mem_lowHalf.mp (mem_filter.mp hx).1
  have hxpos := hP.pos_of_mem hsub hxL.1
  have hlo := lt_scaledMove (b := 0) (T := N) (q := 2) (by omega) hxpos
  have hexp : 0 < scaledWindowExp 0 N 2 x := by
    by_contra he
    have he0 : scaledWindowExp 0 N 2 x = 0 := by omega
    rw [scaledMove, he0] at hlo
    simp only [pow_zero, one_mul] at hlo
    omega
  rw [scaledMove, Nat.mul_mod]
  have hp : 2 ∣ 2 ^ scaledWindowExp 0 N 2 x := dvd_pow_self 2 (Nat.ne_of_gt hexp)
  rw [Nat.dvd_iff_mod_eq_zero] at hp
  simp [hp]

lemma upperNonthreeImage_mod_three_ne_zero {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ upperNonthreeImage A N) : z % 3 ≠ 0 := by
  simp only [upperNonthreeImage, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hx3 := (mem_filter.mp hx).2
  intro hz3
  have hd : 3 ∣ scaledMove 0 N 2 x := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hz3
  rw [scaledMove] at hd
  rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp hd with hp | hxdiv
  · have : 3 ∣ 2 := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hp
    norm_num at this
  · exact hx3 (Nat.dvd_iff_mod_eq_zero.mp hxdiv)

lemma upperNonthreeImage_disjoint_upperHalf {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (upperNonthreeImage A N) (upperHalf A N) := by
  rw [Finset.disjoint_left]
  intro z hzC hzV
  simp only [upperNonthreeImage, mem_image] at hzC
  obtain ⟨x, hx, rfl⟩ := hzC
  have hxL := mem_lowHalf.mp (mem_filter.mp hx).1
  have hzV' := mem_upperHalf.mp hzV
  have hxpos := hP.pos_of_mem hsub hxL.1
  have hlt := lt_scaledMove (b := 0) (T := N) (q := 2) (by omega) hxpos
  exact hP.not_dvd_of_lt hxL.1 hzV'.1 (by omega) (dvd_scaledMove 0 N 2 x)

/-- A set in the upper half consisting of even nonmultiples of three uses
only the residue classes `2,4 (mod 6)`. -/
lemma six_mul_card_even_nonthree_upper_le {S : Finset ℕ} {N : ℕ}
    (hI : S ⊆ Icc (N / 2 + 1) N)
    (heven : ∀ x ∈ S, x % 2 = 0) (hthree : ∀ x ∈ S, x % 3 ≠ 0) :
    6 * S.card ≤ N + 12 := by
  let S₂ := S.filter fun x ↦ x % 6 = 2
  let S₄ := S.filter fun x ↦ x % 6 = 4
  have hdisj : Disjoint S₂ S₄ := by
    rw [Finset.disjoint_left]
    intro x hx₂ hx₄
    have h₂ := (mem_filter.mp hx₂).2
    have h₄ := (mem_filter.mp hx₄).2
    omega
  have hunion : S₂ ∪ S₄ = S := by
    ext x
    simp only [S₂, S₄, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      have h6 : x % 6 < 6 := Nat.mod_lt _ (by omega)
      have h2rel : x % 2 = (x % 6) % 2 :=
        (Nat.mod_mod_of_dvd x (by omega : 2 ∣ 6)).symm
      have h3rel : x % 3 = (x % 6) % 3 :=
        (Nat.mod_mod_of_dvd x (by omega : 3 ∣ 6)).symm
      have he := heven x hx
      have hn := hthree x hx
      interval_cases x % 6 <;> simp_all
  have hcard : S₂.card + S₄.card = S.card := by
    rw [← card_union_of_disjoint hdisj, hunion]
  have hcap₂ := mul_card_fixed_zmod_le (2 : ZMod 6)
    ((filter_subset _ _).trans hI) (fun x hx ↦ by
      apply (ZMod.natCast_eq_natCast_iff' x 2 6).mpr
      simpa using (mem_filter.mp hx).2)
  have hcap₄ := mul_card_fixed_zmod_le (4 : ZMod 6)
    ((filter_subset _ _).trans hI) (fun x hx ↦ by
      apply (ZMod.natCast_eq_natCast_iff' x 4 6).mpr
      simpa using (mem_filter.mp hx).2)
  change 6 * S₂.card ≤ (N + 6) - (N / 2 + 1) at hcap₂
  change 6 * S₄.card ≤ (N + 6) - (N / 2 + 1) at hcap₄
  omega

/-- An odd subset of the upper half contained in one class modulo nine is
contained in one class modulo eighteen. -/
lemma thirtysix_mul_card_odd_one_mod_nine_upper_le {S : Finset ℕ} {N : ℕ}
    (hI : S ⊆ Icc (N / 2 + 1) N) (hodd : ∀ x ∈ S, x % 2 = 1)
    (hres : InOneResidue S 9) : 36 * S.card ≤ N + 36 := by
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    obtain ⟨r, hr⟩ := hres
    have hmod : ∀ y ∈ S, (y : ZMod 18) = (x : ZMod 18) := by
      intro y hy
      apply (ZMod.natCast_eq_natCast_iff y x 18).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 2 9)).mp
      constructor
      · change y % 2 = x % 2
        rw [hodd y hy, hodd x hx]
      · exact (ZMod.natCast_eq_natCast_iff y x 9).mp
          ((hr y hy).trans (hr x hx).symm)
    have hcap := mul_card_fixed_zmod_le (x : ZMod 18) hI hmod
    change 18 * S.card ≤ (N + 18) - (N / 2 + 1) at hcap
    omega
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp [he]

/-- When the step-nine progression consists of multiples of nine, its
quotient fills essentially the whole zero residue class in the central
third.  Consequently only constantly many lower-half multiples of three
can remain. -/
lemma caseThree_step_nine_zero_low_multiples {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha : a % 9 = 0)
    (hQ : natAP a 9 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    3 * (((lowHalf A N).filter fun x ↦ x % 3 = 0).card) ≤ 9 := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let len := V₁.card + V₂.card - 1
  let Q₃ := natAP (a / 3) 3 len
  let B₀ := zmodFiber (centralImage A N) (0 : ZMod 3)
  let L₀ := (lowHalf A N).filter fun x ↦ x % 3 = 0
  let M₀ := L₀.image (scaledMove 0 N 3)
  change (N + 1) / 2 < 3 * V.card at htail
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hsum : N / 9 + 1 ≤ V₁.card + V₂.card := by omega
  have hlen : N / 9 ≤ len := by omega
  have ha9 : 9 ∣ a := Nat.dvd_iff_mod_eq_zero.mpr ha
  have hQ₃sub : Q₃ ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 9 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show upperHalfResidue A N 1 ⊆ upperHalf A N from filter_subset _ _)
          (show upperHalfResidue A N 2 ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        apply mem_natAP.mpr
        exact ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 3 * j, by
          have ha3 : 3 * (a / 3) = a := Nat.mul_div_cancel' (dvd_trans (by norm_num) ha9)
          omega⟩
    · exact ⟨a / 3 + 3 * j, by
        rw [Nat.mul_add]
        have ha3 : 3 * (a / 3) = a := Nat.mul_div_cancel' (dvd_trans (by norm_num) ha9)
        omega⟩
    · have ha3 : 3 * (a / 3) = a := Nat.mul_div_cancel' (dvd_trans (by norm_num) ha9)
      have heq : a + 9 * j = 3 * (a / 3 + 3 * j) := by omega
      rw [heq]
      simpa using hz
  have hQ₃I : Q₃ ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    hQ₃sub.trans (thirdSumQuotient_subset_central hsub)
  have hQ₃res : ∀ z ∈ Q₃, (z : ZMod 3) = 0 := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
    rw [ZMod.natCast_eq_zero_iff]
    have ha3 : 3 ∣ a / 3 := by
      obtain ⟨k, hk⟩ := ha9
      subst a
      exact ⟨k, by omega⟩
    exact dvd_add ha3 (dvd_mul_right 3 j)
  have hB₀I : B₀ ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro z hz
    have hzB := (mem_zmodFiber.mp hz).1
    have hzW := mem_ratSection.mp (centralImage_subset_window hP hsub hzB)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hB₀res : ∀ z ∈ B₀, (z : ZMod 3) = 0 := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hdisj : Disjoint B₀ Q₃ := by
    apply (centralImage_disjoint_thirdSumQuotient hP hsub).mono
    · exact filter_subset _ _
    · exact hQ₃sub
  let W := B₀ ∪ Q₃
  have hWI : W ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hB₀I hQ₃I
  have hWres : ∀ z ∈ W, (z : ZMod 3) = 0 := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact hB₀res z hz
    · exact hQ₃res z hz
  have hWcap := mul_card_fixed_zmod_le (0 : ZMod 3) hWI hWres
  have hWcard : W.card = B₀.card + Q₃.card := card_union_of_disjoint hdisj
  have hQ₃card : Q₃.card = len := by
    exact card_natAP (by omega)
  change 3 * W.card ≤ (2 * N / 3 + 3) - (N / 3 + 1) at hWcap
  have hB₀small : B₀.card ≤ 3 := by omega
  have hM₀card : M₀.card = L₀.card := by
    apply card_image_iff.mpr
    apply scaledMove_injOn (hP.mono ((filter_subset _ _).trans (filter_subset _ _)))
    intro x hx
    exact hP.pos_of_mem hsub ((mem_lowHalf.mp (mem_filter.mp hx).1).1)
  have hM₀B₀ : M₀ ⊆ B₀ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_zmodFiber.mpr
    constructor
    · apply centralImage_mem_iff.mpr
      exact ⟨x, hxL.1, by omega, rfl⟩
    · rw [ZMod.natCast_eq_zero_iff]
      have hx3 : 3 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr hx'.2
      exact dvd_trans hx3 (dvd_scaledMove 0 N 3 x)
  have hM₀le : M₀.card ≤ B₀.card := card_le_card hM₀B₀
  change 3 * L₀.card ≤ 9
  omega

/-- The `0 (mod 9)` part of the step-nine structural case.  This is the
eight-residue packing in Bedert's equation (34), with explicit floor loss. -/
lemma caseThree_nonzero_step_nine_zero {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha : a % 9 = 0)
    (hQ : natAP a 9 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2)
    (hres : InOneResidue
      (upperHalfResidue A N 1 + upperHalfResidue A N 2) 9) :
    3 * A.card ≤ N + 30 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let C := upperNonthreeImage A N
  let E₁ := parityPart V₁ 0
  let O₁ := parityPart V₁ 1
  let E₂ := parityPart V₂ 0
  let O₂ := parityPart V₂ 1
  let E := C ∪ E₁ ∪ E₂
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  change (N + 1) / 2 < 3 * V.card at htail
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hres₁ : InOneResidue V₁ 9 := inOneResidue_add_left hV₂ hres
  have hres₂ : InOneResidue V₂ 9 := inOneResidue_add_right hV₁ hres
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  obtain ⟨r₁, hr₁⟩ := hres₁
  obtain ⟨r₂, hr₂⟩ := hres₂
  have hcap₁ := mul_card_fixed_zmod_le r₁ hV₁I hr₁
  have hcap₂ := mul_card_fixed_zmod_le r₂ hV₂I hr₂
  change 9 * V₁.card ≤ (N + 9) - (N / 2 + 1) at hcap₁
  change 9 * V₂.card ≤ (N + 9) - (N / 2 + 1) at hcap₂
  have hV₀ratio : 2 * V₀.card ≤ V₁.card + V₂.card := by omega
  have hsumcap : 9 * (V₁.card + V₂.card) ≤ N + 18 := by omega
  have hV₀cap : 18 * V₀.card ≤ N + 18 := by nlinarith
  have hCcard := card_upperNonthreeImage hP hsub
  change C.card = Lₙ.card at hCcard
  have hCI := upperNonthreeImage_subset_interval hP hsub
  change C ⊆ Icc (N / 2 + 1) N at hCI
  have hCV : Disjoint C V := upperNonthreeImage_disjoint_upperHalf hP hsub
  have hCE₁ : Disjoint C E₁ := hCV.mono_right <|
    (filter_subset _ _).trans (filter_subset _ _)
  have hCE₂ : Disjoint C E₂ := hCV.mono_right <|
    (filter_subset _ _).trans (filter_subset _ _)
  have hE₁E₂ : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h1 := (mem_upperHalfResidue.mp (mem_parityPart.mp hx₁).1).2
    have h2 := (mem_upperHalfResidue.mp (mem_parityPart.mp hx₂).1).2
    omega
  have hCE₁E₂ : Disjoint (C ∪ E₁) E₂ := by
    rw [Finset.disjoint_left]
    intro x hx hx₂
    rcases mem_union.mp hx with hxC | hxE
    · exact (Finset.disjoint_left.mp hCE₂) hxC hx₂
    · exact (Finset.disjoint_left.mp hE₁E₂) hxE hx₂
  have hEcard : E.card = C.card + E₁.card + E₂.card := by
    change (C ∪ E₁ ∪ E₂).card = _
    rw [card_union_of_disjoint hCE₁E₂, card_union_of_disjoint hCE₁]
  have hEI : E ⊆ Icc (N / 2 + 1) N := by
    exact union_subset (union_subset hCI
      (((filter_subset _ _).trans (filter_subset _ _)).trans
        (upperHalf_subset_interval hsub)))
      (((filter_subset _ _).trans (filter_subset _ _)).trans
        (upperHalf_subset_interval hsub))
  have hEeven : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hxC | hxE
      · exact upperNonthreeImage_even hP hsub hxC
      · simpa using (mem_parityPart.mp hxE).2
    · simpa using (mem_parityPart.mp hx).2
  have hEnonthree : ∀ x ∈ E, x % 3 ≠ 0 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hxC | hxE
      · exact upperNonthreeImage_mod_three_ne_zero hxC
      · have h1 := (mem_upperHalfResidue.mp (mem_parityPart.mp hxE).1).2
        omega
    · have h2 := (mem_upperHalfResidue.mp (mem_parityPart.mp hx).1).2
      omega
  have hEcap := six_mul_card_even_nonthree_upper_le hEI hEeven hEnonthree
  have hO₁I : O₁ ⊆ Icc (N / 2 + 1) N :=
    ((filter_subset _ _).trans hV₁I)
  have hO₂I : O₂ ⊆ Icc (N / 2 + 1) N :=
    ((filter_subset _ _).trans hV₂I)
  have hO₁odd : ∀ x ∈ O₁, x % 2 = 1 := by
    intro x hx; simpa using (mem_parityPart.mp hx).2
  have hO₂odd : ∀ x ∈ O₂, x % 2 = 1 := by
    intro x hx; simpa using (mem_parityPart.mp hx).2
  have hO₁cap := thirtysix_mul_card_odd_one_mod_nine_upper_le hO₁I hO₁odd
    (inOneResidue_mono ⟨r₁, hr₁⟩ (filter_subset _ _))
  have hO₂cap := thirtysix_mul_card_odd_one_mod_nine_upper_le hO₂I hO₂odd
    (inOneResidue_mono ⟨r₂, hr₂⟩ (filter_subset _ _))
  have hpar₁ := card_parity_parts V₁
  have hpar₂ := card_parity_parts V₂
  change E₁.card + O₁.card = V₁.card at hpar₁
  change E₂.card + O₂.card = V₂.card at hpar₂
  have hnonzeroPack : 36 * (C.card + V₁.card + V₂.card) ≤ 8 * N + 216 := by
    omega
  have hL₀small := caseThree_step_nine_zero_low_multiples hP hsub htail hdom ha hQ
  change 3 * L₀.card ≤ 9 at hL₀small
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx₀ hxₙ
      exact (mem_filter.mp hxₙ).2 (mem_filter.mp hx₀).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        exact if h : x % 3 = 0 then Or.inl ⟨hx, h⟩ else Or.inr ⟨hx, h⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  omega

/-- Move a point of `(N/4,N/2]` into the central third, doubling precisely
the points in its left part. -/
def halfCentralize (N z : ℕ) : ℕ := if 3 * z ≤ N then 2 * z else z

lemma halfCentralize_injOn_interval (N : ℕ) :
    Set.InjOn (halfCentralize N) (Icc (N / 4 + 1) (N / 2)) := by
  intro x hx y hy hxy
  have hxI := mem_Icc.mp hx
  have hyI := mem_Icc.mp hy
  simp only [halfCentralize] at hxy
  split at hxy <;> split at hxy
  · omega
  · omega
  · omega
  · exact hxy

lemma halfCentralize_subset_central {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ Icc (N / 4 + 1) (N / 2)) :
    S.image (halfCentralize N) ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
  have hxI := mem_Icc.mp (hS hx)
  simp only [halfCentralize]
  split
  · exact mem_Icc.mpr ⟨by omega, by omega⟩
  · exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma card_image_halfCentralize {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ Icc (N / 4 + 1) (N / 2)) :
    (S.image (halfCentralize N)).card = S.card := by
  exact card_image_iff.mpr ((halfCentralize_injOn_interval N).mono hS)

/-- Centralizing the half-window image preserves the fact that each point is
a multiple of an originating lower-half member of `A`. -/
lemma halfCentralize_lowNonthree_has_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ (lowNonthreeImage A N).image (halfCentralize N)) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ z := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
  have hbH := lowNonthreeImage_subset_halfImage A N hb
  obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor hbH
  refine ⟨a, ha, haN, ?_⟩
  simp only [halfCentralize]
  split
  · exact dvd_trans hab (dvd_mul_left b 2)
  · exact hab

lemma halfCentralized_lowNonthree_disjoint_thirdSum {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (_hsub : A ⊆ Icc 1 N) :
    Disjoint ((lowNonthreeImage A N).image (halfCentralize N))
      (thirdSumQuotient A N) := by
  rw [Finset.disjoint_left]
  intro z hzC hzQ
  obtain ⟨a, ha, haN, haz⟩ := halfCentralize_lowNonthree_has_divisor hzC
  have h3z := quotientPart_spec hzQ
  have hsum := (mem_zmodFiber.mp h3z).1
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp hsum
  have hx' := mem_upperHalf.mp hx
  have hy' := mem_upperHalf.mp hy
  apply hP.not_dvd_add ha hx'.1 hy'.1 (by omega) (by omega)
  rw [hxy]
  exact haz.mul_left 3

/-- If the step-nine progression has nonzero residue after division by
three, nearly all of the half-window image is forced into one residue in
each of `(N/4,N/3]` and `(N/3,N/2]`. -/
lemma caseThree_step_nine_nonzero_low_nonthree_data
    {A : Finset ℕ} {N q len : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hlen : N / 9 ≤ len) (hq : q % 3 ≠ 0)
    (hQsub : natAP q 3 len ⊆ thirdSumQuotient A N) :
    36 * (lowNonthreeImage A N).card ≤ 3 * N + 300 := by
  let C := lowNonthreeImage A N
  let f := halfCentralize N
  let t := q % 3
  let Bad := C.filter fun z ↦ f z % 3 = t
  let Lo := C.filter fun z ↦ f z % 3 ≠ t ∧ 3 * z ≤ N
  let Hi := C.filter fun z ↦ f z % 3 ≠ t ∧ N < 3 * z
  let FBad := Bad.image f
  let Q₃ := natAP q 3 len
  have hCI := lowNonthreeImage_subset_interval hP hsub
  change C ⊆ Icc (N / 4 + 1) (N / 2) at hCI
  have hQ₃sub : Q₃ ⊆ thirdSumQuotient A N := by simpa [Q₃] using hQsub
  have hQ₃I : Q₃ ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    hQ₃sub.trans (thirdSumQuotient_subset_central hsub)
  have hQ₃res : ∀ z ∈ Q₃, (z : ZMod 3) = (t : ZMod 3) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
    apply (ZMod.natCast_eq_natCast_iff' _ t 3).mpr
    dsimp [t]
    omega
  have hFBadI : FBad ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    exact halfCentralize_subset_central ((filter_subset _ _).trans hCI)
  have hFBadres : ∀ z ∈ FBad, (z : ZMod 3) = (t : ZMod 3) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    apply (ZMod.natCast_eq_natCast_iff' _ t 3).mpr
    have htlt' : t < 3 := Nat.mod_lt _ (by omega)
    simpa [Nat.mod_eq_of_lt htlt'] using (mem_filter.mp hx).2
  have hFQ : Disjoint FBad Q₃ := by
    apply (halfCentralized_lowNonthree_disjoint_thirdSum hP hsub).mono
    · exact image_subset_image (filter_subset _ _)
    · exact hQ₃sub
  let W := FBad ∪ Q₃
  have hWI : W ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hFBadI hQ₃I
  have hWres : ∀ z ∈ W, (z : ZMod 3) = (t : ZMod 3) := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact hFBadres z hz
    · exact hQ₃res z hz
  have hWcap := mul_card_fixed_zmod_le (t : ZMod 3) hWI hWres
  have hWcard : W.card = FBad.card + Q₃.card := card_union_of_disjoint hFQ
  have hFBadcard : FBad.card = Bad.card :=
    card_image_halfCentralize ((filter_subset _ _).trans hCI)
  have hQ₃card : Q₃.card = len := card_natAP (by omega)
  change 3 * W.card ≤ (2 * N / 3 + 3) - (N / 3 + 1) at hWcap
  have hBadsmall : Bad.card ≤ 3 := by omega
  have htlt : t < 3 := Nat.mod_lt _ (by omega)
  have htne : t ≠ 0 := by simpa [t] using hq
  have hLoI : Lo ⊆ Icc (N / 4 + 1) (N / 3) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzI := mem_Icc.mp (hCI hz'.1)
    exact mem_Icc.mpr ⟨hzI.1, by omega⟩
  have hHiI : Hi ⊆ Icc (N / 3 + 1) (N / 2) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzI := mem_Icc.mp (hCI hz'.1)
    exact mem_Icc.mpr ⟨by omega, hzI.2⟩
  have hLores : ∀ z ∈ Lo, (z : ZMod 3) = (t : ZMod 3) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzn := lowNonthreeImage_not_dvd_three hz'.1
    rw [Nat.dvd_iff_mod_eq_zero] at hzn
    have hzmod := Nat.mod_lt z (by omega : 0 < 3)
    have hbad := hz'.2.1
    have hf : f z = 2 * z := by simp [f, halfCentralize, hz'.2.2]
    rw [hf, Nat.mul_mod] at hbad
    apply (ZMod.natCast_eq_natCast_iff' z t 3).mpr
    interval_cases t <;> interval_cases z % 3 <;> simp_all
  have hHires : ∀ z ∈ Hi, (z : ZMod 3) = ((3 - t : ℕ) : ZMod 3) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzn := lowNonthreeImage_not_dvd_three hz'.1
    rw [Nat.dvd_iff_mod_eq_zero] at hzn
    have hzmod := Nat.mod_lt z (by omega : 0 < 3)
    have hbad := hz'.2.1
    have hnle : ¬ 3 * z ≤ N := by omega
    have hf : f z = z := by simp [f, halfCentralize, hnle]
    rw [hf] at hbad
    apply (ZMod.natCast_eq_natCast_iff' z (3 - t) 3).mpr
    interval_cases t <;> interval_cases z % 3 <;> simp_all
  have hLocap := mul_card_fixed_zmod_le (t : ZMod 3) hLoI hLores
  have hHicap := mul_card_fixed_zmod_le ((3 - t : ℕ) : ZMod 3) hHiI hHires
  change 3 * Lo.card ≤ (N / 3 + 3) - (N / 4 + 1) at hLocap
  change 3 * Hi.card ≤ (N / 2 + 3) - (N / 3 + 1) at hHicap
  have hparts : Bad.card + Lo.card + Hi.card = C.card := by
    have hdisjBL : Disjoint Bad Lo := by
      rw [Finset.disjoint_left]
      intro z hzB hzL
      exact (mem_filter.mp hzL).2.1 (mem_filter.mp hzB).2
    have hdisjBH : Disjoint Bad Hi := by
      rw [Finset.disjoint_left]
      intro z hzB hzH
      exact (mem_filter.mp hzH).2.1 (mem_filter.mp hzB).2
    have hdisjLH : Disjoint Lo Hi := by
      rw [Finset.disjoint_left]
      intro z hzL hzH
      have hl := (mem_filter.mp hzL).2.2
      have hh := (mem_filter.mp hzH).2.2
      omega
    have hdisj : Disjoint (Bad ∪ Lo) Hi := by
      rw [Finset.disjoint_left]
      intro z hz hzH
      rcases mem_union.mp hz with hz | hz
      · exact (Finset.disjoint_left.mp hdisjBH) hz hzH
      · exact (Finset.disjoint_left.mp hdisjLH) hz hzH
    have hunion : Bad ∪ Lo ∪ Hi = C := by
      ext z
      simp only [Bad, Lo, Hi, mem_union, mem_filter]
      constructor
      · rintro ((h | h) | h) <;> exact h.1
      · intro hz
        by_cases hb : f z % 3 = t
        · exact Or.inl (Or.inl ⟨hz, hb⟩)
        · by_cases hlo : 3 * z ≤ N
          · exact Or.inl (Or.inr ⟨hz, hb, hlo⟩)
          · exact Or.inr ⟨hz, hb, by omega⟩
    calc
      Bad.card + Lo.card + Hi.card = (Bad ∪ Lo).card + Hi.card := by
        rw [card_union_of_disjoint hdisjBL]
      _ = (Bad ∪ Lo ∪ Hi).card := (card_union_of_disjoint hdisj).symm
      _ = C.card := congrArg Finset.card hunion
  change 36 * C.card ≤ 3 * N + 300
  omega

lemma caseThree_step_nine_nonzero_low_nonthree {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha3 : 3 ∣ a) (hat : (a / 3) % 3 ≠ 0)
    (hQ : natAP a 9 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    36 * (lowNonthreeImage A N).card ≤ 3 * N + 300 := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let len := V₁.card + V₂.card - 1
  change (N + 1) / 2 < 3 * V.card at htail
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hlen : N / 9 ≤ len := by dsimp [len]; omega
  have hQsub : natAP (a / 3) 3 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 9 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₁ ⊆ upperHalf A N from filter_subset _ _)
          (show V₂ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 3 * j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + 3 * j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 9 * j = 3 * (a / 3 + 3 * j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  exact caseThree_step_nine_nonzero_low_nonthree_data hP hsub hlen hat hQsub

/-- Common final estimate for a step-nine progression whose divided start
is nonzero modulo three. -/
lemma caseThree_step_nine_nonzero_data {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (hVcap : 6 * (upperHalf A N).card ≤ N + 18)
    (hZcap : 36 * (lowNonthreeImage A N).card ≤ 3 * N + 300)
    (hind : CoarseBound C (N / 6)
      ((divisibleInitial A N 3 2).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 2
  let Z := lowNonthreeImage A N
  change 6 * V.card ≤ N + 18 at hVcap
  change 36 * Z.card ≤ 3 * N + 300 at hZcap
  have hZcard := card_lowNonthreeImage hP hsub
  change Z.card = Lₙ.card at hZcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx₀ hxₙ
      exact (mem_filter.mp hxₙ).2 (mem_filter.mp hx₀).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        exact if h : x % 3 = 0 then Or.inl ⟨hx, h⟩ else Or.inr ⟨hx, h⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    exact ⟨hxL.1, Nat.dvd_iff_mod_eq_zero.mpr hx'.2, hxL.2⟩
  have hL₀le : L₀.card ≤ D.card := card_le_card hL₀D
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 2)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 6 + C at hDbound
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  change 3 * A.card ≤ N + C
  omega

lemma caseThree_nonzero_step_nine_nonzero {A : Finset ℕ} {N C a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) (hN : 1000 ≤ N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha3 : 3 ∣ a) (hat : (a / 3) % 3 ≠ 0)
    (hQ : natAP a 9 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2)
    (hres : InOneResidue
      (upperHalfResidue A N 1 + upperHalfResidue A N 2) 9)
    (hind : CoarseBound C (N / 6)
      ((divisibleInitial A N 3 2).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 2
  let Z := lowNonthreeImage A N
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hres₁ : InOneResidue V₁ 9 := inOneResidue_add_left hV₂ hres
  have hres₂ : InOneResidue V₂ 9 := inOneResidue_add_right hV₁ hres
  obtain ⟨r₁, hr₁⟩ := hres₁
  obtain ⟨r₂, hr₂⟩ := hres₂
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hcap₁ := mul_card_fixed_zmod_le r₁ hV₁I hr₁
  have hcap₂ := mul_card_fixed_zmod_le r₂ hV₂I hr₂
  change 9 * V₁.card ≤ (N + 9) - (N / 2 + 1) at hcap₁
  change 9 * V₂.card ≤ (N + 9) - (N / 2 + 1) at hcap₂
  have hVcap : 6 * V.card ≤ N + 18 := by omega
  have hZcap := caseThree_step_nine_nonzero_low_nonthree hP hsub htail hdom
    ha3 hat hQ
  change 36 * Z.card ≤ 3 * N + 300 at hZcap
  have hZcard := card_lowNonthreeImage hP hsub
  change Z.card = Lₙ.card at hZcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx₀ hxₙ
      exact (mem_filter.mp hxₙ).2 (mem_filter.mp hx₀).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        exact if h : x % 3 = 0 then Or.inl ⟨hx, h⟩ else Or.inr ⟨hx, h⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    exact ⟨hxL.1, Nat.dvd_iff_mod_eq_zero.mpr hx'.2, hxL.2⟩
  have hL₀le : L₀.card ≤ D.card := card_le_card hL₀D
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 2)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 6 + C at hDbound
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  change 3 * A.card ≤ N + C
  omega

/-- The step-six structural case.  Exact terminal density removes the small
linear error used in the paper: the even and odd alternatives both close by
packing into the two parity classes of the central third. -/
lemma caseThree_step_six_data {A : Finset ℕ} {N q len : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hVcap : 4 * (upperHalf A N).card ≤ N + 12)
    (hdomlen : 2 * (upperHalf A N).card ≤ 3 * len + 3)
    (hoddcover : (upperHalf A N).card ≤
      len + (upperHalfResidue A N 0).card + 1)
    (hQsub : natAP q 2 len ⊆ thirdSumQuotient A N) :
    3 * A.card ≤ N + 18 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let Y := middleSixth A N
  let H := highThird A N
  let B := centralImage A N
  let E := parityPart B 0
  let O := parityPart B 1
  let Oₗ := O.filter fun z ↦ 2 * z ≤ N
  let Oᵣ := O.filter fun z ↦ N < 2 * z
  let Q₃ := natAP q 2 len
  change 4 * V.card ≤ N + 12 at hVcap
  change 2 * V.card ≤ 3 * len + 3 at hdomlen
  change V.card ≤ len + V₀.card + 1 at hoddcover
  have hQ₃sub : Q₃ ⊆ thirdSumQuotient A N := by simpa [Q₃] using hQsub
  have hQ₃I : Q₃ ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    hQ₃sub.trans (thirdSumQuotient_subset_central hsub)
  have hQ₃card : Q₃.card = len := card_natAP (by omega)
  have hBI : B ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro z hz
    have hz' := mem_ratSection.mp (centralImage_subset_window hP hsub hz)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hBpart := card_parity_parts B
  change E.card + O.card = B.card at hBpart
  have hOpart : Oₗ.card + Oᵣ.card = O.card := by
    have hd : Disjoint Oₗ Oᵣ := by
      rw [Finset.disjoint_left]
      intro z hzₗ hzᵣ
      have hl := (mem_filter.mp hzₗ).2
      have hr := (mem_filter.mp hzᵣ).2
      omega
    have hu : Oₗ ∪ Oᵣ = O := by
      ext z
      simp only [Oₗ, Oᵣ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        exact (le_or_gt (2 * z) N).imp (And.intro hz) (And.intro hz)
    rw [← card_union_of_disjoint hd, hu]
  have hOₗI : Oₗ ⊆ Icc (N / 3 + 1) (N / 2) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzI := mem_Icc.mp (hBI ((filter_subset _ _) hz'.1))
    exact mem_Icc.mpr ⟨hzI.1, by omega⟩
  have hOₗodd : ∀ z ∈ Oₗ, (z : ZMod 2) = 1 := by
    intro z hz
    apply (ZMod.natCast_eq_natCast_iff' z 1 2).mpr
    simpa using (mem_parityPart.mp (mem_filter.mp hz).1).2
  have hOₗcap := mul_card_fixed_zmod_le (1 : ZMod 2) hOₗI hOₗodd
  change 2 * Oₗ.card ≤ (N / 2 + 2) - (N / 3 + 1) at hOₗcap
  have hOᵣY : Oᵣ ⊆ Y := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzO := mem_parityPart.mp hz'.1
    obtain ⟨x, hxA, hxN, hxb⟩ := centralImage_mem_iff.mp
      hzO.1
    have hodd : z % 2 = 1 := by simpa using hzO.2
    have heq : z = x := by
      have := scaledMove_eq_self_of_odd (T := N) (q := 3) (a := x) (by rwa [hxb])
      omega
    have hright : N < 2 * x := by simpa [heq] using hz'.2
    rw [heq]
    apply mem_middleSixth.mpr
    exact ⟨hxA, hright, hxN⟩
  have hOᵣle : Oᵣ.card ≤ Y.card := card_le_card hOᵣY
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  have hAB := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hAB
  by_cases heven : q % 2 = 0
  · have hQeven : ∀ z ∈ Q₃, (z : ZMod 2) = 0 := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
      rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
      omega
    have hEI : E ⊆ Icc (N / 3 + 1) (2 * N / 3) := (filter_subset _ _).trans hBI
    have hEeven : ∀ z ∈ E, (z : ZMod 2) = 0 := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z 0 2).mpr
      simpa using (mem_parityPart.mp hz).2
    have hdisj : Disjoint E Q₃ := by
      apply (centralImage_disjoint_thirdSumQuotient hP hsub).mono
      · exact filter_subset _ _
      · exact hQ₃sub
    let W := E ∪ Q₃
    have hWI : W ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hEI hQ₃I
    have hWres : ∀ z ∈ W, (z : ZMod 2) = 0 := by
      intro z hz
      rcases mem_union.mp hz with hz | hz
      · exact hEeven z hz
      · exact hQeven z hz
    have hWcap := mul_card_fixed_zmod_le (0 : ZMod 2) hWI hWres
    have hWcard : W.card = E.card + Q₃.card := card_union_of_disjoint hdisj
    change 2 * W.card ≤ (2 * N / 3 + 2) - (N / 3 + 1) at hWcap
    have hEbound : 6 * (E.card + len) ≤ N + 6 := by omega
    have hObound : 12 * Oₗ.card ≤ N + 12 := by omega
    have hright : Oᵣ.card + H.card ≤ V.card := by omega
    omega
  · have hodd : q % 2 = 1 := by
      have := Nat.mod_lt q (by omega : 0 < 2)
      omega
    have hQodd : ∀ z ∈ Q₃, (z : ZMod 2) = 1 := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
      apply (ZMod.natCast_eq_natCast_iff' _ 1 2).mpr
      omega
    have hOI : O ⊆ Icc (N / 3 + 1) (2 * N / 3) := (filter_subset _ _).trans hBI
    have hOodd : ∀ z ∈ O, (z : ZMod 2) = 1 := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z 1 2).mpr
      simpa using (mem_parityPart.mp hz).2
    have hOQ : Disjoint O Q₃ := by
      apply (centralImage_disjoint_thirdSumQuotient hP hsub).mono
      · exact filter_subset _ _
      · exact hQ₃sub
    let Wₒ := O ∪ Q₃
    have hWₒI : Wₒ ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hOI hQ₃I
    have hWₒres : ∀ z ∈ Wₒ, (z : ZMod 2) = 1 := by
      intro z hz
      rcases mem_union.mp hz with hz | hz
      · exact hOodd z hz
      · exact hQodd z hz
    have hWₒcap := mul_card_fixed_zmod_le (1 : ZMod 2) hWₒI hWₒres
    have hWₒcard : Wₒ.card = O.card + Q₃.card := card_union_of_disjoint hOQ
    let T₀ := V₀.image fun x ↦ 2 * (x / 3)
    have hT₀card : T₀.card = V₀.card := by
      apply card_image_iff.mpr
      intro x hx y hy hxy
      have hx3 : 3 ∣ x := by
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using (mem_upperHalfResidue.mp hx).2
      have hy3 : 3 ∣ y := by
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using (mem_upperHalfResidue.mp hy).2
      have hxmul := Nat.mul_div_cancel' hx3
      have hymul := Nat.mul_div_cancel' hy3
      have hdiv : x / 3 = y / 3 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
      calc
        x = 3 * (x / 3) := hxmul.symm
        _ = 3 * (y / 3) := by rw [hdiv]
        _ = y := hymul
    have hT₀sub : T₀ ⊆ thirdSumQuotient A N := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      have hx' := mem_upperHalfResidue.mp hx
      have hxV := mem_upperHalf.mp hx'.1
      have hx3 : 3 ∣ x := by
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using hx'.2
      apply mem_quotientPart.mpr
      refine ⟨2 * x, ?_, ?_, ?_⟩
      · apply mem_zmodFiber.mpr
        constructor
        · simpa [two_mul] using Finset.add_mem_add hx'.1 hx'.1
        · rw [ZMod.natCast_eq_zero_iff]
          exact hx3.mul_left 2
      · exact hx3.mul_left 2
      · have heq : 2 * x = 3 * (2 * (x / 3)) := by
          have := Nat.mul_div_cancel' hx3
          omega
        rw [heq]
        simp
    have hT₀I : T₀ ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
      hT₀sub.trans (thirdSumQuotient_subset_central hsub)
    have hT₀even : ∀ z ∈ T₀, (z : ZMod 2) = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right 2 (x / 3)
    have hEI : E ⊆ Icc (N / 3 + 1) (2 * N / 3) := (filter_subset _ _).trans hBI
    have hEeven : ∀ z ∈ E, (z : ZMod 2) = 0 := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z 0 2).mpr
      simpa using (mem_parityPart.mp hz).2
    have hET : Disjoint E T₀ := by
      apply (centralImage_disjoint_thirdSumQuotient hP hsub).mono
      · exact filter_subset _ _
      · exact hT₀sub
    let Wₑ := E ∪ T₀
    have hWₑI : Wₑ ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hEI hT₀I
    have hWₑres : ∀ z ∈ Wₑ, (z : ZMod 2) = 0 := by
      intro z hz
      rcases mem_union.mp hz with hz | hz
      · exact hEeven z hz
      · exact hT₀even z hz
    have hWₑcap := mul_card_fixed_zmod_le (0 : ZMod 2) hWₑI hWₑres
    have hWₑcard : Wₑ.card = E.card + T₀.card := card_union_of_disjoint hET
    change 2 * Wₒ.card ≤ (2 * N / 3 + 2) - (N / 3 + 1) at hWₒcap
    change 2 * Wₑ.card ≤ (2 * N / 3 + 2) - (N / 3 + 1) at hWₑcap
    have hObound : 6 * (O.card + len) ≤ N + 6 := by omega
    have hEbound : 6 * (E.card + V₀.card) ≤ N + 6 := by omega
    omega

lemma caseThree_nonzero_step_six {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha3 : 3 ∣ a)
    (hQ : natAP a 6 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2)
    (hres : InOneResidue
      (upperHalfResidue A N 1 + upperHalfResidue A N 2) 6) :
    3 * A.card ≤ N + 18 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let len := V₁.card + V₂.card - 1
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hres₁ : InOneResidue V₁ 6 := inOneResidue_add_left hV₂ hres
  have hres₂ : InOneResidue V₂ 6 := inOneResidue_add_right hV₁ hres
  obtain ⟨r₁, hr₁⟩ := hres₁
  obtain ⟨r₂, hr₂⟩ := hres₂
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hcap₁ := mul_card_fixed_zmod_le r₁ hV₁I hr₁
  have hcap₂ := mul_card_fixed_zmod_le r₂ hV₂I hr₂
  change 6 * V₁.card ≤ (N + 6) - (N / 2 + 1) at hcap₁
  change 6 * V₂.card ≤ (N + 6) - (N / 2 + 1) at hcap₂
  have hVcap : 4 * V.card ≤ N + 12 := by omega
  have hdomlen : 2 * V.card ≤ 3 * len + 3 := by dsimp [len]; omega
  have hoddcover : V.card ≤ len + V₀.card + 1 := by dsimp [len]; omega
  have hQsub : natAP (a / 3) 2 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 6 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₁ ⊆ upperHalf A N from filter_subset _ _)
          (show V₂ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 2 * j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + 2 * j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 6 * j = 3 * (a / 3 + 2 * j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  exact caseThree_step_six_data hP hsub hVcap hdomlen hoddcover hQsub

/-! ### The step-three structural branch -/

/-- A unit-step interval in the divided upper-half sumset excludes every
member of `A` no larger than the interval. -/
lemma not_mem_of_le_thirdSum_interval {A : Finset ℕ} {N q len x : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hI : natAP q 1 len ⊆ thirdSumQuotient A N)
    (hxA : x ∈ A) (hxlen : x ≤ len) (hxhalf : 2 * x ≤ N) : False := by
  have hxpos : 0 < x := hP.pos_of_mem hsub hxA
  obtain ⟨y, hyI, hxy⟩ := exists_dvd_mem_natAP_one hxpos hxlen
  have hyQ := quotientPart_spec (hI hyI)
  have hysum := (mem_zmodFiber.mp hyQ).1
  obtain ⟨b, hb, c, hc, hbc⟩ := mem_add.mp hysum
  have hb' := mem_upperHalf.mp hb
  have hc' := mem_upperHalf.mp hc
  have hxb : x < b := by
    omega
  have hxc : x < c := by
    omega
  apply hP.not_dvd_add hxA hb'.1 hc'.1 hxb hxc
  rw [hbc]
  exact hxy.mul_left 3

/-- The same divided interval excludes every multiple of three up to three
times its length. -/
lemma not_mem_three_of_le_thirdSum_interval {A : Finset ℕ} {N q len x : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hI : natAP q 1 len ⊆ thirdSumQuotient A N)
    (hxA : x ∈ A) (hx3 : 3 ∣ x) (hxlen : x ≤ 3 * len)
    (hxhalf : 2 * x ≤ N) : False := by
  have hxpos : 0 < x := hP.pos_of_mem hsub hxA
  have huPos : 0 < x / 3 := Nat.div_pos (Nat.le_of_dvd hxpos hx3) (by omega)
  have hulen : x / 3 ≤ len := by
    have hxeq : 3 * (x / 3) = x := Nat.mul_div_cancel' hx3
    omega
  obtain ⟨y, hyI, huy⟩ := exists_dvd_mem_natAP_one huPos hulen
  have hyQ := quotientPart_spec (hI hyI)
  have hysum := (mem_zmodFiber.mp hyQ).1
  obtain ⟨b, hb, c, hc, hbc⟩ := mem_add.mp hysum
  have hb' := mem_upperHalf.mp hb
  have hc' := mem_upperHalf.mp hc
  have hxb : x < b := by
    omega
  have hxc : x < c := by
    omega
  apply hP.not_dvd_add hxA hb'.1 hc'.1 hxb hxc
  rw [hbc]
  obtain ⟨k, hk⟩ := huy
  refine ⟨k, ?_⟩
  have hxeq : 3 * (x / 3) = x := Nat.mul_div_cancel' hx3
  calc
    3 * y = 3 * ((x / 3) * k) := by rw [hk]
    _ = (3 * (x / 3)) * k := by ring
    _ = x * k := by rw [hxeq]

/-- Bedert's piecewise compression of the lower half in the step-three
case.  Its five branches are, in order, multiplication by `3`, by `2`, by
`3/2`, and the identity on each of the two remaining intervals. -/
def stepThreeCompress (N x : ℕ) : ℕ :=
  if 6 * x ≤ N then 3 * x
  else if 4 * x ≤ N then 2 * x
  else if 3 * x ≤ N then if x % 2 = 0 then 3 * (x / 2) else x
  else x

lemma dvd_two_stepThreeCompress (N x : ℕ) : x ∣ 2 * stepThreeCompress N x := by
  simp only [stepThreeCompress]
  split_ifs with h6 h4 h3 heven
  · exact ⟨6, by ring⟩
  · exact ⟨4, by ring⟩
  · have hx2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
    exact ⟨3, by omega⟩
  · exact ⟨2, by ring⟩
  · exact ⟨2, by ring⟩

/-- The step-three compression maps the relevant lower-half window into
`(N/4,N/2]`. -/
lemma stepThreeCompress_mem_window {N x : ℕ} (hsmall : N / 9 < x)
    (hhalf : 2 * x ≤ N) : stepThreeCompress N x ∈ Icc (N / 4 + 1) (N / 2) := by
  simp only [stepThreeCompress]
  split_ifs with h6 h4 h3 heven
  · apply mem_Icc.mpr
    omega
  · apply mem_Icc.mpr
    omega
  · have hx2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
    apply mem_Icc.mpr
    omega
  · apply mem_Icc.mpr
    omega
  · apply mem_Icc.mpr
    omega

/-- Every compressed value has its source dividing four times the value. -/
lemma dvd_four_stepThreeCompress (N x : ℕ) : x ∣ 4 * stepThreeCompress N x := by
  simp only [stepThreeCompress]
  split_ifs with h6 h4 h3 heven
  · exact ⟨12, by ring⟩
  · exact ⟨8, by ring⟩
  · have hx2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
    exact ⟨6, by omega⟩
  · exact ⟨4, by ring⟩
  · exact ⟨4, by ring⟩

/-- Values in the left third of the compression window are unchanged odd
sources. -/
lemma stepThreeCompress_left {N x : ℕ} (hx : N / 9 < x)
    (hz : stepThreeCompress N x ≤ N / 3) :
    stepThreeCompress N x = x ∧ x % 2 = 1 ∧ N < 4 * x ∧ 3 * x ≤ N := by
  simp only [stepThreeCompress] at hz ⊢
  split_ifs at hz ⊢ with h6 h4 h3 heven
  · omega
  · omega
  · have hx2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
    omega
  · have hmodlt := Nat.mod_lt x (by omega : 0 < 2)
    omega
  · omega

/-- The piecewise compression is injective on a property-P lower set once
the only exceptional collision is ruled out by excluding small multiples
of three. -/
lemma stepThreeCompress_injOn {A D : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hD : ∀ x ∈ D, x ∈ A ∧ 2 * x ≤ N)
    (hno3 : ∀ x ∈ D, 3 ∣ x → x ≤ N / 3 → False) :
    Set.InjOn (stepThreeCompress N) D := by
  intro x hx y hy hxy
  have hxD := hD x hx
  have hyD := hD y hy
  have contra (u v : ℕ) (hu : u ∈ A) (hv : v ∈ A)
      (huv : u < v) (hd : u ∣ 2 * v) : False :=
    hP.not_dvd_two_mul hu hv huv hd
  simp only [stepThreeCompress] at hxy
  split_ifs at hxy with hx6 hx4 hx3 hxe hy6 hy4 hy3 hye
  all_goals try have hxEvenEq : 2 * (x / 2) = x :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by assumption))
  all_goals try have hyEvenEq : 2 * (y / 2) = y :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by assumption))
  all_goals try omega
  all_goals
    first
    | exact False.elim (hno3 x hx
        ((by norm_num : Nat.Coprime 3 2).dvd_of_dvd_mul_left ⟨y / 2, hxy⟩)
        (by omega))
    | exact False.elim (hno3 y hy
        ((by norm_num : Nat.Coprime 3 2).dvd_of_dvd_mul_left ⟨x / 2, hxy.symm⟩)
        (by omega))
    | exact False.elim (contra x y hxD.1 hyD.1 (by omega) ⟨3, by omega⟩)
    | exact False.elim (contra y x hyD.1 hxD.1 (by omega) ⟨3, by omega⟩)
    | exact False.elim (contra x y hxD.1 hyD.1 (by omega) ⟨2, by omega⟩)
    | exact False.elim (contra y x hyD.1 hxD.1 (by omega) ⟨2, by omega⟩)
    | exact False.elim (contra x y hxD.1 hyD.1 (by omega) ⟨4, by omega⟩)
    | exact False.elim (contra y x hyD.1 hxD.1 (by omega) ⟨4, by omega⟩)
    | exact False.elim (contra x y hxD.1 hyD.1 (by omega) ⟨6, by omega⟩)
    | exact False.elim (contra y x hyD.1 hxD.1 (by omega) ⟨6, by omega⟩)

/-- The compressed copy of the lower half used in Bedert's `B₂`. -/
def stepThreeImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (lowHalf A N).image (stepThreeCompress N)

def stepThreeImageLeft (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (stepThreeImage A N).filter fun z ↦ z ≤ N / 3

def stepThreeImageRight (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (stepThreeImage A N).filter fun z ↦ N / 3 < z

@[simp] lemma mem_stepThreeImage {A : Finset ℕ} {N z : ℕ} :
    z ∈ stepThreeImage A N ↔
      ∃ x ∈ A, 2 * x ≤ N ∧ stepThreeCompress N x = z := by
  simp only [stepThreeImage, mem_image, mem_lowHalf]
  constructor
  · rintro ⟨x, ⟨hxA, hxN⟩, hxz⟩
    exact ⟨x, hxA, hxN, hxz⟩
  · rintro ⟨x, hxA, hxN, hxz⟩
    exact ⟨x, ⟨hxA, hxN⟩, hxz⟩

@[simp] lemma mem_stepThreeImageLeft {A : Finset ℕ} {N z : ℕ} :
    z ∈ stepThreeImageLeft A N ↔ z ∈ stepThreeImage A N ∧ z ≤ N / 3 := by
  simp [stepThreeImageLeft]

@[simp] lemma mem_stepThreeImageRight {A : Finset ℕ} {N z : ℕ} :
    z ∈ stepThreeImageRight A N ↔ z ∈ stepThreeImage A N ∧ N / 3 < z := by
  simp [stepThreeImageRight]

lemma stepThreeImage_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hno3 : ∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False) :
    (stepThreeImage A N).card = (lowHalf A N).card := by
  apply card_image_iff.mpr
  apply stepThreeCompress_injOn hP
  · intro x hx
    exact mem_lowHalf.mp hx
  · exact hno3

lemma stepThreeImage_subset_window {A : Finset ℕ} {N : ℕ}
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x) :
    stepThreeImage A N ⊆ Icc (N / 4 + 1) (N / 2) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
  exact stepThreeCompress_mem_window (hsmall x hx) (mem_lowHalf.mp hx).2

lemma card_stepThreeImage_left_add_right (A : Finset ℕ) (N : ℕ) :
    (stepThreeImageLeft A N).card + (stepThreeImageRight A N).card =
      (stepThreeImage A N).card := by
  have hd : Disjoint (stepThreeImageLeft A N) (stepThreeImageRight A N) := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    have hl := mem_stepThreeImageLeft.mp hzL
    have hr := mem_stepThreeImageRight.mp hzR
    omega
  have hu : stepThreeImageLeft A N ∪ stepThreeImageRight A N =
      stepThreeImage A N := by
    ext z
    simp only [mem_union, mem_stepThreeImageLeft, mem_stepThreeImageRight]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      exact (le_or_gt z (N / 3)).imp (And.intro hz) (And.intro hz)
  rw [← card_union_of_disjoint hd, hu]

lemma stepThreeImageLeft_spec {A : Finset ℕ} {N z : ℕ}
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x)
    (hz : z ∈ stepThreeImageLeft A N) :
    z ∈ A ∧ z % 2 = 1 ∧ N < 4 * z ∧ 3 * z ≤ N := by
  have hz' := mem_stepThreeImageLeft.mp hz
  obtain ⟨x, hx, hzx⟩ := mem_image.mp hz'.1
  have hs := stepThreeCompress_left (hsmall x hx) (by simpa [hzx] using hz'.2)
  have hzx' : z = x := hzx.symm.trans hs.1
  have hxA := (mem_lowHalf.mp hx).1
  rw [hzx']
  exact ⟨hxA, hs.2⟩

lemma stepThreeImageRight_has_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ stepThreeImageRight A N) :
    ∃ x ∈ A, x ≤ N / 2 ∧ x ∣ 4 * z := by
  obtain ⟨x, hxA, hxN, hzx⟩ := mem_stepThreeImage.mp
    (mem_stepThreeImageRight.mp hz).1
  refine ⟨x, hxA, by omega, ?_⟩
  rw [← hzx]
  exact dvd_four_stepThreeCompress N x

lemma stepThreeImageRight_has_divisor_two {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ stepThreeImageRight A N) :
    ∃ x ∈ A, x ≤ N / 2 ∧ x ∣ 2 * z := by
  obtain ⟨x, hxA, hxN, hzx⟩ := mem_stepThreeImage.mp
    (mem_stepThreeImageRight.mp hz).1
  refine ⟨x, hxA, by omega, ?_⟩
  rw [← hzx]
  exact dvd_two_stepThreeCompress N x

lemma card_modThree_parts (S : Finset ℕ) :
    (residue S 0 3).card + (residue S 1 3).card +
      (residue S 2 3).card = S.card := by
  let f : ℕ → ℕ := fun x ↦ x % 3
  have hmap : (S : Set ℕ).MapsTo f (range 3) := by
    intro x hx
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have h := Finset.card_eq_sum_card_fiberwise hmap
  simp only [sum_range_succ, sum_range_zero] at h
  have heq (r : ℕ) (hr : r < 3) : S.filter (fun x ↦ f x = r) = residue S r 3 := by
    ext x
    simp [f, residue, Nat.mod_eq_of_lt hr]
  rw [heq 0 (by omega), heq 1 (by omega), heq 2 (by omega)] at h
  omega

/-- Any odd lower-window packing set and either odd residue class modulo
four in the top third fit into one twelfth of the ambient interval. -/
lemma oddLeft_add_high_odd_le {A B : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hBI : B ⊆ Icc (2 * N / 9 + 1) (N / 3))
    (hBodd : ∀ z ∈ B, z % 2 = 1)
    (hBpack : ∀ z ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 6 * z)
    (hi : i = 1 ∨ i = 3) :
    B.card + (modFourPart (highThird A N) i).card ≤ N / 12 + 10 := by
  let H := highThird A N
  let K := modFourPart H i
  let K₀ := residue K 0 3
  let K₁ := residue K 1 3
  let K₂ := residue K 2 3
  let S := zmodFiber (H + H) (6 : ZMod 12)
  let U := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (6 : ZMod 12)
  have hKpart := card_modThree_parts K
  change K₀.card + K₁.card + K₂.card = K.card at hKpart
  have hKI : K ⊆ Icc (2 * N / 3 + 1) N :=
    (filter_subset _ _).trans (highThird_subset_interval hsub)
  have hHpack : ∀ x ∈ H, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hBU : B.image (fun z ↦ 6 * z) ⊆ U := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzI := mem_Icc.mp (hBI hz)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (6 * z) 6 12).mpr
      have hzmod := Nat.mod_lt z (by omega : 0 < 2)
      have hzodd := hBodd z hz
      omega
  have hSU : S ⊆ U := by
    intro w hw
    have hw' := mem_zmodFiber.mp hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hw'.1
    have hxI := mem_Icc.mp (highThird_subset_interval hsub hx)
    have hyI := mem_Icc.mp (highThird_subset_interval hsub hy)
    exact mem_zmodFiber.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hw'.2⟩
  have hpack := packing (k := 6) (t := N / 2) (by omega) hP hBpack hHpack
    (filter_subset _ _) hBU hSU
  have hUI : U ⊆ Icc (4 * N / 3 + 1) (2 * N) := filter_subset _ _
  have hUres : ∀ z ∈ U, (z : ZMod 12) = 6 := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hcap := mul_card_fixed_zmod_le (6 : ZMod 12) hUI hUres
  have hSI : S ⊆ Icc (4 * N / 3 + 1) (2 * N) := hSU.trans hUI
  have hSres : ∀ z ∈ S, (z : ZMod 12) = 6 := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hScap := mul_card_fixed_zmod_le (6 : ZMod 12) hSI hSres
  change B.card + S.card ≤ U.card at hpack
  change 12 * U.card ≤ (2 * N + 12) - (4 * N / 3 + 1) at hcap
  change 12 * S.card ≤ (2 * N + 12) - (4 * N / 3 + 1) at hScap
  have hBoddZ : ∀ z ∈ B, (z : ZMod 2) = 1 := by
    intro z hz
    apply (ZMod.natCast_eq_natCast_iff' z 1 2).mpr
    exact hBodd z hz
  have hBcap := mul_card_fixed_zmod_le (1 : ZMod 2) hBI hBoddZ
  change 2 * B.card ≤ (N / 3 + 2) - (2 * N / 9 + 1) at hBcap
  have hsum12 {X Y : Finset ℕ} (hX : X ⊆ K) (hY : Y ⊆ K)
      (hX3 : ∀ x ∈ X, x % 3 = 1) (hY3 : ∀ y ∈ Y, y % 3 = 2) :
      X + Y ⊆ S := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hxK := mem_modFourPart.mp (hX hx)
    have hyK := mem_modFourPart.mp (hY hy)
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hxK.1 hyK.1
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) 6 12).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _
      · rw [Nat.add_mod, hX3 x hx, hY3 y hy]
      · rcases hi with rfl | rfl <;> omega
  have hself0 : K₀ + K₀ ⊆ S := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hxK := mem_residue.mp hx
    have hyK := mem_residue.mp hy
    have hx4 := (mem_modFourPart.mp hxK.1).2
    have hy4 := (mem_modFourPart.mp hyK.1).2
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add (mem_modFourPart.mp hxK.1).1
        (mem_modFourPart.mp hyK.1).1
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) 6 12).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _
      · have hx0 : x % 3 = 0 := by simpa using hxK.2
        have hy0 : y % 3 = 0 := by simpa using hyK.2
        rw [Nat.add_mod, hx0, hy0]
      · rcases hi with rfl | rfl <;> omega
  have h12sub : K₁ + K₂ ⊆ S := hsum12 (filter_subset _ _) (filter_subset _ _)
    (fun x hx ↦ by simpa using (mem_residue.mp hx).2)
    (fun y hy ↦ by simpa using (mem_residue.mp hy).2)
  by_cases hK₁ : K₁.Nonempty
  · by_cases hK₂ : K₂.Nonempty
    · have h12cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hK₁ hK₂
      have h12card := card_le_card h12sub
      have h12 : K₁.card + K₂.card ≤ S.card + 1 := by
        change K₁.card + K₂.card - 1 ≤ (K₁ + K₂).card at h12cd
        omega
      have h00 : 2 * K₀.card ≤ S.card + 1 := by
        obtain hK₀ | hK₀ := K₀.eq_empty_or_nonempty
        · rw [hK₀]
          simp
        · have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hK₀ hK₀
          have hc := card_le_card hself0
          omega
      have hKlower : 2 * K.card ≤ 3 * (S.card + 1) := by omega
      change B.card + K.card ≤ N / 12 + 10
      omega
    · have hK₂card : K₂.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hK₂)
      have hK₁I : K₁ ⊆ Icc (2 * N / 3 + 1) N := (filter_subset _ _).trans hKI
      obtain ⟨r, hr⟩ : ∃ r : ZMod 12, ∀ x ∈ K₁, (x : ZMod 12) = r := by
        refine ⟨((3 * i - 2) : ℕ), ?_⟩
        intro x hx
        have hxK := mem_modFourPart.mp (mem_residue.mp hx).1
        apply (ZMod.natCast_eq_natCast_iff' x (3 * i - 2) 12).mpr
        apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
        constructor <;> change _ % _ = _ % _
        · rcases hi with rfl | rfl <;> simpa using (mem_residue.mp hx).2
        · rcases hi with rfl | rfl <;> omega
      have hK₁cap := mul_card_fixed_zmod_le r hK₁I hr
      have h00 : 2 * K₀.card ≤ S.card + 1 := by
        obtain hK₀ | hK₀ := K₀.eq_empty_or_nonempty
        · rw [hK₀]
          simp
        · have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hK₀ hK₀
          have hc := card_le_card hself0
          omega
      change 12 * K₁.card ≤ (N + 12) - (2 * N / 3 + 1) at hK₁cap
      change B.card + K.card ≤ N / 12 + 10
      omega
  · have hK₁card : K₁.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hK₁)
    have hK₂I : K₂ ⊆ Icc (2 * N / 3 + 1) N := (filter_subset _ _).trans hKI
    obtain ⟨r, hr⟩ : ∃ r : ZMod 12, ∀ x ∈ K₂, (x : ZMod 12) = r := by
      refine ⟨((3 * i + 2) : ℕ), ?_⟩
      intro x hx
      have hxK := mem_modFourPart.mp (mem_residue.mp hx).1
      apply (ZMod.natCast_eq_natCast_iff' x (3 * i + 2) 12).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _
      · rcases hi with rfl | rfl <;> simpa using (mem_residue.mp hx).2
      · rcases hi with rfl | rfl <;> omega
    have hK₂cap := mul_card_fixed_zmod_le r hK₂I hr
    have h00 : 2 * K₀.card ≤ S.card + 1 := by
      obtain hK₀ | hK₀ := K₀.eq_empty_or_nonempty
      · rw [hK₀]
        simp
      · have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hK₀ hK₀
        have hc := card_le_card hself0
        omega
    change 12 * K₂.card ≤ (N + 12) - (2 * N / 3 + 1) at hK₂cap
    change B.card + K.card ≤ N / 12 + 10
    omega

/-- The left part of `B₂` is the principal instance of the abstract odd
lower-window packing estimate. -/
lemma stepThree_left_add_high_odd_le {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x)
    (hi : i = 1 ∨ i = 3) :
    (stepThreeImageLeft A N).card +
      (modFourPart (highThird A N) i).card ≤ N / 12 + 10 := by
  let B := stepThreeImageLeft A N
  have hspec : ∀ z ∈ B, z ∈ A ∧ z % 2 = 1 ∧ N < 4 * z ∧ 3 * z ≤ N := by
    intro z hz
    exact stepThreeImageLeft_spec hsmall hz
  apply oddLeft_add_high_odd_le hP hsub
  · intro z hz
    have hz' := hspec z hz
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro z hz
    exact (hspec z hz).2.1
  · intro z hz
    have hz' := hspec z hz
    exact ⟨z, hz'.1, by omega, dvd_mul_left z 6⟩
  · exact hi

/-- Twice the right part of `B₂` packs against the even part of the top
third. -/
lemma stepThree_right_add_high_even_le {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x) :
    (stepThreeImageRight A N).card +
      (parityPart (highThird A N) 0).card ≤ N / 6 + 4 := by
  let B := stepThreeImageRight A N
  let E := parityPart (highThird A N) 0
  let T := B.image fun z ↦ 2 * z
  have hTcard : T.card = B.card := by
    apply card_image_iff.mpr
    intro x hx y hy hxy
    change 2 * x = 2 * y at hxy
    omega
  have hTI : T ⊆ Icc (2 * N / 3 + 1) N := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzR := mem_stepThreeImageRight.mp hz
    have hzI := mem_Icc.mp (stepThreeImage_subset_window hsmall hzR.1)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hEI : E ⊆ Icc (2 * N / 3 + 1) N :=
    (filter_subset _ _).trans (highThird_subset_interval hsub)
  have hdisj : Disjoint T E := by
    rw [Finset.disjoint_left]
    intro w hwT hwE
    obtain ⟨z, hz, hzw⟩ := mem_image.mp hwT
    obtain ⟨a, haA, haN, hadiv⟩ := stepThreeImageRight_has_divisor_two hz
    have hwH := mem_highThird.mp (mem_parityPart.mp hwE).1
    apply hP.not_dvd_of_lt haA hwH.1 (by omega)
    simpa [hzw] using hadiv
  let W := T ∪ E
  have hWI : W ⊆ Icc (2 * N / 3 + 1) N := union_subset hTI hEI
  have hWeven : ∀ w ∈ W, (w : ZMod 2) = 0 := by
    intro w hw
    rcases mem_union.mp hw with hw | hw
    · obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right 2 z
    · apply (ZMod.natCast_eq_natCast_iff' w 0 2).mpr
      simpa using (mem_parityPart.mp hw).2
  have hcap := mul_card_fixed_zmod_le (0 : ZMod 2) hWI hWeven
  have hWcard : W.card = T.card + E.card := card_union_of_disjoint hdisj
  change 2 * W.card ≤ (N + 2) - (2 * N / 3 + 1) at hcap
  change B.card + E.card ≤ N / 6 + 4
  omega

/-- With small multiples of three excluded, the odd left part of `B₂`
occupies only the two coprime residue classes `1,5 (mod 6)`. -/
lemma stepThree_left_card_le {A : Finset ℕ} {N : ℕ}
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x)
    (hno3 : ∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False) :
    36 * (stepThreeImageLeft A N).card ≤ N + 72 := by
  let B := stepThreeImageLeft A N
  let B₁ := residue B 1 6
  let B₅ := residue B 5 6
  have hBI : B ⊆ Icc (N / 4 + 1) (N / 3) := by
    intro z hz
    have hz' := stepThreeImageLeft_spec hsmall hz
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hpart : B₁.card + B₅.card = B.card := by
    have hd : Disjoint B₁ B₅ := by
      rw [Finset.disjoint_left]
      intro z hz1 hz5
      have h1 := (mem_residue.mp hz1).2
      have h5 := (mem_residue.mp hz5).2
      omega
    have hu : B₁ ∪ B₅ = B := by
      change residue B 1 6 ∪ residue B 5 6 = B
      ext z
      simp only [mem_union, mem_residue]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        have hz' := stepThreeImageLeft_spec hsmall hz
        have hzlow : z ∈ lowHalf A N := mem_lowHalf.mpr ⟨hz'.1, by omega⟩
        have hz3 : z % 3 ≠ 0 := by
          intro heq
          exact hno3 z hzlow (Nat.dvd_of_mod_eq_zero heq) (by omega)
        have hz6 := Nat.mod_lt z (by omega : 0 < 6)
        have hzpar : z % 6 % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd z (by omega : 2 ∣ 6)]
          exact hz'.2.1
        have hzthree : z % 6 % 3 ≠ 0 := by
          rw [Nat.mod_mod_of_dvd z (by omega : 3 ∣ 6)]
          exact hz3
        interval_cases z % 6 <;> simp_all
    rw [← card_union_of_disjoint hd, hu]
  have hcap (r : ℕ) (hr : r = 1 ∨ r = 5) :
      6 * (residue B r 6).card ≤ (N / 3 + 6) - (N / 4 + 1) := by
    have hI : residue B r 6 ⊆ Icc (N / 4 + 1) (N / 3) :=
      (filter_subset _ _).trans hBI
    have hres : ∀ z ∈ residue B r 6, (z : ZMod 6) = (r : ZMod 6) := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z r 6).mpr
      exact (mem_residue.mp hz).2
    exact mul_card_fixed_zmod_le (r : ZMod 6) hI hres
  have h1 := hcap 1 (Or.inl rfl)
  have h5 := hcap 5 (Or.inr rfl)
  change 6 * B₁.card ≤ (N / 3 + 6) - (N / 4 + 1) at h1
  change 6 * B₅.card ≤ (N / 3 + 6) - (N / 4 + 1) at h5
  change 36 * B.card ≤ N + 72
  omega

/-- Bedert's `B₂` dichotomy.  If both odd top-third classes occur, their
cross-sum (together with the two even self-sums) packs against the right
part.  If an odd class is absent, direct parity packing controls the whole
compressed lower half together with the top third. -/
lemma stepThree_image_dichotomy {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x) :
    2 * (stepThreeImageRight A N).card + (highThird A N).card ≤ N / 3 + 12 ∨
      (stepThreeImage A N).card + (highThird A N).card ≤ N / 4 + 24 := by
  let B := stepThreeImage A N
  let Bₗ := stepThreeImageLeft A N
  let Bᵣ := stepThreeImageRight A N
  let H := highThird A N
  let H₀ := modFourPart H 0
  let H₁ := modFourPart H 1
  let H₂ := modFourPart H 2
  let H₃ := modFourPart H 3
  let E := parityPart H 0
  let O := parityPart H 1
  have hBpart := card_stepThreeImage_left_add_right A N
  change Bₗ.card + Bᵣ.card = B.card at hBpart
  have hHfour : H₀.card + H₁.card + H₂.card + H₃.card = H.card := by
    let f : ℕ → ℕ := fun x ↦ x % 4
    have hmap : (H : Set ℕ).MapsTo f (range 4) := by
      intro x hx
      exact mem_range.mpr (Nat.mod_lt _ (by omega))
    have h := Finset.card_eq_sum_card_fiberwise hmap
    simp only [sum_range_succ, sum_range_zero] at h
    have heq (r : ℕ) (hr : r < 4) : H.filter (fun x ↦ f x = r) = modFourPart H r := by
      ext x
      simp [f, modFourPart, Nat.mod_eq_of_lt hr]
    rw [heq 0 (by omega), heq 1 (by omega), heq 2 (by omega),
      heq 3 (by omega)] at h
    change H.card = 0 + H₀.card + H₁.card + H₂.card + H₃.card at h
    omega
  have hHE := card_parity_parts H
  change E.card + O.card = H.card at hHE
  by_cases h1 : H₁.Nonempty
  · by_cases h3 : H₃.Nonempty
    · left
      let S := zmodFiber (H + H) (0 : ZMod 4)
      let U := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 4)
      have h13 : H₁ + H₃ ⊆ S := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
        have hx' := mem_modFourPart.mp hx
        have hy' := mem_modFourPart.mp hy
        apply mem_zmodFiber.mpr
        constructor
        · exact Finset.add_mem_add hx'.1 hy'.1
        · rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
            Nat.add_mod, hx'.2, hy'.2]
      have h00 : H₀ + H₀ ⊆ S := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
        have hx' := mem_modFourPart.mp hx
        have hy' := mem_modFourPart.mp hy
        apply mem_zmodFiber.mpr
        exact ⟨Finset.add_mem_add hx'.1 hy'.1, by
          rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
            Nat.add_mod, hx'.2, hy'.2]⟩
      have h22 : H₂ + H₂ ⊆ S := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
        have hx' := mem_modFourPart.mp hx
        have hy' := mem_modFourPart.mp hy
        apply mem_zmodFiber.mpr
        exact ⟨Finset.add_mem_add hx'.1 hy'.1, by
          rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
            Nat.add_mod, hx'.2, hy'.2]⟩
      have h13cd := cauchy_davenport_add_of_linearOrder_isCancelAdd h1 h3
      have h13c := card_le_card h13
      have h13lower : H₁.card + H₃.card ≤ S.card + 1 := by omega
      have h00lower : 2 * H₀.card ≤ S.card + 1 := by
        obtain he | he := H₀.eq_empty_or_nonempty
        · rw [he]
          simp
        · have hc := cauchy_davenport_add_of_linearOrder_isCancelAdd he he
          have hs := card_le_card h00
          omega
      have h22lower : 2 * H₂.card ≤ S.card + 1 := by
        obtain he | he := H₂.eq_empty_or_nonempty
        · rw [he]
          simp
        · have hc := cauchy_davenport_add_of_linearOrder_isCancelAdd he he
          have hs := card_le_card h22
          omega
      have hHlower : H.card ≤ 2 * (S.card + 1) := by omega
      have hBdiv : ∀ z ∈ Bᵣ, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * z := by
        intro z hz
        exact stepThreeImageRight_has_divisor hz
      have hHhigh : ∀ x ∈ H, x ∈ A ∧ N / 2 < x := by
        intro x hx
        have hx' := mem_highThird.mp hx
        exact ⟨hx'.1, by omega⟩
      have hBU : Bᵣ.image (fun z ↦ 4 * z) ⊆ U := by
        intro w hw
        obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
        have hzR := mem_stepThreeImageRight.mp hz
        have hzI := mem_Icc.mp (stepThreeImage_subset_window hsmall hzR.1)
        have hzright := hzR.2
        apply mem_zmodFiber.mpr
        exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by
          rw [ZMod.natCast_eq_zero_iff]
          exact dvd_mul_right 4 z⟩
      have hSU : S ⊆ U := by
        intro w hw
        have hw' := mem_zmodFiber.mp hw
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hw'.1
        have hxI := mem_Icc.mp (highThird_subset_interval hsub hx)
        have hyI := mem_Icc.mp (highThird_subset_interval hsub hy)
        exact mem_zmodFiber.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hw'.2⟩
      have hp := packing (k := 4) (t := N / 2) (by omega) hP hBdiv hHhigh
        (filter_subset _ _) hBU hSU
      have hUI : U ⊆ Icc (4 * N / 3 + 1) (2 * N) := filter_subset _ _
      have hUres : ∀ z ∈ U, (z : ZMod 4) = 0 := by
        intro z hz
        exact (mem_zmodFiber.mp hz).2
      have hcap := mul_card_fixed_zmod_le (0 : ZMod 4) hUI hUres
      change Bᵣ.card + S.card ≤ U.card at hp
      change 4 * U.card ≤ (2 * N + 4) - (4 * N / 3 + 1) at hcap
      change 2 * Bᵣ.card + H.card ≤ N / 3 + 12
      omega
    · right
      have hBL := stepThree_left_add_high_odd_le hP hsub hsmall (i := 1) (Or.inl rfl)
      have hH₃card : H₃.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h3)
      have hOdd : O.card = H₁.card := by
        have hp := card_modFour_one_add_three H
        change H₁.card + H₃.card = O.card at hp
        omega
      have hBE := stepThree_right_add_high_even_le hP hsub hsmall
      change Bₗ.card + H₁.card ≤ N / 12 + 10 at hBL
      change Bᵣ.card + E.card ≤ N / 6 + 4 at hBE
      change B.card + H.card ≤ N / 4 + 24
      omega
  · right
    have hBL := stepThree_left_add_high_odd_le hP hsub hsmall (i := 3) (Or.inr rfl)
    have hH₁card : H₁.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h1)
    have hOdd : O.card = H₃.card := by
      have hp := card_modFour_one_add_three H
      change H₁.card + H₃.card = O.card at hp
      omega
    have hBE := stepThree_right_add_high_even_le hP hsub hsmall
    change Bₗ.card + H₃.card ≤ N / 12 + 10 at hBL
    change Bᵣ.card + E.card ≤ N / 6 + 4 at hBE
    change B.card + H.card ≤ N / 4 + 24
    omega

/-- Division by three turns a step-three progression in the nonzero
upper-half sumset into a genuine interval in `thirdSumQuotient`. -/
lemma stepThree_divided_interval {A : Finset ℕ} {N a len : ℕ}
    (ha3 : 3 ∣ a)
    (hQ : natAP a 3 len ⊆
      upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    natAP (a / 3) 1 len ⊆ thirdSumQuotient A N := by
  intro z hz
  obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
  apply mem_quotientPart.mpr
  refine ⟨a + 3 * j, ?_, ?_, ?_⟩
  · apply mem_zmodFiber.mpr
    constructor
    · apply Finset.add_subset_add
        (show upperHalfResidue A N 1 ⊆ upperHalf A N from filter_subset _ _)
        (show upperHalfResidue A N 2 ⊆ upperHalf A N from filter_subset _ _)
      apply hQ
      exact mem_natAP.mpr ⟨j, hj, rfl⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨a / 3 + j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
  · exact ⟨a / 3 + j, by
      have := Nat.mul_div_cancel' ha3
      omega⟩
  · have heq : a + 3 * j = 3 * (a / 3 + j) := by
      have := Nat.mul_div_cancel' ha3
      omega
    rw [heq]
    simpa using hz

/-- The first consequences of a step-three progression: the whole first
ninth is empty and there are no multiples of three in the first third. -/
lemma stepThree_small_exclusions {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha3 : 3 ∣ a)
    (hQ : natAP a 3 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    (∀ x ∈ lowHalf A N, N / 9 < x) ∧
      (∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False) := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let len := V₁.card + V₂.card - 1
  have hp₁ : 0 < V₁.card := card_pos.mpr hV₁
  have hp₂ : 0 < V₂.card := card_pos.mpr hV₂
  have hlarge : N / 9 + 1 ≤ V₁.card + V₂.card := by
    change (N + 1) / 2 < 3 * V.card at htail
    change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
    omega
  have hlen : N / 9 ≤ len := by
    dsimp [len]
    omega
  have hI : natAP (a / 3) 1 len ⊆ thirdSumQuotient A N := by
    apply stepThree_divided_interval ha3
    simpa [len, V₁, V₂] using hQ
  constructor
  · intro x hx
    by_contra hn
    have hxsmall : x ≤ N / 9 := by omega
    exact not_mem_of_le_thirdSum_interval hP hsub hI (mem_lowHalf.mp hx).1
      (by omega) (mem_lowHalf.mp hx).2
  · intro x hx hx3 hxthird
    have hxlen : x ≤ 3 * len := by omega
    exact not_mem_three_of_le_thirdSum_interval hP hsub hI
      (mem_lowHalf.mp hx).1 hx3 hxlen (mem_lowHalf.mp hx).2

/-- Unless the desired additive-constant bound already holds, the `B₂`
dichotomy bootstraps the upper half to size at least `5N/24-O(1)`. -/
lemma stepThree_bootstrap {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hmid : 2 * (middleSixth A N).card < (highThird A N).card + 3)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 3 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    3 * A.card ≤ N + 300 ∨
      5 * N ≤ 24 * (upperHalf A N).card + 20000 := by
  let L := lowHalf A N
  let V := upperHalf A N
  let Y := middleSixth A N
  let H := highThird A N
  let B := stepThreeImage A N
  let Bₗ := stepThreeImageLeft A N
  let Bᵣ := stepThreeImageRight A N
  obtain ⟨hsmall, hno3⟩ := stepThree_small_exclusions hP hsub hV₁ hV₂
    htail hdom ha3 hQ
  have hBcard := stepThreeImage_card hP hno3
  change B.card = L.card at hBcard
  have hBpart := card_stepThreeImage_left_add_right A N
  change Bₗ.card + Bᵣ.card = B.card at hBpart
  have hBLcap := stepThree_left_card_le hsmall hno3
  change 36 * Bₗ.card ≤ N + 72 at hBLcap
  have hLV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hLV
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  have hVcard : V.card = Y.card + H.card := hYH.symm
  change 6 * H.card < N + 144 at hcase3
  change 2 * Y.card < H.card + 3 at hmid
  rcases stepThree_image_dichotomy hP hsub hsmall with hright | hwhole
  · change 2 * Bᵣ.card + H.card ≤ N / 3 + 12 at hright
    by_cases hdone : 3 * A.card ≤ N + 300
    · exact Or.inl hdone
    · right
      rw [hVcard]
      omega
  · change B.card + H.card ≤ N / 4 + 24 at hwhole
    left
    omega

lemma three_mul_card_nonthree_le {S : Finset ℕ} {L U : ℕ}
    (hI : S ⊆ Icc L U) (h3 : ∀ z ∈ S, z % 3 ≠ 0) :
    3 * S.card ≤ 2 * ((U + 3) - L) := by
  let S₁ := residue S 1 3
  let S₂ := residue S 2 3
  have hp : S₁.card + S₂.card = S.card := by
    have hd : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have h1 := (mem_residue.mp hz1).2
      have h2 := (mem_residue.mp hz2).2
      omega
    have hu : S₁ ∪ S₂ = S := by
      change residue S 1 3 ∪ residue S 2 3 = S
      ext z
      simp only [mem_union, mem_residue]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        have hm := Nat.mod_lt z (by omega : 0 < 3)
        have hn := h3 z hz
        interval_cases z % 3 <;> simp_all
    rw [← card_union_of_disjoint hd, hu]
  have hcap (r : ℕ) :
      3 * (residue S r 3).card ≤ (U + 3) - L := by
    have hSI : residue S r 3 ⊆ Icc L U := (filter_subset _ _).trans hI
    have hr : ∀ z ∈ residue S r 3, (z : ZMod 3) = (r : ZMod 3) := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z r 3).mpr
      exact (mem_residue.mp hz).2
    exact mul_card_fixed_zmod_le (r : ZMod 3) hSI hr
  have h1 := hcap 1
  have h2 := hcap 2
  change 3 * S₁.card ≤ (U + 3) - L at h1
  change 3 * S₂.card ≤ (U + 3) - L at h2
  omega

lemma six_mul_card_even_nonthree_le {S : Finset ℕ} {L U : ℕ}
    (hI : S ⊆ Icc L U) (heven : ∀ z ∈ S, z % 2 = 0)
    (h3 : ∀ z ∈ S, z % 3 ≠ 0) :
    6 * S.card ≤ 2 * ((U + 6) - L) := by
  let S₂ := residue S 2 6
  let S₄ := residue S 4 6
  have hp : S₂.card + S₄.card = S.card := by
    have hd : Disjoint S₂ S₄ := by
      rw [Finset.disjoint_left]
      intro z hz2 hz4
      have h2 := (mem_residue.mp hz2).2
      have h4 := (mem_residue.mp hz4).2
      omega
    have hu : S₂ ∪ S₄ = S := by
      change residue S 2 6 ∪ residue S 4 6 = S
      ext z
      simp only [mem_union, mem_residue]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        have hm := Nat.mod_lt z (by omega : 0 < 6)
        have h2 : z % 6 % 2 = 0 := by
          rw [Nat.mod_mod_of_dvd z (by omega : 2 ∣ 6)]
          exact heven z hz
        have hthree : z % 6 % 3 ≠ 0 := by
          rw [Nat.mod_mod_of_dvd z (by omega : 3 ∣ 6)]
          exact h3 z hz
        interval_cases z % 6 <;> simp_all
    rw [← card_union_of_disjoint hd, hu]
  have hcap (r : ℕ) :
      6 * (residue S r 6).card ≤ (U + 6) - L := by
    have hSI : residue S r 6 ⊆ Icc L U := (filter_subset _ _).trans hI
    have hr : ∀ z ∈ residue S r 6, (z : ZMod 6) = (r : ZMod 6) := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z r 6).mpr
      exact (mem_residue.mp hz).2
    exact mul_card_fixed_zmod_le (r : ZMod 6) hSI hr
  have h2 := hcap 2
  have h4 := hcap 4
  change 6 * S₂.card ≤ (U + 6) - L at h2
  change 6 * S₄.card ≤ (U + 6) - L at h4
  omega

lemma scaledMove_eq_self_of_mem_central {N x : ℕ} (hx : N < 3 * x) :
    scaledMove 0 N 3 x = x := by
  have hxpos : 0 < x := by omega
  have he : scaledWindowExp 0 N 3 x = 0 := by
    by_contra hn
    have hp : 0 < scaledWindowExp 0 N 3 x := by omega
    have hm := scaledWindowExp_min (b := 0) (T := N) (q := 3) (a := x)
      (by omega) hxpos (j := 0) hp
    simp at hm
    omega
  simp [scaledMove, he]

noncomputable def centralRemainder (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (centralImage A N).filter fun z ↦ z ∉ middleSixth A N

lemma middleSixth_subset_centralImage {A : Finset ℕ} {N : ℕ} :
    middleSixth A N ⊆ centralImage A N := by
  intro x hx
  have hx' := mem_middleSixth.mp hx
  apply centralImage_mem_iff.mpr
  exact ⟨x, hx'.1, hx'.2.2, scaledMove_eq_self_of_mem_central (by omega)⟩

lemma card_centralRemainder_add_middle (A : Finset ℕ) (N : ℕ) :
    (centralRemainder A N).card + (middleSixth A N).card =
      (centralImage A N).card := by
  have hd : Disjoint (centralRemainder A N) (middleSixth A N) := by
    rw [Finset.disjoint_left]
    intro z hzD hzY
    exact (mem_filter.mp hzD).2 hzY
  have hu : centralRemainder A N ∪ middleSixth A N = centralImage A N := by
    ext z
    simp only [centralRemainder, mem_union, mem_filter]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact middleSixth_subset_centralImage h
    · intro hz
      by_cases hy : z ∈ middleSixth A N
      · exact Or.inr hy
      · exact Or.inl ⟨hz, hy⟩
  rw [← card_union_of_disjoint hd, hu]

lemma centralImage_not_three_below_interval {A : Finset ℕ} {N q len z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hI : natAP q 1 len ⊆ thirdSumQuotient A N)
    (hzB : z ∈ centralImage A N) (hz3 : 3 ∣ z)
    (hzlen : z ≤ 3 * len) (hzhalf : 2 * z ≤ N) : False := by
  obtain ⟨x, hxA, hxN, hxz⟩ := centralImage_mem_iff.mp hzB
  have hxpos := hP.pos_of_mem hsub hxA
  have hzpos : 0 < z := by
    rw [← hxz, scaledMove]
    positivity
  have hxdvd : x ∣ z := by rw [← hxz]; exact dvd_scaledMove 0 N 3 x
  have hxle : x ≤ z := Nat.le_of_dvd hzpos hxdvd
  have hx3 : 3 ∣ x := by
    rw [← hxz, scaledMove] at hz3
    rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp hz3 with hp | hp
    · have : 3 ∣ 2 := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hp
      norm_num at this
    · exact hp
  exact not_mem_three_of_le_thirdSum_interval hP hsub hI hxA hx3
    (by omega) (by omega)

lemma centralRemainder_upper_spec {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hno3 : ∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False)
    (hzD : z ∈ centralRemainder A N) (hzupper : N < 2 * z) :
    z % 2 = 0 ∧ z % 3 ≠ 0 := by
  have hzD' := mem_filter.mp hzD
  have hzI := mem_ratSection.mp (centralImage_subset_window hP hsub hzD'.1)
  obtain ⟨x, hxA, hxN, hxz⟩ := centralImage_mem_iff.mp hzD'.1
  have hxpos := hP.pos_of_mem hsub hxA
  have hzpos : 0 < z := by omega
  have hxdvd : x ∣ z := by rw [← hxz]; exact dvd_scaledMove 0 N 3 x
  have hxle : x ≤ z := Nat.le_of_dvd hzpos hxdvd
  have hxne : x ≠ z := by
    intro heq
    apply hzD'.2
    apply mem_middleSixth.mpr
    exact ⟨by simpa [heq] using hxA, hzupper, hzI.2.2⟩
  have hxlt : x < z := lt_of_le_of_ne hxle hxne
  have htwox : 2 * x ≤ z := by
    obtain ⟨k, hk⟩ := hxdvd
    have hk2 : 2 ≤ k := by
      by_contra hn
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl <;> simp_all
    calc
      2 * x = x * 2 := by omega
      _ ≤ x * k := Nat.mul_le_mul_left x hk2
      _ = z := hk.symm
  constructor
  · by_contra hodd
    have hmod := Nat.mod_lt z (by omega : 0 < 2)
    have hzodd : z % 2 = 1 := by omega
    have heq := scaledMove_eq_self_of_odd (T := N) (q := 3) (a := x)
    apply hxne
    rw [hxz] at heq
    exact (heq hzodd).symm
  · intro hz3mod
    have hz3 : 3 ∣ z := Nat.dvd_of_mod_eq_zero hz3mod
    have hx3 : 3 ∣ x := by
      rw [← hxz, scaledMove] at hz3
      rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp hz3 with hp | hp
      · have : 3 ∣ 2 := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hp
        norm_num at this
      · exact hp
    have hxlow : x ∈ lowHalf A N := mem_lowHalf.mpr ⟨hxA, by omega⟩
    exact hno3 x hxlow hx3 (by omega)

lemma mem_natAP_one_iff {q len z : ℕ} :
    z ∈ natAP q 1 len ↔ q ≤ z ∧ z < q + len := by
  constructor
  · intro hz
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
    omega
  · rintro ⟨hl, hu⟩
    apply mem_natAP.mpr
    exact ⟨z - q, by omega, by omega⟩

lemma card_filter_lt_add_ge (S : Finset ℕ) (t : ℕ) :
    (S.filter fun z ↦ z < t).card + (S.filter fun z ↦ t ≤ z).card = S.card := by
  have hd : Disjoint (S.filter fun z ↦ z < t) (S.filter fun z ↦ t ≤ z) := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    have h₁ := (mem_filter.mp hz₁).2
    have h₂ := (mem_filter.mp hz₂).2
    omega
  have hu : (S.filter fun z ↦ z < t) ∪ (S.filter fun z ↦ t ≤ z) = S := by
    ext z
    simp only [mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      exact (lt_or_ge z t).imp (And.intro hz) (And.intro hz)
  rw [← card_union_of_disjoint hd, hu]

lemma card_filter_le_add_gt (S : Finset ℕ) (t : ℕ) :
    (S.filter fun z ↦ z ≤ t).card + (S.filter fun z ↦ t < z).card = S.card := by
  simpa [Nat.lt_add_one_iff] using card_filter_lt_add_ge S (t + 1)

/-- The complete step-three structural estimate.  The three branches are
the late-start, crossing, and noncrossing positions of the divided
interval. -/
lemma caseThree_step_three_interval {A : Finset ℕ} {N q len : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hlenpos : 0 < len)
    (hlen : 2 * (upperHalf A N).card ≤ 3 * (len + 1))
    (hinterval : natAP q 1 len ⊆ thirdSumQuotient A N) :
    3 * A.card ≤ N + 100000 := by
  let V := upperHalf A N
  let Y := middleSixth A N
  let H := highThird A N
  let B := centralImage A N
  let D := centralRemainder A N
  let I := natAP q 1 len
  have hI : I ⊆ thirdSumQuotient A N := by simpa [I] using hinterval
  have hIcard : I.card = len := card_natAP (by omega)
  have hII : I ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    hI.trans (thirdSumQuotient_subset_central hsub)
  have hqI : q ∈ I := mem_natAP.mpr ⟨0, hlenpos, by simp⟩
  have hqcentral := mem_Icc.mp (hII hqI)
  have hBI : B ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro z hz
    have hz' := mem_ratSection.mp (centralImage_subset_window hP hsub hz)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hDI : D ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    (filter_subset _ _).trans hBI
  have hdisjBI : Disjoint B I :=
    (centralImage_disjoint_thirdSumQuotient hP hsub).mono subset_rfl hI
  have hdisjDI : Disjoint D I := hdisjBI.mono (filter_subset _ _) subset_rfl
  have hBH := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hBH
  have hDY := card_centralRemainder_add_middle A N
  change D.card + Y.card = B.card at hDY
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  have hVcard : V.card = Y.card + H.card := hYH.symm
  have hDA : D.card + V.card = A.card := by omega
  change 2 * V.card ≤ 3 * (len + 1) at hlen
  have hdomlen := hlen
  by_cases hlarge : H.card + 3 ≤ 2 * Y.card
  · have hHlen : H.card ≤ len := by omega
    have hIQ : I.card ≤ (thirdSumQuotient A N).card := card_le_card hI
    have hHQ : H.card ≤ (thirdSumQuotient A N).card := by omega
    have hpack := caseThree_basic_packing hP hsub
    change B.card + (thirdSumQuotient A N).card ≤
      (Icc (N / 3 + 1) (2 * N / 3)).card at hpack
    have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
      simp
      omega
    omega
  have hmid : 2 * Y.card < H.card + 3 := by omega
  change 6 * H.card < N + 144 at hcase3
  have hnine : N / 9 ≤ len := by
    change (N + 1) / 2 < 3 * V.card at htail
    omega
  have hsmall : ∀ x ∈ lowHalf A N, N / 9 < x := by
    intro x hx
    by_contra hn
    exact not_mem_of_le_thirdSum_interval hP hsub hI (mem_lowHalf.mp hx).1
      (by omega) (mem_lowHalf.mp hx).2
  have hno3 : ∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False := by
    intro x hx hx3 hxN
    exact not_mem_three_of_le_thirdSum_interval hP hsub hI
      (mem_lowHalf.mp hx).1 hx3 (by omega) (mem_lowHalf.mp hx).2
  let C := stepThreeImage A N
  let Cₗ := stepThreeImageLeft A N
  let Cᵣ := stepThreeImageRight A N
  have hCcard := stepThreeImage_card hP hno3
  change C.card = (lowHalf A N).card at hCcard
  have hCpart := card_stepThreeImage_left_add_right A N
  change Cₗ.card + Cᵣ.card = C.card at hCpart
  have hCLcap := stepThree_left_card_le hsmall hno3
  change 36 * Cₗ.card ≤ N + 72 at hCLcap
  have hLV := card_lowHalf_add_upperHalf hsub
  change (lowHalf A N).card + V.card = A.card at hLV
  by_cases hdone : 3 * A.card ≤ N + 300
  · exact hdone.trans (by omega)
  have hdense : 5 * N ≤ 24 * V.card + 20000 := by
    rcases stepThree_image_dichotomy hP hsub hsmall with hright | hwhole
    · change 2 * Cᵣ.card + H.card ≤ N / 3 + 12 at hright
      rw [hVcard]
      omega
    · change C.card + H.card ≤ N / 4 + 24 at hwhole
      have hYupper : 12 * Y.card ≤ N + 300 := by omega
      have hAeq : A.card = C.card + V.card := by omega
      apply False.elim
      apply hdone
      rw [hAeq, hVcard]
      omega
  have hVupper : 4 * V.card ≤ N + 200 := by omega
  have hgap : 5 * N / 12 ≤ 3 * len + 2000 := by omega
  have hDupper : ∀ z ∈ D, N < 2 * z → z % 2 = 0 ∧ z % 3 ≠ 0 := by
    intro z hz hzN
    exact centralRemainder_upper_spec hP hsub hno3 hz hzN
  have hnotI {z : ℕ} (hzB : z ∈ B) : ¬(q ≤ z ∧ z < q + len) := by
    intro hzrange
    exact (Finset.disjoint_left.mp hdisjBI) hzB (mem_natAP_one_iff.mpr hzrange)
  by_cases hlate : 5 * N / 12 < q
  · let Bp := B.filter fun z ↦ z ≤ 5 * N / 12
    let Bt := B.filter fun z ↦ 5 * N / 12 < z
    let P := Bp.filter fun z ↦ z ≤ 3 * len
    let E := Bp.filter fun z ↦ 3 * len < z
    have hBpart := card_filter_le_add_gt B (5 * N / 12)
    change Bp.card + Bt.card = B.card at hBpart
    have hPpart := card_filter_le_add_gt Bp (3 * len)
    change P.card + E.card = Bp.card at hPpart
    have hPI : P ⊆ Icc (N / 3 + 1) (5 * N / 12) := by
      intro z hz
      have hz' := mem_filter.mp hz
      have hzBp := mem_filter.mp hz'.1
      have hzI := mem_Icc.mp (hBI hzBp.1)
      exact mem_Icc.mpr ⟨hzI.1, hzBp.2⟩
    have hP3 : ∀ z ∈ P, z % 3 ≠ 0 := by
      intro z hz hz3
      have hz' := mem_filter.mp hz
      have hzB := (mem_filter.mp hz'.1).1
      exact centralImage_not_three_below_interval hP hsub hI hzB
        (Nat.dvd_of_mod_eq_zero hz3) hz'.2 (by
          have hzBp := mem_filter.mp hz'.1
          omega)
    have hPcap := three_mul_card_nonthree_le hPI hP3
    change 3 * P.card ≤ 2 * ((5 * N / 12 + 3) - (N / 3 + 1)) at hPcap
    have hEI : E ⊆ Icc (3 * len + 1) (5 * N / 12) := by
      intro z hz
      have hz' := mem_filter.mp hz
      have hzBp := mem_filter.mp hz'.1
      exact mem_Icc.mpr ⟨by omega, hzBp.2⟩
    have hEcap := card_Icc_le hEI
    change E.card ≤ (5 * N / 12 + 1) - (3 * len + 1) at hEcap
    have hEsmall : E.card ≤ 2000 := by omega
    have hBtI : Bt ⊆ Icc (5 * N / 12 + 1) (2 * N / 3) := by
      intro z hz
      have hz' := mem_filter.mp hz
      have hzI := mem_Icc.mp (hBI hz'.1)
      exact mem_Icc.mpr ⟨by omega, hzI.2⟩
    have hItail : I ⊆ Icc (5 * N / 12 + 1) (2 * N / 3) := by
      intro z hz
      have hzrange := mem_natAP_one_iff.mp hz
      have hzI := mem_Icc.mp (hII hz)
      exact mem_Icc.mpr ⟨by omega, hzI.2⟩
    have htailpack := card_add_card_le_of_disjoint_subsets
      (hdisjBI.mono (filter_subset _ _) subset_rfl) hBtI hItail
    have htailcap := card_Icc_le
      (S := Icc (5 * N / 12 + 1) (2 * N / 3)) (subset_rfl)
    change Bt.card + I.card ≤ (Icc (5 * N / 12 + 1) (2 * N / 3)).card at htailpack
    change (Icc (5 * N / 12 + 1) (2 * N / 3)).card ≤
      (2 * N / 3 + 1) - (5 * N / 12 + 1) at htailcap
    rw [hIcard] at htailpack
    omega
  · have hq : q ≤ 5 * N / 12 := by omega
    have hqgap : q ≤ 3 * len + 2000 := by omega
    by_cases hcross : N < 2 * (q + len)
    · let Dl := D.filter fun z ↦ z < q
      let Dr := D.filter fun z ↦ q + len ≤ z
      let P := Dl.filter fun z ↦ z ≤ 3 * len
      let E := Dl.filter fun z ↦ 3 * len < z
      have hDpart : Dl.card + Dr.card = D.card := by
        have hd : Disjoint Dl Dr := by
          rw [Finset.disjoint_left]
          intro z hzl hzr
          have hl := (mem_filter.mp hzl).2
          have hr := (mem_filter.mp hzr).2
          omega
        have hu : Dl ∪ Dr = D := by
          ext z
          simp only [Dl, Dr, mem_union, mem_filter]
          constructor
          · rintro (h | h) <;> exact h.1
          · intro hz
            have hn := hnotI ((filter_subset _ _) hz)
            by_cases hl : z < q
            · exact Or.inl ⟨hz, hl⟩
            · exact Or.inr ⟨hz, by omega⟩
        rw [← card_union_of_disjoint hd, hu]
      have hPpart := card_filter_le_add_gt Dl (3 * len)
      change P.card + E.card = Dl.card at hPpart
      have hPI : P ⊆ Icc (N / 3 + 1) (q - 1) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        have hzI := mem_Icc.mp (hDI hzl.1)
        exact mem_Icc.mpr ⟨hzI.1, by omega⟩
      have hP3 : ∀ z ∈ P, z % 3 ≠ 0 := by
        intro z hz hz3
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        exact centralImage_not_three_below_interval hP hsub hI
          ((filter_subset _ _) hzl.1) (Nat.dvd_of_mod_eq_zero hz3)
          hz'.2 (by have hzI := mem_Icc.mp (hDI hzl.1); omega)
      have hPcap := three_mul_card_nonthree_le hPI hP3
      change 3 * P.card ≤ 2 * ((q - 1 + 3) - (N / 3 + 1)) at hPcap
      have hEI : E ⊆ Icc (3 * len + 1) (q - 1) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      have hEcap := card_Icc_le hEI
      change E.card ≤ (q - 1 + 1) - (3 * len + 1) at hEcap
      have hEsmall : E.card ≤ 2000 := by omega
      have hDrI : Dr ⊆ Icc (q + len) (2 * N / 3) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzI := mem_Icc.mp (hDI hz'.1)
        exact mem_Icc.mpr ⟨hz'.2, hzI.2⟩
      have hDreven : ∀ z ∈ Dr, z % 2 = 0 := by
        intro z hz
        have hz' := mem_filter.mp hz
        exact (hDupper z hz'.1 (by omega)).1
      have hDr3 : ∀ z ∈ Dr, z % 3 ≠ 0 := by
        intro z hz
        have hz' := mem_filter.mp hz
        exact (hDupper z hz'.1 (by omega)).2
      have hDrcap := six_mul_card_even_nonthree_le hDrI hDreven hDr3
      change 6 * Dr.card ≤ 2 * ((2 * N / 3 + 6) - (q + len)) at hDrcap
      omega
    · have hnoncross : 2 * (q + len) ≤ N := by omega
      let Dl := D.filter fun z ↦ z < q
      let R := D.filter fun z ↦ q + len ≤ z
      let P := Dl.filter fun z ↦ z ≤ 3 * len
      let E := Dl.filter fun z ↦ 3 * len < z
      let Dm := R.filter fun z ↦ 2 * z ≤ N
      let Du := R.filter fun z ↦ N < 2 * z
      have hDpart : Dl.card + R.card = D.card := by
        have hd : Disjoint Dl R := by
          rw [Finset.disjoint_left]
          intro z hzl hzr
          have hl := (mem_filter.mp hzl).2
          have hr := (mem_filter.mp hzr).2
          omega
        have hu : Dl ∪ R = D := by
          ext z
          simp only [Dl, R, mem_union, mem_filter]
          constructor
          · rintro (h | h) <;> exact h.1
          · intro hz
            have hn := hnotI ((filter_subset _ _) hz)
            by_cases hl : z < q
            · exact Or.inl ⟨hz, hl⟩
            · exact Or.inr ⟨hz, by omega⟩
        rw [← card_union_of_disjoint hd, hu]
      have hRpart : Dm.card + Du.card = R.card := by
        have hd : Disjoint Dm Du := by
          rw [Finset.disjoint_left]
          intro z hzm hzu
          have hm := (mem_filter.mp hzm).2
          have hu := (mem_filter.mp hzu).2
          omega
        have hu : Dm ∪ Du = R := by
          ext z
          simp only [Dm, Du, mem_union, mem_filter]
          constructor
          · rintro (h | h) <;> exact h.1
          · intro hz
            exact (le_or_gt (2 * z) N).imp (And.intro hz) (And.intro hz)
        rw [← card_union_of_disjoint hd, hu]
      have hPpart := card_filter_le_add_gt Dl (3 * len)
      change P.card + E.card = Dl.card at hPpart
      have hPI : P ⊆ Icc (N / 3 + 1) (q - 1) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        have hzI := mem_Icc.mp (hDI hzl.1)
        exact mem_Icc.mpr ⟨hzI.1, by omega⟩
      have hP3 : ∀ z ∈ P, z % 3 ≠ 0 := by
        intro z hz hz3
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        exact centralImage_not_three_below_interval hP hsub hI
          ((filter_subset _ _) hzl.1) (Nat.dvd_of_mod_eq_zero hz3)
          hz'.2 (by have hzI := mem_Icc.mp (hDI hzl.1); omega)
      have hPcap := three_mul_card_nonthree_le hPI hP3
      change 3 * P.card ≤ 2 * ((q - 1 + 3) - (N / 3 + 1)) at hPcap
      have hEI : E ⊆ Icc (3 * len + 1) (q - 1) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      have hEcap := card_Icc_le hEI
      change E.card ≤ (q - 1 + 1) - (3 * len + 1) at hEcap
      have hEsmall : E.card ≤ 2000 := by omega
      have hDmI : Dm ⊆ Icc (q + len) (N / 2) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzR := mem_filter.mp hz'.1
        exact mem_Icc.mpr ⟨hzR.2, by omega⟩
      have hDmcap := card_Icc_le hDmI
      change Dm.card ≤ (N / 2 + 1) - (q + len) at hDmcap
      have hDuI : Du ⊆ Icc (N / 2 + 1) (2 * N / 3) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzI := mem_Icc.mp (hDI ((filter_subset _ _) hz'.1))
        exact mem_Icc.mpr ⟨by omega, hzI.2⟩
      have hDueven : ∀ z ∈ Du, z % 2 = 0 := by
        intro z hz
        have hz' := mem_filter.mp hz
        exact (hDupper z ((filter_subset _ _) hz'.1) hz'.2).1
      have hDu3 : ∀ z ∈ Du, z % 3 ≠ 0 := by
        intro z hz
        have hz' := mem_filter.mp hz
        exact (hDupper z ((filter_subset _ _) hz'.1) hz'.2).2
      have hDucap := six_mul_card_even_nonthree_le hDuI hDueven hDu3
      change 6 * Du.card ≤ 2 * ((2 * N / 3 + 6) - (N / 2 + 1)) at hDucap
      omega

lemma caseThree_nonzero_step_three {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 3 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    3 * A.card ≤ N + 100000 := by
  let len := (upperHalfResidue A N 1).card +
    (upperHalfResidue A N 2).card - 1
  have hp₁ : 0 < (upperHalfResidue A N 1).card := card_pos.mpr hV₁
  have hp₂ : 0 < (upperHalfResidue A N 2).card := card_pos.mpr hV₂
  have hlenpos : 0 < len := by dsimp [len]; omega
  have hlen : 2 * (upperHalf A N).card ≤ 3 * (len + 1) := by
    dsimp [len]
    omega
  have hI : natAP (a / 3) 1 len ⊆ thirdSumQuotient A N := by
    apply stepThree_divided_interval ha3
    simpa [len] using hQ
  exact caseThree_step_three_interval hP hsub htail hcase3 hlenpos hlen hI

/-- The first term of a nonempty progression lying in `V₀ + V₀` is divisible
by three. -/
lemma zero_AP_start_dvd_three {A : Finset ℕ} {N a d : ℕ}
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (hQ : natAP a d (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0) :
    3 ∣ a := by
  have hlen : 0 < 2 * (upperHalfResidue A N 0).card - 1 := by
    have h0 := card_pos.mpr hV₀
    omega
  have ha : a ∈ upperHalfResidue A N 0 + upperHalfResidue A N 0 :=
    hQ (mem_natAP.mpr ⟨0, hlen, by simp⟩)
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp ha
  subst a
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have hx3 := (mem_upperHalfResidue.mp hx).2
  have hy3 := (mem_upperHalfResidue.mp hy).2
  omega

/-- In the zero-dominant structural branch the common difference is again
one of `3,6,9`. -/
lemma zero_structural_step {A : Finset ℕ} {N a d : ℕ}
    (hsub : A ⊆ Icc 1 N) (hN : 1000 ≤ N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (hd : 0 < d)
    (hQ : natAP a d (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0)
    (hres : InOneResidue
      (upperHalfResidue A N 0 + upperHalfResidue A N 0) d) :
    d = 3 ∨ d = 6 ∨ d = 9 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  have hV₀sub : V₀ ⊆ V := filter_subset _ _
  have hV₀I : V₀ ⊆ Icc (N / 2 + 1) N :=
    hV₀sub.trans (upperHalf_subset_interval hsub)
  have hres₀ : InOneResidue V₀ d := inOneResidue_add_left hV₀ hres
  obtain ⟨r, hr⟩ := hres₀
  have hcap := mul_card_fixed_zmod_le r hV₀I hr
  change d * V₀.card ≤ (N + d) - (N / 2 + 1) at hcap
  change (N + 1) / 2 < 3 * V.card at htail
  change V.card ≤ 3 * V₀.card at hdom
  have hlarge : N / 18 + 1 ≤ V₀.card := by omega
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hlen : 2 ≤ 2 * V₀.card - 1 := by omega
  have hlenpos : 0 < 2 * V₀.card - 1 := by omega
  have hlenone : 1 < 2 * V₀.card - 1 := by omega
  have hqa : a ∈ V₀ + V₀ := hQ (mem_natAP.mpr ⟨0, hlenpos, by simp⟩)
  have hqad : a + d ∈ V₀ + V₀ := by
    apply hQ
    exact mem_natAP.mpr ⟨1, hlenone, by simp⟩
  have hthree : ∀ z ∈ V₀ + V₀, 3 ∣ z := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx3 := (mem_upperHalfResidue.mp hx).2
    have hy3 := (mem_upperHalfResidue.mp hy).2
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
    omega
  have h3a := hthree a hqa
  have h3ad := hthree (a + d) hqad
  have h3d : 3 ∣ d := by
    obtain ⟨u, hu⟩ := h3a
    obtain ⟨v, hv⟩ := h3ad
    exact ⟨v - u, by omega⟩
  have hdlt : d < 12 := by
    by_contra hn
    have hd12 : 12 ≤ d := by omega
    obtain ⟨k, hk⟩ : ∃ k, V₀.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr hV₀)
    have hspan : d * k ≤ N - (N / 2 + 1) := by
      rw [hk, Nat.mul_add, Nat.mul_one] at hcap
      have heq : (N + d) - (N / 2 + 1) = N - (N / 2 + 1) + d := by omega
      rw [heq] at hcap
      omega
    have hmul : 12 * k ≤ d * k := Nat.mul_le_mul_right k hd12
    rw [hk] at hlarge
    omega
  obtain ⟨k, hk⟩ := h3d
  have hklt : k < 4 := by nlinarith
  interval_cases k <;> omega

/-- In the zero-dominant step-nine case the upper-half class cannot itself
be `0 (mod 9)`.  After division by nine, its least element has more than
half a complete block of successors, contradicting opposite-residue
pairing modulo that least element. -/
lemma zero_step_nine_start_nonzero {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 9 (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0)
    (hres : InOneResidue
      (upperHalfResidue A N 0 + upperHalfResidue A N 0) 9) :
    (a / 3) % 3 ≠ 0 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  change (a / 3) % 3 ≠ 0
  intro ha0
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hlenpos : 0 < 2 * V₀.card - 1 := by omega
  have hqa : a ∈ V₀ + V₀ := by
    apply hQ
    exact mem_natAP.mpr ⟨0, hlenpos, by simp⟩
  obtain ⟨u, hu, v, hv, huv⟩ := mem_add.mp hqa
  have ha9 : 9 ∣ a := by
    have hk3 : 3 ∣ a / 3 := Nat.dvd_iff_mod_eq_zero.mpr ha0
    obtain ⟨k, hk⟩ := hk3
    refine ⟨k, ?_⟩
    have haeq := Nat.mul_div_cancel' ha3
    omega
  have hsum9 : (u + v) % 9 = 0 := by
    rw [huv]
    exact Nat.dvd_iff_mod_eq_zero.mp ha9
  have hres₀ : InOneResidue V₀ 9 := inOneResidue_add_left hV₀ hres
  obtain ⟨r, hr⟩ := hres₀
  have hdiv9 : ∀ x ∈ V₀, 9 ∣ x := by
    intro x hx
    have hxu : x % 9 = u % 9 :=
      (ZMod.natCast_eq_natCast_iff x u 9).mp ((hr x hx).trans (hr u hu).symm)
    have hvu : v % 9 = u % 9 :=
      (ZMod.natCast_eq_natCast_iff v u 9).mp ((hr v hv).trans (hr u hu).symm)
    have hx3 : x % 3 = 0 := by
      simpa using (mem_upperHalfResidue.mp hx).2
    have hu3 : u % 3 = 0 := by
      simpa using (mem_upperHalfResidue.mp hu).2
    have hxrem3 : x % 9 % 3 = 0 := by
      rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 9)]
      exact hx3
    have hurem3 : u % 9 % 3 = 0 := by
      rw [Nat.mod_mod_of_dvd u (by norm_num : 3 ∣ 9)]
      exact hu3
    have hxlt := Nat.mod_lt x (by omega : 0 < 9)
    have hult := Nat.mod_lt u (by omega : 0 < 9)
    have hvlt := Nat.mod_lt v (by omega : 0 < 9)
    rw [Nat.add_mod] at hsum9
    rw [Nat.dvd_iff_mod_eq_zero]
    interval_cases x % 9 <;> interval_cases u % 9 <;>
      interval_cases v % 9 <;> omega
  let W := V₀.image fun x ↦ x / 9
  have hV₀sub : V₀ ⊆ A :=
    (filter_subset _ _).trans (ratSection_subset A N 1 2 1 1)
  have hPW : IsForbiddenTripleFree W := by
    exact (hP.mono hV₀sub).map_div (by omega) hdiv9
  have hWcard : W.card = V₀.card := by
    apply card_image_iff.mpr
    exact div_injOn_residue (r := 0) (q := 9) (by omega) fun x hx ↦
      Nat.dvd_iff_mod_eq_zero.mp (hdiv9 x hx)
  have hWne : W.Nonempty := hV₀.image _
  have hWI : W ⊆ Icc (N / 18 + 1) (N / 9) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have hxV := mem_upperHalf.mp (mem_upperHalfResidue.mp hx).1
    have hxmul := Nat.mul_div_cancel' (hdiv9 x hx)
    apply mem_Icc.mpr
    constructor
    · omega
    · exact Nat.div_le_div_right (mem_Icc.mp (hsub hxV.1)).2
  let s := W.min' hWne
  have hsW : s ∈ W := W.min'_mem hWne
  have hleast : ∀ x ∈ W, s ≤ x := fun x hx ↦ W.min'_le x hx
  have hsI := mem_Icc.mp (hWI hsW)
  have hspos : 0 < s := by omega
  have hWs : W ⊆ Icc s (N / 9) := by
    intro x hx
    exact mem_Icc.mpr ⟨hleast x hx, (mem_Icc.mp (hWI hx)).2⟩
  have hposition := card_Icc_le hWs
  have htop : ∀ x ∈ W, x ≤ 2 * s := by
    intro x hx
    have hxI := mem_Icc.mp (hWI hx)
    omega
  have hdecomp : W = {s} ∪ firstBlock W s := by
    ext x
    simp only [mem_union, mem_singleton, mem_firstBlock]
    constructor
    · intro hx
      by_cases hxs : x = s
      · exact Or.inl hxs
      · exact Or.inr ⟨hx, by have := hleast x hx; omega, htop x hx⟩
    · rintro (rfl | hx)
      · exact hsW
      · exact hx.1
  have hdisj : Disjoint ({s} : Finset ℕ) (firstBlock W s) := by
    rw [Finset.disjoint_left]
    intro x hxs hx
    simp only [mem_singleton] at hxs
    subst x
    have := (mem_firstBlock.mp hx).2.1
    omega
  have hcardDecomp : W.card = 1 + (firstBlock W s).card := by
    calc
      W.card = ({s} ∪ firstBlock W s).card := congrArg Finset.card hdecomp
      _ = ({s} : Finset ℕ).card + (firstBlock W s).card :=
        card_union_of_disjoint hdisj
      _ = 1 + (firstBlock W s).card := by simp
  have hfirst := two_mul_card_firstBlock_le hPW hsW hspos
  change V.card ≤ 3 * V₀.card at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  change W.card ≤ (N / 9 + 1) - s at hposition
  omega

/-- The remaining zero-dominant step-nine branch has divided start `1` or
`2 (mod 3)` and therefore closes by the common half-window packing plus
induction on the lower-half multiples of three. -/
lemma caseThree_zero_step_nine {A : Finset ℕ} {N C a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 9 (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0)
    (hres : InOneResidue
      (upperHalfResidue A N 0 + upperHalfResidue A N 0) 9)
    (hind : CoarseBound C (N / 6)
      ((divisibleInitial A N 3 2).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let len := 2 * V₀.card - 1
  change V.card ≤ 3 * V₀.card at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hres₀ : InOneResidue V₀ 9 := inOneResidue_add_left hV₀ hres
  obtain ⟨r, hr⟩ := hres₀
  have hV₀I : V₀ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hcap := mul_card_fixed_zmod_le r hV₀I hr
  change 9 * V₀.card ≤ (N + 9) - (N / 2 + 1) at hcap
  have hVcap : 6 * V.card ≤ N + 18 := by omega
  have hlen : N / 9 ≤ len := by dsimp [len]; omega
  have hat := zero_step_nine_start_nonzero hP hsub hN hV₀ htail hdom ha3 hQ hres
  have hQsub : natAP (a / 3) 3 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 9 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 3 * j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + 3 * j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 9 * j = 3 * (a / 3 + 3 * j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  have hZcap := caseThree_step_nine_nonzero_low_nonthree_data
    hP hsub hlen hat hQsub
  exact caseThree_step_nine_nonzero_data hP hsub hN hVcap hZcap hind

/-- The zero-dominant step-six alternative is an instance of the common
parity packing argument above. -/
lemma caseThree_zero_step_six {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 6 (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0)
    (hres : InOneResidue
      (upperHalfResidue A N 0 + upperHalfResidue A N 0) 6) :
    3 * A.card ≤ N + 18 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let len := 2 * V₀.card - 1
  change V.card ≤ 3 * V₀.card at hdom
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hres₀ : InOneResidue V₀ 6 := inOneResidue_add_left hV₀ hres
  obtain ⟨r, hr⟩ := hres₀
  have hV₀I : V₀ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hcap := mul_card_fixed_zmod_le r hV₀I hr
  change 6 * V₀.card ≤ (N + 6) - (N / 2 + 1) at hcap
  have hVcap : 4 * V.card ≤ N + 12 := by omega
  have hdomlen : 2 * V.card ≤ 3 * len + 3 := by
    dsimp [len]
    omega
  have hoddcover : V.card ≤ len + V₀.card + 1 := by
    dsimp [len]
    omega
  have hQsub : natAP (a / 3) 2 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 6 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 2 * j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + 2 * j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 6 * j = 3 * (a / 3 + 2 * j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  exact caseThree_step_six_data hP hsub hVcap hdomlen hoddcover hQsub

/-- Division by three turns the zero-dominant step-three progression into
the unit-step interval required by the complete step-three estimate. -/
lemma caseThree_zero_step_three {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 3 (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0) :
    3 * A.card ≤ N + 100000 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let len := 2 * V₀.card - 1
  change V.card ≤ 3 * V₀.card at hdom
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hlenpos : 0 < len := by dsimp [len]; omega
  have hlen : 2 * V.card ≤ 3 * (len + 1) := by
    dsimp [len]
    omega
  have hI : natAP (a / 3) 1 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 3 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 3 * j = 3 * (a / 3 + j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  exact caseThree_step_three_interval hP hsub htail hcase3 hlenpos hlen hI

/-! ### The enhanced central packing for the nonzero growth case -/

/-- A power of three times one property-P element cannot equal twice a
power of three times another.  This is Bedert's basic collision lemma. -/
lemma three_pow_ne_two_three_pow {A : Finset ℕ} (hP : IsForbiddenTripleFree A)
    {a b i j : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hapos : 0 < a)
    (hbpos : 0 < b) : 3 ^ i * a ≠ 2 * (3 ^ j * b) := by
  intro heq
  rcases le_total i j with hij | hji
  · have hp : 3 ^ j = 3 ^ i * 3 ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_of_le hij]
    rw [hp, mul_assoc, ← mul_assoc 2 (3 ^ i), mul_comm 2 (3 ^ i),
      mul_assoc] at heq
    have hcancel : a = 2 * (3 ^ (j - i) * b) :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 3)) heq
    have hba : b < a := by
      have hp1 : 1 ≤ 3 ^ (j - i) :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
      nlinarith
    apply hP.not_dvd_of_lt hb ha hba
    exact ⟨2 * 3 ^ (j - i), by simpa [mul_assoc, mul_comm, mul_left_comm]
      using hcancel⟩
  · by_cases heqij : i = j
    · subst i
      have heq' : 3 ^ j * a = 3 ^ j * (2 * b) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using heq
      have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 3)) heq'
      have hba : b < a := by nlinarith
      apply hP.not_dvd_of_lt hb ha hba
      exact ⟨2, by omega⟩
    · have hji' : j < i := lt_of_le_of_ne hji (Ne.symm heqij)
      have hp : 3 ^ i = 3 ^ j * 3 ^ (i - j) := by
        rw [← pow_add, Nat.add_sub_of_le hji]
      rw [hp, mul_assoc, ← mul_assoc 2 (3 ^ j), mul_comm 2 (3 ^ j),
        mul_assoc] at heq
      have hcancel : 3 ^ (i - j) * a = 2 * b :=
        Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 3)) heq
      have hpow : 3 ≤ 3 ^ (i - j) := by
        have hd : 0 < i - j := Nat.sub_pos_of_lt hji'
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
        rw [hk, pow_succ]
        have : 1 ≤ 3 ^ k :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        nlinarith
      have hab : a < b := by nlinarith
      apply hP.not_dvd_two_mul ha hb hab
      exact ⟨3 ^ (i - j), by simpa [mul_comm] using hcancel.symm⟩

/-- First move the lower half by powers of three into `(N/6,N/2]`. -/
noncomputable def tripleHalfBase (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (lowHalf A N).image (scaledMove 1 N 6)

/-- Double precisely the part of the power-three image at most `2N/9`. -/
def tripleHalfAdjust (N z : ℕ) : ℕ := if 9 * z ≤ 2 * N then 2 * z else z

noncomputable def tripleHalfImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfBase A N).image (tripleHalfAdjust N)

lemma tripleHalfBase_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleHalfBase A N).card = (lowHalf A N).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono (filter_subset _ _))
  intro a ha
  exact hP.pos_of_mem hsub (mem_lowHalf.mp ha).1

lemma tripleHalfBase_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleHalfBase A N ⊆ Icc (N / 6 + 1) (N / 2) := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
  have ha' := mem_lowHalf.mp ha
  have hapos := hP.pos_of_mem hsub ha'.1
  have hlo := lt_scaledMove (b := 1) (T := N) (q := 6) (by omega) hapos
  have hup := scaledMove_le (b := 1) (T := N) (q := 6) (by omega) hapos
    (by omega)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma tripleHalfBase_has_source {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ tripleHalfBase A N) :
    ∃ a ∈ lowHalf A N, ∃ e : ℕ, z = 3 ^ e * a := by
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
  exact ⟨a, ha, scaledWindowExp 1 N 6 a, by simp [scaledMove]⟩

lemma tripleHalfBase_no_double {A : Finset ℕ} {N x y : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hx : x ∈ tripleHalfBase A N) (hy : y ∈ tripleHalfBase A N) :
    x ≠ 2 * y := by
  obtain ⟨a, ha, i, rfl⟩ := tripleHalfBase_has_source hx
  obtain ⟨b, hb, j, rfl⟩ := tripleHalfBase_has_source hy
  exact three_pow_ne_two_three_pow (hP.mono (filter_subset _ _)) ha hb
    (hP.pos_of_mem hsub (mem_lowHalf.mp ha).1)
    (hP.pos_of_mem hsub (mem_lowHalf.mp hb).1)

lemma tripleHalfAdjust_injOn {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Set.InjOn (tripleHalfAdjust N) (tripleHalfBase A N) := by
  intro x hx y hy hxy
  simp only [tripleHalfAdjust] at hxy
  split at hxy <;> split at hxy
  · omega
  · exact False.elim (tripleHalfBase_no_double hP hsub hy hx hxy.symm)
  · exact False.elim (tripleHalfBase_no_double hP hsub hx hy hxy)
  · exact hxy

lemma tripleHalfImage_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleHalfImage A N).card = (lowHalf A N).card := by
  rw [tripleHalfImage, card_image_iff.mpr (tripleHalfAdjust_injOn hP hsub),
    tripleHalfBase_card hP hsub]

lemma tripleHalfImage_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleHalfImage A N ⊆ Icc (2 * N / 9 + 1) (N / 2) := by
  intro z hz
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
  have hbI := mem_Icc.mp (tripleHalfBase_subset hP hsub hb)
  simp only [tripleHalfAdjust]
  split
  · exact mem_Icc.mpr ⟨by omega, by omega⟩
  · exact mem_Icc.mpr ⟨by omega, hbI.2⟩

lemma tripleHalfImage_has_source {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ tripleHalfImage A N) :
    ∃ a ∈ lowHalf A N, ∃ e : ℕ,
      z = 3 ^ e * a ∨ z = 2 * (3 ^ e * a) := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
  obtain ⟨a, ha, e, rfl⟩ := tripleHalfBase_has_source hb
  refine ⟨a, ha, e, ?_⟩
  simp only [tripleHalfAdjust]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The four pieces of Bedert's power-three image. -/
noncomputable def tripleOddLow (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).filter fun z ↦ 3 * z ≤ N ∧ z % 2 = 1

noncomputable def tripleBad (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).filter fun z ↦
    3 * z ≤ N ∧ z % 2 = 0 ∧ 3 * (z / 2) ∈ tripleHalfImage A N

noncomputable def tripleGood (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).filter fun z ↦
    3 * z ≤ N ∧ z % 2 = 0 ∧ 3 * (z / 2) ∉ tripleHalfImage A N

noncomputable def tripleUpper (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).filter fun z ↦ N < 3 * z

noncomputable def tripleUpperGood (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleGood A N).image (fun z ↦ 3 * (z / 2)) ∪ tripleUpper A N

lemma tripleHalfImage_source_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ tripleHalfImage A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ z := by
  obtain ⟨a, ha, e, he | he⟩ := tripleHalfImage_has_source hz
  · refine ⟨a, (mem_lowHalf.mp ha).1, (mem_lowHalf.mp ha).2, ?_⟩
    rw [he]
    exact dvd_mul_left a (3 ^ e)
  · refine ⟨a, (mem_lowHalf.mp ha).1, (mem_lowHalf.mp ha).2, ?_⟩
    rw [he]
    simpa [mul_assoc] using dvd_mul_left a (2 * 3 ^ e)

lemma tripleImage_partition_card (A : Finset ℕ) (N : ℕ) :
    (tripleOddLow A N).card + (tripleBad A N).card +
      (tripleGood A N).card + (tripleUpper A N).card =
        (tripleHalfImage A N).card := by
  let Z := tripleHalfImage A N
  let O := tripleOddLow A N
  let B := tripleBad A N
  let G := tripleGood A N
  let U := tripleUpper A N
  have hOB : Disjoint O B := by
    rw [Finset.disjoint_left]
    intro z ho hb
    have ho' := (mem_filter.mp ho).2.2
    have hb' := (mem_filter.mp hb).2.2.1
    omega
  have hOG : Disjoint O G := by
    rw [Finset.disjoint_left]
    intro z ho hg
    have ho' := (mem_filter.mp ho).2.2
    have hg' := (mem_filter.mp hg).2.2.1
    omega
  have hOU : Disjoint O U := by
    rw [Finset.disjoint_left]
    intro z ho hu
    have ho' := (mem_filter.mp ho).2.1
    have hu' := (mem_filter.mp hu).2
    omega
  have hBG : Disjoint B G := by
    rw [Finset.disjoint_left]
    intro z hb hg
    exact (mem_filter.mp hg).2.2.2 (mem_filter.mp hb).2.2.2
  have hBU : Disjoint B U := by
    rw [Finset.disjoint_left]
    intro z hb hu
    have hb' := (mem_filter.mp hb).2.1
    have hu' := (mem_filter.mp hu).2
    omega
  have hGU : Disjoint G U := by
    rw [Finset.disjoint_left]
    intro z hg hu
    have hg' := (mem_filter.mp hg).2.1
    have hu' := (mem_filter.mp hu).2
    omega
  have hOBG : Disjoint (O ∪ B) G := by
    rw [Finset.disjoint_left]
    intro z hz hg
    rcases mem_union.mp hz with ho | hb
    · exact (Finset.disjoint_left.mp hOG) ho hg
    · exact (Finset.disjoint_left.mp hBG) hb hg
  have hAllU : Disjoint (O ∪ B ∪ G) U := by
    rw [Finset.disjoint_left]
    intro z hz hu
    rcases mem_union.mp hz with hz | hg
    · rcases mem_union.mp hz with ho | hb
      · exact (Finset.disjoint_left.mp hOU) ho hu
      · exact (Finset.disjoint_left.mp hBU) hb hu
    · exact (Finset.disjoint_left.mp hGU) hg hu
  have hunion : O ∪ B ∪ G ∪ U = Z := by
    ext z
    simp only [O, B, G, U, tripleOddLow, tripleBad, tripleGood, tripleUpper,
      mem_union, mem_filter]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hz
      by_cases hlo : 3 * z ≤ N
      · by_cases hodd : z % 2 = 1
        · exact Or.inl (Or.inl (Or.inl ⟨hz, hlo, hodd⟩))
        · have heven : z % 2 = 0 := by
            have := Nat.mod_lt z (by omega : 0 < 2)
            omega
          by_cases hm : 3 * (z / 2) ∈ Z
          · exact Or.inl (Or.inl (Or.inr ⟨hz, hlo, heven, hm⟩))
          · exact Or.inl (Or.inr ⟨hz, hlo, heven, hm⟩)
      · exact Or.inr ⟨hz, by omega⟩
  calc
    O.card + B.card + G.card + U.card =
        (O ∪ B ∪ G ∪ U).card := by
      rw [card_union_of_disjoint hAllU, card_union_of_disjoint hOBG,
        card_union_of_disjoint hOB]
    _ = Z.card := congrArg Finset.card hunion

lemma tripleUpperGood_card {A : Finset ℕ} {N : ℕ} :
    (tripleUpperGood A N).card =
      (tripleGood A N).card + (tripleUpper A N).card := by
  let G := tripleGood A N
  let U := tripleUpper A N
  let f : ℕ → ℕ := fun z ↦ 3 * (z / 2)
  have hinj : Set.InjOn f G := by
    intro x hx y hy hxy
    have hx0 := (mem_filter.mp hx).2.2.1
    have hy0 := (mem_filter.mp hy).2.2.1
    have hx2 : 2 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr hx0
    have hy2 : 2 ∣ y := Nat.dvd_iff_mod_eq_zero.mpr hy0
    have hdiv : x / 2 = y / 2 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
    calc
      x = 2 * (x / 2) := (Nat.mul_div_cancel' hx2).symm
      _ = 2 * (y / 2) := by rw [hdiv]
      _ = y := Nat.mul_div_cancel' hy2
  have hdisj : Disjoint (G.image f) U := by
    rw [Finset.disjoint_left]
    intro w hw hu
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    exact (mem_filter.mp hz).2.2.2 (mem_filter.mp hu).1
  rw [tripleUpperGood, card_union_of_disjoint hdisj,
    card_image_iff.mpr hinj]

lemma tripleUpperGood_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleUpperGood A N ⊆ Icc (N / 3 + 1) (N / 2) := by
  intro w hw
  rcases mem_union.mp hw with hw | hw
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub (mem_filter.mp hz).1)
    have hzlo := (mem_filter.mp hz).2.1
    have hz0 := (mem_filter.mp hz).2.2.1
    have hz2 : 2 ∣ z := Nat.dvd_iff_mod_eq_zero.mpr hz0
    have hzeq := Nat.mul_div_cancel' hz2
    have hzlo' : 2 * N < 9 * z := by omega
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub (mem_filter.mp hw).1)
    have hzlo := (mem_filter.mp hw).2
    exact mem_Icc.mpr ⟨by omega, hzI.2⟩

lemma tripleUpperGood_source {A : Finset ℕ} {N w : ℕ}
    (hw : w ∈ tripleUpperGood A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ 2 * w := by
  rcases mem_union.mp hw with hw | hw
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    obtain ⟨a, ha, haN, haz⟩ := tripleHalfImage_source_divisor (mem_filter.mp hz).1
    refine ⟨a, ha, haN, ?_⟩
    have hz0 := (mem_filter.mp hz).2.2.1
    have hz2 : 2 ∣ z := Nat.dvd_iff_mod_eq_zero.mpr hz0
    have hzeq := Nat.mul_div_cancel' hz2
    have : 2 * (3 * (z / 2)) = 3 * z := by omega
    rw [this]
    exact haz.mul_left 3
  · obtain ⟨a, ha, haN, haw⟩ := tripleHalfImage_source_divisor (mem_filter.mp hw).1
    exact ⟨a, ha, haN, haw.mul_left 2⟩

lemma tripleOddLow_add_high_odd_le {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hi : i = 1 ∨ i = 3) :
    (tripleOddLow A N).card + (modFourPart (highThird A N) i).card ≤
      N / 12 + 10 := by
  apply oddLeft_add_high_odd_le hP hsub
  · intro z hz
    have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub (mem_filter.mp hz).1)
    refine mem_Icc.mpr ⟨hzI.1, ?_⟩
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
    simpa [mul_comm] using (mem_filter.mp hz).2.1
  · intro z hz
    exact (mem_filter.mp hz).2.2
  · intro z hz
    obtain ⟨a, ha, haN, haz⟩ := tripleHalfImage_source_divisor (mem_filter.mp hz).1
    exact ⟨a, ha, by omega, haz.mul_left 6⟩
  · exact hi

lemma tripleUpperGood_add_high_even_le {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleUpperGood A N).card +
      (parityPart (highThird A N) 0).card ≤ N / 6 + 3 := by
  let Z := tripleUpperGood A N
  let E := parityPart (highThird A N) 0
  let W := zmodFiber (Icc (2 * N / 3 + 1) N) (0 : ZMod 2)
  have hZE : Disjoint (Z.image fun z ↦ 2 * z) E := by
    rw [Finset.disjoint_left]
    intro w hw he
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    obtain ⟨a, ha, haN, haz⟩ := tripleUpperGood_source hz
    have he' := mem_highThird.mp (mem_parityPart.mp he).1
    have halt : a < 2 * z := by
      have hzI := mem_Icc.mp (tripleUpperGood_subset hP hsub hz)
      omega
    exact hP.not_dvd_of_lt ha he'.1 halt haz
  have hZU : Z.image (fun z ↦ 2 * z) ⊆ W := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzI := mem_Icc.mp (tripleUpperGood_subset hP hsub hz)
    apply mem_zmodFiber.mpr
    exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right 2 z⟩
  have hEU : E ⊆ W := by
    intro z hz
    have hz' := mem_parityPart.mp hz
    have hzI := mem_Icc.mp (highThird_subset_interval hsub hz'.1)
    apply mem_zmodFiber.mpr
    refine ⟨mem_Icc.mpr hzI, ?_⟩
    apply (ZMod.natCast_eq_natCast_iff' z 0 2).mpr
    simpa using hz'.2
  have hpack := card_add_card_le_of_disjoint_subsets hZE hZU hEU
  have hcap := mul_card_fixed_zmod_le (S := W) (L := 2 * N / 3 + 1) (U := N)
    (0 : ZMod 2) (filter_subset _ _)
    (fun z hz ↦ (mem_zmodFiber.mp hz).2)
  have hZcard : (Z.image fun z ↦ 2 * z).card = Z.card := by
    apply card_image_iff.mpr
    intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  change (Z.image fun z ↦ 2 * z).card + E.card ≤ W.card at hpack
  change 2 * W.card ≤ (N + 2) - (2 * N / 3 + 1) at hcap
  have hL : 2 * N / 3 + 1 ≤ N + 2 := by omega
  have hraw := (Nat.le_sub_iff_add_le hL).mp hcap
  rw [hZcard] at hpack
  change Z.card + E.card ≤ N / 6 + 3
  omega

/-- With both odd classes present, the divisible-by-four high sumset has
size at least the maximum used in Bedert's Lemma 10, up to one. -/
lemma high_mod_four_max_le_sum_add_one {A : Finset ℕ} {N : ℕ}
    (h1 : (modFourPart (highThird A N) 1).Nonempty)
    (h3 : (modFourPart (highThird A N) 3).Nonempty) :
    max ((modFourPart (highThird A N) 1).card +
          (modFourPart (highThird A N) 3).card)
        (max (2 * (modFourPart (highThird A N) 0).card)
          (2 * (modFourPart (highThird A N) 2).card)) ≤
      (highFourSums A N).card + 1 := by
  let H := highThird A N
  let S := highFourSums A N
  change (modFourPart H 1).Nonempty at h1
  change (modFourPart H 3).Nonempty at h3
  have h13sub : modFourPart H 1 + modFourPart H 3 ⊆ S := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx' := mem_modFourPart.mp hx
    have hy' := mem_modFourPart.mp hy
    apply mem_zmodFiber.mpr
    refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
      Nat.add_mod, hx'.2, hy'.2]
  have h13cd := cauchy_davenport_add_of_linearOrder_isCancelAdd h1 h3
  have h13card := card_le_card h13sub
  have h13 : (modFourPart H 1).card + (modFourPart H 3).card ≤ S.card + 1 := by
    omega
  have hself (r : ℕ) (hr : r = 0 ∨ r = 2) :
      2 * (modFourPart H r).card ≤ S.card + 1 := by
    obtain hempty | hne := (modFourPart H r).eq_empty_or_nonempty
    · simp [hempty]
    · have hsubself : modFourPart H r + modFourPart H r ⊆ S := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
        have hx' := mem_modFourPart.mp hx
        have hy' := mem_modFourPart.mp hy
        apply mem_zmodFiber.mpr
        refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
        rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
          Nat.add_mod, hx'.2, hy'.2]
        rcases hr with rfl | rfl <;> decide
      have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hne hne
      have hc := card_le_card hsubself
      omega
  have h0 := hself 0 (Or.inl rfl)
  have h2 := hself 2 (Or.inr rfl)
  change max ((modFourPart H 1).card + (modFourPart H 3).card)
      (max (2 * (modFourPart H 0).card) (2 * (modFourPart H 2).card)) ≤
    S.card + 1
  omega

lemma tripleUpperGood_add_highFourSums_le {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleUpperGood A N).card + (highFourSums A N).card ≤ N / 6 + 4 := by
  let Z := tripleUpperGood A N
  let S := highFourSums A N
  let W := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 4)
  have hB : ∀ z ∈ Z, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * z := by
    intro z hz
    obtain ⟨a, ha, haN, haz⟩ := tripleUpperGood_source hz
    exact ⟨a, ha, by omega, dvd_trans haz (by exact ⟨2, by ring⟩)⟩
  have hH : ∀ x ∈ highThird A N, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hZU : Z.image (fun z ↦ 4 * z) ⊆ W := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzI := mem_Icc.mp (tripleUpperGood_subset hP hsub hz)
    apply mem_zmodFiber.mpr
    exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right 4 z⟩
  have hSU : S ⊆ W := by
    intro w hw
    have hw' := mem_zmodFiber.mp hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hw'.1
    have hxI := mem_Icc.mp (highThird_subset_interval hsub hx)
    have hyI := mem_Icc.mp (highThird_subset_interval hsub hy)
    exact mem_zmodFiber.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hw'.2⟩
  have hp := packing (k := 4) (t := N / 2) (by omega) hP hB hH
    (filter_subset _ _) hZU hSU
  have hcap := mul_card_fixed_zmod_le (S := W) (L := 4 * N / 3 + 1) (U := 2 * N)
    (0 : ZMod 4) (filter_subset _ _)
    (fun z hz ↦ (mem_zmodFiber.mp hz).2)
  change Z.card + S.card ≤ W.card at hp
  change 4 * W.card ≤ (2 * N + 4) - (4 * N / 3 + 1) at hcap
  have hL : 4 * N / 3 + 1 ≤ 2 * N + 4 := by omega
  have hraw := (Nat.le_sub_iff_add_le hL).mp hcap
  change Z.card + S.card ≤ N / 6 + 4
  omega

lemma card_modFour_parts (H : Finset ℕ) :
    (modFourPart H 0).card + (modFourPart H 1).card +
      (modFourPart H 2).card + (modFourPart H 3).card = H.card := by
  let f : ℕ → ℕ := fun x ↦ x % 4
  have hmap : (H : Set ℕ).MapsTo f (range 4) := by
    intro x hx
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have h := Finset.card_eq_sum_card_fiberwise hmap
  simp only [sum_range_succ, sum_range_zero] at h
  have heq (r : ℕ) (hr : r < 4) :
      H.filter (fun x ↦ f x = r) = modFourPart H r := by
    ext x
    simp [f, modFourPart, Nat.mod_eq_of_lt hr]
  rw [heq 0 (by omega), heq 1 (by omega), heq 2 (by omega),
    heq 3 (by omega)] at h
  change H.card = 0 + (modFourPart H 0).card + (modFourPart H 1).card +
    (modFourPart H 2).card + (modFourPart H 3).card at h
  omega

/-- The bad-image reserve used in the hard nonzero growth branch. -/
lemma triple_bad_reserve {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hlarge : N + 2 < 3 * A.card) :
    N ≤ 24 * ((middleSixth A N).card + (tripleBad A N).card) + 2000 := by
  let O := tripleOddLow A N
  let B := tripleBad A N
  let G := tripleGood A N
  let U := tripleUpper A N
  let R := tripleUpperGood A N
  let H := highThird A N
  let Y := middleSixth A N
  let H₀ := modFourPart H 0
  let H₁ := modFourPart H 1
  let H₂ := modFourPart H 2
  let H₃ := modFourPart H 3
  let E := parityPart H 0
  let P := parityPart H 1
  have hZcard := tripleHalfImage_card hP hsub
  have hpart := tripleImage_partition_card A N
  have hRcard := tripleUpperGood_card (A := A) (N := N)
  have hHpart := card_modFour_one_add_three H
  have hHfour := card_modFour_parts H
  have hpar := card_parity_parts H
  have hVpart := card_middleSixth_add_highThird hsub
  have hAV := card_lowHalf_add_upperHalf hsub
  change O.card + B.card + G.card + U.card = (tripleHalfImage A N).card at hpart
  change R.card = G.card + U.card at hRcard
  change H₁.card + H₃.card = P.card at hHpart
  change H₀.card + H₁.card + H₂.card + H₃.card = H.card at hHfour
  change E.card + P.card = H.card at hpar
  change Y.card + H.card = (upperHalf A N).card at hVpart
  change (lowHalf A N).card + (upperHalf A N).card = A.card at hAV
  change (tripleHalfImage A N).card = (lowHalf A N).card at hZcard
  change 6 * H.card < N + 144 at hcase3
  change N + 2 < 3 * A.card at hlarge
  change N ≤ 24 * (Y.card + B.card) + 2000
  have hRe := tripleUpperGood_add_high_even_le hP hsub
  change R.card + E.card ≤ N / 6 + 3 at hRe
  by_cases h1 : H₁.Nonempty
  · by_cases h3 : H₃.Nonempty
    · let M := max (H₁.card + H₃.card) (max (2 * H₀.card) (2 * H₂.card))
      have hM := high_mod_four_max_le_sum_add_one h1 h3
      change M ≤ (highFourSums A N).card + 1 at hM
      have hRS := tripleUpperGood_add_highFourSums_le hP hsub
      change R.card + (highFourSums A N).card ≤ N / 6 + 4 at hRS
      have hO1 := tripleOddLow_add_high_odd_le hP hsub (i := 1) (Or.inl rfl)
      have hO3 := tripleOddLow_add_high_odd_le hP hsub (i := 3) (Or.inr rfl)
      change O.card + H₁.card ≤ N / 12 + 10 at hO1
      change O.card + H₃.card ≤ N / 12 + 10 at hO3
      have hOm : O.card + max H₁.card H₃.card ≤ N / 12 + 10 := by
        omega
      have hRM : R.card + M ≤ N / 6 + 5 := by omega
      have hMlower : 3 * H.card ≤ 4 * (M + max H₁.card H₃.card) := by
        dsimp [M]
        omega
      have hcore : 24 * (O.card + R.card + H.card) ≤ 7 * N + 504 := by
        omega
      have hAeq : A.card = B.card + Y.card + O.card + R.card + H.card := by
        omega
      omega
    · have hH₃ : H₃.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h3)
      have hO1 := tripleOddLow_add_high_odd_le hP hsub (i := 1) (Or.inl rfl)
      change O.card + H₁.card ≤ N / 12 + 10 at hO1
      have hcore : 4 * (O.card + R.card + H.card) ≤ N + 52 := by omega
      have hAeq : A.card = B.card + Y.card + O.card + R.card + H.card := by
        omega
      omega
  · have hH₁ : H₁.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h1)
    have hO3 := tripleOddLow_add_high_odd_le hP hsub (i := 3) (Or.inr rfl)
    change O.card + H₃.card ≤ N / 12 + 10 at hO3
    have hcore : 4 * (O.card + R.card + H.card) ≤ N + 52 := by omega
    have hAeq : A.card = B.card + Y.card + O.card + R.card + H.card := by
      omega
    omega

/-! ### Bedert's final auxiliary set `B₃` -/

def tripleCentralMove (N z : ℕ) : ℕ := if 3 * z ≤ N then 2 * z else z

noncomputable def triplePrimary (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).image (tripleCentralMove N) ∪ middleSixth A N

lemma tripleHalfImage_low_mem_base {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hz : z ∈ tripleHalfImage A N) (hzlo : 3 * z ≤ N) :
    z ∈ tripleHalfBase A N := by
  obtain ⟨b, hb, hbeq⟩ := mem_image.mp hz
  have hbI := mem_Icc.mp (tripleHalfBase_subset hP hsub hb)
  simp only [tripleHalfAdjust] at hbeq
  split at hbeq
  · omega
  · simpa [hbeq] using hb

lemma tripleHalfImage_no_double_low {A : Finset ℕ} {N x : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hx : x ∈ tripleHalfImage A N) (hxlo : 3 * x ≤ N) :
    2 * x ∉ tripleHalfImage A N := by
  intro h2x
  have hxB := tripleHalfImage_low_mem_base hP hsub hx hxlo
  obtain ⟨b, hb, hbeq⟩ := mem_image.mp h2x
  simp only [tripleHalfAdjust] at hbeq
  split at hbeq
  · have hbx : b = x := by omega
    subst b
    have hxI := mem_Icc.mp (tripleHalfImage_subset hP hsub hx)
    omega
  · apply tripleHalfBase_no_double hP hsub hb hxB
    omega

lemma tripleCentralMove_injOn {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Set.InjOn (tripleCentralMove N) (tripleHalfImage A N) := by
  intro x hx y hy hxy
  simp only [tripleCentralMove] at hxy
  split at hxy <;> split at hxy
  · omega
  · exact False.elim (tripleHalfImage_no_double_low hP hsub hx (by assumption)
      (by simpa [hxy] using hy))
  · exact False.elim (tripleHalfImage_no_double_low hP hsub hy (by assumption)
      (by simpa [hxy] using hx))
  · exact hxy

lemma tripleCentralMove_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleHalfImage A N).image (tripleCentralMove N) ⊆
      Icc (N / 3 + 1) (2 * N / 3) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
  have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub hz)
  simp only [tripleCentralMove]
  split
  · have hzlo : 2 * N < 9 * z := by omega
    refine mem_Icc.mpr ⟨?_, ?_⟩
    · omega
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
      omega
  · refine mem_Icc.mpr ⟨by omega, ?_⟩
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
    omega

lemma tripleCentralMove_source_divisor {A : Finset ℕ} {N w : ℕ}
    (hw : w ∈ (tripleHalfImage A N).image (tripleCentralMove N)) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ w := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
  obtain ⟨a, ha, haN, haz⟩ := tripleHalfImage_source_divisor hz
  refine ⟨a, ha, haN, ?_⟩
  simp only [tripleCentralMove]
  split
  · exact haz.mul_left 2
  · exact haz

lemma triplePrimary_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    triplePrimary A N ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
  intro z hz
  rcases mem_union.mp hz with hz | hz
  · exact tripleCentralMove_subset hP hsub hz
  · have hz' := mem_middleSixth.mp hz
    have hzN := (mem_Icc.mp (hsub hz'.1)).2
    exact mem_Icc.mpr ⟨by omega, by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
      simpa [mul_comm] using hz'.2.2⟩

lemma triplePrimary_source_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ triplePrimary A N) :
    ∃ a ∈ A, 3 * a ≤ 2 * N ∧ a ∣ z := by
  rcases mem_union.mp hz with hz | hz
  · obtain ⟨a, ha, haN, haz⟩ := tripleCentralMove_source_divisor hz
    exact ⟨a, ha, by omega, haz⟩
  · have hz' := mem_middleSixth.mp hz
    exact ⟨z, hz'.1, hz'.2.2, dvd_refl z⟩

lemma triplePrimary_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (triplePrimary A N).card =
      (lowHalf A N).card + (middleSixth A N).card := by
  let Z := tripleHalfImage A N
  let f := tripleCentralMove N
  let Y := middleSixth A N
  have hdisj : Disjoint (Z.image f) Y := by
    rw [Finset.disjoint_left]
    intro z hz hy
    obtain ⟨a, ha, haN, haz⟩ := tripleCentralMove_source_divisor hz
    have hy' := mem_middleSixth.mp hy
    have halt : a < z := by omega
    exact hP.not_dvd_of_lt ha hy'.1 halt haz
  change (Z.image f ∪ Y).card = (lowHalf A N).card + Y.card
  rw [card_union_of_disjoint hdisj,
    card_image_iff.mpr (tripleCentralMove_injOn hP hsub),
    tripleHalfImage_card hP hsub]

lemma tripleBad_extra_spec {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hz : z ∈ tripleBad A N) :
    ∃ a ∈ lowHalf A N, ∃ e : ℕ,
      4 ∣ z ∧ 9 * (z / 4) = 3 ^ e * a ∧
        N < 2 * (9 * (z / 4)) ∧ 3 * (9 * (z / 4)) ≤ 2 * N := by
  have hzZ := (mem_filter.mp hz).1
  have hzlo := (mem_filter.mp hz).2.1
  have hz0 := (mem_filter.mp hz).2.2.1
  have hwZ := (mem_filter.mp hz).2.2.2
  have hz2 : 2 ∣ z := Nat.dvd_iff_mod_eq_zero.mpr hz0
  have hzeven := Nat.mul_div_cancel' hz2
  have hzB := tripleHalfImage_low_mem_base hP hsub hzZ hzlo
  obtain ⟨a, ha, i, hza⟩ := tripleHalfBase_has_source hzB
  obtain ⟨b, hb, hbw⟩ := mem_image.mp hwZ
  by_cases hbsmall : 9 * b ≤ 2 * N
  · simp only [tripleHalfAdjust, if_pos hbsmall] at hbw
    obtain ⟨c, hc, j, hbc⟩ := tripleHalfBase_has_source hb
    have h4mul : 4 ∣ 3 * z := by
      refine ⟨b, ?_⟩
      omega
    have h4z : 4 ∣ z :=
      (show Nat.Coprime 4 3 by decide).dvd_mul_left.mp h4mul
    have hzfour := Nat.mul_div_cancel' h4z
    have hbeq : b = 3 * (z / 4) := by omega
    refine ⟨c, hc, j + 1, h4z, ?_, ?_, ?_⟩
    · calc
        9 * (z / 4) = 3 * b := by omega
        _ = 3 ^ (j + 1) * c := by rw [hbc, pow_succ]; ring
    · have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub hzZ)
      omega
    · omega
  · simp only [tripleHalfAdjust, if_neg hbsmall] at hbw
    obtain ⟨c, hc, j, hbc⟩ := tripleHalfBase_has_source hb
    have hcollision : 3 ^ (i + 1) * a = 2 * (3 ^ j * c) := by
      calc
        3 ^ (i + 1) * a = 3 * (3 ^ i * a) := by rw [pow_succ]; ring
        _ = 3 * z := by rw [hza]
        _ = 2 * b := by omega
        _ = 2 * (3 ^ j * c) := by rw [hbc]
    exact False.elim ((three_pow_ne_two_three_pow hP
      (mem_lowHalf.mp ha).1 (mem_lowHalf.mp hc).1
      (hP.pos_of_mem hsub (mem_lowHalf.mp ha).1)
      (hP.pos_of_mem hsub (mem_lowHalf.mp hc).1)) hcollision)

noncomputable def tripleBadExtra (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleBad A N).image fun z ↦ 9 * (z / 4)

lemma tripleBadExtra_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleBadExtra A N ⊆ Icc (N / 2 + 1) (2 * N / 3) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
  obtain ⟨a, ha, e, h4z, hlo, hlow, hupp⟩ := tripleBad_extra_spec hP hsub hz
  refine mem_Icc.mpr ⟨by omega, ?_⟩
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
  simpa [mul_comm] using hupp

lemma tripleBadExtra_source {A : Finset ℕ} {N w : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hw : w ∈ tripleBadExtra A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ w := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
  obtain ⟨a, ha, e, h4z, heq, hlo, hupp⟩ := tripleBad_extra_spec hP hsub hz
  refine ⟨a, (mem_lowHalf.mp ha).1, (mem_lowHalf.mp ha).2, ?_⟩
  rw [heq]
  exact dvd_mul_left a (3 ^ e)

lemma tripleBadExtra_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleBadExtra A N).card = (tripleBad A N).card := by
  apply card_image_iff.mpr
  intro x hx y hy hxy
  obtain ⟨a, ha, i, hx4, hxa, hxlo, hxhi⟩ := tripleBad_extra_spec hP hsub hx
  obtain ⟨b, hb, j, hy4, hyb, hylo, hyhi⟩ := tripleBad_extra_spec hP hsub hy
  have hqx : 4 * (x / 4) = x := Nat.mul_div_cancel' hx4
  have hqy : 4 * (y / 4) = y := Nat.mul_div_cancel' hy4
  have hq : x / 4 = y / 4 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
  omega

lemma tripleBadExtra_disjoint_triplePrimary {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (tripleBadExtra A N) (triplePrimary A N) := by
  rw [Finset.disjoint_left]
  intro w hwE hwP
  rcases mem_union.mp hwP with hwM | hwY
  · obtain ⟨x, hx, hxw⟩ := mem_image.mp hwM
    have hwI := mem_Icc.mp (tripleBadExtra_subset hP hsub hwE)
    simp only [tripleCentralMove] at hxw
    split at hxw
    · have hxB := tripleHalfImage_low_mem_base hP hsub hx (by assumption)
      obtain ⟨b, hb, j, hxb⟩ := tripleHalfBase_has_source hxB
      obtain ⟨z, hz, hzw⟩ := mem_image.mp hwE
      obtain ⟨a, ha, i, hz4, hza, hzlo, hzhi⟩ :=
        tripleBad_extra_spec hP hsub hz
      have hcollision : 3 ^ i * a = 2 * (3 ^ j * b) := by
        calc
          3 ^ i * a = 9 * (z / 4) := hza.symm
          _ = w := hzw
          _ = 2 * x := hxw.symm
          _ = 2 * (3 ^ j * b) := by rw [hxb]
      exact (three_pow_ne_two_three_pow hP
        (mem_lowHalf.mp ha).1 (mem_lowHalf.mp hb).1
        (hP.pos_of_mem hsub (mem_lowHalf.mp ha).1)
        (hP.pos_of_mem hsub (mem_lowHalf.mp hb).1)) hcollision
    · have hxI := mem_Icc.mp (tripleHalfImage_subset hP hsub hx)
      omega
  · obtain ⟨a, ha, haN, haw⟩ := tripleBadExtra_source hP hsub hwE
    have hwY' := mem_middleSixth.mp hwY
    have halt : a < w := by omega
    exact hP.not_dvd_of_lt ha hwY'.1 halt haw

noncomputable def tripleFinal (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  tripleBadExtra A N ∪ triplePrimary A N

lemma card_lowHalf_add_middleSixth {A : Finset ℕ} {N : ℕ}
    (_hsub : A ⊆ Icc 1 N) :
    (lowHalf A N).card + (middleSixth A N).card =
      (lowTwoThirds A N).card := by
  have hdisj : Disjoint (lowHalf A N) (middleSixth A N) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have hx' := mem_lowHalf.mp hx
    have hy' := mem_middleSixth.mp hy
    omega
  have hunion : lowHalf A N ∪ middleSixth A N = lowTwoThirds A N := by
    ext x
    simp only [mem_union, mem_lowHalf, mem_middleSixth, mem_lowTwoThirds]
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, by omega⟩
      · exact ⟨hx.1, hx.2.2⟩
    · intro hx
      by_cases hlo : 2 * x ≤ N
      · exact Or.inl ⟨hx.1, hlo⟩
      · exact Or.inr ⟨hx.1, by omega, hx.2⟩
  rw [← card_union_of_disjoint hdisj, hunion]

lemma tripleFinal_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleFinal A N).card =
      (lowTwoThirds A N).card + (tripleBad A N).card := by
  rw [tripleFinal,
    card_union_of_disjoint (tripleBadExtra_disjoint_triplePrimary hP hsub),
    tripleBadExtra_card hP hsub, triplePrimary_card hP hsub,
    ← card_lowHalf_add_middleSixth hsub]
  omega

lemma tripleFinal_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleFinal A N ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
  intro z hz
  rcases mem_union.mp hz with hz | hz
  · have hzI := mem_Icc.mp (tripleBadExtra_subset hP hsub hz)
    exact mem_Icc.mpr ⟨by omega, hzI.2⟩
  · exact triplePrimary_subset hP hsub hz

lemma tripleFinal_source_divisor {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hz : z ∈ tripleFinal A N) :
    ∃ a ∈ A, 3 * a ≤ 2 * N ∧ a ∣ z := by
  rcases mem_union.mp hz with hz | hz
  · obtain ⟨a, ha, haN, haz⟩ := tripleBadExtra_source hP hsub hz
    exact ⟨a, ha, by omega, haz⟩
  · exact triplePrimary_source_divisor hz

lemma tripleFinal_disjoint_thirdSumQuotient {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (tripleFinal A N) (thirdSumQuotient A N) := by
  rw [Finset.disjoint_left]
  intro b hbB hbQ
  obtain ⟨a, haA, haN, hab⟩ := tripleFinal_source_divisor hP hsub hbB
  have hbW := mem_Icc.mp (tripleFinal_subset hP hsub hbB)
  have hbpos : 0 < b := by omega
  have hapos : 0 < a := hP.pos_of_mem hsub haA
  have hab_le : a ≤ b := Nat.le_of_dvd hbpos hab
  have h3 := quotientPart_spec hbQ
  have hsum := (mem_zmodFiber.mp h3).1
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp hsum
  have hx' := mem_upperHalf.mp hx
  have hy' := mem_upperHalf.mp hy
  have hxN := (mem_Icc.mp (hsub hx'.1)).2
  have hyN := (mem_Icc.mp (hsub hy'.1)).2
  by_cases hax : a < x
  · by_cases hay : a < y
    · apply hP.not_dvd_add haA hx'.1 hy'.1 hax hay
      rw [hxy]
      exact hab.mul_left 3
    · have : x > N := by omega
      omega
  · have : y > N := by omega
    omega

lemma caseThree_enhanced_packing {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (lowTwoThirds A N).card + (tripleBad A N).card +
      (thirdSumQuotient A N).card ≤
        (Icc (N / 3 + 1) (2 * N / 3)).card := by
  have hp := card_add_card_le_of_disjoint_subsets
    (tripleFinal_disjoint_thirdSumQuotient hP hsub)
    (tripleFinal_subset hP hsub) (thirdSumQuotient_subset_central hsub)
  rw [tripleFinal_card hP hsub] at hp
  exact hp

lemma nonzero_decomposition {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    A.card ≤ (divisibleInitial A N 3 1).card +
      (lowNonthreeImagePart A N 1).card +
      (lowNonthreeImagePart A N 2).card +
      (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 1
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  have hCparts := card_lowNonthreeImage_parts (A := A) (N := N)
  have hCcard := card_lowNonthreeImage hP hsub
  change C₁.card + C₂.card = (lowNonthreeImage A N).card at hCparts
  have hCcard' : (lowNonthreeImage A N).card = Lₙ.card := by
    simpa [Lₙ, L] using hCcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx0 hxn
      exact (mem_filter.mp hxn).2 (mem_filter.mp hx0).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases hmod : x % 3 = 0
        · exact Or.inl ⟨hx, hmod⟩
        · exact Or.inr ⟨hx, hmod⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxL.1, Nat.dvd_iff_mod_eq_zero.mpr hx'.2, ?_⟩
    have hxN := (mem_Icc.mp (hsub hxL.1)).2
    omega
  have hV₀D : V₀ ⊆ D := by
    intro x hx
    have hx' := mem_upperHalfResidue.mp hx
    have hxV := mem_upperHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxV.1, Nat.dvd_iff_mod_eq_zero.mpr (by simpa using hx'.2), ?_⟩
    have hxN := (mem_Icc.mp (hsub hxV.1)).2
    omega
  have hL₀V₀ : Disjoint L₀ V₀ := by
    rw [Finset.disjoint_left]
    intro x hxL hxV
    have hl := mem_lowHalf.mp (mem_filter.mp hxL).1
    have hv := mem_upperHalf.mp (mem_upperHalfResidue.mp hxV).1
    omega
  have hDcover : L₀.card + V₀.card ≤ D.card := by
    rw [← card_union_of_disjoint hL₀V₀]
    exact card_le_card (union_subset hL₀D hV₀D)
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  change A.card ≤ D.card + C₁.card + C₂.card + V₁.card + V₂.card
  omega

lemma modFour_one_add_three_subset {H : Finset ℕ} :
    modFourPart H 1 + modFourPart H 3 ⊆
      zmodFiber (H + H) (0 : ZMod 4) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
  have hx' := mem_modFourPart.mp hx
  have hy' := mem_modFourPart.mp hy
  apply mem_zmodFiber.mpr
  refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
    Nat.add_mod, hx'.2, hy'.2]

lemma modFour_self_subset {H : Finset ℕ} {r : ℕ} (hr : r = 0 ∨ r = 2) :
    modFourPart H r + modFourPart H r ⊆
      zmodFiber (H + H) (0 : ZMod 4) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
  have hx' := mem_modFourPart.mp hx
  have hy' := mem_modFourPart.mp hy
  apply mem_zmodFiber.mpr
  refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
    Nat.add_mod, hx'.2, hy'.2]
  rcases hr with rfl | rfl <;> decide

/-- Bedert's Lemma 10/Corollary 1 fork.  Either the middle-sixth/bad-set
reserve is already of order `N/12`, or the divisible-by-four top sumset
contains a progression whose length is at least half the size of the top
third, up to one endpoint. -/
lemma strong_reserve_or_fourAP {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hlarge : N + 2 < 3 * A.card) :
    N ≤ 12 * ((middleSixth A N).card + (tripleBad A N).card) + 1000 ∨
      ∃ a d len : ℕ, 0 < d ∧
        natAP a d len ⊆ highFourSums A N ∧
        (highThird A N).card ≤ 2 * (len + 1) := by
  let O := tripleOddLow A N
  let B := tripleBad A N
  let R := tripleUpperGood A N
  let H := highThird A N
  let Y := middleSixth A N
  let H₀ := modFourPart H 0
  let H₁ := modFourPart H 1
  let H₂ := modFourPart H 2
  let H₃ := modFourPart H 3
  let S := highFourSums A N
  have hZcard := tripleHalfImage_card hP hsub
  have hpart := tripleImage_partition_card A N
  have hRcard := tripleUpperGood_card (A := A) (N := N)
  have hHfour := card_modFour_parts H
  have hVpart := card_middleSixth_add_highThird hsub
  have hAV := card_lowHalf_add_upperHalf hsub
  change O.card + B.card + (tripleGood A N).card + (tripleUpper A N).card =
    (tripleHalfImage A N).card at hpart
  change R.card = (tripleGood A N).card + (tripleUpper A N).card at hRcard
  change H₀.card + H₁.card + H₂.card + H₃.card = H.card at hHfour
  change Y.card + H.card = (upperHalf A N).card at hVpart
  change (lowHalf A N).card + (upperHalf A N).card = A.card at hAV
  change (tripleHalfImage A N).card = (lowHalf A N).card at hZcard
  change N + 2 < 3 * A.card at hlarge
  by_cases h1 : H₁.Nonempty
  · by_cases h3 : H₃.Nonempty
    · have h13sub : H₁ + H₃ ⊆ S := modFour_one_add_three_subset
      have h00sub : H₀ + H₀ ⊆ S := modFour_self_subset (Or.inl rfl)
      have h22sub : H₂ + H₂ ⊆ S := modFour_self_subset (Or.inr rfl)
      let m13 := H₁.card + H₃.card
      let m0 := 2 * H₀.card
      let m2 := 2 * H₂.card
      have hhalf : H.card ≤ 2 * max m13 (max m0 m2) := by
        dsimp [m13, m0, m2]
        omega
      have hm13pos : 0 < m13 := by
        have hp1 : 0 < H₁.card := card_pos.mpr h1
        have hp3 : 0 < H₃.card := card_pos.mpr h3
        dsimp [m13]
        omega
      have hRS := tripleUpperGood_add_highFourSums_le hP hsub
      change R.card + S.card ≤ N / 6 + 4 at hRS
      have hO1 := tripleOddLow_add_high_odd_le hP hsub (i := 1) (Or.inl rfl)
      have hO3 := tripleOddLow_add_high_odd_le hP hsub (i := 3) (Or.inr rfl)
      change O.card + H₁.card ≤ N / 12 + 10 at hO1
      change O.card + H₃.card ≤ N / 12 + 10 at hO3
      have hOmax : O.card + max H₁.card H₃.card ≤ N / 12 + 10 := by omega
      have finish (hHS : H.card ≤ S.card + 3 + max H₁.card H₃.card) :
          N ≤ 12 * (Y.card + B.card) + 1000 := by
        have hcore : O.card + R.card + H.card ≤ N / 4 + 20 := by omega
        omega
      rcases le_total m13 (max m0 m2) with hle | hge
      · rcases le_total m0 m2 with h02 | h20
        · have hm : max m0 m2 = m2 := max_eq_right h02
          rw [hm] at hle hhalf
          have hall : max m13 m2 = m2 := max_eq_right hle
          rw [hall] at hhalf
          have hm2pos : 0 < H₂.card := by dsimp [m2] at hle; omega
          rcases bgAlternative_of_nonempty (S := H₂) (T := H₂)
            (card_pos.mp hm2pos) (card_pos.mp hm2pos) with hg | hs
          · left
            apply finish
            have hc := card_le_card h22sub
            simp only [min_self] at hg
            dsimp [m13, m0, m2] at hle h02
            omega
          · right
            obtain ⟨a, d, hd, hQ, hres⟩ := hs
            refine ⟨a, d, m2 - 1, hd, ?_, ?_⟩
            · simpa [m2, two_mul] using hQ.trans h22sub
            · have hm2pos' : 0 < m2 := by dsimp [m2]; omega
              rw [Nat.sub_add_cancel (by omega : 1 ≤ m2)]
              exact hhalf
        · have hm : max m0 m2 = m0 := max_eq_left h20
          rw [hm] at hle hhalf
          have hall : max m13 m0 = m0 := max_eq_right hle
          rw [hall] at hhalf
          have hm0pos : 0 < H₀.card := by dsimp [m0] at hle; omega
          rcases bgAlternative_of_nonempty (S := H₀) (T := H₀)
            (card_pos.mp hm0pos) (card_pos.mp hm0pos) with hg | hs
          · left
            apply finish
            have hc := card_le_card h00sub
            simp only [min_self] at hg
            dsimp [m13, m0, m2] at hle h20
            omega
          · right
            obtain ⟨a, d, hd, hQ, hres⟩ := hs
            refine ⟨a, d, m0 - 1, hd, ?_, ?_⟩
            · simpa [m0, two_mul] using hQ.trans h00sub
            · have hm0pos' : 0 < m0 := by dsimp [m0]; omega
              rw [Nat.sub_add_cancel (by omega : 1 ≤ m0)]
              exact hhalf
      · have hall : max m13 (max m0 m2) = m13 := max_eq_left hge
        rw [hall] at hhalf
        rcases bgAlternative_of_nonempty h1 h3 with hg | hs
        · left
          apply finish
          have hc := card_le_card h13sub
          change H₁.card + H₃.card + min H₁.card H₃.card ≤
            (H₁ + H₃).card + 3 at hg
          dsimp [m13, m0, m2] at hge
          omega
        · right
          obtain ⟨a, d, hd, hQ, hres⟩ := hs
          refine ⟨a, d, m13 - 1, hd, ?_, ?_⟩
          · simpa [m13] using hQ.trans h13sub
          · rw [Nat.sub_add_cancel (by omega : 1 ≤ m13)]
            exact hhalf
    · left
      have hH₃ : H₃.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h3)
      have hRe := tripleUpperGood_add_high_even_le hP hsub
      change R.card + (parityPart H 0).card ≤ N / 6 + 3 at hRe
      have hO1 := tripleOddLow_add_high_odd_le hP hsub (i := 1) (Or.inl rfl)
      change O.card + H₁.card ≤ N / 12 + 10 at hO1
      have hpar := card_parity_parts H
      have hodd := card_modFour_one_add_three H
      change (parityPart H 0).card + (parityPart H 1).card = H.card at hpar
      change H₁.card + H₃.card = (parityPart H 1).card at hodd
      change N ≤ 12 * (Y.card + B.card) + 1000
      omega
  · left
    have hH₁ : H₁.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h1)
    have hRe := tripleUpperGood_add_high_even_le hP hsub
    change R.card + (parityPart H 0).card ≤ N / 6 + 3 at hRe
    have hO3 := tripleOddLow_add_high_odd_le hP hsub (i := 3) (Or.inr rfl)
    change O.card + H₃.card ≤ N / 12 + 10 at hO3
    have hpar := card_parity_parts H
    have hodd := card_modFour_one_add_three H
    change (parityPart H 0).card + (parityPart H 1).card = H.card at hpar
    change H₁.card + H₃.card = (parityPart H 1).card at hodd
    change N ≤ 12 * (Y.card + B.card) + 1000
    omega

lemma highFourSums_subset_interval {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    highFourSums A N ⊆ Icc (4 * N / 3 + 1) (2 * N) := by
  intro z hz
  have hz' := mem_zmodFiber.mp hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz'.1
  have hxI := mem_Icc.mp (highThird_subset_interval hsub hx)
  have hyI := mem_Icc.mp (highThird_subset_interval hsub hy)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma fourAP_step_or_small {A : Finset ℕ} {N a d len : ℕ}
    (hsub : A ⊆ Icc 1 N) (hd : 0 < d)
    (hQ : natAP a d len ⊆ highFourSums A N)
    (hH : (highThird A N).card ≤ 2 * (len + 1)) :
    9 * (highThird A N).card ≤ N + 100 ∨ d = 4 ∨ d = 8 := by
  by_cases hlen : 2 ≤ len
  · have haQ : a ∈ highFourSums A N := hQ (mem_natAP.mpr ⟨0, by omega, by simp⟩)
    have hadQ : a + d ∈ highFourSums A N := by
      apply hQ
      exact mem_natAP.mpr ⟨1, by omega, by simp⟩
    have ha4 : 4 ∣ a := by
      have := (mem_zmodFiber.mp haQ).2
      rw [ZMod.natCast_eq_zero_iff] at this
      exact this
    have had4 : 4 ∣ a + d := by
      have := (mem_zmodFiber.mp hadQ).2
      rw [ZMod.natCast_eq_zero_iff] at this
      exact this
    have hd4 : 4 ∣ d := by
      rw [Nat.dvd_iff_mod_eq_zero] at ha4 had4 ⊢
      rw [Nat.add_mod, ha4] at had4
      simpa using had4
    rcases hd4 with ⟨k, rfl⟩
    by_cases hk : 3 ≤ k
    · left
      have hlastQ : a + 4 * k * (len - 1) ∈ highFourSums A N := by
        apply hQ
        exact mem_natAP.mpr ⟨len - 1, by omega, by ring⟩
      have haI := mem_Icc.mp (highFourSums_subset_interval hsub haQ)
      have hlI := mem_Icc.mp (highFourSums_subset_interval hsub hlastQ)
      have hwidth : 12 * (len - 1) ≤ 2 * N - (4 * N / 3 + 1) := by
        have hmul : 12 * (len - 1) ≤ 4 * k * (len - 1) := by nlinarith
        omega
      omega
    · right
      have hkpos : 0 < k := by omega
      interval_cases k <;> simp_all
  · left
    omega

lemma exists_AP_residue_offset {a d r : ℕ} (ha : 4 ∣ a)
    (hd : d = 4 ∨ d = 8) (hr : r = 1 ∨ r = 2) :
    ∃ t < 3, (a + d * t) % 12 = (4 * r) % 12 := by
  obtain ⟨k, rfl⟩ := ha
  have hk : k % 3 < 3 := Nat.mod_lt _ (by omega)
  rcases hd with rfl | rfl <;> rcases hr with rfl | rfl <;>
    interval_cases hkm : k % 3 <;>
    first
    | exact ⟨0, by omega, by omega⟩
    | exact ⟨1, by omega, by omega⟩
    | exact ⟨2, by omega, by omega⟩

def apResidueSlice (a d len t : ℕ) : Finset ℕ :=
  (range (len / 3)).image fun j ↦ a + d * (t + 3 * j)

lemma apResidueSlice_card {a d len t : ℕ} (hd : 0 < d) :
    (apResidueSlice a d len t).card = len / 3 := by
  unfold apResidueSlice
  rw [card_image_iff.mpr]
  · simp
  · intro x hx y hy hxy
    have hmul : d * (t + 3 * x) = d * (t + 3 * y) := Nat.add_left_cancel hxy
    have := Nat.eq_of_mul_eq_mul_left hd hmul
    omega

lemma apResidueSlice_subset {a d len t : ℕ} (ht : t < 3) :
    apResidueSlice a d len t ⊆ natAP a d len := by
  intro z hz
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
  have hj' := mem_range.mp hj
  apply mem_natAP.mpr
  refine ⟨t + 3 * j, ?_, rfl⟩
  have hdiv : 3 * (len / 3) ≤ len := Nat.mul_div_le len 3
  omega

lemma apResidueSlice_mod {a d len t r : ℕ}
    (hd : d = 4 ∨ d = 8) (ht : (a + d * t) % 12 = (4 * r) % 12) :
    ∀ z ∈ apResidueSlice a d len t, z % 12 = (4 * r) % 12 := by
  intro z hz
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
  rcases hd with rfl | rfl
  · have heq : a + 4 * (t + 3 * j) = (a + 4 * t) + j * 12 := by ring
    rw [heq]
    exact (Nat.add_mul_mod_self_right (a + 4 * t) j 12).trans ht
  · have heq : a + 8 * (t + 3 * j) = (a + 8 * t) + (2 * j) * 12 := by ring
    rw [heq]
    exact (Nat.add_mul_mod_self_right (a + 8 * t) (2 * j) 12).trans ht

lemma upperThreeClass_pack_five_low {A U B : Finset ℕ} {N r : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hU : U ⊆ upperHalf A N) (hthree : ∀ x ∈ U, x % 3 = r % 3)
    (hB : B ⊆ lowNonthreeImage A N)
    (hBthree : ∀ b ∈ B, b % 3 = r % 3)
    (hBlow : ∀ b ∈ B, 5 * b ≤ 2 * N)
    (hdense : N / 6 + 6 ≤ 2 * U.card) :
    15 * B.card + 6 * U.card ≤ N + 30 := by
  let S := zmodFiber (U + U) (0 : ZMod 5)
  let e := 5 * (r % 3)
  let W := zmodFiber (Icc (N + 1) (2 * N)) (e : ZMod 15)
  have hUI : U ⊆ Icc (N / 2 + 1) N := hU.trans (upperHalf_subset_interval hsub)
  have hd := dense_residue_upperHalf_fixed_three (q := 5) (r := r)
    (by omega) (by norm_num) hUI hthree hdense (0 : ZMod 5)
  have hBdiv : ∀ b ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 5 * b := by
    intro b hb
    obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor
      (lowNonthreeImage_subset_halfImage A N (hB hb))
    exact ⟨a, ha, by omega, hab.mul_left 5⟩
  have hUH : ∀ x ∈ U, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_upperHalf.mp (hU hx)
    exact ⟨hx'.1, by omega⟩
  have hBW : B.image (fun b ↦ 5 * b) ⊆ W := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    have hbI := mem_Icc.mp (lowNonthreeImage_subset_interval hP hsub (hB hb))
    have hb3 := hBthree b hb
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, hBlow b hb⟩
    · apply (ZMod.natCast_eq_natCast_iff' (5 * b) e 15).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 5)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hSW : S ⊆ W := by
    intro z hz
    have hz' := mem_zmodFiber.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz'.1
    have hxI := mem_Icc.mp (hUI hx)
    have hyI := mem_Icc.mp (hUI hy)
    have hx3 := hthree x hx
    have hy3 := hthree y hy
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) e 15).mpr
      have h5 := (ZMod.natCast_eq_zero_iff (x + y) 5).mp hz'.2
      rw [Nat.dvd_iff_mod_eq_zero] at h5
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 5)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hp := packing (k := 5) (t := N / 2) (by omega) hP hBdiv hUH
    (filter_subset _ _) hBW hSW
  have hcap := mul_card_fixed_zmod_le (S := W) (L := N + 1) (U := 2 * N)
    (e : ZMod 15) (filter_subset _ _)
    (fun z hz ↦ (mem_zmodFiber.mp hz).2)
  change 2 * U.card ≤ 5 * (S.card + 1) at hd
  change B.card + S.card ≤ W.card at hp
  change 15 * W.card ≤ (2 * N + 15) - (N + 1) at hcap
  omega

lemma fourAP_high_pack {A B P : Finset ℕ} {N r : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hB : B ⊆ lowNonthreeImage A N)
    (hBthree : ∀ b ∈ B, b % 3 = r % 3)
    (hBhigh : ∀ b ∈ B, 2 * N < 5 * b)
    (hPsum : P ⊆ highFourSums A N)
    (hPres : ∀ z ∈ P, z % 12 = (4 * r) % 12) :
    18 * (B.card + P.card) ≤ N + 30 := by
  let W := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) ((4 * r : ℕ) : ZMod 12)
  have hBdiv : ∀ b ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * b := by
    intro b hb
    obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor
      (lowNonthreeImage_subset_halfImage A N (hB hb))
    exact ⟨a, ha, by omega, hab.mul_left 4⟩
  have hH : ∀ x ∈ highThird A N, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hBW : B.image (fun b ↦ 4 * b) ⊆ W := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    have hbI := mem_Icc.mp (lowNonthreeImage_subset_interval hP hsub (hB hb))
    have hb3 := hBthree b hb
    have hbhi := hBhigh b hb
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (4 * b) (4 * r) 12).mpr
      calc
        (4 * b) % 12 = 4 * (b % 3) := Nat.mul_mod_mul_left 4 b 3
        _ = 4 * (r % 3) := by rw [hb3]
        _ = (4 * r) % 12 := (Nat.mul_mod_mul_left 4 r 3).symm
  have hPW : P ⊆ W := by
    intro z hz
    apply mem_zmodFiber.mpr
    refine ⟨highFourSums_subset_interval hsub (hPsum hz), ?_⟩
    apply (ZMod.natCast_eq_natCast_iff' z (4 * r) 12).mpr
    exact hPres z hz
  have hp := packing (k := 4) (t := N / 2) (by omega) hP hBdiv hH
    (hPsum.trans (filter_subset _ _)) hBW hPW
  have hcap := mul_card_fixed_zmod_le (S := W) (L := 4 * N / 3 + 1) (U := 2 * N)
    ((4 * r : ℕ) : ZMod 12)
    (filter_subset _ _) (fun z hz ↦ (mem_zmodFiber.mp hz).2)
  change B.card + P.card ≤ W.card at hp
  change 12 * W.card ≤ (2 * N + 12) - (4 * N / 3 + 1) at hcap
  omega

lemma improved_same_part_bound {A : Finset ℕ} {N r a d len : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hr : r = 1 ∨ r = 2)
    (hd : d = 4 ∨ d = 8) (hlen : 0 < len)
    (hQ : natAP a d len ⊆ highFourSums A N)
    (hH : (highThird A N).card ≤ 2 * (len + 1))
    (hdense : N / 6 + 6 ≤ 2 * (upperHalfResidue A N r).card) :
    90 * (lowNonthreeImagePart A N r).card +
        36 * (upperHalfResidue A N r).card +
        15 * (highThird A N).card ≤ 11 * N + 500 := by
  let U := upperHalfResidue A N r
  let C := lowNonthreeImagePart A N r
  let Cₗ := C.filter fun b ↦ 5 * b ≤ 2 * N
  let Cₕ := C.filter fun b ↦ 2 * N < 5 * b
  have hCpart : Cₗ.card + Cₕ.card = C.card := by
    have hdisj : Disjoint Cₗ Cₕ := by
      rw [Finset.disjoint_left]
      intro b hb hbh
      have hb' := (mem_filter.mp hb).2
      have hbh' := (mem_filter.mp hbh).2
      omega
    have hunion : Cₗ ∪ Cₕ = C := by
      ext b
      simp only [Cₗ, Cₕ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hb
        exact (le_or_gt (5 * b) (2 * N)).imp (And.intro hb) (And.intro hb)
    rw [← card_union_of_disjoint hdisj, hunion]
  have hUsub : U ⊆ upperHalf A N := filter_subset _ _
  have hUthree : ∀ x ∈ U, x % 3 = r % 3 := by
    intro x hx
    exact (mem_upperHalfResidue.mp hx).2
  have hCsub : C ⊆ lowNonthreeImage A N := by
    intro b hb
    exact (mem_lowNonthreeImagePart.mp hb).1
  have hCthree : ∀ b ∈ C, b % 3 = r % 3 := by
    intro b hb
    exact (mem_lowNonthreeImagePart.mp hb).2
  have hpLow := upperThreeClass_pack_five_low hP hsub hUsub hUthree
    (B := Cₗ) ((filter_subset _ _).trans hCsub)
    (fun b hb ↦ hCthree b (mem_filter.mp hb).1)
    (fun b hb ↦ (mem_filter.mp hb).2) hdense
  change 15 * Cₗ.card + 6 * U.card ≤ N + 30 at hpLow
  have haQ : a ∈ highFourSums A N := hQ (mem_natAP.mpr ⟨0, hlen, by simp⟩)
  have ha4 : 4 ∣ a := by
    have haZ := (mem_zmodFiber.mp haQ).2
    rw [ZMod.natCast_eq_zero_iff] at haZ
    exact haZ
  obtain ⟨t, ht, htmod⟩ := exists_AP_residue_offset ha4 hd hr
  let P := apResidueSlice a d len t
  have hPcard := apResidueSlice_card (a := a) (d := d) (len := len) (t := t)
    (by rcases hd with rfl | rfl <;> omega)
  change P.card = len / 3 at hPcard
  have hPsub : P ⊆ highFourSums A N :=
    (apResidueSlice_subset ht).trans hQ
  have hPres : ∀ z ∈ P, z % 12 = (4 * r) % 12 :=
    apResidueSlice_mod hd htmod
  have hpHigh := fourAP_high_pack hP hsub
    (B := Cₕ) (P := P) ((filter_subset _ _).trans hCsub)
    (fun b hb ↦ hCthree b (mem_filter.mp hb).1)
    (fun b hb ↦ (mem_filter.mp hb).2) hPsub hPres
  change 18 * (Cₕ.card + P.card) ≤ N + 30 at hpHigh
  change 90 * C.card + 36 * U.card + 15 * (highThird A N).card ≤ 11 * N + 500
  have hlenDiv : len ≤ 3 * (len / 3) + 2 := by omega
  omega

/-! The three numerical closures used in the hard nonzero-growth branch are
kept separate from the combinatorial context.  Besides making the constants
auditable, this prevents the Presburger procedure from having to normalize
several dozen irrelevant set-theoretic hypotheses. -/

lemma hard_finish_standard_strong {a y b d h n c : ℕ}
    (hn : 1000000000 ≤ n)
    (hd : 3 * d ≤ n / 3 + c)
    (hh : 6 * h < n + 144)
    (hr : n ≤ 12 * (y + b) + 1000)
    (hm : 60 * a + 32 * y + 54 * b ≤ 60 * d + 11 * n + 500 + 22 * h) :
    3 * a ≤ n + c := by
  omega

lemma hard_finish_standard_small {a y b d h n c : ℕ}
    (hn : 1000000000 ≤ n)
    (hd : 3 * d ≤ n / 3 + c)
    (hr : n ≤ 24 * (y + b) + 2000)
    (hh : 9 * h ≤ n + 100)
    (hm : 60 * a + 32 * y + 54 * b ≤ 60 * d + 11 * n + 500 + 22 * h) :
    3 * a ≤ n + c := by
  omega

lemma hard_finish_improved {a y b d h n c : ℕ}
    (hn : 1000000000 ≤ n)
    (hd : 3 * d ≤ n / 3 + c)
    (hh : 6 * h < n + 144)
    (hr : n ≤ 24 * (y + b) + 2000)
    (hm : 180 * a + 96 * y + 162 * b ≤
      180 * d + 37 * n + 2000 + 36 * h) :
    3 * a ≤ n + c := by
  omega

lemma caseThree_nonzero_growth_hard {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000000000 ≤ N)
    (hC : 2 ≤ C)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hgrowth :
      (upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card +
        min (upperHalfResidue A N 1).card (upperHalfResidue A N 2).card ≤
          (upperHalfResidue A N 1 + upperHalfResidue A N 2).card + 3)
    (hind : CoarseBound C (N / 3)
      ((divisibleInitial A N 3 1).image fun x ↦ x / 3))
    (hfail : ¬ CoarseBound C N A) : False := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let H := highThird A N
  let Y := middleSixth A N
  let B := tripleBad A N
  let D := divisibleInitial A N 3 1
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  let R := zmodFiber (V + V) (0 : ZMod 3)
  let Q := thirdSumQuotient A N
  have hlarge : N + 2 < 3 * A.card := by
    by_contra hn
    apply hfail
    change 3 * A.card ≤ N + C
    omega
  have h12 : V₁ + V₂ ⊆ R := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
    have hxZ : (x : ZMod 3) = 1 := by
      apply (ZMod.natCast_eq_natCast_iff x 1 3).mpr
      change x % 3 = 1 % 3
      simpa using hx'.2
    have hyZ : (y : ZMod 3) = 2 := by
      apply (ZMod.natCast_eq_natCast_iff y 2 3).mpr
      change y % 3 = 2 % 3
      simpa using hy'.2
    push_cast
    rw [hxZ, hyZ]
    decide
  have hsumQ : (V₁ + V₂).card ≤ Q.card := by
    have hc := card_le_card h12
    have hQc := thirdSumQuotient_card A N
    change Q.card = R.card at hQc
    omega
  have hrel : V₁.card + V₂.card + min V₁.card V₂.card + B.card ≤ H.card + 3 := by
    by_contra hn
    have hp := caseThree_enhanced_packing hP hsub
    have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
      simp
      omega
    have hAH := card_low_add_card_high A N
    change (lowTwoThirds A N).card + H.card = A.card at hAH
    change (lowTwoThirds A N).card + B.card + Q.card ≤
      (Icc (N / 3 + 1) (2 * N / 3)).card at hp
    change V₁.card + V₂.card + min V₁.card V₂.card ≤
      (V₁ + V₂).card + 3 at hgrowth
    have hQB : H.card + 1 ≤ Q.card + B.card := by omega
    apply hfail
    change 3 * A.card ≤ N + C
    omega
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  change 6 * H.card < N + 144 at hcase3
  have hweak := triple_bad_reserve hP hsub hcase3 hlarge
  change N ≤ 24 * (Y.card + B.card) + 2000 at hweak
  have hbonus :
      N ≤ 12 * (Y.card + B.card) + 1000 ∨
      9 * H.card ≤ N + 100 ∨
      ∃ a d len, 0 < len ∧ (d = 4 ∨ d = 8) ∧
        natAP a d len ⊆ highFourSums A N ∧ H.card ≤ 2 * (len + 1) := by
    rcases strong_reserve_or_fourAP hP hsub hlarge with hs | hp
    · exact Or.inl hs
    · obtain ⟨a, d, len, hd, hQ, hH⟩ := hp
      change H.card ≤ 2 * (len + 1) at hH
      by_cases hlen : 0 < len
      · rcases fourAP_step_or_small hsub hd hQ hH with hsmall | hstep
        · exact Or.inr (Or.inl hsmall)
        · exact Or.inr (Or.inr ⟨a, d, len, hlen, hstep, hQ, hH⟩)
      · right
        left
        have : len = 0 := by omega
        omega
  have hAcover := nonzero_decomposition hP hsub
  change A.card ≤ D.card + C₁.card + C₂.card + V₁.card + V₂.card at hAcover
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 1)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 3 + C at hDbound
  have hC₁sub : C₁ ⊆ lowNonthreeImage A N := by
    intro z hz
    exact (mem_lowNonthreeImagePart.mp hz).1
  have hC₂sub : C₂ ⊆ lowNonthreeImage A N := by
    intro z hz
    exact (mem_lowNonthreeImagePart.mp hz).1
  have hC₁res : ∀ z ∈ C₁, z % 3 = 1 := by
    intro z hz
    simpa using (mem_lowNonthreeImagePart.mp hz).2
  have hC₂res : ∀ z ∈ C₂, z % 3 = 2 := by
    intro z hz
    simpa using (mem_lowNonthreeImagePart.mp hz).2
  rcases le_total V₂.card V₁.card with h21 | h12c
  · have hmin : min V₁.card V₂.card = V₂.card := min_eq_right h21
    have hlower : V.card + 3 * Y.card + 3 * B.card ≤ 3 * V₁.card + 9 := by
      rw [hmin] at hrel
      omega
    have hdense : N / 6 + 6 ≤ 2 * V₁.card := by omega
    have hdense4 : N / 6 + 5 ≤ 2 * V₁.card := by omega
    have hVsub : V₁ ⊆ V := filter_subset _ _
    have hVres : ∀ x ∈ V₁, x % 3 = 1 := by
      intro x hx
      simpa using (mem_upperHalfResidue.mp hx).2
    have hp4 := upperThreeClass_pack_four (r := 1) hP hsub hVsub hVres
      (B := C₂) hC₂sub hC₂res hdense4
    have hp5 := upperThreeClass_pack_five (r := 1) hP hsub hVsub hVres
      (B := C₁) hC₁sub hC₁res hdense
    change 12 * C₂.card + 6 * V₁.card ≤ N + 24 at hp4
    change 10 * C₁.card + 4 * V₁.card ≤ N + 30 at hp5
    rcases hbonus with hstrong | hbonus
    · have hmaster :
          60 * A.card + 32 * Y.card + 54 * B.card ≤
            60 * D.card + 11 * N + 500 + 22 * H.card := by omega
      apply hfail
      exact hard_finish_standard_strong hN hDbound hcase3 hstrong hmaster
    · rcases hbonus with hsmall | ⟨a, d, len, hlen, hd, hQ, hH⟩
      · have hmaster :
            60 * A.card + 32 * Y.card + 54 * B.card ≤
              60 * D.card + 11 * N + 500 + 22 * H.card := by omega
        apply hfail
        exact hard_finish_standard_small hN hDbound hweak hsmall hmaster
      · have himp := improved_same_part_bound hP hsub (r := 1)
          (a := a) (d := d) (len := len) (Or.inl rfl) hd hlen hQ hH hdense
        change 90 * C₁.card + 36 * V₁.card + 15 * H.card ≤ 11 * N + 500 at himp
        have hmaster :
            180 * A.card + 96 * Y.card + 162 * B.card ≤
              180 * D.card + 37 * N + 2000 + 36 * H.card := by omega
        apply hfail
        exact hard_finish_improved hN hDbound hcase3 hweak hmaster
  · have hmin : min V₁.card V₂.card = V₁.card := min_eq_left h12c
    have hlower : V.card + 3 * Y.card + 3 * B.card ≤ 3 * V₂.card + 9 := by
      rw [hmin] at hrel
      omega
    have hdense : N / 6 + 6 ≤ 2 * V₂.card := by omega
    have hdense4 : N / 6 + 5 ≤ 2 * V₂.card := by omega
    have hVsub : V₂ ⊆ V := filter_subset _ _
    have hVres : ∀ x ∈ V₂, x % 3 = 2 := by
      intro x hx
      simpa using (mem_upperHalfResidue.mp hx).2
    have hp4 := upperThreeClass_pack_four (r := 2) hP hsub hVsub hVres
      (B := C₁) hC₁sub hC₁res hdense4
    have hp5 := upperThreeClass_pack_five (r := 2) hP hsub hVsub hVres
      (B := C₂) hC₂sub hC₂res hdense
    change 12 * C₁.card + 6 * V₂.card ≤ N + 24 at hp4
    change 10 * C₂.card + 4 * V₂.card ≤ N + 30 at hp5
    rcases hbonus with hstrong | hbonus
    · have hmaster :
          60 * A.card + 32 * Y.card + 54 * B.card ≤
            60 * D.card + 11 * N + 500 + 22 * H.card := by omega
      apply hfail
      exact hard_finish_standard_strong hN hDbound hcase3 hstrong hmaster
    · rcases hbonus with hsmall | ⟨a, d, len, hlen, hd, hQ, hH⟩
      · have hmaster :
            60 * A.card + 32 * Y.card + 54 * B.card ≤
              60 * D.card + 11 * N + 500 + 22 * H.card := by omega
        apply hfail
        exact hard_finish_standard_small hN hDbound hweak hsmall hmaster
      · have himp := improved_same_part_bound hP hsub (r := 2)
          (a := a) (d := d) (len := len) (Or.inr rfl) hd hlen hQ hH hdense
        change 90 * C₂.card + 36 * V₂.card + 15 * H.card ≤ 11 * N + 500 at himp
        have hmaster :
            180 * A.card + 96 * Y.card + 162 * B.card ≤
              180 * D.card + 37 * N + 2000 + 36 * H.card := by omega
        apply hfail
        exact hard_finish_improved hN hDbound hcase3 hweak hmaster

end Bedert

/-! The remaining sections implement the quantitative form of Bedert's
induction. -/

open Bedert

/-- Bedert's quantitative finite theorem, in the weaker form needed here. -/
private theorem bedert_bound : ∃ C : ℕ, ∀ N : ℕ, ∀ A ⊆ Icc 1 N,
    IsForbiddenTripleFree A → 3 * A.card ≤ N + C := by
  refine ⟨2000000000, ?_⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro A hsub hP
      change CoarseBound 2000000000 N A
      by_cases hsmallN : N < 1000000000
      · have hcard := card_le_card hsub
        simp only [Nat.card_Icc, Nat.add_sub_cancel_right] at hcard
        change 3 * A.card ≤ N + 2000000000
        omega
      have hN : 1000000000 ≤ N := by omega
      have hN1000 : 1000 ≤ N := by omega
      by_contra hfail
      have hhalfPos : 0 < (N + 1) / 2 := by omega
      have hhalfLe : (N + 1) / 2 ≤ N := by omega
      have hhalfLt : N - (N + 1) / 2 < N := by omega
      have hindInitial : CoarseBound 2000000000
          (N - (N + 1) / 2) (initialPart A N ((N + 1) / 2)) := by
        apply ih (N - (N + 1) / 2) hhalfLt
        · exact initialPart_subset_Icc hsub
        · exact initialPart_property hP
      have htail := terminal_dense_of_not_coarseBound
        hhalfPos hhalfLe hfail hindInitial
      rw [terminalPart_half_eq_upperHalf hsub] at htail
      have hind3 : CoarseBound 2000000000 (N / 3)
          ((divisibleInitial A N 3 1).image fun x ↦ x / 3) := by
        apply ih (N / 3) (by omega)
        · simpa using image_div_divisibleInitial_subset
            (A := A) (N := N) (k := 3) (ell := 1)
            (by omega) (by omega) hsub
        · exact image_div_divisibleInitial_property
            (A := A) (N := N) (k := 3) (ell := 1) (by omega) hP
      have hind6 : CoarseBound 2000000000 (N / 6)
          ((divisibleInitial A N 3 2).image fun x ↦ x / 3) := by
        apply ih (N / 6) (by omega)
        · simpa using image_div_divisibleInitial_subset
            (A := A) (N := N) (k := 3) (ell := 2)
            (by omega) (by omega) hsub
        · exact image_div_divisibleInitial_property
            (A := A) (N := N) (k := 3) (ell := 2) (by omega) hP
      by_cases hcase1 : 2 * N + 12 ≤ 9 * (highThird A N).card
      · have hb := caseOne hP hsub hcase1
        apply hfail
        change 3 * A.card ≤ N + 2000000000
        omega
      have hcase1' : 9 * (highThird A N).card < 2 * N + 12 := by omega
      by_cases hcase2 : N + 144 ≤ 6 * (highThird A N).card
      · have hb := caseTwo hP hsub hcase2 hcase1'
        apply hfail
        change 3 * A.card ≤ N + 2000000000
        omega
      have hcase3 : 6 * (highThird A N).card < N + 144 := by omega
      by_cases hzero : (upperHalf A N).card ≤
          3 * (upperHalfResidue A N 0).card
      · have hV0card : 0 < (upperHalfResidue A N 0).card := by
          change (N + 1) / 2 < 3 * (upperHalf A N).card at htail
          omega
        have hV0 : (upperHalfResidue A N 0).Nonempty := Finset.card_pos.mp hV0card
        rcases bgAlternative_self (upperHalfResidue A N 0) with hgrowth | hstruct
        · have hgrowth' : 3 * (upperHalfResidue A N 0).card ≤
              (upperHalfResidue A N 0 + upperHalfResidue A N 0).card + 3 := by
            omega
          have hb := caseThree_zero_growth_coarse hP hsub hzero hgrowth'
          apply hfail
          change 3 * A.card ≤ N + 2000000000
          omega
        · obtain ⟨a, d, hd, hQ, hres⟩ := hstruct
          have hQ' : natAP a d (2 * (upperHalfResidue A N 0).card - 1) ⊆
              upperHalfResidue A N 0 + upperHalfResidue A N 0 := by
            simpa [two_mul] using hQ
          have ha3 := zero_AP_start_dvd_three hV0 hQ'
          rcases zero_structural_step hsub hN1000 hV0 htail hzero hd hQ' hres with
            rfl | rfl | rfl
          · have hb := caseThree_zero_step_three
              hP hsub hV0 htail hzero hcase3 ha3 hQ'
            apply hfail
            change 3 * A.card ≤ N + 2000000000
            omega
          · have hb := caseThree_zero_step_six
              hP hsub hV0 hzero ha3 hQ' hres
            apply hfail
            change 3 * A.card ≤ N + 2000000000
            omega
          · apply hfail
            exact caseThree_zero_step_nine
              hP hsub hN1000 hV0 htail hzero ha3 hQ' hres hind6
      · have hparts := card_upperHalf_residues A N
        have hdom : 2 * (upperHalf A N).card ≤
            3 * ((upperHalfResidue A N 1).card +
              (upperHalfResidue A N 2).card) := by
          omega
        by_cases hV1 : (upperHalfResidue A N 1).Nonempty
        · by_cases hV2 : (upperHalfResidue A N 2).Nonempty
          · by_cases hmid : (highThird A N).card + 3 ≤
                2 * (middleSixth A N).card
            · have hb := caseThree_of_large_middle hP hsub hV1 hV2 hmid
              apply hfail
              change 3 * A.card ≤ N + 2000000000
              omega
            · rcases bgAlternative_of_nonempty hV1 hV2 with hgrowth | hstruct
              · by_cases hcover : (highThird A N).card + 3 ≤
                    (upperHalfResidue A N 1).card +
                      (upperHalfResidue A N 2).card +
                        min (upperHalfResidue A N 1).card
                          (upperHalfResidue A N 2).card
                · have hb := caseThree_nonzero_growth hP hsub hgrowth hcover
                  apply hfail
                  change 3 * A.card ≤ N + 2000000000
                  omega
                · exact caseThree_nonzero_growth_hard hP hsub hN
                    (by omega) htail hcase3 hdom hgrowth hind3 hfail
              · obtain ⟨a, d, hd, hQ, hres⟩ := hstruct
                have ha3 := nonzero_AP_start_dvd_three hV1 hV2 hQ
                rcases nonzero_structural_step hsub hN1000 hV1 hV2 htail hdom
                    hd hQ hres with rfl | rfl | rfl
                · have hb := caseThree_nonzero_step_three
                    hP hsub hV1 hV2 htail hdom hcase3 ha3 hQ
                  apply hfail
                  change 3 * A.card ≤ N + 2000000000
                  omega
                · have hb := caseThree_nonzero_step_six
                    hP hsub hV1 hV2 hdom ha3 hQ hres
                  apply hfail
                  change 3 * A.card ≤ N + 2000000000
                  omega
                · by_cases hat : (a / 3) % 3 = 0
                  · have haeq : 3 * (a / 3) = a := Nat.mul_div_cancel' ha3
                    have ha9 : a % 9 = 0 := by omega
                    have hb := caseThree_nonzero_step_nine_zero
                      hP hsub hV1 hV2 htail hdom ha9 hQ hres
                    apply hfail
                    change 3 * A.card ≤ N + 2000000000
                    omega
                  · apply hfail
                    exact caseThree_nonzero_step_nine_nonzero
                      hP hsub hN1000 hV1 hV2 htail hdom ha3 hat hQ hres hind6
          · apply hfail
            exact caseThree_nonzero_empty
              hP hsub hN1000 htail hdom hV2 hind3
        · apply hfail
          exact caseThree_nonzero_empty_one
            hP hsub hN1000 htail hdom hV1 hind3

/-- If `A ⊆ {1, ..., N}` has no `a,b,c ∈ A` such that `a ∣ b+c` and
`a < min b c`, then `|A| ≤ N/3 + O(1)`. -/
theorem erdos_13 : ∃ C : ℝ, ∀ N : ℕ, ∀ A ⊆ Icc 1 N, IsForbiddenTripleFree A →
    (A.card : ℝ) ≤ (N : ℝ) / 3 + C := by
  obtain ⟨C, hC⟩ := bedert_bound
  refine ⟨(C : ℝ) / 3, ?_⟩
  intro N A hsub hP
  have h := hC N A hsub hP
  have h' : (3 : ℝ) * (A.card : ℝ) ≤ (N : ℝ) + C := by
    exact_mod_cast h
  nlinarith

#print axioms Erdos13.erdos_13

end Erdos13
