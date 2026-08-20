/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# The finite local decoder for clique incidence

The short proof of design existence uses an explicit integer vector on the
`q`-subsets of a `(q+r)`-set whose boundary is supported at one prescribed
`r`-edge.  This file proves its inclusion--exclusion identity.  We index a
`q`-set by its `r`-element complement; the conversion back to clique
coordinates is supplied at the end.
-/

namespace Erdos722.LocalDecoder

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coefficient attached to a complement `C`.  Only subsets of `e ∩ C`
contribute. -/
def complementCoeff (q r : ℕ) (e C : Finset V) : ℤ :=
  ∑ I ∈ (e ∩ C).powerset,
    (-1 : ℤ) ^ I.card * q.descFactorial I.card * Nat.factorial (r - I.card)

/-- Uniform pointwise bound for the explicit decoder coefficients.  This
coarse bound is the one needed when averaging local decoders in the
regularity boost. -/
theorem natAbs_complementCoeff_le
    {q r : ℕ} (hq : 0 < q) {e C : Finset V} (hecard : e.card = r) :
    (complementCoeff q r e C).natAbs ≤
      (2 * q) ^ r * Nat.factorial r := by
  classical
  have hterm (I : Finset V) (hI : I ∈ (e ∩ C).powerset) :
      (( (-1 : ℤ) ^ I.card * q.descFactorial I.card *
          Nat.factorial (r - I.card))).natAbs ≤
        q ^ r * Nat.factorial r := by
    have hIe : I ⊆ e := (Finset.mem_powerset.mp hI).trans Finset.inter_subset_left
    have hir : I.card ≤ r := by
      rw [← hecard]
      exact Finset.card_le_card hIe
    have hdesc : q.descFactorial I.card ≤ q ^ I.card :=
      Nat.descFactorial_le_pow q I.card
    have hqpow : q ^ I.card ≤ q ^ r :=
      Nat.pow_le_pow_right hq hir
    have hfact : Nat.factorial (r - I.card) ≤ Nat.factorial r :=
      Nat.factorial_le (Nat.sub_le _ _)
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg,
      Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul (hdesc.trans hqpow) hfact
  calc
    (complementCoeff q r e C).natAbs ≤
        ∑ I ∈ (e ∩ C).powerset,
          (((-1 : ℤ) ^ I.card * q.descFactorial I.card *
            Nat.factorial (r - I.card))).natAbs := by
      unfold complementCoeff
      exact Int.natAbs_sum_le _ _
    _ ≤ ∑ _I ∈ (e ∩ C).powerset,
          (q ^ r * Nat.factorial r) := by
      apply Finset.sum_le_sum
      exact hterm
    _ = 2 ^ (e ∩ C).card * (q ^ r * Nat.factorial r) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
      norm_num
    _ ≤ 2 ^ r * (q ^ r * Nat.factorial r) := by
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_right (by omega)
      rw [← hecard]
      exact Finset.card_le_card Finset.inter_subset_left
    _ = (2 * q) ^ r * Nat.factorial r := by rw [mul_pow]; ring

private lemma powerset_inter_eq_filter (e C : Finset V) :
    (e ∩ C).powerset = e.powerset.filter (· ⊆ C) := by
  ext I
  simp only [mem_powerset, mem_filter, subset_inter_iff]

private lemma descFactorial_mul_factorial_choose
    {q r i : ℕ} (hir : i ≤ r) :
    q.descFactorial i * Nat.factorial (r - i) * Nat.choose (q - i) (r - i) =
      q.descFactorial r := by
  rw [Nat.mul_assoc, ← Nat.descFactorial_eq_factorial_mul_choose]
  rw [Nat.mul_comm, Nat.descFactorial_mul_descFactorial hir]

private lemma inner_complement_sum
    {q r : ℕ} {Z e' I : Finset V}
    (hZcard : Z.card = q + r) (he'card : e'.card = r)
    (he'Z : e' ⊆ Z) (hIr : I.card ≤ r) :
    (∑ C ∈ (Z \ e').powersetCard r,
        if I ⊆ C then
          ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
            Nat.factorial (r - I.card))
        else 0) =
      if I ⊆ Z \ e' then
        (-1 : ℤ) ^ I.card * q.descFactorial r
      else 0 := by
  by_cases hIbase : I ⊆ Z \ e'
  · rw [if_pos hIbase]
    have hbasecard : (Z \ e').card = q := by
      rw [card_sdiff_of_subset he'Z, hZcard, he'card]
      omega
    have hcount := card_filter_powersetCard_subset I (Z \ e') r hIbase hIr
    calc
      (∑ C ∈ (Z \ e').powersetCard r,
          if I ⊆ C then
            ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
              Nat.factorial (r - I.card))
          else 0) =
          (((((Z \ e').powersetCard r).filter (I ⊆ ·)).card : ℕ) : ℤ) *
            ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
              Nat.factorial (r - I.card)) := by
        simp [Finset.sum_ite]
      _ = (Nat.choose (q - I.card) (r - I.card) : ℤ) *
            ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
              Nat.factorial (r - I.card)) := by
        rw [hcount, hbasecard]
      _ = (-1 : ℤ) ^ I.card * q.descFactorial r := by
        have hnat := descFactorial_mul_factorial_choose
          (q := q) (r := r) (i := I.card) hIr
        calc
          (Nat.choose (q - I.card) (r - I.card) : ℤ) *
                ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
                  Nat.factorial (r - I.card)) =
              (-1 : ℤ) ^ I.card *
                (q.descFactorial I.card * Nat.factorial (r - I.card) *
                  Nat.choose (q - I.card) (r - I.card) : ℕ) := by
            push_cast
            ring
          _ = (-1 : ℤ) ^ I.card * q.descFactorial r := by rw [hnat]
  · rw [if_neg hIbase]
    apply Finset.sum_eq_zero
    intro C hC
    have hCZ : C ⊆ Z \ e' := (mem_powersetCard.mp hC).1
    rw [if_neg]
    exact fun hIC ↦ hIbase (hIC.trans hCZ)

/-- Complement-indexed form of the local decoder identity. -/
theorem sum_complementCoeff
    {q r : ℕ} {Z e e' : Finset V}
    (hZcard : Z.card = q + r)
    (hecard : e.card = r) (he'card : e'.card = r)
    (heZ : e ⊆ Z) (he'Z : e' ⊆ Z) :
    (∑ C ∈ (Z \ e').powersetCard r, complementCoeff q r e C) =
      if e = e' then (q.descFactorial r : ℤ) else 0 := by
  classical
  have hre (I : Finset V) (hIe : I ∈ e.powerset) : I.card ≤ r := by
    rw [← hecard]
    exact card_le_card (mem_powerset.mp hIe)
  calc
    (∑ C ∈ (Z \ e').powersetCard r, complementCoeff q r e C) =
        ∑ C ∈ (Z \ e').powersetCard r, ∑ I ∈ e.powerset,
          if I ⊆ C then
          ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
            Nat.factorial (r - I.card))
          else 0 := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [complementCoeff, powerset_inter_eq_filter]
      simp [Finset.sum_filter]
    _ = ∑ I ∈ e.powerset, ∑ C ∈ (Z \ e').powersetCard r,
          if I ⊆ C then
            ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
              Nat.factorial (r - I.card))
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ I ∈ e.powerset,
          if I ⊆ Z \ e' then
            (-1 : ℤ) ^ I.card * q.descFactorial r
          else 0 := by
      apply Finset.sum_congr rfl
      intro I hIe
      exact inner_complement_sum hZcard he'card he'Z (hre I hIe)
    _ = ∑ I ∈ (e \ e').powerset,
          (-1 : ℤ) ^ I.card * q.descFactorial r := by
      rw [← Finset.sum_filter]
      congr 1
      ext I
      simp only [mem_filter, mem_powerset, subset_sdiff]
      constructor
      · rintro ⟨hIe, hIZ, hIe'⟩
        exact ⟨hIe, hIe'⟩
      · rintro ⟨hIe, hIe'⟩
        exact ⟨hIe, hIe.trans heZ, hIe'⟩
    _ = (∑ I ∈ (e \ e').powerset, (-1 : ℤ) ^ I.card) *
          q.descFactorial r := by
      rw [Finset.sum_mul]
    _ = if e = e' then (q.descFactorial r : ℤ) else 0 := by
      rw [Finset.sum_powerset_neg_one_pow_card]
      by_cases heq : e = e'
      · subst e'
        simp
      · have hne : e \ e' ≠ ∅ := by
          intro hzero
          have hsub : e ⊆ e' := sdiff_eq_empty_iff_subset.mp hzero
          exact heq (Finset.eq_of_subset_of_card_le hsub (by omega))
        simp [heq, hne]

/-- The coefficient on a `q`-set is the coefficient on its complement in
the ambient `(q+r)`-set. -/
def cliqueCoeff (q r : ℕ) (Z e Q : Finset V) : ℤ :=
  complementCoeff q r e (Z \ Q)

theorem natAbs_cliqueCoeff_le
    {q r : ℕ} (hq : 0 < q) {Z e Q : Finset V} (hecard : e.card = r) :
    (cliqueCoeff q r Z e Q).natAbs ≤
      (2 * q) ^ r * Nat.factorial r := by
  exact natAbs_complementCoeff_le hq hecard

/-- Clique-indexed local decoder identity.  The boundary of the coefficient
vector is `q.descFactorial r` at `e` and zero at every other `r`-edge of
`Z`. -/
theorem sum_cliqueCoeff
    {q r : ℕ} {Z e e' : Finset V}
    (hZcard : Z.card = q + r)
    (hecard : e.card = r) (he'card : e'.card = r)
    (heZ : e ⊆ Z) (he'Z : e' ⊆ Z) :
    (∑ Q ∈ (Z.powersetCard q).filter (e' ⊆ ·),
        cliqueCoeff q r Z e Q) =
      if e = e' then (q.descFactorial r : ℤ) else 0 := by
  classical
  calc
    (∑ Q ∈ (Z.powersetCard q).filter (e' ⊆ ·),
        cliqueCoeff q r Z e Q) =
        ∑ C ∈ (Z \ e').powersetCard r, complementCoeff q r e C := by
      refine Finset.sum_bij'
        (i := fun Q _ ↦ Z \ Q) (j := fun C _ ↦ Z \ C) ?_ ?_ ?_ ?_ ?_
      · intro Q hQ
        have hm := mem_filter.mp hQ
        have hQdata := mem_powersetCard.mp hm.1
        apply mem_powersetCard.mpr
        constructor
        · intro x hx
          have hxdata := mem_sdiff.mp hx
          exact mem_sdiff.mpr ⟨hxdata.1, fun hxe' ↦ hxdata.2 (hm.2 hxe')⟩
        · rw [card_sdiff_of_subset hQdata.1, hZcard, hQdata.2]
          omega
      · intro C hC
        have hCdata := mem_powersetCard.mp hC
        have hCZ : C ⊆ Z := hCdata.1.trans sdiff_subset
        apply mem_filter.mpr
        constructor
        · apply mem_powersetCard.mpr
          refine ⟨sdiff_subset, ?_⟩
          rw [card_sdiff_of_subset hCZ, hZcard, hCdata.2]
          omega
        · intro x hxe'
          apply mem_sdiff.mpr
          refine ⟨he'Z hxe', ?_⟩
          intro hxC
          exact (mem_sdiff.mp (hCdata.1 hxC)).2 hxe'
      · intro Q hQ
        exact Finset.sdiff_sdiff_eq_self
          (mem_powersetCard.mp (mem_filter.mp hQ).1).1
      · intro C hC
        exact Finset.sdiff_sdiff_eq_self
          ((mem_powersetCard.mp hC).1.trans sdiff_subset)
      · intro Q hQ
        rfl
    _ = if e = e' then (q.descFactorial r : ℤ) else 0 :=
      sum_complementCoeff hZcard hecard he'card heZ he'Z

/-- Boundary of an integer vector on the `q`-subsets of `Z`. -/
def intBoundary (Z : Finset V) (q : ℕ) (φ : Finset V → ℤ)
    (e : Finset V) : ℤ :=
  ∑ Q ∈ Z.powersetCard q, if e ⊆ Q then φ Q else 0

/-! ### Superposition of local delta decoders -/

/-- Sum of the explicit local delta decoders rooted at `roots`.  The
membership test is important: `cliqueCoeff` is an algebraic formula on all
finite sets, whereas a local decoder uses it only on the `q`-subsets of its
assigned `(q+r)`-set. -/
def superposedDecoder (roots : Finset (Finset V))
    (Z : Finset V → Finset V) (q r : ℕ)
    (m : Finset V → ℤ) (Q : Finset V) : ℤ :=
  ∑ e ∈ roots,
    if Q ∈ (Z e).powersetCard q then
      m e * cliqueCoeff q r (Z e) e Q
    else 0

private theorem sum_superposedDecoder_single
    {U : Finset V} {roots : Finset (Finset V)}
    {Z : Finset V → Finset V} {q r : ℕ}
    {m : Finset V → ℤ} {e e' : Finset V}
    (he : e ∈ roots) (her : e.card = r) (heZ : e ⊆ Z e)
    (hZU : Z e ⊆ U) (hZcard : (Z e).card = q + r)
    (he'card : e'.card = r) :
    (∑ Q ∈ U.powersetCard q,
        if e' ⊆ Q then
          (if Q ∈ (Z e).powersetCard q then
            m e * cliqueCoeff q r (Z e) e Q
          else 0)
        else 0) =
      if e = e' then m e * (q.descFactorial r : ℤ) else 0 := by
  classical
  by_cases he'Z : e' ⊆ Z e
  · have hfilter :
        (U.powersetCard q).filter (fun Q ↦
            e' ⊆ Q ∧ Q ∈ (Z e).powersetCard q) =
          ((Z e).powersetCard q).filter (e' ⊆ ·) := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hQU, hQcard⟩, he'Q, hQZ, _⟩
        exact ⟨⟨hQZ, hQcard⟩, he'Q⟩
      · rintro ⟨⟨hQZ, hQcard⟩, he'Q⟩
        exact ⟨⟨hQZ.trans hZU, hQcard⟩, he'Q, hQZ, hQcard⟩
    calc
      (∑ Q ∈ U.powersetCard q,
          if e' ⊆ Q then
            (if Q ∈ (Z e).powersetCard q then
              m e * cliqueCoeff q r (Z e) e Q
            else 0)
          else 0) =
          ∑ Q ∈ (U.powersetCard q).filter (fun Q ↦
              e' ⊆ Q ∧ Q ∈ (Z e).powersetCard q),
            m e * cliqueCoeff q r (Z e) e Q := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro Q hQ
        by_cases he'Q : e' ⊆ Q <;>
          by_cases hQZ : Q ∈ (Z e).powersetCard q <;>
          simp [he'Q, hQZ]
      _ = m e * ∑ Q ∈ ((Z e).powersetCard q).filter (e' ⊆ ·),
            cliqueCoeff q r (Z e) e Q := by
        rw [hfilter, Finset.mul_sum]
      _ = if e = e' then m e * (q.descFactorial r : ℤ) else 0 := by
        rw [sum_cliqueCoeff hZcard her he'card heZ he'Z]
        split_ifs <;> simp
  · have hne : e ≠ e' := by
      intro heq
      subst e'
      exact he'Z heZ
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro Q hQU
    by_cases he'Q : e' ⊆ Q
    · rw [if_pos he'Q, if_neg]
      intro hQZ
      exact he'Z (he'Q.trans (Finset.mem_powersetCard.mp hQZ).1)
    · simp [he'Q]

/-- Superposing explicit local decoders gives the prescribed multiple of
the coordinate vector on `roots`, and zero on every other `r`-edge of the
ambient set.  No disjointness between the local `(q+r)`-sets is required
for this boundary identity. -/
theorem intBoundary_superposedDecoder
    {U : Finset V} {roots : Finset (Finset V)}
    {Z : Finset V → Finset V} {q r : ℕ}
    {m : Finset V → ℤ}
    (hroot : ∀ e ∈ roots, e ∈ U.powersetCard r)
    (heZ : ∀ e ∈ roots, e ⊆ Z e)
    (hZU : ∀ e ∈ roots, Z e ⊆ U)
    (hZcard : ∀ e ∈ roots, (Z e).card = q + r)
    {e' : Finset V} (he' : e' ∈ U.powersetCard r) :
    intBoundary U q (superposedDecoder roots Z q r m) e' =
      (q.descFactorial r : ℤ) * (if e' ∈ roots then m e' else 0) := by
  classical
  have he'card : e'.card = r := (Finset.mem_powersetCard.mp he').2
  calc
    intBoundary U q (superposedDecoder roots Z q r m) e' =
        ∑ Q ∈ U.powersetCard q, ∑ e ∈ roots,
          if e' ⊆ Q then
            (if Q ∈ (Z e).powersetCard q then
              m e * cliqueCoeff q r (Z e) e Q
            else 0)
          else 0 := by
      rw [intBoundary]
      apply Finset.sum_congr rfl
      intro Q hQ
      by_cases he'Q : e' ⊆ Q
      · simp only [if_pos he'Q, superposedDecoder]
      · simp [he'Q, superposedDecoder]
    _ = ∑ e ∈ roots, ∑ Q ∈ U.powersetCard q,
          if e' ⊆ Q then
            (if Q ∈ (Z e).powersetCard q then
              m e * cliqueCoeff q r (Z e) e Q
            else 0)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ roots,
          if e = e' then m e * (q.descFactorial r : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      exact sum_superposedDecoder_single he
        (Finset.mem_powersetCard.mp (hroot e he)).2
        (heZ e he) (hZU e he) (hZcard e he) he'card
    _ = (q.descFactorial r : ℤ) * (if e' ∈ roots then m e' else 0) := by
      by_cases he'root : e' ∈ roots
      · rw [if_pos he'root]
        simp [he'root, mul_comm]
      · rw [if_neg he'root]
        apply Finset.sum_eq_zero
        intro e he
        have hne : e ≠ e' := fun h ↦ he'root (h ▸ he)
        simp [hne]

theorem superposedDecoder_ne_zero_support
    {roots : Finset (Finset V)} {Z : Finset V → Finset V}
    {q r : ℕ} {m : Finset V → ℤ} {Q : Finset V}
    (hQ : superposedDecoder roots Z q r m Q ≠ 0) :
    ∃ e ∈ roots, Q ∈ (Z e).powersetCard q := by
  classical
  by_contra hnone
  push_neg at hnone
  apply hQ
  rw [superposedDecoder]
  apply Finset.sum_eq_zero
  intro e he
  simp [hnone e he]

/-- When the assigned `q`-set families are pairwise disjoint and every
root multiplier has absolute value at most one, the superposition retains
the pointwise coefficient bound of one explicit decoder. -/
theorem natAbs_superposedDecoder_le
    {roots : Finset (Finset V)} {Z : Finset V → Finset V}
    {q r : ℕ} {m : Finset V → ℤ}
    (hq : 0 < q)
    (hrootcard : ∀ e ∈ roots, e.card = r)
    (hm : ∀ e ∈ roots, (m e).natAbs ≤ 1)
    (hdisjoint : ∀ e ∈ roots, ∀ e' ∈ roots, e ≠ e' →
      Disjoint ((Z e).powersetCard q) ((Z e').powersetCard q))
    (Q : Finset V) :
    (superposedDecoder roots Z q r m Q).natAbs ≤
      (2 * q) ^ r * Nat.factorial r := by
  classical
  by_cases hsome : ∃ e ∈ roots, Q ∈ (Z e).powersetCard q
  · obtain ⟨e, he, hQe⟩ := hsome
    have hsum : superposedDecoder roots Z q r m Q =
        m e * cliqueCoeff q r (Z e) e Q := by
      rw [superposedDecoder, Finset.sum_eq_single_of_mem e he]
      · simp [hQe]
      · intro e' he' hne
        have hQnot : Q ∉ (Z e').powersetCard q := by
          intro hQe'
          exact Finset.disjoint_left.mp
            (hdisjoint e' he' e he hne) hQe' hQe
        simp [hQnot]
    rw [hsum, Int.natAbs_mul]
    calc
      (m e).natAbs * (cliqueCoeff q r (Z e) e Q).natAbs ≤
          1 * ((2 * q) ^ r * Nat.factorial r) :=
        Nat.mul_le_mul (hm e he)
          (natAbs_cliqueCoeff_le hq (hrootcard e he))
      _ = (2 * q) ^ r * Nat.factorial r := by simp
  · push_neg at hsome
    rw [superposedDecoder]
    have hzero : ∀ e ∈ roots,
        (if Q ∈ (Z e).powersetCard q then
          m e * cliqueCoeff q r (Z e) e Q else 0) = 0 := by
      intro e he
      rw [if_neg (hsome e he)]
    rw [Finset.sum_eq_zero hzero]
    simp

/-- Normalized real local-decoder coefficient. -/
noncomputable def decoderWeight (q r : ℕ) (Z e Q : Finset V) : ℝ :=
  (cliqueCoeff q r Z e Q : ℝ) / q.descFactorial r

/-- The normalized decoder has boundary exactly the coordinate vector at
the prescribed edge. -/
theorem sum_decoderWeight
    {q r : ℕ} (hrq : r ≤ q) {Z e e' : Finset V}
    (hZcard : Z.card = q + r)
    (hecard : e.card = r) (he'card : e'.card = r)
    (heZ : e ⊆ Z) (he'Z : e' ⊆ Z) :
    (∑ Q ∈ (Z.powersetCard q).filter (e' ⊆ ·),
        decoderWeight q r Z e Q) = if e = e' then 1 else 0 := by
  have hN : 0 < q.descFactorial r := Nat.descFactorial_pos.mpr hrq
  unfold decoderWeight
  rw [← Finset.sum_div]
  have hsum := sum_cliqueCoeff hZcard hecard he'card heZ he'Z
  have hsumReal :
      (∑ Q ∈ (Z.powersetCard q).filter (e' ⊆ ·),
          (cliqueCoeff q r Z e Q : ℝ)) =
        if e = e' then (q.descFactorial r : ℝ) else 0 := by
    exact_mod_cast hsum
  rw [hsumReal]
  split_ifs <;> simp [show (q.descFactorial r : ℝ) ≠ 0 by exact_mod_cast hN.ne']

theorem abs_decoderWeight_le
    {q r : ℕ} (hq : 0 < q) (hrq : r ≤ q)
    {Z e Q : Finset V} (hecard : e.card = r) :
    |decoderWeight q r Z e Q| ≤
      (((2 * q) ^ r * Nat.factorial r : ℕ) : ℝ) /
        q.descFactorial r := by
  have hN : (0 : ℝ) < q.descFactorial r := by
    exact_mod_cast Nat.descFactorial_pos.mpr hrq
  unfold decoderWeight
  rw [abs_div, abs_of_nonneg hN.le]
  apply div_le_div_of_nonneg_right _ hN.le
  have hcoeff := natAbs_cliqueCoeff_le (Z := Z) (Q := Q) hq hecard
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast hcoeff

/-- Integer degree of an integer-valued `r`-graph at a face `I`. -/
def intLocalDegree (Z : Finset V) (r : ℕ) (J : Finset V → ℤ)
    (I : Finset V) : ℤ :=
  ∑ e ∈ Z.powersetCard r, if I ⊆ e then J e else 0

/-- The local degree congruences for an integer-valued `r`-graph. -/
def IsLocallyDivisible (Z : Finset V) (q r : ℕ)
    (J : Finset V → ℤ) : Prop :=
  ∀ I ⊆ Z, I.card ≤ r →
    (Nat.choose (q - I.card) (r - I.card) : ℤ) ∣
      intLocalDegree Z r J I

/-- Numerator obtained by applying all local decoders to `J`. -/
def decoderNumerator (Z : Finset V) (q r : ℕ)
    (J : Finset V → ℤ) (Q : Finset V) : ℤ :=
  ∑ e ∈ Z.powersetCard r, J e * cliqueCoeff q r Z e Q

private lemma powerset_inter_eq_filter_left (e C : Finset V) :
    (e ∩ C).powerset = C.powerset.filter (· ⊆ e) := by
  ext I
  simp only [mem_powerset, mem_filter, subset_inter_iff]
  tauto

private lemma decoderNumerator_eq
    (Z : Finset V) (q r : ℕ) (J : Finset V → ℤ)
    (Q : Finset V) :
    decoderNumerator Z q r J Q =
      ∑ I ∈ (Z \ Q).powerset,
        ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
          Nat.factorial (r - I.card)) * intLocalDegree Z r J I := by
  classical
  calc
    decoderNumerator Z q r J Q =
        ∑ e ∈ Z.powersetCard r, J e *
          ∑ I ∈ (Z \ Q).powerset,
            if I ⊆ e then
              ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
                Nat.factorial (r - I.card))
            else 0 := by
      rw [decoderNumerator]
      apply Finset.sum_congr rfl
      intro e he
      rw [cliqueCoeff, complementCoeff,
        powerset_inter_eq_filter_left]
      congr 1
      simp [Finset.sum_filter]
    _ = ∑ e ∈ Z.powersetCard r, ∑ I ∈ (Z \ Q).powerset,
          J e *
            (if I ⊆ e then
              ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
                Nat.factorial (r - I.card))
            else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
    _ = ∑ I ∈ (Z \ Q).powerset, ∑ e ∈ Z.powersetCard r,
          J e *
            (if I ⊆ e then
              ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
                Nat.factorial (r - I.card))
            else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ I ∈ (Z \ Q).powerset,
        ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
          Nat.factorial (r - I.card)) * intLocalDegree Z r J I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [intLocalDegree, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hIe : I ⊆ e <;> simp [hIe]
      ring

private lemma decoderNumerator_dvd
    {Z : Finset V} {q r : ℕ} {J : Finset V → ℤ}
    (hZcard : Z.card = q + r) (hlocal : IsLocallyDivisible Z q r J)
    {Q : Finset V} (hQ : Q ∈ Z.powersetCard q) :
    (q.descFactorial r : ℤ) ∣ decoderNumerator Z q r J Q := by
  classical
  rw [decoderNumerator_eq]
  apply Finset.dvd_sum
  intro I hI
  have hQdata := mem_powersetCard.mp hQ
  have hCcard : (Z \ Q).card = r := by
    rw [card_sdiff_of_subset hQdata.1, hZcard, hQdata.2]
    omega
  have hIZ : I ⊆ Z := (mem_powerset.mp hI).trans sdiff_subset
  have hIr : I.card ≤ r := by
    rw [← hCcard]
    exact card_le_card (mem_powerset.mp hI)
  obtain ⟨z, hz⟩ := hlocal I hIZ hIr
  refine ⟨(-1 : ℤ) ^ I.card * z, ?_⟩
  have hnat := descFactorial_mul_factorial_choose
    (q := q) (r := r) (i := I.card) hIr
  rw [hz]
  calc
    ((-1 : ℤ) ^ I.card * q.descFactorial I.card *
          Nat.factorial (r - I.card)) *
        ((Nat.choose (q - I.card) (r - I.card) : ℤ) * z) =
      (-1 : ℤ) ^ I.card *
        (q.descFactorial I.card * Nat.factorial (r - I.card) *
          Nat.choose (q - I.card) (r - I.card) : ℕ) * z := by
      push_cast
      ring
    _ = (q.descFactorial r : ℤ) * ((-1 : ℤ) ^ I.card * z) := by
      rw [hnat]
      ring

private lemma boundary_decoderNumerator
    {Z : Finset V} {q r : ℕ} (J : Finset V → ℤ)
    (hZcard : Z.card = q + r)
    {e' : Finset V} (he' : e' ∈ Z.powersetCard r) :
    intBoundary Z q (decoderNumerator Z q r J) e' =
      (q.descFactorial r : ℤ) * J e' := by
  classical
  have he'data := mem_powersetCard.mp he'
  calc
    intBoundary Z q (decoderNumerator Z q r J) e' =
        ∑ Q ∈ (Z.powersetCard q).filter (e' ⊆ ·),
          decoderNumerator Z q r J Q := by
      rw [intBoundary, ← Finset.sum_filter]
    _ = ∑ Q ∈ (Z.powersetCard q).filter (e' ⊆ ·),
          ∑ e ∈ Z.powersetCard r, J e * cliqueCoeff q r Z e Q := by rfl
    _ = ∑ e ∈ Z.powersetCard r, J e *
          ∑ Q ∈ (Z.powersetCard q).filter (e' ⊆ ·),
            cliqueCoeff q r Z e Q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
    _ = ∑ e ∈ Z.powersetCard r, J e *
          (if e = e' then (q.descFactorial r : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      have hedata := mem_powersetCard.mp he
      rw [sum_cliqueCoeff hZcard hedata.2 he'data.2 hedata.1 he'data.1]
    _ = (q.descFactorial r : ℤ) * J e' := by
      simp [he', mul_comm]

/-- On a `(q+r)`-vertex set the local degree congruences already give an
integer clique decomposition.  This is the base case in the induction that
identifies the full clique-incidence lattice. -/
theorem exists_intBoundary_eq_of_card_add
    {Z : Finset V} {q r : ℕ} {J : Finset V → ℤ}
    (hrq : r ≤ q) (hZcard : Z.card = q + r)
    (hlocal : IsLocallyDivisible Z q r J) :
    ∃ φ : Finset V → ℤ, ∀ e ∈ Z.powersetCard r,
      intBoundary Z q φ e = J e := by
  classical
  have hNne : (q.descFactorial r : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hrq))
  have hdiv (Q : Finset V) (hQ : Q ∈ Z.powersetCard q) :
      (q.descFactorial r : ℤ) ∣ decoderNumerator Z q r J Q :=
    decoderNumerator_dvd hZcard hlocal hQ
  let φ : Finset V → ℤ := fun Q ↦
    if hQ : Q ∈ Z.powersetCard q then Classical.choose (hdiv Q hQ) else 0
  have hφ (Q : Finset V) (hQ : Q ∈ Z.powersetCard q) :
      decoderNumerator Z q r J Q = (q.descFactorial r : ℤ) * φ Q := by
    simp only [φ, dif_pos hQ]
    exact Classical.choose_spec (hdiv Q hQ)
  refine ⟨φ, ?_⟩
  intro e he
  apply mul_left_cancel₀ hNne
  calc
    (q.descFactorial r : ℤ) * intBoundary Z q φ e =
        intBoundary Z q (decoderNumerator Z q r J) e := by
      rw [intBoundary, intBoundary, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q hQ
      by_cases h : e ⊆ Q
      · simp only [if_pos h]
        rw [hφ Q hQ]
      · simp [h]
    _ = (q.descFactorial r : ℤ) * J e :=
      boundary_decoderNumerator J hZcard he

private lemma sum_containing_indicator
    {Z I Q : Finset V} {r : ℕ} (hQZ : Q ⊆ Z) (hIr : I.card ≤ r) :
    (∑ e ∈ Z.powersetCard r,
        if I ⊆ e then (if e ⊆ Q then (1 : ℤ) else 0) else 0) =
      if I ⊆ Q then
        (Nat.choose (Q.card - I.card) (r - I.card) : ℤ)
      else 0 := by
  classical
  by_cases hIQ : I ⊆ Q
  · rw [if_pos hIQ]
    have heq :
        (Z.powersetCard r).filter (fun e ↦ I ⊆ e ∧ e ⊆ Q) =
          (Q.powersetCard r).filter (I ⊆ ·) := by
      ext e
      simp only [mem_filter, mem_powersetCard]
      constructor
      · rintro ⟨⟨heZ, her⟩, hIe, heQ⟩
        exact ⟨⟨heQ, her⟩, hIe⟩
      · rintro ⟨⟨heQ, her⟩, hIe⟩
        exact ⟨⟨heQ.trans hQZ, her⟩, hIe, heQ⟩
    calc
      (∑ e ∈ Z.powersetCard r,
          if I ⊆ e then (if e ⊆ Q then (1 : ℤ) else 0) else 0) =
          ((((Z.powersetCard r).filter
            (fun e ↦ I ⊆ e ∧ e ⊆ Q)).card : ℕ) : ℤ) := by
        rw [← Finset.sum_boole (R := ℤ)
          (fun e ↦ I ⊆ e ∧ e ⊆ Q) (Z.powersetCard r)]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hIe : I ⊆ e <;> by_cases heQ : e ⊆ Q <;>
          simp [hIe, heQ]
      _ = ((((Q.powersetCard r).filter (I ⊆ ·)).card : ℕ) : ℤ) := by rw [heq]
      _ = (Nat.choose (Q.card - I.card) (r - I.card) : ℤ) := by
        exact_mod_cast card_filter_powersetCard_subset I Q r hIQ hIr
  · rw [if_neg hIQ]
    apply Finset.sum_eq_zero
    intro e he
    by_cases hIe : I ⊆ e
    · have hnot : ¬e ⊆ Q := fun heQ ↦ hIQ (hIe.trans heQ)
      simp [hIe, hnot]
    · simp [hIe]

/-- The local degree of an integer clique boundary is the expected binomial
multiple of the sum of clique coefficients through the face. -/
theorem intLocalDegree_intBoundary
    {Z I : Finset V} {q r : ℕ} (φ : Finset V → ℤ)
    (hIZ : I ⊆ Z) (hIr : I.card ≤ r) :
    intLocalDegree Z r (intBoundary Z q φ) I =
      (Nat.choose (q - I.card) (r - I.card) : ℤ) *
        ∑ Q ∈ Z.powersetCard q, if I ⊆ Q then φ Q else 0 := by
  classical
  calc
    intLocalDegree Z r (intBoundary Z q φ) I =
        ∑ e ∈ Z.powersetCard r, ∑ Q ∈ Z.powersetCard q,
          if I ⊆ e then (if e ⊆ Q then φ Q else 0) else 0 := by
      rw [intLocalDegree]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hIe : I ⊆ e
      · simp [hIe, intBoundary]
      · simp [hIe]
    _ = ∑ Q ∈ Z.powersetCard q, ∑ e ∈ Z.powersetCard r,
          if I ⊆ e then (if e ⊆ Q then φ Q else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ Q ∈ Z.powersetCard q,
          (Nat.choose (q - I.card) (r - I.card) : ℤ) *
            (if I ⊆ Q then φ Q else 0) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have hQdata := mem_powersetCard.mp hQ
      have hcount := sum_containing_indicator
        (r := r) hQdata.1 hIr
      rw [hQdata.2] at hcount
      calc
        (∑ e ∈ Z.powersetCard r,
            if I ⊆ e then (if e ⊆ Q then φ Q else 0) else 0) =
            (∑ e ∈ Z.powersetCard r,
              if I ⊆ e then (if e ⊆ Q then (1 : ℤ) else 0) else 0) *
                φ Q := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e he
          split_ifs <;> simp
        _ = (if I ⊆ Q then
              (Nat.choose (q - I.card) (r - I.card) : ℤ)
            else 0) * φ Q := by rw [hcount]
        _ = (Nat.choose (q - I.card) (r - I.card) : ℤ) *
            (if I ⊆ Q then φ Q else 0) := by
          split_ifs <;> simp
    _ = (Nat.choose (q - I.card) (r - I.card) : ℤ) *
        ∑ Q ∈ Z.powersetCard q, if I ⊆ Q then φ Q else 0 := by
      rw [Finset.mul_sum]

/-- Every integer clique boundary satisfies all local degree congruences. -/
theorem isLocallyDivisible_intBoundary
    {Z : Finset V} {q r : ℕ} (φ : Finset V → ℤ) :
    IsLocallyDivisible Z q r (intBoundary Z q φ) := by
  intro I hIZ hIr
  rw [intLocalDegree_intBoundary φ hIZ hIr]
  exact dvd_mul_right _ _

private lemma sum_powersetCard_filter_mem_erase
    {M : Type*} [AddCommMonoid M]
    {Z : Finset V} {v : V} {m : ℕ} (hvm : v ∈ Z) (hm : 0 < m)
    (f : Finset V → M) :
    (∑ S ∈ (Z.powersetCard m).filter (v ∈ ·), f (S.erase v)) =
      ∑ T ∈ (Z.erase v).powersetCard (m - 1), f T := by
  classical
  refine Finset.sum_bij'
    (i := fun S _ ↦ S.erase v) (j := fun T _ ↦ insert v T) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    have hmS := mem_filter.mp hS
    have hSdata := mem_powersetCard.mp hmS.1
    apply mem_powersetCard.mpr
    constructor
    · intro x hx
      have hxS := mem_erase.mp hx
      exact mem_erase.mpr ⟨hxS.1, hSdata.1 hxS.2⟩
    · rw [card_erase_of_mem hmS.2, hSdata.2]
  · intro T hT
    have hTdata := mem_powersetCard.mp hT
    have hvT : v ∉ T := by
      intro hv
      exact (mem_erase.mp (hTdata.1 hv)).1 rfl
    apply mem_filter.mpr
    constructor
    · apply mem_powersetCard.mpr
      constructor
      · intro x hx
        rcases mem_insert.mp hx with rfl | hxT
        · exact hvm
        · exact (mem_erase.mp (hTdata.1 hxT)).2
      · rw [card_insert_of_notMem hvT, hTdata.2]
        omega
    · exact mem_insert_self v T
  · intro S hS
    exact insert_erase (mem_filter.mp hS).2
  · intro T hT
    apply erase_insert
    intro hvT
    exact (mem_erase.mp ((mem_powersetCard.mp hT).1 hvT)).1 rfl
  · intro S hS
    rfl

/-- Link of an integer hypergraph at a vertex. -/
def intLink (v : V) (J : Finset V → ℤ) (e : Finset V) : ℤ :=
  J (insert v e)

private lemma intLocalDegree_link
    {Z I : Finset V} {v : V} {r : ℕ} (J : Finset V → ℤ)
    (hvZ : v ∈ Z) (hvI : v ∉ I) (hr : 0 < r) :
    intLocalDegree (Z.erase v) (r - 1) (intLink v J) I =
      intLocalDegree Z r J (insert v I) := by
  classical
  calc
    intLocalDegree (Z.erase v) (r - 1) (intLink v J) I =
        ∑ T ∈ (Z.erase v).powersetCard (r - 1),
          if I ⊆ T then J (insert v T) else 0 := by rfl
    _ = ∑ E ∈ (Z.powersetCard r).filter (v ∈ ·),
          if I ⊆ E.erase v then J (insert v (E.erase v)) else 0 := by
      symm
      exact sum_powersetCard_filter_mem_erase hvZ hr
        (fun T ↦ if I ⊆ T then J (insert v T) else 0)
    _ = ∑ E ∈ Z.powersetCard r, if v ∈ E then
          (if I ⊆ E.erase v then J (insert v (E.erase v)) else 0)
        else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ E ∈ Z.powersetCard r,
          if insert v I ⊆ E then J E else 0 := by
      apply Finset.sum_congr rfl
      intro E hE
      by_cases hvE : v ∈ E
      · have hins : insert v (E.erase v) = E := insert_erase hvE
        have hsubset : I ⊆ E.erase v ↔ insert v I ⊆ E := by
          constructor
          · intro hIE
            intro x hx
            rcases mem_insert.mp hx with rfl | hxI
            · exact hvE
            · exact (mem_erase.mp (hIE hxI)).2
          · intro hIE x hxI
            have hxv : x ≠ v := fun hx ↦ hvI (hx ▸ hxI)
            exact mem_erase.mpr ⟨hxv, hIE (mem_insert_of_mem hxI)⟩
        rw [hins]
        by_cases hIE : insert v I ⊆ E <;> simp [hvE, hIE, hsubset]
      · have hnot : ¬insert v I ⊆ E := fun h ↦ hvE (h (mem_insert_self v I))
        simp [hvE, hnot]
    _ = intLocalDegree Z r J (insert v I) := by rfl

/-- Lift coefficients from `(q-1)`-sets avoiding `v` to `q`-sets through
`v`. -/
def liftCoeffs (v : V) (ψ : Finset V → ℤ) (Q : Finset V) : ℤ :=
  if v ∈ Q then ψ (Q.erase v) else 0

private lemma intBoundary_lift_of_mem
    {Z e : Finset V} {v : V} {q : ℕ} (ψ : Finset V → ℤ)
    (hvZ : v ∈ Z) (hve : v ∈ e) (hq : 0 < q) :
    intBoundary Z q (liftCoeffs v ψ) e =
      intBoundary (Z.erase v) (q - 1) ψ (e.erase v) := by
  classical
  calc
    intBoundary Z q (liftCoeffs v ψ) e =
        ∑ Q ∈ Z.powersetCard q, if v ∈ Q then
          (if e.erase v ⊆ Q.erase v then ψ (Q.erase v) else 0)
        else 0 := by
      rw [intBoundary]
      apply Finset.sum_congr rfl
      intro Q hQ
      by_cases hvQ : v ∈ Q
      · have hsubset : e ⊆ Q ↔ e.erase v ⊆ Q.erase v := by
          constructor
          · exact erase_subset_erase v
          · intro h x hx
            by_cases hxv : x = v
            · subst x
              exact hvQ
            · exact (mem_erase.mp (h (mem_erase.mpr ⟨hxv, hx⟩))).2
        simp only [liftCoeffs, if_pos hvQ]
        by_cases heQ : e ⊆ Q
        · have herase : e.erase v ⊆ Q.erase v := hsubset.mp heQ
          simp [heQ, herase]
        · have hnotErase : ¬e.erase v ⊆ Q.erase v :=
            fun h ↦ heQ (hsubset.mpr h)
          simp [heQ, hnotErase]
      · have hnot : ¬e ⊆ Q := fun h ↦ hvQ (h hve)
        simp [liftCoeffs, hvQ, hnot]
    _ = ∑ Q ∈ (Z.powersetCard q).filter (v ∈ ·),
          if e.erase v ⊆ Q.erase v then ψ (Q.erase v) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ T ∈ (Z.erase v).powersetCard (q - 1),
          if e.erase v ⊆ T then ψ T else 0 :=
      sum_powersetCard_filter_mem_erase hvZ hq
        (fun T ↦ if e.erase v ⊆ T then ψ T else 0)
    _ = intBoundary (Z.erase v) (q - 1) ψ (e.erase v) := by rfl

private lemma isLocallyDivisible_link
    {Z : Finset V} {v : V} {q r : ℕ} {J : Finset V → ℤ}
    (hvZ : v ∈ Z) (hr : 0 < r) (hq : 0 < q)
    (hlocal : IsLocallyDivisible Z q r J) :
    IsLocallyDivisible (Z.erase v) (q - 1) (r - 1) (intLink v J) := by
  intro I hIZ hIr
  have hvI : v ∉ I := by
    intro hvI
    exact (mem_erase.mp (hIZ hvI)).1 rfl
  have hinsertZ : insert v I ⊆ Z := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hxI
    · exact hvZ
    · exact (mem_erase.mp (hIZ hxI)).2
  have hcard : (insert v I).card = I.card + 1 := by
    rw [card_insert_of_notMem hvI]
  have hcardr : (insert v I).card ≤ r := by omega
  have hdiv := hlocal (insert v I) hinsertZ hcardr
  rw [intLocalDegree_link J hvZ hvI hr]
  have hqsub : q - 1 - I.card = q - (I.card + 1) := by omega
  have hrsub : r - 1 - I.card = r - (I.card + 1) := by omega
  rw [hqsub, hrsub]
  simpa [hcard] using hdiv

private lemma intLocalDegree_sub
    (Z : Finset V) (r : ℕ) (J K : Finset V → ℤ) (I : Finset V) :
    intLocalDegree Z r (fun e ↦ J e - K e) I =
      intLocalDegree Z r J I - intLocalDegree Z r K I := by
  classical
  rw [intLocalDegree, intLocalDegree, intLocalDegree, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hIe : I ⊆ e <;> simp [hIe]

private lemma IsLocallyDivisible.sub
    {Z : Finset V} {q r : ℕ} {J K : Finset V → ℤ}
    (hJ : IsLocallyDivisible Z q r J)
    (hK : IsLocallyDivisible Z q r K) :
    IsLocallyDivisible Z q r (fun e ↦ J e - K e) := by
  intro I hIZ hIr
  rw [intLocalDegree_sub]
  exact dvd_sub (hJ I hIZ hIr) (hK I hIZ hIr)

private lemma intLocalDegree_erase_of_zero_mem
    {Z I : Finset V} {v : V} {r : ℕ} {J : Finset V → ℤ}
    (hzero : ∀ e ∈ Z.powersetCard r, v ∈ e → J e = 0) :
    intLocalDegree (Z.erase v) r J I = intLocalDegree Z r J I := by
  classical
  rw [intLocalDegree, intLocalDegree]
  apply Finset.sum_subset
  · intro e he
    have hedata := mem_powersetCard.mp he
    exact mem_powersetCard.mpr
      ⟨hedata.1.trans (Finset.erase_subset v Z), hedata.2⟩
  · intro e heZ heNot
    have hedata := mem_powersetCard.mp heZ
    have hve : v ∈ e := by
      by_contra hvnot
      apply heNot
      apply mem_powersetCard.mpr
      refine ⟨?_, hedata.2⟩
      intro x hxe
      exact mem_erase.mpr ⟨fun hxv ↦ hvnot (hxv ▸ hxe), hedata.1 hxe⟩
    rw [hzero e heZ hve]
    split_ifs <;> simp

private lemma isLocallyDivisible_erase_of_zero_mem
    {Z : Finset V} {v : V} {q r : ℕ} {J : Finset V → ℤ}
    (hlocal : IsLocallyDivisible Z q r J)
    (hzero : ∀ e ∈ Z.powersetCard r, v ∈ e → J e = 0) :
    IsLocallyDivisible (Z.erase v) q r J := by
  intro I hIZ hIr
  rw [intLocalDegree_erase_of_zero_mem hzero]
  apply hlocal I
  · exact hIZ.trans (Finset.erase_subset v Z)
  · exact hIr

/-- Keep only clique coefficients whose clique avoids `v`. -/
def avoidCoeffs (v : V) (χ : Finset V → ℤ) (Q : Finset V) : ℤ :=
  if v ∈ Q then 0 else χ Q

private lemma intBoundary_avoid
    (Z : Finset V) (v : V) (q : ℕ) (χ : Finset V → ℤ)
    (e : Finset V) :
    intBoundary Z q (avoidCoeffs v χ) e =
      intBoundary (Z.erase v) q χ e := by
  classical
  have hsub : (Z.erase v).powersetCard q ⊆ Z.powersetCard q := by
    intro Q hQ
    have hQdata := mem_powersetCard.mp hQ
    exact mem_powersetCard.mpr
      ⟨hQdata.1.trans (Finset.erase_subset v Z), hQdata.2⟩
  rw [intBoundary, intBoundary]
  calc
    (∑ Q ∈ Z.powersetCard q,
        if e ⊆ Q then avoidCoeffs v χ Q else 0) =
        ∑ Q ∈ (Z.erase v).powersetCard q,
          if e ⊆ Q then avoidCoeffs v χ Q else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro Q hQbig hQnot
      have hQdata := mem_powersetCard.mp hQbig
      have hvQ : v ∈ Q := by
        by_contra hvnot
        apply hQnot
        apply mem_powersetCard.mpr
        refine ⟨?_, hQdata.2⟩
        intro x hxQ
        exact mem_erase.mpr ⟨fun hxv ↦ hvnot (hxv ▸ hxQ), hQdata.1 hxQ⟩
      simp [avoidCoeffs, hvQ]
    _ = ∑ Q ∈ (Z.erase v).powersetCard q,
          if e ⊆ Q then χ Q else 0 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have hvQ : v ∉ Q := by
        intro hvQ
        exact (mem_erase.mp ((mem_powersetCard.mp hQ).1 hvQ)).1 rfl
      simp [avoidCoeffs, hvQ]

private lemma intBoundary_add
    (Z : Finset V) (q : ℕ) (φ ψ : Finset V → ℤ) (e : Finset V) :
    intBoundary Z q (fun Q ↦ φ Q + ψ Q) e =
      intBoundary Z q φ e + intBoundary Z q ψ e := by
  classical
  rw [intBoundary, intBoundary, intBoundary, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases heQ : e ⊆ Q <;> simp [heQ]

/-- Full clique-incidence lattice theorem.  On every ground set of size at
least `q+r`, the local degree congruences are sufficient for an integer
`q`-clique boundary representation.  The recursion first lowers the rank by
taking a link, then lowers the ground-set size on the residual vector. -/
theorem exists_intBoundary_eq
    {Z : Finset V} {q r : ℕ} {J : Finset V → ℤ}
    (hrq : r ≤ q) (hsize : q + r ≤ Z.card)
    (hlocal : IsLocallyDivisible Z q r J) :
    ∃ φ : Finset V → ℤ, ∀ e ∈ Z.powersetCard r,
      intBoundary Z q φ e = J e := by
  classical
  by_cases hr0 : r = 0
  · subst r
    obtain ⟨Q₀, hQ₀⟩ := powersetCard_nonempty.mpr (by omega : q ≤ Z.card)
    refine ⟨fun Q ↦ if Q = Q₀ then J ∅ else 0, ?_⟩
    intro e he
    have he0 : e = ∅ := card_eq_zero.mp (mem_powersetCard.mp he).2
    subst e
    rw [intBoundary]
    simp [hQ₀]
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  have hq : 0 < q := lt_of_lt_of_le hr hrq
  by_cases hbase : Z.card = q + r
  · exact exists_intBoundary_eq_of_card_add hrq hbase hlocal
  have hstrict : q + r < Z.card := by omega
  have hZpos : 0 < Z.card := by omega
  obtain ⟨v, hvZ⟩ := card_pos.mp hZpos
  have herasecard : (Z.erase v).card = Z.card - 1 := by
    rw [card_erase_of_mem hvZ]
  have hlinkLocal :
      IsLocallyDivisible (Z.erase v) (q - 1) (r - 1) (intLink v J) :=
    isLocallyDivisible_link hvZ hr hq hlocal
  have hlinkSize : (q - 1) + (r - 1) ≤ (Z.erase v).card := by
    rw [herasecard]
    omega
  obtain ⟨ψ, hψ⟩ := exists_intBoundary_eq
    (Z := Z.erase v) (q := q - 1) (r := r - 1) (J := intLink v J)
    (by omega) hlinkSize hlinkLocal
  have hmatch (e : Finset V) (he : e ∈ Z.powersetCard r) (hve : v ∈ e) :
      intBoundary Z q (liftCoeffs v ψ) e = J e := by
    rw [intBoundary_lift_of_mem ψ hvZ hve hq]
    have hedata := mem_powersetCard.mp he
    have herase : e.erase v ∈ (Z.erase v).powersetCard (r - 1) := by
      apply mem_powersetCard.mpr
      constructor
      · intro x hx
        have hxdata := mem_erase.mp hx
        exact mem_erase.mpr ⟨hxdata.1, hedata.1 hxdata.2⟩
      · rw [card_erase_of_mem hve, hedata.2]
    rw [hψ (e.erase v) herase]
    simp only [intLink]
    rw [insert_erase hve]
  let R : Finset V → ℤ := fun e ↦
    J e - intBoundary Z q (liftCoeffs v ψ) e
  have hRlocalZ : IsLocallyDivisible Z q r R := by
    exact hlocal.sub (isLocallyDivisible_intBoundary (liftCoeffs v ψ))
  have hRzero : ∀ e ∈ Z.powersetCard r, v ∈ e → R e = 0 := by
    intro e he hve
    simp only [R]
    rw [hmatch e he hve]
    simp
  have hRlocalErase : IsLocallyDivisible (Z.erase v) q r R :=
    isLocallyDivisible_erase_of_zero_mem hRlocalZ hRzero
  have hresidualSize : q + r ≤ (Z.erase v).card := by
    rw [herasecard]
    omega
  obtain ⟨χ, hχ⟩ := exists_intBoundary_eq
    (Z := Z.erase v) (q := q) (r := r) (J := R)
    hrq hresidualSize hRlocalErase
  let φ : Finset V → ℤ := fun Q ↦ liftCoeffs v ψ Q + avoidCoeffs v χ Q
  refine ⟨φ, ?_⟩
  intro e he
  rw [show intBoundary Z q φ e =
      intBoundary Z q (liftCoeffs v ψ) e +
        intBoundary Z q (avoidCoeffs v χ) e by
    exact intBoundary_add Z q (liftCoeffs v ψ) (avoidCoeffs v χ) e]
  rw [intBoundary_avoid]
  by_cases hve : v ∈ e
  · have hsmallzero : intBoundary (Z.erase v) q χ e = 0 := by
      rw [intBoundary]
      apply Finset.sum_eq_zero
      intro Q hQ
      have hvQ : v ∉ Q := by
        intro hvQ
        exact (mem_erase.mp ((mem_powersetCard.mp hQ).1 hvQ)).1 rfl
      have hnot : ¬e ⊆ Q := fun heQ ↦ hvQ (heQ hve)
      simp [hnot]
    rw [hmatch e he hve, hsmallzero]
    simp
  · have hedata := mem_powersetCard.mp he
    have heErase : e ∈ (Z.erase v).powersetCard r := by
      apply mem_powersetCard.mpr
      refine ⟨?_, hedata.2⟩
      intro x hxe
      exact mem_erase.mpr ⟨fun hxv ↦ hve (hxv ▸ hxe), hedata.1 hxe⟩
    rw [hχ e heErase]
    simp only [R]
    ring
termination_by (r, Z.card)
decreasing_by
  · simp_wf
    omega
  · simp_wf
    rw [card_erase_of_mem hvZ]
    omega

end Erdos722.LocalDecoder
