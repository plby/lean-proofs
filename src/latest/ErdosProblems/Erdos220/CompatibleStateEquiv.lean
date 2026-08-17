import Mathlib

/-!
# Compatible prime states on a six-element support

For a nonempty support `J : Finset (Fin 6)`, a vector over `ZMod p` which is
zero off `J` and whose coordinates sum to zero is freely determined by all
but one of its coordinates.  This file gives the explicit equivalence and
the resulting cardinality `p ^ (J.card - 1)` (for prime `p`).
-/

open scoped BigOperators

namespace Erdos220

/-- A prime-local compatible state: it is supported on `J` and its six
coordinates have sum zero. -/
def CompatiblePrimeState (p : ℕ) (J : Finset (Fin 6)) :=
  {a : Fin 6 → ZMod p //
    (∀ i, i ∉ J → a i = 0) ∧ ∑ i, a i = 0}

namespace CompatiblePrimeState

variable {p : ℕ} {J : Finset (Fin 6)}

@[simp] lemma zero_outside (a : CompatiblePrimeState p J) {i : Fin 6}
    (hi : i ∉ J) : a.1 i = 0 :=
  a.2.1 i hi

@[simp] lemma sum_eq_zero (a : CompatiblePrimeState p J) :
    ∑ i, a.1 i = 0 :=
  a.2.2

/-- Sum of a function over the subtype associated with `J.erase j0`, written
using `attach` so no choice of membership proofs enters later formulas. -/
def eraseSum (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p) : ZMod p :=
  ∑ k ∈ (J.erase j0).attach, f k

/-- Extend freely chosen values on `J.erase j0` to a compatible vector by
putting at `j0` the negative of their sum and putting zero off `J`. -/
def extendErase (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p) : Fin 6 → ZMod p :=
  fun i ↦ if hij : i = j0 then
      -eraseSum J j0 f
    else if hiJ : i ∈ J then
      f ⟨i, Finset.mem_erase.mpr ⟨hij, hiJ⟩⟩
    else 0

@[simp] lemma extendErase_apply_j0 (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p) :
    extendErase J j0 f j0 = -eraseSum J j0 f := by
  simp [extendErase]

@[simp] lemma extendErase_apply_of_mem_erase (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p)
    {i : Fin 6} (hi : i ∈ J.erase j0) :
    extendErase J j0 f i = f ⟨i, hi⟩ := by
  have hij : i ≠ j0 := (Finset.mem_erase.mp hi).1
  have hiJ : i ∈ J := (Finset.mem_erase.mp hi).2
  simp [extendErase, hij, hiJ]

@[simp] lemma extendErase_apply_of_not_mem (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p)
    {i : Fin 6} (hi : i ∉ J) (hij : i ≠ j0) :
    extendErase J j0 f i = 0 := by
  simp [extendErase, hij, hi]

private lemma sum_extendErase (J : Finset (Fin 6)) (j0 : Fin 6)
    (hj0 : j0 ∈ J) (f : ↑(J.erase j0) → ZMod p) :
    ∑ i, extendErase J j0 f i = 0 := by
  classical
  let g : Fin 6 → ZMod p := extendErase J j0 f
  have hsupport :
      (∑ i ∈ J, g i) = ∑ i : Fin 6, g i := by
    apply Finset.sum_subset (Finset.subset_univ J)
    intro i _ hiJ
    have hij : i ≠ j0 := by
      intro h
      subst i
      exact hiJ hj0
    exact extendErase_apply_of_not_mem J j0 f hiJ hij
  have herase :
      (∑ i ∈ J.erase j0, g i) =
        eraseSum J j0 f := by
    calc
      (∑ i ∈ J.erase j0, g i) =
          ∑ k ∈ (J.erase j0).attach, g k := by
            rw [Finset.sum_attach]
      _ = ∑ k ∈ (J.erase j0).attach, f k := by
        apply Finset.sum_congr rfl
        intro k _
        exact extendErase_apply_of_mem_erase J j0 f k.2
      _ = eraseSum J j0 f := rfl
  rw [← hsupport, ← Finset.sum_erase_add J g hj0, herase]
  simp [g]

/-- The explicit equivalence obtained by deleting one chosen support
coordinate. -/
def compatiblePrimeStateEquivErase (p : ℕ) (J : Finset (Fin 6))
    (j0 : Fin 6) (hj0 : j0 ∈ J) :
    CompatiblePrimeState p J ≃ (↑(J.erase j0) → ZMod p) where
  toFun a := fun i ↦ a.1 i
  invFun f := ⟨extendErase J j0 f, by
    constructor
    · intro i hiJ
      have hij : i ≠ j0 := by
        intro h
        subst i
        exact hiJ hj0
      exact extendErase_apply_of_not_mem J j0 f hiJ hij
    · exact sum_extendErase J j0 hj0 f⟩
  left_inv a := by
    apply Subtype.ext
    change extendErase J j0 (fun i : ↑(J.erase j0) ↦ a.1 i) = a.1
    funext i
    by_cases hij : i = j0
    · subst i
      have hsmall :
          eraseSum J j0 (fun k ↦ a.1 k) =
            ∑ i ∈ J.erase j0, a.1 i := by
        unfold eraseSum
        rw [Finset.sum_attach]
      have hsupport :
          (∑ i ∈ J, a.1 i) = ∑ i : Fin 6, a.1 i := by
        apply Finset.sum_subset (Finset.subset_univ J)
        intro i _ hiJ
        exact a.2.1 i hiJ
      have hsplit : (∑ i ∈ J.erase j0, a.1 i) + a.1 j0 = 0 := by
        rw [Finset.sum_erase_add J a.1 hj0, hsupport]
        exact a.2.2
      have hjvalue : a.1 j0 = -(∑ i ∈ J.erase j0, a.1 i) := by
        exact eq_neg_of_add_eq_zero_right hsplit
      simp only [extendErase_apply_j0]
      rw [hsmall, hjvalue]
    · by_cases hiJ : i ∈ J
      · have hi : i ∈ J.erase j0 := Finset.mem_erase.mpr ⟨hij, hiJ⟩
        exact extendErase_apply_of_mem_erase J j0 _ hi
      · rw [extendErase_apply_of_not_mem J j0 _ hiJ hij, a.2.1 i hiJ]
  right_inv f := by
    change (fun i : ↑(J.erase j0) ↦ extendErase J j0 f i) = f
    funext i
    exact extendErase_apply_of_mem_erase J j0 f i.2

@[simp] lemma compatiblePrimeStateEquivErase_apply
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J)
    (a : CompatiblePrimeState p J) (i : ↑(J.erase j0)) :
    compatiblePrimeStateEquivErase p J j0 hj0 a i = a.1 i :=
  rfl

@[simp] lemma compatiblePrimeStateEquivErase_symm_apply_mem
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J)
    (f : ↑(J.erase j0) → ZMod p)
    (i : ↑(J.erase j0)) :
    ((compatiblePrimeStateEquivErase p J j0 hj0).symm f).1 i = f i := by
  exact extendErase_apply_of_mem_erase J j0 f i.2

@[simp] lemma compatiblePrimeStateEquivErase_symm_apply_j0
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J)
    (f : ↑(J.erase j0) → ZMod p) :
    ((compatiblePrimeStateEquivErase p J j0 hj0).symm f).1 j0 = -eraseSum J j0 f := by
  exact extendErase_apply_j0 J j0 f

@[simp] lemma compatiblePrimeStateEquivErase_symm_apply_outside
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J)
    (f : ↑(J.erase j0) → ZMod p)
    {i : Fin 6} (hiJ : i ∉ J) :
    ((compatiblePrimeStateEquivErase p J j0 hj0).symm f).1 i = 0 := by
  have hij : i ≠ j0 := fun h ↦ hiJ (h ▸ hj0)
  exact extendErase_apply_of_not_mem J j0 f hiJ hij

lemma compatiblePrimeState_restrict_injective
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J) :
    Function.Injective
      (fun a : CompatiblePrimeState p J ↦
        fun i : ↑(J.erase j0) ↦ a.1 i) :=
  (compatiblePrimeStateEquivErase p J j0 hj0).injective

/-- A compatible state has one freely chosen residue for each element of
`J.erase j0`. -/
theorem card_compatiblePrimeState (hp : p.Prime)
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J) :
    Nat.card (CompatiblePrimeState p J) = p ^ (J.card - 1) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fintype (CompatiblePrimeState p J) :=
    Fintype.ofEquiv (↑(J.erase j0) → ZMod p)
      (compatiblePrimeStateEquivErase p J j0 hj0).symm
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr (compatiblePrimeStateEquivErase p J j0 hj0)]
  simp only [Fintype.card_fun, ZMod.card]
  rw [Fintype.card_coe, Finset.card_erase_of_mem hj0]

theorem card_compatiblePrimeState_of_nonempty (hp : p.Prime)
    (J : Finset (Fin 6)) (hJ : J.Nonempty) :
    Nat.card (CompatiblePrimeState p J) = p ^ (J.card - 1) := by
  classical
  let j0 := J.min' hJ
  exact card_compatiblePrimeState hp J j0 (Finset.min'_mem J hJ)

end CompatiblePrimeState

end Erdos220
