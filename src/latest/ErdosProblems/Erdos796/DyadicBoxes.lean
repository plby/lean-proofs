import ErdosProblems.Erdos796.Core
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite dyadic boxes

This file gives the purely finite dyadic decomposition used by the pruning
argument.  Positive integers are assigned the scale `Nat.log 2 x`; thus the
`k`-th scale lies in `[2^k,2^(k+1))`.  Taking products of three scale
intervals gives at most `(log₂ n + 1)^3` boxes for triples in `[1,n]^3`.

No comparison with the real logarithm is made here.
-/

namespace Erdos796

namespace DyadicBoxes

open scoped BigOperators

/-- The dyadic scale of a natural number.  Only positive inputs are used in
the partition, so the conventional value `log 2 0 = 0` is irrelevant. -/
def dyadicScale (x : ℕ) : ℕ := Nat.log 2 x

/-- The positive integers at scale `k`, truncated at `n`. -/
def scaleInterval (n k : ℕ) : Finset ℕ :=
  (positiveIcc n).filter fun x => dyadicScale x = k

@[simp] theorem mem_scaleInterval {n k x : ℕ} :
    x ∈ scaleInterval n k ↔
      1 ≤ x ∧ x ≤ n ∧ dyadicScale x = k := by
  simp [scaleInterval, and_assoc]

theorem scaleInterval_subset_positiveIcc (n k : ℕ) :
    scaleInterval n k ⊆ positiveIcc n :=
  Finset.filter_subset _ _

/-- Every member of scale `k` lies in the usual half-open dyadic interval. -/
theorem bounds_of_mem_scaleInterval {n k x : ℕ}
    (hx : x ∈ scaleInterval n k) :
    2 ^ k ≤ x ∧ x < 2 ^ (k + 1) := by
  have hx' := mem_scaleInterval.mp hx
  have hx0 : x ≠ 0 := by omega
  have hk : Nat.log 2 x = k := by
    simpa [dyadicScale] using! hx'.2.2
  constructor
  · rw [← hk]
    exact Nat.pow_log_le_self 2 hx0
  · have h := Nat.lt_pow_succ_log_self Nat.one_lt_two x
    rw [← hk]
    simpa [Nat.succ_eq_add_one] using! h

/-- The truncated scale interval is contained in `[2^k,2^(k+1))`. -/
theorem scaleInterval_subset_Ico (n k : ℕ) :
    scaleInterval n k ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
  intro x hx
  exact Finset.mem_Ico.mpr (bounds_of_mem_scaleInterval hx)

/-- A dyadic scale contains at most `2^k` natural numbers. -/
theorem card_scaleInterval_le_pow (n k : ℕ) :
    (scaleInterval n k).card ≤ 2 ^ k := by
  calc
    (scaleInterval n k).card ≤
        (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card :=
      Finset.card_le_card (scaleInterval_subset_Ico n k)
    _ = 2 ^ k := by
      rw [Nat.card_Ico, pow_succ]
      omega

/-- The finite set of all scales that can meet `[1,n]`. -/
def scaleIndices (n : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 n + 1)

@[simp] theorem mem_scaleIndices {n k : ℕ} :
    k ∈ scaleIndices n ↔ k ≤ Nat.log 2 n := by
  simp [scaleIndices]

@[simp] theorem card_scaleIndices (n : ℕ) :
    (scaleIndices n).card = Nat.log 2 n + 1 := by
  simp [scaleIndices]

/-- The scale of every positive `x ≤ n` is one of the displayed indices. -/
theorem dyadicScale_mem_scaleIndices {n x : ℕ}
    (hx : x ∈ positiveIcc n) :
    dyadicScale x ∈ scaleIndices n := by
  rw [mem_scaleIndices]
  exact Nat.log_mono_right (mem_positiveIcc.mp hx).2

/-- Pointwise covering lemma for the dyadic partition. -/
theorem mem_own_scaleInterval {n x : ℕ} (hx : x ∈ positiveIcc n) :
    x ∈ scaleInterval n (dyadicScale x) := by
  exact mem_scaleInterval.mpr
    ⟨(mem_positiveIcc.mp hx).1, (mem_positiveIcc.mp hx).2, rfl⟩

/-- Distinct scales are disjoint. -/
theorem disjoint_scaleInterval {n k l : ℕ} (hkl : k ≠ l) :
    Disjoint (scaleInterval n k) (scaleInterval n l) := by
  rw [Finset.disjoint_left]
  intro x hxk hxl
  exact hkl ((mem_scaleInterval.mp hxk).2.2.symm.trans
    (mem_scaleInterval.mp hxl).2.2)

/-- Exact covering of `[1,n]` by its dyadic scales. -/
theorem biUnion_scaleIntervals (n : ℕ) :
    (scaleIndices n).biUnion (scaleInterval n) = positiveIcc n := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨k, hk, hxk⟩
    exact scaleInterval_subset_positiveIcc n k hxk
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨dyadicScale x, dyadicScale_mem_scaleIndices hx,
        mem_own_scaleInterval hx⟩

/-- The three dyadic scales attached to a triple. -/
def tripleScale (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (dyadicScale p.1, dyadicScale p.2.1, dyadicScale p.2.2)

/-- All possible triples of scales up to `n`. -/
def tripleScaleIndices (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  scaleIndices n ×ˢ (scaleIndices n ×ˢ scaleIndices n)

@[simp] theorem mem_tripleScaleIndices {n : ℕ} {ijk : ℕ × ℕ × ℕ} :
    ijk ∈ tripleScaleIndices n ↔
      ijk.1 ≤ Nat.log 2 n ∧
      ijk.2.1 ≤ Nat.log 2 n ∧
      ijk.2.2 ≤ Nat.log 2 n := by
  simp [tripleScaleIndices]

/-- There are exactly `(log₂ n + 1)^3` possible scale boxes. -/
@[simp] theorem card_tripleScaleIndices (n : ℕ) :
    (tripleScaleIndices n).card = (Nat.log 2 n + 1) ^ 3 := by
  simp [tripleScaleIndices]
  ring

/-- The full dyadic box belonging to three scale indices. -/
def tripleBox (n : ℕ) (ijk : ℕ × ℕ × ℕ) :
    Finset (ℕ × ℕ × ℕ) :=
  scaleInterval n ijk.1 ×ˢ
    (scaleInterval n ijk.2.1 ×ˢ scaleInterval n ijk.2.2)

@[simp] theorem mem_tripleBox {n : ℕ} {ijk : ℕ × ℕ × ℕ}
    {p : ℕ × ℕ × ℕ} :
    p ∈ tripleBox n ijk ↔
      p.1 ∈ scaleInterval n ijk.1 ∧
      p.2.1 ∈ scaleInterval n ijk.2.1 ∧
      p.2.2 ∈ scaleInterval n ijk.2.2 := by
  simp [tripleBox, and_assoc]

/-- Ambient positive triples. -/
def tripleAmbient (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  positiveIcc n ×ˢ (positiveIcc n ×ˢ positiveIcc n)

@[simp] theorem mem_tripleAmbient {n : ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ tripleAmbient n ↔
      p.1 ∈ positiveIcc n ∧ p.2.1 ∈ positiveIcc n ∧
        p.2.2 ∈ positiveIcc n := by
  simp [tripleAmbient, and_assoc]

theorem tripleBox_subset_ambient (n : ℕ) (ijk : ℕ × ℕ × ℕ) :
    tripleBox n ijk ⊆ tripleAmbient n := by
  intro p hp
  have hp' := mem_tripleBox.mp hp
  exact mem_tripleAmbient.mpr
    ⟨scaleInterval_subset_positiveIcc _ _ hp'.1,
      scaleInterval_subset_positiveIcc _ _ hp'.2.1,
      scaleInterval_subset_positiveIcc _ _ hp'.2.2⟩

theorem tripleScale_eq_of_mem_tripleBox {n : ℕ}
    {ijk : ℕ × ℕ × ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ tripleBox n ijk) : tripleScale p = ijk := by
  have hp' := mem_tripleBox.mp hp
  apply Prod.ext
  · exact (mem_scaleInterval.mp hp'.1).2.2
  · apply Prod.ext
    · exact (mem_scaleInterval.mp hp'.2.1).2.2
    · exact (mem_scaleInterval.mp hp'.2.2).2.2

/-- Distinct scale triples give disjoint Cartesian boxes. -/
theorem disjoint_tripleBox {n : ℕ} {ijk abc : ℕ × ℕ × ℕ}
    (hne : ijk ≠ abc) : Disjoint (tripleBox n ijk) (tripleBox n abc) := by
  rw [Finset.disjoint_left]
  intro p hpijk hpabc
  exact hne ((tripleScale_eq_of_mem_tripleBox hpijk).symm.trans
    (tripleScale_eq_of_mem_tripleBox hpabc))

/-- A positive triple belongs to the box indexed by its own three scales. -/
theorem triple_mem_own_box {n : ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ tripleAmbient n) :
    p ∈ tripleBox n (tripleScale p) := by
  have hp' := mem_tripleAmbient.mp hp
  exact mem_tripleBox.mpr
    ⟨mem_own_scaleInterval hp'.1,
      mem_own_scaleInterval hp'.2.1,
      mem_own_scaleInterval hp'.2.2⟩

theorem tripleScale_mem_indices {n : ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ tripleAmbient n) :
    tripleScale p ∈ tripleScaleIndices n := by
  have hp' := mem_tripleAmbient.mp hp
  exact Finset.mem_product.mpr
    ⟨dyadicScale_mem_scaleIndices hp'.1,
      Finset.mem_product.mpr
        ⟨dyadicScale_mem_scaleIndices hp'.2.1,
          dyadicScale_mem_scaleIndices hp'.2.2⟩⟩

/-- Exact covering of the positive triple ambient set by dyadic boxes. -/
theorem biUnion_tripleBoxes (n : ℕ) :
    (tripleScaleIndices n).biUnion (tripleBox n) = tripleAmbient n := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨ijk, hijk, hpbox⟩
    exact tripleBox_subset_ambient n ijk hpbox
  · intro hp
    exact Finset.mem_biUnion.mpr
      ⟨tripleScale p, tripleScale_mem_indices hp, triple_mem_own_box hp⟩

/-- Coordinate-wise cardinality bound for one dyadic triple box. -/
theorem card_tripleBox_le (n : ℕ) (ijk : ℕ × ℕ × ℕ) :
    (tripleBox n ijk).card ≤
      2 ^ ijk.1 * (2 ^ ijk.2.1 * 2 ^ ijk.2.2) := by
  rw [tripleBox, Finset.card_product, Finset.card_product]
  exact Nat.mul_le_mul (card_scaleInterval_le_pow n ijk.1)
    (Nat.mul_le_mul (card_scaleInterval_le_pow n ijk.2.1)
      (card_scaleInterval_le_pow n ijk.2.2))

/-- The part of an arbitrary finite triple family lying in one dyadic box. -/
def tripleBoxPart (_n : ℕ) (H : Finset (ℕ × ℕ × ℕ))
    (ijk : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  H.filter fun p => tripleScale p = ijk

@[simp] theorem mem_tripleBoxPart {n : ℕ} {H : Finset (ℕ × ℕ × ℕ)}
    {ijk p : ℕ × ℕ × ℕ} :
    p ∈ tripleBoxPart n H ijk ↔ p ∈ H ∧ tripleScale p = ijk := by
  simp [tripleBoxPart]

theorem tripleBoxPart_subset (n : ℕ) (H : Finset (ℕ × ℕ × ℕ))
    (ijk : ℕ × ℕ × ℕ) : tripleBoxPart n H ijk ⊆ H :=
  Finset.filter_subset _ _

/-- Distinct scale fibres of any family are disjoint. -/
theorem disjoint_tripleBoxPart {n : ℕ} {H : Finset (ℕ × ℕ × ℕ)}
    {ijk abc : ℕ × ℕ × ℕ} (hne : ijk ≠ abc) :
    Disjoint (tripleBoxPart n H ijk) (tripleBoxPart n H abc) := by
  rw [Finset.disjoint_left]
  intro p hpijk hpabc
  have hi := (mem_tripleBoxPart.mp hpijk).2
  have ha := (mem_tripleBoxPart.mp hpabc).2
  exact hne (hi.symm.trans ha)

/-- Under the ambient support hypothesis, a scale fibre is supported in its
corresponding Cartesian dyadic box. -/
theorem tripleBoxPart_subset_tripleBox {n : ℕ}
    {H : Finset (ℕ × ℕ × ℕ)} (hH : H ⊆ tripleAmbient n)
    (ijk : ℕ × ℕ × ℕ) :
    tripleBoxPart n H ijk ⊆ tripleBox n ijk := by
  intro p hp
  have hp' := mem_tripleBoxPart.mp hp
  have hamb := mem_tripleAmbient.mp (hH hp'.1)
  have hs := congrArg Prod.fst hp'.2
  have hm := congrArg (fun q => q.2.1) hp'.2
  have hr := congrArg (fun q => q.2.2) hp'.2
  apply mem_tripleBox.mpr
  exact ⟨mem_scaleInterval.mpr
      ⟨(mem_positiveIcc.mp hamb.1).1, (mem_positiveIcc.mp hamb.1).2, hs⟩,
    mem_scaleInterval.mpr
      ⟨(mem_positiveIcc.mp hamb.2.1).1,
        (mem_positiveIcc.mp hamb.2.1).2, hm⟩,
    mem_scaleInterval.mpr
      ⟨(mem_positiveIcc.mp hamb.2.2).1,
        (mem_positiveIcc.mp hamb.2.2).2, hr⟩⟩

/-- Every supported family is exactly the union of its dyadic box parts. -/
theorem biUnion_tripleBoxParts {n : ℕ}
    {H : Finset (ℕ × ℕ × ℕ)} (hH : H ⊆ tripleAmbient n) :
    (tripleScaleIndices n).biUnion (tripleBoxPart n H) = H := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨ijk, hijk, hpart⟩
    exact (mem_tripleBoxPart.mp hpart).1
  · intro hp
    have hamb := hH hp
    exact Finset.mem_biUnion.mpr
      ⟨tripleScale p, tripleScale_mem_indices hamb,
        mem_tripleBoxPart.mpr ⟨hp, rfl⟩⟩

/-- Exact cardinality decomposition into the dyadic scale fibres. -/
theorem card_eq_sum_card_tripleBoxParts {n : ℕ}
    {H : Finset (ℕ × ℕ × ℕ)} (hH : H ⊆ tripleAmbient n) :
    H.card = ∑ ijk ∈ tripleScaleIndices n,
      (tripleBoxPart n H ijk).card := by
  have hmap : Set.MapsTo tripleScale (H : Set (ℕ × ℕ × ℕ))
      (tripleScaleIndices n : Set (ℕ × ℕ × ℕ)) := by
    intro p hp
    exact tripleScale_mem_indices (hH hp)
  exact Finset.card_eq_sum_card_fiberwise hmap

/-- Indices of the nonempty box parts of `H`. -/
def activeTripleBoxIndices (n : ℕ) (H : Finset (ℕ × ℕ × ℕ)) :
    Finset (ℕ × ℕ × ℕ) :=
  (tripleScaleIndices n).filter fun ijk =>
    (tripleBoxPart n H ijk).Nonempty

@[simp] theorem mem_activeTripleBoxIndices
    {n : ℕ} {H : Finset (ℕ × ℕ × ℕ)} {ijk : ℕ × ℕ × ℕ} :
    ijk ∈ activeTripleBoxIndices n H ↔
      ijk ∈ tripleScaleIndices n ∧
        (tripleBoxPart n H ijk).Nonempty := by
  simp [activeTripleBoxIndices]

/-- At most `(log₂ n + 1)^3` nonempty boxes occur. -/
theorem card_activeTripleBoxIndices_le (n : ℕ)
    (H : Finset (ℕ × ℕ × ℕ)) :
    (activeTripleBoxIndices n H).card ≤ (Nat.log 2 n + 1) ^ 3 := by
  calc
    (activeTripleBoxIndices n H).card ≤ (tripleScaleIndices n).card :=
      Finset.card_filter_le _ _
    _ = (Nat.log 2 n + 1) ^ 3 := card_tripleScaleIndices n

/-- The active (nonempty) box parts still cover every supported family. -/
theorem biUnion_activeTripleBoxParts {n : ℕ}
    {H : Finset (ℕ × ℕ × ℕ)} (hH : H ⊆ tripleAmbient n) :
    (activeTripleBoxIndices n H).biUnion (tripleBoxPart n H) = H := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨ijk, hijk, hpart⟩
    exact (mem_tripleBoxPart.mp hpart).1
  · intro hp
    have hamb := hH hp
    have hidx : tripleScale p ∈ tripleScaleIndices n :=
      tripleScale_mem_indices hamb
    have hpart : p ∈ tripleBoxPart n H (tripleScale p) :=
      mem_tripleBoxPart.mpr ⟨hp, rfl⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨tripleScale p,
      mem_activeTripleBoxIndices.mpr ⟨hidx, ⟨p, hpart⟩⟩, hpart⟩

/-- Exact cardinality decomposition over nonempty boxes only. -/
theorem card_eq_sum_card_activeTripleBoxParts {n : ℕ}
    {H : Finset (ℕ × ℕ × ℕ)} (hH : H ⊆ tripleAmbient n) :
    H.card = ∑ ijk ∈ activeTripleBoxIndices n H,
      (tripleBoxPart n H ijk).card := by
  have hmap : Set.MapsTo tripleScale (H : Set (ℕ × ℕ × ℕ))
      (activeTripleBoxIndices n H : Set (ℕ × ℕ × ℕ)) := by
    intro p hp
    have hamb := hH hp
    have hpart : p ∈ tripleBoxPart n H (tripleScale p) :=
      mem_tripleBoxPart.mpr ⟨hp, rfl⟩
    exact mem_activeTripleBoxIndices.mpr
      ⟨tripleScale_mem_indices hamb, ⟨p, hpart⟩⟩
  exact Finset.card_eq_sum_card_fiberwise hmap

end DyadicBoxes

end Erdos796
