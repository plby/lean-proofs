import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Erdos327.Analytic

open scoped BigOperators

/-- The zero set modulo `p` of the first linear form in the centered
three-line configuration `(U, V, U + V)`. -/
def centeredZeroU (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun x => x.1 = 0

/-- The zero set modulo `p` of the second linear form in the centered
three-line configuration `(U, V, U + V)`. -/
def centeredZeroV (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun x => x.2 = 0

/-- The zero set modulo `p` of the third linear form in the centered
three-line configuration `(U, V, U + V)`. -/
def centeredZeroSum (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun x => x.1 + x.2 = 0

/-- The zero set modulo `p` of the first linear form in the cross
three-line configuration `(U, W, 2U + W)`. -/
def crossZeroU (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun x => x.1 = 0

/-- The zero set modulo `p` of the second linear form in the cross
three-line configuration `(U, W, 2U + W)`. -/
def crossZeroW (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun x => x.2 = 0

/-- The zero set modulo `p` of the third linear form in the cross
three-line configuration `(U, W, 2U + W)`. -/
def crossZeroLinear (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun x => 2 * x.1 + x.2 = 0

@[simp] theorem mem_centeredZeroU {p : ℕ} [NeZero p] {x : ZMod p × ZMod p} :
    x ∈ centeredZeroU p ↔ x.1 = 0 := by
  simp [centeredZeroU]

@[simp] theorem mem_centeredZeroV {p : ℕ} [NeZero p] {x : ZMod p × ZMod p} :
    x ∈ centeredZeroV p ↔ x.2 = 0 := by
  simp [centeredZeroV]

@[simp] theorem mem_centeredZeroSum {p : ℕ} [NeZero p] {x : ZMod p × ZMod p} :
    x ∈ centeredZeroSum p ↔ x.1 + x.2 = 0 := by
  simp [centeredZeroSum]

@[simp] theorem mem_crossZeroU {p : ℕ} [NeZero p] {x : ZMod p × ZMod p} :
    x ∈ crossZeroU p ↔ x.1 = 0 := by
  simp [crossZeroU]

@[simp] theorem mem_crossZeroW {p : ℕ} [NeZero p] {x : ZMod p × ZMod p} :
    x ∈ crossZeroW p ↔ x.2 = 0 := by
  simp [crossZeroW]

@[simp] theorem mem_crossZeroLinear {p : ℕ} [NeZero p] {x : ZMod p × ZMod p} :
    x ∈ crossZeroLinear p ↔ 2 * x.1 + x.2 = 0 := by
  simp [crossZeroLinear]

/-- The graph of any function on `ZMod p` has exactly `p` points. -/
private theorem card_graph (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    (Finset.univ.filter fun x : ZMod p × ZMod p => x.2 = f x.1).card = p := by
  calc
    (Finset.univ.filter fun x : ZMod p × ZMod p => x.2 = f x.1).card =
        (Finset.univ : Finset (ZMod p)).card := by
      refine Finset.card_bij (fun x _ => x.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro a ha b hb hab
        have ha' : a.2 = f a.1 := (Finset.mem_filter.mp ha).2
        have hb' : b.2 = f b.1 := (Finset.mem_filter.mp hb).2
        apply Prod.ext hab
        simp [ha', hb', hab]
      · intro u hu
        exact ⟨(u, f u), by simp, rfl⟩
    _ = p := by simp [ZMod.card]

/-- The transposed graph of any function on `ZMod p` has exactly `p`
points. -/
private theorem card_verticalGraph (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    (Finset.univ.filter fun x : ZMod p × ZMod p => x.1 = f x.2).card = p := by
  calc
    (Finset.univ.filter fun x : ZMod p × ZMod p => x.1 = f x.2).card =
        (Finset.univ : Finset (ZMod p)).card := by
      refine Finset.card_bij (fun x _ => x.2) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro a ha b hb hab
        have ha' : a.1 = f a.2 := (Finset.mem_filter.mp ha).2
        have hb' : b.1 = f b.2 := (Finset.mem_filter.mp hb).2
        apply Prod.ext
        · simp [ha', hb', hab]
        · exact hab
      · intro v hv
        exact ⟨(f v, v), by simp, rfl⟩
    _ = p := by simp [ZMod.card]

@[simp] theorem card_centeredZeroU (p : ℕ) [NeZero p] :
    (centeredZeroU p).card = p := by
  simpa [centeredZeroU] using card_verticalGraph p (fun _ => 0)

@[simp] theorem card_centeredZeroV (p : ℕ) [NeZero p] :
    (centeredZeroV p).card = p := by
  simpa [centeredZeroV] using card_graph p (fun _ => 0)

@[simp] theorem card_centeredZeroSum (p : ℕ) [NeZero p] :
    (centeredZeroSum p).card = p := by
  simpa [centeredZeroSum, eq_neg_iff_add_eq_zero, add_comm] using
    card_graph p (fun u => -u)

@[simp] theorem card_crossZeroU (p : ℕ) [NeZero p] :
    (crossZeroU p).card = p := by
  simpa [crossZeroU] using card_verticalGraph p (fun _ => 0)

@[simp] theorem card_crossZeroW (p : ℕ) [NeZero p] :
    (crossZeroW p).card = p := by
  simpa [crossZeroW] using card_graph p (fun _ => 0)

@[simp] theorem card_crossZeroLinear (p : ℕ) [NeZero p] :
    (crossZeroLinear p).card = p := by
  simpa [crossZeroLinear, eq_neg_iff_add_eq_zero, add_comm] using
    card_graph p (fun u => -(2 * u))

/-- Any two centered forms vanish simultaneously only at the origin. -/
theorem centered_pairwise_zero_iff_origin {p : ℕ} (x : ZMod p × ZMod p) :
    ((x.1 = 0 ∧ x.2 = 0) ∨
      (x.1 = 0 ∧ x.1 + x.2 = 0) ∨
      (x.2 = 0 ∧ x.1 + x.2 = 0)) ↔ x = (0, 0) := by
  rcases x with ⟨u, v⟩
  simp only [Prod.mk.injEq]
  constructor
  · rintro (h | h | h)
    · exact h
    · exact ⟨h.1, by simpa [h.1] using h.2⟩
    · exact ⟨by simpa [h.1] using h.2, h.1⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- For an odd prime, any two cross forms vanish simultaneously only at
the origin. -/
theorem cross_pairwise_zero_iff_origin {p : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (x : ZMod p × ZMod p) :
    ((x.1 = 0 ∧ x.2 = 0) ∨
      (x.1 = 0 ∧ 2 * x.1 + x.2 = 0) ∨
      (x.2 = 0 ∧ 2 * x.1 + x.2 = 0)) ↔ x = (0, 0) := by
  let hpFact : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    change ((2 : ℕ) : ZMod p) = 0 at hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hp2 : 2 ≤ p := hp.two_le
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by omega) hdiv
    omega
  rcases x with ⟨u, w⟩
  simp only [Prod.mk.injEq]
  constructor
  · rintro (h | h | h)
    · exact h
    · exact ⟨h.1, by simpa [h.1] using h.2⟩
    · refine ⟨?_, h.1⟩
      have : (2 : ZMod p) * u = 0 := by simpa [h.1] using h.2
      exact (mul_eq_zero.mp this).resolve_left htwo
  · rintro ⟨rfl, rfl⟩
    simp

/-- The union of the three centered zero sets. -/
def centeredBadResidues (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  centeredZeroU p ∪ centeredZeroV p ∪ centeredZeroSum p

/-- The union of the three cross zero sets. -/
def crossBadResidues (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  crossZeroU p ∪ crossZeroW p ∪ crossZeroLinear p

theorem centeredZeroU_inter_centeredZeroV (p : ℕ) [NeZero p] :
    centeredZeroU p ∩ centeredZeroV p = {(0, 0)} := by
  ext x
  constructor
  · intro hx
    have hzero := (centered_pairwise_zero_iff_origin x).mp
      (Or.inl ⟨mem_centeredZeroU.mp (Finset.mem_inter.mp hx).1,
        mem_centeredZeroV.mp (Finset.mem_inter.mp hx).2⟩)
    simpa using hzero
  · intro hx
    have : x = (0, 0) := by simpa using hx
    subst x
    simp

theorem centeredZeroU_inter_centeredZeroSum (p : ℕ) [NeZero p] :
    centeredZeroU p ∩ centeredZeroSum p = {(0, 0)} := by
  ext x
  constructor
  · intro hx
    have hzero := (centered_pairwise_zero_iff_origin x).mp
      (Or.inr (Or.inl ⟨mem_centeredZeroU.mp (Finset.mem_inter.mp hx).1,
        mem_centeredZeroSum.mp (Finset.mem_inter.mp hx).2⟩))
    simpa using hzero
  · intro hx
    have : x = (0, 0) := by simpa using hx
    subst x
    simp

theorem centeredZeroV_inter_centeredZeroSum (p : ℕ) [NeZero p] :
    centeredZeroV p ∩ centeredZeroSum p = {(0, 0)} := by
  ext x
  constructor
  · intro hx
    have hzero := (centered_pairwise_zero_iff_origin x).mp
      (Or.inr (Or.inr ⟨mem_centeredZeroV.mp (Finset.mem_inter.mp hx).1,
        mem_centeredZeroSum.mp (Finset.mem_inter.mp hx).2⟩))
    simpa using hzero
  · intro hx
    have : x = (0, 0) := by simpa using hx
    subst x
    simp

theorem crossZeroU_inter_crossZeroW (p : ℕ) [NeZero p]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    crossZeroU p ∩ crossZeroW p = {(0, 0)} := by
  ext x
  constructor
  · intro hx
    have hzero := (cross_pairwise_zero_iff_origin hp hpodd x).mp
      (Or.inl ⟨mem_crossZeroU.mp (Finset.mem_inter.mp hx).1,
        mem_crossZeroW.mp (Finset.mem_inter.mp hx).2⟩)
    simpa using hzero
  · intro hx
    have : x = (0, 0) := by simpa using hx
    subst x
    simp

theorem crossZeroU_inter_crossZeroLinear (p : ℕ) [NeZero p]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    crossZeroU p ∩ crossZeroLinear p = {(0, 0)} := by
  ext x
  constructor
  · intro hx
    have hzero := (cross_pairwise_zero_iff_origin hp hpodd x).mp
      (Or.inr (Or.inl ⟨mem_crossZeroU.mp (Finset.mem_inter.mp hx).1,
        mem_crossZeroLinear.mp (Finset.mem_inter.mp hx).2⟩))
    simpa using hzero
  · intro hx
    have : x = (0, 0) := by simpa using hx
    subst x
    simp

theorem crossZeroW_inter_crossZeroLinear (p : ℕ) [NeZero p]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    crossZeroW p ∩ crossZeroLinear p = {(0, 0)} := by
  ext x
  constructor
  · intro hx
    have hzero := (cross_pairwise_zero_iff_origin hp hpodd x).mp
      (Or.inr (Or.inr ⟨mem_crossZeroW.mp (Finset.mem_inter.mp hx).1,
        mem_crossZeroLinear.mp (Finset.mem_inter.mp hx).2⟩))
    simpa using hzero
  · intro hx
    have : x = (0, 0) := by simpa using hx
    subst x
    simp

/-- Exactly `3p - 2` residue pairs make at least one of
`U`, `V`, and `U + V` vanish modulo `p`. -/
theorem card_centeredBadResidues (p : ℕ) [NeZero p] :
    (centeredBadResidues p).card = 3 * p - 2 := by
  have hab := Finset.card_union_add_card_inter (centeredZeroU p) (centeredZeroV p)
  rw [centeredZeroU_inter_centeredZeroV] at hab
  simp only [card_centeredZeroU, card_centeredZeroV, Finset.card_singleton] at hab
  have habc :
      (centeredZeroU p ∪ centeredZeroV p) ∩ centeredZeroSum p = {(0, 0)} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, hc⟩
      · have hx : x ∈ centeredZeroU p ∩ centeredZeroSum p :=
          Finset.mem_inter.mpr ⟨h, hc⟩
        simpa [centeredZeroU_inter_centeredZeroSum] using hx
      · have hx : x ∈ centeredZeroV p ∩ centeredZeroSum p :=
          Finset.mem_inter.mpr ⟨h, hc⟩
        simpa [centeredZeroV_inter_centeredZeroSum] using hx
    · intro hx
      subst x
      simp
  have habc_card := Finset.card_union_add_card_inter
    (centeredZeroU p ∪ centeredZeroV p) (centeredZeroSum p)
  rw [habc] at habc_card
  simp only [card_centeredZeroSum, Finset.card_singleton] at habc_card
  change (centeredZeroU p ∪ centeredZeroV p ∪ centeredZeroSum p).card = 3 * p - 2
  omega

/-- Exactly `3p - 2` residue pairs make at least one of
`U`, `W`, and `2U + W` vanish modulo an odd prime `p`. -/
theorem card_crossBadResidues (p : ℕ) [NeZero p]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    (crossBadResidues p).card = 3 * p - 2 := by
  have hab := Finset.card_union_add_card_inter (crossZeroU p) (crossZeroW p)
  rw [crossZeroU_inter_crossZeroW p hp hpodd] at hab
  simp only [card_crossZeroU, card_crossZeroW, Finset.card_singleton] at hab
  have habc :
      (crossZeroU p ∪ crossZeroW p) ∩ crossZeroLinear p = {(0, 0)} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, hc⟩
      · have hx : x ∈ crossZeroU p ∩ crossZeroLinear p :=
          Finset.mem_inter.mpr ⟨h, hc⟩
        simpa [crossZeroU_inter_crossZeroLinear p hp hpodd] using hx
      · have hx : x ∈ crossZeroW p ∩ crossZeroLinear p :=
          Finset.mem_inter.mpr ⟨h, hc⟩
        simpa [crossZeroW_inter_crossZeroLinear p hp hpodd] using hx
    · intro hx
      subst x
      simp
  have habc_card := Finset.card_union_add_card_inter
    (crossZeroU p ∪ crossZeroW p) (crossZeroLinear p)
  rw [habc] at habc_card
  simp only [card_crossZeroLinear, Finset.card_singleton] at habc_card
  change (crossZeroU p ∪ crossZeroW p ∪ crossZeroLinear p).card = 3 * p - 2
  omega

/-- Product local weight attached to the centered forms `U`, `V`, and
`U + V`. -/
def centeredLocalWeight {p : ℕ} {R : Type*} [One R] [Mul R]
    (qU qV qSum : R) (x : ZMod p × ZMod p) : R :=
  (if x.1 = 0 then qU else 1) *
    (if x.2 = 0 then qV else 1) *
    (if x.1 + x.2 = 0 then qSum else 1)

/-- Product local weight attached to the cross forms `U`, `W`, and
`2U + W`. -/
def crossLocalWeight {p : ℕ} {R : Type*} [One R] [Mul R]
    (qU qW qLinear : R) (x : ZMod p × ZMod p) : R :=
  (if x.1 = 0 then qU else 1) *
    (if x.2 = 0 then qW else 1) *
    (if 2 * x.1 + x.2 = 0 then qLinear else 1)

private theorem sum_indicator_const
    {X R : Type*} [Fintype X] [CommRing R]
    (P : X → Prop) [DecidablePred P] (c : R) :
    (∑ x : X, if P x then c else 0) =
      ((Finset.univ.filter P).card : R) * c := by
  rw [Finset.sum_ite]
  simp

private theorem weighted_three_predicate_sum
    {X R : Type*} [Fintype X] [CommRing R]
    (P₁ P₂ P₃ : X → Prop)
    [DecidablePred P₁] [DecidablePred P₂] [DecidablePred P₃]
    (q₁ q₂ q₃ : R) (n₁ n₂ n₃ : ℕ)
    (h₁ : (Finset.univ.filter P₁).card = n₁)
    (h₂ : (Finset.univ.filter P₂).card = n₂)
    (h₃ : (Finset.univ.filter P₃).card = n₃)
    (h₁₂ : (Finset.univ.filter fun x => P₁ x ∧ P₂ x).card = 1)
    (h₁₃ : (Finset.univ.filter fun x => P₁ x ∧ P₃ x).card = 1)
    (h₂₃ : (Finset.univ.filter fun x => P₂ x ∧ P₃ x).card = 1)
    (h₁₂₃ : (Finset.univ.filter fun x => P₁ x ∧ P₂ x ∧ P₃ x).card = 1) :
    (∑ x : X,
        (if P₁ x then q₁ else 1) *
          (if P₂ x then q₂ else 1) *
          (if P₃ x then q₃ else 1)) =
      (Fintype.card X : R) +
        (n₁ : R) * (q₁ - 1) +
        (n₂ : R) * (q₂ - 1) +
        (n₃ : R) * (q₃ - 1) +
        (q₁ - 1) * (q₂ - 1) +
        (q₁ - 1) * (q₃ - 1) +
        (q₂ - 1) * (q₃ - 1) +
        (q₁ - 1) * (q₂ - 1) * (q₃ - 1) := by
  classical
  have hpoint (x : X) :
      (if P₁ x then q₁ else 1) *
          (if P₂ x then q₂ else 1) *
          (if P₃ x then q₃ else 1) =
        1 +
          (if P₁ x then q₁ - 1 else 0) +
          (if P₂ x then q₂ - 1 else 0) +
          (if P₃ x then q₃ - 1 else 0) +
          (if P₁ x ∧ P₂ x then (q₁ - 1) * (q₂ - 1) else 0) +
          (if P₁ x ∧ P₃ x then (q₁ - 1) * (q₃ - 1) else 0) +
          (if P₂ x ∧ P₃ x then (q₂ - 1) * (q₃ - 1) else 0) +
          (if P₁ x ∧ P₂ x ∧ P₃ x then
            (q₁ - 1) * (q₂ - 1) * (q₃ - 1) else 0) := by
    by_cases h₁x : P₁ x <;> by_cases h₂x : P₂ x <;> by_cases h₃x : P₃ x <;>
      simp [h₁x, h₂x, h₃x] <;> ring
  calc
    _ = ∑ x : X,
        (1 +
          (if P₁ x then q₁ - 1 else 0) +
          (if P₂ x then q₂ - 1 else 0) +
          (if P₃ x then q₃ - 1 else 0) +
          (if P₁ x ∧ P₂ x then (q₁ - 1) * (q₂ - 1) else 0) +
          (if P₁ x ∧ P₃ x then (q₁ - 1) * (q₃ - 1) else 0) +
          (if P₂ x ∧ P₃ x then (q₂ - 1) * (q₃ - 1) else 0) +
          (if P₁ x ∧ P₂ x ∧ P₃ x then
            (q₁ - 1) * (q₂ - 1) * (q₃ - 1) else 0)) := by
          exact Finset.sum_congr rfl fun x _ => hpoint x
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
      rw [sum_indicator_const, sum_indicator_const, sum_indicator_const,
        sum_indicator_const, sum_indicator_const, sum_indicator_const,
        sum_indicator_const]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h₁, h₂, h₃,
        h₁₂, h₁₃, h₂₃, h₁₂₃, Nat.cast_one, one_mul, mul_one]

@[simp] theorem centeredLocalWeight_origin
    {p : ℕ} {R : Type*} [Monoid R] (qU qV qSum : R) :
    centeredLocalWeight qU qV qSum ((0, 0) : ZMod p × ZMod p) =
      qU * qV * qSum := by
  simp [centeredLocalWeight]

theorem centeredLocalWeight_of_only_U
    {p : ℕ} {R : Type*} [Monoid R] (qU qV qSum : R)
    (x : ZMod p × ZMod p) (hU : x.1 = 0) (hV : x.2 ≠ 0)
    (hSum : x.1 + x.2 ≠ 0) :
    centeredLocalWeight qU qV qSum x = qU := by
  simp only [centeredLocalWeight, if_pos hU, if_neg hV, if_neg hSum, mul_one]

theorem centeredLocalWeight_of_only_V
    {p : ℕ} {R : Type*} [Monoid R] (qU qV qSum : R)
    (x : ZMod p × ZMod p) (hU : x.1 ≠ 0) (hV : x.2 = 0)
    (hSum : x.1 + x.2 ≠ 0) :
    centeredLocalWeight qU qV qSum x = qV := by
  simp only [centeredLocalWeight, if_neg hU, if_pos hV, if_neg hSum, one_mul, mul_one]

theorem centeredLocalWeight_of_only_sum
    {p : ℕ} {R : Type*} [Monoid R] (qU qV qSum : R)
    (x : ZMod p × ZMod p) (hU : x.1 ≠ 0) (hV : x.2 ≠ 0)
    (hSum : x.1 + x.2 = 0) :
    centeredLocalWeight qU qV qSum x = qSum := by
  simp only [centeredLocalWeight, if_neg hU, if_neg hV, if_pos hSum, one_mul]

@[simp] theorem crossLocalWeight_origin
    {p : ℕ} {R : Type*} [Monoid R] (qU qW qLinear : R) :
    crossLocalWeight qU qW qLinear ((0, 0) : ZMod p × ZMod p) =
      qU * qW * qLinear := by
  simp [crossLocalWeight]

theorem crossLocalWeight_of_only_U
    {p : ℕ} {R : Type*} [Monoid R] (qU qW qLinear : R)
    (x : ZMod p × ZMod p) (hU : x.1 = 0) (hW : x.2 ≠ 0)
    (hLinear : 2 * x.1 + x.2 ≠ 0) :
    crossLocalWeight qU qW qLinear x = qU := by
  simp only [crossLocalWeight, if_pos hU, if_neg hW, if_neg hLinear, mul_one]

theorem crossLocalWeight_of_only_W
    {p : ℕ} {R : Type*} [Monoid R] (qU qW qLinear : R)
    (x : ZMod p × ZMod p) (hU : x.1 ≠ 0) (hW : x.2 = 0)
    (hLinear : 2 * x.1 + x.2 ≠ 0) :
    crossLocalWeight qU qW qLinear x = qW := by
  simp only [crossLocalWeight, if_neg hU, if_pos hW, if_neg hLinear, one_mul, mul_one]

theorem crossLocalWeight_of_only_linear
    {p : ℕ} {R : Type*} [Monoid R] (qU qW qLinear : R)
    (x : ZMod p × ZMod p) (hU : x.1 ≠ 0) (hW : x.2 ≠ 0)
    (hLinear : 2 * x.1 + x.2 = 0) :
    crossLocalWeight qU qW qLinear x = qLinear := by
  simp only [crossLocalWeight, if_neg hU, if_neg hW, if_pos hLinear, one_mul]

/-- Exact finite-field sum of the centered local weight. -/
theorem sum_centeredLocalWeight
    {R : Type*} [CommRing R] (p : ℕ) [NeZero p] (qU qV qSum : R) :
    (∑ x : ZMod p × ZMod p, centeredLocalWeight qU qV qSum x) =
      (p : R) ^ 2 - 3 * (p : R) + 2 +
        ((p : R) - 1) * (qU + qV + qSum) + qU * qV * qSum := by
  classical
  have h12 :
      (Finset.univ.filter fun x : ZMod p × ZMod p =>
        x.1 = 0 ∧ x.2 = 0).card = 1 := by
    have heq :
        (Finset.univ.filter fun x : ZMod p × ZMod p => x.1 = 0 ∧ x.2 = 0) =
          centeredZeroU p ∩ centeredZeroV p := by
      ext x
      simp
    rw [heq, centeredZeroU_inter_centeredZeroV]
    simp
  have h13 :
      (Finset.univ.filter fun x : ZMod p × ZMod p =>
        x.1 = 0 ∧ x.1 + x.2 = 0).card = 1 := by
    have heq :
        (Finset.univ.filter fun x : ZMod p × ZMod p =>
          x.1 = 0 ∧ x.1 + x.2 = 0) =
          centeredZeroU p ∩ centeredZeroSum p := by
      ext x
      simp
    rw [heq, centeredZeroU_inter_centeredZeroSum]
    simp
  have h23 :
      (Finset.univ.filter fun x : ZMod p × ZMod p =>
        x.2 = 0 ∧ x.1 + x.2 = 0).card = 1 := by
    have heq :
        (Finset.univ.filter fun x : ZMod p × ZMod p =>
          x.2 = 0 ∧ x.1 + x.2 = 0) =
          centeredZeroV p ∩ centeredZeroSum p := by
      ext x
      simp
    rw [heq, centeredZeroV_inter_centeredZeroSum]
    simp
  have h123 :
      (Finset.univ.filter fun x : ZMod p × ZMod p =>
        x.1 = 0 ∧ x.2 = 0 ∧ x.1 + x.2 = 0).card = 1 := by
    have heq :
        (Finset.univ.filter fun x : ZMod p × ZMod p =>
          x.1 = 0 ∧ x.2 = 0 ∧ x.1 + x.2 = 0) = {(0, 0)} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hU, hV, _⟩
        exact Prod.ext hU hV
      · rintro rfl
        simp
    rw [heq]
    simp
  have hsum := weighted_three_predicate_sum
    (X := ZMod p × ZMod p) (R := R)
    (fun x => x.1 = 0) (fun x => x.2 = 0) (fun x => x.1 + x.2 = 0)
    qU qV qSum p p p
    (by simpa [centeredZeroU] using card_centeredZeroU p)
    (by simpa [centeredZeroV] using card_centeredZeroV p)
    (by simpa [centeredZeroSum] using card_centeredZeroSum p)
    h12 h13 h23 h123
  rw [show (∑ x : ZMod p × ZMod p, centeredLocalWeight qU qV qSum x) =
      ∑ x : ZMod p × ZMod p,
        (if x.1 = 0 then qU else 1) *
          (if x.2 = 0 then qV else 1) *
          (if x.1 + x.2 = 0 then qSum else 1) by
      rfl]
  rw [hsum]
  simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul]
  ring

/-- Exact finite-field sum of the cross local weight at an odd prime. -/
theorem sum_crossLocalWeight
    {R : Type*} [CommRing R] (p : ℕ) [NeZero p]
    (hp : p.Prime) (hpodd : p ≠ 2) (qU qW qLinear : R) :
    (∑ x : ZMod p × ZMod p, crossLocalWeight qU qW qLinear x) =
      (p : R) ^ 2 - 3 * (p : R) + 2 +
        ((p : R) - 1) * (qU + qW + qLinear) + qU * qW * qLinear := by
  classical
  have h12 :
      (Finset.univ.filter fun x : ZMod p × ZMod p =>
        x.1 = 0 ∧ x.2 = 0).card = 1 := by
    have heq :
        (Finset.univ.filter fun x : ZMod p × ZMod p => x.1 = 0 ∧ x.2 = 0) =
          crossZeroU p ∩ crossZeroW p := by
      ext x
      simp
    rw [heq, crossZeroU_inter_crossZeroW p hp hpodd]
    simp
  have h13 :
      (Finset.univ.filter fun x : ZMod p × ZMod p =>
        x.1 = 0 ∧ 2 * x.1 + x.2 = 0).card = 1 := by
    have heq :
        (Finset.univ.filter fun x : ZMod p × ZMod p =>
          x.1 = 0 ∧ 2 * x.1 + x.2 = 0) =
          crossZeroU p ∩ crossZeroLinear p := by
      ext x
      simp
    rw [heq, crossZeroU_inter_crossZeroLinear p hp hpodd]
    simp
  have h23 :
      (Finset.univ.filter fun x : ZMod p × ZMod p =>
        x.2 = 0 ∧ 2 * x.1 + x.2 = 0).card = 1 := by
    have heq :
        (Finset.univ.filter fun x : ZMod p × ZMod p =>
          x.2 = 0 ∧ 2 * x.1 + x.2 = 0) =
          crossZeroW p ∩ crossZeroLinear p := by
      ext x
      simp
    rw [heq, crossZeroW_inter_crossZeroLinear p hp hpodd]
    simp
  have h123 :
      (Finset.univ.filter fun x : ZMod p × ZMod p =>
        x.1 = 0 ∧ x.2 = 0 ∧ 2 * x.1 + x.2 = 0).card = 1 := by
    have heq :
        (Finset.univ.filter fun x : ZMod p × ZMod p =>
          x.1 = 0 ∧ x.2 = 0 ∧ 2 * x.1 + x.2 = 0) = {(0, 0)} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hU, hW, _⟩
        exact Prod.ext hU hW
      · rintro rfl
        simp
    rw [heq]
    simp
  have hsum := weighted_three_predicate_sum
    (X := ZMod p × ZMod p) (R := R)
    (fun x => x.1 = 0) (fun x => x.2 = 0) (fun x => 2 * x.1 + x.2 = 0)
    qU qW qLinear p p p
    (by simpa [crossZeroU] using card_crossZeroU p)
    (by simpa [crossZeroW] using card_crossZeroW p)
    (by simpa [crossZeroLinear] using card_crossZeroLinear p)
    h12 h13 h23 h123
  rw [show (∑ x : ZMod p × ZMod p, crossLocalWeight qU qW qLinear x) =
      ∑ x : ZMod p × ZMod p,
        (if x.1 = 0 then qU else 1) *
          (if x.2 = 0 then qW else 1) *
          (if 2 * x.1 + x.2 = 0 then qLinear else 1) by
      rfl]
  rw [hsum]
  simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul]
  ring

end Erdos327.Analytic
