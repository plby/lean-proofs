import Mathlib

open scoped BigOperators

namespace ZpTuckerScratch

abbrev SignedVector (p n : ℕ) := Fin n → Option (ZMod p)

def SignedVector.Nonzero {p n : ℕ} (x : SignedVector p n) : Prop :=
  ∃ i, x i ≠ none

def SignedVector.LE {p n : ℕ} (x y : SignedVector p n) : Prop :=
  ∀ i g, x i = some g → y i = some g

instance {p n : ℕ} : LE (SignedVector p n) := ⟨SignedVector.LE⟩

@[simp] theorem SignedVector.le_def {p n : ℕ} {x y : SignedVector p n} :
    x ≤ y ↔ ∀ i g, x i = some g → y i = some g := Iff.rfl

theorem SignedVector.le_refl {p n : ℕ} (x : SignedVector p n) : x ≤ x := by
  intro i g h
  exact h

theorem SignedVector.le_trans {p n : ℕ} {x y z : SignedVector p n}
    (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  intro i g h
  exact hyz i g (hxy i g h)

theorem SignedVector.le_antisymm {p n : ℕ} {x y : SignedVector p n}
    (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  funext i
  cases hxi : x i with
  | none =>
      cases hyi : y i with
      | none => rfl
      | some g =>
          have h := hyx i g hyi
          rw [hxi] at h
          contradiction
  | some g =>
      cases hyi : y i with
      | none =>
          have h := hxy i g hxi
          rw [hyi] at h
          contradiction
      | some g' =>
          have h := hxy i g hxi
          rw [hyi] at h
          cases h
          rfl

instance {p n : ℕ} : PartialOrder (SignedVector p n) where
  le_refl := SignedVector.le_refl
  le_trans _ _ _ := SignedVector.le_trans
  le_antisymm _ _ := SignedVector.le_antisymm

def SignedVector.shift {p n : ℕ} (a : ZMod p) (x : SignedVector p n) :
    SignedVector p n := fun i => (x i).map (a + ·)

@[simp] theorem SignedVector.shift_apply {p n : ℕ} (a : ZMod p)
    (x : SignedVector p n) (i : Fin n) :
    x.shift a i = (x i).map (a + ·) := rfl

@[simp] theorem SignedVector.shift_zero {p n : ℕ} (x : SignedVector p n) :
    x.shift 0 = x := by
  funext i
  cases h : x i <;> simp [SignedVector.shift, h]

@[simp] theorem SignedVector.shift_add {p n : ℕ} (a b : ZMod p)
    (x : SignedVector p n) :
    (x.shift b).shift a = x.shift (a + b) := by
  funext i
  cases x i <;> simp [SignedVector.shift, add_assoc]

theorem SignedVector.Nonzero.shift {p n : ℕ} {x : SignedVector p n}
    (hx : x.Nonzero) (a : ZMod p) : (x.shift a).Nonzero := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  rcases h : x i with _ | g
  · exact (hi h).elim
  · simp [SignedVector.shift, h]

theorem SignedVector.shift_mono {p n : ℕ} {x y : SignedVector p n}
    (hxy : x ≤ y) (a : ZMod p) : x.shift a ≤ y.shift a := by
  intro i g hi
  rcases hxi : x i with _ | b
  · simp [SignedVector.shift, hxi] at hi
  · simp only [SignedVector.shift, hxi, Option.map_some] at hi
    have hab : a + b = g := Option.some.inj hi
    change (y i).map (a + ·) = some g
    rw [hxy i _ hxi, ← hab]
    rfl

abbrev NonzeroSignedVector (p n : ℕ) :=
  {x : SignedVector p n // x.Nonzero}

def NonzeroSignedVector.shift {p n : ℕ} (a : ZMod p)
    (x : NonzeroSignedVector p n) : NonzeroSignedVector p n :=
  ⟨x.1.shift a, x.2.shift a⟩

instance {p n : ℕ} : LE (NonzeroSignedVector p n) :=
  ⟨fun x y => x.1 ≤ y.1⟩

instance {p n : ℕ} : PartialOrder (NonzeroSignedVector p n) :=
  PartialOrder.lift Subtype.val Subtype.val_injective

@[simp] theorem NonzeroSignedVector.coe_shift {p n : ℕ} (a : ZMod p)
    (x : NonzeroSignedVector p n) :
    (x.shift a : SignedVector p n) = x.1.shift a := rfl

theorem NonzeroSignedVector.shift_mono {p n : ℕ} {x y : NonzeroSignedVector p n}
    (hxy : x ≤ y) (a : ZMod p) : x.shift a ≤ y.shift a :=
  SignedVector.shift_mono hxy a

/-- A fully signed chain: a strictly increasing p-chain whose labels have one
common second coordinate and every element of `ZMod p` occurs as a first coordinate. -/
def FullySignedChain {p n m : ℕ}
    (lab : NonzeroSignedVector p n → ZMod p × Fin m) : Prop :=
  ∃ x : Fin p → NonzeroSignedVector p n,
    StrictMono x ∧
    (∃ j : Fin m, ∀ i, (lab (x i)).2 = j) ∧
    Function.Surjective (fun i => (lab (x i)).1)

/-- Equivariance for the cyclic shift action. -/
def IsEquivariant {p n m : ℕ}
    (lab : NonzeroSignedVector p n → ZMod p × Fin m) : Prop :=
  ∀ a x, lab (x.shift a) = (a + (lab x).1, (lab x).2)

/-- The two hypotheses of the alpha-split Z_p-Tucker lemma. Indices below
`alpha` have only one sign along a chain; indices at least `alpha` never see
all p signs on a p-chain. -/
def IsAlphaAdmissible {p n m : ℕ} (alpha : ℕ)
    (lab : NonzeroSignedVector p n → ZMod p × Fin m) : Prop :=
  (∀ ⦃x y⦄, x ≤ y → (lab x).2 = (lab y).2 →
      (lab x).2.val < alpha → (lab x).1 = (lab y).1) ∧
  (∀ (x : Fin p → NonzeroSignedVector p n), Monotone x →
      (∃ j : Fin m, alpha ≤ j.val ∧ ∀ i, (lab (x i)).2 = j) →
      ¬ Function.Surjective (fun i => (lab (x i)).1))

end ZpTuckerScratch
