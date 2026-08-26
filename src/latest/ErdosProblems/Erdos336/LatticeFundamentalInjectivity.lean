import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Minimal lattice representatives inject into the quotient
-/

namespace Erdos336

/-- Strict positivity for the lexicographic order on `ℤ²`. -/
def LexPositive (v : ℤ × ℤ) : Prop :=
  0 < v.1 ∨ (v.1 = 0 ∧ 0 < v.2)

/-- The integer points in an anisotropic triangle. -/
def InLatticeTriangle (H V : ℤ) (p : ℤ × ℤ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ H ∧ 0 ≤ p.2 ∧ p.2 ≤ V * p.1

/-- A point is fundamental if it lies in the triangle but cannot be moved
backward by a lexicographically positive kernel vector while staying in the
triangle. -/
def IsFundamentalPoint {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (H V : ℤ) (p : ℤ × ℤ) : Prop :=
  InLatticeTriangle H V p ∧
    ∀ v : ℤ × ℤ, φ v = 0 → LexPositive v →
      ¬ InLatticeTriangle H V (p - v)

/-- Two fundamental points in the same kernel class coincide. -/
theorem fundamentalPoint_injective
    {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (H V : ℤ) :
    Set.InjOn φ {p | IsFundamentalPoint φ H V p} := by
  intro p hp q hq hpq
  by_contra hpne
  rcases lt_trichotomy p.1 q.1 with hx | hx | hx
  · let v : ℤ × ℤ := q - p
    have hvker : φ v = 0 := by
      dsimp [v]
      rw [φ.map_sub, hpq, sub_self]
    have hvpos : LexPositive v := by
      left
      dsimp [v]
      omega
    have hback : q - v = p := by
      dsimp [v]
      abel
    exact (hq.2 v hvker hvpos) (hback ▸ hp.1)
  · have hyne : p.2 ≠ q.2 := by
      intro hy
      apply hpne
      exact Prod.ext hx hy
    rcases lt_or_gt_of_ne hyne with hy | hy
    · let v : ℤ × ℤ := q - p
      have hvker : φ v = 0 := by
        dsimp [v]
        rw [φ.map_sub, hpq, sub_self]
      have hvpos : LexPositive v := by
        right
        constructor
        · dsimp [v]
          omega
        · dsimp [v]
          omega
      have hback : q - v = p := by
        dsimp [v]
        abel
      exact (hq.2 v hvker hvpos) (hback ▸ hp.1)
    · let v : ℤ × ℤ := p - q
      have hvker : φ v = 0 := by
        dsimp [v]
        rw [φ.map_sub, hpq, sub_self]
      have hvpos : LexPositive v := by
        right
        constructor
        · dsimp [v]
          omega
        · dsimp [v]
          omega
      have hback : p - v = q := by
        dsimp [v]
        abel
      exact (hp.2 v hvker hvpos) (hback ▸ hq.1)
  · let v : ℤ × ℤ := p - q
    have hvker : φ v = 0 := by
      dsimp [v]
      rw [φ.map_sub, hpq, sub_self]
    have hvpos : LexPositive v := by
      left
      dsimp [v]
      omega
    have hback : p - v = q := by
      dsimp [v]
      abel
    exact (hp.2 v hvker hvpos) (hback ▸ hq.1)

/-- Every finite collection of fundamental points has size at most the size of
the target group.  No surjectivity assumption on the lattice map is needed. -/
theorem card_fundamentalPoints_le
    {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (H V : ℤ) (s : Finset (ℤ × ℤ))
    (hs : ∀ p ∈ s, IsFundamentalPoint φ H V p) :
    s.card ≤ Fintype.card G := by
  classical
  have hinj : Set.InjOn φ (s : Set (ℤ × ℤ)) := by
    intro p hp q hq hpq
    apply fundamentalPoint_injective φ H V (hs p hp) (hs q hq) hpq
  calc
    s.card = (s.image φ).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ Fintype.card G := Finset.card_le_univ _

end Erdos336
