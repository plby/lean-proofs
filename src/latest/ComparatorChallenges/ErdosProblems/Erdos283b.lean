import Mathlib

namespace Erdos283b

open Finset BigOperators

def sumPow (A : Finset ℕ) (d : ℕ) : ℤ :=
  ∑ x ∈ A, (x : ℤ) ^ d

def sumRecip (A : Finset ℕ) : ℚ :=
  ∑ x ∈ A, ((x : ℚ))⁻¹

def sumF (a b : ℤ) (d : ℕ) (A : Finset ℕ) : ℤ :=
  a * sumPow A d + b * (A.card : ℤ)

open Classical in
noncomputable def n₀ (f : ℕ → ℤ) (α : ℚ) : WithTop ℤ :=
  let S := {N : ℤ | ∀ n : ℤ, N ≤ n →
    ∃ A : Finset ℕ, (∀ x ∈ A, 0 < x) ∧ (∑ x ∈ A, f x) = n ∧ sumRecip A = α}
  if S.Nonempty ∧ BddBelow S then ↑(sInf S) else ⊤

def mFinset (m : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image (· * m)
end Erdos283b

open Erdos283b


open Finset BigOperators

namespace Erdos283b

open scoped Classical in
theorem meta_theorem
    (a : ℤ) (ha : 0 < a)
    (b : ℤ)
    (d : ℕ) (hd : 0 < d)
    (m : ℕ) (hm : 2 ≤ m)
    (hcop : Int.gcd a m = 1)
    (s : ℕ) (hs_div : a ∣ s)
    (S : Set ℚ)
    (Q : Finset ℕ → Prop)
    (getβ : ℚ → Fin (m ^ d) → ℚ)
    (getA : ℚ → Fin (m ^ d) → Finset ℕ)
    (prop_pos : ∀ α ∈ S, ∀ i, ∀ x ∈ getA α i, 0 < x)
    (prop1 : ∀ α ∈ S, ∀ i, getβ α i ∈ S)
    (prop2 : ∀ α ∈ S, ∀ i, sumPow (getA α i) d % (m ^ d) = i)
    (prop3 : ∀ α ∈ S, ∀ i, (getA α i).card = s)
    (prop4 : ∀ α ∈ S, ∀ i, α = sumRecip (getA α i) + getβ α i / m)
    (prop5 : ∀ α ∈ S, ∀ i, ∀ B, Q B → Disjoint (getA α i) (mFinset m B))
    (prop6 : ∀ α ∈ S, ∀ i, ∀ B, Q B → Q ((getA α i) ∪ mFinset m B))
    (L : ℤ) (hL : ∀ α ∈ S, ∀ i, L ≤ sumPow (getA α i) d)
    (M : ℤ) (hM : ∀ α ∈ S, ∀ i, sumPow (getA α i) d ≤ M)
    (T : ℤ) (ht : ⌈a * (M - L) / ((m : ℚ) ^ d - 1)⌉ - 1 ≤ T)
    (r : ℕ)
    (X : ℤ) (hX : 0 ≤ X)
    (ineq1a : 0 ≤ b * r * (m ^ d - 1) - b * s + a * (M - L))
    (ineq1b : 0 ≤ b * s * (m ^ d - 1) + a * (M - L))
    (base : ∀ α ∈ S, ∀ n : ℤ,
      X - T ≤ n → n ≤ m ^ d * X + a * M + T →
      a ∣ (n - b * r) →
      ∃ A : Finset ℕ, Q A ∧ (∀ x ∈ A, 0 < x) ∧ A.card = r ∧ sumF a b d A = n ∧ sumRecip A = α)
    : ∀ α ∈ S, ∀ n : ℤ,
      X - T ≤ n →
      a ∣ (n - b * r) →
      ∃ A : Finset ℕ, Q A ∧ (∀ x ∈ A, 0 < x) ∧ sumF a b d A = n ∧ sumRecip A = α := by
  sorry

end Erdos283b
open scoped Classical in
theorem Erdos283b.general_theorem
    (a : ℤ) (ha : 0 < a)
    (b : ℤ)
    (d : ℕ) (hd : 0 < d)
    (m : ℕ) (hm : 2 ≤ m)
    (hcop : Int.gcd a m = 1)
    (s : ℕ) (hs_div : a ∣ s)
    (S : Set ℚ)
    (Q : Finset ℕ → Prop)
    (getβ : ℚ → Fin (m ^ d) → ℚ)
    (getA : ℚ → Fin (m ^ d) → Finset ℕ)
    (prop_pos : ∀ α ∈ S, ∀ i, ∀ x ∈ getA α i, 0 < x)
    (prop1 : ∀ α ∈ S, ∀ i, getβ α i ∈ S)
    (prop2 : ∀ α ∈ S, ∀ i, sumPow (getA α i) d % (m ^ d) = i)
    (prop3 : ∀ α ∈ S, ∀ i, (getA α i).card = s)
    (prop4 : ∀ α ∈ S, ∀ i, α = sumRecip (getA α i) + getβ α i / m)
    (prop5 : ∀ α ∈ S, ∀ i, ∀ B, Q B → Disjoint (getA α i) (mFinset m B))
    (prop6 : ∀ α ∈ S, ∀ i, ∀ B, Q B → Q ((getA α i) ∪ mFinset m B))
    (L : ℤ) (hL : ∀ α ∈ S, ∀ i, L ≤ sumPow (getA α i) d)
    (M : ℤ) (hM : ∀ α ∈ S, ∀ i, sumPow (getA α i) d ≤ M)
    (T : ℤ) (ht : ⌈a * (M - L) / ((m : ℚ) ^ d - 1)⌉ - 1 ≤ T)
    (l₁ l₂ : ℤ) (hl₁ : l₁ ≤ 0) (hl₂ : 0 ≤ l₂)
    (r_w : Fin a.natAbs → ℕ)
    (hr_w : ∀ w : Fin a.natAbs, a ∣ (b * r_w w - w))
    (X_w : Fin a.natAbs → ℤ)
    (hX_lower : ∀ w : Fin a.natAbs, l₁.natAbs * r_w w ≤ X_w w)
    (ineq2a : ∀ w : Fin a.natAbs,
      0 ≤ (b + l₁) * r_w w * (m ^ d - 1) - (b + l₁) * s + a * (M - L))
    (ineq2b : ∀ w : Fin a.natAbs,
      0 ≤ (b + l₂) * r_w w * (m ^ d - 1) - (b + l₂) * s + a * (M - L))
    (ineq2c : 0 ≤ (b + l₁) * s * (m ^ d - 1) + a * (M - L))
    (base_general : ∀ w : Fin a.natAbs, ∀ α ∈ S, ∀ n : ℤ,
      X_w w + l₁ * r_w w - T ≤ n →
      n ≤ m ^ d * (X_w w + l₂ * r_w w) + a * M + T →
      a ∣ (n - w) →
      ∃ A : Finset ℕ,
        Q A ∧ (∀ x ∈ A, 0 < x) ∧ A.card = r_w w ∧
          sumF a b d A = n ∧ sumRecip A = α) :
    ∀ j : ℤ, l₁ ≤ j → j ≤ l₂ → Int.gcd (b + j) a = 1 →
      ∀ α ∈ S,
        n₀ (fun x : ℕ => a * x ^ d + (b + j)) α ≤
          Finset.univ.sup' ⟨⟨0, Int.natAbs_pos.mpr ha.ne'⟩, Finset.mem_univ _⟩
            (fun w : Fin a.natAbs => X_w w + j * r_w w - T) := by
  sorry
