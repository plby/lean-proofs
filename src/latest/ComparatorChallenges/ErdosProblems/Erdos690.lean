import Mathlib

open Filter Set
open scoped Topology BigOperators

noncomputable section


namespace Erdos690

open scoped Classical in
def IsKthSmallestPrimeFactor (k p n : ℕ) : Prop :=
  0 < k ∧ p ∈ n.primeFactors ∧
    (n.primeFactors.filter (fun q => q < p)).card = k - 1

end Erdos690

namespace Erdos690

open scoped Classical in
def kthPrimeFactorSet (k p : ℕ) : Set ℕ :=
  {n | IsKthSmallestPrimeFactor k p n}

end Erdos690

namespace Set

open scoped Classical in
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

open scoped Classical in
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos690

open scoped Classical in
def coeffStep (a : ℕ) (row : List ℕ) : List ℕ :=
  (List.range (row.length + 1)).map fun r =>
    a * row.getD r 0 + if r = 0 then 0 else row.getD (r - 1) 0

end Erdos690

namespace Erdos690

open scoped Classical in
def coeffRow (p : ℕ) : List ℕ :=
  (List.range p).foldl
    (fun row q => if q.Prime then coeffStep (q - 1) row else row) [1]

end Erdos690

namespace Erdos690

open scoped Classical in
def coeff (r p : ℕ) : ℕ := (coeffRow p).getD r 0

end Erdos690

namespace Erdos690

open scoped Classical in
def primeModulus (p : ℕ) : ℕ :=
  (List.range p).foldl (fun n q => if q.Prime then n * q else n) 1

end Erdos690

namespace Erdos690

open scoped Classical in
def primeFactorDensity (k p : ℕ) : ℚ :=
  if 0 < k ∧ p.Prime then
    (coeff (k - 1) p : ℚ) / (p * primeModulus p : ℕ)
  else 0

end Erdos690

namespace Erdos690

open scoped Classical in
def UnimodalOnPrimes {α : Type*} [Preorder α] (f : ℕ → α) : Prop :=
  ∃ m, m.Prime ∧
    (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ m → f p ≤ f q) ∧
    (∀ p q, p.Prime → q.Prime → m ≤ p → p ≤ q → f q ≤ f p)

end Erdos690

namespace Erdos690

open scoped Classical in
def DensityUnimodal (k : ℕ) : Prop :=
  UnimodalOnPrimes (primeFactorDensity k)

end Erdos690

namespace Erdos690

open scoped Classical in
theorem erdos_690 :
    (∀ k p, 0 < k → p.Prime →
      (kthPrimeFactorSet k p).HasDensity
        ((primeFactorDensity k p : ℚ) : ℝ)) ∧
    (∀ k, 1 ≤ k → k ≤ 3 → DensityUnimodal k) ∧
    (∀ k, 4 ≤ k → k ≤ 20 → ¬DensityUnimodal k) := by
  sorry

end Erdos690

end
