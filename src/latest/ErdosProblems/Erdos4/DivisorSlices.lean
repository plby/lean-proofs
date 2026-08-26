import ErdosProblems.Erdos4.DivisorCoefficients
import Mathlib.Logic.Equiv.Prod

/-!
# Conductor-coordinate slices of the actual divisor coefficients

Splitting the prime coordinates into a finite set and its complement is an
exact reindexing. The monotone erasure inequality therefore bounds each
slice by the full coefficient energy, with the product of the local
square-root divisor factors and no loss depending on the cutoff.
-/

open scoped BigOperators

namespace Erdos4.DivisorSlices

open DivisorCoefficients RestrictedProductNorm

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

def join (J : Finset P) (a : J → Option (Fin k))
    (b : {p : P // p ∉ J} → Option (Fin k)) (p : P) : Option (Fin k) :=
  if hp : p ∈ J then a ⟨p, hp⟩ else b ⟨p, hp⟩

noncomputable def slice (m : ℝ) (R : ℕ) (ell : P → ℕ) (J : Finset P)
    (a : J → Option (Fin k)) (b : {p : P // p ∉ J} → Option (Fin k)) : ℝ :=
  coefficient m R ell (join J a b)

noncomputable def sliceFactor (ell : P → ℕ) (J : Finset P)
    (a : J → Option (Fin k)) : ℝ :=
  ∏ p : J, localWeight (ell p) (a p)

omit [Fintype P] in
theorem erase_join (J : Finset P) (a : J → Option (Fin k))
    (b : {p : P // p ∉ J} → Option (Fin k)) :
    erase J (join J a b) = join J (fun _ => none) b := by
  funext p
  by_cases hp : p ∈ J <;> simp [erase, join, hp]

omit [Fintype P] in
theorem removedFactor_join (ell : P → ℕ) (J : Finset P)
    (a : J → Option (Fin k)) (b : {p : P // p ∉ J} → Option (Fin k)) :
    removedFactor ell J (join J a b) = sliceFactor ell J a := by
  unfold removedFactor sliceFactor
  rw [← Finset.prod_coe_sort J (fun p => localWeight (ell p) (join J a b p))]
  apply Finset.prod_congr rfl
  intro p _hp
  simp only [join, dif_pos p.property]

omit [Fintype P] [DecidableEq P] in
theorem sliceFactor_nonneg (ell : P → ℕ) (J : Finset P) (a : J → Option (Fin k)) :
    0 ≤ sliceFactor ell J a :=
  Finset.prod_nonneg (fun p _hp => localWeight_nonneg (ell p) (a p))

theorem slice_nonneg {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (J : Finset P) (a : J → Option (Fin k))
    (b : {p : P // p ∉ J} → Option (Fin k)) : 0 ≤ slice m R ell J a b :=
  coefficient_nonneg hm hR ell (join J a b)

/-- The conductor slice is pointwise dominated by the empty conductor slice. -/
theorem abs_slice_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (a : J → Option (Fin k)) (b : {p : P // p ∉ J} → Option (Fin k)) :
    |slice m R ell J a b| ≤ sliceFactor ell J a * |slice m R ell J (fun _ => none) b| := by
  rw [abs_of_nonneg (slice_nonneg (by linarith) hR ell J a b),
    abs_of_nonneg (slice_nonneg (by linarith) hR ell J (fun _ => none) b)]
  have hh := coefficient_le_removedFactor_mul_erase hm hR ell hell J (join J a b)
  rw [erase_join, removedFactor_join] at hh
  exact hh

theorem sum_join (J : Finset P) (f : (P → Option (Fin k)) → ℝ) :
    (∑ a : J → Option (Fin k), ∑ b : {p : P // p ∉ J} → Option (Fin k),
      f (join J a b)) = ∑ c, f c := by
  let e := Equiv.piEquivPiSubtypeProd (fun p : P => p ∈ J)
    (fun _ => Option (Fin k))
  have hh := e.symm.sum_comp f
  rw [Fintype.sum_prod_type] at hh
  exact hh

theorem sum_slice_energy (m : ℝ) (R : ℕ) (ell : P → ℕ) (J : Finset P) :
    (∑ a : J → Option (Fin k), energy (slice m R ell J a)) =
      energy (coefficient (k := k) m R ell) := by
  unfold energy slice
  exact sum_join J (fun c => coefficient m R ell c ^ 2)

/-- The exact full norm controls every actual conductor slice. -/
theorem slice_energy_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (a : J → Option (Fin k)) :
    energy (slice m R ell J a) ≤ sliceFactor ell J a ^ 2 *
      energy (coefficient (k := k) m R ell) := by
  have hh := SliceBounds.slice_energy_le_total (slice m R ell J) (fun _ => none)
    (sliceFactor ell J) (sliceFactor_nonneg ell J) (abs_slice_le hm hR ell hell J) a
  rwa [sum_slice_energy] at hh

end Erdos4.DivisorSlices
