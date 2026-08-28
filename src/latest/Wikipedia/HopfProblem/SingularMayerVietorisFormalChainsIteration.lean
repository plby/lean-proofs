import Wikipedia.HopfProblem.SingularMayerVietorisFormalChainsHomotopy
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Abel

/-!
# Iterated subdivision and its explicit homotopy

For `k` subdivisions the homotopy is the finite telescoping sum
`H + H sd + ... + H sd^(k-1)`. Its chain identity and naturality are proved
directly from the one-step formal subdivision and homotopy identities.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open scoped BigOperators

variable {V W : Type*}

/-- Every iterate of subdivision commutes with the augmented boundary. -/
theorem formalBoundary_subdivision_iterate (center : FormalCenter V) (k n : ℕ)
    (c : FormalChains V (n + 1)) :
    formalBoundary n ((formalSubdivision center (n + 1))^[k] c) =
      (formalSubdivision center n)^[k] (formalBoundary n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        formalBoundary_subdivision, ih]

/-- Naturality of every subdivision iterate. -/
theorem formalMap_subdivision_iterate (center : FormalCenter V) (center' : FormalCenter W)
    (f : V → W) (hf : ∀ n v, f (center n v) = center' n (f ∘ v))
    (k n : ℕ) (c : FormalChains V n) :
    formalMap f n ((formalSubdivision center n)^[k] c) =
      (formalSubdivision center' n)^[k] (formalMap f n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        formalMap_subdivision center center' f hf, ih]

/-- The finite telescoping homotopy from `k` subdivisions to the identity. -/
def formalSubdivisionIteratedHomotopy (center : FormalCenter V) (k n : ℕ) :
    FormalChains V n →ₗ[ℤ] FormalChains V (n + 1) :=
  ∑ j ∈ Finset.range k,
    (formalSubdivisionHomotopy center n).comp ((formalSubdivision center n) ^ j)

theorem formalSubdivisionIteratedHomotopy_apply (center : FormalCenter V) (k n : ℕ)
    (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center k n c =
      ∑ j ∈ Finset.range k,
        formalSubdivisionHomotopy center n ((formalSubdivision center n)^[j] c) := by
  simp only [formalSubdivisionIteratedHomotopy, LinearMap.sum_apply,
    LinearMap.comp_apply, Module.End.pow_apply]

@[simp] theorem formalSubdivisionIteratedHomotopy_zero (center : FormalCenter V)
    (n : ℕ) (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center 0 n c = 0 := by
  simp [formalSubdivisionIteratedHomotopy]

theorem formalSubdivisionIteratedHomotopy_succ (center : FormalCenter V) (k n : ℕ)
    (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center (k + 1) n c =
      formalSubdivisionIteratedHomotopy center k n c +
        formalSubdivisionHomotopy center n ((formalSubdivision center n)^[k] c) := by
  simp only [formalSubdivisionIteratedHomotopy_apply, Finset.sum_range_succ]

@[simp] theorem formalSubdivisionIteratedHomotopy_degree_zero (center : FormalCenter V)
    (k : ℕ) (c : FormalChains V 0) :
    formalSubdivisionIteratedHomotopy center k 0 c = 0 := by
  simp [formalSubdivisionIteratedHomotopy_apply]

@[simp] theorem formalSubdivision_iterate_degree_zero (center : FormalCenter V)
    (k : ℕ) (c : FormalChains V 0) :
    (formalSubdivision center 0)^[k] c = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', formalSubdivision_zero, ih]

/-- The iterated homotopy identity in augmented degree zero. -/
theorem formalSubdivisionIteratedHomotopy_boundary_zero (center : FormalCenter V)
    (k : ℕ) (c : FormalChains V 0) :
    formalBoundary 0 (formalSubdivisionIteratedHomotopy center k 0 c) =
      c - (formalSubdivision center 0)^[k] c := by
  simp

/-- The full telescoping identity `d Hₖ + Hₖ d = id - sd^k`. -/
theorem formalSubdivisionIteratedHomotopy_boundary (center : FormalCenter V)
    (k n : ℕ) (c : FormalChains V (n + 1)) :
    formalBoundary (n + 1) (formalSubdivisionIteratedHomotopy center k (n + 1) c) +
        formalSubdivisionIteratedHomotopy center k n (formalBoundary n c) =
      c - (formalSubdivision center (n + 1))^[k] c := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [formalSubdivisionIteratedHomotopy_succ, formalSubdivisionIteratedHomotopy_succ,
        map_add]
      have hh := formalSubdivisionHomotopy_boundary center n
        ((formalSubdivision center (n + 1))^[k] c)
      rw [formalBoundary_subdivision_iterate] at hh
      calc
        _ = (formalBoundary (n + 1)
                (formalSubdivisionIteratedHomotopy center k (n + 1) c) +
              formalSubdivisionIteratedHomotopy center k n (formalBoundary n c)) +
            (formalBoundary (n + 1)
                (formalSubdivisionHomotopy center (n + 1)
                  ((formalSubdivision center (n + 1))^[k] c)) +
              formalSubdivisionHomotopy center n
                ((formalSubdivision center n)^[k] (formalBoundary n c))) := by abel
        _ = (c - (formalSubdivision center (n + 1))^[k] c) +
            ((formalSubdivision center (n + 1))^[k] c -
              formalSubdivision center (n + 1)
                ((formalSubdivision center (n + 1))^[k] c)) := by rw [ih, hh]
        _ = c - (formalSubdivision center (n + 1))^[k + 1] c := by
          rw [Function.iterate_succ_apply']
          abel

/-- Naturality of the explicit finite homotopy sum. -/
theorem formalMap_subdivisionIteratedHomotopy (center : FormalCenter V)
    (center' : FormalCenter W) (f : V → W)
    (hf : ∀ n v, f (center n v) = center' n (f ∘ v))
    (k n : ℕ) (c : FormalChains V n) :
    formalMap f (n + 1) (formalSubdivisionIteratedHomotopy center k n c) =
      formalSubdivisionIteratedHomotopy center' k n (formalMap f n c) := by
  simp only [formalSubdivisionIteratedHomotopy_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [formalMap_subdivisionHomotopy center center' f hf,
    formalMap_subdivision_iterate center center' f hf]

end Wikipedia.HopfProblem.SingularMayerVietoris
