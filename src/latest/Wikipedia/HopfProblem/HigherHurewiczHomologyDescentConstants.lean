import Wikipedia.HopfProblem.HigherHurewiczHomologyDescent
import Mathlib.Algebra.BigOperators.Fin

/-!
# Constant-simplex corrections in the original singular chain complex

The alternating face signs give the exact parity of the boundary of a
constant simplex. Odd-dimensional constant simplices are genuine boundaries.
In every positive degree a simplex with constant faces becomes a cycle
after subtracting the constant simplex of that same degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SingularMayerVietoris

/-- The boundary of a positive even-dimensional simplex has sign sum one. -/
theorem boundarySignSum_even (n : ℕ) (hn : Even (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 1 := by
  rw [Fin.sum_neg_one_pow]
  have h : ¬ Even (n + 2) := Nat.not_even_iff_odd.mpr hn.add_one
  exact if_neg h

/-- The boundary of an odd-dimensional simplex has sign sum zero. -/
theorem boundarySignSum_odd (n : ℕ) (hn : Odd (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 0 := by
  rw [Fin.sum_neg_one_pow]
  have h : Even (n + 2) := hn.add_one
  exact if_pos h

variable {X : Type} [TopologicalSpace X]

/-- The actual constant singular generator in degree `n`. -/
def constantSimplexChain (n : ℕ) (x : X) : Chains X n :=
  simplexChain X n (ContinuousMap.const (Simplex n) x)

theorem boundary_constantSimplexChain (n : ℕ) (x : X) :
    ((singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) • constantSimplexChain n x := by
  rw [constantSimplexChain, boundary_simplex]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • constantSimplexChain n x) = _
  exact (map_sum (zmultiplesHom (Chains X n) (constantSimplexChain n x))
    (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val) Finset.univ).symm

/-- In positive even degree the constant generator has the constant face as boundary. -/
theorem boundary_constantSimplexChain_even (n : ℕ) (x : X) (hn : Even (n + 1)) :
    ((singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      constantSimplexChain n x := by
  rw [boundary_constantSimplexChain, boundarySignSum_even n hn, one_smul]

/-- Odd-dimensional constant generators have zero boundary. -/
theorem boundary_constantSimplexChain_odd (n : ℕ) (x : X) (hn : Odd (n + 1)) :
    ((singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) = 0 := by
  rw [boundary_constantSimplexChain, boundarySignSum_odd n hn, zero_smul]

theorem constantSimplexChain_cycle_condition (n : ℕ) (x : X) (hn : Odd n) :
    ((singularComplex X).d n (n - 1)).hom (constantSimplexChain n x) = 0 := by
  cases n with
  | zero => simp at hn
  | succ n => exact boundary_constantSimplexChain_odd n x hn

/-- An odd-dimensional constant simplex as a cycle of the original complex. -/
def constantSimplexCycle (n : ℕ) (x : X) (hn : Odd n) :
    ModuleHomology.Cycle (singularComplex X) n :=
  ModuleHomology.mkCycle (singularComplex X) n (constantSimplexChain n x)
    (constantSimplexChain_cycle_condition n x hn)

@[simp] theorem constantSimplexCycle_val (n : ℕ) (x : X) (hn : Odd n) :
    (constantSimplexCycle n x hn).1 = constantSimplexChain n x := rfl

/-- The next constant simplex is a genuine boundary witness for this cycle. -/
@[simp] theorem constantSimplexCycle_class (n : ℕ) (x : X) (hn : Odd n) :
    ModuleHomology.cycleClass (singularComplex X) n (constantSimplexCycle n x hn) = 0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) n _).mpr
  exact ⟨constantSimplexChain (n + 1) x, boundary_constantSimplexChain_even n x hn.add_one⟩

/-- The corrected actual chain of a singular simplex in any degree. -/
def correctedSimplexChain (n : ℕ) (x : X) (smp : SingularSimplex X n) : Chains X n :=
  simplexChain X n smp - constantSimplexChain n x

/-- Constant actual faces cancel against the same faces of the constant simplex. -/
theorem correctedSimplexChain_boundary (n : ℕ) (x : X)
    (smp : SingularSimplex X (n + 1))
    (hfaces : ∀ i : Fin (n + 2), smp.comp (simplexFace n i) =
      ContinuousMap.const (Simplex n) x) :
    ((singularComplex X).d (n + 1) n).hom (correctedSimplexChain (n + 1) x smp) = 0 := by
  rw [correctedSimplexChain, map_sub, constantSimplexChain,
    boundary_simplex, boundary_simplex]
  simp only [hfaces, ContinuousMap.const_comp, sub_self]

/-- The corrected simplex as an actual positive-degree singular cycle. -/
def correctedSimplexCycle (n : ℕ) (x : X) (smp : SingularSimplex X (n + 1))
    (hfaces : ∀ i : Fin (n + 2), smp.comp (simplexFace n i) =
      ContinuousMap.const (Simplex n) x) :
    ModuleHomology.Cycle (singularComplex X) (n + 1) :=
  ModuleHomology.mkCycle (singularComplex X) (n + 1) (correctedSimplexChain (n + 1) x smp)
    (correctedSimplexChain_boundary n x smp hfaces)

@[simp] theorem correctedSimplexCycle_val (n : ℕ) (x : X)
    (smp : SingularSimplex X (n + 1))
    (hfaces : ∀ i : Fin (n + 2), smp.comp (simplexFace n i) =
      ContinuousMap.const (Simplex n) x) :
    (correctedSimplexCycle n x smp hfaces).1 =
      simplexChain X (n + 1) smp - constantSimplexChain (n + 1) x := rfl

@[simp] theorem correctedSimplexCycle_const (n : ℕ) (x : X) :
    correctedSimplexCycle n x (ContinuousMap.const (Simplex (n + 1)) x)
      (fun _ => rfl) = 0 := by
  apply Subtype.ext
  exact sub_self _

end Wikipedia.HopfProblem.HigherHurewicz
