/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Basic
import ErdosProblems.Erdos285.UpperAssembly
import UnitFractions.Definitions

/-!
# Erdős Problem 284: elementary definitions and finite-set infrastructure

The problem maximizes the first denominator of a strictly increasing
Egyptian-fraction representation.  This file records the literal indexed
predicate, its finite-set form, and the natural-valued short-interval
interface used by the Croot construction.
-/

open Filter
open scoped BigOperators Topology Real

namespace Erdos284

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A strictly increasing representation of one by exactly `k + 1` positive,
distinct unit fractions. -/
def Representation (k : ℕ) (n : Fin k.succ → ℕ) : Prop :=
  StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i

/-- The indices for which a `k + 1`-term representation exists. -/
def ValidIndices : Set ℕ :=
  {k | ∃ n : Fin k.succ → ℕ, Representation k n}

/-- The possible first denominators of `k + 1`-term representations. -/
def FirstDenominators (k : ℕ) : Set ℕ :=
  {n 0 |
    (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
      (_ : 1 = ∑ i, (1 : ℝ) / n i)}

/-- `m` is the greatest possible first denominator for `k + 1` terms. -/
def IsMaximalFirstDenominator (k m : ℕ) : Prop :=
  IsGreatest (FirstDenominators k) m

@[simp] theorem mem_validIndices {k : ℕ} :
    k ∈ ValidIndices ↔ ∃ n : Fin k.succ → ℕ, Representation k n :=
  Iff.rfl

@[simp] theorem mem_firstDenominators {k m : ℕ} :
    m ∈ FirstDenominators k ↔
      ∃ n : Fin k.succ → ℕ, Representation k n ∧ n 0 = m := by
  simp only [FirstDenominators, Representation, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hnmono, hnzero, hnsum, rfl⟩
    exact ⟨n, ⟨hnmono, hnzero, hnsum⟩, rfl⟩
  · rintro ⟨n, ⟨hnmono, hnzero, hnsum⟩, rfl⟩
    exact ⟨n, hnmono, hnzero, hnsum, rfl⟩

/-- The finite-set formulation used by all constructions. -/
structure FinsetRepresentation (t : ℕ) (A : Finset ℕ) : Prop where
  card_eq : A.card = t
  zero_not_mem : 0 ∉ A
  sum_eq : UnitFractions.rec_sum A = 1

namespace FinsetRepresentation

theorem nonempty {t : ℕ} {A : Finset ℕ} (hA : FinsetRepresentation t A)
    (ht : 0 < t) : A.Nonempty := by
  rw [← Finset.card_pos, hA.card_eq]
  exact ht

theorem two_le {t : ℕ} {A : Finset ℕ} (hA : FinsetRepresentation t A)
    {n : ℕ} (hn : n ∈ A) : 1 ≤ n := by
  exact Nat.one_le_iff_ne_zero.mpr fun hn0 ↦ hA.zero_not_mem (hn0 ▸ hn)

end FinsetRepresentation

/-- Increasingly enumerate a finite-set representation. -/
def enumerate {k : ℕ} (A : Finset ℕ) (hcard : A.card = k.succ) :
    Fin k.succ → ℕ :=
  Erdos285.enumerate A hcard

theorem representation_enumerate {k : ℕ} {A : Finset ℕ}
    (hA : FinsetRepresentation k.succ A) :
    Representation k (enumerate A hA.card_eq) := by
  unfold enumerate
  refine ⟨Erdos285.enumerate_strictMono A hA.card_eq, ?_, ?_⟩
  · rw [Erdos285.range_enumerate A hA.card_eq]
    simpa using hA.zero_not_mem
  · rw [Erdos285.sum_enumerate A hA.card_eq]
    have hcast := congrArg (fun q : ℚ ↦ (q : ℝ)) hA.sum_eq
    simpa [UnitFractions.rec_sum, Rat.cast_sum, Rat.cast_div,
      Rat.cast_one, Rat.cast_natCast] using hcast.symm

theorem enumerate_zero_eq_min' {k : ℕ} (A : Finset ℕ)
    (hcard : A.card = k.succ) :
    enumerate A hcard 0 = A.min' (Finset.card_pos.mp (by omega)) := by
  unfold enumerate
  exact Finset.orderEmbOfFin_zero hcard (Nat.succ_pos k)

/-- A finite witness whose denominators lie in the natural interval `(N, X]`. -/
structure ShortIntervalWitness (N X : ℕ) (A : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ A
  sum_eq : UnitFractions.rec_sum A = 1
  interval : ∀ n ∈ A, N < n ∧ n ≤ X

/-- The exact filter-level form of Croot's `r = 1` theorem needed below. -/
def HasCrootShortIntervals : Prop :=
  ∃ X : ℕ → ℕ,
    Tendsto (fun N : ℕ ↦ (X N : ℝ) / (N : ℝ)) atTop (nhds (Real.exp 1)) ∧
    ∀ᶠ N : ℕ in atTop,
      ∃ A : Finset ℕ, ShortIntervalWitness N (X N) A

end

end Erdos284

#print axioms Erdos284.representation_enumerate
#print axioms Erdos284.enumerate_zero_eq_min'
