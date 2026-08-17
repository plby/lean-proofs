/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
module

public import ErdosProblems.Erdos565.Graph

/-!
# The induced Ramsey number

This file packages existence of induced Ramsey hosts and the least admissible
host order.  The definition of `inducedRamseyNumber` takes an existence proof
as an explicit argument.  In particular, merely introducing the notation for
the least order does not smuggle in the difficult existence theorem.
-/

@[expose] public section

namespace Erdos565

/-- Some finite host witnesses the induced Ramsey property for `G`. -/
def InducedRamseyExists {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ m, IsInducedRamseyOrder G m

/-- An induced Ramsey host for `G` exists with at most `bound` vertices. -/
def HasInducedRamseyOrderAtMost {n : ℕ} (G : SimpleGraph (Fin n))
    (bound : ℕ) : Prop :=
  ∃ m ≤ bound, IsInducedRamseyOrder G m

/-- A bounded witness in particular proves qualitative existence. -/
theorem HasInducedRamseyOrderAtMost.exists {n bound : ℕ}
    {G : SimpleGraph (Fin n)}
    (h : HasInducedRamseyOrderAtMost G bound) : InducedRamseyExists G := by
  rcases h with ⟨m, _, hm⟩
  exact ⟨m, hm⟩

/-- An order itself gives a bounded witness at that same order. -/
theorem IsInducedRamseyOrder.hasAtMost {n m : ℕ}
    {G : SimpleGraph (Fin n)} (h : IsInducedRamseyOrder G m) :
    HasInducedRamseyOrderAtMost G m :=
  ⟨m, le_rfl, h⟩

/-- Bounded existence is monotone in the numerical bound. -/
theorem HasInducedRamseyOrderAtMost.mono {n a b : ℕ}
    {G : SimpleGraph (Fin n)} (h : HasInducedRamseyOrderAtMost G a)
    (hab : a ≤ b) : HasInducedRamseyOrderAtMost G b := by
  rcases h with ⟨m, hma, hm⟩
  exact ⟨m, hma.trans hab, hm⟩

/--
The least order of an induced Ramsey host, defined only after a proof that such
a host exists has been supplied.
-/
noncomputable def inducedRamseyNumber {n : ℕ} (G : SimpleGraph (Fin n))
    (exists_host : InducedRamseyExists G) : ℕ :=
  by
    classical
    exact Nat.find exists_host

/-- The least order selected by `inducedRamseyNumber` is a Ramsey order. -/
theorem inducedRamseyNumber_spec {n : ℕ} (G : SimpleGraph (Fin n))
    (exists_host : InducedRamseyExists G) :
    IsInducedRamseyOrder G (inducedRamseyNumber G exists_host) := by
  classical
  simpa only [inducedRamseyNumber] using Nat.find_spec exists_host

/-- No Ramsey order is smaller than `inducedRamseyNumber`. -/
theorem inducedRamseyNumber_minimal {n m : ℕ} (G : SimpleGraph (Fin n))
    (exists_host : InducedRamseyExists G) (hm : IsInducedRamseyOrder G m) :
    inducedRamseyNumber G exists_host ≤ m := by
  classical
  simpa only [inducedRamseyNumber] using Nat.find_min' exists_host hm

/-- Every number below `inducedRamseyNumber` fails to be a Ramsey order. -/
theorem not_isInducedRamseyOrder_of_lt_inducedRamseyNumber {n m : ℕ}
    (G : SimpleGraph (Fin n)) (exists_host : InducedRamseyExists G)
    (hm : m < inducedRamseyNumber G exists_host) :
    ¬ IsInducedRamseyOrder G m := by
  intro hm'
  exact (Nat.not_lt_of_ge (inducedRamseyNumber_minimal G exists_host hm')) hm

/-- The numerical value is independent of the proof of qualitative existence. -/
theorem inducedRamseyNumber_proof_irrel {n : ℕ} (G : SimpleGraph (Fin n))
    (h₁ h₂ : InducedRamseyExists G) :
    inducedRamseyNumber G h₁ = inducedRamseyNumber G h₂ := by
  congr

/-- A bounded host theorem yields the corresponding upper bound on the minimum. -/
theorem inducedRamseyNumber_le_of_hasAtMost {n bound : ℕ}
    (G : SimpleGraph (Fin n)) (exists_host : InducedRamseyExists G)
    (h : HasInducedRamseyOrderAtMost G bound) :
    inducedRamseyNumber G exists_host ≤ bound := by
  rcases h with ⟨m, hmb, hm⟩
  exact (inducedRamseyNumber_minimal G exists_host hm).trans hmb

/-- Bounded host existence is equivalent to the usual upper-bound formulation. -/
theorem hasInducedRamseyOrderAtMost_iff {n bound : ℕ}
    (G : SimpleGraph (Fin n)) (exists_host : InducedRamseyExists G) :
    HasInducedRamseyOrderAtMost G bound ↔
      inducedRamseyNumber G exists_host ≤ bound := by
  constructor
  · exact inducedRamseyNumber_le_of_hasAtMost G exists_host
  · intro h
    exact ⟨inducedRamseyNumber G exists_host, h,
      inducedRamseyNumber_spec G exists_host⟩

/-- An order works exactly when it is at least the least Ramsey order. -/
theorem isInducedRamseyOrder_iff_inducedRamseyNumber_le {n m : ℕ}
    (G : SimpleGraph (Fin n)) (exists_host : InducedRamseyExists G) :
    IsInducedRamseyOrder G m ↔ inducedRamseyNumber G exists_host ≤ m := by
  constructor
  · exact inducedRamseyNumber_minimal G exists_host
  · intro h
    exact (inducedRamseyNumber_spec G exists_host).mono h

/-- A convenient predicate for a uniform numerical upper bound. -/
def UniformInducedRamseyBound (bound : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    HasInducedRamseyOrderAtMost G (bound n)

/-- A uniform bound also gives qualitative existence for every finite graph. -/
theorem UniformInducedRamseyBound.exists {bound : ℕ → ℕ}
    (h : UniformInducedRamseyBound bound) (n : ℕ)
    (G : SimpleGraph (Fin n)) : InducedRamseyExists G :=
  (h n G).exists

/-- A uniform bounded-host theorem yields the same bound for the least order. -/
theorem UniformInducedRamseyBound.inducedRamseyNumber_le {bound : ℕ → ℕ}
    (h : UniformInducedRamseyBound bound) (n : ℕ)
    (G : SimpleGraph (Fin n)) :
    inducedRamseyNumber G (h.exists n G) ≤ bound n :=
  inducedRamseyNumber_le_of_hasAtMost G (h.exists n G) (h n G)

end Erdos565
