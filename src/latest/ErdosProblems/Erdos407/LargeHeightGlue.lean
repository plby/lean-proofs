/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.ApproximationDomain

/-!
# The large-height GLR glue for the rational p-adic Subspace Theorem

This file isolates the finite, logical part of the large-height argument.
The analytic input is deliberately kept as a hypothesis.  After the usual
finite boxing, a primitive strong solution belongs to one of finitely many
approximation domains.  For a domain containing that solution, the analytic
GLR step says either that its rational rank has dropped, or that the same
solution belongs to another one of the fixed domains with strictly larger
height parameter.  The latter alternative cannot continue indefinitely
inside a finite family.

Thus every sufficiently large solution belongs to a rank-dropping
approximation domain.  Such a domain lies in one proper rational hyperplane,
and the finitely many domains give a finite hyperplane cover.  Finally the
bounded-height points are added using the elementary lemmas in
`PadicSubspace.lean`.

No Subspace-Theorem conclusion is assumed here: the only analytic assertion
is rank drop (or the stated fixed-exception-or-height-growth alternative) for
the concrete approximation domains.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators

/-- The height parameter and exponent box defining one approximation domain. -/
structure ApproximationDatum (n : ℕ) where
  scale : ℕ
  exponents : LocalExponents n

namespace ApproximationDatum

/-- The rational approximation domain attached to one datum. -/
def domain {n : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (c : ApproximationDatum n) : Set (Fin n → ℚ) :=
  approximationDomain c.scale L c.exponents

@[simp] theorem mem_domain {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {c : ApproximationDatum n} {x : Fin n → ℚ} :
    x ∈ c.domain L ↔
      ∀ v i, placeNorm v (L v i x) ≤ localRadius c.scale (c.exponents v i) :=
  Iff.rfl

end ApproximationDatum

/-- The genuinely analytic conclusion needed from one approximation datum:
its rational span has dimension strictly below the ambient dimension. -/
def ApproximationDatum.RankDrops {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (c : ApproximationDatum n) : Prop :=
  approximationDomainRank c.scale L c.exponents < n

/-- Primitive strong solutions whose integral height is above a cutoff. -/
def largePrimitiveStrongSolutions {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (H : ℕ) :
    Set (Fin n → ℤ) :=
  {x | x ∈ primitiveStrongSolutions L ∧ H < boxHeight x}

@[simp] theorem mem_largePrimitiveStrongSolutions {n H : ℕ}
    {L : Place23 → Fin n → RatLinearForm n} {x : Fin n → ℤ} :
    x ∈ largePrimitiveStrongSolutions L H ↔
      x ∈ primitiveStrongSolutions L ∧ H < boxHeight x :=
  Iff.rfl

/-- A fixed finite collection of approximation domains covers all primitive
strong solutions above `H`.  This is the finite-boxing, non-analytic input. -/
def IsFiniteApproximationCover {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (H : ℕ)
    (C : Finset (ApproximationDatum n)) : Prop :=
  ∀ x ∈ largePrimitiveStrongSolutions L H,
    ∃ c ∈ C, intCastVec x ∈ c.domain L

/-- The minimal fixed-exception-or-height-growth statement used by the GLR
induction.  A datum containing a large solution either has rank drop, or the
same solution occurs in a datum from the same fixed finite collection with a
strictly larger height parameter.

The next datum may depend on the solution.  No uniform choice, hyperplane,
or finite-cover conclusion is hidden in this hypothesis. -/
def FixedExceptionOrHeightGrowth {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (H : ℕ)
    (C : Finset (ApproximationDatum n)) : Prop :=
  ∀ c ∈ C, ∀ x ∈ largePrimitiveStrongSolutions L H,
    intCastVec x ∈ c.domain L →
      c.RankDrops L ∨
        ∃ d ∈ C, c.scale < d.scale ∧ intCastVec x ∈ d.domain L

/-! ## The finite GLR induction -/

/-- In a finite approximation family, repeated strict growth of the scale
must end at a rank-dropping datum. -/
theorem exists_rankDropping_datum
    {n H : ℕ} {L : Place23 → Fin n → RatLinearForm n}
    {C : Finset (ApproximationDatum n)}
    (hcover : IsFiniteApproximationCover L H C)
    (hGLR : FixedExceptionOrHeightGrowth L H C) :
    ∀ x ∈ largePrimitiveStrongSolutions L H,
      ∃ c ∈ C, c.RankDrops L ∧ intCastVec x ∈ c.domain L := by
  classical
  intro x hx
  obtain ⟨c, hcC, hxc⟩ := hcover x hx
  let M : ℕ := C.sup ApproximationDatum.scale
  have hreach :
      ∀ k : ℕ, ∀ c : ApproximationDatum n,
        M - c.scale = k → c ∈ C → intCastVec x ∈ c.domain L →
          ∃ d ∈ C, d.RankDrops L ∧ intCastVec x ∈ d.domain L := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro c hck hcC hxc
        rcases hGLR c hcC x hx hxc with hdrop | ⟨d, hdC, hcd, hxd⟩
        · exact ⟨c, hcC, hdrop, hxc⟩
        · have hcM : c.scale ≤ M := by
            exact Finset.le_sup (s := C) (f := ApproximationDatum.scale) hcC
          have hdM : d.scale ≤ M := by
            exact Finset.le_sup (s := C) (f := ApproximationDatum.scale) hdC
          have hrem : M - d.scale < k := by omega
          exact ih (M - d.scale) hrem d rfl hdC hxd
  exact hreach (M - c.scale) c rfl hcC hxc

/-! ## Rank drop gives proper rational hyperplanes -/

/-- A finite family of rank-dropping approximation domains gives a finite
hyperplane cover of every set whose points belong to one of those domains. -/
theorem hasFiniteHyperplaneCover_of_finite_rankDropping_domains
    {n : ℕ} {L : Place23 → Fin n → RatLinearForm n}
    {X : Set (Fin n → ℤ)} (C : Finset (ApproximationDatum n))
    (hX : ∀ x ∈ X, ∃ c ∈ C,
      c.RankDrops L ∧ intCastVec x ∈ c.domain L) :
    HasFiniteHyperplaneCover X := by
  classical
  let R : Finset (ApproximationDatum n) := C.filter fun c ↦ c.RankDrops L
  have hRrank (c : {c // c ∈ R}) : c.1.RankDrops L := by
    exact (Finset.mem_filter.mp c.2).2
  choose f hf hvan using fun c : {c // c ∈ R} ↦
    approximationDomain_subset_hyperplane_of_rank_lt
      L c.1.exponents (hRrank c)
  let B : Finset (Fin n → ℚ) :=
    Finset.univ.image fun c : {c // c ∈ R} ↦ coefficientVector (f c)
  refine ⟨B, ?_, ?_⟩
  · intro b hb
    simp only [B, Finset.mem_image] at hb
    obtain ⟨c, _hc, rfl⟩ := hb
    exact coefficientVector_ne_zero (hf c)
  · intro x hx
    obtain ⟨c, hcC, hcrank, hxc⟩ := hX x hx
    have hcR : c ∈ R := Finset.mem_filter.mpr ⟨hcC, hcrank⟩
    let rc : {c // c ∈ R} := ⟨c, hcR⟩
    refine ⟨coefficientVector (f rc), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩
    · change ∑ i, coefficientVector (f rc) i * (x i : ℚ) = 0
      rw [← linearForm_eq_dotProduct]
      exact hvan rc (intCastVec x) hxc

/-- The direct finite-box form: if every datum in a finite approximation
cover has rank drop, all large primitive strong solutions have a finite
hyperplane cover. -/
theorem largeHeight_finiteCover_of_rankDrop
    {n H : ℕ} {L : Place23 → Fin n → RatLinearForm n}
    (C : Finset (ApproximationDatum n))
    (hcover : IsFiniteApproximationCover L H C)
    (hrank : ∀ c ∈ C, c.RankDrops L) :
    HasFiniteHyperplaneCover (largePrimitiveStrongSolutions L H) := by
  refine hasFiniteHyperplaneCover_of_finite_rankDropping_domains (L := L) C ?_
  intro x hx
  obtain ⟨c, hcC, hxc⟩ := hcover x hx
  exact ⟨c, hcC, hrank c hcC, hxc⟩

/-- The abstract GLR conclusion above a fixed height.  The induction in
`exists_rankDropping_datum` eliminates the height-growth alternative. -/
theorem largeHeight_finiteCover_of_fixedExceptionOrHeightGrowth
    {n H : ℕ} {L : Place23 → Fin n → RatLinearForm n}
    (C : Finset (ApproximationDatum n))
    (hcover : IsFiniteApproximationCover L H C)
    (hGLR : FixedExceptionOrHeightGrowth L H C) :
    HasFiniteHyperplaneCover (largePrimitiveStrongSolutions L H) := by
  apply hasFiniteHyperplaneCover_of_finite_rankDropping_domains C
  exact exists_rankDropping_datum hcover hGLR

/-- Package the GLR conclusion in the large-height interface from
`PadicSubspace.lean`. -/
theorem largeHeightSubspaceConclusion_of_fixedExceptionOrHeightGrowth
    {n H : ℕ} {L : Place23 → Fin n → RatLinearForm n}
    (C : Finset (ApproximationDatum n))
    (hcover : IsFiniteApproximationCover L H C)
    (hGLR : FixedExceptionOrHeightGrowth L H C) :
    HasLargeHeightSubspaceConclusion L := by
  refine ⟨H, ?_⟩
  exact largeHeight_finiteCover_of_fixedExceptionOrHeightGrowth C hcover hGLR

/-- The full finite-cover theorem obtained from the analytic GLR hypothesis:
large solutions are covered by the preceding induction, while bounded
nonzero integral solutions are absorbed by the elementary PadicSubspace
cover. -/
theorem finiteCover_of_fixedExceptionOrHeightGrowth
    {n H : ℕ} (hn : 2 ≤ n)
    {L : Place23 → Fin n → RatLinearForm n}
    (C : Finset (ApproximationDatum n))
    (hcover : IsFiniteApproximationCover L H C)
    (hGLR : FixedExceptionOrHeightGrowth L H C) :
    HasFiniteHyperplaneCover (primitiveStrongSolutions L) := by
  apply finiteCover_of_largeHeightConclusion hn
  exact largeHeightSubspaceConclusion_of_fixedExceptionOrHeightGrowth C hcover hGLR

/-- The corresponding full theorem when the analytic input directly gives
rank drop for every member of the finite approximation cover. -/
theorem finiteCover_of_rankDrop
    {n H : ℕ} (hn : 2 ≤ n)
    {L : Place23 → Fin n → RatLinearForm n}
    (C : Finset (ApproximationDatum n))
    (hcover : IsFiniteApproximationCover L H C)
    (hrank : ∀ c ∈ C, c.RankDrops L) :
    HasFiniteHyperplaneCover (primitiveStrongSolutions L) := by
  apply finiteCover_of_largeHeightConclusion hn
  exact ⟨H, largeHeight_finiteCover_of_rankDrop C hcover hrank⟩

end Erdos407.PadicSubspace
