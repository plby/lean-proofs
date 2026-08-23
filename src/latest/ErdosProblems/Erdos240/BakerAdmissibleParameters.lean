/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerParameters

/-!
# Admissible source parameters for van der Poorten--Loxton

This file separates two logically different roles of the parameter called
`k` in van der Poorten--Loxton:

* the elementary baseline in `BakerParameters` proves the radical-prime
  inequality `13 <= k ^ epsilon`;
* equation (1) is the single bound
  `(32 * (rank+1))^(1/epsilon) < k`, proved already by the canonical seed;
* the three additional p.39 hypotheses and subsequent corrected estimates
  impose a finite collection of further lower bounds.

The baseline is not asserted to satisfy the latter bounds.  Instead we choose
one real number strictly above the baseline and every member of a finite set
of requirements.  The three additional p.39 requirements are included
explicitly below (specialized to field degree `D = 1`).  The
`extra` argument is for further explicit bounds introduced by the
corrigendum or by later estimates.  Thus adding a requirement cannot silently
invalidate an earlier fixed numerical choice.

After setting `D = 1`, these three requirements are
`81^(rank+1)`, `6^(1/epsilon)`, and
`(10/epsilon)^((1+mu)(rank+1))`.

This module addresses only the choice of `k`.  The current
`VDPLParameters` structure does **not** itself express four other source
hypotheses which must be discharged at the application site:

* at least two logarithms (`Nonempty ι` in the old-prime specialization);
* ordered height majorants and `1 <= log (log A_i)`;
* that `kRequirements` is independent of the varying prime and coefficient
  bound.  This dependency discipline is established by the family-level
  constructor, not by the field's type.

In particular, a height floor of `exp 2` is insufficient for the displayed
double-logarithm hypothesis: it gives `log (log (exp 2)) = log 2 < 1`.
-/

namespace Erdos240

open scoped NNReal
open Finset

noncomputable section

namespace VDPLParameters

variable {ι : Type*} [Fintype ι] (P : VDPLParameters ι)

/-- The degree-one version of the first additional p.39 lower bound. -/
def sourceDimensionThreshold : ℝ :=
  (81 : ℝ) ^ (P.rank + 1 : ℝ)

/-- The second additional p.39 lower bound, `6^(1/epsilon)`.  The separate
auxiliary-prime constraint `13 ≤ k^epsilon` is proved in `BakerParameters`. -/
def sourceSixThreshold : ℝ :=
  (6 : ℝ) ^ (1 / P.epsilon)

/-- The degree-one specialization of the third additional p.39 bound. -/
def sourceTenThreshold : ℝ :=
  (10 / P.epsilon : ℝ) ^ ((1 + P.mu) * (P.rank + 1 : ℝ))

/-- The three explicit additional p.39 requirements, together with any
finite family required by corrected or later estimates. -/
def sourceRequirements (extra : Finset ℝ) : Finset ℝ :=
  insert P.sourceDimensionThreshold
    (insert P.sourceSixThreshold (insert P.sourceTenThreshold extra))

theorem sourceDimensionThreshold_mem (extra : Finset ℝ) :
    P.sourceDimensionThreshold ∈ P.sourceRequirements extra := by
  simp [sourceRequirements]

theorem sourceSixThreshold_mem (extra : Finset ℝ) :
    P.sourceSixThreshold ∈ P.sourceRequirements extra := by
  simp [sourceRequirements]

theorem sourceTenThreshold_mem (extra : Finset ℝ) :
    P.sourceTenThreshold ∈ P.sourceRequirements extra := by
  simp [sourceRequirements]

theorem mem_sourceRequirements_of_mem {extra : Finset ℝ} {x : ℝ}
    (hx : x ∈ extra) : x ∈ P.sourceRequirements extra := by
  simp [sourceRequirements, hx]

/-- Install the complete finite requirement set before any source quantities
are formed.  The supplied `extra` set must itself be chosen from the fixed old
family, and is deliberately the only caller-supplied dependency: arbitrary
requirements already stored in `P` are discarded.  This point is important
both for uniformity in the varying prime and because all later definitions
(`C`, `Slevel`, `R`, side lengths, and coefficient height) must use the
resulting parameter's actual `k`, rather than a detached larger number. -/
def withSourceRequirements (extra : Finset ℝ) : VDPLParameters ι where
  old := P.old
  old_prime := P.old_prime
  old_injective := P.old_injective
  newPrime := P.newPrime
  new_prime := P.new_prime
  new_fresh := P.new_fresh
  Bsrc := P.Bsrc
  Bsrc_lower := P.Bsrc_lower
  kRequirements := P.sourceRequirements extra

@[simp] theorem withSourceRequirements_old (extra : Finset ℝ) :
    (P.withSourceRequirements extra).old = P.old := rfl

@[simp] theorem withSourceRequirements_newPrime (extra : Finset ℝ) :
    (P.withSourceRequirements extra).newPrime = P.newPrime := rfl

@[simp] theorem withSourceRequirements_Bsrc (extra : Finset ℝ) :
    (P.withSourceRequirements extra).Bsrc = P.Bsrc := rfl

@[simp] theorem withSourceRequirements_rank (extra : Finset ℝ) :
    (P.withSourceRequirements extra).rank = P.rank := rfl

@[simp] theorem withSourceRequirements_mu (extra : Finset ℝ) :
    (P.withSourceRequirements extra).mu = P.mu := rfl

@[simp] theorem withSourceRequirements_kappa (extra : Finset ℝ) :
    (P.withSourceRequirements extra).kappa = P.kappa := rfl

@[simp] theorem withSourceRequirements_epsilon (extra : Finset ℝ) :
    (P.withSourceRequirements extra).epsilon = P.epsilon := rfl

@[simp] theorem withSourceRequirements_q (extra : Finset ℝ) :
    (P.withSourceRequirements extra).q = P.q := rfl

@[simp] theorem withSourceRequirements_dimensionThreshold (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceDimensionThreshold =
      P.sourceDimensionThreshold := rfl

@[simp] theorem withSourceRequirements_sixThreshold (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceSixThreshold =
      P.sourceSixThreshold := rfl

@[simp] theorem withSourceRequirements_tenThreshold (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceTenThreshold =
      P.sourceTenThreshold := rfl

/-- With the same index type and the same fixed finite requirement set, the
actual source parameter is definitionally independent of the varying prime,
the coefficient bound, and the numerical values of the old primes. -/
theorem withSourceRequirements_k_eq (Q : VDPLParameters ι)
    (extra : Finset ℝ) :
    (P.withSourceRequirements extra).k =
      (Q.withSourceRequirements extra).k := by
  rfl

theorem sourceDimensionThreshold_mem_withSourceRequirements (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceDimensionThreshold ∈
      (P.withSourceRequirements extra).kRequirements := by
  rw [P.withSourceRequirements_dimensionThreshold]
  simp [withSourceRequirements, sourceRequirements]

theorem sourceSixThreshold_mem_withSourceRequirements (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceSixThreshold ∈
      (P.withSourceRequirements extra).kRequirements := by
  rw [P.withSourceRequirements_sixThreshold]
  simp [withSourceRequirements, sourceRequirements]

theorem sourceTenThreshold_mem_withSourceRequirements (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceTenThreshold ∈
      (P.withSourceRequirements extra).kRequirements := by
  rw [P.withSourceRequirements_tenThreshold]
  simp [withSourceRequirements, sourceRequirements]

theorem mem_withSourceRequirements_of_mem {extra : Finset ℝ} {x : ℝ}
    (hx : x ∈ extra) : x ∈ (P.withSourceRequirements extra).kRequirements := by
  simp [withSourceRequirements, sourceRequirements, hx]

theorem withSourceRequirements_dimension_lt_k (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceDimensionThreshold <
      (P.withSourceRequirements extra).k := by
  exact (P.withSourceRequirements extra).requirement_lt_k
    (P.sourceDimensionThreshold_mem_withSourceRequirements extra)

theorem withSourceRequirements_sixThreshold_lt_k (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceSixThreshold <
      (P.withSourceRequirements extra).k := by
  exact (P.withSourceRequirements extra).requirement_lt_k
    (P.sourceSixThreshold_mem_withSourceRequirements extra)

theorem withSourceRequirements_ten_lt_k (extra : Finset ℝ) :
    (P.withSourceRequirements extra).sourceTenThreshold <
      (P.withSourceRequirements extra).k := by
  exact (P.withSourceRequirements extra).requirement_lt_k
    (P.sourceTenThreshold_mem_withSourceRequirements extra)

theorem withSourceRequirements_extra_lt_k {extra : Finset ℝ} {x : ℝ}
    (hx : x ∈ extra) : x < (P.withSourceRequirements extra).k := by
  exact (P.withSourceRequirements extra).requirement_lt_k
    (P.mem_withSourceRequirements_of_mem hx)

theorem withSourceRequirements_radical_prime_bound (extra : Finset ℝ) :
    ((P.withSourceRequirements extra).q : ℝ) ≤
      (P.withSourceRequirements extra).k ^
        (P.withSourceRequirements extra).epsilon := by
  exact (P.withSourceRequirements extra).q_le_k_rpow_epsilon

theorem withSourceRequirements_equationOne_lt_k (extra : Finset ℝ) :
    (P.withSourceRequirements extra).equationOneThreshold <
      (P.withSourceRequirements extra).k :=
  (P.withSourceRequirements extra).equationOneThreshold_lt_k

/-- The actual source parameter used by every downstream definition satisfies
equation (1), the radical-prime constraint, and every supplied finite extra
requirement. -/
theorem exists_parameters_with_admissible_k (extra : Finset ℝ) :
    ∃ Q : VDPLParameters ι,
      Q.old = P.old ∧ Q.newPrime = P.newPrime ∧ Q.Bsrc = P.Bsrc ∧
      Q.equationOneThreshold < Q.k ∧
      Q.sourceDimensionThreshold < Q.k ∧
      Q.sourceSixThreshold < Q.k ∧
      Q.sourceTenThreshold < Q.k ∧
      (∀ x ∈ extra, x < Q.k) ∧
      (Q.q : ℝ) ≤ Q.k ^ Q.epsilon := by
  refine ⟨P.withSourceRequirements extra, rfl, rfl, rfl,
    P.withSourceRequirements_equationOne_lt_k extra,
    P.withSourceRequirements_dimension_lt_k extra,
    P.withSourceRequirements_sixThreshold_lt_k extra,
    P.withSourceRequirements_ten_lt_k extra, ?_,
    P.withSourceRequirements_radical_prime_bound extra⟩
  intro x hx
  exact P.withSourceRequirements_extra_lt_k hx

end VDPLParameters

end

end Erdos240

#print axioms Erdos240.VDPLParameters.exists_parameters_with_admissible_k
