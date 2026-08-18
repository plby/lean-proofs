/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4VolumeIteration
import ErdosProblems.Erdos186.CFP.Bilu.Section94ReducedCoordinates

/-!
# Bilu Section 4: uniform selection and the bounded-cardinality branch

The analytic construction preceding Lemma 4.5 produces a nonempty class of
admissible realizations.  For sets of bounded cardinality one fixed member
already has the required linear volume bound.  Above that cardinality,
Lemma 4.5 gives the polynomial volume-decay step used by the infimum
argument in `Section4VolumeIteration`.

This file combines those two branches and packages the result directly at
the source-facing `ReducedOuterExistenceStatement` boundary.  The package
contains no extra conclusion: its `realize` field is precisely the final
conversion of a selected admissible body into the already stable
`ReducedOuterRealization` structure.
-/

namespace Erdos186.CFP.Bilu.Section4UniformVolumeDecay

open Set
open CFP.BiluFreiman
open Section4VolumeIteration
open Section94SortedContainerAssembly
open Section94ReducedCoordinates

noncomputable section

set_option autoImplicit false

/-! ## The order-theoretic selection on an indexed class -/

/-- Indexed form of `exists_le_of_pow_decay`.  It avoids exposing the set
of attained volumes to source-facing callers. -/
theorem exists_candidate_le_of_pow_decay
    {X : Type*} (volume : X → ℝ)
    (hpos : ∀ x, 0 < volume x)
    (initial : X) (q : ℕ) (hq : 0 < q)
    (bound : ℝ) (hbound : 0 < bound)
    (hstep : ∀ x, bound < volume x →
      ∃ y, (2 * volume y) ^ q ≤
        bound * volume x ^ (q - 1)) :
    ∃ x, volume x ≤ bound := by
  let volumes : Set ℝ := Set.range volume
  have hne : volumes.Nonempty := ⟨volume initial, ⟨initial, rfl⟩⟩
  have hpositive : ∀ v ∈ volumes, 0 < v := by
    rintro v ⟨x, rfl⟩
    exact hpos x
  have hdecay : ∀ v ∈ volumes, bound < v →
      ∃ w ∈ volumes, (2 * w) ^ q ≤
        bound * v ^ (q - 1) := by
    rintro v ⟨x, rfl⟩ hx
    obtain ⟨y, hy⟩ := hstep x hx
    exact ⟨volume y, ⟨y, rfl⟩, hy⟩
  obtain ⟨v, ⟨x, rfl⟩, hx⟩ :=
    exists_le_of_pow_decay q hq volumes hne hpositive bound hbound hdecay
  exact ⟨x, hx⟩

/-- The exact two-branch selection used at the end of Section 4.  On the
bounded-cardinality branch the distinguished initial realization is used;
on the complementary branch the uniform power-decay iteration is run. -/
theorem exists_candidate_le_of_bounded_or_pow_decay
    {X : Type*} (volume : X → ℝ)
    (hpos : ∀ x, 0 < volume x)
    (initial : X) (q threshold cardinality : ℕ) (hq : 0 < q)
    (bound : ℝ) (hbound : 0 < bound)
    (hbounded : cardinality ≤ threshold → volume initial ≤ bound)
    (hstep : threshold < cardinality →
      ∀ x, bound < volume x →
        ∃ y, (2 * volume y) ^ q ≤
          bound * volume x ^ (q - 1)) :
    ∃ x, volume x ≤ bound := by
  by_cases hcard : cardinality ≤ threshold
  · exact ⟨initial, hbounded hcard⟩
  · exact exists_candidate_le_of_pow_decay volume hpos initial q hq
      bound hbound (hstep (Nat.lt_of_not_ge hcard))

/-! ## Uniform package at the reduced-realization boundary -/

/-- All data used by the final Section 4 selection for fixed source
parameters.  `Candidate A` is the class of admissible bodies/presentations
for `A`; quotient and affine-span repairs are reflected by closure of this
class under `decay`.

The volume is real because this is the scale on which Lemma 4.5 and the
infimum argument operate.  `realize` performs the already-established
Mahler/container conversion after the chosen volume is at most the uniform
linear bound. -/
structure UniformReducedOuterDecayPackage
    (s d : ℕ) (delta : ℝ) where
  volumeConstant : ℕ
  rankBound : ℕ
  cardinalityThreshold : ℕ
  exponent : ℕ
  volumeConstant_pos : 0 < volumeConstant
  exponent_pos : 0 < exponent
  Candidate : Finset ℤ → Type*
  volume : ∀ {A : Finset ℤ}, Candidate A → ℝ
  volume_pos : ∀ {A : Finset ℤ} (x : Candidate A), 0 < volume x
  initial : ∀ (A : Finset ℤ), A.Nonempty → Candidate A
  boundedCardinality : ∀ (A : Finset ℤ) (hA : A.Nonempty),
    A.card ≤ cardinalityThreshold →
      volume (initial A hA) ≤
        ((volumeConstant * A.card : ℕ) : ℝ)
  decay : ∀ (A : Finset ℤ) (hA : A.Nonempty),
    ((twoA A).card : ℝ) ≤
        Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card →
    cardinalityThreshold < A.card →
    ∀ x : Candidate A,
      ((volumeConstant * A.card : ℕ) : ℝ) < volume x →
      ∃ y : Candidate A,
        (2 * volume y) ^ exponent ≤
          ((volumeConstant * A.card : ℕ) : ℝ) *
            volume x ^ (exponent - 1)
  realize : ∀ {A : Finset ℤ} (x : Candidate A),
    volume x ≤ ((volumeConstant * A.card : ℕ) : ℝ) →
      Nonempty (ReducedOuterRealization
        s volumeConstant rankBound A)

namespace UniformReducedOuterDecayPackage

/-- Select the terminal realization for one source set. -/
theorem exists_reducedOuterRealization
    {s d : ℕ} {delta : ℝ}
    (P : UniformReducedOuterDecayPackage s d delta)
    (A : Finset ℤ) (hA : A.Nonempty)
    (hdouble : ((twoA A).card : ℝ) ≤
      Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card) :
    Nonempty (ReducedOuterRealization
      s P.volumeConstant P.rankBound A) := by
  let bound : ℝ := ((P.volumeConstant * A.card : ℕ) : ℝ)
  have hbound : 0 < bound := by
    dsimp only [bound]
    exact_mod_cast Nat.mul_pos P.volumeConstant_pos hA.card_pos
  obtain ⟨x, hx⟩ := exists_candidate_le_of_bounded_or_pow_decay
    (@P.volume A) (@P.volume_pos A) (P.initial A hA)
    P.exponent P.cardinalityThreshold A.card P.exponent_pos
    bound hbound
    (by
      intro hcard
      exact P.boundedCardinality A hA hcard)
    (by
      intro hcard x hx
      exact P.decay A hA hdouble hcard x hx)
  exact P.realize x hx

end UniformReducedOuterDecayPackage

/-- A uniform family of Section 4 packages proves the exact remaining
source-facing reduced-body existence statement. -/
theorem reducedOuterExistenceStatement_of_uniformVolumeDecay
    (hpackage : ∀ s d : ℕ, 0 < s → 0 < d →
      ∀ delta : ℝ, 0 < delta →
        Nonempty (UniformReducedOuterDecayPackage s d delta)) :
    ReducedOuterExistenceStatement := by
  intro s d hs hd delta hdelta
  obtain ⟨P⟩ := hpackage s d hs hd delta hdelta
  refine ⟨P.volumeConstant, P.rankBound, P.volumeConstant_pos, ?_⟩
  intro A hA hdouble
  exact P.exists_reducedOuterRealization A hA hdouble

end

end Erdos186.CFP.Bilu.Section4UniformVolumeDecay

#print axioms
  Erdos186.CFP.Bilu.Section4UniformVolumeDecay.exists_candidate_le_of_bounded_or_pow_decay
#print axioms
  Erdos186.CFP.Bilu.Section4UniformVolumeDecay.UniformReducedOuterDecayPackage.exists_reducedOuterRealization
#print axioms
  Erdos186.CFP.Bilu.Section4UniformVolumeDecay.reducedOuterExistenceStatement_of_uniformVolumeDecay
