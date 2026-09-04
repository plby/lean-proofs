/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos185.DHJ.Cube
import ErdosProblems.Erdos185.DHJ.Density
import ErdosProblems.Erdos185.Corollary

/-!
# The density-increment endgame for ternary density Hales--Jewett

This file isolates the formal iteration argument from the combinatorial work
which produces one density increment.  The increment is required to be
uniform over all sets whose current density is at least a fixed positive base
density.  Iterating inside pullbacks then either finds a line, or raises the
density by the same positive amount at every step.  The latter alternative is
eventually incompatible with the elementary upper bound `densityIn <= 1`.

The exact-dimension conclusion is promoted to all larger dimensions by fixing
a suffix whose section is at least as dense as the original set.  This final
fibre argument is recorded explicitly because the proposition used by Erdős
Problem 185 has an eventual-dimension formulation.
-/

namespace Erdos185.DHJ

open scoped BigOperators

noncomputable section

/-- The abstract combinatorial input needed by the density-increment
endgame.  For a fixed positive base density `delta`, the gain `gamma` is
independent of both the requested target dimension and the current set.

The lower bound on the current set is always the original `delta`, while the
conclusion increases its *actual* density.  This is the uniformity which makes
the principle legitimately iterable. -/
def TernaryIncrementPrinciple : Prop :=
  forall delta : Real, 0 < delta ->
    exists gamma : Real, 0 < gamma /\
      forall d : Nat, exists n : Nat,
        forall A : Finset (Word 3 n), delta <= density A ->
          HasLine A \/
            exists U : Combinatorics.Subspace (Fin d) (Fin 3) (Fin n),
              density A + gamma <= densityIn U A

/-- `densityIn` is the ordinary density of the pullback to the parameter
cube. -/
theorem densityIn_eq_density_pullback {eta alpha iota : Type*}
    [Fintype eta] [Fintype alpha] [DecidableEq eta]
    (U : Combinatorics.Subspace eta alpha iota)
    (A : Finset (iota -> alpha)) :
    densityIn U A = density (pullbackFinset U A) := by
  simp [densityIn, density, Nat.card_eq_fintype_card]

/-- Starting from one uniform increment step, build dimensions backwards so
that `r + 1` nested applications either find a line or produce a prescribed
`d`-dimensional subspace on which the density has risen by
`(r + 1) * gamma`.

The backwards choice of dimensions is important: an outer application first
produces a parameter cube whose dimension is exactly the source dimension
chosen for the remaining recursive applications. -/
theorem iterated_increment
    {delta gamma : Real} (hgamma : 0 < gamma)
    (hstep : forall d : Nat, exists n : Nat,
      forall A : Finset (Word 3 n), delta <= density A ->
        HasLine A \/
          exists U : Combinatorics.Subspace (Fin d) (Fin 3) (Fin n),
            density A + gamma <= densityIn U A)
    (d r : Nat) :
    exists n : Nat, forall A : Finset (Word 3 n), delta <= density A ->
      HasLine A \/
        exists U : Combinatorics.Subspace (Fin d) (Fin 3) (Fin n),
          density A + ((r + 1 : Nat) : Real) * gamma <= densityIn U A := by
  induction r with
  | zero =>
      obtain ⟨n, hn⟩ := hstep d
      refine ⟨n, fun A hA => ?_⟩
      simpa using hn A hA
  | succ r ihr =>
      obtain ⟨m, hm⟩ := ihr
      obtain ⟨n, hn⟩ := hstep m
      refine ⟨n, fun A hA => ?_⟩
      rcases hn A hA with hline | ⟨U, hU⟩
      . exact Or.inl hline
      . have hU' : density A + gamma <= density (pullbackFinset U A) := by
          simpa only [densityIn_eq_density_pullback] using hU
        have hpull : delta <= density (pullbackFinset U A) := by
          exact hA.trans ((le_add_of_nonneg_right hgamma.le).trans hU')
        rcases hm (pullbackFinset U A) hpull with hline | ⟨V, hV⟩
        . exact Or.inl (HasLine.of_pullback U hline)
        . refine Or.inr ⟨U.comp V, ?_⟩
          rw [densityIn_comp]
          have hchain :
              density A + gamma + ((r + 1 : Nat) : Real) * gamma <=
                densityIn V (pullbackFinset U A) := by
            nlinarith
          push_cast at hchain ⊢
          nlinarith

/-- A positive uniform increment principle already gives a line in one exact
dimension for every positive density. -/
theorem exists_exact_dimension_hasLine_of_increment
    (hinc : TernaryIncrementPrinciple) (delta : Real) (hdelta : 0 < delta) :
    exists N : Nat, forall A : Finset (Word 3 N),
      delta <= density A -> HasLine A := by
  obtain ⟨gamma, hgamma, hstep⟩ := hinc delta hdelta
  obtain ⟨r, hr⟩ := exists_nat_gt ((1 - delta) / gamma)
  have hr' : (1 - delta) / gamma < ((r + 1 : Nat) : Real) := by
    exact hr.trans_le (by exact_mod_cast Nat.le_succ r)
  have hover : 1 < delta + ((r + 1 : Nat) : Real) * gamma := by
    have := (div_lt_iff₀ hgamma).mp hr'
    nlinarith
  obtain ⟨N, hN⟩ := iterated_increment hgamma hstep 1 r
  refine ⟨N, fun A hA => ?_⟩
  rcases hN A hA with hline | ⟨U, hU⟩
  . exact hline
  . exfalso
    have hupper := densityIn_le_one U A
    have hlower :
        delta + ((r + 1 : Nat) : Real) * gamma <= densityIn U A := by
      nlinarith
    linarith

section SuffixSections

/-- Reindex the ambient coordinates of a combinatorial line by an
equivalence. -/
def reindexLine {alpha iota kappa : Type*}
    (l : Combinatorics.Line alpha iota) (e : iota ≃ kappa) :
    Combinatorics.Line alpha kappa where
  idxFun j := l.idxFun (e.symm j)
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simp [hi]⟩

@[simp] theorem reindexLine_apply {alpha iota kappa : Type*}
    (l : Combinatorics.Line alpha iota) (e : iota ≃ kappa)
    (a : alpha) (j : kappa) :
    reindexLine l e a j = l a (e.symm j) := by
  rfl

/-- Swap the two coordinates of a finset in a product. -/
noncomputable def swapFinset {X Y : Type*} (A : Finset (X × Y)) :
    Finset (Y × X) :=
  A.map (Equiv.prodComm X Y).toEmbedding

@[simp] theorem mem_swapFinset {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset (X × Y)) (y : Y) (x : X) :
    (y, x) ∈ swapFinset A <-> (x, y) ∈ A := by
  simp [swapFinset]

@[simp] theorem card_swapFinset {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset (X × Y)) : (swapFinset A).card = A.card := by
  simp [swapFinset]

/-- The section obtained by fixing the final `r` coordinates of a word. -/
noncomputable def suffixSection {k m r : Nat}
    (A : Finset (Word k (m + r))) (y : Word k r) : Finset (Word k m) :=
  fiber (swapFinset (splitFinset A)) y

@[simp] theorem mem_suffixSection {k m r : Nat}
    (A : Finset (Word k (m + r))) (y : Word k r) (x : Word k m) :
    x ∈ suffixSection A y <-> (wordSplitEquiv k m r).symm (x, y) ∈ A := by
  simp [suffixSection]

/-- Density is the average of the densities of the sections obtained by
fixing the final block. -/
theorem density_eq_average_suffixSection {k m r : Nat}
    (A : Finset (Word k (m + r))) :
    density A = average fun y : Word k r => density (suffixSection A y) := by
  let B : Finset (Word k r × Word k m) := swapFinset (splitFinset A)
  have hB : density B = density A := by
    dsimp [B]
    rw [card_swapFinset, card_splitFinset, Fintype.card_prod]
    simp [Word, pow_add, mul_comm]
  rw [← hB, density_eq_average_fiber]
  rfl

/-- Some suffix section is at least as dense as the whole set. -/
theorem exists_suffixSection_density_ge {k m r : Nat} (hk : 0 < k)
    (A : Finset (Word k (m + r))) :
    exists y : Word k r, density A <= density (suffixSection A y) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [density_eq_average_suffixSection]
  exact exists_average_le _

/-- Append a fixed suffix to every point of a line, then identify the sum of
the two coordinate blocks with `Fin (m + r)`. -/
def lineWithFixedSuffix {k m r : Nat}
    (l : Combinatorics.Line (Fin k) (Fin m)) (y : Word k r) :
    Combinatorics.Line (Fin k) (Fin (m + r)) :=
  reindexLine (l.horizontal y) finSumFinEquiv

@[simp] theorem lineWithFixedSuffix_apply {k m r : Nat}
    (l : Combinatorics.Line (Fin k) (Fin m)) (y : Word k r) (a : Fin k) :
    lineWithFixedSuffix l y a =
      (wordSplitEquiv k m r).symm (l a, y) := by
  apply (wordSplitEquiv k m r).injective
  apply Prod.ext
  . funext i
    simp [lineWithFixedSuffix, reindexLine, Combinatorics.Line.apply_def]
    cases h : finSumFinEquiv.symm (Fin.castAdd r i) <;> rfl
  . funext i
    simp [lineWithFixedSuffix, reindexLine, Combinatorics.Line.apply_def]
    cases h : finSumFinEquiv.symm (Fin.natAdd m i) <;> rfl

end SuffixSections

/-- A line theorem in one exact dimension extends to every larger dimension
by taking a dense suffix section and appending that fixed suffix to the line
found in the section. -/
theorem hasLine_in_larger_dimensions
    (delta : Real) {N : Nat}
    (hN : forall A : Finset (Word 3 N), delta <= density A -> HasLine A) :
    forall n : Nat, N <= n -> forall A : Finset (Word 3 n),
      delta <= density A -> HasLine A := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro A hA
  obtain ⟨y, hy⟩ := exists_suffixSection_density_ge (k := 3) (m := N)
    (r := r) (by norm_num) A
  obtain ⟨l, hl⟩ := hN (suffixSection A y) (hA.trans hy)
  refine ⟨lineWithFixedSuffix l y, fun a => ?_⟩
  rw [lineWithFixedSuffix_apply]
  exact (mem_suffixSection A y (l a)).1 (hl a)

/-- The abstract increment principle implies the exact eventual-dimension
ternary density Hales--Jewett proposition used by the geometric corollary. -/
theorem densityHalesJewettThree_of_increment
    (hinc : TernaryIncrementPrinciple) : Erdos185.DensityHalesJewettThree := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_exact_dimension_hasLine_of_increment hinc delta hdelta
  refine ⟨N, fun n hn A hcard => ?_⟩
  have hdensity : delta <= density A := by
    rw [density, le_div_iff₀ (by positivity)]
    simpa [Word] using hcard
  obtain ⟨l, hl⟩ := hasLine_in_larger_dimensions delta hN n hn A hdensity
  exact ⟨l, by rintro _ ⟨a, rfl⟩; exact hl a⟩

end

end Erdos185.DHJ
