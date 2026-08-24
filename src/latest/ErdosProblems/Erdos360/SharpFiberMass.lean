import ErdosProblems.Erdos360.AffineConnector

namespace Erdos360

open scoped Pointwise BigOperators

attribute [local instance] Classical.propDecidable

/-!
# The sharp fibre-excess endpoint

Balasubramanian--Pandey state the final endpoint of their Theorem 5 with a
strict inequality.  Their Hall count proves the non-strict inequality, and
the latter is sharp: a full arithmetic progression of full subgroup fibres
has equality.  This file records the exact selection-level statement behind
the valid endpoint and checks that the non-strict form is already sufficient
for the `52 / 25` progression-mass estimate used by CFP.
-/

/-- The exact last counting step in the desirable/almost-desirable argument.
The pairs in `P` have distinct first-coordinate sums.  Those in `Full`
contribute at least `Hcard` points each, while the remaining pairs contribute
the entire mass of `X`.  Consequently every `M` full pairs pay for
`M * Hcard` points of excess.

This formulation cleanly separates the fibrewise counting from the finite
ordered-support lemma which constructs `P` and `Full`. -/
theorem sharp_fiber_excess_le_of_pairSelection
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (P Full : Finset (ℕ × ℕ)) (M Hcard : ℕ)
    (hFullSub : Full ⊆ P)
    (hP : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X)
    (hinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P)
    (hFullCard : M ≤ Full.card)
    (hfull : ∀ p ∈ Full, Hcard ≤
      (coordinateFiber X p.1 + coordinateFiber X p.2).card)
    (hrest : X.card ≤
      ∑ p ∈ P \ Full,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card) :
    M * Hcard ≤ (X + X).card - X.card := by
  classical
  let weight : ℕ × ℕ → ℕ := fun p ↦
    (coordinateFiber X p.1 + coordinateFiber X p.2).card
  have hfullSum : Full.card * Hcard ≤ ∑ p ∈ Full, weight p := by
    calc
      Full.card * Hcard = ∑ _p ∈ Full, Hcard := by simp
      _ ≤ ∑ p ∈ Full, weight p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hfull p hp
  have hMfull : M * Hcard ≤ ∑ p ∈ Full, weight p :=
    (Nat.mul_le_mul_right Hcard hFullCard).trans hfullSum
  have hsplit :
      (∑ p ∈ P \ Full, weight p) + ∑ p ∈ Full, weight p =
        ∑ p ∈ P, weight p :=
    Finset.sum_sdiff hFullSub
  have hcount : M * Hcard + X.card ≤ ∑ p ∈ P, weight p := by
    rw [← hsplit]
    exact Nat.add_le_add hMfull hrest |>.trans_eq (add_comm _ _)
  have hsum : (∑ p ∈ P, weight p) ≤ (X + X).card := by
    exact sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hP hinj
  omega

/-- The `51 / 25` small-doubling estimate only needs the valid non-strict
fibre-excess endpoint.  Strictness was not used in the original arithmetic
proof: six occupied layers give the endpoint factor `6 / 5`, while the
excess is at most `26 / 25` of the original mass. -/
lemma progression_mass_of_sharp_fiber_excess_le
    {Xcard Xsum M Hcard : ℕ}
    (hsix : 6 ≤ M + 1)
    (hXle : Xcard ≤ Xsum)
    (hsmall : 25 * Xsum ≤ 51 * Xcard)
    (hsharp : M * Hcard ≤ Xsum - Xcard) :
    25 * ((M + 1) * Hcard) ≤ 52 * Xcard := by
  have hexcess : 25 * (Xsum - Xcard) ≤ 26 * Xcard := by
    omega
  have hMfive : 5 ≤ M := by omega
  have hendpoint : 5 * ((M + 1) * Hcard) ≤ 6 * (M * Hcard) := by
    nlinarith
  calc
    25 * ((M + 1) * Hcard) =
        5 * (5 * ((M + 1) * Hcard)) := by ring
    _ ≤ 5 * (6 * (M * Hcard)) := Nat.mul_le_mul_left 5 hendpoint
    _ ≤ 30 * (Xsum - Xcard) := by
      nlinarith
    _ ≤ 52 * Xcard := by
      nlinarith

/-- The quotient--remainder progression bridge with the corrected non-strict
endpoint.  This is the exact form consumed by the CFP `51 / 25` slow-scale
argument. -/
theorem quotientRemainder_sharpFiber_le_to_DF_progression
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (D : Finset (ZMod (m * d))) (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m d D)).Nonempty)
    (hAcard : 6 ≤
      (firstCoordinateSet (zmodQuotRemImage m d D)).card)
    (H : AddSubgroup (ZMod d)) (u v : ZMod d)
    (haffine : ∀ a ∈ firstCoordinateSet (zmodQuotRemImage m d D),
      ∀ y ∈ coordinateFiber (zmodQuotRemImage m d D) a,
        y - (a • u + v) ∈ H)
    (hsmall : 25 *
        (zmodQuotRemImage m d D + zmodQuotRemImage m d D).card ≤
      51 * (zmodQuotRemImage m d D).card)
    (hsharp :
      (firstCoordinateSet (zmodQuotRemImage m d D)).max' hA *
          Nat.card H ≤
        (zmodQuotRemImage m d D + zmodQuotRemImage m d D).card -
          (zmodQuotRemImage m d D).card) :
    ∃ K : AddSubgroup (ZMod (m * d)), ∃ a step : ZMod (m * d),
      ∃ L : ℕ,
        D ⊆ cyclicCosetProgression K a step L ∧
        25 * (L * Nat.card K) ≤ 52 * D.card := by
  classical
  let X := zmodQuotRemImage m d D
  let A := firstCoordinateSet X
  let L := A.max' hA + 1
  let K := H.map (zmodQuotientEmbedding m d)
  have hrange : A ⊆ Finset.range L := by
    intro r hr
    exact Finset.mem_range.mpr (by
      have := A.le_max' r hr
      omega)
  have hDprog : D ⊆ cyclicCosetProgression K
      (zmodQuotientEmbedding m d v)
      ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u) L :=
    commonFiberCosets_pullback_cyclicCosetProgression D hrange haffine
  have hAmax : A.card ≤ A.max' hA + 1 := by
    have hsub : A ⊆ Finset.range (A.max' hA + 1) := by
      intro r hr
      exact Finset.mem_range.mpr (by
        have := A.le_max' r hr
        omega)
    simpa using Finset.card_le_card hsub
  have hsix : 6 ≤ A.max' hA + 1 := hAcard.trans hAmax
  have hXne : X.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨y, hy⟩ := mem_firstCoordinateSet.mp ha
    exact ⟨(a, y), hy⟩
  have hXle : X.card ≤ (X + X).card :=
    Finset.card_le_card_add_right hXne
  have hmassX : 25 * (L * Nat.card H) ≤ 52 * X.card := by
    exact progression_mass_of_sharp_fiber_excess_le hsix hXle
      (by simpa [X] using hsmall) (by simpa [X, A] using hsharp)
  have hcardX : X.card = D.card := zmodQuotRemImage_card hm D
  have hcardK : Nat.card K = Nat.card H :=
    natCard_map_zmodQuotientEmbedding hm H
  refine ⟨K, zmodQuotientEmbedding m d v,
    (1 : ZMod (m * d)) + zmodQuotientEmbedding m d u,
    L, hDprog, ?_⟩
  rw [hcardK, ← hcardX]
  exact hmassX

/-- The numerical data of the full-progression equality example.  They
satisfy the six-layer and strict `5 / 2` hypotheses, but the sharp excess is
an equality.  The geometric realization is
`X = {(0,0),...,(5,0)} ⊆ ℕ × ZMod d` with `H = ⊥`. -/
lemma sharp_fiber_excess_strict_endpoint_arithmetic_counterexample :
    ∃ Xcard Xsum M Hcard : ℕ,
      6 ≤ M + 1 ∧
      2 * Xsum < 5 * Xcard ∧
      M * Hcard = Xsum - Xcard := by
  exact ⟨6, 11, 5, 1, by omega⟩

end Erdos360

#print axioms Erdos360.sharp_fiber_excess_le_of_pairSelection
#print axioms Erdos360.progression_mass_of_sharp_fiber_excess_le
#print axioms Erdos360.quotientRemainder_sharpFiber_le_to_DF_progression
#print axioms Erdos360.sharp_fiber_excess_strict_endpoint_arithmetic_counterexample
