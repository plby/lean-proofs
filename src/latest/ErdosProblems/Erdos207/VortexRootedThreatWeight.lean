/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootedThreatAbsorberBound
import ErdosProblems.Erdos207.VortexIndexedSharpWeight

/-!
# Density-sensitive rooted threat weights along a vortex

The pre-existing rooted-threat code injects a witness into its distinguished
triangle through the fixed pair and its indexed outside family.  W4 supplies
the sharp weight after that distinguished triangle is planted.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Sum of the sharp indexed W4 coefficients over all possible outside
orders. -/
def indexedRootedThreatVortexDensityCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q : ℕ) (B : TripleSystemOn V)
    (c : ℝ≥0) : ℝ≥0 :=
  ∑ j : IndexedThreatOrder q,
    (((j.1 + 1) ^ ell * inducedVortexCoefficient q ell B : ℕ) : ℝ≥0) *
      c ^ (j.1 - 3)

/-- W1 coefficient for a rooted-threat extension after `a` remainder
triangles have already been planted. -/
def indexedRootedThreatVortexExtensionCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q : ℕ) (B : TripleSystemOn V)
    (c : ℝ≥0) (a : ℕ) : ℝ≥0 :=
  ∑ j : IndexedThreatOrder q,
    (((j.1 + 1) ^ ell *
      indexedInducedVortexSpreadCoefficient q ell B W.terminalSize : ℕ) :
        ℝ≥0) * c ^ (j.1 - 3 - a)

/-- Root-uniform coefficient obtained by discarding only the remaining
density powers.  It is finite and independent of the ambient vertex order. -/
def indexedRootedThreatVortexUniformCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  ∑ j : IndexedThreatOrder q,
    (((j.1 + 1) ^ ell *
      indexedInducedVortexSpreadCoefficient q ell B W.terminalSize : ℕ) :
        ℝ≥0)

/-- The empty-root weight of all indexed rooted threats through a fixed
distinct pair.  The sole ambient factor is the number of choices for the
third vertex of the distinguished triangle. -/
theorem extensionWeight_indexedRootedThreat_vortex_empty_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) :
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (vortexTripleWeight W c) ∅ ≤
      (Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexDensityCoefficient W q B c := by
  let p : TripleOn V → ℝ≥0 := vortexTripleWeight W c
  calc
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1) p ∅ =
      ∑ z : IndexedRootedThreatWitness V q B u v,
        if ∅ ⊆ rootedThreatRemainder z.1 then
          setWeight p (rootedThreatRemainder z.1 \ ∅) else 0 := rfl
    _ ≤ ∑ code : IndexedRootedThreatCode V q B u v,
        indexedRootedThreatCodeWeight p ∅ code :=
      indexedRootedThreat_weight_le_code p ∅
    _ = ∑ T : universeTriplesThroughPair u v,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1 ∅) :=
      sum_indexedRootedThreatCodeWeight_eq p ∅
    _ ≤ ∑ _T : universeTriplesThroughPair u v,
        indexedRootedThreatVortexDensityCoefficient W q B c := by
      apply sum_le_sum
      intro T _hT
      unfold indexedRootedThreatVortexDensityCoefficient
      apply sum_le_sum
      intro j _hj
      simpa only [p, insert_empty] using
        (extensionWeight_absorberInduced_vortex_singleton_le_sharp
          (q := q) (j := j.1) W B c (mem_Icc.mp j.2).1
            houter hterminal T.1)
    _ = (Fintype.card (universeTriplesThroughPair u v) : ℝ≥0) *
        indexedRootedThreatVortexDensityCoefficient W q B c := by
      rw [sum_const, card_univ]
      simp only [nsmul_eq_mul]
    _ ≤ (Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexDensityCoefficient W q B c := by
      gcongr
      exact_mod_cast (by
        simpa only [Fintype.card_coe] using
          card_universeTriplesThroughPair_le V huv)

/-- Density-sensitive W1 bound above an arbitrary planted remainder root.
The designated missing triangle contributes the only additional ambient
choice. -/
theorem extensionWeight_indexedRootedThreat_vortex_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (vortexTripleWeight W c) A ≤
      (Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexExtensionCoefficient W q B c A.card := by
  let p : TripleOn V → ℝ≥0 := vortexTripleWeight W c
  calc
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1) p A =
      ∑ z : IndexedRootedThreatWitness V q B u v,
        if A ⊆ rootedThreatRemainder z.1 then
          setWeight p (rootedThreatRemainder z.1 \ A) else 0 := rfl
    _ ≤ ∑ code : IndexedRootedThreatCode V q B u v,
        indexedRootedThreatCodeWeight p A code :=
      indexedRootedThreat_weight_le_code p A
    _ = ∑ T : universeTriplesThroughPair u v,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1 A) :=
      sum_indexedRootedThreatCodeWeight_eq p A
    _ ≤ ∑ _T : universeTriplesThroughPair u v,
        indexedRootedThreatVortexExtensionCoefficient W q B c A.card := by
      apply sum_le_sum
      intro T _hT
      unfold indexedRootedThreatVortexExtensionCoefficient
      apply sum_le_sum
      intro j _hj
      by_cases hrootcard : (insert T.1 A).card ≤ j.1 - 2
      · have hsharp := extensionWeight_absorberInduced_vortex_nonempty_le_sharp
          (q := q) (j := j.1) W B c (mem_Icc.mp j.2).1 houter
            hterminal (insert T.1 A) (by simp) hrootcard
        apply hsharp.trans
        have hExp : j.1 - 3 - A.card ≤
            j.1 - 2 - (insert T.1 A).card := by
          have hinsert := card_insert_le T.1 A
          omega
        simpa only [mul_comm] using
          mul_le_mul_left (pow_le_pow_right_of_le_one' hc hExp)
            ((((j.1 + 1) ^ ell *
              indexedInducedVortexSpreadCoefficient q ell B W.terminalSize :
                ℕ) : ℝ≥0))
      · have hzero :
            extensionWeight
                (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
                p (insert T.1 A) = 0 := by
          unfold extensionWeight
          apply sum_eq_zero
          intro S _hS
          rw [if_neg]
          intro hsub
          apply hrootcard
          calc
            (insert T.1 A).card ≤ S.1.card := card_le_card hsub
            _ = j.1 - 2 :=
              (mem_absorberInducedConfigurationsOn_iff.mp S.2).1
        rw [hzero]
        exact bot_le
    _ = (Fintype.card (universeTriplesThroughPair u v) : ℝ≥0) *
        indexedRootedThreatVortexExtensionCoefficient W q B c A.card := by
      rw [sum_const, card_univ]
      simp only [nsmul_eq_mul]
    _ ≤ (Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexExtensionCoefficient W q B c A.card := by
      gcongr
      exact_mod_cast (by
        simpa only [Fintype.card_coe] using
          card_universeTriplesThroughPair_le V huv)

/-- Uniform all-root extension bound for the indexed rooted-threat family.
The sharper root-cardinality dependence remains available in the preceding
theorem; this corollary is the interface required by the generic moment
lemma. -/
theorem indexedRootedThreatRemainder_hasExtensionBound_vortex
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) :
    HasExtensionBound
      (fun z : IndexedRootedThreatWitness V q B u v ↦
        rootedThreatRemainder z.1)
      (vortexTripleWeight W c)
      ((Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexUniformCoefficient W q B) := by
  intro A
  apply (extensionWeight_indexedRootedThreat_vortex_le_sharp
    W B c hc houter hterminal huv A).trans
  gcongr
  unfold indexedRootedThreatVortexExtensionCoefficient
  unfold indexedRootedThreatVortexUniformCoefficient
  apply sum_le_sum
  intro j hj
  have hpow : c ^ (j.1 - 3 - A.card) ≤ (1 : ℝ≥0) :=
    pow_le_one₀ (by positivity) hc
  simpa only [mul_one, one_mul, mul_comm] using
    mul_le_mul_left hpow
      ((((j.1 + 1) ^ ell *
        indexedInducedVortexSpreadCoefficient q ell B W.terminalSize : ℕ) :
          ℝ≥0))

/-- One-power-shifted coefficient for vortex multipliers at least one. -/
def indexedRootedThreatVortexLargeCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q : ℕ) (B : TripleSystemOn V)
    (c : ℝ≥0) (a : ℕ) : ℝ≥0 :=
  ∑ j : IndexedThreatOrder q,
    (((j.1 + 1) ^ ell *
      indexedInducedVortexSpreadCoefficient q ell B W.terminalSize : ℕ) :
        ℝ≥0) * c ^ (j.1 - 2 - a)

/-- Uniform all-root indexed extension bound for a multiplier at least one.
The shifted exponent covers the possible overlap between the designated
missing triangle and the planted root. -/
theorem indexedRootedThreatRemainder_hasExtensionBound_vortex_of_one_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hc : 1 ≤ c)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) :
    HasExtensionBound
      (fun z : IndexedRootedThreatWitness V q B u v ↦
        rootedThreatRemainder z.1)
      (vortexTripleWeight W c)
      ((Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexLargeCoefficient W q B c 0) := by
  intro A
  let p : TripleOn V → ℝ≥0 := vortexTripleWeight W c
  calc
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1) p A =
      ∑ z : IndexedRootedThreatWitness V q B u v,
        if A ⊆ rootedThreatRemainder z.1 then
          setWeight p (rootedThreatRemainder z.1 \ A) else 0 := rfl
    _ ≤ ∑ code : IndexedRootedThreatCode V q B u v,
        indexedRootedThreatCodeWeight p A code :=
      indexedRootedThreat_weight_le_code p A
    _ = ∑ T : universeTriplesThroughPair u v,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1 A) :=
      sum_indexedRootedThreatCodeWeight_eq p A
    _ ≤ ∑ _T : universeTriplesThroughPair u v,
        indexedRootedThreatVortexLargeCoefficient W q B c A.card := by
      apply sum_le_sum
      intro T _hT
      unfold indexedRootedThreatVortexLargeCoefficient
      apply sum_le_sum
      intro j _hj
      by_cases hrootcard : (insert T.1 A).card ≤ j.1 - 2
      · have hsharp := extensionWeight_absorberInduced_vortex_nonempty_le_sharp
          (q := q) (j := j.1) W B c (mem_Icc.mp j.2).1 houter
            hterminal (insert T.1 A) (by simp) hrootcard
        apply hsharp.trans
        have hExp : j.1 - 2 - (insert T.1 A).card ≤
            j.1 - 2 - A.card := by
          have hinsert : A.card ≤ (insert T.1 A).card :=
            card_le_card (subset_insert _ _)
          omega
        simpa only [mul_comm] using
          mul_le_mul_left (pow_le_pow_right₀ hc hExp)
            ((((j.1 + 1) ^ ell *
              indexedInducedVortexSpreadCoefficient q ell B W.terminalSize :
                ℕ) : ℝ≥0))
      · have hzero :
            extensionWeight
                (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
                p (insert T.1 A) = 0 := by
          unfold extensionWeight
          apply sum_eq_zero
          intro S _hS
          rw [if_neg]
          intro hsub
          apply hrootcard
          calc
            (insert T.1 A).card ≤ S.1.card := card_le_card hsub
            _ = j.1 - 2 :=
              (mem_absorberInducedConfigurationsOn_iff.mp S.2).1
        rw [hzero]
        exact bot_le
    _ = (Fintype.card (universeTriplesThroughPair u v) : ℝ≥0) *
        indexedRootedThreatVortexLargeCoefficient W q B c A.card := by
      rw [sum_const, card_univ]
      simp only [nsmul_eq_mul]
    _ ≤ (Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexLargeCoefficient W q B c A.card := by
      gcongr
      exact_mod_cast (by
        simpa only [Fintype.card_coe] using
          card_universeTriplesThroughPair_le V huv)
    _ ≤ (Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexLargeCoefficient W q B c 0 := by
      gcongr
      unfold indexedRootedThreatVortexLargeCoefficient
      apply sum_le_sum
      intro j _hj
      have hExp : j.1 - 2 - A.card ≤ j.1 - 2 - 0 := by omega
      simpa only [mul_comm] using
        mul_le_mul_left (pow_le_pow_right₀ hc hExp)
          ((((j.1 + 1) ^ ell *
            indexedInducedVortexSpreadCoefficient
              q ell B W.terminalSize : ℕ) : ℝ≥0))

end

end Erdos207
