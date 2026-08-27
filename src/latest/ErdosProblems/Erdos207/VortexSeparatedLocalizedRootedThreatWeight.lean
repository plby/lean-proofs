/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SeparatedLocalizedRootedThreat
import ErdosProblems.Erdos207.VortexAbsorberSingletonCount

/-!
# Sharp separated rooted-threat weights

The empty remainder is controlled by the six padded-root obstructions.  A
nonempty remainder has indexed outside order at least four, so the sharp WS4
estimate from KSSS Lemma 7.2 applies without the exceptional `j = 3` term.
-/

namespace Erdos207

open Finset
open scoped BigOperators Classical NNReal

noncomputable section

/-- Indexed outside orders whose rooted remainder can be nonempty. -/
abbrev NonemptyRootedThreatOrder (q : ℕ) :=
  {j : IndexedThreatOrder q // 4 ≤ j.1}

/-- A localized injective code restricted to nonempty rooted remainders. -/
abbrev LocalizedNonemptyIndexedRootedThreatCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V) (U : Finset V) :=
  Σ T : LocalizedUniverseTriplesThroughPair V u v U,
    Σ j : NonemptyRootedThreatOrder q,
      {S : TripleSystemOn V //
        S ∈ absorberInducedConfigurationsOn q j.1.1 B}

lemma localizedNonemptyRootedThreat_order_four
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (z : LocalizedNonemptyRootedThreatWitness V q B u v U) :
    4 ≤ z.1.1.1.1.card + 2 := by
  have hpos : 0 < (localizedRootedThreatRemainder z.1).card :=
    card_pos.mpr (nonempty_iff_ne_empty.mpr z.2)
  have herase : (localizedRootedThreatRemainder z.1).card + 1 =
      z.1.1.1.1.card := by
    exact card_erase_add_one z.1.1.2.2.1
  omega

/-- The restricted code of a nonempty localized rooted witness. -/
def localizedNonemptyIndexedRootedThreatCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (z : LocalizedNonemptyRootedThreatWitness V q B u v U) :
    LocalizedNonemptyIndexedRootedThreatCode V q B u v U :=
  let zi : IndexedRootedThreatWitness V q B u v :=
    ⟨z.1.1, localizedRootedThreat_isIndexed z.1⟩
  ⟨⟨⟨z.1.1.1.2, mem_universeTriplesThroughPair_iff.mpr
      ⟨z.1.1.2.2.2.1, z.1.1.2.2.2.2⟩⟩, z.1.2⟩,
    ⟨⟨⟨z.1.1.1.1.card + 2, indexedRootedThreat_order_mem zi⟩,
        localizedNonemptyRootedThreat_order_four z⟩,
      ⟨z.1.1.1.1, zi.2⟩⟩⟩

lemma localizedNonemptyIndexedRootedThreatCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V} :
    Function.Injective
      (localizedNonemptyIndexedRootedThreatCode :
        LocalizedNonemptyRootedThreatWitness V q B u v U →
          LocalizedNonemptyIndexedRootedThreatCode V q B u v U) := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun c ↦ c.2.2.1) hzw
  · exact congrArg (fun c ↦ c.1.1.1) hzw

/-- Weight of one restricted code word above the designated singleton. -/
def localizedNonemptyIndexedRootedThreatCodeWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (p : TripleOn V → ℝ≥0)
    (d : LocalizedNonemptyIndexedRootedThreatCode V q B u v U) : ℝ≥0 :=
  if ({d.1.1.1} : TripleSystemOn V) ⊆ d.2.2.1 then
    setWeight p (d.2.2.1 \ {d.1.1.1})
  else 0

/-- The nonempty-witness sum is dominated by the restricted injective code. -/
theorem sum_localizedNonemptyRootedThreatWeight_le_code
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (p : TripleOn V → ℝ≥0) :
    (∑ z : LocalizedNonemptyRootedThreatWitness V q B u v U,
      setWeight p (localizedRootedThreatRemainder z.1)) ≤
      ∑ d : LocalizedNonemptyIndexedRootedThreatCode V q B u v U,
        localizedNonemptyIndexedRootedThreatCodeWeight p d := by
  apply sum_le_sum_of_injective_code
    localizedNonemptyIndexedRootedThreatCode
    localizedNonemptyIndexedRootedThreatCode_injective
  intro z
  unfold localizedNonemptyIndexedRootedThreatCodeWeight
  rw [if_pos]
  · change setWeight p (z.1.1.1.1.erase z.1.1.1.2) ≤
      setWeight p (z.1.1.1.1 \ {z.1.1.1.2})
    rw [sdiff_singleton_eq_erase]
  · simp only [singleton_subset_iff]
    exact z.1.1.2.2.1

/-- Summing the restricted code fibers gives singleton extension weights. -/
theorem sum_localizedNonemptyIndexedRootedThreatCodeWeight_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (p : TripleOn V → ℝ≥0) :
    (∑ d : LocalizedNonemptyIndexedRootedThreatCode V q B u v U,
      localizedNonemptyIndexedRootedThreatCodeWeight p d) =
      ∑ T : LocalizedUniverseTriplesThroughPair V u v U,
        ∑ j : NonemptyRootedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1.1 B ↦ S.1)
            p {T.1.1} := by
  unfold LocalizedNonemptyIndexedRootedThreatCode
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro T _hT
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro j _hj
  rfl

/-- The bank-independent density coefficient for nonempty localized rooted
threats at the first level of an `(m+1)`-step vortex. -/
def localizedNonemptyRootedThreatSharpCoefficient
    (m q M : ℕ) (c : ℝ≥0) : ℝ≥0 :=
  ∑ j : NonemptyRootedThreatOrder q,
    (((j.1.1 + 1) ^ (m + 1) *
      ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1)) : ℕ) :
        ℝ≥0) * c ^ (j.1.1 - 3)

/-- Sharp empty-root estimate for the nonempty localized witnesses. -/
theorem sum_localizedNonemptyRootedThreatWeight_vortex_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {m q M : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (c : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : AbsorberSeparatedLevel H X B (W.U 1))
    (houter : ∀ i : Fin (m + 1), 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    {u v : V} (U : Finset V) (huv : u ≠ v) :
    (∑ z : LocalizedNonemptyRootedThreatWitness
        V q B u v U,
      setWeight (vortexTripleWeight W c)
        (localizedRootedThreatRemainder z.1)) ≤
      (U.card : ℝ≥0) *
        localizedNonemptyRootedThreatSharpCoefficient m q M c := by
  calc
    (∑ z : LocalizedNonemptyRootedThreatWitness
          V q B u v U,
        setWeight (vortexTripleWeight W c)
          (localizedRootedThreatRemainder z.1)) ≤
        ∑ d : LocalizedNonemptyIndexedRootedThreatCode
            V q B u v U,
          localizedNonemptyIndexedRootedThreatCodeWeight
            (vortexTripleWeight W c) d :=
      sum_localizedNonemptyRootedThreatWeight_le_code _
    _ = ∑ T : LocalizedUniverseTriplesThroughPair V u v U,
        ∑ j : NonemptyRootedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1.1 B ↦ S.1)
            (vortexTripleWeight W c) {T.1.1} :=
      sum_localizedNonemptyIndexedRootedThreatCodeWeight_eq _
    _ ≤ ∑ _T : LocalizedUniverseTriplesThroughPair V u v U,
        localizedNonemptyRootedThreatSharpCoefficient m q M c := by
      apply sum_le_sum
      intro T _hT
      unfold localizedNonemptyRootedThreatSharpCoefficient
      apply sum_le_sum
      intro j _hj
      exact extensionWeight_absorberInduced_vortex_singleton_le_sharpWS4
        W H X B c hA2
          (fun x hx hxX ↦ (hsep.2 x hx hxX).1)
          j.2 (mem_Icc.mp j.1.2).2 houter hterminal hbank T.1.1
    _ = (Fintype.card
          (LocalizedUniverseTriplesThroughPair V u v U) : ℝ≥0) *
        localizedNonemptyRootedThreatSharpCoefficient m q M c := by
      rw [sum_const, card_univ]
      simp only [nsmul_eq_mul]
    _ ≤ (U.card : ℝ≥0) *
        localizedNonemptyRootedThreatSharpCoefficient m q M c := by
      gcongr
      exact_mod_cast card_localizedUniverseTriplesThroughPair_le
        V huv U

/-- Uniform sharp empty-root estimate for every rooted pair.  The endpoint
with empty remainder costs at most one choice per vertex of `U`; all
nonempty remainders are controlled by the sharp WS4 coefficient. -/
theorem extensionWeight_localizedRootedThreat_vortex_empty_le_level_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {m q M : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (c : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : AbsorberSeparatedLevel H X B (W.U 1))
    (houter : ∀ i : Fin (m + 1), 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    {u v : V} (U : Finset V) (huv : u ≠ v) :
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B)
            u v U ↦ localizedRootedThreatRemainder z)
        (vortexTripleWeight W c) ∅ ≤
      (U.card : ℝ≥0) *
        (1 + localizedNonemptyRootedThreatSharpCoefficient m q M c) := by
  calc
    extensionWeight
          (fun z : LocalizedRootedThreatWitness V
              (absorberErdosForbiddenConfigurationsOn q B)
              u v U ↦ localizedRootedThreatRemainder z)
          (vortexTripleWeight W c) ∅ ≤
        (U.card : ℝ≥0) +
          ∑ z : LocalizedNonemptyRootedThreatWitness V q B u v U,
            setWeight (vortexTripleWeight W c)
              (localizedRootedThreatRemainder z.1) :=
      extensionWeight_localizedRootedThreat_empty_le_level_add_nonempty
        huv (vortexTripleWeight W c)
    _ ≤ (U.card : ℝ≥0) + (U.card : ℝ≥0) *
        localizedNonemptyRootedThreatSharpCoefficient m q M c :=
      add_le_add le_rfl
        (sum_localizedNonemptyRootedThreatWeight_vortex_le_sharp
          W H X B c hA2 hsep houter hterminal hbank U huv)
    _ = (U.card : ℝ≥0) *
        (1 + localizedNonemptyRootedThreatSharpCoefficient m q M c) := by
      ring

/-- The complete empty-root estimate: six exceptional empty remainders plus
the density-sensitive nonempty part. -/
theorem extensionWeight_localizedRootedThreat_vortex_empty_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {m q M : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (c : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : AbsorberSeparatedLevel H X B (W.U 1))
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (houter : ∀ i : Fin (m + 1), 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    {u v : V} (huv : u ≠ v) (huvH : ¬ H.Adj u v) :
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B)
            u v (W.U 1) ↦ localizedRootedThreatRemainder z)
        (vortexTripleWeight W c) ∅ ≤
      6 + ((W.U 1).card : ℝ≥0) *
        localizedNonemptyRootedThreatSharpCoefficient m q M c := by
  exact (extensionWeight_localizedRootedThreat_empty_le_six_add_nonempty
    huv huvH hsep hroot (vortexTripleWeight W c)).trans
      (add_le_add le_rfl
        (sum_localizedNonemptyRootedThreatWeight_vortex_le_sharp
          W H X B c hA2 hsep houter hterminal hbank (W.U 1) huv))

end

end Erdos207
