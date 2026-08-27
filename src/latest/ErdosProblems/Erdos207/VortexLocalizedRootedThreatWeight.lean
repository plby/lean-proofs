/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedThreatWeight
import ErdosProblems.Erdos207.VortexRootedThreatWeight
import ErdosProblems.Erdos207.VortexRootedThreatFourWeight

/-!
# Vortex weights for localized rooted threats

Restricting the missing third vertex to `U` replaces the ambient factor
`|V|` in the rooted extension estimate by `|U|`.  The proof retains this
restriction in the injective rooted-threat code before summing its fibers.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Triples through `u,v` whose third vertex belongs to `U`. -/
abbrev LocalizedUniverseTriplesThroughPair
    (V : Type*) [Fintype V] [DecidableEq V]
    (u v : V) (U : Finset V) :=
  {T : universeTriplesThroughPair u v //
    ∃ w ∈ T.1.1, w ∈ U ∧ w ≠ u ∧ w ≠ v}

/-- The third vertex retained by a localized rooted triangle. -/
def localizedPairThirdVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} {U : Finset V}
    (T : LocalizedUniverseTriplesThroughPair V u v U) : {w // w ∈ U} :=
  ⟨Classical.choose T.2, (Classical.choose_spec T.2).2.1⟩

lemma eraseThroughPair_localized_eq_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} {U : Finset V} (huv : u ≠ v)
    (T : LocalizedUniverseTriplesThroughPair V u v U) :
    (eraseThroughPair huv T.1).1 =
      {(localizedPairThirdVertex T : V)} := by
  let w : V := localizedPairThirdVertex T
  change (T.1.1.1.erase u).erase v = {w}
  have hw := Classical.choose_spec T.2
  have hwu : w ≠ u := hw.2.2.1
  have hwv : w ≠ v := hw.2.2.2
  have hwErase : w ∈ (T.1.1.1.erase u).erase v := by
    exact mem_erase.mpr ⟨hwv, mem_erase.mpr ⟨hwu, hw.1⟩⟩
  have hcardEq := (eraseThroughPair huv T.1).2
  change ((T.1.1.1.erase u).erase v).card = 1 at hcardEq
  have hcard : ((T.1.1.1.erase u).erase v).card ≤ 1 := hcardEq.le
  ext x
  constructor
  · intro hx
    have hxw := card_le_one.mp hcard x hx w hwErase
    simpa only [mem_singleton] using hxw
  · intro hx
    have hxw : x = w := by simpa only [mem_singleton] using hx
    simpa only [hxw] using hwErase

lemma localizedPairThirdVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} {U : Finset V} (huv : u ≠ v) :
    Function.Injective
      (localizedPairThirdVertex :
        LocalizedUniverseTriplesThroughPair V u v U → {w // w ∈ U}) := by
  intro T S hTS
  apply Subtype.ext
  apply eraseThroughPair_injective huv
  apply Subtype.ext
  rw [eraseThroughPair_localized_eq_singleton huv T,
    eraseThroughPair_localized_eq_singleton huv S]
  exact congrArg (fun w : {w // w ∈ U} ↦ ({(w : V)} : Finset V)) hTS

/-- At most `|U|` localized rooted triangles pass through a fixed distinct
pair. -/
theorem card_localizedUniverseTriplesThroughPair_le
    (V : Type*) [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    Fintype.card (LocalizedUniverseTriplesThroughPair V u v U) ≤ U.card := by
  calc
    Fintype.card (LocalizedUniverseTriplesThroughPair V u v U) ≤
        Fintype.card {w : V // w ∈ U} :=
      Fintype.card_le_of_injective localizedPairThirdVertex
        (localizedPairThirdVertex_injective huv)
    _ = U.card := Fintype.card_coe U

/-- For the packing-filtered absorber forbidden family every rooted witness
belongs to the indexed part; the nominal order-four complement is empty. -/
lemma localizedRootedThreat_isIndexed
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (z : LocalizedRootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v U) :
    IsIndexedRootedThreatWitness q B u v z.1 := by
  by_contra hindexed
  let z4 : FourRootedThreatWitness V q B u v := ⟨z.1, hindexed⟩
  exact fourRootedThreatWitness_isEmpty z4

/-- Injective code retaining a localized designated triangle. -/
abbrev LocalizedIndexedRootedThreatCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V) (U : Finset V) :=
  Σ T : LocalizedUniverseTriplesThroughPair V u v U,
    Σ j : IndexedThreatOrder q,
      {S : TripleSystemOn V //
        S ∈ absorberInducedConfigurationsOn q j.1 B}

def localizedIndexedRootedThreatCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (z : LocalizedRootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v U) :
    LocalizedIndexedRootedThreatCode V q B u v U :=
  let zi : IndexedRootedThreatWitness V q B u v :=
    ⟨z.1, localizedRootedThreat_isIndexed z⟩
  ⟨⟨⟨z.1.1.2, mem_universeTriplesThroughPair_iff.mpr
      ⟨z.1.2.2.2.1, z.1.2.2.2.2⟩⟩, z.2⟩,
    ⟨⟨z.1.1.1.card + 2, indexedRootedThreat_order_mem zi⟩,
      ⟨z.1.1.1, zi.2⟩⟩⟩

lemma localizedIndexedRootedThreatCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V} :
    Function.Injective
      (localizedIndexedRootedThreatCode :
        LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v U →
          LocalizedIndexedRootedThreatCode V q B u v U) := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun c ↦ c.2.2.1) hzw
  · exact congrArg (fun c ↦ c.1.1.1) hzw

def localizedIndexedRootedThreatCodeWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V)
    (c : LocalizedIndexedRootedThreatCode V q B u v U) : ℝ≥0 :=
  if insert c.1.1.1 A ⊆ c.2.2.1 then
    setWeight p (c.2.2.1 \ insert c.1.1.1 A)
  else 0

theorem localizedRootedThreat_weight_le_code
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
          localizedRootedThreatRemainder z)
        p A ≤
      ∑ c : LocalizedIndexedRootedThreatCode V q B u v U,
        localizedIndexedRootedThreatCodeWeight p A c := by
  classical
  unfold extensionWeight
  apply sum_le_sum_of_injective_code localizedIndexedRootedThreatCode
    localizedIndexedRootedThreatCode_injective
  intro z
  by_cases hA : A ⊆ localizedRootedThreatRemainder z
  · rw [if_pos hA]
    change setWeight p (rootedThreatRemainder z.1 \ A) ≤
      if insert z.1.1.2 A ⊆ z.1.1.1 then
        setWeight p (z.1.1.1 \ insert z.1.1.2 A) else 0
    rw [if_pos (insert_root_subset_of_remainder z.1 hA)]
    rw [rootedThreatRemainder_sdiff]
  · simp [hA, localizedIndexedRootedThreatCodeWeight]

theorem sum_localizedIndexedRootedThreatCodeWeight_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    (∑ c : LocalizedIndexedRootedThreatCode V q B u v U,
      localizedIndexedRootedThreatCodeWeight p A c) =
      ∑ T : LocalizedUniverseTriplesThroughPair V u v U,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1.1 A) := by
  unfold LocalizedIndexedRootedThreatCode
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro T _hT
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro j _hj
  rfl

/-- Uniform all-root extension bound with the sharp localized factor
`|U|`. -/
theorem localizedRootedThreatRemainder_hasExtensionBound_vortex
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
        localizedRootedThreatRemainder z)
      (vortexTripleWeight W c)
      ((U.card : ℝ≥0) *
        indexedRootedThreatVortexUniformCoefficient W q B) := by
  intro A
  let p : TripleOn V → ℝ≥0 := vortexTripleWeight W c
  calc
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
          localizedRootedThreatRemainder z) p A ≤
      ∑ code : LocalizedIndexedRootedThreatCode V q B u v U,
        localizedIndexedRootedThreatCodeWeight p A code :=
      localizedRootedThreat_weight_le_code p A
    _ = ∑ T : LocalizedUniverseTriplesThroughPair V u v U,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1.1 A) :=
      sum_localizedIndexedRootedThreatCodeWeight_eq p A
    _ ≤ ∑ _T : LocalizedUniverseTriplesThroughPair V u v U,
        indexedRootedThreatVortexExtensionCoefficient W q B c A.card := by
      apply sum_le_sum
      intro T _hT
      unfold indexedRootedThreatVortexExtensionCoefficient
      apply sum_le_sum
      intro j _hj
      by_cases hrootcard : (insert T.1.1 A).card ≤ j.1 - 2
      · have hsharp :=
          extensionWeight_absorberInduced_vortex_nonempty_le_sharp
            (q := q) (j := j.1) W B c (mem_Icc.mp j.2).1 houter
              hterminal (insert T.1.1 A) (by simp) hrootcard
        apply hsharp.trans
        have hExp : j.1 - 3 - A.card ≤
            j.1 - 2 - (insert T.1.1 A).card := by
          have hinsert := card_insert_le T.1.1 A
          omega
        simpa only [mul_comm] using
          mul_le_mul_left (pow_le_pow_right_of_le_one' hc hExp)
            ((((j.1 + 1) ^ ell *
              indexedInducedVortexSpreadCoefficient
                q ell B W.terminalSize : ℕ) : ℝ≥0))
      · have hzero :
            extensionWeight
                (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
                p (insert T.1.1 A) = 0 := by
          unfold extensionWeight
          apply sum_eq_zero
          intro S _hS
          rw [if_neg]
          intro hsub
          apply hrootcard
          calc
            (insert T.1.1 A).card ≤ S.1.card := card_le_card hsub
            _ = j.1 - 2 :=
              (mem_absorberInducedConfigurationsOn_iff.mp S.2).1
        rw [hzero]
        exact bot_le
    _ = (Fintype.card
          (LocalizedUniverseTriplesThroughPair V u v U) : ℝ≥0) *
        indexedRootedThreatVortexExtensionCoefficient W q B c A.card := by
      rw [sum_const, card_univ]
      simp only [nsmul_eq_mul]
    _ ≤ (U.card : ℝ≥0) *
        indexedRootedThreatVortexExtensionCoefficient W q B c A.card := by
      gcongr
      exact_mod_cast card_localizedUniverseTriplesThroughPair_le V huv U
    _ ≤ (U.card : ℝ≥0) *
        indexedRootedThreatVortexUniformCoefficient W q B := by
      gcongr
      unfold indexedRootedThreatVortexExtensionCoefficient
      unfold indexedRootedThreatVortexUniformCoefficient
      apply sum_le_sum
      intro j _hj
      have hpow : c ^ (j.1 - 3 - A.card) ≤ (1 : ℝ≥0) :=
        pow_le_one₀ (by positivity) hc
      simpa only [mul_one, one_mul, mul_comm] using
        mul_le_mul_left hpow
          ((((j.1 + 1) ^ ell *
            indexedInducedVortexSpreadCoefficient
              q ell B W.terminalSize : ℕ) : ℝ≥0))

/-- The one-power-shifted coefficient needed when the vortex multiplier is
at least one.  The shift covers the case in which the designated missing
triangle is already present in the planted root. -/
def localizedRootedThreatVortexLargeCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q : ℕ) (B : TripleSystemOn V)
    (c : ℝ≥0) (a : ℕ) : ℝ≥0 :=
  ∑ j : IndexedThreatOrder q,
    (((j.1 + 1) ^ ell *
      indexedInducedVortexSpreadCoefficient q ell B W.terminalSize : ℕ) :
        ℝ≥0) * c ^ (j.1 - 2 - a)

/-- For a vortex multiplier at least one, the root-cardinality-dependent
coefficient is largest at the empty root.  This is the companion to the
`c ≤ 1` uniform estimate above and is the form used to dominate the sum of
the initial and later master weights. -/
theorem localizedRootedThreatRemainder_hasExtensionBound_vortex_of_one_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hc : 1 ≤ c)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
        localizedRootedThreatRemainder z)
      (vortexTripleWeight W c)
      ((U.card : ℝ≥0) *
        localizedRootedThreatVortexLargeCoefficient W q B c 0) := by
  intro A
  let p : TripleOn V → ℝ≥0 := vortexTripleWeight W c
  calc
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
          localizedRootedThreatRemainder z) p A ≤
      ∑ code : LocalizedIndexedRootedThreatCode V q B u v U,
        localizedIndexedRootedThreatCodeWeight p A code :=
      localizedRootedThreat_weight_le_code p A
    _ = ∑ T : LocalizedUniverseTriplesThroughPair V u v U,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1.1 A) :=
      sum_localizedIndexedRootedThreatCodeWeight_eq p A
    _ ≤ ∑ _T : LocalizedUniverseTriplesThroughPair V u v U,
        localizedRootedThreatVortexLargeCoefficient W q B c A.card := by
      apply sum_le_sum
      intro T _hT
      unfold localizedRootedThreatVortexLargeCoefficient
      apply sum_le_sum
      intro j _hj
      by_cases hrootcard : (insert T.1.1 A).card ≤ j.1 - 2
      · have hsharp :=
          extensionWeight_absorberInduced_vortex_nonempty_le_sharp
            (q := q) (j := j.1) W B c (mem_Icc.mp j.2).1 houter
              hterminal (insert T.1.1 A) (by simp) hrootcard
        apply hsharp.trans
        have hExp : j.1 - 2 - (insert T.1.1 A).card ≤
            j.1 - 2 - A.card := by
          have hinsert : A.card ≤ (insert T.1.1 A).card :=
            card_le_card (subset_insert _ _)
          omega
        simpa only [mul_comm] using
          mul_le_mul_left (pow_le_pow_right₀ hc hExp)
            ((((j.1 + 1) ^ ell *
              indexedInducedVortexSpreadCoefficient
                q ell B W.terminalSize : ℕ) : ℝ≥0))
      · have hzero :
            extensionWeight
                (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
                p (insert T.1.1 A) = 0 := by
          unfold extensionWeight
          apply sum_eq_zero
          intro S _hS
          rw [if_neg]
          intro hsub
          apply hrootcard
          calc
            (insert T.1.1 A).card ≤ S.1.card := card_le_card hsub
            _ = j.1 - 2 :=
              (mem_absorberInducedConfigurationsOn_iff.mp S.2).1
        rw [hzero]
        exact bot_le
    _ = (Fintype.card
          (LocalizedUniverseTriplesThroughPair V u v U) : ℝ≥0) *
        localizedRootedThreatVortexLargeCoefficient W q B c A.card := by
      rw [sum_const, card_univ]
      simp only [nsmul_eq_mul]
    _ ≤ (U.card : ℝ≥0) *
        localizedRootedThreatVortexLargeCoefficient W q B c A.card := by
      gcongr
      exact_mod_cast card_localizedUniverseTriplesThroughPair_le V huv U
    _ ≤ (U.card : ℝ≥0) *
        localizedRootedThreatVortexLargeCoefficient W q B c 0 := by
      gcongr
      unfold localizedRootedThreatVortexLargeCoefficient
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
