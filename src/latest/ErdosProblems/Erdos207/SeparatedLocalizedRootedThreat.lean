/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexLocalizedRootedThreatWeight
import ErdosProblems.Erdos207.PaddedAbsorberRootBounds
import ErdosProblems.Erdos207.PaddedAbsorberRootLocalization
import ErdosProblems.Erdos207.InitialVortexTypicality

/-!
# Sharp localized rooted threats at a separated absorber level

The generic vortex rooted-threat estimate deliberately forgets the geometry
of the padded absorber.  At a separated level this is far too coarse for the
empty-remainder endpoint.  Such a witness is uniquely determined by its
missing third vertex, and that vertex belongs to the six-element padded-root
obstruction set.  This file records that injection.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

/-- A three-set containing `u`, `v`, and a third distinct vertex is the
canonical triangle on those three vertices. -/
lemma thirdVertexTriple_eq_of_mem
    {V : Type*} [DecidableEq V] {u v w : V} (huv : u ≠ v)
    (T : TripleOn V) (huT : u ∈ T.1) (hvT : v ∈ T.1)
    (hwT : w ∈ T.1) (hwu : w ≠ u) (hwv : w ≠ v) :
    thirdVertexTriple huv ⟨w, hwu, hwv⟩ = T := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [thirdVertexTriple, tripleOfThree, mem_insert,
      mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact huT
    · exact hvT
    · exact hwT
  · rw [T.2]
    exact (thirdVertexTriple huv ⟨w, hwu, hwv⟩).2.ge

/-- Localized rooted witnesses whose selected remainder is empty. -/
abbrev LocalizedEmptyRootedThreatWitness
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V)
    (u v : V) (U : Finset V) :=
  {z : LocalizedRootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v U //
    localizedRootedThreatRemainder z = ∅}

/-- Localized rooted witnesses whose selected remainder is nonempty. -/
abbrev LocalizedNonemptyRootedThreatWitness
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V)
    (u v : V) (U : Finset V) :=
  {z : LocalizedRootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v U //
    localizedRootedThreatRemainder z ≠ ∅}

/-- The missing third vertex of an empty-remainder witness, retaining only
its localization in `U`.  Unlike the padded-root refinement below, this map
does not need the rooted pair to avoid the absorber graph. -/
def localizedEmptyRootedThreatThirdVertexInLevel
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : Finset V} {u v : V}
    (z : LocalizedEmptyRootedThreatWitness V q B u v U) :
    {x // x ∈ U} :=
  ⟨Classical.choose z.1.2, (Classical.choose_spec z.1.2).2.1⟩

/-- An empty rooted remainder is determined by its missing third vertex. -/
lemma localizedEmptyRootedThreatThirdVertexInLevel_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : Finset V} {u v : V}
    (huv : u ≠ v) :
    Function.Injective
      (localizedEmptyRootedThreatThirdVertexInLevel :
        LocalizedEmptyRootedThreatWitness V q B u v U → {x // x ∈ U}) := by
  intro z z' hzz'
  have hx : Classical.choose z.1.2 = Classical.choose z'.1.2 :=
    congrArg Subtype.val hzz'
  have hzdata := Classical.choose_spec z.1.2
  have hz'data := Classical.choose_spec z'.1.2
  let w : ThirdVertex u v :=
    ⟨Classical.choose z.1.2, hzdata.2.2.1, hzdata.2.2.2⟩
  let w' : ThirdVertex u v :=
    ⟨Classical.choose z'.1.2, hz'data.2.2.1, hz'data.2.2.2⟩
  have hww' : w = w' := by
    apply Subtype.ext
    exact hx
  have hT : z.1.1.1.2 = z'.1.1.1.2 := by
    calc
      z.1.1.1.2 = thirdVertexTriple huv w :=
        (thirdVertexTriple_eq_of_mem huv z.1.1.1.2
          z.1.1.2.2.2.1 z.1.1.2.2.2.2 hzdata.1
          hzdata.2.2.1 hzdata.2.2.2).symm
      _ = thirdVertexTriple huv w' := congrArg _ hww'
      _ = z'.1.1.1.2 :=
        thirdVertexTriple_eq_of_mem huv z'.1.1.1.2
          z'.1.1.2.2.2.1 z'.1.1.2.2.2.2 hz'data.1
          hz'data.2.2.1 hz'data.2.2.2
  have hS : z.1.1.1.1 = z'.1.1.1.1 := by
    have hzSingleton : z.1.1.1.1 = {z.1.1.1.2} := by
      rcases (erase_eq_empty_iff z.1.1.1.1 z.1.1.1.2).mp z.2 with
        hzEmpty | hzSingle
      · exfalso
        have hmem := z.1.1.2.2.1
        rw [hzEmpty] at hmem
        simpa using hmem
      · exact hzSingle
    have hz'Singleton : z'.1.1.1.1 = {z'.1.1.1.2} := by
      rcases (erase_eq_empty_iff z'.1.1.1.1 z'.1.1.1.2).mp z'.2 with
        hzEmpty | hzSingle
      · exfalso
        have hmem := z'.1.1.2.2.1
        rw [hzEmpty] at hmem
        simpa using hmem
      · exact hzSingle
    rw [hzSingleton, hz'Singleton, hT]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hS hT

/-- The empty-remainder endpoint has at most one witness for each possible
missing third vertex in the localization level. -/
theorem card_localizedEmptyRootedThreatWitness_le_level
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : Finset V} {u v : V}
    (huv : u ≠ v) :
    Fintype.card (LocalizedEmptyRootedThreatWitness V q B u v U) ≤ U.card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective
      (localizedEmptyRootedThreatThirdVertexInLevel :
        LocalizedEmptyRootedThreatWitness V q B u v U → {x // x ∈ U})
      (localizedEmptyRootedThreatThirdVertexInLevel_injective huv)

/-- The missing third vertex of an empty-remainder localized witness, viewed
as an element of the padded absorber's pair-obstruction set. -/
def localizedEmptyRootedThreatThirdVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {u v : V} (huv : u ≠ v)
    (huvH : ¬ H.Adj u v)
    (hUX : ∀ x ∈ U, x ∉ X →
      x ∉ graphSupportFinset H ∧ x ∉ verticesOn B)
    (z : LocalizedEmptyRootedThreatWitness V q B u v U) :
    {x // x ∈ absorberRootPairObstructionSet q B X huv} := by
  let x : V := Classical.choose z.1.2
  have hx := Classical.choose_spec z.1.2
  have hxu : x ≠ u := hx.2.2.1
  have hxv : x ≠ v := hx.2.2.2
  let w : ThirdVertex u v := ⟨x, hxu, hxv⟩
  have hT : thirdVertexTriple huv w = z.1.1.1.2 := by
    exact thirdVertexTriple_eq_of_mem huv z.1.1.1.2
      z.1.1.2.2.2.1 z.1.1.2.2.2.2 hx.1 hxu hxv
  have hcomplete : CompletesForbidden
      (absorberErdosForbiddenConfigurationsOn q B) ∅
      (thirdVertexTriple huv w) := by
    refine ⟨z.1.1.1.1, z.1.1.2.1, ?_, ?_⟩
    · simpa only [hT] using z.1.1.2.2.1
    · intro R hR
      have hR' : R ∈ localizedRootedThreatRemainder z.1 := by
        simpa only [localizedRootedThreatRemainder,
          rootedThreatRemainder, hT] using hR
      exact (congrArg (fun A : TripleSystemOn V ↦ R ∈ A) z.2).mp hR'
  have hxX : x ∈ X := by
    by_contra hxnot
    have hxSep := hUX x hx.2.1 hxnot
    have hAvoid : TriangleAvoidsGraph H (thirdVertexTriple huv w) :=
      (triangleAvoidsGraph_thirdVertexTriple_iff H huv w).mpr
        ⟨huvH,
          fun h ↦ hxSep.1
            (mem_graphSupportFinset_iff.mpr ⟨u, h.symm⟩),
          fun h ↦ hxSep.1
            (mem_graphSupportFinset_iff.mpr ⟨v, h.symm⟩)⟩
    exact hxSep.2
      (singleton_absorberForbidden_third_mem_bankSupport
        huv w hAvoid hcomplete)
  refine ⟨x, mem_absorberRootPairObstructionSet_iff.mpr ?_⟩
  exact ⟨hxX, w, rfl, Or.inr hcomplete⟩

/-- The preceding third-vertex map is injective: an empty remainder forces
the forbidden outside family to be the singleton containing its designated
triangle. -/
lemma localizedEmptyRootedThreatThirdVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {u v : V} (huv : u ≠ v)
    (huvH : ¬ H.Adj u v)
    (hUX : ∀ x ∈ U, x ∉ X →
      x ∉ graphSupportFinset H ∧ x ∉ verticesOn B) :
    Function.Injective
      (localizedEmptyRootedThreatThirdVertex huv huvH hUX :
        LocalizedEmptyRootedThreatWitness V q B u v U →
          {x // x ∈ absorberRootPairObstructionSet q B X huv}) := by
  intro z z' hzz'
  have hx : Classical.choose z.1.2 = Classical.choose z'.1.2 :=
    congrArg Subtype.val hzz'
  have hzdata := Classical.choose_spec z.1.2
  have hz'data := Classical.choose_spec z'.1.2
  let w : ThirdVertex u v :=
    ⟨Classical.choose z.1.2, hzdata.2.2.1, hzdata.2.2.2⟩
  let w' : ThirdVertex u v :=
    ⟨Classical.choose z'.1.2, hz'data.2.2.1, hz'data.2.2.2⟩
  have hww' : w = w' := by
    apply Subtype.ext
    exact hx
  have hT : z.1.1.1.2 = z'.1.1.1.2 := by
    calc
      z.1.1.1.2 = thirdVertexTriple huv w :=
        (thirdVertexTriple_eq_of_mem huv z.1.1.1.2
          z.1.1.2.2.2.1 z.1.1.2.2.2.2 hzdata.1
          hzdata.2.2.1 hzdata.2.2.2).symm
      _ = thirdVertexTriple huv w' := congrArg _ hww'
      _ = z'.1.1.1.2 :=
        thirdVertexTriple_eq_of_mem huv z'.1.1.1.2
          z'.1.1.2.2.2.1 z'.1.1.2.2.2.2 hz'data.1
          hz'data.2.2.1 hz'data.2.2.2
  have hS : z.1.1.1.1 = z'.1.1.1.1 := by
    have hzSingleton : z.1.1.1.1 = {z.1.1.1.2} := by
      rcases (erase_eq_empty_iff z.1.1.1.1 z.1.1.1.2).mp z.2 with
        hzEmpty | hzSingle
      · exfalso
        have hmem := z.1.1.2.2.1
        rw [hzEmpty] at hmem
        simpa using hmem
      · exact hzSingle
    have hz'Singleton : z'.1.1.1.1 = {z'.1.1.1.2} := by
      rcases (erase_eq_empty_iff z'.1.1.1.1 z'.1.1.1.2).mp z'.2 with
        hzEmpty | hzSingle
      · exfalso
        have hmem := z'.1.1.2.2.1
        rw [hzEmpty] at hmem
        simpa using hmem
      · exact hzSingle
    rw [hzSingleton, hz'Singleton, hT]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hS hT

/-- In every localized rooted witness, the designated third vertex is
incident with either a remainder triangle or a bank triangle.  Minimality at
order at least five says that every configuration vertex lies in at least
two configuration triangles; the second triangle cannot disappear anywhere
except into the bank or the rooted remainder. -/
lemma localizedRootedThreat_thirdVertex_mem_remainder_or_bank
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : Finset V}
    {u v : V}
    (z : LocalizedRootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v U) :
    Classical.choose z.2 ∈ verticesOn (localizedRootedThreatRemainder z) ∨
      Classical.choose z.2 ∈ verticesOn B := by
  let x : V := Classical.choose z.2
  have hx := Classical.choose_spec z.2
  have hindexed := localizedRootedThreat_isIndexed z
  obtain ⟨_hScard, r, hr5, _hrq, E, hE, hEout⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hindexed
  have hTE : z.1.1.2 ∈ E := by
    have hTdiff : z.1.1.2 ∈ E \ B := by
      rw [hEout]
      exact z.1.2.2.1
    exact (mem_sdiff.mp hTdiff).1
  have hxE : x ∈ verticesOn E :=
    mem_biUnion.mpr ⟨z.1.1.2, hTE, hx.1⟩
  have htwo := IsErdosConfig.two_le_card_triplesThrough hE hr5 hxE
  obtain ⟨R, hRthrough, hRT⟩ :=
    Finset.exists_mem_ne (by omega : 1 < (triplesThrough E x).card)
      z.1.1.2
  have hRdata := mem_filter.mp hRthrough
  by_cases hRB : R ∈ B
  · exact Or.inr (mem_biUnion.mpr ⟨R, hRB, hRdata.2⟩)
  · apply Or.inl
    apply mem_biUnion.mpr
    refine ⟨R, ?_, hRdata.2⟩
    apply mem_erase.mpr
    refine ⟨hRT, ?_⟩
    have hRdiff : R ∈ E \ B := mem_sdiff.mpr ⟨hRdata.1, hRB⟩
    rw [hEout] at hRdiff
    exact hRdiff

/-- At a separated level, a nonroot missing third vertex must already occur
in the witness remainder.  This is the key incidence saving which avoids a
factor equal to the whole level size in the first-moment rooted count. -/
lemma localizedRootedThreat_thirdVertex_mem_remainder_of_not_mem_root
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {u v : V}
    (hsep : AbsorberSeparatedLevel H X B U)
    (z : LocalizedRootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v U)
    (hxX : Classical.choose z.2 ∉ X) :
    Classical.choose z.2 ∈
      verticesOn (localizedRootedThreatRemainder z) := by
  rcases localizedRootedThreat_thirdVertex_mem_remainder_or_bank z with
    hrem | hbank
  · exact hrem
  · exact ((hsep.2 (Classical.choose z.2)
      (Classical.choose_spec z.2).2.1 hxX).2 hbank).elim

/-- Empty-remainder localized threats are bounded by the padded absorber's
six root obstructions, independently of the ambient order and bank size. -/
theorem card_localizedEmptyRootedThreatWitness_le_six
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V}
    {X U : Finset V} {u v : V} (huv : u ≠ v)
    (huvH : ¬ H.Adj u v)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hroot : HasPaddedAbsorberRootBounds q H X B) :
    Fintype.card (LocalizedEmptyRootedThreatWitness V q B u v U) ≤ 6 := by
  calc
    Fintype.card (LocalizedEmptyRootedThreatWitness V q B u v U) ≤
        Fintype.card {x // x ∈ absorberRootPairObstructionSet q B X huv} :=
      Fintype.card_le_of_injective
        (localizedEmptyRootedThreatThirdVertex huv
          huvH hsep.2)
        (localizedEmptyRootedThreatThirdVertex_injective huv huvH hsep.2)
    _ = (absorberRootPairObstructionSet q B X huv).card :=
      Fintype.card_coe _
    _ ≤ 6 := hroot.2 u v huv

/-- At the empty planted root, the localized rooted extension weight splits
exactly into the genuinely empty endpoint and the nonempty remainders. -/
lemma extensionWeight_localizedRootedThreat_empty_eq_empty_add_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} {U : Finset V}
    (p : TripleOn V → ℝ≥0) :
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
          localizedRootedThreatRemainder z)
        p ∅ =
      ∑ z : LocalizedEmptyRootedThreatWitness V q B u v U,
          setWeight p (localizedRootedThreatRemainder z.1) +
        ∑ z : LocalizedNonemptyRootedThreatWitness V q B u v U,
          setWeight p (localizedRootedThreatRemainder z.1) := by
  classical
  unfold extensionWeight
  simp only [empty_subset, true_and, if_true, sdiff_empty]
  symm
  simpa using Fintype.sum_subtype_add_sum_subtype
    (fun z : LocalizedRootedThreatWitness V
        (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
      localizedRootedThreatRemainder z = ∅)
    (fun z ↦ setWeight p (localizedRootedThreatRemainder z))

/-- Without using absorber-root geometry, the empty-remainder contribution
is bounded by the number of possible missing third vertices in `U`. -/
theorem sum_localizedEmptyRootedThreatWeight_le_level
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : Finset V} {u v : V}
    (huv : u ≠ v) (p : TripleOn V → ℝ≥0) :
    (∑ z : LocalizedEmptyRootedThreatWitness V q B u v U,
      setWeight p (localizedRootedThreatRemainder z.1)) ≤ U.card := by
  calc
    (∑ z : LocalizedEmptyRootedThreatWitness V q B u v U,
        setWeight p (localizedRootedThreatRemainder z.1)) =
        Fintype.card (LocalizedEmptyRootedThreatWitness V q B u v U) := by
      calc
        (∑ z : LocalizedEmptyRootedThreatWitness V q B u v U,
            setWeight p (localizedRootedThreatRemainder z.1)) =
            ∑ _z : LocalizedEmptyRootedThreatWitness V q B u v U,
              (1 : ℝ≥0) := by
          apply Finset.sum_congr rfl
          intro z _hz
          rw [z.2]
          simp [setWeight]
        _ = Fintype.card
            (LocalizedEmptyRootedThreatWitness V q B u v U) := by
          simp
    _ ≤ U.card := by
      exact_mod_cast card_localizedEmptyRootedThreatWitness_le_level huv

/-- The complete empty-root extension weight is the level-sized empty
endpoint plus the contribution of nonempty remainders. -/
theorem extensionWeight_localizedRootedThreat_empty_le_level_add_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : Finset V} {u v : V}
    (huv : u ≠ v) (p : TripleOn V → ℝ≥0) :
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
          localizedRootedThreatRemainder z)
        p ∅ ≤
      U.card + ∑ z : LocalizedNonemptyRootedThreatWitness V q B u v U,
        setWeight p (localizedRootedThreatRemainder z.1) := by
  rw [extensionWeight_localizedRootedThreat_empty_eq_empty_add_nonempty]
  exact add_le_add
    (sum_localizedEmptyRootedThreatWeight_le_level huv p) le_rfl

/-- The empty-remainder summand in the preceding decomposition has weight at
most six. -/
theorem sum_localizedEmptyRootedThreatWeight_le_six
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V}
    {X U : Finset V} {u v : V} (huv : u ≠ v)
    (huvH : ¬ H.Adj u v)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (p : TripleOn V → ℝ≥0) :
    (∑ z : LocalizedEmptyRootedThreatWitness V q B u v U,
      setWeight p (localizedRootedThreatRemainder z.1)) ≤ 6 := by
  calc
    (∑ z : LocalizedEmptyRootedThreatWitness V q B u v U,
        setWeight p (localizedRootedThreatRemainder z.1)) =
        Fintype.card (LocalizedEmptyRootedThreatWitness V q B u v U) := by
      calc
        (∑ z : LocalizedEmptyRootedThreatWitness V q B u v U,
            setWeight p (localizedRootedThreatRemainder z.1)) =
            ∑ _z : LocalizedEmptyRootedThreatWitness V q B u v U,
              (1 : ℝ≥0) := by
          apply Finset.sum_congr rfl
          intro z _hz
          rw [z.2]
          simp [setWeight]
        _ = Fintype.card
            (LocalizedEmptyRootedThreatWitness V q B u v U) := by
          simp
    _ ≤ 6 := by
      exact_mod_cast card_localizedEmptyRootedThreatWitness_le_six
        huv huvH hsep hroot

/-- The full empty-root extension weight is six plus only the contribution
of nonempty remainders. -/
theorem extensionWeight_localizedRootedThreat_empty_le_six_add_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V}
    {X U : Finset V} {u v : V} (huv : u ≠ v)
    (huvH : ¬ H.Adj u v)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (p : TripleOn V → ℝ≥0) :
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
          localizedRootedThreatRemainder z)
        p ∅ ≤
      6 + ∑ z : LocalizedNonemptyRootedThreatWitness V q B u v U,
        setWeight p (localizedRootedThreatRemainder z.1) := by
  rw [extensionWeight_localizedRootedThreat_empty_eq_empty_add_nonempty]
  exact add_le_add
    (sum_localizedEmptyRootedThreatWeight_le_six huv huvH hsep hroot p)
    le_rfl

/-- The bounded set of possible missing third vertices above a fixed
remainder, obtained from the padded absorber's vertex-root candidates. -/
def localizedRootedThreatThirdVertexSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (candidates : V → Finset V) (R : TripleSystemOn V) (u v : V) :
    Finset V :=
  verticesOn R ∪
    ((verticesOn R ∪ {u, v}).biUnion candidates)

/-- Root localization and level separation put every missing third vertex in
the preceding bounded set. -/
lemma localizedRootedThreat_thirdVertex_mem_boundedSet
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {u v : V}
    (huv : u ≠ v)
    (hsep : AbsorberSeparatedLevel H X B U)
    (candidates : V → Finset V)
    (hlocal : ∀ S ∈ absorberErdosForbiddenConfigurationsOn q B,
      ∀ T ∈ S, ∀ x ∈ X, x ∈ T.1 →
        x ∈ verticesOn (S.erase T) ∨
          ∃ y ∈ verticesOn (S.erase T) ∪ T.1.erase x,
            x ∈ candidates y)
    (z : LocalizedRootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v U) :
    Classical.choose z.2 ∈ localizedRootedThreatThirdVertexSet candidates
      (localizedRootedThreatRemainder z) u v := by
  let x : V := Classical.choose z.2
  have hx := Classical.choose_spec z.2
  by_cases hxX : x ∈ X
  · have hloc := hlocal z.1.1.1 z.1.2.1 z.1.1.2 z.1.2.2.1 x hxX hx.1
    rcases hloc with hrem | ⟨y, hy, hxy⟩
    · exact mem_union_left _ hrem
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨y, ?_, hxy⟩
      rcases mem_union.mp hy with hyrem | hyT
      · exact mem_union_left _ hyrem
      · apply mem_union_right
        have hxu : x ≠ u := hx.2.2.1
        have hxv : x ≠ v := hx.2.2.2
        let w : ThirdVertex u v := ⟨x, hxu, hxv⟩
        have hT : thirdVertexTriple huv w =
            z.1.1.2 := by
          exact thirdVertexTriple_eq_of_mem
            huv z.1.1.2
              z.1.2.2.2.1 z.1.2.2.2.2 hx.1 hxu hxv
        rw [← hT] at hyT
        simp only [thirdVertexTriple, tripleOfThree, mem_erase,
          mem_insert, mem_singleton] at hyT
        rcases hyT.2 with rfl | rfl | h
        · simp
        · simp
        · exact (hyT.1 h).elim
  · exact mem_union_left _
      (localizedRootedThreat_thirdVertex_mem_remainder_of_not_mem_root
        hsep z hxX)

/-- The fiber of the remainder map above one fixed outside family. -/
abbrev LocalizedRootedThreatRemainderFiber
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V) (U : Finset V)
    (R : TripleSystemOn V) :=
  {z : LocalizedRootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v U //
    localizedRootedThreatRemainder z = R}

def localizedRootedThreatFiberThirdVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {u v : V} {R : TripleSystemOn V}
    (huv : u ≠ v)
    (hsep : AbsorberSeparatedLevel H X B U)
    (candidates : V → Finset V)
    (hlocal : ∀ S ∈ absorberErdosForbiddenConfigurationsOn q B,
      ∀ T ∈ S, ∀ x ∈ X, x ∈ T.1 →
        x ∈ verticesOn (S.erase T) ∨
          ∃ y ∈ verticesOn (S.erase T) ∪ T.1.erase x,
            x ∈ candidates y)
    (z : LocalizedRootedThreatRemainderFiber V q B u v U R) :
    {x // x ∈ localizedRootedThreatThirdVertexSet candidates R u v} :=
  ⟨Classical.choose z.1.2, by
    simpa only [z.2] using
      (localizedRootedThreat_thirdVertex_mem_boundedSet
        huv hsep candidates hlocal z.1)⟩

lemma localizedRootedThreatFiberThirdVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {u v : V} {R : TripleSystemOn V}
    (huv : u ≠ v)
    (hsep : AbsorberSeparatedLevel H X B U)
    (candidates : V → Finset V)
    (hlocal : ∀ S ∈ absorberErdosForbiddenConfigurationsOn q B,
      ∀ T ∈ S, ∀ x ∈ X, x ∈ T.1 →
        x ∈ verticesOn (S.erase T) ∨
          ∃ y ∈ verticesOn (S.erase T) ∪ T.1.erase x,
            x ∈ candidates y) :
    Function.Injective
      (localizedRootedThreatFiberThirdVertex huv hsep candidates hlocal :
        LocalizedRootedThreatRemainderFiber V q B u v U R →
          {x // x ∈ localizedRootedThreatThirdVertexSet candidates R u v}) := by
  intro z z' hzz'
  have hx : Classical.choose z.1.2 = Classical.choose z'.1.2 :=
    congrArg Subtype.val hzz'
  have hzdata := Classical.choose_spec z.1.2
  have hz'data := Classical.choose_spec z'.1.2
  let w : ThirdVertex u v :=
    ⟨Classical.choose z.1.2, hzdata.2.2.1, hzdata.2.2.2⟩
  let w' : ThirdVertex u v :=
    ⟨Classical.choose z'.1.2, hz'data.2.2.1, hz'data.2.2.2⟩
  have hww' : w = w' := by
    apply Subtype.ext
    exact hx
  have hT : z.1.1.1.2 = z'.1.1.1.2 := by
    calc
      z.1.1.1.2 = thirdVertexTriple huv w :=
        (thirdVertexTriple_eq_of_mem huv z.1.1.1.2
          z.1.1.2.2.2.1 z.1.1.2.2.2.2 hzdata.1
          hzdata.2.2.1 hzdata.2.2.2).symm
      _ = thirdVertexTriple huv w' := congrArg _ hww'
      _ = z'.1.1.1.2 :=
        thirdVertexTriple_eq_of_mem huv z'.1.1.1.2
          z'.1.1.2.2.2.1 z'.1.1.2.2.2.2 hz'data.1
          hz'data.2.2.1 hz'data.2.2.2
  have hS : z.1.1.1.1 = z'.1.1.1.1 := by
    calc
      z.1.1.1.1 = insert z.1.1.1.2
          (localizedRootedThreatRemainder z.1) := by
        exact (insert_erase z.1.1.2.2.1).symm
      _ = insert z.1.1.1.2 R := by rw [z.2]
      _ = insert z'.1.1.1.2 R := by rw [hT]
      _ = insert z'.1.1.1.2
          (localizedRootedThreatRemainder z'.1) := by rw [z'.2]
      _ = z'.1.1.1.1 := insert_erase z'.1.1.2.2.1
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hS hT

/-- A fixed remainder has only linearly many rooted witnesses, independently
of the ambient order and of the absorber bank size. -/
theorem card_localizedRootedThreatRemainderFiber_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {u v : V} (huv : u ≠ v) (R : TripleSystemOn V)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hrootLocal : HasPaddedAbsorberRootLocalization q X B) :
    Fintype.card (LocalizedRootedThreatRemainderFiber V q B u v U R) ≤
      45 * R.card + 28 := by
  obtain ⟨candidates, hcandidates, hlocal⟩ := hrootLocal
  let A := verticesOn R
  let D := A ∪ {u, v}
  have hA : A.card ≤ 3 * R.card := by
    calc
      A.card ≤ ∑ T ∈ R, T.1.card := card_biUnion_le
      _ = ∑ _T ∈ R, 3 := by
        apply sum_congr rfl
        intro T _hT
        exact T.2
      _ = 3 * R.card := by simp [mul_comm]
  have hD : D.card ≤ A.card + 2 := by
    calc
      D.card ≤ A.card + ({u, v} : Finset V).card := card_union_le _ _
      _ ≤ A.card + 2 := by
        have hp : ({u, v} : Finset V).card ≤ 2 := by
          calc
            ({u, v} : Finset V).card ≤ ({v} : Finset V).card + 1 :=
              card_insert_le _ _
            _ = 2 := by simp
        omega
  have hC : (D.biUnion candidates).card ≤ 14 * D.card := by
    calc
      (D.biUnion candidates).card ≤ ∑ y ∈ D, (candidates y).card :=
        card_biUnion_le
      _ ≤ ∑ _y ∈ D, 14 := by
        apply sum_le_sum
        intro y _hy
        exact hcandidates y
      _ = 14 * D.card := by simp [mul_comm]
  calc
    Fintype.card (LocalizedRootedThreatRemainderFiber V q B u v U R) ≤
        Fintype.card
          {x // x ∈ localizedRootedThreatThirdVertexSet candidates R u v} :=
      Fintype.card_le_of_injective
        (localizedRootedThreatFiberThirdVertex huv hsep candidates hlocal)
        (localizedRootedThreatFiberThirdVertex_injective
          huv hsep candidates hlocal)
    _ = (localizedRootedThreatThirdVertexSet candidates R u v).card :=
      Fintype.card_coe _
    _ ≤ A.card + (D.biUnion candidates).card := by
      exact card_union_le _ _
    _ ≤ (3 * R.card) + 14 * (A.card + 2) := by omega
    _ ≤ (3 * R.card) + 14 * (3 * R.card + 2) := by omega
    _ = 45 * R.card + 28 := by ring

end

end Erdos207
