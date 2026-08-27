/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedNewRootedBlocker
import ErdosProblems.Erdos207.LocalizedRootedThreatExtraction
import ErdosProblems.Erdos207.FiniteJointBind

/-!
# Probability bounds for newly activated localized rooted obstructions

At a stage beginning with `Pold`, a relevant obstruction has a nonempty
remainder outside `Pold`.  Keeping this nonemptiness in the witness type is
essential: witnesses already active over `Pold` cannot block a triangle that
was available at the beginning of the stage.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Uniform moment/Markov tail used for newly activated localized rooted
configurations. -/
def newLocalizedRootedTail
    (V : Type*) [Fintype V] [DecidableEq V]
    (C κ : ℝ≥0) (r k s : ℕ) : ℝ≥0 :=
  (Fintype.card (DistinctPair V) : ℝ≥0) *
    ((C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) /
      (r + 1 : ℝ≥0) ^ s)

/-- A localized rooted witness with at least one triangle outside `Pold`. -/
abbrev LocalizedNewRootedThreatWitness
    (V : Type*) [DecidableEq V] (F : ForbiddenFamilyOn V)
    (Pold : TripleSystemOn V) (u v : V) (U : Finset V) :=
  {z : LocalizedRootedThreatWitness V F u v U //
    (localizedRootedThreatRemainder z \ Pold).Nonempty}

/-- The genuinely new part of a localized rooted remainder. -/
def localizedNewRootedThreatRemainder
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {Pold : TripleSystemOn V} {u v : V} {U : Finset V}
    (z : LocalizedNewRootedThreatWitness V F Pold u v U) :
    TripleSystemOn V :=
  localizedRootedThreatRemainder z.1 \ Pold

/-- New witnesses whose outside-`Pold` remainders are supplied by `R`. -/
noncomputable def activeLocalizedNewRootedThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Pold R : TripleSystemOn V)
    (u v : V) (U : Finset V) :
    Finset (LocalizedNewRootedThreatWitness V F Pold u v U) := by
  classical
  exact univ.filter fun z ↦ localizedNewRootedThreatRemainder z ⊆ R

@[simp]
lemma mem_activeLocalizedNewRootedThreatWitnesses_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold R : TripleSystemOn V}
    {u v : V} {U : Finset V}
    {z : LocalizedNewRootedThreatWitness V F Pold u v U} :
    z ∈ activeLocalizedNewRootedThreatWitnesses F Pold R u v U ↔
      localizedNewRootedThreatRemainder z ⊆ R := by
  classical
  simp [activeLocalizedNewRootedThreatWitnesses]

/-- Every newly activated configuration is represented by a genuinely-new
localized witness.  We deliberately forget the extra requirement that its
missing triangle lies in `A`, since forgetting it only enlarges the family. -/
lemma rootedNewActive_subset_image_activeLocalizedNewWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold R A : TripleSystemOn V}
    {u v : V} {U : Finset V} :
    rootedNewActiveForbiddenConfigurationsIn
        F Pold (Pold ∪ R) A u v U ⊆
      (activeLocalizedNewRootedThreatWitnesses
        F Pold R u v U).image (fun z ↦ z.1.1.1.1) := by
  classical
  intro C hC
  obtain ⟨hCF, T, hTC, _hTA, huT, hvT, hthird, hrem, hnotOld⟩ :=
    mem_rootedNewActiveForbiddenConfigurationsIn_iff.mp hC
  let z : RootedThreatWitness V F u v :=
    ⟨(C, T), hCF, hTC, huT, hvT⟩
  let zU : LocalizedRootedThreatWitness V F u v U := ⟨z, hthird⟩
  have hnewNonempty :
      (localizedRootedThreatRemainder zU \ Pold).Nonempty := by
    exact sdiff_nonempty.mpr hnotOld
  let zNew : LocalizedNewRootedThreatWitness V F Pold u v U :=
    ⟨zU, hnewNonempty⟩
  apply mem_image.mpr
  refine ⟨zNew, mem_activeLocalizedNewRootedThreatWitnesses_iff.mpr ?_, rfl⟩
  intro S hS
  have hSrem : S ∈ C.erase T := (mem_sdiff.mp hS).1
  have hSPoldR := hrem hSrem
  exact (mem_union.mp hSPoldR).resolve_left (mem_sdiff.mp hS).2

/-- Newly activated configurations are dominated by the selected count of
their nonempty relative remainders. -/
lemma rootedNewActive_count_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Pold R A : TripleSystemOn V)
    (u v : V) (U : Finset V) :
    ((rootedNewActiveForbiddenConfigurationsIn
        F Pold (Pold ∪ R) A u v U).card : ℝ≥0) ≤
      selectedCount
        (fun z : LocalizedNewRootedThreatWitness V F Pold u v U ↦
          localizedNewRootedThreatRemainder z) R := by
  classical
  calc
    ((rootedNewActiveForbiddenConfigurationsIn
        F Pold (Pold ∪ R) A u v U).card : ℝ≥0) ≤
        (((activeLocalizedNewRootedThreatWitnesses
          F Pold R u v U).image (fun z ↦ z.1.1.1.1)).card : ℝ≥0) := by
      exact_mod_cast card_le_card
        (rootedNewActive_subset_image_activeLocalizedNewWitnesses
          (F := F) (Pold := Pold) (R := R) (A := A)
          (u := u) (v := v) (U := U))
    _ ≤ ((activeLocalizedNewRootedThreatWitnesses
          F Pold R u v U).card : ℝ≥0) := by
      exact_mod_cast card_image_le
    _ = selectedCount
        (fun z : LocalizedNewRootedThreatWitness V F Pold u v U ↦
          localizedNewRootedThreatRemainder z) R := by
      unfold selectedCount activeLocalizedNewRootedThreatWitnesses
      simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
      apply sum_congr rfl
      intro z _hz
      by_cases h : localizedNewRootedThreatRemainder z ⊆ R <;> simp [h]

/-- Relative remainders retain the usual `k-1` cardinality bound. -/
lemma card_localizedNewRootedThreatRemainder_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold : TripleSystemOn V}
    {u v : V} {U : Finset V} {k : ℕ}
    (hcard : ∀ C ∈ F, C.card ≤ k)
    (z : LocalizedNewRootedThreatWitness V F Pold u v U) :
    (localizedNewRootedThreatRemainder z).card ≤ k - 1 := by
  exact (card_le_card sdiff_subset).trans
    (card_localizedRootedThreatRemainder_le hcard z.1)

/-- Filtering to nonempty relative remainders can only decrease every
extension weight. -/
lemma localizedNewRootedThreatRemainder_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold : TripleSystemOn V}
    {u v : V} {U : Finset V} {π : TripleOn V → ℝ≥0} {κ : ℝ≥0}
    (hκ : HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V F u v U ↦
        localizedRootedThreatRemainder z \ Pold) π κ) :
    HasExtensionBound
      (fun z : LocalizedNewRootedThreatWitness V F Pold u v U ↦
        localizedNewRootedThreatRemainder z) π κ := by
  classical
  intro Q
  apply le_trans ?_ (hκ Q)
  unfold extensionWeight localizedNewRootedThreatRemainder
  let f : LocalizedRootedThreatWitness V F u v U → ℝ≥0 := fun z ↦
    if Q ⊆ localizedRootedThreatRemainder z \ Pold then
      setWeight π ((localizedRootedThreatRemainder z \ Pold) \ Q)
    else 0
  change (∑ z : LocalizedNewRootedThreatWitness V F Pold u v U,
    f z.1) ≤ ∑ z : LocalizedRootedThreatWitness V F u v U, f z
  let pred : LocalizedRootedThreatWitness V F u v U → Prop := fun z ↦
    (localizedRootedThreatRemainder z \ Pold).Nonempty
  calc
    (∑ z : LocalizedNewRootedThreatWitness V F Pold u v U, f z.1) ≤
        (∑ z : {z // pred z}, f z.1) +
          ∑ z : {z // ¬ pred z}, f z.1 := by
      change (∑ z : {z // pred z}, f z.1) ≤ _
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ zero_le)
    _ = ∑ z : LocalizedRootedThreatWitness V F u v U, f z :=
      Fintype.sum_subtype_add_sum_subtype pred f

/-- Moment bound for the number of newly activated localized rooted
configurations over a fixed pre-stage packing. -/
theorem rootedNewActiveInMomentBound
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (Pold A : TripleSystemOn V)
    (u v : V) (U : Finset V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0) {k s : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : HasExtensionBound
      (fun z : LocalizedNewRootedThreatWitness V F Pold u v U ↦
        localizedNewRootedThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦
      ((rootedNewActiveForbiddenConfigurationsIn
        F Pold (Pold ∪ R ω) A u v U).card : ℝ≥0) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s) := by
  calc
    L.expectation (fun ω ↦
        ((rootedNewActiveForbiddenConfigurationsIn
          F Pold (Pold ∪ R ω) A u v U).card : ℝ≥0) ^ s) ≤
        L.expectation (fun ω ↦
          (selectedCount
            (fun z : LocalizedNewRootedThreatWitness V F Pold u v U ↦
              localizedNewRootedThreatRemainder z) (R ω)) ^ s) := by
      apply L.expectation_mono
      intro ω
      exact pow_le_pow_left'
        (rootedNewActive_count_le_selectedCount F Pold (R ω) A u v U) s
    _ ≤ C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s) := by
      apply configurationMomentBound L
        (fun z : LocalizedNewRootedThreatWitness V F Pold u v U ↦
          localizedNewRootedThreatRemainder z) R π C κ
      · exact card_localizedNewRootedThreatRemainder_le hcard
      · exact hκ
      · exact hjoint

/-- Markov tail bound for a fixed root and a fixed pre-stage packing. -/
theorem rootedNewActiveIn_probability_ge_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (Pold A : TripleSystemOn V)
    (u v : V) (U : Finset V)
    (π : TripleOn V → ℝ≥0) (C κ a : ℝ≥0) {k s : ℕ}
    (ha : 0 < a)
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : HasExtensionBound
      (fun z : LocalizedNewRootedThreatWitness V F Pold u v U ↦
        localizedNewRootedThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦ a ≤
      (rootedNewActiveForbiddenConfigurationsIn
        F Pold (Pold ∪ R ω) A u v U).card) ≤
      (C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) / a ^ s := by
  have hmono : L.probability (fun ω ↦ a ≤
      (rootedNewActiveForbiddenConfigurationsIn
        F Pold (Pold ∪ R ω) A u v U).card) ≤
      L.probability (fun ω ↦ a ^ s ≤
        ((rootedNewActiveForbiddenConfigurationsIn
          F Pold (Pold ∪ R ω) A u v U).card : ℝ≥0) ^ s) := by
    apply L.probability_mono
    intro ω hω
    exact pow_le_pow_left' hω s
  refine hmono.trans ?_
  apply (L.probability_le_expectation_div
    (fun ω ↦ ((rootedNewActiveForbiddenConfigurationsIn
      F Pold (Pold ∪ R ω) A u v U).card : ℝ≥0) ^ s)
    (pow_pos ha s)).trans
  exact (div_le_div_iff_of_pos_right (pow_pos ha s)).2
    (rootedNewActiveInMomentBound L R F Pold A u v U π C κ
      hcard hκ hjoint)

/-- A moment bound followed by a union bound over ordered distinct pairs
controls all newly activated localized rooted obstructions at once. -/
theorem probability_not_newRootedActiveCapsGoodIn_le_of_moment
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (Pold A : TripleSystemOn V)
    (U : Finset V) (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0)
    (r : ℕ) {k s : ℕ}
    (hcard : ∀ T ∈ F, T.card ≤ k)
    (hκ : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : LocalizedNewRootedThreatWitness
            V F Pold e.1.1 e.1.2 U ↦
          localizedNewRootedThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦
      ¬ NewRootedActiveCapsGoodIn F Pold (Pold ∪ R ω) A U r) ≤
      newLocalizedRootedTail V C κ r k s := by
  let Bad : DistinctPair V → Ω → Prop := fun e ω ↦
    (r + 1 : ℝ≥0) ≤
      (rootedNewActiveForbiddenConfigurationsIn
        F Pold (Pold ∪ R ω) A e.1.1 e.1.2 U).card
  have hpoint : ∀ e : DistinctPair V,
      L.probability (Bad e) ≤
        (C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) /
          (r + 1 : ℝ≥0) ^ s := by
    intro e
    exact rootedNewActiveIn_probability_ge_le
      L R F Pold A e.1.1 e.1.2 U π C κ (r + 1) (by positivity)
        hcard (hκ e) hjoint
  calc
    L.probability (fun ω ↦
        ¬ NewRootedActiveCapsGoodIn F Pold (Pold ∪ R ω) A U r) ≤
        L.probability (fun ω ↦ ∃ e : DistinctPair V, Bad e ω) := by
      apply L.probability_mono
      intro ω hbad
      unfold NewRootedActiveCapsGoodIn at hbad
      push Not at hbad
      obtain ⟨u, v, huv, hlarge⟩ := hbad
      let e : DistinctPair V := ⟨(u, v), huv⟩
      refine ⟨e, ?_⟩
      dsimp only [Bad, e]
      exact_mod_cast (Nat.add_one_le_iff.mpr hlarge)
    _ ≤ ∑ e : DistinctPair V, L.probability (Bad e) := by
      simpa using L.probability_exists_le
        (univ : Finset (DistinctPair V)) Bad
    _ ≤ ∑ _e : DistinctPair V,
        (C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) /
          (r + 1 : ℝ≥0) ^ s := by
      apply sum_le_sum
      intro e _he
      exact hpoint e
    _ = newLocalizedRootedTail V C κ r k s := by
      unfold newLocalizedRootedTail
      simp only [sum_const, card_univ, nsmul_eq_mul]

/-- Fiberwise newly-activated moment estimates pass through a dependent
joint law.  This is the form used for the raw internal sampler: `Pold` may
depend on the preliminary outcome, while the inclusion estimate for the
genuinely new internal family is conditional on that outcome. -/
theorem FiniteLaw.jointBind_probability_not_newRootedActiveCapsGoodIn_le
    {Ω Ξ V : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype Ξ] [DecidableEq Ξ] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (added : Ω → Ξ → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (Pold A : Ω → TripleSystemOn V)
    (U : Finset V) (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0)
    (r : ℕ) {k s : ℕ}
    (hcard : ∀ T ∈ F, T.card ≤ k)
    (hκ : ∀ ω, 0 < L.mass ω → ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : LocalizedNewRootedThreatWitness
            V F (Pold ω) e.1.1 e.1.2 U ↦
          localizedNewRootedThreatRemainder z) π κ)
    (hjoint : ∀ ω, 0 < L.mass ω → ∀ T : TripleSystemOn V,
      T.card ≤ s * (k - 1) →
      (K ω).probability (fun ξ ↦ T ⊆ added ω ξ) ≤
        C * setWeight π T) :
    (L.jointBind K).probability (fun z ↦
      ¬ NewRootedActiveCapsGoodIn F (Pold z.1)
        (Pold z.1 ∪ added z.1 z.2) (A z.1) U r) ≤
      newLocalizedRootedTail V C κ r k s := by
  let epsilon : ℝ≥0 := newLocalizedRootedTail V C κ r k s
  let Bad : Ω → Ξ → Prop := fun ω ξ ↦
    ¬ NewRootedActiveCapsGoodIn F (Pold ω)
      (Pold ω ∪ added ω ξ) (A ω) U r
  have hfiber : ∀ ω, 0 < L.mass ω →
      (K ω).probability (Bad ω) ≤ epsilon := by
    intro ω hω
    exact probability_not_newRootedActiveCapsGoodIn_le_of_moment
      (K ω) (added ω) F (Pold ω) (A ω) U π C κ r hcard
        (hκ ω hω) (hjoint ω hω)
  have hbound := L.jointBind_probability_and_le_on_support K
    (fun _ω ↦ True) Bad epsilon (fun ω hω _htrue ↦ hfiber ω hω)
  simpa only [true_and, FiniteLaw.probability_true, mul_one, Bad, epsilon]
    using hbound

end

end Erdos207
