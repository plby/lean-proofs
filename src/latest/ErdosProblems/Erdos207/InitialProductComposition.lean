/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialSparsificationStrongLaw
import ErdosProblems.Erdos207.FiniteJointBind
import ErdosProblems.Erdos207.GreedySelectedUncovered

/-!
# Composing initial selected--uncovered product phases

A long initial sparsification is naturally split into a bounded number of
well-controlled phases.  The event for the union of the old and new selected
families is partitioned according to the triangles already supplied by the
old phase.  Uncovered edges must survive both phases.  The theorem below is
the exact finite probability identity needed before any scalar estimates are
inserted.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

private def initialSelectedUncoveredEvent
    {Omega V : Type*} [DecidableEq V]
    (selected : Omega → TripleSystemOn V)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) (omega : Omega) : Prop :=
  Q ⊆ selected omega ∧
    ∀ e ∈ E, e ∉ (coveredGraph (selected omega)).edgeSet

private lemma initialSelectedUncoveredEvent_union_partition
    {Omega Xi V : Type*} [Fintype V] [DecidableEq V]
    (old : Omega → TripleSystemOn V)
    (added : Omega → Xi → TripleSystemOn V)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V))
    (z : Omega × Xi)
    (hz : initialSelectedUncoveredEvent
      (fun z : Omega × Xi ↦ old z.1 ∪ added z.1 z.2) Q E z) :
    ∃ S ∈ Q.powerset,
      initialSelectedUncoveredEvent old S E z.1 ∧
      initialSelectedUncoveredEvent (added z.1) (Q \ S) E z.2 := by
  classical
  let S := Q ∩ old z.1
  refine ⟨S, mem_powerset.mpr inter_subset_left, ?_, ?_⟩
  · refine ⟨inter_subset_right, ?_⟩
    intro e heE heOld
    exact hz.2 e heE
      (SimpleGraph.edgeSet_mono (coveredGraph_mono subset_union_left) heOld)
  · refine ⟨?_, ?_⟩
    · intro T hT
      obtain ⟨hTQ, hTnotS⟩ := mem_sdiff.mp hT
      have hTunion := hz.1 hTQ
      rw [mem_union] at hTunion
      exact hTunion.resolve_left fun hTOld ↦
        hTnotS (mem_inter.mpr ⟨hTQ, hTOld⟩)
    · intro e heE heAdded
      exact hz.2 e heE
        (SimpleGraph.edgeSet_mono (coveredGraph_mono subset_union_right)
          heAdded)

/-- Exact powerset convolution for two consecutive initial product phases.
The conditional estimate may depend on both the newly prescribed triangle
family and the common family of edges required to survive. -/
theorem FiniteLaw.jointBind_probability_initialProduct_union_le
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (old : Omega → TripleSystemOn V)
    (added : Omega → Xi → TripleSystemOn V)
    (newBound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0)
    (hnew : ∀ omega Q E,
      (K omega).probability
          (initialSelectedUncoveredEvent (added omega) Q E) ≤
        newBound Q E)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    (L.jointBind K).probability
        (initialSelectedUncoveredEvent
          (fun z ↦ old z.1 ∪ added z.1 z.2) Q E) ≤
      ∑ S ∈ Q.powerset,
        newBound (Q \ S) E *
          L.probability (initialSelectedUncoveredEvent old S E) := by
  classical
  let Event : TripleSystemOn V → (Omega × Xi) → Prop := fun S z ↦
    initialSelectedUncoveredEvent old S E z.1 ∧
      initialSelectedUncoveredEvent (added z.1) (Q \ S) E z.2
  calc
    (L.jointBind K).probability
        (initialSelectedUncoveredEvent
          (fun z ↦ old z.1 ∪ added z.1 z.2) Q E) ≤
        (L.jointBind K).probability
          (fun z ↦ ∃ S ∈ Q.powerset, Event S z) := by
      apply (L.jointBind K).probability_mono
      intro z hz
      simpa only [Event] using
        initialSelectedUncoveredEvent_union_partition old added Q E z hz
    _ ≤ ∑ S ∈ Q.powerset, (L.jointBind K).probability (Event S) :=
      (L.jointBind K).probability_exists_le Q.powerset Event
    _ ≤ ∑ S ∈ Q.powerset,
        newBound (Q \ S) E *
          L.probability (initialSelectedUncoveredEvent old S E) := by
      apply sum_le_sum
      intro S hS
      apply L.jointBind_probability_and_le K
        (initialSelectedUncoveredEvent old S E)
        (fun omega xi ↦
          initialSelectedUncoveredEvent (added omega) (Q \ S) E xi)
        (newBound (Q \ S) E)
      intro omega _hold
      exact hnew omega (Q \ S) E

/-- Two initial product phases compose.  Survival parameters multiply, the
powerset partition costs a factor two in the strong constant, and the
additive errors combine by the elementary product formula.  As in the
one-phase bounded-sharp theorem, prescriptions above `Kcut` are paid for by
the amplified error term. -/
theorem IsInitialProductBound.jointBind_union_of_conditional
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {old : Omega → TripleSystemOn V}
    {added : Omega → Xi → TripleSystemOn V}
    {p₁ p₂ C₁ C₂ b₁ b₂ : ℝ≥0} {Kcut : ℕ}
    (hold : IsInitialProductBound L old p₁ C₁ b₁)
    (hnew : ∀ omega Q E,
      (K omega).probability
          (initialSelectedUncoveredEvent (added omega) Q E) ≤
        C₂ ^ (Q.card + E.card) *
          (p₂ ^ E.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b₂))
    (hp₁ : p₁ ≤ 1) (hp₂ : p₂ ≤ 1)
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (hlarge : 1 ≤ (2 * C₁ * C₂) ^ (Kcut + 1) *
      (b₁ + b₂ + b₁ * b₂)) :
    IsInitialProductBound (L.jointBind K)
      (fun z ↦ old z.1 ∪ added z.1 z.2)
      (p₁ * p₂) (2 * C₁ * C₂) (b₁ + b₂ + b₁ * b₂) := by
  classical
  intro Q E
  let Ninv : ℝ≥0 := (Fintype.card V : ℝ≥0)⁻¹
  let b' : ℝ≥0 := b₁ + b₂ + b₁ * b₂
  let C' : ℝ≥0 := 2 * C₁ * C₂
  by_cases hsmall : Q.card + E.card ≤ Kcut
  · let newBound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0 :=
      fun R B ↦ C₂ ^ (R.card + B.card) *
        (p₂ ^ B.card * Ninv ^ R.card + b₂)
    have hconv := L.jointBind_probability_initialProduct_union_le K old
      added newBound (fun omega R B ↦ by
        simpa only [newBound, Ninv] using hnew omega R B) Q E
    apply hconv.trans
    calc
      ∑ S ∈ Q.powerset,
          newBound (Q \ S) E *
            L.probability (initialSelectedUncoveredEvent old S E) ≤
          ∑ _S ∈ Q.powerset,
            (C₁ * C₂) ^ (Q.card + E.card) *
              ((p₁ * p₂) ^ E.card * Ninv ^ Q.card + b') := by
        apply sum_le_sum
        intro S hS
        have hSQ : S ⊆ Q := mem_powerset.mp hS
        have hScard : S.card ≤ Q.card := card_le_card hSQ
        have hcard : (Q \ S).card + S.card = Q.card := by
          rw [card_sdiff_of_subset hSQ]
          omega
        have hOld := hold S E
        have hNinv : Ninv ≤ 1 := by
          by_cases hV : Fintype.card V = 0
          · simp [Ninv, hV]
          · apply inv_le_one_of_one_le₀
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hV)
        have hA : p₂ ^ E.card * Ninv ^ (Q \ S).card ≤ 1 := by
          calc
            p₂ ^ E.card * Ninv ^ (Q \ S).card ≤ 1 * 1 :=
              mul_le_mul (pow_le_one₀ zero_le hp₂)
                (pow_le_one₀ zero_le hNinv) zero_le zero_le
            _ = 1 := by simp
        have hB : p₁ ^ E.card * Ninv ^ S.card ≤ 1 := by
          calc
            p₁ ^ E.card * Ninv ^ S.card ≤ 1 * 1 :=
              mul_le_mul (pow_le_one₀ zero_le hp₁)
                (pow_le_one₀ zero_le hNinv) zero_le zero_le
            _ = 1 := by simp
        have hbase :
            (p₂ ^ E.card * Ninv ^ (Q \ S).card + b₂) *
                (p₁ ^ E.card * Ninv ^ S.card + b₁) ≤
              (p₁ * p₂) ^ E.card * Ninv ^ Q.card + b' := by
          have hAb₁ :
              (p₂ ^ E.card * Ninv ^ (Q \ S).card) * b₁ ≤ b₁ := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hA zero_le
          have hb₂B :
              b₂ * (p₁ ^ E.card * Ninv ^ S.card) ≤ b₂ := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hB zero_le
          calc
            (p₂ ^ E.card * Ninv ^ (Q \ S).card + b₂) *
                (p₁ ^ E.card * Ninv ^ S.card + b₁) =
                (p₂ ^ E.card * Ninv ^ (Q \ S).card) *
                    (p₁ ^ E.card * Ninv ^ S.card) +
                  (p₂ ^ E.card * Ninv ^ (Q \ S).card) * b₁ +
                  b₂ * (p₁ ^ E.card * Ninv ^ S.card) + b₂ * b₁ := by
              ring
            _ ≤ (p₂ ^ E.card * Ninv ^ (Q \ S).card) *
                    (p₁ ^ E.card * Ninv ^ S.card) +
                  b₁ + b₂ + b₁ * b₂ := by
              exact add_le_add
                (add_le_add
                  (add_le_add le_rfl hAb₁)
                  hb₂B)
                (by rw [mul_comm])
            _ = (p₁ * p₂) ^ E.card * Ninv ^ Q.card + b' := by
              dsimp only [b']
              have hNpow :
                  Ninv ^ (Q \ S).card * Ninv ^ S.card = Ninv ^ Q.card := by
                rw [← pow_add, hcard]
              calc
                p₂ ^ E.card * Ninv ^ (Q \ S).card *
                        (p₁ ^ E.card * Ninv ^ S.card) +
                      b₁ + b₂ + b₁ * b₂ =
                    (p₁ ^ E.card * p₂ ^ E.card) *
                        (Ninv ^ (Q \ S).card * Ninv ^ S.card) +
                      b₁ + b₂ + b₁ * b₂ := by ring
                _ = (p₁ * p₂) ^ E.card * Ninv ^ Q.card +
                      (b₁ + b₂ + b₁ * b₂) := by
                    rw [hNpow, mul_pow]
                    ring
        have hconstants :
            C₂ ^ ((Q \ S).card + E.card) *
                C₁ ^ (S.card + E.card) ≤
              (C₁ * C₂) ^ (Q.card + E.card) := by
          calc
            C₂ ^ ((Q \ S).card + E.card) *
                C₁ ^ (S.card + E.card) =
                C₁ ^ (S.card + E.card) *
                  C₂ ^ ((Q \ S).card + E.card) := by ring
            _ ≤ C₁ ^ (Q.card + E.card) *
                C₂ ^ (Q.card + E.card) :=
              mul_le_mul (pow_le_pow_right₀ hC₁ (by omega))
                (pow_le_pow_right₀ hC₂ (by omega)) zero_le zero_le
            _ = (C₁ * C₂) ^ (Q.card + E.card) := by rw [mul_pow]
        calc
          newBound (Q \ S) E *
              L.probability (initialSelectedUncoveredEvent old S E) ≤
              (C₂ ^ ((Q \ S).card + E.card) *
                (p₂ ^ E.card * Ninv ^ (Q \ S).card + b₂)) *
              (C₁ ^ (S.card + E.card) *
                (p₁ ^ E.card * Ninv ^ S.card + b₁)) := by
            dsimp only [newBound]
            exact mul_le_mul (le_refl _) hOld zero_le zero_le
          _ = (C₂ ^ ((Q \ S).card + E.card) *
                C₁ ^ (S.card + E.card)) *
              ((p₂ ^ E.card * Ninv ^ (Q \ S).card + b₂) *
                (p₁ ^ E.card * Ninv ^ S.card + b₁)) := by ring
          _ ≤ (C₁ * C₂) ^ (Q.card + E.card) *
              ((p₁ * p₂) ^ E.card * Ninv ^ Q.card + b') :=
            mul_le_mul hconstants hbase zero_le zero_le
      _ = (2 : ℝ≥0) ^ Q.card *
          ((C₁ * C₂) ^ (Q.card + E.card) *
            ((p₁ * p₂) ^ E.card * Ninv ^ Q.card + b')) := by simp
      _ ≤ C' ^ (Q.card + E.card) *
          ((p₁ * p₂) ^ E.card * Ninv ^ Q.card + b') := by
        have htwo : (2 : ℝ≥0) ^ Q.card ≤ 2 ^ (Q.card + E.card) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        calc
          (2 : ℝ≥0) ^ Q.card *
              ((C₁ * C₂) ^ (Q.card + E.card) *
                ((p₁ * p₂) ^ E.card * Ninv ^ Q.card + b')) =
              (2 ^ Q.card * (C₁ * C₂) ^ (Q.card + E.card)) *
                ((p₁ * p₂) ^ E.card * Ninv ^ Q.card + b') := by ring
          _ ≤ (2 ^ (Q.card + E.card) *
                (C₁ * C₂) ^ (Q.card + E.card)) *
                ((p₁ * p₂) ^ E.card * Ninv ^ Q.card + b') := by
              exact mul_le_mul
                (mul_le_mul htwo le_rfl zero_le zero_le)
                le_rfl zero_le zero_le
          _ = C' ^ (Q.card + E.card) *
                ((p₁ * p₂) ^ E.card * Ninv ^ Q.card + b') := by
              dsimp only [C']
              rw [mul_pow, mul_pow]
              ring
  · calc
      (L.jointBind K).probability
          (initialSelectedUncoveredEvent
            (fun z ↦ old z.1 ∪ added z.1 z.2) Q E) ≤ 1 :=
        (L.jointBind K).probability_le_one _
      _ ≤ C' ^ (Q.card + E.card) * b' := by
        have hm : Kcut + 1 ≤ Q.card + E.card := by omega
        have hC' : 1 ≤ C' := by
          dsimp only [C']
          calc
            1 = 1 * 1 := by simp
            _ ≤ C₁ * C₂ := mul_le_mul hC₁ hC₂ zero_le zero_le
            _ ≤ 2 * (C₁ * C₂) := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right
                  (by norm_num : (1 : ℝ≥0) ≤ 2) zero_le
            _ = 2 * C₁ * C₂ := by ring
        have hp := pow_le_pow_right₀ hC' hm
        exact hlarge.trans (by
          dsimp only [C', b'] at hp ⊢
          exact mul_le_mul hp le_rfl zero_le zero_le)
      _ ≤ C' ^ (Q.card + E.card) *
          ((p₁ * p₂) ^ E.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b') := by
        gcongr
        exact le_add_left le_rfl

end

end Erdos207
