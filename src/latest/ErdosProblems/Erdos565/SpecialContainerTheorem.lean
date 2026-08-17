import ErdosProblems.Erdos565.SpecialContainerBridge
import ErdosProblems.Erdos565.SpecialLocalization
import ErdosProblems.Erdos565.ContainerA
import ErdosProblems.Erdos565.ContainerConsistency
import Mathlib.Tactic

/-!
# The specialised non-Janson container theorem

This module combines the canonical conditional fingerprint, the finite
Campos--Samotij container algorithm, and the fixed-container localisation
theorem.  Shared projection and parameter bridges live in
`SpecialContainerBridge`, keeping the dependency on `SpecialLocalization`
acyclic.
-/

open scoped BigOperators

namespace Erdos565
namespace SpecialContainerTheorem

open Hypergraph

variable {V U : Type*}

section CanonicalContainer

variable [Fintype V] [DecidableEq V]

/-- The deterministic Campos--Samotij container indexed only by its
fingerprint.  The representative construction and its consistency theorem
are in `ContainerConsistency`. -/
noncomputable def canonicalContainer (H : Hypergraph V) (s : ℕ) (t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (S : Finset V) : Finset V :=
  (ContainerA.algorithmSelector (V := V) t s hs ht).containerMap H S

/-- The canonical representative is independent even off the range of the
fingerprint map: in that case it is empty, and positive uniformity excludes
an empty hyperedge. -/
theorem canonicalRepresentative_independent
    (H : Hypergraph V) (s : ℕ) (t : ℝ)
    (hs : 0 < s) (ht : 0 < t)
    (hH : Hypergraph.IsUniform H s) (S : Finset V) :
    Hypergraph.IsIndependent H
      ((ContainerA.algorithmSelector (V := V) t s hs ht).representative H S) := by
  let selector := ContainerA.algorithmSelector (V := V) t s hs ht
  classical
  by_cases hS : ∃ I : Finset V,
      ContainerA.Independent H I ∧ selector.fingerprint H I = S
  · have hrep := selector.representative_spec H S hS
    exact hrep.1
  · have hrep : selector.representative H S = ∅ := by
      simp [ContainerA.Selector.representative, hS]
    rw [hrep]
    intro E hEH hEempty
    have hE : E = ∅ := Finset.subset_empty.mp hEempty
    have hcard := hH E hEH
    rw [hE] at hcard
    simp at hcard
    omega

/-- The rich finite-container output agrees with the fingerprint-indexed
canonical map on the fingerprint that it returns. -/
theorem finiteContainer_canonicalContainer
    (H : Hypergraph V) (s : ℕ) (t : ℝ)
    (hs : 0 < s) (ht : 0 < t)
    (htmax : t ≤ 1 / (8 * (s : ℝ) ^ 2))
    (hH : Hypergraph.IsUniform H s) (I : Finset V)
    (hI : Hypergraph.IsIndependent H I) :
    canonicalContainer H s t hs ht
        (ContainerA.finiteContainer H s t hs ht htmax hH I hI).fingerprint =
      (ContainerA.finiteContainer H s t hs ht htmax hH I hI).container := by
  unfold canonicalContainer
  exact ContainerA.Selector.algorithmSelector_containerMap_finiteContainer_fingerprint
    H I t s hs ht htmax hH hI

/-- Every nonempty canonical container has the rescaled non-Janson property
from Theorem 3.4. -/
theorem canonicalContainer_not_isJanson
    (H : Hypergraph V) (s : ℕ) {p zeta : ℝ}
    (hs : 0 < s) (hp : 0 < p) (hzeta : 0 < zeta)
    (hzeta_one : zeta ≤ 1)
    (hpmax : p / zeta ≤ 1 / (8 * (s : ℝ) ^ 2))
    (hH : Hypergraph.IsUniform H s) (S : Finset V)
    (hX : (canonicalContainer H s (p / zeta) hs
      (div_pos hp hzeta) S).Nonempty) :
    ¬ (H.restrict (canonicalContainer H s (p / zeta) hs
        (div_pos hp hzeta) S)).IsJanson p
      (zeta * p * (canonicalContainer H s (p / zeta) hs
        (div_pos hp hzeta) S).card) := by
  let selector := ContainerA.algorithmSelector (V := V)
    (p / zeta) s hs (div_pos hp hzeta)
  let I := selector.representative H S
  let hI : H.IsIndependent I :=
    canonicalRepresentative_independent H s (p / zeta) hs
      (div_pos hp hzeta) hH S
  let hHA : ContainerA.IsUniform H s := fun E hE ↦ hH E hE
  let hIA : ContainerA.Independent H I := fun E hE ↦ hI E hE
  let out := ContainerA.finiteCoverOutput H s (p / zeta) hs
    (div_pos hp hzeta) hpmax hHA I hIA
  have hout : out.container = canonicalContainer H s (p / zeta) hs
      (div_pos hp hzeta) S := by
    change (ContainerA.finiteContainer H s (p / zeta) hs
      (div_pos hp hzeta) hpmax hHA I hIA).container = _
    calc
      _ = (ContainerA.algorithmSelector (V := V) (p / zeta) s hs
          (div_pos hp hzeta)).container H I :=
        ContainerA.Selector.finiteContainer_container_eq_selector_container
          H I (p / zeta) s hs (div_pos hp hzeta) hpmax hHA hIA
      _ = canonicalContainer H s (p / zeta) hs
          (div_pos hp hzeta) S := rfl
  have houtne : out.container.Nonempty := by simpa [hout] using hX
  have hnon := out.not_isJanson_rescale hp hzeta hzeta_one houtne
  simpa [hout] using hnon

end CanonicalContainer

section Assembly

variable [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

/-- The specialised non-Janson container theorem (ACDFM Theorem 5.4), with
both fingerprint cutoffs rounded down explicitly.  All three substantive
inputs to the deterministic assembly are constructed here: the conditional
decomposition, the finite Campos--Samotij container, and the fixed-container
localisation theorem. -/
noncomputable def specializedNonJansonContainer
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    (q p R R' η : ℝ) (r s : ℕ)
    (hs : 0 < s)
    (hpar : SpecialContainer.ParameterConditions
      (Fintype.card V) s r q p R R' η)
    (hH : H.IsUniform s)
    (hF : F.IsUniform (s + 1))
    (hFJ : F.IsJanson p R')
    (hFfresh : ∀ E ∈ F, v ∉ E)
    (hπ : SpecialContainer.ProjectionConditions π H)
    (hv : ∀ x, π x ≠ v) :
    SpecialContainer.Output π v H F p (R' + η * R) R r
      (SpecialContainer.fingerprintCount (Fintype.card V)
          ⌊2 * q * Fintype.card V⌋₊ *
        SpecialContainer.fingerprintCount (Fintype.card V)
          ⌊q * Fintype.card V⌋₊) := by
  classical
  let J : Hypergraph V :=
    SpecialContainer.jansonGeneratingFamily π v H F p (R' + η * R)
  let cover : Finset V → Hypergraph V := fun T ↦ uniformizedCover q J s T
  let zeta : ℝ := containerZeta r
  let t : ℝ := p / zeta
  have hr : 2 ≤ r := hpar.2.1
  have hq : 0 < q := hpar.2.2.1
  have hq8 : q < 1 / 8 := hpar.2.2.2.1
  have hp : 0 < p := hpar.2.2.2.2.1
  have hzeta : 0 < zeta := by
    exact containerZeta_pos hr
  have hzeta_one : zeta ≤ 1 := by
    exact containerZeta_le_one hr
  have ht : 0 < t := by
    exact div_pos hp hzeta
  have htmax : t ≤ 1 / (8 * (s : ℝ) ^ 2) := by
    have hbase := parameter_p_le_containerZeta hs hpar
    apply (div_le_iff₀ hzeta).2
    simpa [t, zeta, div_eq_mul_inv, mul_comm] using hbase
  let selector := ContainerA.algorithmSelector (V := V) t s hs ht
  let ψ : Finset V → Finset V → Finset V := fun T S ↦
    if J.IsIndependent T then selector.containerMap (cover T) S else ∅
  have hassembly : SpecialContainer.AssemblyHypotheses
      π v H F q p R R' η r s
      ⌊q * Fintype.card V⌋₊ ⌊2 * q * Fintype.card V⌋₊ cover ψ := by
    refine
      { parameters := hpar
        positive_uniformity := hs
        base_uniform := hH
        available_uniform := hF
        available_janson := hFJ
        available_fresh := hFfresh
        projection := hπ
        fresh := hv
        invalidContainer := ?_
        decompose := ?_
        containerStep := ?_
        container_nonJanson := ?_
        localize := ?_ }
    · intro T S hTb hTbad
      have hTbadJ : ¬ J.IsIndependent T := by
        simpa [J] using hTbad
      simp only [ψ, if_neg hTbadJ]
    · intro I hI
      obtain ⟨T, hTcard, hTI, hTind, hcoverI⟩ :=
        exists_conditionalFingerprint_uniformized_with_seedIndependent
          q J s I hq hq8 hI
      exact ⟨T, hTcard, hTI, hTind, by simpa [cover] using hcoverI⟩
    · intro T I hTcard hTind hcoverI
      have hcoverU : (cover T).IsUniform s := by
        exact uniformizedCover_isUniform q J s T
      let out := ContainerA.finiteContainer (cover T) s t hs ht htmax
        hcoverU I hcoverI
      have hScard : out.fingerprint.card ≤ ⌊q * Fintype.card V⌋₊ := by
        apply containerFingerprint_card_le_floor hs hpar
        exact out.fingerprint_card
      refine ⟨out.fingerprint, hScard, out.fingerprint_subset, ?_⟩
      have hcanonical : canonicalContainer (cover T) s t hs ht out.fingerprint =
          out.container := by
        exact finiteContainer_canonicalContainer (cover T) s t hs ht htmax
          hcoverU I hcoverI
      have hψ : ψ T out.fingerprint = out.container := by
        have hTindJ : J.IsIndependent T := by
          simpa [J] using hTind
        rw [show ψ T out.fingerprint =
            canonicalContainer (cover T) s t hs ht out.fingerprint by
          simp only [ψ, if_pos hTindJ, canonicalContainer, selector]]
        exact hcanonical
      rw [hψ]
      exact out.input_subset
    · intro T S hTcard hScard hX
      by_cases hTind : J.IsIndependent T
      · have hcoverU : (cover T).IsUniform s := by
          exact uniformizedCover_isUniform q J s T
        have hψ : ψ T S = canonicalContainer (cover T) s t hs ht S := by
          simp [ψ, selector, canonicalContainer, hTind]
        rw [hψ] at hX ⊢
        simpa [t, zeta, containerZeta] using
          (canonicalContainer_not_isJanson (cover T) s hs hp hzeta
            hzeta_one htmax hcoverU S hX)
      · simp [ψ, hTind] at hX
    · intro T S hTcard hTind hScard hXlarge
      have hcoverU : (cover T).IsUniform s := by
        exact uniformizedCover_isUniform q J s T
      have hTindJ : J.IsIndependent T := by
        simpa [J] using hTind
      have hψ : ψ T S = canonicalContainer (cover T) s t hs ht S := by
        simp only [ψ, if_pos hTindJ, canonicalContainer, selector]
      have hX : (ψ T S).Nonempty :=
        largeContainer_nonempty hs hpar hXlarge
      have hnon : ¬ ((cover T).restrict (ψ T S)).IsJanson p
          (containerZeta r * p * (ψ T S).card) := by
        rw [hψ] at hX ⊢
        simpa [t, zeta] using
          (canonicalContainer_not_isJanson (cover T) s hs hp hzeta
            hzeta_one htmax hcoverU S hX)
      exact SpecialLocalization.fixedContainer_localize
        π v H F q p R R' η r s T (ψ T S) hpar hs hH hF hFJ hπ hv
        hFfresh hTind (by simpa [cover] using hnon) hXlarge
  exact SpecialContainer.specializedNonJansonContainer
    π v H F q p R R' η r s
    ⌊q * Fintype.card V⌋₊ ⌊2 * q * Fintype.card V⌋₊ cover ψ hassembly

end Assembly

end SpecialContainerTheorem
end Erdos565

#print axioms Erdos565.SpecialContainerTheorem.specializedNonJansonContainer
