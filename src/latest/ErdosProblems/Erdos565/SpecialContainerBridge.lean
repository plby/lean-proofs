import ErdosProblems.Erdos565.SpecialContainer
import ErdosProblems.Erdos565.ConditionalDecomposition
import ErdosProblems.Erdos565.JansonContainer
import ErdosProblems.Erdos565.ProjectionFibers
import ErdosProblems.Erdos565.Pullback
import ErdosProblems.Erdos565.BoundedDegree
import ErdosProblems.Erdos565.RandomRestriction
import ErdosProblems.Erdos565.FiniteExpectation
import ErdosProblems.Erdos565.JensenContradiction
import Mathlib.Tactic

/-!
# Shared bridges for the specialised non-Janson container theorem

This file supplies the mathematical stages consumed by
`SpecialContainer.assemble`.  In particular, the first-stage cover below is
canonical: it is a function of the fingerprint and not of the independent set
from which that fingerprint was selected.
-/

open scoped BigOperators

namespace Erdos565
namespace SpecialContainerTheorem

open Hypergraph

variable {V U : Type*}

section ConditionalStage

variable [Fintype V] [DecidableEq V]

/-- The canonical first-stage cover associated with a conditional-probability
fingerprint. -/
noncomputable def conditionalCover (q : ℝ) (G : Hypergraph V)
    (T : Finset V) : Hypergraph V :=
  ConditionalDecomposition.badExtensions q (1 / 2) Finset.univ G T

/-- The `s`-uniform part of the upward closure of the canonical first-stage
cover.  This is the family to which the Janson-container theorem is applied. -/
noncomputable def uniformizedCover (q : ℝ) (G : Hypergraph V)
    (s : ℕ) (T : Finset V) : Hypergraph V :=
  (conditionalCover q G T).upClosure.layer s

theorem uniformizedCover_isUniform (q : ℝ) (G : Hypergraph V)
    (s : ℕ) (T : Finset V) :
    (uniformizedCover q G s T).IsUniform s := by
  intro E hE
  exact (mem_layer.mp hE).2

/-- Independence passes from a cover to the uniform layer of its upward
closure. -/
theorem uniformizedCover_isIndependent {q : ℝ} {G : Hypergraph V}
    {s : ℕ} {T I : Finset V}
    (hI : (conditionalCover q G T).IsIndependent I) :
    (uniformizedCover q G s T).IsIndependent I := by
  intro E hE hEI
  obtain ⟨L, hLC, hLE⟩ := mem_upClosure.mp (mem_layer.mp hE).1
  exact hI L hLC (hLE.trans hEI)

/-- The strict half-threshold conclusion of the decomposition, stated for the
canonical cover used by the specialised theorem. -/
theorem conditional_large_of_not_mem_cover
    {q : ℝ} {G : Hypergraph V} {T L : Finset V}
    (hL : L ⊆ Finset.univ \ T) (hLne : L.Nonempty)
    (hnot : L ∉ conditionalCover q G T) :
    ConditionalDecomposition.threshold q (1 / 2) L <
      ConditionalDecomposition.extensionProbability q Finset.univ G T L := by
  have hnot' :
      ¬ ConditionalDecomposition.extensionProbability q Finset.univ G T L ≤
        ConditionalDecomposition.threshold q (1 / 2) L := by
    intro hle
    apply hnot
    exact ConditionalDecomposition.mem_badExtensions.mpr ⟨hL, hLne, hle⟩
  exact lt_of_not_ge hnot'

/-- The conditional-probability decomposition with `α = 1/2`, including
the exact natural floor cutoff `⌊2q|V|⌋` required for finite counting.

The proof uses the chosen decomposition only to select its fingerprint.  If a
canonical bad extension were contained in the input but absent from the
chosen cover, the strict outside-cover inequality would contradict the very
definition of a bad extension.  Thus the resulting cover is determined by
the fingerprint alone. -/
theorem exists_conditionalFingerprint
    (q : ℝ) (G : Hypergraph V) (I : Finset V)
    (hq : 0 < q) (hq8 : q < 1 / 8)
    (hI : G.IsIndependent I) :
    ∃ T : Finset V,
      T.card ≤ ⌊2 * q * Fintype.card V⌋₊ ∧
      T ⊆ I ∧
      (conditionalCover q G T).IsIndependent I := by
  have hqhalf : q ≤ (1 / 2 : ℝ) := by linarith
  have hsupported : ConditionalDecomposition.SupportedOn G
      (Finset.univ : Finset V) := by
    intro E hE
    exact Finset.subset_univ E
  obtain ⟨T, hTcard, hTI, hTind⟩ :=
    ConditionalDecomposition.exists_half_fingerprint q Finset.univ G I
      hq hqhalf hsupported (Finset.subset_univ I) hI
  exact ⟨T, Nat.le_floor hTcard, hTI, hTind⟩

/-- The same decomposition, with the independent uniformized cover needed by
the second fingerprint stage. -/
theorem exists_conditionalFingerprint_uniformized
    (q : ℝ) (G : Hypergraph V) (s : ℕ) (I : Finset V)
    (hq : 0 < q) (hq8 : q < 1 / 8)
    (hI : G.IsIndependent I) :
    ∃ T : Finset V,
      T.card ≤ ⌊2 * q * Fintype.card V⌋₊ ∧
      T ⊆ I ∧
      (uniformizedCover q G s T).IsIndependent I := by
  obtain ⟨T, hTcard, hTI, hTind⟩ :=
    exists_conditionalFingerprint q G I hq hq8 hI
  exact ⟨T, hTcard, hTI, uniformizedCover_isIndependent hTind⟩

/-- The chosen first fingerprint is itself independent in the generating
family.  This is the positivity premise needed when Section 7 conditions on
independent supersets containing that fingerprint. -/
theorem exists_conditionalFingerprint_uniformized_with_seedIndependent
    (q : ℝ) (G : Hypergraph V) (s : ℕ) (I : Finset V)
    (hq : 0 < q) (hq8 : q < 1 / 8)
    (hI : G.IsIndependent I) :
    ∃ T : Finset V,
      T.card ≤ ⌊2 * q * Fintype.card V⌋₊ ∧
      T ⊆ I ∧
      G.IsIndependent T ∧
      (uniformizedCover q G s T).IsIndependent I := by
  obtain ⟨T, hTcard, hTI, hTCover⟩ :=
    exists_conditionalFingerprint_uniformized q G s I hq hq8 hI
  exact ⟨T, hTcard, hTI, hI.mono hTI, hTCover⟩

end ConditionalStage

section ProjectionStage

variable [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

/-- The part of `X` whose projections lie in `W`. -/
def retainedByProjectedSet (π : V → U) (X : Finset V) (W : Finset U) :
    Finset V :=
  X.filter fun x ↦ π x ∈ W

@[simp] theorem mem_retainedByProjectedSet {π : V → U} {X : Finset V}
    {W : Finset U} {x : V} :
    x ∈ retainedByProjectedSet π X W ↔ x ∈ X ∧ π x ∈ W := by
  simp [retainedByProjectedSet]

theorem retainedByProjectedSet_subset (π : V → U) (X : Finset V)
    (W : Finset U) : retainedByProjectedSet π X W ⊆ X := by
  intro x hx
  exact (mem_retainedByProjectedSet.mp hx).1

/-- Restricting the projected hypergraph to `W` is exactly restriction to
the inverse image of `W` before projecting. -/
theorem map_restrict_retained (π : V → U) (H : Hypergraph V)
    (X : Finset V) (W : Finset U) :
    ((H.restrict X).map π).restrict W =
      (H.restrict (retainedByProjectedSet π X W)).map π := by
  ext K
  constructor
  · intro hK
    have hKr := mem_restrict.mp hK
    obtain ⟨E, hEX, rfl⟩ := mem_map.mp hKr.1
    have hEX' := mem_restrict.mp hEX
    apply mem_map.mpr
    refine ⟨E, mem_restrict.mpr ⟨hEX'.1, ?_⟩, rfl⟩
    intro x hxE
    exact mem_retainedByProjectedSet.mpr
      ⟨hEX'.2 hxE, hKr.2 (Finset.mem_image.mpr ⟨x, hxE, rfl⟩)⟩
  · intro hK
    obtain ⟨E, hEY, rfl⟩ := mem_map.mp hK
    have hEY' := mem_restrict.mp hEY
    apply mem_restrict.mpr
    refine ⟨mem_map.mpr ⟨E, mem_restrict.mpr
      ⟨hEY'.1, hEY'.2.trans (retainedByProjectedSet_subset π X W)⟩, rfl⟩, ?_⟩
    intro u hu
    obtain ⟨x, hxE, rfl⟩ := Finset.mem_image.mp hu
    exact (mem_retainedByProjectedSet.mp (hEY'.2 hxE)).2

/-- The source points deleted by retaining `W` are precisely the projected
container deletion from `ProjectionFibers`. -/
theorem sdiff_retained_eq_removed (π : V → U) (X : Finset V)
    (W : Finset U) :
    X \ retainedByProjectedSet π X W =
      ProjectionFibers.removedByProjectedContainer π X W := by
  ext x
  by_cases hx : x ∈ X <;> by_cases hu : π x ∈ W <;>
    simp [retainedByProjectedSet,
      ProjectionFibers.removedByProjectedContainer, hx, hu]

theorem retained_card_loss_eq_removed_card (π : V → U) (X : Finset V)
    (W : Finset U) :
    X.card - (retainedByProjectedSet π X W).card =
      (ProjectionFibers.removedByProjectedContainer π X W).card := by
  let Y := retainedByProjectedSet π X W
  have hYX : Y ⊆ X := retainedByProjectedSet_subset π X W
  calc
    X.card - Y.card = X.card - (Y ∩ X).card := by
      rw [Finset.inter_eq_left.mpr hYX]
    _ = (X \ Y).card := Finset.card_sdiff.symm
    _ = (ProjectionFibers.removedByProjectedContainer π X W).card := by
      rw [sdiff_retained_eq_removed]

/-- The global half-image hypothesis controls the cost of restricting to a
projected set, without first converting it to a fibre-bound predicate. -/
theorem retained_card_loss_le_twice
    (π : V → U) (H : Hypergraph V)
    (hπ : SpecialContainer.ProjectionConditions π H)
    (X : Finset V) (W : Finset U) :
    X.card - (retainedByProjectedSet π X W).card ≤
      2 * (X.image π \ W).card := by
  rw [retained_card_loss_eq_removed_card]
  have h := hπ.1
    (ProjectionFibers.removedByProjectedContainer π X W)
  rwa [ProjectionFibers.image_removedByProjectedContainer] at h

/-- Projection preserves uniformity because the theorem assumes injectivity
on every source edge. -/
theorem projected_restrict_isUniform
    (π : V → U) (H : Hypergraph V) {s : ℕ}
    (hH : H.IsUniform s)
    (hπ : SpecialContainer.ProjectionConditions π H)
    (X : Finset V) :
    ((H.restrict X).map π).IsUniform s := by
  intro K hK
  obtain ⟨E, hEX, rfl⟩ := mem_map.mp hK
  have hE := (mem_restrict.mp hEX).1
  rw [hπ.2 E hE, hH E hE]

theorem projected_restrict_edgewiseInjective
    (π : V → U) (H : Hypergraph V)
    (hπ : SpecialContainer.ProjectionConditions π H)
    (X : Finset V) :
    Hypergraph.EdgewiseInjective (H.restrict X) π := by
  rw [Hypergraph.edgewiseInjective_iff_card_image]
  intro E hEX
  exact hπ.2 E (mem_restrict.mp hEX).1

/-- A genuinely new extension vertex is fresh for every projected
restriction. -/
theorem freshFor_projected_restrict
    (π : V → U) (v : U) (H : Hypergraph V)
    (hv : ∀ x, π x ≠ v) (X : Finset V) :
    Hypergraph.FreshFor v ((H.restrict X).map π) := by
  intro K hK hvK
  obtain ⟨E, hEX, rfl⟩ := mem_map.mp hK
  obtain ⟨x, hxE, hxv⟩ := Finset.mem_image.mp hvK
  exact hv x hxv

end ProjectionStage

section ConditionalExpectationBridge

variable [Fintype V] [DecidableEq V]

/-- The finite event that a random subset of `ground` contains `L`. -/
def containmentEvent (ground L : Finset V) : Finset (Finset V) :=
  ground.powerset.filter fun X ↦ L ⊆ X

@[simp] theorem mem_containmentEvent {ground L X : Finset V} :
    X ∈ containmentEvent ground L ↔ X ⊆ ground ∧ L ⊆ X := by
  simp [containmentEvent]

/-- `FiniteExpectation`'s conditioning mass agrees with the binomial mass
used by the conditional decomposition. -/
theorem conditioningMass_independentContaining
    (q : ℝ) (ground T : Finset V) (G : Hypergraph V) :
    FiniteExpectation.conditioningMass ground.powerset
        (ConditionalDecomposition.independentContainingEvent ground G T)
        (ConditionalDecomposition.subsetWeight q ground) =
      ConditionalDecomposition.independentContainingMass q ground G T := by
  unfold FiniteExpectation.conditioningMass
    FiniteExpectation.conditioningSet
    ConditionalDecomposition.independentContainingMass
    ConditionalDecomposition.qMass
  congr 1
  ext X
  simp

theorem conditioningMass_independentContaining_inter
    (q : ℝ) (ground T L : Finset V) (G : Hypergraph V) :
    FiniteExpectation.conditioningMass ground.powerset
        (ConditionalDecomposition.independentContainingEvent ground G T ∩
          containmentEvent ground L)
        (ConditionalDecomposition.subsetWeight q ground) =
      ConditionalDecomposition.independentContainingMass q ground G (T ∪ L) := by
  unfold FiniteExpectation.conditioningMass
    FiniteExpectation.conditioningSet
    ConditionalDecomposition.independentContainingMass
    ConditionalDecomposition.qMass
  congr 1
  ext X
  simp [and_assoc, Finset.union_subset_iff]
  aesop

/-- The abstract conditional probability of a containment cylinder is the
`extensionProbability` used in the decomposition theorem. -/
theorem conditionalProbability_containmentEvent
    (q : ℝ) (ground T L : Finset V) (G : Hypergraph V) :
    FiniteExpectation.conditionalProbability ground.powerset
        (ConditionalDecomposition.independentContainingEvent ground G T)
        (containmentEvent ground L)
        (ConditionalDecomposition.subsetWeight q ground) =
      ConditionalDecomposition.extensionProbability q ground G T L := by
  rw [FiniteExpectation.conditionalProbability_eq_mass_div]
  rw [conditioningMass_independentContaining_inter,
    conditioningMass_independentContaining]
  rfl

/-- Positivity of the finite conditioning distribution. -/
theorem conditioningMass_independentContaining_pos
    {q : ℝ} {ground T : Finset V} {G : Hypergraph V}
    (hq : 0 < q) (hq1 : q < 1) (hTground : T ⊆ ground)
    (hTind : G.IsIndependent T) :
    0 < FiniteExpectation.conditioningMass ground.powerset
      (ConditionalDecomposition.independentContainingEvent ground G T)
      (ConditionalDecomposition.subsetWeight q ground) := by
  rw [conditioningMass_independentContaining]
  exact ConditionalDecomposition.independentContainingMass_pos
    hTground hTind hq hq1

end ConditionalExpectationBridge

section Parameters

/-- The Janson-container loss parameter in Theorem 5.4. -/
noncomputable def containerZeta (r : ℕ) : ℝ := 1 / (256 * (r : ℝ))

/-- The deletion proportion used in the bounded-one-degree lemma. -/
noncomputable def deletionBeta (r : ℕ) : ℝ := 1 / (512 * (r : ℝ))

theorem containerZeta_pos {r : ℕ} (hr : 2 ≤ r) :
    0 < containerZeta r := by
  unfold containerZeta
  have hr' : (0 : ℝ) < r := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hr)
  exact one_div_pos.mpr (mul_pos (by norm_num) hr')

theorem containerZeta_le_one {r : ℕ} (hr : 2 ≤ r) :
    containerZeta r ≤ 1 := by
  unfold containerZeta
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : 0 < 256 * (r : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

theorem deletionBeta_pos {r : ℕ} (hr : 2 ≤ r) :
    0 < deletionBeta r := by
  unfold deletionBeta
  have hr' : (0 : ℝ) < r := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hr)
  exact one_div_pos.mpr (mul_pos (by norm_num) hr')

theorem parameter_n_pos {n s r : ℕ} {q p R R' η : ℝ}
    (hs : 0 < s)
    (h : SpecialContainer.ParameterConditions n s r q p R R' η) :
    0 < n :=
  lt_of_lt_of_le hs h.1

theorem parameter_R_pos {n s r : ℕ} {q p R R' η : ℝ}
    (hs : 0 < s)
    (h : SpecialContainer.ParameterConditions n s r q p R R' η) :
    0 < R := by
  rcases h with ⟨hsn, hr, hq, hq8, hp, hpq, rfl, hR'0, hR'le, hη⟩
  have hn : 0 < n := lt_of_lt_of_le hs hsn
  positivity

theorem parameter_sixteen_R'_le_R
    {n s r : ℕ} {q p R R' η : ℝ}
    (h : SpecialContainer.ParameterConditions n s r q p R R' η) :
    16 * R' ≤ R := by
  rcases h with ⟨hsn, hr, hq, hq8, hp, hpq, hR, hR'0, hR'le, hη⟩
  linarith

/-- The published bound on `p` implies the hypothesis of the ordinary
Janson-container theorem at `ζ = 1/(256r)`. -/
theorem parameter_p_le_containerZeta
    {n s r : ℕ} {q p R R' η : ℝ}
    (hs : 0 < s)
    (h : SpecialContainer.ParameterConditions n s r q p R R' η) :
    p ≤ containerZeta r / (8 * (s : ℝ) ^ 2) := by
  rcases h with ⟨hsn, hr, hq, hq8, hp, hpq, hR, hR'0, hR'le, hη⟩
  have hrR : 0 < (r : ℝ) := by positivity
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hq1 : q ≤ 1 := by linarith
  have hden : 0 < 2048 * (r : ℝ) * (s : ℝ) ^ 2 := by positivity
  norm_num at hpq
  have hmul : p * (2048 * (r : ℝ) * (s : ℝ) ^ 2) ≤ q := by
    exact (le_div_iff₀ hden).mp hpq
  have htarget : containerZeta r / (8 * (s : ℝ) ^ 2) =
      1 / (2048 * (r : ℝ) * (s : ℝ) ^ 2) := by
    unfold containerZeta
    field_simp [ne_of_gt hrR, ne_of_gt hsR]
    <;> ring
  rw [htarget]
  exact (le_div_iff₀ hden).2 (hmul.trans hq1)

/-- The second fingerprint has real size at most `q*n`. -/
theorem parameter_secondFingerprint_bound
    {n s r : ℕ} {q p R R' η : ℝ}
    (hs : 0 < s)
    (h : SpecialContainer.ParameterConditions n s r q p R R' η) :
    8 * (s : ℝ) ^ 2 * (p / containerZeta r) * n ≤ q * n := by
  rcases h with ⟨hsn, hr, hq, hq8, hp, hpq, hR, hR'0, hR'le, hη⟩
  have hrR : 0 < (r : ℝ) := by positivity
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hden : 0 < 2048 * (r : ℝ) * (s : ℝ) ^ 2 := by positivity
  norm_num at hpq
  have hmul : p * (2048 * (r : ℝ) * (s : ℝ) ^ 2) ≤ q := by
    exact (le_div_iff₀ hden).mp hpq
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hz : p / containerZeta r = 256 * (r : ℝ) * p := by
    unfold containerZeta
    field_simp [ne_of_gt hrR]
    <;> ring
  rw [hz]
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hmul)]

/-- Convert the real fingerprint estimate produced by the finite container
algorithm to the exact natural floor cutoff used by the assembly count. -/
theorem containerFingerprint_card_le_floor
    {n s r : ℕ} {q p R R' η : ℝ} {S : Finset V}
    (hs : 0 < s)
    (h : SpecialContainer.ParameterConditions n s r q p R R' η)
    (hS : (S.card : ℝ) ≤
      8 * (s : ℝ) ^ 2 * (p / containerZeta r) * n) :
    S.card ≤ ⌊q * n⌋₊ := by
  apply Nat.le_floor
  exact hS.trans (parameter_secondFingerprint_bound hs h)

/-- A container satisfying the large-container cutoff is nonempty.  This is
the exact guard needed for the corrected Janson-container conclusion. -/
theorem largeContainer_nonempty [Fintype V]
    {s r : ℕ} {q p R R' η : ℝ} {X : Finset V}
    (hs : 0 < s)
    (h : SpecialContainer.ParameterConditions
      (Fintype.card V) s r q p R R' η)
    (hlarge : Fintype.card V ≤ 8 * r * X.card) : X.Nonempty := by
  have hn : 0 < Fintype.card V := parameter_n_pos hs h
  by_contra hX
  rw [Finset.not_nonempty_iff_eq_empty.mp hX] at hlarge
  simp at hlarge
  omega

end Parameters

end SpecialContainerTheorem
end Erdos565
