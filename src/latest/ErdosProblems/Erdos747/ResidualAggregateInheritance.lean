import ErdosProblems.Erdos747.SharpDeletionInitial
import ErdosProblems.Erdos747.KahnAggregateLower

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Aggregate-degree inheritance in a one-edge residual graph -/

/-- The inverse outside-vertex map is injective even after forgetting its
proof of lying outside the removed triple. -/
lemma outsideVertexValue_injective {n : ℕ} {Z : Edge n}
    (hZ : Z ∈ allEdges n) :
    Function.Injective
      (fun w : Vertex (n - 1) ↦ ((outsideVertexEquiv Z hZ).symm w).1) := by
  intro u v huv
  apply (outsideVertexEquiv Z hZ).symm.injective
  apply Subtype.ext
  exact huv

/-- Aggregate degree regularity passes to the graph induced outside one
triple, provided the displayed deterministic changes of scale have been
absorbed into the new parameters. -/
lemma degreeAggregateRegular_reindexGraphAway
    {n M codegCap : ℕ} {H : Finset (Edge n)} {Z : Edge n}
    (hZ : Z ∈ allEdges n) (hHcard : H.card = M)
    (q eta B q' eta' B' : ℝ)
    (hcodeg : ∀ u v : Vertex n, u ≠ v →
      vertexCodegree H u v ≤ codegCap)
    (hreg : DegreeAggregateRegular n M q eta B H)
    (hlower :
      (1 - q') *
          (((reindexGraphAway H Z hZ).card : ℝ) / (n - 1 : ℕ)) ≤
        (1 - q) * ((M : ℝ) / n) - 3 * codegCap)
    (hupper :
      (1 + q) * ((M : ℝ) / n) ≤
        (1 + q') *
          (((reindexGraphAway H Z hZ).card : ℝ) / (n - 1 : ℕ)))
    (heta : eta * (3 * n : ℝ) ≤
      eta' * (3 * ((n - 1 : ℕ) : ℝ)))
    (hB : B * ((M : ℝ) / n) ≤
      B' * (((reindexGraphAway H Z hZ).card : ℝ) / (n - 1 : ℕ))) :
    DegreeAggregateRegular (n - 1) (reindexGraphAway H Z hZ).card
      q' eta' B' (reindexGraphAway H Z hZ) := by
  let J := reindexGraphAway H Z hZ
  let f : Vertex (n - 1) → Vertex n := fun w ↦
    ((outsideVertexEquiv Z hZ).symm w).1
  let BadJ := degreeRelativeBadVertices (n - 1) J.card q' J
  let BadH := degreeRelativeBadVertices n M q H
  have hf : Function.Injective f := outsideVertexValue_injective hZ
  have hbad : ∀ w : Vertex (n - 1), w ∈ BadJ → f w ∈ BadH := by
    intro w hwJ
    by_contra hwH
    have hparent : ¬ DegreeRelativeBad n M q (f w) H := by
      intro h
      exact hwH (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    unfold DegreeRelativeBad at hparent
    push Not at hparent
    rcases hparent with ⟨hparentLower, hparentUpper⟩
    have hvZ : f w ∉ Z := ((outsideVertexEquiv Z hZ).symm w).2
    have hsum : ∑ z ∈ Z, vertexCodegree H (f w) z ≤
        3 * codegCap := by
      calc
        ∑ z ∈ Z, vertexCodegree H (f w) z ≤ ∑ _z ∈ Z, codegCap := by
          apply Finset.sum_le_sum
          intro z hz
          exact hcodeg (f w) z (fun heq ↦ hvZ (heq ▸ hz))
        _ = 3 * codegCap := by simp [mem_allEdges.mp hZ]
    have hdegreeLoss := vertexDegree_inducedAway_add_codegrees_ge H Z (f w)
    have hdegreeLower :
        (vertexDegree H (f w) : ℝ) - ((3 * codegCap : ℕ) : ℝ) ≤
          vertexDegree (inducedAway H Z) (f w) := by
      have hdegreeLossR : (vertexDegree H (f w) : ℝ) ≤
          (vertexDegree (inducedAway H Z) (f w) : ℝ) +
            (∑ z ∈ Z, vertexCodegree H (f w) z : ℕ) := by
        exact_mod_cast hdegreeLoss
      have hsumR : ((∑ z ∈ Z, vertexCodegree H (f w) z : ℕ) : ℝ) ≤
          ((3 * codegCap : ℕ) : ℝ) := by
        exact_mod_cast hsum
      linarith
    have hdegreeUpper :
        (vertexDegree (inducedAway H Z) (f w) : ℝ) ≤
          vertexDegree H (f w) := by
      exact_mod_cast vertexDegree_inducedAway_le H Z (f w)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hdegreeLower
    have hnotChild : ¬ DegreeRelativeBad (n - 1) J.card q' w J := by
      unfold DegreeRelativeBad
      push Not
      rw [show vertexDegree J w =
          vertexDegree (inducedAway H Z) (f w) by
        simpa only [J, f] using vertexDegree_reindexGraphAway H hZ w]
      constructor
      · exact lt_of_le_of_lt hlower
          (lt_of_lt_of_le (sub_lt_sub_right hparentLower _) hdegreeLower)
      · exact hdegreeUpper.trans_lt (hparentUpper.trans_le hupper)
    exact hnotChild (Finset.mem_filter.mp hwJ).2
  have himage : BadJ.image f ⊆ BadH := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    exact hbad w hw
  have hcardNat : BadJ.card ≤ BadH.card := by
    calc
      BadJ.card = (BadJ.image f).card := by
        symm
        exact Finset.card_image_iff.mpr fun u hu v hv huv ↦ hf huv
      _ ≤ BadH.card := Finset.card_le_card himage
  have hcard : (BadJ.card : ℝ) ≤ BadH.card := by exact_mod_cast hcardNat
  constructor
  · change ((degreeRelativeBadVertices (n - 1)
        (reindexGraphAway H Z hZ).card q'
        (reindexGraphAway H Z hZ)).card : ℝ) ≤
      eta' * (3 * ((n - 1 : ℕ) : ℝ))
    calc
      ((degreeRelativeBadVertices (n - 1)
          (reindexGraphAway H Z hZ).card q'
          (reindexGraphAway H Z hZ)).card : ℝ) ≤
          ((degreeRelativeBadVertices n M q H).card : ℝ) := by
            simpa only [J, BadJ, BadH] using hcard
      _ ≤ eta * (3 * n : ℝ) := hreg.1
      _ ≤ eta' * (3 * ((n - 1 : ℕ) : ℝ)) := heta
  · intro w
    have hold := hreg.2 (f w)
    have hmono : (vertexDegree J w : ℝ) ≤ vertexDegree H (f w) := by
      rw [show vertexDegree J w =
          vertexDegree (inducedAway H Z) (f w) by
        simpa only [J, f] using vertexDegree_reindexGraphAway H hZ w]
      exact_mod_cast vertexDegree_inducedAway_le H Z (f w)
    exact hmono.trans (hold.trans hB)

/-- The residual package needed for aggregate lower spreading.  It keeps the
parent regularity used by coordinate transfer and records, only for triples
above the maximum-weight cutoff, the two facts needed in the reindexed graph:
the sharp count lower bound and aggregate degree regularity. -/
def ResidualAggregateInheritanceGood
    (n M d D codegCap : ℕ)
    (c C₀ C₁ q₁ etaDeg₁ Bdeg₁ : ℝ)
    (H : Finset (Edge n)) : Prop :=
  (perfectMatchings n H).card ≠ 0 ∧
  KahnCountLower H C₀ ∧
  (∀ v : Vertex n, d ≤ vertexDegree H v - 3 * codegCap) ∧
  (∀ v : Vertex n, vertexDegree H v ≤ D) ∧
  (∀ u v : Vertex n, u ≠ v → vertexCodegree H u v ≤ codegCap) ∧
  ∀ (Z : Edge n) (hZ : Z ∈ allEdges n),
    c^2 * matchingWeightTarget n H ≤ completionWeight H Z →
      (((n - 1 : ℕ) : ℝ) *
            Real.log (((reindexGraphAway H Z hZ).card : ℝ) /
              (n - 1 : ℕ)) -
          2 * ((n - 1 : ℕ) : ℝ) - C₁ * ((n - 1 : ℕ) : ℝ) ≤
        ((n : ℝ) * Real.log ((M : ℝ) / n) -
          2 * (n : ℝ) - C₀ * (n : ℝ)) +
          Real.log (c^2 * (n : ℝ) / M)) ∧
      DegreeAggregateRegular (n - 1)
        (reindexGraphAway H Z hZ).card q₁ etaDeg₁ Bdeg₁
        (reindexGraphAway H Z hZ)

/-- A high residual graph satisfying the aggregate inheritance package is
exactly a predecessor accepted by the aggregate lower-spreading theorem. -/
lemma reindexGraphAway_kahnAggregateInsertionGood
    {n M d D codegCap : ℕ}
    {c C₀ C₁ q₁ etaDeg₁ Bdeg₁ : ℝ}
    {H : Finset (Edge n)} {Z : Edge n}
    (hn : 2 ≤ n) (hM : 0 < M) (hH : H ∈ sample n M)
    (hZ : Z ∈ allEdges n) (hc : 0 < c)
    (hgood : ResidualAggregateInheritanceGood
      n M d D codegCap c C₀ C₁ q₁ etaDeg₁ Bdeg₁ H)
    (hweight : c^2 * matchingWeightTarget n H ≤ completionWeight H Z) :
    KahnAggregateInsertionGood (n - 1) (reindexGraphAway H Z hZ).card
      codegCap C₁ q₁ etaDeg₁ Bdeg₁ (reindexGraphAway H Z hZ) := by
  rcases hgood with
    ⟨hPhi, hcount, hdegreeLower, hdegreeUpper, hcodeg, hinherit⟩
  rcases hinherit Z hZ hweight with ⟨hcountBudget, haggregate⟩
  have hpm := hasPerfectMatching_reindexGraphAway_of_weightLower
    hn (by simpa [(mem_sample.mp hH).2] using hM) hZ hPhi hc hweight
  have hJall : reindexGraphAway H Z hZ ⊆ allEdges (n - 1) :=
    reindexGraphAway_subset_allEdges hZ (mem_sample.mp hH).1
  refine ⟨mem_sample.mpr ⟨hJall, rfl⟩, hpm, ?_, ?_, haggregate⟩
  · exact kahnCountLower_reindexGraphAway_of_weightLower
      hn hM hH hZ hc hPhi hcount hweight hcountBudget
  · intro u v huv
    rw [vertexCodegree_reindexGraphAway]
    exact (vertexCodegree_inducedAway_le H Z _ _).trans
      (hcodeg _ _ (fun huv' ↦ huv
        ((outsideVertexEquiv Z hZ).symm.injective (Subtype.ext huv'))))

/-- Failure of high residual lower spreading inside the aggregate
inheritance package produces a bad reindexed predecessor in the relevant
cardinality range. -/
lemma residualAggregate_not_highResidual_implies_someReindexFailure
    {n M d D codegCap : ℕ}
    {c C₀ C₁ q₁ etaDeg₁ Bdeg₁ L eta : ℝ}
    {H : Finset (Edge n)}
    (hn : 2 ≤ n) (hM : 0 < M) (hH : H ∈ sample n M) (hc : 0 < c)
    (hgood : ResidualAggregateInheritanceGood
      n M d D codegCap c C₀ C₁ q₁ etaDeg₁ Bdeg₁ H)
    (hfail : ¬ HighResidualLowerSpread n H c L eta) :
    SomeReindexLayerCardAtLeastFailure (M - 3 * D)
      (KahnAggregateInsertionLowerFailure
        (n - 1) codegCap C₁ q₁ etaDeg₁ Bdeg₁ L eta) H := by
  rcases hgood with
    ⟨hPhi, hcount, hdegreeLower, hdegreeUpper, hcodeg, hinherit⟩
  obtain ⟨Z₀, hZ₀, hmax⟩ := exists_max_completionWeight H (by omega)
  have hnotall : ¬ ∀ (Z : Edge n) (hZ : Z ∈ allEdges n),
      c^2 * (completionWeight H Z₀ : ℝ) ≤ completionWeight H Z →
        GlobalLowerWeightSpread (n - 1)
          (reindexGraphAway H Z hZ) L eta := by
    intro hall
    exact hfail ⟨Z₀, hZ₀, hmax, hall⟩
  push Not at hnotall
  rcases hnotall with ⟨Z, hZ, hhigh, hbad⟩
  have hweight : c^2 * matchingWeightTarget n H ≤ completionWeight H Z :=
    high_from_max_completionWeight hM hH hmax hc.le hhigh
  have haggregate : KahnAggregateInsertionGood (n - 1)
      (reindexGraphAway H Z hZ).card codegCap C₁ q₁ etaDeg₁ Bdeg₁
      (reindexGraphAway H Z hZ) := by
    apply reindexGraphAway_kahnAggregateInsertionGood hn hM hH hZ hc
    · exact ⟨hPhi, hcount, hdegreeLower, hdegreeUpper, hcodeg, hinherit⟩
    · exact hweight
  unfold SomeReindexLayerCardAtLeastFailure
  refine ⟨⟨Z, hZ⟩, ?_⟩
  unfold ReindexLayerCardAtLeastFailure LayerCardAtLeastFailure
  refine ⟨?_, ?_⟩
  · exact card_reindexGraphAway_lower hZ (mem_sample.mp hH).2
      (fun z hz ↦ hdegreeUpper z)
  · exact ⟨haggregate, hbad⟩

/-- Uniform fixed-layer aggregate lower-spreading bounds control failure of
high residual spreading in the parent sample. -/
lemma residualAggregate_highResidual_failure_probability_le
    {n M d D codegCap : ℕ}
    {c C₀ C₁ q₁ etaDeg₁ Bdeg₁ L eta delta : ℝ}
    (hn : 2 ≤ n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hc : 0 < c) (hdelta : 0 ≤ delta)
    (hlayer : ∀ k, M - 3 * D ≤ k → k ≤ M →
      finsetProbability (sample (n - 1) k)
        (KahnAggregateInsertionLowerFailure
          (n - 1) codegCap C₁ q₁ etaDeg₁ Bdeg₁ L eta) ≤ delta) :
    finsetProbability (sample n M)
        (fun H ↦ ResidualAggregateInheritanceGood
            n M d D codegCap c C₀ C₁ q₁ etaDeg₁ Bdeg₁ H ∧
          ¬ HighResidualLowerSpread n H c L eta) ≤
      (allEdges n).card * delta := by
  calc
    finsetProbability (sample n M)
        (fun H ↦ ResidualAggregateInheritanceGood
            n M d D codegCap c C₀ C₁ q₁ etaDeg₁ Bdeg₁ H ∧
          ¬ HighResidualLowerSpread n H c L eta) ≤
      finsetProbability (sample n M)
        (SomeReindexLayerCardAtLeastFailure (M - 3 * D)
          (KahnAggregateInsertionLowerFailure
            (n - 1) codegCap C₁ q₁ etaDeg₁ Bdeg₁ L eta)) := by
      apply finsetProbability_mono_event
      intro H hHs hfail
      exact residualAggregate_not_highResidual_implies_someReindexFailure
        hn hM0 hHs hc hfail.1 hfail.2
    _ ≤ (allEdges n).card * delta :=
      some_reindexGraphAway_failure_probability_le_of_layer_range
        (KahnAggregateInsertionLowerFailure
          (n - 1) codegCap C₁ q₁ etaDeg₁ Bdeg₁ L eta)
        delta hdelta hM hlayer

end

end Erdos747
