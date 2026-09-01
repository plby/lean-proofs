import ErdosProblems.Erdos260.DeepMind

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Declaration and regression audit

This module checks the complete paper-label surface, the DeepMind-compatible
endpoint, and small executable examples of the semantic definitions.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace Erdos260

def auditPositiveNaturals : Set ℕ := {n | 0 < n}

def auditUnitEnumeration : SupportEnumeration auditPositiveNaturals where
  a := fun n => n + 1
  strictMono := by
    intro a b hab
    exact Nat.add_lt_add_right hab 1
  positive := by
    intro n
    omega
  range_eq := by
    ext n
    constructor
    · rintro ⟨k, rfl⟩
      simp [auditPositiveNaturals]
    · intro hn
      refine ⟨n - 1, ?_⟩
      simp only [auditPositiveNaturals, Set.mem_ofPred_eq] at hn
      exact Nat.sub_add_cancel hn

-- Appendix A (5)
#check lem_composition_entropy
#check lem_lattice_det
#check lem_farey
#check lem_word_cylinder
#check lem_quant_entropy

-- Both composition-count entropy arguments are frozen inside the monotone
-- half interval; the strict entropy margins alone do not imply these facts.
example (p : EntropyParams) :
    p.kappa / (p.structural.Caff + 1) ≤ (1 : ℝ) / 2 :=
  p.kappa_initial_half

example (p : EntropyParams) :
    p.kappa / (p.structural.Gamma + 1) ≤ (1 : ℝ) / 2 :=
  p.kappa_exterior_half

-- Section 3, including the labelled definition (4)
#check prop_carry
#check lem_gap
#check mass
#check lem_refinement_principle
#check WindowSystem.measurableSet_pairSet
#check WindowSystem.measurable_excess
#check totalMass_finite
#check ofReal_integratedExcess

-- Section 4 (3)
#check lem_window_count
#check prop_pressure
#check prop_moderate

-- Section 5 (8)
#check lem_firstdeep_exists
#check lem_firstdeep_count
#check prop_low_firstdeep
#check lem_ap_locking
#check lem_strict_unique
#check lem_step_monotone
#check lem_boundary_stretch
#check lem_dichotomy

-- Section 6 (9)
#check lem_stable_segment
#check lem_primitive_direction
#check lem_denominator_span
#check lem_sparse_cover
#check selectedBlocks_eq_pointwiseSelectedBlocks
#check lem_signature_entropy
#check lem_word_slope
#check lem_line_unique
#check lem_source_fibre
#check thm_strict_mass

-- Section 7 (5)
#check lem_off_amplify
#check lem_off_corridor
#check prop_fixed_off_word
#check lem_seconddeep
#check thm_off_mass

-- Appendix D and completion (5)
#check prop_uniform_errors
#check InteriorRefinement.selection_valid
#check InteriorRefinement.selected_data
#check InteriorRefinement.blocks_nodup
#check InteriorRefinement.labels_eq
#check InteriorRefinement.weight_eq
#check prop_exact_source_decomp
#check prop_upper
#check thm_main_density
#check cor_erdos260

-- All three non-boundary error families share the same denominator-level
-- cutoff in the uniformity interface.
example (context : FixedScaleContext) :
    ∃ Zmin : ℕ, ∃ interiorBound : ℕ → ℝ,
      (∀ Z0, 0 ≤ interiorBound Z0) ∧
      Tendsto interiorBound atTop (𝓝 0) ∧
      ∀ F : ScaleFamily, F.MatchesContext context →
        Tendsto (fun L => boundaryLossRatio (F.system L)) atTop (𝓝 0) ∧
        (∀ Z0, Zmin ≤ Z0 →
          (fun L => rareLargePairsMass (F.system L) Z0) =o[atTop]
            (fun L => normalizationScale (F.system L))) ∧
        (∀ Z0, Zmin ≤ Z0 →
          (fun L => exteriorPairsMass (F.system L) Z0) =o[atTop]
            (fun L => normalizationScale (F.system L))) ∧
        ∀ Z0, Zmin ≤ Z0 → ∀ᶠ L : ℕ in atTop,
          interiorMassRatio (F.system L) Z0 ≤ interiorBound Z0 :=
  prop_uniform_errors context

-- DeepMind RHS compatibility.
example : deepmindStatement := erdos_260

-- The half-open block `(2,4]` contains exactly 3 and 4.
example : (Finset.Ioc 2 4 : Finset ℕ) = {3, 4} := by
  decide

-- The selected prefix is the first one whose span is strictly above 2.
example : GapWord.firstPrefixAbove [1, 2, 4] 2 = [1, 2] := by
  decide

-- An offset-zero window contains exactly its one terminal gap.
example :
    windowGapWord auditUnitEnumeration ⟨3, 0, by omega⟩ = [1] := by
  decide

-- A finite nonnegative partition of unity, matching refinement weights.
example :
    (∑ i : Fin 2, if i = 0 then (1 / 4 : ℚ) else 3 / 4) = 1 := by
  norm_num [Fin.sum_univ_two]

-- Boundary slopes are not classified as exterior.
example : classifySlope (0 : ℚ) = .boundaryZero := by decide
example : classifySlope (1 : ℚ) = .boundaryOne := by decide

-- Initial-exterior records contain no fictitious exit gap.
example : FirstExitRecord.initialExterior.exitGap = 0 := rfl

-- Shared-gap transformation retains the original horizontal parameter even
-- for a nonprimitive direction.
example :
    let line : AffineLine := ⟨0, 0, 6, 4, by decide⟩
    (line.transform 3 2).H = 6 := by
  rfl

example :
    let line : AffineLine := ⟨0, 0, 6, 4, by decide⟩
    (line.transform 3 2).K = -2 := by
  decide

-- Translating the raw integer parameter origin does not change the canonical
-- primitive direction and intercept.
example (line : AffineLine) (t : ℤ) :
    (line.shiftOrigin t).canonicalGeometricLine = line.canonicalGeometricLine :=
  line.canonicalGeometricLine_shiftOrigin t

-- Interior block/prefix selection is spatial and therefore threshold-free.
example (W : WindowSystem) (k : ℕ) (T₁ T₂ : ℝ) :
    initialLongPrefix W (k, T₁).1 = initialLongPrefix W (k, T₂).1 := rfl

-- A refinement's labels at an interior anchor are literally the same finite
-- spatial block list for every threshold coordinate.
example (W : WindowSystem) (Z0 k : ℕ) (T₁ T₂ : ℝ)
    (refinement : InteriorRefinement W Z0)
    (h₁ : (k, T₁) ∈ interiorPairs W Z0)
    (h₂ : (k, T₂) ∈ interiorPairs W Z0) :
    refinement.labels (k, T₁) = refinement.labels (k, T₂) := by
  rw [refinement.labels_eq (k, T₁) h₁,
    refinement.labels_eq (k, T₂) h₂]

-- Interior labels cannot be manufactured independently of the actual
-- anchor segment and its deterministic greedy decomposition.
example (W : WindowSystem) (Z0 : ℕ)
    (refinement : InteriorRefinement W Z0) (e : WindowThreshold)
    (he : e ∈ interiorPairs W Z0) :
    ∃ data : AnchorInteriorData,
      refinement.selection e.1 = some data ∧
      data.Valid W.rational.eta.den W Z0 e.1 ∧
      refinement.blocks e.1 =
        selectedBlocks data.segment W.structural.B
          (refinement.ell e.1) (refinement.meanGap e.1)
          (refinement.forward e.1) :=
  refinement.selected_data e he

-- The strict interior estimate chooses one cutoff and one nonnegative
-- vanishing coefficient at denominator-context level.  Beyond that cutoff,
-- each compatible family eventually supplies the actual refinement
-- certificate together with the mass bound.
example (context : FixedScaleContext) :
    ∃ Zmin : ℕ, ∃ ηQ : ℕ → ℝ,
      (∀ Z0, 0 ≤ ηQ Z0) ∧ Tendsto ηQ atTop (𝓝 0) ∧
      ∀ Z0, Zmin ≤ Z0 → ∀ F : ScaleFamily,
        F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∃ _refinement : InteriorRefinement (F.system L) Z0,
              interiorPairsMass (F.system L) Z0 ≤
                ηQ Z0 * (F.system L).m * (F.system L).X *
                  thresholdLength (F.system L) :=
  thm_strict_mass context

-- The completion estimate chooses one cutoff and one vanishing error before
-- quantifying the compatible family and sparsity coefficient.
example (context : FixedScaleContext) :
    ∀ θ : ℝ, 0 < θ →
      ∃ Z0 : ℕ, ∃ error : ℕ → ℝ,
        Tendsto error atTop (𝓝 0) ∧
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop, ∀ cstar : ℝ,
            cstar ∈ Set.Icc (0 : ℝ) 1 →
            (dyadicBlockCount (F.system L).rational.S
                (F.system L).X : ℝ) ≤ cstar * (F.system L).X →
            integratedExcess (F.system L) ≤
              ((Z0 : ℝ) * cstar + θ + error L) *
                normalizationScale (F.system L) :=
  prop_upper context

-- Empty event families have zero nonnegative mass.
example (weight : WindowThreshold → ℝ) : mass (∅ : Set WindowThreshold) weight = 0 := by
  simp [mass]

-- The paper interval is `[2L+C₀, 2L+C₀+cᵢL]`; for this concrete instance
-- its Lebesgue length is exactly `cᵢL = 12`.
example : volume (thresholdInterval 3 2 4) = 12 := by
  norm_num [thresholdInterval, Real.volume_Icc]

-- Normalizing a public support deletes zero and nothing else.
example : positiveSupport ({0, 1, 2} : Set ℕ) = ({1, 2} : Set ℕ) := by
  ext n
  simp [positiveSupport]
  omega

-- The boundary theorem now carries the missing step-count invariant; in
-- particular even the number of gap-one steps is bounded by `m`.
example (gaps : GapWord) (m : ℕ) (hlen : gaps.length ≤ m) :
    gaps.count 1 ≤ m :=
  List.count_le_length.trans hlen

-- A genuinely positive logarithmic target cannot be met by the empty word.
example (B : ℝ) (hB : 2 < B) (ell : ℕ) (hell : 0 < ell) :
    ¬ B * ell ≤ ((GapWord.span ([] : GapWord) : ℕ) : ℝ) := by
  intro h
  have hB0 : 0 < B := lt_trans (by norm_num) hB
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hprod := mul_pos hB0 hellR
  simp [GapWord.span] at h
  linarith

-- A zero gap cannot be used to forge a valid odd-denominator trajectory.
example (Q q : ℕ) (line : AffineLine) (slopes : List ℚ) :
    ¬ OddDenominatorSegment.Valid Q
      { startLine := line, gaps := [0], slopes := slopes, q := q } := by
  intro h
  have : 0 < (0 : ℕ) := h.2.1 0 (by simp)
  omega

-- Greedy decomposition records completed blocks separately from the final
-- below-threshold remainder.
example :
    (GapWord.greedyDecompose [1, 2, 1] 3).completed = [[1, 2]] ∧
      (GapWord.greedyDecompose [1, 2, 1] 3).remainder = [1] := by
  decide

-- Every spatial source has a genuine selected block offset, bounded by the
-- window order; arbitrary offsets can no longer generate an infinite fibre.
example (Q Cgap : ℕ) (B Cstep : ℝ) (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding)
    (kb : ℕ × LowGapBlock)
    (hkb : kb ∈ spatialPreimage Q Cgap B Cstep W Z0 selection σ) :
    ∃ data : AnchorInteriorData,
      selection kb.1 = some data ∧
        sourceWindowOffset W kb.1 data kb.2 < W.m := by
  change IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ kb at hkb
  rcases hkb with ⟨data, _t, hreconstructed, _hparameter⟩
  exact ⟨data, hreconstructed.1, hreconstructed.2.2.2.2.2.1⟩

-- An initially exterior trajectory has exactly the canonical initial-exterior
-- record; it cannot carry arbitrary unused record fields.
example (Q : ℕ) (base : AffineLine) :
    FirstExitRecord.ofFirstExit Q base [] =
      FirstExitRecord.initialExterior := by simp

-- Infinite ENNReal mass cannot be equipped with the certificate required for
-- conversion to a real mass.
example (E : Set WindowThreshold) (weight : WindowThreshold → ℝ)
    (hinfinite : mass E weight = ∞) : ¬ FiniteMass E weight := by
  intro hfinite
  exact hfinite.ne_top hinfinite

-- The DeepMind endpoint intentionally retains its `n = 0` division and
-- negative integer exponent semantics.
example : (1 : ℝ) / (0 : ℕ) = 0 := by norm_num
example : integerSequenceTerm (fun _ => (-1 : ℤ)) 0 = -2 := by
  norm_num [integerSequenceTerm]

-- Deleting a finite nonpositive prefix gives the expected first positive
-- natural term.
example : positiveTail (fun n => (n : ℤ) - 2) 3 0 = 1 := by
  norm_num [positiveTail]

-- The public endpoint must not depend on proof placeholders or project-local
-- mathematical axioms.  The expected output is exactly Lean's standard
-- classical foundation: `propext`, `Classical.choice`, and `Quot.sound`.
#print axioms erdos_260

end Erdos260
