import ErdosProblems.Erdos260.Uniformity
import ErdosProblems.Erdos260.SequenceBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Exact partition, integrated upper bound, and the main theorem

This module corresponds to Section 8 and contains the paper's public theorem
and sequence corollary.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace Erdos260

/-- The four parent families form a literal disjoint partition. -/
def ParentPartition (W : WindowSystem) (Z0 : ℕ) : Prop :=
  W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪
      interiorPairs W Z0 ∪ exteriorPairs W Z0 = W.pairSet ∧
    W.boundedPairs Z0 ∩ rareLargePairs W Z0 = ∅ ∧
    W.boundedPairs Z0 ∩ interiorPairs W Z0 = ∅ ∧
    W.boundedPairs Z0 ∩ exteriorPairs W Z0 = ∅ ∧
    rareLargePairs W Z0 ∩ interiorPairs W Z0 = ∅ ∧
    rareLargePairs W Z0 ∩ exteriorPairs W Z0 = ∅ ∧
    interiorPairs W Z0 ∩ exteriorPairs W Z0 = ∅

/-- Scale-local form of the continuation dichotomy.  Lemma `lem_dichotomy`
supplies this predicate only after the cutoff and scale are sufficiently
large; it is therefore an explicit input to the exact partition theorem. -/
def ExactContinuationDichotomy (W : WindowSystem) (Z0 : ℕ) : Prop :=
  ∀ e : WindowThreshold, e ∈ W.largePairs Z0 →
    IsFrequentPrefix W Z0 (initialLongPrefix W e.1) →
      (LongInteriorPair W Z0 e ∨ LongExteriorPair W Z0 e) ∧
      ¬ (LongInteriorPair W Z0 e ∧ LongExteriorPair W Z0 e)

local instance : Countable AffineLine := by
  let code : AffineLine → ℤ × ℤ × ℤ × ℤ := fun line =>
    (line.A, line.C, line.H, line.K)
  exact (show Function.Injective code from by
    intro line₁ line₂ h
    cases line₁
    cases line₂
    simp only [code, Prod.mk.injEq] at h
    simp_all).countable

private theorem measurableSet_exists_le_countable {α β : Type*}
    [Countable α] [MeasurableSpace β] (f : β → ℝ) (hf : Measurable f)
    (P : α → Prop) (c : α → ℝ) :
    MeasurableSet {x | ∃ a, P a ∧ f x ≤ c a} := by
  classical
  rw [show {x | ∃ a, P a ∧ f x ≤ c a} =
      ⋃ a, if P a then {x | f x ≤ c a} else ∅ by
    ext x
    simp]
  exact MeasurableSet.iUnion fun a => by
    by_cases ha : P a
    · simpa [ha] using measurableSet_le hf measurable_const
    · simp [ha]

private theorem measurableSet_windowThreshold_of_sections
    (E : Set WindowThreshold)
    (hsection : ∀ k : ℕ, MeasurableSet {T : ℝ | (k, T) ∈ E}) :
    MeasurableSet E := by
  rw [show E = ⋃ k : ℕ, Set.prod {k} {T : ℝ | (k, T) ∈ E} by
    ext e
    rcases e with ⟨k, T⟩
    rw [Set.mem_iUnion]
    change (k, T) ∈ E ↔
      ∃ i : ℕ, (k, T) ∈ Set.prod {i} {u : ℝ | (i, u) ∈ E}
    constructor
    · intro h
      exact ⟨k, ⟨by simp, h⟩⟩
    · rintro ⟨i, hi⟩
      have hik : k = i := hi.1
      subst i
      exact hi.2]
  exact MeasurableSet.iUnion fun k =>
    (MeasurableSet.singleton k).prod (hsection k)

theorem measurableSet_boundedPairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (W.boundedPairs Z0) := by
  exact W.measurableSet_pairSet.inter
    (measurableSet_le W.measurable_excess
      (measurable_const : Measurable
        (fun _ : WindowThreshold => (W.m : ℝ) * Z0)))

theorem measurableSet_largePairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (W.largePairs Z0) := by
  exact W.measurableSet_pairSet.inter
    (measurableSet_lt
      (measurable_const : Measurable
        (fun _ : WindowThreshold => (W.m : ℝ) * Z0))
      W.measurable_excess)

private theorem measurableSet_longInteriorPair_section
    (W : WindowSystem) (Z0 k : ℕ) :
    MeasurableSet {T : ℝ | LongInteriorPair W Z0 (k, T)} := by
  classical
  have hlargeSection :
      MeasurableSet {T : ℝ | (k, T) ∈ W.largePairs Z0} :=
    (measurableSet_largePairs W Z0).preimage measurable_prodMk_left
  let P : AffineLine × GapWord → Prop := fun lg =>
    IsActualInitialContinuation W Z0 (k, 0) lg.1 lg.2 ∧
      IsInteriorTrajectory W.rational.eta.den lg.1 lg.2
  have hexists : MeasurableSet
      {T : ℝ | ∃ lg : AffineLine × GapWord,
        P lg ∧ W.excess (k, T) / 8 ≤ (lg.2.span : ℝ)} := by
    apply measurableSet_exists_le_countable
    exact W.measurable_excess.comp measurable_prodMk_left |>.div_const 8
  by_cases hfreq : IsFrequentPrefix W Z0 (initialLongPrefix W k)
  · have heq : {T : ℝ | LongInteriorPair W Z0 (k, T)} =
        {T | (k, T) ∈ W.largePairs Z0 ∧
          ∃ lg : AffineLine × GapWord,
            P lg ∧ W.excess (k, T) / 8 ≤ (lg.2.span : ℝ)} := by
      ext T
      change
        ((k, T) ∈ W.largePairs Z0 ∧
          IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
          ∃ line gaps,
            IsActualInitialContinuation W Z0 (k, T) line gaps ∧
            IsInteriorTrajectory W.rational.eta.den line gaps ∧
            W.excess (k, T) / 8 ≤ (gaps.span : ℝ)) ↔ _
      have hactual : ∀ line gaps,
          IsActualInitialContinuation W Z0 (k, T) line gaps ↔
            IsActualInitialContinuation W Z0 (k, 0) line gaps := by
        intro line gaps
        rfl
      simp only [hfreq, true_and, hactual, P]
      constructor <;> aesop
    rw [heq]
    exact hlargeSection.inter hexists
  · have heq : {T : ℝ | LongInteriorPair W Z0 (k, T)} = ∅ := by
      ext T
      constructor
      · intro h
        exact (hfreq h.2.1).elim
      · intro h
        exact h.elim
    rw [heq]
    exact MeasurableSet.empty

private theorem measurableSet_longExteriorPair_section
    (W : WindowSystem) (Z0 k : ℕ) :
    MeasurableSet {T : ℝ | LongExteriorPair W Z0 (k, T)} := by
  classical
  have hlargeSection :
      MeasurableSet {T : ℝ | (k, T) ∈ W.largePairs Z0} :=
    (measurableSet_largePairs W Z0).preimage measurable_prodMk_left
  have hinteriorSection :
      MeasurableSet {T : ℝ | LongInteriorPair W Z0 (k, T)} :=
    measurableSet_longInteriorPair_section W Z0 k
  let P : AffineLine × GapWord → Prop := fun lg =>
    IsActualFirstExteriorContinuation W Z0 (k, 0) lg.1 lg.2 ∧
      IsExteriorTrajectory W.rational.eta.den lg.1 lg.2
  have hexists : MeasurableSet
      {T : ℝ | ∃ lg : AffineLine × GapWord,
        P lg ∧ W.excess (k, T) / 4 ≤ (lg.2.span : ℝ)} := by
    apply measurableSet_exists_le_countable
    exact W.measurable_excess.comp measurable_prodMk_left |>.div_const 4
  by_cases hfreq : IsFrequentPrefix W Z0 (initialLongPrefix W k)
  · have heq : {T : ℝ | LongExteriorPair W Z0 (k, T)} =
        {T | (k, T) ∈ W.largePairs Z0 ∧
          ¬ LongInteriorPair W Z0 (k, T) ∧
          ∃ lg : AffineLine × GapWord,
            P lg ∧ W.excess (k, T) / 4 ≤ (lg.2.span : ℝ)} := by
      ext T
      change
        ((k, T) ∈ W.largePairs Z0 ∧
          IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
          ¬ LongInteriorPair W Z0 (k, T) ∧
          ∃ line gaps,
            IsActualFirstExteriorContinuation W Z0 (k, T) line gaps ∧
            IsExteriorTrajectory W.rational.eta.den line gaps ∧
            W.excess (k, T) / 4 ≤ (gaps.span : ℝ)) ↔ _
      have hactual : ∀ line gaps,
          IsActualFirstExteriorContinuation W Z0 (k, T) line gaps ↔
            IsActualFirstExteriorContinuation W Z0 (k, 0) line gaps := by
        intro line gaps
        rfl
      simp only [hfreq, true_and, hactual, P]
      constructor <;> aesop
    rw [heq]
    convert (hlargeSection.inter hinteriorSection.compl).inter hexists using 1
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    aesop
  · have heq : {T : ℝ | LongExteriorPair W Z0 (k, T)} = ∅ := by
      ext T
      constructor
      · intro h
        exact (hfreq h.2.1).elim
      · intro h
        exact h.elim
    rw [heq]
    exact MeasurableSet.empty

theorem measurableSet_rareLargePairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (rareLargePairs W Z0) := by
  apply measurableSet_windowThreshold_of_sections
  intro k
  have hlargeSection :
      MeasurableSet {T : ℝ | (k, T) ∈ W.largePairs Z0} :=
    (measurableSet_largePairs W Z0).preimage measurable_prodMk_left
  by_cases hrare : IsRarePrefix W Z0 (initialLongPrefix W k)
  · simpa [rareLargePairs, hrare] using hlargeSection
  · have heq : {T : ℝ | (k, T) ∈ rareLargePairs W Z0} = ∅ := by
      ext T
      simp [rareLargePairs, hrare]
    rw [heq]
    exact MeasurableSet.empty

theorem measurableSet_interiorPairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (interiorPairs W Z0) := by
  apply measurableSet_windowThreshold_of_sections
  intro k
  exact measurableSet_longInteriorPair_section W Z0 k

theorem measurableSet_exteriorPairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (exteriorPairs W Z0) := by
  apply measurableSet_windowThreshold_of_sections
  intro k
  exact measurableSet_longExteriorPair_section W Z0 k

theorem refinedInteriorMass_eq_mass {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) :
    refinedInteriorMass refinement = mass (interiorPairs W Z0) W.excess := by
  unfold refinedInteriorMass mass
  apply setLIntegral_congr_fun (measurableSet_interiorPairs W Z0)
  intro e he
  apply congrArg ENNReal.ofReal
  have hsum := refinement.sums_to_excess e he
  calc
    (∑ b ∈ (refinement.blocks e.1).toFinset,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b) =
        ∑ b ∈ refinement.labels e, refinement.weight e b := by
          rw [refinement.labels_eq e he]
          apply Finset.sum_congr rfl
          intro b hb
          symm
          apply refinement.weight_eq e he b
          simpa [refinement.labels_eq e he] using hb
    _ = W.excess e := hsum

private theorem parentPartition_of_exactContinuationDichotomy
    (W : WindowSystem) (Z0 : ℕ)
    (hdichotomy : ExactContinuationDichotomy W Z0) :
    ParentPartition W Z0 := by
  unfold ParentPartition
  have hunion :
      W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪
          interiorPairs W Z0 ∪ exteriorPairs W Z0 = W.pairSet := by
    apply Set.Subset.antisymm
    · intro e he
      rcases he with (((hbounded | hrare) | hinterior) | hexterior)
      · exact hbounded.1
      · exact hrare.1.1
      · exact hinterior.1.1
      · exact hexterior.1.1
    · intro e he
      by_cases hbounded : W.excess e ≤ (W.m : ℝ) * Z0
      · exact Or.inl (Or.inl (Or.inl ⟨he, hbounded⟩))
      · have hlarge : e ∈ W.largePairs Z0 :=
          ⟨he, lt_of_not_ge hbounded⟩
        by_cases hfrequent :
            IsFrequentPrefix W Z0 (initialLongPrefix W e.1)
        · rcases (hdichotomy e hlarge hfrequent).1 with
            hinterior | hexterior
          · exact Or.inl (Or.inr hinterior)
          · exact Or.inr hexterior
        · have hrarePrefix :
              IsRarePrefix W Z0 (initialLongPrefix W e.1) := by
            unfold IsRarePrefix
            change ¬ frequencyCutoff W ≤
              prefixMultiplicity W Z0 (initialLongPrefix W e.1) at hfrequent
            exact lt_of_not_ge hfrequent
          exact Or.inl (Or.inl (Or.inr ⟨hlarge, hrarePrefix⟩))
  refine ⟨hunion, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hbounded := he.1.2
    have hlarge := he.2.1.2
    change W.excess e ≤ (W.m : ℝ) * Z0 at hbounded
    change (W.m : ℝ) * Z0 < W.excess e at hlarge
    exact (not_lt_of_ge hbounded) hlarge
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hbounded := he.1.2
    have hlarge := he.2.1.2
    change W.excess e ≤ (W.m : ℝ) * Z0 at hbounded
    change (W.m : ℝ) * Z0 < W.excess e at hlarge
    exact (not_lt_of_ge hbounded) hlarge
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hbounded := he.1.2
    have hlarge := he.2.1.2
    change W.excess e ≤ (W.m : ℝ) * Z0 at hbounded
    change (W.m : ℝ) * Z0 < W.excess e at hlarge
    exact (not_lt_of_ge hbounded) hlarge
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hrare := he.1.2
    have hfrequent := he.2.2.1
    change (prefixMultiplicity W Z0 (initialLongPrefix W e.1) : ℝ) <
      frequencyCutoff W at hrare
    unfold IsFrequentPrefix at hfrequent
    exact (not_lt_of_ge hfrequent) hrare
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hrare := he.1.2
    have hfrequent := he.2.2.1
    change (prefixMultiplicity W Z0 (initialLongPrefix W e.1) : ℝ) <
      frequencyCutoff W at hrare
    unfold IsFrequentPrefix at hfrequent
    exact (not_lt_of_ge hfrequent) hrare
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact he.2.2.2.1 he.1

private theorem mass_union_of_disjoint {E F : Set WindowThreshold}
    {weight : WindowThreshold → ℝ} (hF : MeasurableSet F)
    (hdisjoint : Disjoint E F) :
    mass (E ∪ F) weight = mass E weight + mass F weight := by
  unfold mass
  exact lintegral_union hF hdisjoint

/-- Paper label: `prop:exact-source-decomp` (Section 8). -/
theorem prop_exact_source_decomp (W : WindowSystem) (Z0 : ℕ)
    (hdichotomy : ExactContinuationDichotomy W Z0)
    (refinement : InteriorRefinement W Z0) :
    ParentPartition W Z0 ∧ MeasurableSet W.pairSet ∧
    MeasurableSet (W.boundedPairs Z0) ∧
    MeasurableSet (rareLargePairs W Z0) ∧
    MeasurableSet (interiorPairs W Z0) ∧
    MeasurableSet (exteriorPairs W Z0) ∧
    FiniteMass W.pairSet W.excess ∧
    mass W.pairSet W.excess =
      mass (W.boundedPairs Z0) W.excess +
      mass (rareLargePairs W Z0) W.excess +
      refinedInteriorMass refinement +
      mass (exteriorPairs W Z0) W.excess ∧
    refinedInteriorMass refinement = mass (interiorPairs W Z0) W.excess := by
  have hpartition :=
    parentPartition_of_exactContinuationDichotomy W Z0 hdichotomy
  have hpair := W.measurableSet_pairSet
  have hbounded := measurableSet_boundedPairs W Z0
  have hrare := measurableSet_rareLargePairs W Z0
  have hinterior := measurableSet_interiorPairs W Z0
  have hexterior := measurableSet_exteriorPairs W Z0
  have hrefined := refinedInteriorMass_eq_mass refinement
  have hAB : Disjoint (W.boundedPairs Z0) (rareLargePairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.1
  have hAC : Disjoint (W.boundedPairs Z0) (interiorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.1
  have hAD : Disjoint (W.boundedPairs Z0) (exteriorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.2.1
  have hBC : Disjoint (rareLargePairs W Z0) (interiorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.2.2.1
  have hBD : Disjoint (rareLargePairs W Z0) (exteriorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.2.2.2.1
  have hCD : Disjoint (interiorPairs W Z0) (exteriorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.2.2.2.2
  have hAB_C :
      Disjoint (W.boundedPairs Z0 ∪ rareLargePairs W Z0)
        (interiorPairs W Z0) := by
    apply Set.disjoint_left.2
    intro e heAB heC
    rcases heAB with heA | heB
    · exact Set.disjoint_left.1 hAC heA heC
    · exact Set.disjoint_left.1 hBC heB heC
  have hABC_D :
      Disjoint
        (W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪ interiorPairs W Z0)
        (exteriorPairs W Z0) := by
    apply Set.disjoint_left.2
    intro e heABC heD
    rcases heABC with (heA | heB) | heC
    · exact Set.disjoint_left.1 hAD heA heD
    · exact Set.disjoint_left.1 hBD heB heD
    · exact Set.disjoint_left.1 hCD heC heD
  have hmass :
      mass W.pairSet W.excess =
        mass (W.boundedPairs Z0) W.excess +
        mass (rareLargePairs W Z0) W.excess +
        refinedInteriorMass refinement +
        mass (exteriorPairs W Z0) W.excess := by
    calc
      mass W.pairSet W.excess =
          mass
            (W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪
              interiorPairs W Z0 ∪ exteriorPairs W Z0)
            W.excess := congrArg (fun E => mass E W.excess) hpartition.1.symm
      _ = mass
              (W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪
                interiorPairs W Z0) W.excess +
            mass (exteriorPairs W Z0) W.excess :=
        mass_union_of_disjoint hexterior hABC_D
      _ = (mass (W.boundedPairs Z0 ∪ rareLargePairs W Z0) W.excess +
              mass (interiorPairs W Z0) W.excess) +
            mass (exteriorPairs W Z0) W.excess := by
        rw [mass_union_of_disjoint hinterior hAB_C]
      _ = ((mass (W.boundedPairs Z0) W.excess +
              mass (rareLargePairs W Z0) W.excess) +
              mass (interiorPairs W Z0) W.excess) +
            mass (exteriorPairs W Z0) W.excess := by
        rw [mass_union_of_disjoint hrare hAB]
      _ = mass (W.boundedPairs Z0) W.excess +
            mass (rareLargePairs W Z0) W.excess +
            refinedInteriorMass refinement +
            mass (exteriorPairs W Z0) W.excess := by
        rw [hrefined]
  exact ⟨hpartition, hpair, hbounded, hrare, hinterior, hexterior,
    totalFiniteMass W, hmass, hrefined⟩

private theorem finiteWindowMass_nonneg (W : WindowSystem)
    (E : Set WindowThreshold) (hE : E ⊆ W.pairSet) :
    0 ≤ finiteWindowMass W E hE := by
  change 0 ≤ (finiteMassOfSubset W E hE).toReal
  exact FiniteMass.toReal_nonneg _

private theorem ofReal_finiteWindowMass (W : WindowSystem)
    (E : Set WindowThreshold) (hE : E ⊆ W.pairSet) :
    ENNReal.ofReal (finiteWindowMass W E hE) = mass E W.excess := by
  change ENNReal.ofReal (finiteMassOfSubset W E hE).toReal = mass E W.excess
  exact FiniteMass.ofReal_toReal _

/-- Safe real-valued form of the exact parent decomposition.  Every real
conversion is backed by `finiteMassOfSubset`; in particular no infinite
`ENNReal` mass is ever silently mapped to zero. -/
theorem integratedExcess_exact_decomposition (W : WindowSystem) (Z0 : ℕ)
    (hdichotomy : ExactContinuationDichotomy W Z0)
    (refinement : InteriorRefinement W Z0) :
    integratedExcess W =
      boundedPairsMass W Z0 + rareLargePairsMass W Z0 +
      interiorPairsMass W Z0 + exteriorPairsMass W Z0 := by
  obtain ⟨_, _, _, _, _, _, _, hmass, hrefined⟩ :=
    prop_exact_source_decomp W Z0 hdichotomy refinement
  rw [hrefined] at hmass
  have htotal : 0 ≤ integratedExcess W := by
    change 0 ≤ (totalFiniteMass W).toReal
    exact FiniteMass.toReal_nonneg _
  have hbounded : 0 ≤ boundedPairsMass W Z0 := by
    exact finiteWindowMass_nonneg W (W.boundedPairs Z0)
      (boundedPairs_subset_pairSet W Z0)
  have hrare : 0 ≤ rareLargePairsMass W Z0 := by
    exact finiteWindowMass_nonneg W (rareLargePairs W Z0)
      (rareLargePairs_subset_pairSet W Z0)
  have hinterior : 0 ≤ interiorPairsMass W Z0 := by
    exact finiteWindowMass_nonneg W (interiorPairs W Z0)
      (interiorPairs_subset_pairSet W Z0)
  have hexterior : 0 ≤ exteriorPairsMass W Z0 := by
    exact finiteWindowMass_nonneg W (exteriorPairs W Z0)
      (exteriorPairs_subset_pairSet W Z0)
  have hsum : 0 ≤
      boundedPairsMass W Z0 + rareLargePairsMass W Z0 +
      interiorPairsMass W Z0 + exteriorPairsMass W Z0 := by
    positivity
  have hbounded_ofReal :
      ENNReal.ofReal (boundedPairsMass W Z0) =
        mass (W.boundedPairs Z0) W.excess := by
    unfold boundedPairsMass
    exact ofReal_finiteWindowMass W (W.boundedPairs Z0)
      (boundedPairs_subset_pairSet W Z0)
  have hrare_ofReal :
      ENNReal.ofReal (rareLargePairsMass W Z0) =
        mass (rareLargePairs W Z0) W.excess := by
    unfold rareLargePairsMass
    exact ofReal_finiteWindowMass W (rareLargePairs W Z0)
      (rareLargePairs_subset_pairSet W Z0)
  have hinterior_ofReal :
      ENNReal.ofReal (interiorPairsMass W Z0) =
        mass (interiorPairs W Z0) W.excess := by
    unfold interiorPairsMass
    exact ofReal_finiteWindowMass W (interiorPairs W Z0)
      (interiorPairs_subset_pairSet W Z0)
  have hexterior_ofReal :
      ENNReal.ofReal (exteriorPairsMass W Z0) =
        mass (exteriorPairs W Z0) W.excess := by
    unfold exteriorPairsMass
    exact ofReal_finiteWindowMass W (exteriorPairs W Z0)
      (exteriorPairs_subset_pairSet W Z0)
  apply (ENNReal.ofReal_eq_ofReal_iff htotal hsum).mp
  calc
    ENNReal.ofReal (integratedExcess W) =
        mass W.pairSet W.excess := ofReal_integratedExcess W
    _ = mass (W.boundedPairs Z0) W.excess +
          mass (rareLargePairs W Z0) W.excess +
          mass (interiorPairs W Z0) W.excess +
          mass (exteriorPairs W Z0) W.excess := hmass
    _ = ENNReal.ofReal
          (boundedPairsMass W Z0 + rareLargePairsMass W Z0 +
            interiorPairsMass W Z0 + exteriorPairsMass W Z0) := by
      rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hbounded hrare) hinterior)
          hexterior,
        ENNReal.ofReal_add (add_nonneg hbounded hrare) hinterior,
        ENNReal.ofReal_add hbounded hrare,
        hbounded_ofReal, hrare_ofReal, hinterior_ofReal, hexterior_ofReal]

/-- Paper label: `prop:upper` (Section 8).  The cutoff and vanishing error are
selected from the denominator-level context before the numerator/support
family and before the pointwise density deficit. -/
theorem prop_upper (context : FixedScaleContext) :
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
                normalizationScale (F.system L) := by
  intro θ hθ
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  obtain ⟨Zdichotomy, hdichotomy⟩ := lem_dichotomy context gap
  obtain ⟨Zuniform, interiorBound, hinterior_nonneg, hinterior_zero,
      huniform⟩ := prop_uniform_errors context
  obtain ⟨Zstrict, ηQ, hηQ_nonneg, hηQ_zero, hstrict⟩ :=
    thm_strict_mass context
  have hinterior_small : ∀ᶠ Z : ℕ in atTop, interiorBound Z < θ / 3 :=
    (tendsto_order.1 hinterior_zero).2 _ (by linarith)
  obtain ⟨Zsmall, hZsmall⟩ := eventually_atTop.1 hinterior_small
  let Z0 := max Zsmall (max Zdichotomy (max Zuniform Zstrict))
  have hZsmall_le : Zsmall ≤ Z0 := le_max_left _ _
  have hZdichotomy : Zdichotomy ≤ Z0 := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hZuniform : Zuniform ≤ Z0 := by
    exact le_trans
      (le_trans (le_max_left _ _) (le_max_right Zdichotomy _))
      (le_max_right Zsmall _)
  have hZstrict : Zstrict ≤ Z0 := by
    exact le_trans
      (le_trans (le_max_right _ _) (le_max_right Zdichotomy _))
      (le_max_right Zsmall _)
  have hbound_small : interiorBound Z0 < θ / 3 :=
    hZsmall Z0 hZsmall_le
  refine ⟨Z0, (fun _ : ℕ => (0 : ℝ)), tendsto_const_nhds, ?_⟩
  intro F hF
  obtain ⟨_hboundary, hrare_all, hexterior_all, hinterior_all⟩ :=
    huniform F hF
  have hrare_zero :
      Tendsto (fun L => rareMassRatio (F.system L) Z0) atTop (𝓝 0) := by
    simpa [rareMassRatio] using
      (hrare_all Z0 hZuniform).tendsto_div_nhds_zero
  have hexterior_zero :
      Tendsto (fun L => exteriorMassRatio (F.system L) Z0) atTop (𝓝 0) := by
    simpa [exteriorMassRatio] using
      (hexterior_all Z0 hZuniform).tendsto_div_nhds_zero
  have hrare_small : ∀ᶠ L : ℕ in atTop,
      rareMassRatio (F.system L) Z0 < θ / 3 :=
    (tendsto_order.1 hrare_zero).2 _ (by linarith)
  have hexterior_small : ∀ᶠ L : ℕ in atTop,
      exteriorMassRatio (F.system L) Z0 < θ / 3 :=
    (tendsto_order.1 hexterior_zero).2 _ (by linarith)
  filter_upwards [hdichotomy Z0 hZdichotomy F hF,
      hstrict Z0 hZstrict F hF,
      hinterior_all Z0 hZuniform,
      hrare_small, hexterior_small, eventually_ge_atTop 1] with
      L hLdichotomy hLstrict hLinterior hLrare hLexterior hLpos
  intro cstar hcstar hsparse
  obtain ⟨refinement, _hrefinement_bound⟩ := hLstrict
  have hnormalization : 0 < normalizationScale (F.system L) := by
    rw [normalizationScale, thresholdLength, F.level_eq]
    have hm : (0 : ℝ) < (F.system L).m := by
      exact_mod_cast Nat.succ_pos (F.system L).s
    have hX : (0 : ℝ) < (F.system L).X := by
      exact_mod_cast pow_pos (by decide : 0 < (2 : ℕ)) (F.system L).L
    have hcI : 0 < (F.system L).structural.cI :=
      (F.system L).structural.cI_pos
    have hLreal : (0 : ℝ) < L := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hLpos)
    positivity
  have hrare_mass : rareLargePairsMass (F.system L) Z0 ≤
      (θ / 3) * normalizationScale (F.system L) := by
    have h := mul_lt_mul_of_pos_right hLrare hnormalization
    simpa [rareMassRatio, hnormalization.ne'] using h.le
  have hexterior_mass : exteriorPairsMass (F.system L) Z0 ≤
      (θ / 3) * normalizationScale (F.system L) := by
    have h := mul_lt_mul_of_pos_right hLexterior hnormalization
    simpa [exteriorMassRatio, hnormalization.ne'] using h.le
  have hinterior_ratio : interiorMassRatio (F.system L) Z0 < θ / 3 :=
    lt_of_le_of_lt hLinterior hbound_small
  have hinterior_mass : interiorPairsMass (F.system L) Z0 ≤
      (θ / 3) * normalizationScale (F.system L) := by
    have h := mul_lt_mul_of_pos_right hinterior_ratio hnormalization
    simpa [interiorMassRatio, hnormalization.ne'] using h.le
  have hmoderate : boundedPairsMass (F.system L) Z0 ≤
      ((Z0 : ℝ) * cstar) * normalizationScale (F.system L) := by
    simpa [normalizationScale, mul_assoc] using
      prop_moderate (F.system L) Z0 cstar hcstar.1 hsparse
  have hexact : ExactContinuationDichotomy (F.system L) Z0 :=
    hLdichotomy
  rw [integratedExcess_exact_decomposition (F.system L) Z0 hexact refinement]
  calc
    boundedPairsMass (F.system L) Z0 +
          rareLargePairsMass (F.system L) Z0 +
          interiorPairsMass (F.system L) Z0 +
          exteriorPairsMass (F.system L) Z0 ≤
        ((Z0 : ℝ) * cstar) * normalizationScale (F.system L) +
          (θ / 3) * normalizationScale (F.system L) +
          (θ / 3) * normalizationScale (F.system L) +
          (θ / 3) * normalizationScale (F.system L) := by
      gcongr
    _ = ((Z0 : ℝ) * cstar + θ + (fun _ : ℕ => (0 : ℝ)) L) *
          normalizationScale (F.system L) := by ring

/-- Paper label: `thm:main-density` (Introduction / Section 8). -/
theorem thm_main_density :
    ∀ Q : ℕ, 0 < Q →
      ∃ cDensity : ℝ, 0 < cDensity ∧
        ∀ S : Set ℕ, ∀ η : ℚ, η.den = Q → S.Infinite →
          HasSum (weightedSupportTerm S) (η : ℝ) →
          ∀ᶠ L : ℕ in atTop,
            cDensity * dyadicScale L ≤
              (dyadicBlockCount S (dyadicScale L) : ℝ) := by
  intro Q hQ
  obtain ⟨p, entropy, hstructural⟩ := exists_structural_entropy_params
  obtain ⟨ε, cLower, deltaLower, hε, hcLower, hdeltaLower,
      L0, hpressure⟩ := prop_pressure Q hQ p entropy hstructural
  let context : FixedScaleContext :=
    { Q := Q
      Q_pos := hQ
      structural := p
      entropy := entropy
      entropy_structural := hstructural
      epsilon := ε
      epsilon_pos := hε }
  let θ : ℝ := cLower / 4
  have hθ : 0 < θ := by
    dsimp [θ]
    positivity
  obtain ⟨Z0, error, herror, hupper⟩ := prop_upper context θ hθ
  let cDensity : ℝ :=
    min (1 / 2 : ℝ)
      (min (deltaLower / 2) (cLower / (8 * ((Z0 : ℝ) + 1))))
  have hcDensity : 0 < cDensity := by
    dsimp [cDensity]
    apply lt_min
    · norm_num
    · apply lt_min
      · linarith
      · positivity
  have hcDensity_one : cDensity ≤ 1 := by
    calc
      cDensity ≤ 1 / 2 := min_le_left _ _
      _ ≤ 1 := by norm_num
  have hcDensity_delta : cDensity ≤ deltaLower := by
    calc
      cDensity ≤ deltaLower / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      _ ≤ deltaLower := by linarith
  have hcutoff : (Z0 : ℝ) * cDensity < cLower / 4 := by
    have hbound : cDensity ≤ cLower / (8 * ((Z0 : ℝ) + 1)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hZnonneg : (0 : ℝ) ≤ Z0 := by positivity
    have hdenpos : 0 < 8 * ((Z0 : ℝ) + 1) := by positivity
    have hmul : (Z0 : ℝ) * cDensity ≤
        (Z0 : ℝ) * (cLower / (8 * ((Z0 : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hbound hZnonneg
    have hratio :
        (Z0 : ℝ) * (cLower / (8 * ((Z0 : ℝ) + 1))) <
          cLower / 8 := by
      calc
        (Z0 : ℝ) * (cLower / (8 * ((Z0 : ℝ) + 1))) =
            ((Z0 : ℝ) * cLower) / (8 * ((Z0 : ℝ) + 1)) := by ring
        _ < cLower / 8 := by
          rw [div_lt_div_iff₀ hdenpos (by norm_num : (0 : ℝ) < 8)]
          nlinarith
    exact lt_of_le_of_lt hmul (lt_trans hratio (by linarith))
  refine ⟨cDensity, hcDensity, ?_⟩
  intro S η hη hSinfinite hsum
  let rational : RationalSupport :=
    RationalSupport.normalize S η hSinfinite hsum
  let enumeration : SupportEnumeration rational.S :=
    supportEnumerationOfInfinite rational.S rational.infinite rational.positive
  let system : ℕ → WindowSystem := fun L =>
    { rational := rational
      enumeration := enumeration
      structural := p
      entropy := entropy
      entropy_structural := hstructural
      L := L
      s := Nat.floor (entropy.kappa * (L : ℝ))
      epsilon := ε
      epsilon_nonneg := hε.le }
  let F : ScaleFamily :=
    { rational := rational
      enumeration := enumeration
      structural := p
      entropy := entropy
      entropy_structural := hstructural
      epsilon := ε
      epsilon_nonneg := hε.le
      system := system
      level_eq := by intro L; rfl
      rational_eq := by intro L; rfl
      enumeration_eq := by intro L n; rfl
      structural_eq := by intro L; rfl
      entropy_eq := by intro L; rfl
      epsilon_eq := by intro L; rfl
      offset_eq := by intro L; rfl }
  have hmatches : F.MatchesContext context := by
    refine ⟨?_, rfl, rfl, rfl⟩
    simpa [F, rational, RationalSupport.normalize] using hη
  have herrorSmall : ∀ᶠ L : ℕ in atTop, error L < cLower / 4 :=
    (tendsto_order.1 herror).2 _ (by linarith)
  filter_upwards [hupper F hmatches, herrorSmall,
      eventually_ge_atTop L0, eventually_ge_atTop 1] with
      L hupperL herrorL hL0 hLpos
  by_contra hnot
  have hdeficit :
      (dyadicBlockCount S (dyadicScale L) : ℝ) <
        cDensity * dyadicScale L := lt_of_not_ge hnot
  have hsparse :
      (dyadicBlockCount (F.system L).rational.S (F.system L).X : ℝ) ≤
        cDensity * (F.system L).X := by
    have hlt :
        (dyadicBlockCount (F.system L).rational.S (F.system L).X : ℝ) <
          cDensity * (F.system L).X := by
      change
        (dyadicBlockCount (positiveSupport S) (dyadicScale L) : ℝ) <
          cDensity * dyadicScale L
      simpa only [dyadicBlockCount_positiveSupport] using hdeficit
    exact hlt.le
  have hlower := hpressure (F.system L) cDensity
    (by simpa [F, system, rational, RationalSupport.normalize] using hη)
    (by rfl) (by rfl) (by rfl) (by rfl) hL0 hcDensity
    hcDensity_delta hsparse
  have hupperBound := hupperL cDensity
    ⟨hcDensity.le, hcDensity_one⟩ hsparse
  have hnormalization : 0 < normalizationScale (F.system L) := by
    rw [normalizationScale, thresholdLength, F.level_eq]
    have hm : (0 : ℝ) < (F.system L).m := by
      exact_mod_cast Nat.succ_pos (F.system L).s
    have hX : (0 : ℝ) < (F.system L).X := by
      exact_mod_cast pow_pos (by decide : 0 < (2 : ℕ)) (F.system L).L
    have hcI : 0 < (F.system L).structural.cI :=
      (F.system L).structural.cI_pos
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hLpos
    positivity
  have hlower' : cLower * normalizationScale (F.system L) ≤
      integratedExcess (F.system L) := by
    simpa [normalizationScale, mul_assoc] using hlower
  have hcoefficient :
      (Z0 : ℝ) * cDensity + θ + error L < cLower := by
    dsimp [θ]
    linarith
  have hstrictUpper : integratedExcess (F.system L) <
      cLower * normalizationScale (F.system L) :=
    lt_of_le_of_lt hupperBound
      (mul_lt_mul_of_pos_right hcoefficient hnormalization)
  exact (not_lt_of_ge hlower') hstrictUpper

/-- Paper label: `cor:erdos260` (Introduction). -/
theorem cor_erdos260 (a : ℕ → ℕ) (ha : StrictMono a)
    (_hpositive : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / (n + 1)) atTop atTop) :
    Irrational (∑' n : ℕ, natSequenceTerm a n) := by
  by_contra hnot
  obtain ⟨η, hη⟩ := exists_rat_of_not_irrational hnot
  have hsum :
      HasSum (weightedSupportTerm (Set.range a)) (η : ℝ) := by
    rw [← hη]
    exact hasSum_range_weightedSupport a ha
  obtain ⟨cDensity, hcDensity, hmain⟩ :=
    thm_main_density η.den (Rat.den_pos η)
  have hlower := hmain (Set.range a) η rfl
    (range_infinite_of_strictMono a ha) hsum
  have hupper :=
    eventually_dyadicBlockCount_lt_of_growth a hgrowth cDensity hcDensity
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 hlower
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.1 hupper
  let L := max L₁ L₂
  exact (not_lt_of_ge (hL₁ L (le_max_left _ _)))
    (hL₂ L (le_max_right _ _))

end Erdos260
