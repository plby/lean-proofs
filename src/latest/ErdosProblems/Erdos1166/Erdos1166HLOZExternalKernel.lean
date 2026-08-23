import ErdosProblems.Erdos1166.Erdos1166HLOZExternalDeviationChain

namespace Erdos1166.HLOZExternalKernel

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

open HLOZExternalUpper HLOZExternalChain HLOZExternalDeviationChain
open HLOZFixedOriginKac

/-- One iid terminal-label macro increment (two external-chain steps). -/
def externalMacroIncrement (p : ExternalPairLabel) : Site :=
  directionStep (p.1 0) + directionStep (p.1 1)

/-- Macro position after `m` iid terminal labels. -/
def externalMacroPosition (labels : ℕ → ExternalPairLabel) (m : ℕ) : Site :=
  ∑ j ∈ Finset.range m, externalMacroIncrement (labels j)

theorem externalWalk_even_eq_macro
    (labels : ℕ → ExternalPairLabel) (m : ℕ) :
    externalWalk labels (2 * m) = externalMacroPosition labels m := by
  induction m with
  | zero => simp [externalWalk, simpleRandomWalk, externalMacroPosition]
  | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        externalWalk_succ, show 2 * m + 1 = 2 * m + 1 by rfl,
        externalWalk_succ, ih]
      simp only [externalMacroPosition, Finset.sum_range_succ]
      have hdiv : (2 * m + 1) / 2 = m := by omega
      simp [externalDirectionStream, pairOffset, externalMacroIncrement, hdiv]
      abel

/-! ### Disjoint macro blocks -/

/-- Add the deterministic initial macro time zero before the selected times. -/
def augmentedMacroTimes {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) :
    CollisionKernel.TimeTuple n (k + 2) :=
  Fin.cases 0 (fun i ↦ ⟨(t i).val / 2, by omega⟩)

@[simp] theorem augmentedMacroTimes_zero {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) :
    augmentedMacroTimes t 0 = 0 := rfl

@[simp] theorem augmentedMacroTimes_succ {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin (k + 1)) :
    (augmentedMacroTimes t i.succ).val = (t i).val / 2 := rfl

@[simp] theorem augmentedMacroTimes_succ_castSucc {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin k) :
    (augmentedMacroTimes t i.succ.castSucc).val =
      (t i.castSucc).val / 2 := by
  change (augmentedMacroTimes t i.castSucc.succ).val = _
  rfl

theorem monotone_augmentedMacroTimes {n k : ℕ}
    {t : KacMoment.TimeTuple n (k + 1)} (ht : Monotone t) :
    Monotone (augmentedMacroTimes t) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp only [Fin.castSucc_fin_succ, augmentedMacroTimes_succ]
    exact Nat.div_le_div_right (Fin.val_le_of_le
      (ht (Fin.castSucc_le_succ j)))

abbrev ExternalGapIndex {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin (k + 1)) :=
  CollisionKernel.GapIndex (augmentedMacroTimes t) i

def extractExternalBlocks {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1))
    (labels : ℕ → ExternalPairLabel) :
    (i : Fin (k + 1)) → ExternalGapIndex t i → ExternalPairLabel :=
  fun i j ↦ labels (CollisionKernel.blockCoord (augmentedMacroTimes t) ⟨i, j⟩)

theorem measurable_extractExternalBlocks {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) :
    Measurable (extractExternalBlocks t) := by
  unfold extractExternalBlocks
  fun_prop

noncomputable abbrev externalBlockLaw {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin (k + 1)) :
    Measure (ExternalGapIndex t i → ExternalPairLabel) :=
  Measure.infinitePi fun _ : ExternalGapIndex t i ↦ externalPairLabelLaw

theorem extractExternalBlocks_map {n k : ℕ}
    {t : KacMoment.TimeTuple n (k + 1)} (ht : Monotone t) :
    externalLabelLaw.map (extractExternalBlocks t) =
      Measure.infinitePi (externalBlockLaw t) := by
  let flat : (ℕ → ExternalPairLabel) →
      ((i : Fin (k + 1)) × ExternalGapIndex t i) → ExternalPairLabel :=
    fun labels p ↦ labels
      (CollisionKernel.blockCoord (augmentedMacroTimes t) p)
  let curryEquiv := MeasurableEquiv.piCurry
    (fun i : Fin (k + 1) ↦ fun _ : ExternalGapIndex t i ↦ ExternalPairLabel)
  have hfun : extractExternalBlocks t = curryEquiv ∘ flat := by
    funext labels i j
    rfl
  rw [hfun, ← Measure.map_map curryEquiv.measurable (by fun_prop)]
  unfold externalLabelLaw
  rw [Measure.map_infinitePi_infinitePi_of_inj
    (CollisionKernel.blockCoord_injective
      (monotone_augmentedMacroTimes ht))]
  change Measure.map curryEquiv
      (Measure.infinitePi fun _ :
        ((i : Fin (k + 1)) × ExternalGapIndex t i) ↦
          (PMF.uniformOfFintype ExternalPairLabel).toMeasure) =
    Measure.infinitePi fun i : Fin (k + 1) ↦
      Measure.infinitePi fun _ : ExternalGapIndex t i ↦
        (PMF.uniformOfFintype ExternalPairLabel).toMeasure
  simpa [curryEquiv] using
    (Measure.infinitePi_map_piCurry
      (fun i : Fin (k + 1) ↦ fun _ : ExternalGapIndex t i ↦
        (PMF.uniformOfFintype ExternalPairLabel).toMeasure))

def externalFiniteMacroPosition {ι : Type*} [Fintype ι]
    (w : ι → ExternalPairLabel) : Site :=
  ∑ j, externalMacroIncrement (w j)

theorem finitePosition_extractExternalBlock {n k : ℕ}
    {t : KacMoment.TimeTuple n (k + 1)} (ht : Monotone t)
    (i : Fin (k + 1)) (labels : ℕ → ExternalPairLabel) :
    externalFiniteMacroPosition (extractExternalBlocks t labels i) =
      externalMacroPosition labels
          ((augmentedMacroTimes t i.succ).val) -
        externalMacroPosition labels
          ((augmentedMacroTimes t i.castSucc).val) := by
  have ht' := monotone_augmentedMacroTimes ht
  have hab : (augmentedMacroTimes t i.castSucc).val ≤
      (augmentedMacroTimes t i.succ).val :=
    Fin.val_le_of_le (ht' (Fin.castSucc_le_succ i))
  let a := (augmentedMacroTimes t i.castSucc).val
  let b := (augmentedMacroTimes t i.succ).val
  let f : ℕ → Site := fun m ↦ externalMacroIncrement (labels m)
  calc
    externalFiniteMacroPosition (extractExternalBlocks t labels i) =
        ∑ m ∈ Finset.range (b - a), f (a + m) := by
      change (∑ m : ExternalGapIndex t i,
          externalMacroIncrement (labels (a + m.val))) = _
      calc
        (∑ m : ExternalGapIndex t i,
            externalMacroIncrement (labels (a + m.val))) =
            ∑ m ∈ (Finset.range (b - a)).attach,
              externalMacroIncrement (labels (a + m.val)) := by
          apply Finset.sum_congr
          · exact Finset.univ_eq_attach (Finset.range (b - a))
          · intro _ _
            rfl
        _ = ∑ m ∈ Finset.range (b - a), f (a + m) :=
          Finset.sum_attach (Finset.range (b - a)) (fun m ↦ f (a + m))
    _ = ∑ m ∈ Finset.Ico a b, f m := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ = (∑ m ∈ Finset.range b, f m) -
        ∑ m ∈ Finset.range a, f m :=
      Finset.sum_Ico_eq_sub f hab
    _ = externalMacroPosition labels
          ((augmentedMacroTimes t i.succ).val) -
        externalMacroPosition labels
          ((augmentedMacroTimes t i.castSucc).val) := by
      rfl

def externalBlockReturnSet {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin (k + 1)) :
    Set (ExternalGapIndex t i → ExternalPairLabel) :=
  {w | externalFiniteMacroPosition w = (0, 0)}

theorem measurableSet_externalBlockReturnSet {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin (k + 1)) :
    MeasurableSet (externalBlockReturnSet t i) := by
  exact (Set.to_countable (externalBlockReturnSet t i)).measurableSet

def externalFixedHitLabelSet {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) : Set (ℕ → ExternalPairLabel) :=
  {labels | ∀ i, externalWalk labels (t i).val = (0, 0)}

theorem measurableSet_externalFixedHitLabelSet {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) :
    MeasurableSet (externalFixedHitLabelSet t) := by
  have heq : externalFixedHitLabelSet t =
      ⋂ i : Fin (k + 1),
        {labels | externalWalk labels (t i).val = (0, 0)} := by
    ext labels
    simp [externalFixedHitLabelSet]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq_fun
    ((measurable_pi_apply (t i).val).comp measurable_externalWalk)
    measurable_const

theorem externalWalk_eq_macro_of_even
    (labels : ℕ → ExternalPairLabel) {m : ℕ} (hm : Even m) :
    externalWalk labels m = externalMacroPosition labels (m / 2) := by
  obtain ⟨q, rfl⟩ := hm
  rw [show q + q = 2 * q by omega, externalWalk_even_eq_macro]
  congr 1
  omega

theorem externalFixedHitLabelSet_preimage_blocks {n k : ℕ}
    {t : KacMoment.TimeTuple n (k + 1)} (ht : Monotone t)
    (heven : ∀ i, Even (t i).val) :
    externalFixedHitLabelSet t =
      extractExternalBlocks t ⁻¹'
        (Set.univ.pi (externalBlockReturnSet t)) := by
  ext labels
  simp only [externalFixedHitLabelSet, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_pi, Set.mem_univ, forall_const, externalBlockReturnSet]
  constructor
  · intro hhits i
    rw [finitePosition_extractExternalBlock ht]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.castSucc_zero, augmentedMacroTimes_zero,
        augmentedMacroTimes_succ]
      rw [← externalWalk_eq_macro_of_even labels (heven 0), hhits]
      simp [externalMacroPosition]
    · simp only [augmentedMacroTimes_succ,
        augmentedMacroTimes_succ_castSucc]
      rw [← externalWalk_eq_macro_of_even labels (heven j.succ),
        ← externalWalk_eq_macro_of_even labels (heven j.castSucc),
        hhits, hhits]
      rfl
  · intro hblocks
    have hmacro : ∀ i : Fin (k + 1),
        externalMacroPosition labels ((t i).val / 2) = (0, 0) := by
      intro i
      induction i using Fin.induction with
      | zero =>
          have hb := hblocks (0 : Fin (k + 1))
          rw [finitePosition_extractExternalBlock ht] at hb
          simp only [Fin.castSucc_zero, augmentedMacroTimes_zero,
            augmentedMacroTimes_succ] at hb
          have hz := sub_eq_zero.mp hb
          change externalMacroPosition labels ((t 0).val / 2) = (0 : Site)
          simpa [externalMacroPosition] using hz
      | succ i ih =>
          have hb := hblocks i.succ
          rw [finitePosition_extractExternalBlock ht] at hb
          simp only [augmentedMacroTimes_succ,
            augmentedMacroTimes_succ_castSucc] at hb
          exact (sub_eq_zero.mp hb).trans ih
    intro i
    rw [externalWalk_eq_macro_of_even labels (heven i)]
    exact hmacro i

theorem externalFixedHitLabelSet_measure_eq_prod {n k : ℕ}
    {t : KacMoment.TimeTuple n (k + 1)} (ht : Monotone t)
    (heven : ∀ i, Even (t i).val) :
    externalLabelLaw (externalFixedHitLabelSet t) =
      ∏ i : Fin (k + 1),
        externalBlockLaw t i (externalBlockReturnSet t i) := by
  rw [externalFixedHitLabelSet_preimage_blocks ht heven]
  rw [← Measure.map_apply (measurable_extractExternalBlocks t)
    (MeasurableSet.univ_pi fun i ↦ measurableSet_externalBlockReturnSet t i)]
  rw [extractExternalBlocks_map ht]
  rw [Measure.infinitePi_pi_univ (externalBlockLaw t)
    (fun i ↦ measurableSet_externalBlockReturnSet t i)]
  simp only [tprod_fintype]

theorem finiteMacroPosition_iidBlock
    (labels : ℕ → ExternalPairLabel) (m : ℕ) :
    externalFiniteMacroPosition (iidBlock (X := ExternalPairLabel) 0 m labels) =
      externalMacroPosition labels m := by
  unfold externalFiniteMacroPosition externalMacroPosition iidBlock
  simpa using Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ externalMacroIncrement (labels j)) m

theorem externalBlockLaw_return {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin (k + 1)) :
    externalBlockLaw t i (externalBlockReturnSet t i) =
      externalLabelLaw
        {labels | externalMacroPosition labels
          (CollisionKernel.timeGaps n (k + 1)
            (augmentedMacroTimes t) i).val = (0, 0)} := by
  let m := (CollisionKernel.timeGaps n (k + 1)
    (augmentedMacroTimes t) i).val
  let e : ExternalGapIndex t i ≃ Fin m := by
    simpa [m, ExternalGapIndex, CollisionKernel.GapIndex] using
      Finset.equivFin (Finset.range m)
  let R : (ExternalGapIndex t i → ExternalPairLabel) ≃ᵐ
      (Fin m → ExternalPairLabel) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin m ↦ ExternalPairLabel) e
  let B : Set (Fin m → ExternalPairLabel) :=
    {w | externalFiniteMacroPosition w = (0, 0)}
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have hmap :
      (Measure.infinitePi fun _ : ExternalGapIndex t i ↦
        externalPairLabelLaw).map R =
      Measure.infinitePi fun _ : Fin m ↦ externalPairLabelLaw := by
    rw [Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi]
    simpa [R] using Measure.pi_map_piCongrLeft e
      (fun _ : Fin m ↦ externalPairLabelLaw)
  have hsum (w : ExternalGapIndex t i → ExternalPairLabel) :
      externalFiniteMacroPosition (R w) =
        externalFiniteMacroPosition w := by
    unfold externalFiniteMacroPosition
    symm
    apply Fintype.sum_equiv e
    intro j
    rw [show R w (e j) = w j by
      exact MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Fin m ↦ ExternalPairLabel) e w j]
  have hpre : R ⁻¹' B =
      {w : ExternalGapIndex t i → ExternalPairLabel |
        externalFiniteMacroPosition w = (0, 0)} := by
    ext w
    simp only [Set.mem_preimage, B, Set.mem_setOf_eq]
    rw [hsum]
  have hfinite :
      (Measure.infinitePi fun _ : ExternalGapIndex t i ↦ externalPairLabelLaw)
          {w | externalFiniteMacroPosition w = (0, 0)} =
        (Measure.infinitePi fun _ : Fin m ↦ externalPairLabelLaw) B := by
    rw [← hpre, ← Measure.map_apply R.measurable hB, hmap]
  change (Measure.infinitePi fun _ : ExternalGapIndex t i ↦
      externalPairLabelLaw)
      {w | externalFiniteMacroPosition w = (0, 0)} = _
  rw [hfinite]
  rw [← iidBlock_map externalPairLabelLaw 0 m]
  rw [Measure.map_apply (measurable_iidBlock 0 m) hB]
  congr 1
  ext labels
  change externalFiniteMacroPosition
      (iidBlock (X := ExternalPairLabel) 0 m labels) = (0, 0) ↔
    externalMacroPosition labels m = (0, 0)
  rw [finiteMacroPosition_iidBlock]

theorem externalLabelLaw_macroReturn_eq_externalChainReturn (m : ℕ) :
    externalLabelLaw
        {labels | externalMacroPosition labels m = (0, 0)} =
      incrementLaw (externalChainReturnAt (2 * m)) := by
  have hbridge := externalPathLaw_return_eq_externalChainReturnAt (2 * m)
  rw [externalPathLaw,
    Measure.map_apply measurable_externalWalk
      (measurableSet_eq_fun (measurable_pi_apply (2 * m)) measurable_const)]
      at hbridge
  change externalLabelLaw
      {labels | externalWalk labels (2 * m) = (0, 0)} = _ at hbridge
  simpa only [externalWalk_even_eq_macro] using hbridge

theorem externalBlockLaw_return_eq_chain {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin (k + 1)) :
    externalBlockLaw t i (externalBlockReturnSet t i) =
      incrementLaw
        (externalChainReturnAt
          (2 * (CollisionKernel.timeGaps n (k + 1)
            (augmentedMacroTimes t) i).val)) := by
  rw [externalBlockLaw_return,
    externalLabelLaw_macroReturn_eq_externalChainReturn]

theorem measurableSet_externalPathFixedHit {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) :
    MeasurableSet
      (fixedHitSet n (k + 1)
        (fun (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val) (0, 0) t) := by
  have heq :
      fixedHitSet n (k + 1)
          (fun (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val) (0, 0) t =
        ⋂ i : Fin (k + 1), {s : ℕ → Site | s (t i).val = (0, 0)} := by
    ext s
    simp [fixedHitSet]
  rw [heq]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_eq_fun (measurable_pi_apply (t i).val) measurable_const

theorem externalPathLaw_fixedHit_eq_label {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) :
    externalPathLaw
        (fixedHitSet n (k + 1)
          (fun (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val) (0, 0) t) =
      externalLabelLaw (externalFixedHitLabelSet t) := by
  rw [externalPathLaw, Measure.map_apply measurable_externalWalk
    (measurableSet_externalPathFixedHit t)]
  congr 1

theorem externalFixedHitLabelSet_eq_empty_of_odd {n k : ℕ}
    {t : KacMoment.TimeTuple n (k + 1)} {i : Fin (k + 1)}
    (hi : ¬ Even (t i).val) :
    externalFixedHitLabelSet t = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro labels hlabels
  have hhit : externalWalk labels (t i).val = (0, 0) := hlabels i
  have hevenSite : HLOZPairing.chessEven
      (externalWalk labels (t i).val) := by
    rw [hhit]
    simp [HLOZPairing.chessEven]
  exact hi ((chessEven_externalWalk_iff labels (t i).val).mp hevenSite)

theorem two_mul_macroGap_zero {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (heven : Even (t 0).val) :
    2 * (CollisionKernel.timeGaps n (k + 1)
      (augmentedMacroTimes t) 0).val = (t 0).val := by
  simp only [CollisionKernel.timeGaps, Fin.castSucc_zero,
    augmentedMacroTimes_zero, augmentedMacroTimes_succ]
  exact Nat.two_mul_div_two_of_even heven

theorem two_mul_macroGap_succ {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) (i : Fin k)
    (heven₀ : Even (t i.castSucc).val)
    (heven₁ : Even (t i.succ).val) :
    2 * (CollisionKernel.timeGaps n (k + 1)
      (augmentedMacroTimes t) i.succ).val =
      (KacMoment.timeGaps n k t i).val := by
  simp only [CollisionKernel.timeGaps, KacMoment.timeGaps,
    augmentedMacroTimes_succ, augmentedMacroTimes_succ_castSucc]
  obtain ⟨q₀, hq₀⟩ := heven₀
  obtain ⟨q₁, hq₁⟩ := heven₁
  omega

theorem prod_macroReturns_eq_fixedGapWeight {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1))
    (heven : ∀ i, Even (t i).val) :
    (∏ i : Fin (k + 1),
        externalReturnProb
          (2 * (CollisionKernel.timeGaps n (k + 1)
            (augmentedMacroTimes t) i).val)) =
      fixedGapWeight n k
        (fun d : Fin (n + 1) ↦ externalReturnProb d.val) t := by
  rw [Fin.prod_univ_succ]
  rw [two_mul_macroGap_zero t (heven 0)]
  unfold fixedGapWeight KacMoment.gapWeight
  congr 1
  apply Finset.prod_congr rfl
  intro i _hi
  rw [two_mul_macroGap_succ t i (heven i.castSucc) (heven i.succ)]

theorem externalPathLaw_fixedHit_real_eq_gapWeight_of_even {n k : ℕ}
    {t : KacMoment.TimeTuple n (k + 1)} (ht : Monotone t)
    (heven : ∀ i, Even (t i).val) :
    externalPathLaw.real
        (fixedHitSet n (k + 1)
          (fun (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val) (0, 0) t) =
      fixedGapWeight n k
        (fun d : Fin (n + 1) ↦ externalReturnProb d.val) t := by
  have hmeasure := externalFixedHitLabelSet_measure_eq_prod ht heven
  simp_rw [externalBlockLaw_return_eq_chain] at hmeasure
  have hreal := congrArg ENNReal.toReal
    ((externalPathLaw_fixedHit_eq_label t).trans hmeasure)
  rw [Measure.real]
  rw [ENNReal.toReal_prod] at hreal
  change _ = ∏ i : Fin (k + 1), externalReturnProb
    (2 * (CollisionKernel.timeGaps n (k + 1)
      (augmentedMacroTimes t) i).val) at hreal
  exact hreal.trans (prod_macroReturns_eq_fixedGapWeight t heven)

/-- The canonical iid terminal-label external chain satisfies the exact
fixed-origin successive-gap kernel required by the Kac/mgf proof. -/
theorem hasExternalFixedOriginKernel : HasExternalFixedOriginKernel := by
  intro n k t ht
  have htmono : Monotone t := by
    simpa [KacMoment.sortedTuples] using ht
  by_cases heven : ∀ i, Even (t i).val
  · exact (externalPathLaw_fixedHit_real_eq_gapWeight_of_even htmono heven).le
  · push_neg at heven
    obtain ⟨i, hi⟩ := heven
    have hempty := externalFixedHitLabelSet_eq_empty_of_odd hi
    have hzero : externalPathLaw.real
        (fixedHitSet n (k + 1)
          (fun (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val) (0, 0) t) = 0 := by
      rw [Measure.real, externalPathLaw_fixedHit_eq_label, hempty,
        measure_empty]
      rfl
    rw [hzero]
    unfold fixedGapWeight KacMoment.gapWeight
    apply mul_nonneg measureReal_nonneg
    exact Finset.prod_nonneg fun _ _ ↦ measureReal_nonneg

/-- The sharp Green bound alone now implies the genuine external-clock
fixed-origin upper deviation: the iid terminal-label kernel is unconditional. -/
theorem hasExternalChainUpperDeviation_of_sharpGreen
    (hGreen : HasExternalSharpGreenUpper) :
    HasExternalChainUpperDeviation :=
  hasExternalChainUpperDeviation_of_kernel_and_sharpGreen
    hasExternalFixedOriginKernel hGreen

end Erdos1166.HLOZExternalKernel
