/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.BrownianRecenter

/-!
# Deterministic-time Brownian strip iteration

This file turns the quantitative recentering block into the countable
path-space events needed for deterministic-time Markov iteration.
-/

open scoped ENNReal NNReal Topology

namespace Erdos1165.BrownianIteration

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open BrownianDyadic BrownianReflection BrownianRecenter

abbrev Path := ℝ≥0 → ℝ

/-- Time-shift and recenter a real path. -/
def pathShift (t0 : ℝ≥0) (f : Path) : Path :=
  fun t ↦ f (t0 + t) - f t0

lemma measurable_pathShift (t0 : ℝ≥0) : Measurable (pathShift t0) := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- The countable dyadic failure set written directly on canonical path
space.  Indexing edges by `Fin (2^k)` keeps its measurability proof small. -/
def pathDyadicBad (T : ℝ≥0) (a : ℕ → ℝ) : Set Path :=
  ⋃ k : ℕ, ⋃ j : Fin (2 ^ k),
    {f | a k ≤ |f (dyadicTime T k ((j : ℕ) + 1)) -
      f (dyadicTime T k (j : ℕ))|}

lemma measurableSet_pathDyadicBad (T : ℝ≥0) (a : ℕ → ℝ) :
    MeasurableSet (pathDyadicBad T a) := by
  unfold pathDyadicBad
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro j
  have hnext : Measurable
      (fun f : Path ↦ f (dyadicTime T k ((j : ℕ) + 1))) :=
    measurable_pi_apply _
  have hprev : Measurable
      (fun f : Path ↦ f (dyadicTime T k (j : ℕ))) :=
    measurable_pi_apply _
  have hm : Measurable (fun f : Path ↦
      |f (dyadicTime T k ((j : ℕ) + 1)) -
        f (dyadicTime T k (j : ℕ))|) :=
    (hnext.sub hprev).abs
  exact hm measurableSet_Ici

lemma pathDyadicBad_preimage
    {Omega : Type*} (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0) (a : ℕ → ℝ) :
    (fun omega ↦ fun t ↦ B t omega) ⁻¹' pathDyadicBad T a =
      dyadicBad B T a := by
  ext omega
  simp only [pathDyadicBad, dyadicBad, dyadicBadAt, mem_preimage,
    mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, j, hj⟩
    exact ⟨k, (j : ℕ), ⟨j.isLt, hj⟩⟩
  · rintro ⟨k, j, hj, hbad⟩
    exact ⟨k, ⟨j, hj⟩, hbad⟩

/-- Canonical negative recentering set on real path space. -/
def negativeRecenterPath (r : ℝ≥0) : Set Path :=
  (pathDyadicBad (recenterHorizon r) (geometricCutoff (innerRadius r)))ᶜ ∩
    {f | f (recenterHorizon r) < 0}

/-- Canonical positive recentering set on real path space. -/
def positiveRecenterPath (r : ℝ≥0) : Set Path :=
  (pathDyadicBad (recenterHorizon r) (geometricCutoff (innerRadius r)))ᶜ ∩
    {f | 0 < f (recenterHorizon r)}

lemma negativeRecenterPath_preimage
    {Omega : Type*} (B : ℝ≥0 → Omega → ℝ) (r : ℝ≥0) :
    (fun omega ↦ fun t ↦ B t omega) ⁻¹' negativeRecenterPath r =
      negativeRecenterEvent B r := by
  ext omega
  simp only [negativeRecenterPath, negativeRecenterEvent, mem_preimage,
    mem_inter_iff, mem_compl_iff]
  rw [show ((fun t ↦ B t omega) ∈ pathDyadicBad
      (recenterHorizon r) (geometricCutoff (innerRadius r))) ↔
      omega ∈ dyadicBad B (recenterHorizon r)
        (geometricCutoff (innerRadius r)) by
    exact Set.ext_iff.mp (pathDyadicBad_preimage B _ _) omega]
  rfl

lemma positiveRecenterPath_preimage
    {Omega : Type*} (B : ℝ≥0 → Omega → ℝ) (r : ℝ≥0) :
    (fun omega ↦ fun t ↦ B t omega) ⁻¹' positiveRecenterPath r =
      positiveRecenterEvent B r := by
  ext omega
  simp only [positiveRecenterPath, positiveRecenterEvent, mem_preimage,
    mem_inter_iff, mem_compl_iff]
  rw [show ((fun t ↦ B t omega) ∈ pathDyadicBad
      (recenterHorizon r) (geometricCutoff (innerRadius r))) ↔
      omega ∈ dyadicBad B (recenterHorizon r)
        (geometricCutoff (innerRadius r)) by
    exact Set.ext_iff.mp (pathDyadicBad_preimage B _ _) omega]
  rfl

lemma negativeRecenterPath_eq_negativeRecenterEvent (r : ℝ≥0) :
    negativeRecenterPath r =
      negativeRecenterEvent (fun t (f : Path) ↦ f t) r := by
  have h := negativeRecenterPath_preimage (fun t (f : Path) ↦ f t) r
  simpa only [preimage_id'] using h

lemma positiveRecenterPath_eq_positiveRecenterEvent (r : ℝ≥0) :
    positiveRecenterPath r =
      positiveRecenterEvent (fun t (f : Path) ↦ f t) r := by
  have h := positiveRecenterPath_preimage (fun t (f : Path) ↦ f t) r
  simpa only [preimage_id'] using h

lemma measurableSet_negativeRecenterPath (r : ℝ≥0) :
    MeasurableSet (negativeRecenterPath r) := by
  unfold negativeRecenterPath
  apply (measurableSet_pathDyadicBad _ _).compl.inter
  change MeasurableSet ((fun f : Path ↦ f (recenterHorizon r)) ⁻¹' Iio 0)
  exact (measurable_pi_apply _) measurableSet_Iio

lemma measurableSet_positiveRecenterPath (r : ℝ≥0) :
    MeasurableSet (positiveRecenterPath r) := by
  unfold positiveRecenterPath
  apply (measurableSet_pathDyadicBad _ _).compl.inter
  change MeasurableSet ((fun f : Path ↦ f (recenterHorizon r)) ⁻¹' Ioi 0)
  exact (measurable_pi_apply _) measurableSet_Ioi

/-- End time of `n` recentering blocks. -/
def blockTime (r : ℝ≥0) (n : ℕ) : ℝ≥0 := n * recenterHorizon r

@[simp] lemma blockTime_zero (r : ℝ≥0) : blockTime r 0 = 0 := by
  simp [blockTime]

lemma blockTime_succ (r : ℝ≥0) (n : ℕ) :
    blockTime r (n + 1) = blockTime r n + recenterHorizon r := by
  simp [blockTime, Nat.cast_add]
  ring

/-- Recursive path event: at every block, choose the endpoint sign opposite
to the current position. -/
def recenteredPathEvent (r : ℝ≥0) : ℕ → Set Path
  | 0 => Set.univ
  | n + 1 =>
      let A := recenteredPathEvent r n
      let t0 := blockTime r n
      ((A ∩ {f | 0 ≤ f t0}) ∩ pathShift t0 ⁻¹' negativeRecenterPath r) ∪
      ((A ∩ {f | f t0 < 0}) ∩ pathShift t0 ⁻¹' positiveRecenterPath r)

lemma measurableSet_recenteredPathEvent (r : ℝ≥0) :
    ∀ n, MeasurableSet (recenteredPathEvent r n) := by
  intro n
  induction n with
  | zero => simp [recenteredPathEvent]
  | succ n ih =>
      simp only [recenteredPathEvent]
      have hnonneg : MeasurableSet {f : Path | 0 ≤ f (blockTime r n)} := by
        change MeasurableSet
          ((fun f : Path ↦ f (blockTime r n)) ⁻¹' Ici 0)
        exact (measurable_pi_apply _) measurableSet_Ici
      have hneg : MeasurableSet {f : Path | f (blockTime r n) < 0} := by
        change MeasurableSet
          ((fun f : Path ↦ f (blockTime r n)) ⁻¹' Iio 0)
        exact (measurable_pi_apply _) measurableSet_Iio
      exact ((ih.inter hnonneg).inter
          (measurable_pathShift _ (measurableSet_negativeRecenterPath r))).union
        ((ih.inter hneg).inter
          (measurable_pathShift _ (measurableSet_positiveRecenterPath r)))

lemma dyadicTime_le {T : ℝ≥0} {k j : ℕ} (hj : j ≤ 2 ^ k) :
    dyadicTime T k j ≤ T := by
  exact (dyadicTime_mono_index T k hj).trans_eq (dyadicTime_top T k)

lemma pathDyadicBad_congr {T : ℝ≥0} {a : ℕ → ℝ} {f g : Path}
    (hfg : ∀ t, t ≤ T → f t = g t) :
    f ∈ pathDyadicBad T a ↔ g ∈ pathDyadicBad T a := by
  have forward {u v : Path} (huv : ∀ t, t ≤ T → u t = v t)
      (hu : u ∈ pathDyadicBad T a) : v ∈ pathDyadicBad T a := by
    rcases mem_iUnion.1 hu with ⟨k, hu⟩
    rcases mem_iUnion.1 hu with ⟨j, hj⟩
    apply mem_iUnion.2
    refine ⟨k, mem_iUnion.2 ⟨j, ?_⟩⟩
    have hj0 : (j : ℕ) ≤ 2 ^ k := Nat.le_of_lt j.isLt
    have hj1 : (j : ℕ) + 1 ≤ 2 ^ k := j.isLt
    change a k ≤ |u (dyadicTime T k ((j : ℕ) + 1)) -
      u (dyadicTime T k (j : ℕ))| at hj
    change a k ≤ |v (dyadicTime T k ((j : ℕ) + 1)) -
      v (dyadicTime T k (j : ℕ))|
    rw [← huv _ (dyadicTime_le hj0), ← huv _ (dyadicTime_le hj1)]
    exact hj
  constructor
  · exact forward hfg
  · exact forward (fun t ht ↦ (hfg t ht).symm)

lemma negativeRecenterPath_congr {r : ℝ≥0} {f g : Path}
    (hfg : ∀ t, t ≤ recenterHorizon r → f t = g t) :
    f ∈ negativeRecenterPath r ↔ g ∈ negativeRecenterPath r := by
  change (f ∉ pathDyadicBad _ _ ∧ f (recenterHorizon r) < 0) ↔
    (g ∉ pathDyadicBad _ _ ∧ g (recenterHorizon r) < 0)
  rw [pathDyadicBad_congr hfg, hfg _ le_rfl]

lemma positiveRecenterPath_congr {r : ℝ≥0} {f g : Path}
    (hfg : ∀ t, t ≤ recenterHorizon r → f t = g t) :
    f ∈ positiveRecenterPath r ↔ g ∈ positiveRecenterPath r := by
  change (f ∉ pathDyadicBad _ _ ∧ 0 < f (recenterHorizon r)) ↔
    (g ∉ pathDyadicBad _ _ ∧ 0 < g (recenterHorizon r))
  rw [pathDyadicBad_congr hfg, hfg _ le_rfl]

lemma blockTime_mono_succ (r : ℝ≥0) (n : ℕ) :
    blockTime r n ≤ blockTime r (n + 1) := by
  rw [blockTime_succ]
  exact le_add_right le_rfl

/-- The recursive event through `n` blocks depends only on the path through
the end of block `n`. -/
lemma recenteredPathEvent_congr {r : ℝ≥0} {f g : Path} :
    ∀ n, (∀ t, t ≤ blockTime r n → f t = g t) →
      (f ∈ recenteredPathEvent r n ↔ g ∈ recenteredPathEvent r n) := by
  intro n
  induction n with
  | zero => simp [recenteredPathEvent]
  | succ n ih =>
      intro hfg
      have hprev : ∀ t, t ≤ blockTime r n → f t = g t :=
        fun t ht ↦ hfg t (ht.trans (blockTime_mono_succ r n))
      have ht0 : f (blockTime r n) = g (blockTime r n) :=
        hprev _ le_rfl
      have hshift : ∀ s, s ≤ recenterHorizon r →
          pathShift (blockTime r n) f s =
            pathShift (blockTime r n) g s := by
        intro s hs
        unfold pathShift
        rw [hprev _ le_rfl]
        rw [hfg _ (by rw [blockTime_succ]; gcongr)]
      change
        (((f ∈ recenteredPathEvent r n ∧ 0 ≤ f (blockTime r n)) ∧
            pathShift (blockTime r n) f ∈ negativeRecenterPath r) ∨
          ((f ∈ recenteredPathEvent r n ∧ f (blockTime r n) < 0) ∧
            pathShift (blockTime r n) f ∈ positiveRecenterPath r)) ↔
        (((g ∈ recenteredPathEvent r n ∧ 0 ≤ g (blockTime r n)) ∧
            pathShift (blockTime r n) g ∈ negativeRecenterPath r) ∨
          ((g ∈ recenteredPathEvent r n ∧ g (blockTime r n) < 0) ∧
            pathShift (blockTime r n) g ∈ positiveRecenterPath r))
      rw [ih hprev, ht0, negativeRecenterPath_congr hshift,
        positiveRecenterPath_congr hshift]

/-! ## Factoring the recursive event through the past process -/

/-- Extend a path known only through `t0` by zero after `t0`. -/
def extendPast (t0 : ℝ≥0) (p : Set.Iic t0 → ℝ) : Path :=
  fun t ↦ if h : t ≤ t0 then p ⟨t, h⟩ else 0

lemma measurable_extendPast (t0 : ℝ≥0) : Measurable (extendPast t0) := by
  apply measurable_pi_lambda
  intro t
  unfold extendPast
  split_ifs with ht
  · exact measurable_pi_apply (⟨t, ht⟩ : Set.Iic t0)
  · exact measurable_const

/-- A sample point regarded as its full real path. -/
def samplePath {Omega : Type*} (B : ℝ≥0 → Omega → ℝ) (omega : Omega) : Path :=
  fun t ↦ B t omega

/-- The zero extension of the observed path through `t0`. -/
def pastPath {Omega : Type*} (B : ℝ≥0 → Omega → ℝ)
    (t0 : ℝ≥0) (omega : Omega) : Path :=
  extendPast t0 (fun t : Set.Iic t0 ↦ B t omega)

lemma pastPath_agrees {Omega : Type*} (B : ℝ≥0 → Omega → ℝ)
    (t0 : ℝ≥0) (omega : Omega) {t : ℝ≥0} (ht : t ≤ t0) :
    pastPath B t0 omega t = B t omega := by
  simp [pastPath, extendPast, ht]

lemma recenteredPathEvent_sample_iff_past
    {Omega : Type*} (B : ℝ≥0 → Omega → ℝ) (r : ℝ≥0)
    (n : ℕ) (omega : Omega) :
    samplePath B omega ∈ recenteredPathEvent r n ↔
      pastPath B (blockTime r n) omega ∈ recenteredPathEvent r n := by
  apply recenteredPathEvent_congr n
  intro t ht
  exact (pastPath_agrees B _ omega ht).symm

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {P : Measure Omega} {B : ℝ≥0 → Omega → ℝ}

lemma IsPreBrownianReal.indepFun_pathShift_pastPath
    (hB : IsPreBrownianReal B P) (t0 : ℝ≥0) :
    (fun omega ↦ pathShift t0 (samplePath B omega)) ⟂ᵢ[P]
      pastPath B t0 := by
  have hi := hB.indepFun_shift t0
  have hc := hi.comp measurable_id (measurable_extendPast t0)
  convert hc using 1 <;> rfl

lemma IsBrownianReal.one_tenth_le_measure_shift_negativePath
    (hB : IsBrownianReal B P) (t0 : ℝ≥0) {r : ℝ≥0} (hr : 0 < r) :
    (1 : ℝ≥0∞) / 10 ≤
      P ((fun omega ↦ pathShift t0 (samplePath B omega)) ⁻¹'
        negativeRecenterPath r) := by
  let C : ℝ≥0 → Omega → ℝ :=
    fun t omega ↦ B (t0 + t) omega - B t0 omega
  have hC : IsBrownianReal C P := hB.shift t0
  have hbound :=
    BrownianRecenter.IsBrownianReal.one_tenth_le_measure_negativeRecenterEvent
      hC hr
  have heq := negativeRecenterPath_preimage C r
  change samplePath C ⁻¹' negativeRecenterPath r =
    negativeRecenterEvent C r at heq
  rw [show (fun omega ↦ pathShift t0 (samplePath B omega)) ⁻¹'
      negativeRecenterPath r = samplePath C ⁻¹' negativeRecenterPath r by rfl,
    heq]
  exact hbound

lemma IsBrownianReal.one_tenth_le_measure_shift_positivePath
    (hB : IsBrownianReal B P) (t0 : ℝ≥0) {r : ℝ≥0} (hr : 0 < r) :
    (1 : ℝ≥0∞) / 10 ≤
      P ((fun omega ↦ pathShift t0 (samplePath B omega)) ⁻¹'
        positiveRecenterPath r) := by
  let C : ℝ≥0 → Omega → ℝ :=
    fun t omega ↦ B (t0 + t) omega - B t0 omega
  have hC : IsBrownianReal C P := hB.shift t0
  have hbound :=
    BrownianRecenter.IsBrownianReal.one_tenth_le_measure_positiveRecenterEvent
      hC hr
  have heq := positiveRecenterPath_preimage C r
  change samplePath C ⁻¹' positiveRecenterPath r =
    positiveRecenterEvent C r at heq
  rw [show (fun omega ↦ pathShift t0 (samplePath B omega)) ⁻¹'
      positiveRecenterPath r = samplePath C ⁻¹' positiveRecenterPath r by rfl,
    heq]
  exact hbound

/-! ## Recursive probability lower bound -/

def pastNonnegativeSet (r : ℝ≥0) (n : ℕ) : Set Path :=
  recenteredPathEvent r n ∩ {f | 0 ≤ f (blockTime r n)}

def pastNegativeSet (r : ℝ≥0) (n : ℕ) : Set Path :=
  recenteredPathEvent r n ∩ {f | f (blockTime r n) < 0}

lemma measurableSet_pastNonnegativeSet (r : ℝ≥0) (n : ℕ) :
    MeasurableSet (pastNonnegativeSet r n) := by
  unfold pastNonnegativeSet
  apply (measurableSet_recenteredPathEvent r n).inter
  change MeasurableSet ((fun f : Path ↦ f (blockTime r n)) ⁻¹' Ici 0)
  exact (measurable_pi_apply _) measurableSet_Ici

lemma measurableSet_pastNegativeSet (r : ℝ≥0) (n : ℕ) :
    MeasurableSet (pastNegativeSet r n) := by
  unfold pastNegativeSet
  apply (measurableSet_recenteredPathEvent r n).inter
  change MeasurableSet ((fun f : Path ↦ f (blockTime r n)) ⁻¹' Iio 0)
  exact (measurable_pi_apply _) measurableSet_Iio

/-- The actual event on the Brownian sample space. -/
def recenteredEvent (B : ℝ≥0 → Omega → ℝ) (r : ℝ≥0) (n : ℕ) : Set Omega :=
  samplePath B ⁻¹' recenteredPathEvent r n

@[simp] lemma recenteredEvent_zero : recenteredEvent B r 0 = Set.univ := by
  ext omega
  simp [recenteredEvent, recenteredPathEvent]

lemma recenteredEvent_succ (r : ℝ≥0) (n : ℕ) :
    recenteredEvent B r (n + 1) =
      (((fun omega ↦ pathShift (blockTime r n) (samplePath B omega)) ⁻¹'
          negativeRecenterPath r) ∩
        (pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n)) ∪
      (((fun omega ↦ pathShift (blockTime r n) (samplePath B omega)) ⁻¹'
          positiveRecenterPath r) ∩
        (pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n)) := by
  ext omega
  change
    (((samplePath B omega ∈ recenteredPathEvent r n ∧
          0 ≤ samplePath B omega (blockTime r n)) ∧
        pathShift (blockTime r n) (samplePath B omega) ∈ negativeRecenterPath r) ∨
      ((samplePath B omega ∈ recenteredPathEvent r n ∧
          samplePath B omega (blockTime r n) < 0) ∧
        pathShift (blockTime r n) (samplePath B omega) ∈ positiveRecenterPath r)) ↔
    ((pathShift (blockTime r n) (samplePath B omega) ∈ negativeRecenterPath r ∧
        pastPath B (blockTime r n) omega ∈ recenteredPathEvent r n ∧
          0 ≤ pastPath B (blockTime r n) omega (blockTime r n)) ∨
      (pathShift (blockTime r n) (samplePath B omega) ∈ positiveRecenterPath r ∧
        pastPath B (blockTime r n) omega ∈ recenteredPathEvent r n ∧
          pastPath B (blockTime r n) omega (blockTime r n) < 0))
  rw [recenteredPathEvent_sample_iff_past B r n omega]
  rw [pastPath_agrees B _ omega le_rfl]
  simp only [samplePath]
  tauto

lemma pastNonnegative_preimage_eq (r : ℝ≥0) (n : ℕ) :
    pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n =
      recenteredEvent B r n ∩ {omega | 0 ≤ B (blockTime r n) omega} := by
  ext omega
  change
    (pastPath B (blockTime r n) omega ∈ recenteredPathEvent r n ∧
      0 ≤ pastPath B (blockTime r n) omega (blockTime r n)) ↔
    (samplePath B omega ∈ recenteredPathEvent r n ∧
      0 ≤ B (blockTime r n) omega)
  rw [← recenteredPathEvent_sample_iff_past B r n omega,
    pastPath_agrees B _ omega le_rfl]

lemma pastNegative_preimage_eq (r : ℝ≥0) (n : ℕ) :
    pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n =
      recenteredEvent B r n ∩ {omega | B (blockTime r n) omega < 0} := by
  ext omega
  change
    (pastPath B (blockTime r n) omega ∈ recenteredPathEvent r n ∧
      pastPath B (blockTime r n) omega (blockTime r n) < 0) ↔
    (samplePath B omega ∈ recenteredPathEvent r n ∧
      B (blockTime r n) omega < 0)
  rw [← recenteredPathEvent_sample_iff_past B r n omega,
    pastPath_agrees B _ omega le_rfl]

lemma IsPreBrownianReal.nullMeasurableSet_shift_negativePath
    (hB : IsPreBrownianReal B P) (t0 : ℝ≥0) (r : ℝ≥0) :
    NullMeasurableSet
      ((fun omega ↦ pathShift t0 (samplePath B omega)) ⁻¹'
        negativeRecenterPath r) P := by
  let C : ℝ≥0 → Omega → ℝ :=
    fun t omega ↦ B (t0 + t) omega - B t0 omega
  have hC : IsPreBrownianReal C P := hB.shift t0
  have heq := negativeRecenterPath_preimage C r
  change samplePath C ⁻¹' negativeRecenterPath r =
    negativeRecenterEvent C r at heq
  rw [show (fun omega ↦ pathShift t0 (samplePath B omega)) ⁻¹'
      negativeRecenterPath r = samplePath C ⁻¹' negativeRecenterPath r by rfl,
    heq]
  exact BrownianRecenter.IsPreBrownianReal.nullMeasurableSet_negativeRecenterEvent
    hC r

lemma IsPreBrownianReal.nullMeasurableSet_shift_positivePath
    (hB : IsPreBrownianReal B P) (t0 : ℝ≥0) (r : ℝ≥0) :
    NullMeasurableSet
      ((fun omega ↦ pathShift t0 (samplePath B omega)) ⁻¹'
        positiveRecenterPath r) P := by
  let C : ℝ≥0 → Omega → ℝ :=
    fun t omega ↦ B (t0 + t) omega - B t0 omega
  have hC : IsPreBrownianReal C P := hB.shift t0
  have heq := positiveRecenterPath_preimage C r
  change samplePath C ⁻¹' positiveRecenterPath r =
    positiveRecenterEvent C r at heq
  rw [show (fun omega ↦ pathShift t0 (samplePath B omega)) ⁻¹'
      positiveRecenterPath r = samplePath C ⁻¹' positiveRecenterPath r by rfl,
    heq]
  exact BrownianRecenter.IsPreBrownianReal.nullMeasurableSet_positiveRecenterEvent
    hC r

lemma IsPreBrownianReal.nullMeasurableSet_recenteredEvent
    (hB : IsPreBrownianReal B P) (r : ℝ≥0) :
    ∀ n, NullMeasurableSet (recenteredEvent B r n) P := by
  intro n
  induction n with
  | zero => simp [recenteredEvent_zero]
  | succ n ih =>
      rw [recenteredEvent_succ]
      apply NullMeasurableSet.union
      · apply NullMeasurableSet.inter
        · exact BrownianIteration.IsPreBrownianReal.nullMeasurableSet_shift_negativePath
            hB _ r
        · rw [pastNonnegative_preimage_eq]
          exact ih.inter ((hB.aemeasurable _).nullMeasurableSet_preimage measurableSet_Ici)
      · apply NullMeasurableSet.inter
        · exact BrownianIteration.IsPreBrownianReal.nullMeasurableSet_shift_positivePath
            hB _ r
        · rw [pastNegative_preimage_eq]
          exact ih.inter ((hB.aemeasurable _).nullMeasurableSet_preimage measurableSet_Iio)

lemma recenteredEvent_eq_past_partition (r : ℝ≥0) (n : ℕ) :
    recenteredEvent B r n =
      (pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n) ∪
      (pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n) := by
  rw [pastNonnegative_preimage_eq, pastNegative_preimage_eq]
  ext omega
  by_cases hA : omega ∈ recenteredEvent B r n
  · simp only [hA, true_and, mem_union, mem_inter_iff, Set.mem_ofPred_eq]
    exact (iff_true_intro (le_or_gt 0 (B (blockTime r n) omega))).symm
  · simp [hA]

lemma disjoint_past_partition (r : ℝ≥0) (n : ℕ) :
    Disjoint
      (pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n)
      (pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n) := by
  rw [pastNonnegative_preimage_eq, pastNegative_preimage_eq]
  apply Set.disjoint_left.2
  intro omega hpos hneg
  rcases hpos with ⟨_hA, hpos⟩
  rcases hneg with ⟨_hA', hneg⟩
  change 0 ≤ B (blockTime r n) omega at hpos
  change B (blockTime r n) omega < 0 at hneg
  exact (not_lt_of_ge hpos) hneg

lemma IsPreBrownianReal.measure_recenteredEvent_eq_past_add
    (hB : IsPreBrownianReal B P) (r : ℝ≥0) (n : ℕ) :
    P (recenteredEvent B r n) =
      P (pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n) +
      P (pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n) := by
  rw [recenteredEvent_eq_past_partition]
  apply measure_union₀
  · rw [pastNegative_preimage_eq]
    exact (BrownianIteration.IsPreBrownianReal.nullMeasurableSet_recenteredEvent
      hB r n).inter
        ((hB.aemeasurable _).nullMeasurableSet_preimage measurableSet_Iio)
  · exact (disjoint_past_partition r n).aedisjoint

lemma IsPreBrownianReal.measure_recenteredEvent_succ_eq
    (hB : IsPreBrownianReal B P) (r : ℝ≥0) (n : ℕ) :
    P (recenteredEvent B r (n + 1)) =
      P ((fun omega ↦ pathShift (blockTime r n) (samplePath B omega)) ⁻¹'
          negativeRecenterPath r) *
        P (pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n) +
      P ((fun omega ↦ pathShift (blockTime r n) (samplePath B omega)) ⁻¹'
          positiveRecenterPath r) *
        P (pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n) := by
  have hi := BrownianIteration.IsPreBrownianReal.indepFun_pathShift_pastPath
    hB (blockTime r n)
  have hneg := hi.measure_inter_preimage_eq_mul
    (negativeRecenterPath r) (pastNonnegativeSet r n)
    (measurableSet_negativeRecenterPath r)
    (measurableSet_pastNonnegativeSet r n)
  have hpos := hi.measure_inter_preimage_eq_mul
    (positiveRecenterPath r) (pastNegativeSet r n)
    (measurableSet_positiveRecenterPath r)
    (measurableSet_pastNegativeSet r n)
  rw [recenteredEvent_succ]
  rw [measure_union₀]
  · rw [hneg, hpos]
  · apply NullMeasurableSet.inter
    · exact BrownianIteration.IsPreBrownianReal.nullMeasurableSet_shift_positivePath
        hB _ r
    · rw [pastNegative_preimage_eq]
      exact (BrownianIteration.IsPreBrownianReal.nullMeasurableSet_recenteredEvent
        hB r n).inter
          ((hB.aemeasurable _).nullMeasurableSet_preimage measurableSet_Iio)
  · apply (Set.disjoint_left.2 ?_).aedisjoint
    intro omega hfirst hsecond
    exact Set.disjoint_left.1 (disjoint_past_partition r n)
      hfirst.2 hsecond.2

theorem IsBrownianReal.one_tenth_mul_measure_recenteredEvent_le_succ
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) (n : ℕ) :
    (1 : ℝ≥0∞) / 10 * P (recenteredEvent B r n) ≤
      P (recenteredEvent B r (n + 1)) := by
  have hpartition :=
    BrownianIteration.IsPreBrownianReal.measure_recenteredEvent_eq_past_add
      hB.toIsPreBrownianReal r n
  have hsucc :=
    BrownianIteration.IsPreBrownianReal.measure_recenteredEvent_succ_eq
      hB.toIsPreBrownianReal r n
  have hneg :=
    BrownianIteration.IsBrownianReal.one_tenth_le_measure_shift_negativePath
      hB (blockTime r n) hr
  have hpos :=
    BrownianIteration.IsBrownianReal.one_tenth_le_measure_shift_positivePath
      hB (blockTime r n) hr
  calc
    (1 : ℝ≥0∞) / 10 * P (recenteredEvent B r n) =
        (1 : ℝ≥0∞) / 10 *
          (P (pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n) +
            P (pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n)) := by rw [hpartition]
    _ = (1 : ℝ≥0∞) / 10 *
          P (pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n) +
        (1 : ℝ≥0∞) / 10 *
          P (pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n) := by
          rw [mul_add]
    _ ≤ P ((fun omega ↦ pathShift (blockTime r n) (samplePath B omega)) ⁻¹'
          negativeRecenterPath r) *
          P (pastPath B (blockTime r n) ⁻¹' pastNonnegativeSet r n) +
        P ((fun omega ↦ pathShift (blockTime r n) (samplePath B omega)) ⁻¹'
          positiveRecenterPath r) *
          P (pastPath B (blockTime r n) ⁻¹' pastNegativeSet r n) := by
      gcongr
    _ = P (recenteredEvent B r (n + 1)) := hsucc.symm

/-- After `n` blocks, the recursive survival/recentering event has probability
at least `(1/10)^n`. -/
theorem IsBrownianReal.one_tenth_pow_le_measure_recenteredEvent
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    ∀ n : ℕ, ((1 : ℝ≥0∞) / 10) ^ n ≤ P (recenteredEvent B r n) := by
  intro n
  induction n with
  | zero =>
      let _ : IsProbabilityMeasure P :=
        hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
      simp [recenteredEvent_zero]
  | succ n ih =>
      calc
        ((1 : ℝ≥0∞) / 10) ^ (n + 1) =
            (1 : ℝ≥0∞) / 10 * ((1 : ℝ≥0∞) / 10) ^ n := by
              rw [pow_succ]
              ac_rfl
        _ ≤ (1 : ℝ≥0∞) / 10 * P (recenteredEvent B r n) := by
          gcongr
        _ ≤ P (recenteredEvent B r (n + 1)) :=
          BrownianIteration.IsBrownianReal.one_tenth_mul_measure_recenteredEvent_le_succ
            hB hr n

/-! ## Pathwise survival supplied by the recursive event -/

lemma negativeRecenterPath_pathwise {r : ℝ≥0} (hr : 0 < r)
    {f : Path} (hcont : Continuous f) (hzero : f 0 = 0)
    (hf : f ∈ negativeRecenterPath r) {x : ℝ}
    (hx0 : 0 ≤ x) (hxr : |x| ≤ (r : ℝ) / 2) :
    (∀ t : ℝ≥0, t ≤ recenterHorizon r → |x + f t| < (r : ℝ)) ∧
      |x + f (recenterHorizon r)| < (r : ℝ) / 2 := by
  rw [negativeRecenterPath_eq_negativeRecenterEvent] at hf
  exact BrownianRecenter.negativeRecenterEvent_pathwise
    hr hcont hzero hf hx0 hxr

lemma positiveRecenterPath_pathwise {r : ℝ≥0} (hr : 0 < r)
    {f : Path} (hcont : Continuous f) (hzero : f 0 = 0)
    (hf : f ∈ positiveRecenterPath r) {x : ℝ}
    (hx0 : x ≤ 0) (hxr : |x| ≤ (r : ℝ) / 2) :
    (∀ t : ℝ≥0, t ≤ recenterHorizon r → |x + f t| < (r : ℝ)) ∧
      |x + f (recenterHorizon r)| < (r : ℝ) / 2 := by
  rw [positiveRecenterPath_eq_positiveRecenterEvent] at hf
  exact BrownianRecenter.positiveRecenterEvent_pathwise
    hr hcont hzero hf hx0 hxr

/-- A path in the recursive event stays in the full strip through the end of
the last block and is in the central half at that endpoint. -/
lemma recenteredPathEvent_pathwise {r : ℝ≥0} (hr : 0 < r)
    {f : Path} (hcont : Continuous f) (hzero : f 0 = 0) :
    ∀ n, f ∈ recenteredPathEvent r n →
      (∀ t : ℝ≥0, t ≤ blockTime r n → |f t| < (r : ℝ)) ∧
        |f (blockTime r n)| < (r : ℝ) / 2 := by
  intro n
  induction n with
  | zero =>
      intro _hf
      have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
      constructor
      · intro t ht
        have ht0 : t = 0 := by simpa [blockTime] using ht
        subst t
        simpa [hzero] using hrR
      · simpa [blockTime, hzero] using (half_pos hrR)
  | succ n ih =>
      intro hf
      change
        (((f ∈ recenteredPathEvent r n ∧ 0 ≤ f (blockTime r n)) ∧
            pathShift (blockTime r n) f ∈ negativeRecenterPath r) ∨
          ((f ∈ recenteredPathEvent r n ∧ f (blockTime r n) < 0) ∧
            pathShift (blockTime r n) f ∈ positiveRecenterPath r)) at hf
      have hcontShift : Continuous (pathShift (blockTime r n) f) := by
        unfold pathShift
        exact (hcont.comp (continuous_const.add continuous_id)).sub continuous_const
      have hzeroShift : pathShift (blockTime r n) f 0 = 0 := by
        simp [pathShift]
      rcases hf with hneg | hpos
      · rcases hneg with ⟨⟨hprev, hx0⟩, hblock⟩
        have hprevBounds := ih hprev
        have hblockBounds := negativeRecenterPath_pathwise hr hcontShift
          hzeroShift hblock hx0 hprevBounds.2.le
        constructor
        · intro t ht
          by_cases htpast : t ≤ blockTime r n
          · exact hprevBounds.1 t htpast
          · have ht0 : blockTime r n ≤ t := le_of_not_ge htpast
            let s : ℝ≥0 := t - blockTime r n
            have hs : s ≤ recenterHorizon r := by
              unfold s
              rw [tsub_le_iff_left]
              rwa [← blockTime_succ]
            have hts : blockTime r n + s = t := by
              unfold s
              rw [add_comm, tsub_add_cancel_of_le ht0]
            have hb := hblockBounds.1 s hs
            rw [pathShift, hts] at hb
            have heq : f (blockTime r n) +
                (f t - f (blockTime r n)) = f t := by ring
            rwa [heq] at hb
        · rw [blockTime_succ]
          simpa [pathShift] using hblockBounds.2
      · rcases hpos with ⟨⟨hprev, hx0⟩, hblock⟩
        have hprevBounds := ih hprev
        have hblockBounds := positiveRecenterPath_pathwise hr hcontShift
          hzeroShift hblock hx0.le hprevBounds.2.le
        constructor
        · intro t ht
          by_cases htpast : t ≤ blockTime r n
          · exact hprevBounds.1 t htpast
          · have ht0 : blockTime r n ≤ t := le_of_not_ge htpast
            let s : ℝ≥0 := t - blockTime r n
            have hs : s ≤ recenterHorizon r := by
              unfold s
              rw [tsub_le_iff_left]
              rwa [← blockTime_succ]
            have hts : blockTime r n + s = t := by
              unfold s
              rw [add_comm, tsub_add_cancel_of_le ht0]
            have hb := hblockBounds.1 s hs
            rw [pathShift, hts] at hb
            have heq : f (blockTime r n) +
                (f t - f (blockTime r n)) = f t := by ring
            rwa [heq] at hb
        · rw [blockTime_succ]
          simpa [pathShift] using hblockBounds.2

/-- Almost surely, membership in the recursive event implies literal
all-times strip survival through the corresponding block horizon. -/
lemma IsBrownianReal.recenteredEvent_ae_subset_rawStripEvent
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) (n : ℕ) :
    ∀ᵐ omega ∂P, omega ∈ recenteredEvent B r n →
      omega ∈ rawStripEvent B (blockTime r n) (r : ℝ) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with omega hcont hzero
  intro homega
  exact (recenteredPathEvent_pathwise hr hcont hzero n homega).1

/-- Quantitative strip survival at every integer multiple of `r²/8192`. -/
theorem IsBrownianReal.one_tenth_pow_le_measure_rawStripEvent_blockTime
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) (n : ℕ) :
    ((1 : ℝ≥0∞) / 10) ^ n ≤
      P (rawStripEvent B (blockTime r n) (r : ℝ)) := by
  exact (BrownianIteration.IsBrownianReal.one_tenth_pow_le_measure_recenteredEvent
    hB hr n).trans
    (measure_mono_ae
      (BrownianIteration.IsBrownianReal.recenteredEvent_ae_subset_rawStripEvent
        hB hr n))

/-! ## Every deterministic horizon -/

/-- Number of `r²/8192` blocks needed to cover `T`. -/
def blockCount (r T : ℝ≥0) : ℕ :=
  ⌈(T : ℝ) / (recenterHorizon r : ℝ)⌉₊

lemma le_blockTime_blockCount {r : ℝ≥0} (hr : 0 < r) (T : ℝ≥0) :
    T ≤ blockTime r (blockCount r T) := by
  have hH : (0 : ℝ) < recenterHorizon r := by
    exact_mod_cast recenterHorizon_pos hr
  have hc : (T : ℝ) / (recenterHorizon r : ℝ) ≤
      (blockCount r T : ℕ) := Nat.le_ceil _
  have hreal : (T : ℝ) ≤
      (blockCount r T : ℝ) * (recenterHorizon r : ℝ) :=
    (div_le_iff₀ hH).mp hc
  exact_mod_cast hreal

/-- **Quantitative Brownian strip survival at every horizon.**  Covering
`T` by blocks of duration `r²/8192` gives the explicit lower bound

`(1/10) ^ ceil(T / (r²/8192))`.

This is an exponential lower bound in `T/r²`, with completely explicit
constants and with the literal all-times open-strip event. -/
theorem IsBrownianReal.one_tenth_pow_blockCount_le_measure_rawStripEvent
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) (T : ℝ≥0) :
    ((1 : ℝ≥0∞) / 10) ^ blockCount r T ≤
      P (rawStripEvent B T (r : ℝ)) := by
  calc
    ((1 : ℝ≥0∞) / 10) ^ blockCount r T ≤
        P (rawStripEvent B (blockTime r (blockCount r T)) (r : ℝ)) :=
      BrownianIteration.IsBrownianReal.one_tenth_pow_le_measure_rawStripEvent_blockTime
        hB hr _
    _ ≤ P (rawStripEvent B T (r : ℝ)) :=
      measure_mono (rawStripEvent_mono_time (le_blockTime_blockCount hr T) _)

/-- Measurable-envelope form of the every-horizon bound. -/
theorem IsBrownianReal.one_tenth_pow_blockCount_le_measure_stripEvent
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) (T : ℝ≥0) :
    ((1 : ℝ≥0∞) / 10) ^ blockCount r T ≤
      P (stripEvent P B T (r : ℝ)) := by
  simpa only [stripEvent, measure_toMeasurable] using
    BrownianIteration.IsBrownianReal.one_tenth_pow_blockCount_le_measure_rawStripEvent
      hB hr T

/-- Real-exponent form of the same estimate.  Since
`(1/10)^x = exp (-log(10) * x)`, this displays the required
`c * exp (-C*T/r²)` behavior directly (with block length `r²/8192`). -/
theorem IsBrownianReal.one_tenth_rpow_ratio_add_one_le_measure_rawStripEvent
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) (T : ℝ≥0) :
    ((1 : ℝ≥0∞) / 10) ^
        ((T : ℝ) / (recenterHorizon r : ℝ) + 1) ≤
      P (rawStripEvent B T (r : ℝ)) := by
  have hratio : 0 ≤ (T : ℝ) / (recenterHorizon r : ℝ) := by positivity
  have hceil : (blockCount r T : ℝ) ≤
      (T : ℝ) / (recenterHorizon r : ℝ) + 1 :=
    (Nat.ceil_lt_add_one hratio).le
  calc
    ((1 : ℝ≥0∞) / 10) ^
          ((T : ℝ) / (recenterHorizon r : ℝ) + 1) ≤
        ((1 : ℝ≥0∞) / 10) ^ (blockCount r T : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_ge (by norm_num) hceil
    _ = ((1 : ℝ≥0∞) / 10) ^ blockCount r T :=
      ENNReal.rpow_natCast _ _
    _ ≤ P (rawStripEvent B T (r : ℝ)) :=
      BrownianIteration.IsBrownianReal.one_tenth_pow_blockCount_le_measure_rawStripEvent
        hB hr T

lemma ratio_recenterHorizon_eq {r : ℝ≥0} (hr : 0 < r) (T : ℝ≥0) :
    (T : ℝ) / (recenterHorizon r : ℝ) =
      8192 * (T : ℝ) / (r : ℝ) ^ 2 := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [recenterHorizon_eq]
  simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp

/-- Fully expanded diffusive form: the survival probability is bounded below
by `(1/10)^(8192*T/r² + 1)`. -/
theorem IsBrownianReal.one_tenth_rpow_diffusive_le_measure_rawStripEvent
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) (T : ℝ≥0) :
    ((1 : ℝ≥0∞) / 10) ^
        (8192 * (T : ℝ) / (r : ℝ) ^ 2 + 1) ≤
      P (rawStripEvent B T (r : ℝ)) := by
  rw [← ratio_recenterHorizon_eq hr T]
  exact
    BrownianIteration.IsBrownianReal.one_tenth_rpow_ratio_add_one_le_measure_rawStripEvent
      hB hr T

end

end Erdos1165.BrownianIteration
