/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Gap
import ErdosProblems.Erdos1165.LowerAssembly
import ErdosProblems.Erdos1165.ScreeningInstantiation
import ErdosProblems.Erdos1165.UpperCanonical

/-!
# Concrete HLOZ gap mesh and path events

This module supplies the missing path-level objects in the HLOZ upper-bound
assembly.  It defines the successive threshold-creation locations, the
`1/1024` exponent mesh for their three spatial gaps, the overflow and
distance/deficit exceptional events, and the three successive transition
events.  All of these events are proved measurable.

The deterministic results identify the fixed-tiling event `M_m^4 ∩ Pi_m^4`,
cover it by the finite mesh plus the exceptional family, and cover `M_m^4`
by the six concrete tilings.  The final theorem therefore exposes only the
four genuinely probabilistic estimates: three successive transition bounds
and summability of the exceptional family.  It does not assume any of them.
-/

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165
namespace HLOZPathEvents

/-- The positive cutoff parameter used for the upper-bound level clock. -/
noncomputable def upperTailDelta : ℝ := 1 / 40

lemma upperTailDelta_pos : 0 < upperTailDelta := by
  norm_num [upperTailDelta]

def ThresholdCreation (s : WalkPath) (m k n : ℕ) : Prop :=
  k ≤ thresholdCount s n m ∧ ∀ q < n, thresholdCount s q m < k

def thresholdCreationSet (m k n : ℕ) : Set WalkPath :=
  {s | ThresholdCreation s m k n}

lemma thresholdCount_eq_of_creation {s : WalkPath} {m k n : ℕ}
    (hk : 0 < k) (h : ThresholdCreation s m k n) :
    thresholdCount s n m = k := by
  apply Nat.le_antisymm ?_ h.1
  cases n with
  | zero =>
      have hle := thresholdCount_le_time_add_one s 0 m
      omega
  | succ q =>
      have hprev := h.2 q (Nat.lt_succ_self q)
      have hstep := thresholdCount_succ_le s q m
      omega

lemma position_mem_thresholdSites_of_creation {s : WalkPath} {m k n : ℕ}
    (hk : 0 < k) (h : ThresholdCreation s m k n) :
    s n ∈ thresholdSites s n m := by
  cases n with
  | zero =>
      have hcount : 0 < thresholdCount s 0 m := hk.trans_le h.1
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hcount
      have hxv := (mem_thresholdSites s 0 m x).mp hx |>.1
      have hxeq : x = s 0 := by
        simpa [visitedSites, visitedPrefix, pathPrefix] using hxv
      simpa [hxeq] using hx
  | succ q =>
      have hcount : thresholdCount s (q + 1) m = k :=
        thresholdCount_eq_of_creation hk h
      have hprev : thresholdCount s q m < k := h.2 q (Nat.lt_succ_self q)
      by_contra hnot
      have hsub : thresholdSites s (q + 1) m ⊆ thresholdSites s q m := by
        intro x hx
        have hx' := thresholdSites_succ_subset_insert s q m hx
        rw [Finset.mem_insert] at hx'
        rcases hx' with hnew | hold
        · subst x
          exact (hnot hx).elim
        · exact hold
      have hcard := Finset.card_le_card hsub
      change thresholdCount s (q + 1) m ≤ thresholdCount s q m at hcard
      omega

lemma creation_time_lt {s : WalkPath} {m k l nk nl : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hkl : k < l)
    (hfirst : ThresholdCreation s m k nk)
    (hsecond : ThresholdCreation s m l nl) : nk < nl := by
  have hkcount := thresholdCount_eq_of_creation hk hfirst
  have hlcount := thresholdCount_eq_of_creation hl hsecond
  by_contra hnot
  have hmono := thresholdCount_mono_time s m (Nat.le_of_not_gt hnot)
  change thresholdCount s nl m ≤ thresholdCount s nk m at hmono
  rw [hlcount, hkcount] at hmono
  exact (Nat.not_le_of_gt hkl) hmono

lemma creation_locations_ne {s : WalkPath} {m k l nk nl : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hkl : k < l)
    (hfirst : ThresholdCreation s m k nk)
    (hsecond : ThresholdCreation s m l nl) : s nk ≠ s nl := by
  have htime : nk < nl := creation_time_lt hk hl hkl hfirst hsecond
  have hnlpos : 0 < nl := by omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnlpos.ne'
  have hnkle : nk ≤ q := Nat.lt_succ_iff.mp htime
  have hold : s nk ∈ thresholdSites s q m :=
    thresholdSites_mono_time s m hnkle
      (position_mem_thresholdSites_of_creation hk hfirst)
  have hnew : s (q + 1) ∉ thresholdSites s q m := by
    intro hmem
    have hsub : thresholdSites s (q + 1) m ⊆ thresholdSites s q m := by
      intro x hx
      have hx' := thresholdSites_succ_subset_insert s q m hx
      rw [Finset.mem_insert] at hx'
      rcases hx' with hxnew | hxold
      · simpa [hxnew] using hmem
      · exact hxold
    have hcard := Finset.card_le_card hsub
    have hcount := thresholdCount_eq_of_creation hl hsecond
    change thresholdCount s (q + 1) m = l at hcount
    have hprev := hsecond.2 q (Nat.lt_succ_self q)
    change thresholdCount s (q + 1) m ≤ thresholdCount s q m at hcard
    omega
  exact fun heq ↦ hnew (heq ▸ hold)

lemma measurableSet_thresholdCreationSet (m k n : ℕ) :
    MeasurableSet (thresholdCreationSet m k n) := by
  have hfirst : MeasurableSet {s : WalkPath | k ≤ thresholdCount s n m} :=
    measurableSet_le measurable_const (measurable_thresholdCount n m)
  have hprior : MeasurableSet
      (⋂ q : Fin n, {s : WalkPath | thresholdCount s q m < k}) := by
    exact MeasurableSet.iInter fun q ↦
      measurableSet_lt (measurable_thresholdCount q m) measurable_const
  have heq : thresholdCreationSet m k n =
      {s : WalkPath | k ≤ thresholdCount s n m} ∩
        ⋂ q : Fin n, {s : WalkPath | thresholdCount s q m < k} := by
    ext s
    simp only [thresholdCreationSet, ThresholdCreation, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hn, hprior⟩
      refine ⟨hn, fun q ↦ hprior q q.isLt⟩
    · rintro ⟨hn, hprior⟩
      refine ⟨hn, fun q hqn ↦ ?_⟩
      exact hprior ⟨q, hqn⟩
  rw [heq]
  exact hfirst.inter hprior

/-! Concrete spatial mesh. -/

/-- HLOZ use the exponent mesh of width `1/1024`; the extra final value is
the overflow band beyond radius `exp m`. -/
def meshSteps : ℕ := 1024

abbrev GapScale := Fin (meshSteps + 1)

def overflowScale : GapScale := ⟨meshSteps, by simp [meshSteps]⟩

def properGapMesh : Finset GapScale := Finset.univ.erase overflowScale

noncomputable def latticeDistance (x y : Point) : ℝ :=
  Real.sqrt (((x.1 - y.1 : ℤ) : ℝ) ^ 2 + ((x.2 - y.2 : ℤ) : ℝ) ^ 2)

noncomputable def meshExponent (i : ℕ) : ℝ :=
  (i + 1 : ℝ) * ScreeningInstantiation.meshDelta

/-- The part of the spatial mesh to which HLOZ Lemma 4.10 applies.  The
paper's hypothesis is the sharp regime condition `α ≤ κ₂`. -/
noncomputable def lowGapMesh : Finset GapScale :=
  properGapMesh.filter fun a ↦
    meshExponent a ≤ ScreeningInstantiation.kappaTwo

/-- The complementary proper mesh scales.  These are not exceptional gap
events: Proposition 4.7 keeps them in the transition/Harnack analysis. -/
noncomputable def highGapMesh : Finset GapScale :=
  properGapMesh.filter fun a ↦
    ScreeningInstantiation.kappaTwo < meshExponent a

/-- A proper mesh triple containing at least one high-scale gap. -/
def HasHighGapScale (a : (GapScale × GapScale) × GapScale) : Prop :=
  a.1.1 ∈ highGapMesh ∨ a.1.2 ∈ highGapMesh ∨ a.2 ∈ highGapMesh

lemma mem_lowGapMesh_iff {a : GapScale} :
    a ∈ lowGapMesh ↔
      a ∈ properGapMesh ∧
        meshExponent a ≤ ScreeningInstantiation.kappaTwo := by
  simp [lowGapMesh]

lemma mem_highGapMesh_iff {a : GapScale} :
    a ∈ highGapMesh ↔
      a ∈ properGapMesh ∧
        ScreeningInstantiation.kappaTwo < meshExponent a := by
  simp [highGapMesh]

lemma mem_lowGapMesh_or_highGapMesh_of_mem_proper {a : GapScale}
    (ha : a ∈ properGapMesh) : a ∈ lowGapMesh ∨ a ∈ highGapMesh := by
  rcases le_or_gt (meshExponent a) ScreeningInstantiation.kappaTwo with h | h
  · exact Or.inl ((mem_lowGapMesh_iff).2 ⟨ha, h⟩)
  · exact Or.inr ((mem_highGapMesh_iff).2 ⟨ha, h⟩)

lemma lowGapMesh_disjoint_highGapMesh : Disjoint lowGapMesh highGapMesh := by
  rw [Finset.disjoint_left]
  intro a halow hahigh
  have hle := (mem_lowGapMesh_iff.mp halow).2
  have hlt := (mem_highGapMesh_iff.mp hahigh).2
  exact (not_lt_of_ge hle) hlt


/-- The low-mesh hypothesis is safely inside the numerical range required by
the Proposition 4.8 beta-band estimates. -/
lemma meshExponent_add_delta_le_kappaOne_of_mem_lowGapMesh
    {a : GapScale} (ha : a ∈ lowGapMesh) :
    meshExponent a + ScreeningInstantiation.meshDelta ≤
      ScreeningInstantiation.kappaOne := by
  have hle := (mem_lowGapMesh_iff.mp ha).2
  norm_num [ScreeningInstantiation.kappaTwo,
    ScreeningInstantiation.meshDelta, ScreeningInstantiation.kappaOne] at hle ⊢
  linarith

noncomputable def meshRadius (m i : ℕ) : ℝ :=
  Real.exp ((m : ℝ) ^ meshExponent i)

def HasProperGapScale (m : ℕ) (x y : Point) : Prop :=
  ∃ i < meshSteps, latticeDistance x y ≤ meshRadius m i

/-- The least exponent bin whose upper radius contains the gap, or the
overflow value when the gap is larger than every proper mesh radius. -/
noncomputable def gapScaleOf (m : ℕ) (x y : Point) : GapScale := by
  classical
  by_cases h : HasProperGapScale m x y
  · exact ⟨Nat.find h, (Nat.find_spec h).1.trans (Nat.lt_succ_self _)⟩
  · exact overflowScale

lemma gapScaleOf_eq_overflow_iff (m : ℕ) (x y : Point) :
    gapScaleOf m x y = overflowScale ↔ ¬HasProperGapScale m x y := by
  classical
  unfold gapScaleOf
  by_cases h : HasProperGapScale m x y
  · rw [dif_pos h]
    constructor
    · intro heq
      have hlt := (Nat.find_spec h).1
      have hval := congrArg Fin.val heq
      simp only [overflowScale] at hval
      omega
    · intro hn
      exact (hn h).elim
  · simp [h]

lemma gapScaleOf_mem_mesh_or_overflow (m : ℕ) (x y : Point) :
    gapScaleOf m x y ∈ properGapMesh ∨ gapScaleOf m x y = overflowScale := by
  classical
  by_cases h : gapScaleOf m x y = overflowScale
  · exact Or.inr h
  · exact Or.inl (by simp [properGapMesh, h])

lemma meshRadius_last (m : ℕ) : meshRadius m (meshSteps - 1) = Real.exp m := by
  have hexponent : meshExponent (meshSteps - 1) = 1 := by
    norm_num [meshExponent, meshSteps, ScreeningInstantiation.meshDelta]
  simp [meshRadius, hexponent]

lemma distance_gt_exp_of_gapScaleOf_eq_overflow {m : ℕ} {x y : Point}
    (h : gapScaleOf m x y = overflowScale) :
    Real.exp m < latticeDistance x y := by
  have hnone := (gapScaleOf_eq_overflow_iff m x y).mp h
  have hlast : ¬latticeDistance x y ≤ meshRadius m (meshSteps - 1) := by
    intro hle
    apply hnone
    exact ⟨meshSteps - 1, by norm_num [meshSteps], hle⟩
  rw [meshRadius_last] at hlast
  exact lt_of_not_ge hlast

/-! Fixed-time creation configurations. -/

def pairConfiguration (t : DominoTiling) (m : ℕ) (a : GapScale)
    (n₁ n₂ : ℕ) : Set WalkPath :=
  {s | ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    thresholdCount s n₂ (m + 1) = 0 ∧
    ¬Tilings.sameDomino t (s n₁) (s n₂) ∧
    gapScaleOf m (s n₁) (s n₂) = a}

def tripleConfiguration (t : DominoTiling) (m : ℕ) (a₁ a₂ : GapScale)
    (n₁ n₂ n₃ : ℕ) : Set WalkPath :=
  {s | ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ thresholdCount s n₃ (m + 1) = 0 ∧
    ¬Tilings.sameDomino t (s n₁) (s n₂) ∧
    ¬Tilings.sameDomino t (s n₁) (s n₃) ∧
    ¬Tilings.sameDomino t (s n₂) (s n₃) ∧
    gapScaleOf m (s n₁) (s n₂) = a₁ ∧
    gapScaleOf m (s n₂) (s n₃) = a₂}

def quadrupleConfiguration (t : DominoTiling) (m : ℕ)
    (a₁ a₂ a₃ : GapScale) (n₁ n₂ n₃ n₄ : ℕ) : Set WalkPath :=
  {s | ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
    thresholdCount s n₄ (m + 1) = 0 ∧
    fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
    gapScaleOf m (s n₁) (s n₂) = a₁ ∧
    gapScaleOf m (s n₂) (s n₃) = a₂ ∧
    gapScaleOf m (s n₃) (s n₄) = a₃}

/-- The exact `M_m^4 ∩ Pi_m^4` path event for a fixed tiling, expressed
through the four successive threshold-creation locations. -/
def hlozSeparatedLevelEvent (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  {s | ∃ n₁ n₂ n₃ n₄,
    ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
    thresholdCount s n₄ (m + 1) = 0 ∧
    fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄)}

def firstTransitionEvent (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, pairConfiguration t m a.1.1 n₁ n₂

def secondTransitionEvent (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, ⋃ n₃,
    tripleConfiguration t m a.1.1 a.1.2 n₁ n₂ n₃

def thirdTransitionEvent (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, ⋃ n₃, ⋃ n₄,
    quadrupleConfiguration t m a.1.1 a.1.2 a.2 n₁ n₂ n₃ n₄

/-- Configurations for which at least one of the three spatial gaps lies in
the overflow band beyond the finite HLOZ exponent mesh. -/
def meshOverflowEvent (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  {s | ∃ n₁ n₂ n₃ n₄,
    ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
    thresholdCount s n₄ (m + 1) = 0 ∧
    fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
    (gapScaleOf m (s n₁) (s n₂) = overflowScale ∨
      gapScaleOf m (s n₂) (s n₃) = overflowScale ∨
      gapScaleOf m (s n₃) (s n₄) = overflowScale)}

/-- Local-time deficit cutoff `m^(alpha+delta)` for a mesh scale. -/
noncomputable def gapDeficitCutoff (m : ℕ) (a : GapScale) : ℕ :=
  Nat.ceil ((m : ℝ) ^ (meshExponent a + ScreeningInstantiation.meshDelta))

/-- Failure of the HLOZ distance/deficit compatibility for one successive
creation pair in the low-scale regime `α ≤ κ₂` of Lemma 4.10.  High proper
mesh scales remain in the transition/Harnack regime instead. -/
def lowGapDeficitFailure (s : WalkPath) (m nOld nNew : ℕ) : Prop :=
  let a := gapScaleOf m (s nOld) (s nNew)
  a ∈ lowGapMesh ∧
    localTime s nOld (s nNew) + gapDeficitCutoff m a < m

/-- Backwards-compatible name for the now correctly low-scale deficit
failure. -/
abbrev gapDeficitFailure := lowGapDeficitFailure

/-- Union of the three concrete low-scale exceptional gap events in HLOZ
Lemma 4.10. -/
def lowGapDeficitExceptionalEvent (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  {s | ∃ n₁ n₂ n₃ n₄,
    ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
    thresholdCount s n₄ (m + 1) = 0 ∧
    fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
    (lowGapDeficitFailure s m n₁ n₂ ∨ lowGapDeficitFailure s m n₂ n₃ ∨
      lowGapDeficitFailure s m n₃ n₄)}

/-- Backwards-compatible name; this event is now restricted to the low mesh. -/
abbrev gapDeficitExceptionalEvent := lowGapDeficitExceptionalEvent

/-- The gap-deficit event restricted to paths whose fourth level-`m`
creation is not late.  Every stopped-candidate argument with the HLOZ cutoff
must use this event, rather than infer an upper clock bound merely from the
absence of spatial mesh overflow. -/
def onTimeLowGapDeficitExceptionalEvent
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  lowGapDeficitExceptionalEvent t m \ lateLevelSet upperTailDelta m 4

/-- Backwards-compatible name for the on-time low-scale gap event. -/
abbrev onTimeGapDeficitExceptionalEvent := onTimeLowGapDeficitExceptionalEvent

/-- The upper exceptional family explicitly contains the late-clock event,
the spatial overflow event, and only the on-time part of the gap deficit. -/
def hlozExceptionalEvent (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  (lateLevelSet upperTailDelta m 4 ∪ meshOverflowEvent t m) ∪
    onTimeLowGapDeficitExceptionalEvent t m

lemma gapDeficitExceptionalEvent_subset_hlozExceptionalEvent
    (t : DominoTiling) (m : ℕ) :
    gapDeficitExceptionalEvent t m ⊆ hlozExceptionalEvent t m := by
  intro s hs
  by_cases hlate : s ∈ lateLevelSet upperTailDelta m 4
  · exact Or.inl (Or.inl hlate)
  · exact Or.inr ⟨hs, hlate⟩

/-- Terminal mesh branch after the distance/deficit failure has been removed. -/
def screenedThirdTransitionEvent (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) : Set WalkPath :=
  thirdTransitionEvent t m a \ hlozExceptionalEvent t m

lemma mem_screenedThirdTransitionEvent {t : DominoTiling} {m : ℕ}
    {a : (GapScale × GapScale) × GapScale} {s : WalkPath} :
    s ∈ screenedThirdTransitionEvent t m a ↔
      s ∈ thirdTransitionEvent t m a ∧ s ∉ hlozExceptionalEvent t m := Iff.rfl

lemma mem_screenedThirdTransitionEvent_of_mem {t : DominoTiling} {m : ℕ}
    {a : (GapScale × GapScale) × GapScale} {s : WalkPath}
    (hthird : s ∈ thirdTransitionEvent t m a)
    (he : s ∉ hlozExceptionalEvent t m) :
    s ∈ screenedThirdTransitionEvent t m a :=
  ⟨hthird, he⟩

/-! Measurability of all fixed-time and path-level events. -/

lemma measurableSet_pathPairPredicate (n₁ n₂ : ℕ) (P : Point → Point → Prop) :
    MeasurableSet {s : WalkPath | P (s n₁) (s n₂)} := by
  have hmap : Measurable (fun s : WalkPath ↦ (s n₁, s n₂)) :=
    (measurable_pi_apply n₁).prodMk (measurable_pi_apply n₂)
  exact hmap (Set.to_countable {z : Point × Point | P z.1 z.2}).measurableSet

lemma measurableSet_pathTriplePredicate (n₁ n₂ n₃ : ℕ)
    (P : Point → Point → Point → Prop) :
    MeasurableSet {s : WalkPath | P (s n₁) (s n₂) (s n₃)} := by
  have hmap : Measurable (fun s : WalkPath ↦ ((s n₁, s n₂), s n₃)) :=
    ((measurable_pi_apply n₁).prodMk (measurable_pi_apply n₂)).prodMk
      (measurable_pi_apply n₃)
  exact hmap (Set.to_countable {z : (Point × Point) × Point |
    P z.1.1 z.1.2 z.2}).measurableSet

lemma measurableSet_pathQuadruplePredicate (n₁ n₂ n₃ n₄ : ℕ)
    (P : Point → Point → Point → Point → Prop) :
    MeasurableSet {s : WalkPath | P (s n₁) (s n₂) (s n₃) (s n₄)} := by
  have hmap : Measurable
      (fun s : WalkPath ↦ (((s n₁, s n₂), s n₃), s n₄)) :=
    (((measurable_pi_apply n₁).prodMk (measurable_pi_apply n₂)).prodMk
      (measurable_pi_apply n₃)).prodMk (measurable_pi_apply n₄)
  exact hmap (Set.to_countable {z : ((Point × Point) × Point) × Point |
    P z.1.1.1 z.1.1.2 z.1.2 z.2}).measurableSet

lemma measurable_localTime_eval (n q : ℕ) :
    Measurable fun s : WalkPath ↦ localTime s n (s q) := by
  have hmap : Measurable fun s : WalkPath ↦ (pathPrefix s n, s q) :=
    (measurable_pathPrefix n).prodMk (measurable_pi_apply q)
  exact (measurable_of_countable
    (fun z : (Fin (n + 1) → Point) × Point ↦ localTimePrefix z.1 z.2)).comp hmap

lemma measurableSet_gapDeficitFailure (m nOld nNew : ℕ) :
    MeasurableSet {s : WalkPath | gapDeficitFailure s m nOld nNew} := by
  have hmap : Measurable fun s : WalkPath ↦
      ((s nOld, s nNew), localTime s nOld (s nNew)) :=
    ((measurable_pi_apply nOld).prodMk (measurable_pi_apply nNew)).prodMk
      (measurable_localTime_eval nOld nNew)
  exact hmap (Set.to_countable {z : (Point × Point) × ℕ |
    let a := gapScaleOf m z.1.1 z.1.2
    a ∈ lowGapMesh ∧ z.2 + gapDeficitCutoff m a < m}).measurableSet

lemma measurableSet_pairConfiguration (t : DominoTiling) (m : ℕ) (a : GapScale)
    (n₁ n₂ : ℕ) : MeasurableSet (pairConfiguration t m a n₁ n₂) := by
  have h₁ := measurableSet_thresholdCreationSet m 1 n₁
  have h₂ := measurableSet_thresholdCreationSet m 2 n₂
  have hnext : MeasurableSet {s : WalkPath | thresholdCount s n₂ (m + 1) = 0} :=
    measurableSet_eq_fun (measurable_thresholdCount n₂ (m + 1)) measurable_const
  have hgeom := measurableSet_pathPairPredicate n₁ n₂ fun x y ↦
    ¬Tilings.sameDomino t x y ∧ gapScaleOf m x y = a
  simpa only [pairConfiguration, thresholdCreationSet, Set.inter_def,
      Set.mem_ofPred_eq, and_assoc] using h₁.inter (h₂.inter (hnext.inter hgeom))

lemma measurableSet_tripleConfiguration (t : DominoTiling) (m : ℕ)
    (a₁ a₂ : GapScale) (n₁ n₂ n₃ : ℕ) :
    MeasurableSet (tripleConfiguration t m a₁ a₂ n₁ n₂ n₃) := by
  have h₁ := measurableSet_thresholdCreationSet m 1 n₁
  have h₂ := measurableSet_thresholdCreationSet m 2 n₂
  have h₃ := measurableSet_thresholdCreationSet m 3 n₃
  have hnext : MeasurableSet {s : WalkPath | thresholdCount s n₃ (m + 1) = 0} :=
    measurableSet_eq_fun (measurable_thresholdCount n₃ (m + 1)) measurable_const
  have hgeom := measurableSet_pathTriplePredicate n₁ n₂ n₃ fun x y z ↦
    ¬Tilings.sameDomino t x y ∧ ¬Tilings.sameDomino t x z ∧
      ¬Tilings.sameDomino t y z ∧ gapScaleOf m x y = a₁ ∧
      gapScaleOf m y z = a₂
  simpa only [tripleConfiguration, thresholdCreationSet, Set.inter_def,
      Set.mem_ofPred_eq, and_assoc] using
    h₁.inter (h₂.inter (h₃.inter (hnext.inter hgeom)))

lemma measurableSet_quadrupleConfiguration (t : DominoTiling) (m : ℕ)
    (a₁ a₂ a₃ : GapScale) (n₁ n₂ n₃ n₄ : ℕ) :
    MeasurableSet (quadrupleConfiguration t m a₁ a₂ a₃ n₁ n₂ n₃ n₄) := by
  have h₁ := measurableSet_thresholdCreationSet m 1 n₁
  have h₂ := measurableSet_thresholdCreationSet m 2 n₂
  have h₃ := measurableSet_thresholdCreationSet m 3 n₃
  have h₄ := measurableSet_thresholdCreationSet m 4 n₄
  have hnext : MeasurableSet {s : WalkPath | thresholdCount s n₄ (m + 1) = 0} :=
    measurableSet_eq_fun (measurable_thresholdCount n₄ (m + 1)) measurable_const
  have hgeom := measurableSet_pathQuadruplePredicate n₁ n₂ n₃ n₄
    fun w x y z ↦ fourPointsSeparated t w x y z ∧
      gapScaleOf m w x = a₁ ∧ gapScaleOf m x y = a₂ ∧ gapScaleOf m y z = a₃
  simpa only [quadrupleConfiguration, thresholdCreationSet, Set.inter_def,
      Set.mem_ofPred_eq, and_assoc] using
    h₁.inter (h₂.inter (h₃.inter (h₄.inter (hnext.inter hgeom))))

lemma measurableSet_firstTransitionEvent (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    MeasurableSet (firstTransitionEvent t m a) := by
  exact MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    measurableSet_pairConfiguration t m a.1.1 n₁ n₂

lemma measurableSet_secondTransitionEvent (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    MeasurableSet (secondTransitionEvent t m a) := by
  exact MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    MeasurableSet.iUnion fun n₃ ↦
      measurableSet_tripleConfiguration t m a.1.1 a.1.2 n₁ n₂ n₃

lemma measurableSet_thirdTransitionEvent (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    MeasurableSet (thirdTransitionEvent t m a) := by
  exact MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    MeasurableSet.iUnion fun n₃ ↦ MeasurableSet.iUnion fun n₄ ↦
      measurableSet_quadrupleConfiguration t m a.1.1 a.1.2 a.2 n₁ n₂ n₃ n₄

lemma measurableSet_quadrupleCore (t : DominoTiling) (m n₁ n₂ n₃ n₄ : ℕ) :
    MeasurableSet {s : WalkPath |
      ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
      ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
      thresholdCount s n₄ (m + 1) = 0 ∧
      fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄)} := by
  have h₁ := measurableSet_thresholdCreationSet m 1 n₁
  have h₂ := measurableSet_thresholdCreationSet m 2 n₂
  have h₃ := measurableSet_thresholdCreationSet m 3 n₃
  have h₄ := measurableSet_thresholdCreationSet m 4 n₄
  have hnext : MeasurableSet {s : WalkPath | thresholdCount s n₄ (m + 1) = 0} :=
    measurableSet_eq_fun (measurable_thresholdCount n₄ (m + 1)) measurable_const
  have hgeom := measurableSet_pathQuadruplePredicate n₁ n₂ n₃ n₄
    (fourPointsSeparated t)
  simpa only [thresholdCreationSet, Set.inter_def, Set.mem_ofPred_eq, and_assoc] using
    h₁.inter (h₂.inter (h₃.inter (h₄.inter (hnext.inter hgeom))))

lemma measurableSet_hlozSeparatedLevelEvent (t : DominoTiling) (m : ℕ) :
    MeasurableSet (hlozSeparatedLevelEvent t m) := by
  rw [show hlozSeparatedLevelEvent t m =
      ⋃ n₁, ⋃ n₂, ⋃ n₃, ⋃ n₄, {s : WalkPath |
        ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
        ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
        thresholdCount s n₄ (m + 1) = 0 ∧
        fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄)} by
    ext s
    simp [hlozSeparatedLevelEvent]]
  exact MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    MeasurableSet.iUnion fun n₃ ↦ MeasurableSet.iUnion fun n₄ ↦
      measurableSet_quadrupleCore t m n₁ n₂ n₃ n₄

lemma measurableSet_meshOverflowEvent (t : DominoTiling) (m : ℕ) :
    MeasurableSet (meshOverflowEvent t m) := by
  rw [show meshOverflowEvent t m =
      ⋃ n₁, ⋃ n₂, ⋃ n₃, ⋃ n₄, {s : WalkPath |
        ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
        ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
        thresholdCount s n₄ (m + 1) = 0 ∧
        fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
        (gapScaleOf m (s n₁) (s n₂) = overflowScale ∨
          gapScaleOf m (s n₂) (s n₃) = overflowScale ∨
          gapScaleOf m (s n₃) (s n₄) = overflowScale)} by
    ext s
    simp [meshOverflowEvent]]
  refine MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    MeasurableSet.iUnion fun n₃ ↦ MeasurableSet.iUnion fun n₄ ↦ ?_
  have h₁ := measurableSet_thresholdCreationSet m 1 n₁
  have h₂ := measurableSet_thresholdCreationSet m 2 n₂
  have h₃ := measurableSet_thresholdCreationSet m 3 n₃
  have h₄ := measurableSet_thresholdCreationSet m 4 n₄
  have hnext : MeasurableSet {s : WalkPath | thresholdCount s n₄ (m + 1) = 0} :=
    measurableSet_eq_fun (measurable_thresholdCount n₄ (m + 1)) measurable_const
  have hgeom := measurableSet_pathQuadruplePredicate n₁ n₂ n₃ n₄
    fun w x y z ↦ fourPointsSeparated t w x y z ∧
      (gapScaleOf m w x = overflowScale ∨ gapScaleOf m x y = overflowScale ∨
        gapScaleOf m y z = overflowScale)
  simpa only [thresholdCreationSet, Set.inter_def, Set.mem_ofPred_eq, and_assoc] using
    h₁.inter (h₂.inter (h₃.inter (h₄.inter (hnext.inter hgeom))))

lemma measurableSet_gapDeficitExceptionalEvent (t : DominoTiling) (m : ℕ) :
    MeasurableSet (gapDeficitExceptionalEvent t m) := by
  rw [show gapDeficitExceptionalEvent t m =
      ⋃ n₁, ⋃ n₂, ⋃ n₃, ⋃ n₄, {s : WalkPath |
        ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
        ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
        thresholdCount s n₄ (m + 1) = 0 ∧
        fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
        (gapDeficitFailure s m n₁ n₂ ∨ gapDeficitFailure s m n₂ n₃ ∨
          gapDeficitFailure s m n₃ n₄)} by
    ext s
    simp [lowGapDeficitExceptionalEvent]]
  refine MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    MeasurableSet.iUnion fun n₃ ↦ MeasurableSet.iUnion fun n₄ ↦ ?_
  have hcore := measurableSet_quadrupleCore t m n₁ n₂ n₃ n₄
  have hfail := (measurableSet_gapDeficitFailure m n₁ n₂).union
    ((measurableSet_gapDeficitFailure m n₂ n₃).union
      (measurableSet_gapDeficitFailure m n₃ n₄))
  simpa only [Set.inter_def, Set.mem_union, Set.mem_ofPred_eq, and_assoc] using
    hcore.inter hfail

lemma measurableSet_onTimeGapDeficitExceptionalEvent
    (t : DominoTiling) (m : ℕ) :
    MeasurableSet (onTimeGapDeficitExceptionalEvent t m) :=
  (measurableSet_gapDeficitExceptionalEvent t m).diff
    (LowerAssembly.measurableSet_lateLevelSet upperTailDelta m 4 (by omega))

lemma measurableSet_hlozExceptionalEvent (t : DominoTiling) (m : ℕ) :
    MeasurableSet (hlozExceptionalEvent t m) := by
  exact ((LowerAssembly.measurableSet_lateLevelSet upperTailDelta m 4 (by omega)).union
    (measurableSet_meshOverflowEvent t m)).union
      (measurableSet_onTimeGapDeficitExceptionalEvent t m)

lemma measurableSet_screenedThirdTransitionEvent (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    MeasurableSet (screenedThirdTransitionEvent t m a) :=
  (measurableSet_thirdTransitionEvent t m a).diff
    (measurableSet_hlozExceptionalEvent t m)

/-- Direct specialization of the finite gap-screening union bound to the
concrete path event above.  It identifies exactly which candidate-count and
one-candidate return estimates must be supplied to prove the exceptional
probability bound. -/
theorem measure_gapDeficitExceptionalEvent_le_sum_budget_mul_cost
    {Band Candidate : Type*} (t : DominoTiling) (m : ℕ)
    (bands : Finset Band) (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set WalkPath) (budget : Band → ℕ)
    (cost : Band → ℝ≥0∞)
    (hcover : Gap.GapEventCovered (gapDeficitExceptionalEvent t m)
      bands candidates succeeds)
    (hcount : Gap.CandidateCountBound bands candidates budget)
    (hcost : Gap.PerCandidateReturnCostBound simpleRandomWalk bands candidates
      succeeds cost) :
    simpleRandomWalk (gapDeficitExceptionalEvent t m) ≤
      ∑ band ∈ bands, (budget band : ℝ≥0∞) * cost band := by
  exact Gap.measure_gapEvent_le_sum_budget_mul_cost simpleRandomWalk
    (gapDeficitExceptionalEvent t m) bands candidates succeeds budget cost
    hcover hcount hcost

/-- The finite gap-screening union bound specialized to the sound on-time
gap event used by the upper endgame. -/
theorem measure_onTimeGapDeficitExceptionalEvent_le_sum_budget_mul_cost
    {Band Candidate : Type*} (t : DominoTiling) (m : ℕ)
    (bands : Finset Band) (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set WalkPath) (budget : Band → ℕ)
    (cost : Band → ℝ≥0∞)
    (hcover : Gap.GapEventCovered (onTimeGapDeficitExceptionalEvent t m)
      bands candidates succeeds)
    (hcount : Gap.CandidateCountBound bands candidates budget)
    (hcost : Gap.PerCandidateReturnCostBound simpleRandomWalk bands candidates
      succeeds cost) :
    simpleRandomWalk (onTimeGapDeficitExceptionalEvent t m) ≤
      ∑ band ∈ bands, (budget band : ℝ≥0∞) * cost band := by
  exact Gap.measure_gapEvent_le_sum_budget_mul_cost simpleRandomWalk
    (onTimeGapDeficitExceptionalEvent t m) bands candidates succeeds budget cost
    hcover hcount hcost

/-! Deterministic coverage. -/

lemma thresholdCreation_natFind {s : WalkPath} {m k : ℕ}
    (h : ReachesThreshold s m k) : ThresholdCreation s m k (Nat.find h) := by
  refine ⟨Nat.find_spec h, ?_⟩
  intro q hq
  exact Nat.lt_of_not_ge (Nat.find_min h hq)

theorem hlozSeparatedLevelEvent_mesh_cover (t : DominoTiling) (m : ℕ) :
    hlozSeparatedLevelEvent t m ⊆
      meshOverflowEvent t m ∪
        UpperAssembly.meshBranchUnion properGapMesh (thirdTransitionEvent t m) := by
  intro s hs
  obtain ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep⟩ := hs
  let a₁ := gapScaleOf m (s n₁) (s n₂)
  let a₂ := gapScaleOf m (s n₂) (s n₃)
  let a₃ := gapScaleOf m (s n₃) (s n₄)
  rcases gapScaleOf_mem_mesh_or_overflow m (s n₁) (s n₂) with ha₁ | ha₁
  · rcases gapScaleOf_mem_mesh_or_overflow m (s n₂) (s n₃) with ha₂ | ha₂
    · rcases gapScaleOf_mem_mesh_or_overflow m (s n₃) (s n₄) with ha₃ | ha₃
      · right
        rw [UpperAssembly.mem_meshBranchUnion]
        refine ⟨((a₁, a₂), a₃), ?_, ?_⟩
        · simpa [UpperAssembly.meshTriples] using And.intro (And.intro ha₁ ha₂) ha₃
        · simp only [thirdTransitionEvent, Set.mem_iUnion]
          refine ⟨n₁, n₂, n₃, n₄, ?_⟩
          exact ⟨h₁, h₂, h₃, h₄, hnext, hsep, rfl, rfl, rfl⟩
      · left
        exact ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
          Or.inr (Or.inr ha₃)⟩
    · left
      exact ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
        Or.inr (Or.inl ha₂)⟩
  · left
    exact ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
      Or.inl ha₁⟩

theorem hlozSeparatedLevelEvent_exceptional_mesh_cover (t : DominoTiling) (m : ℕ) :
    hlozSeparatedLevelEvent t m ⊆
      hlozExceptionalEvent t m ∪
        UpperAssembly.meshBranchUnion properGapMesh (thirdTransitionEvent t m) := by
  intro s hs
  rcases hlozSeparatedLevelEvent_mesh_cover t m hs with hover | hbranch
  · left
    simp only [hlozExceptionalEvent, Set.mem_union]
    exact Or.inl (Or.inr hover)
  · exact Or.inr hbranch

lemma meshBranchUnion_diff {Scale : Type*} (mesh : Finset Scale)
    (branch : ((Scale × Scale) × Scale) → Set WalkPath) (exceptional : Set WalkPath) :
    UpperAssembly.meshBranchUnion mesh (fun a ↦ branch a \ exceptional) =
      UpperAssembly.meshBranchUnion mesh branch \ exceptional := by
  ext s
  simp only [UpperAssembly.mem_meshBranchUnion, Set.mem_sdiff]
  aesop

lemma subset_union_diff_of_subset_union {A B E : Set WalkPath}
    (h : A ⊆ E ∪ B) : A ⊆ E ∪ (B \ E) := by
  intro s hs
  rcases h hs with he | hb
  · exact Or.inl he
  · by_cases he : s ∈ E
    · exact Or.inl he
    · exact Or.inr ⟨hb, he⟩

/-- The useful screened form of the mesh cover: after moving the exceptional
family outside the branch union, every terminal branch itself avoids all
overflow and distance/deficit failures. -/
theorem hlozSeparatedLevelEvent_screened_mesh_cover (t : DominoTiling) (m : ℕ) :
    hlozSeparatedLevelEvent t m ⊆
      hlozExceptionalEvent t m ∪
        UpperAssembly.meshBranchUnion properGapMesh (screenedThirdTransitionEvent t m) := by
  have h := subset_union_diff_of_subset_union
    (hlozSeparatedLevelEvent_exceptional_mesh_cover t m)
  have hdiff :
      UpperAssembly.meshBranchUnion properGapMesh (thirdTransitionEvent t m) \
          hlozExceptionalEvent t m =
        UpperAssembly.meshBranchUnion properGapMesh (screenedThirdTransitionEvent t m) := by
    rw [← meshBranchUnion_diff]
    rfl
  rw [← hdiff]
  exact h

/-- Every exact four-favorite level is assigned to one of the six concrete
tilings, using its four successive threshold-creation locations. -/
theorem levelFavoriteSet_four_subset_six_hloz_tilings (m : ℕ) :
    levelFavoriteSet m 4 ⊆ ⋃ t, hlozSeparatedLevelEvent t m := by
  intro s hs
  change levelFavorite s m 4 at hs
  obtain ⟨n, hmax, hcount⟩ := hs
  have hthreshold : thresholdCount s n m = 4 := by
    rw [← hmax, thresholdCount_at_max_eq_favoriteCount]
    exact hcount
  let h₁r : ReachesThreshold s m 1 := ⟨n, by omega⟩
  let h₂r : ReachesThreshold s m 2 := ⟨n, by omega⟩
  let h₃r : ReachesThreshold s m 3 := ⟨n, by omega⟩
  let h₄r : ReachesThreshold s m 4 := ⟨n, by omega⟩
  let n₁ := Nat.find h₁r
  let n₂ := Nat.find h₂r
  let n₃ := Nat.find h₃r
  let n₄ := Nat.find h₄r
  have h₁ : ThresholdCreation s m 1 n₁ := thresholdCreation_natFind h₁r
  have h₂ : ThresholdCreation s m 2 n₂ := thresholdCreation_natFind h₂r
  have h₃ : ThresholdCreation s m 3 n₃ := thresholdCreation_natFind h₃r
  have h₄ : ThresholdCreation s m 4 n₄ := thresholdCreation_natFind h₄r
  have hn₄le : n₄ ≤ n := Nat.find_min' h₄r (by omega)
  have hnextAtN : thresholdCount s n (m + 1) = 0 :=
    (thresholdCount_succ_level_eq_zero_iff s n m).mpr hmax.le
  have hnext : thresholdCount s n₄ (m + 1) = 0 := by
    have hmono := thresholdCount_mono_time s (m + 1) hn₄le
    change thresholdCount s n₄ (m + 1) ≤ thresholdCount s n (m + 1) at hmono
    omega
  have h₁₂ : s n₁ ≠ s n₂ := creation_locations_ne (by norm_num) (by norm_num)
    (by norm_num) h₁ h₂
  have h₁₃ : s n₁ ≠ s n₃ := creation_locations_ne (by norm_num) (by norm_num)
    (by norm_num) h₁ h₃
  have h₁₄ : s n₁ ≠ s n₄ := creation_locations_ne (by norm_num) (by norm_num)
    (by norm_num) h₁ h₄
  have h₂₃ : s n₂ ≠ s n₃ := creation_locations_ne (by norm_num) (by norm_num)
    (by norm_num) h₂ h₃
  have h₂₄ : s n₂ ≠ s n₄ := creation_locations_ne (by norm_num) (by norm_num)
    (by norm_num) h₂ h₄
  have h₃₄ : s n₃ ≠ s n₄ := creation_locations_ne (by norm_num) (by norm_num)
    (by norm_num) h₃ h₄
  obtain ⟨t, ht⟩ := exists_dominoTiling_separating_four
    (s n₁) (s n₂) (s n₃) (s n₄) h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  rw [Set.mem_iUnion]
  exact ⟨t, n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, ht⟩

theorem secondTransitionEvent_subset_first (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    secondTransitionEvent t m a ⊆ firstTransitionEvent t m a := by
  intro s hs
  simp only [secondTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, hnext, h₁₂, h₁₃, h₂₃, ha₁, ha₂⟩ := hs
  have htime : n₂ < n₃ := creation_time_lt (by norm_num) (by norm_num)
    (by norm_num) h₂ h₃
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  change thresholdCount s n₂ (m + 1) ≤ thresholdCount s n₃ (m + 1) at hmono
  have hnext₂ : thresholdCount s n₂ (m + 1) = 0 := by omega
  simp only [firstTransitionEvent, Set.mem_iUnion]
  exact ⟨n₁, n₂, h₁, h₂, hnext₂, h₁₂, ha₁⟩

theorem thirdTransitionEvent_subset_second (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    thirdTransitionEvent t m a ⊆ secondTransitionEvent t m a := by
  intro s hs
  simp only [thirdTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
    ha₁, ha₂, ha₃⟩ := hs
  have htime : n₃ < n₄ := creation_time_lt (by norm_num) (by norm_num)
    (by norm_num) h₃ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  change thresholdCount s n₃ (m + 1) ≤ thresholdCount s n₄ (m + 1) at hmono
  have hnext₃ : thresholdCount s n₃ (m + 1) = 0 := by omega
  rcases hsep with ⟨h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩
  simp only [secondTransitionEvent, Set.mem_iUnion]
  exact ⟨n₁, n₂, n₃, h₁, h₂, h₃, hnext₃,
    h₁₂, h₁₃, h₂₃, ha₁, ha₂⟩

/-! Canonical upper-bound assembly. -/

/-- With the path-level events now fixed, the only remaining premises are
measure inequalities for the three successive transitions and the
exceptional family.  The finite mesh cover, six tilings, cubic summability,
recurrence, and Borel--Cantelli steps are all internal. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_path_transition_estimates
    (K : ℝ≥0)
    (hfirst : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (firstTransitionEvent t m a) ≤
        UpperCanonical.hlozTransitionCost K m)
    (hsecond : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (secondTransitionEvent t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (firstTransitionEvent t m a))
    (hthird : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (secondTransitionEvent t m a))
    (hexception : ∀ t, ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  have hscreened : ∀ t, ∑' m, simpleRandomWalk (hlozSeparatedLevelEvent t m) ≠ ∞ := by
    intro t
    apply UpperAssembly.screenedLevel_series_ne_top simpleRandomWalk properGapMesh
      (hlozSeparatedLevelEvent t) (hlozExceptionalEvent t)
      (firstTransitionEvent t) (secondTransitionEvent t) (screenedThirdTransitionEvent t)
      (UpperCanonical.hlozTransitionCost K) (K ^ 3)
      (3 * ScreeningInstantiation.kappa)
    · exact ScreeningInstantiation.hloz_parameter_inequalities.2.2.2.2.2.2.2.1
    · exact hlozSeparatedLevelEvent_screened_mesh_cover t
    · exact hfirst t
    · exact hsecond t
    · exact hthird t
    · exact hexception t
    · intro m
      exact (UpperCanonical.hlozTransitionCost_cube K m).le
  have hsum : ∑' m, simpleRandomWalk (levelFavoriteSet m 4) ≠ ∞ :=
    level_event_summable_of_six_tilings simpleRandomWalk
      levelFavoriteSet_four_subset_six_hloz_tilings hscreened
  exact UpperAssembly.ae_eventually_favoriteCount_le_three_of_M4_summable
    simpleRandomWalk hsum simpleRandomWalk_maxLocalTime_tendsto

end HLOZPathEvents
end Erdos1165
