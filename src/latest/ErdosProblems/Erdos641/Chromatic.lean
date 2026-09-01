/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos641.Structural
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Combinatorics.Pigeonhole

/-!
# Chromatic obstruction for the JSS construction

The proof counts large monochromatic pieces in many layers.  It uses only
finite products and cardinalities; no measure-theoretic probability space is
introduced.
-/

open Finset Fintype Filter
open scoped BigOperators

namespace Erdos641

open SimpleGraph
open Erdos182

noncomputable section

open Classical in
section

/-- The ceiling of `b / q`, in the generic ordered-semiring notation used by
Mathlib's floor/ceiling division API. -/
def majoritySize (b q : ℕ) : ℕ := b ⌈/⌉ q

lemma le_mul_majoritySize {b q : ℕ} (hq : 0 < q) :
    b ≤ q * majoritySize b q := by
  exact (ceilDiv_le_iff_le_mul hq).1 le_rfl

lemma majoritySize_pos {b q : ℕ} (hb : 0 < b) (hq : 0 < q) :
    0 < majoritySize b q := by
  by_contra hzero
  have hz : majoritySize b q = 0 := by omega
  have := le_mul_majoritySize (b := b) hq
  rw [hz] at this
  omega

/-- Vertices of layer `i` receiving color `a`. -/
def layerColorClass {n q : ℕ} (color : JSSVertex n → Fin q)
    (i : Fin (prsLayerCount n)) (a : Fin q) : Finset (JSSVertex n) :=
  (jssLayer n i).filter fun v ↦ color v = a

/-- Every positive layer has a color class of ceiling-average size. -/
lemma exists_majority_color {n q : ℕ} (hq : 0 < q)
    (hlayer : ∀ i < prsLayerCount n, 0 < prsLayerSize n i)
    (color : JSSVertex n → Fin q) (i : Fin (prsLayerCount n)) :
    ∃ a : Fin q, majoritySize (prsLayerSize n i) q ≤
      (layerColorClass color i a).card := by
  classical
  let r := majoritySize (prsLayerSize n i) q
  have hr : 0 < r := majoritySize_pos (hlayer i i.isLt) hq
  have hstrict : q * (r - 1) < prsLayerSize n i := by
    by_contra hnot
    have hle : prsLayerSize n i ≤ q * (r - 1) := by omega
    have hrle : majoritySize (prsLayerSize n i) q ≤ r - 1 :=
      (ceilDiv_le_iff_le_mul hq).2 hle
    dsimp only [r] at hrle hr
    omega
  obtain ⟨a, _ha, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := jssLayer n i) (t := (Finset.univ : Finset (Fin q)))
      (f := color) (n := r - 1) (fun _v _hv ↦ Finset.mem_univ _)
      (by simpa using hstrict)
  refine ⟨a, ?_⟩
  change r ≤ ((jssLayer n i).filter fun v ↦ color v = a).card
  omega

/-- Restrict every coordinate whose source lies in `A` by deleting `T` from
its possible target set. -/
def avoidanceAllowed {n : ℕ} (A T : Finset (JSSVertex n))
    (c : JSSCoordinate n) : Finset (JSSVertex n) :=
  if c.source ∈ A then jssAllowed c \ T else jssAllowed c

/-- Outcomes in which no source in `A` selects a target in `T`. -/
def avoidanceSpace {n : ℕ} (A T : Finset (JSSVertex n)) :
    Finset (JSSOutcome n) :=
  finiteChoiceSpace (avoidanceAllowed A T)

lemma mem_avoidanceSpace {n : ℕ} {A T : Finset (JSSVertex n)}
    {ω : JSSOutcome n} :
    ω ∈ avoidanceSpace A T ↔
      ω ∈ jssOutcomeSpace n ∧
        ∀ c : JSSCoordinate n, c.source ∈ A →
          ω c (Finset.mem_univ c) ∈ jssAllowed c \ T := by
  classical
  rw [avoidanceSpace, mem_finiteChoiceSpace]
  constructor
  · intro h
    constructor
    · rw [mem_jssOutcomeSpace]
      intro c
      by_cases hc : c.source ∈ A
      · exact Finset.sdiff_subset (by
          simpa [avoidanceAllowed, hc] using h c)
      · simpa [avoidanceAllowed, hc] using h c
    · intro c hc
      simpa [avoidanceAllowed, hc] using h c
  · rintro ⟨hspace, h⟩ c
    by_cases hc : c.source ∈ A
    · simpa [avoidanceAllowed, hc] using h c hc
    · simpa [avoidanceAllowed, hc] using (mem_jssOutcomeSpace.mp hspace c)

/-- Every avoidance event is contained in the admissible sample space. -/
lemma avoidanceSpace_subset {n : ℕ} (A T : Finset (JSSVertex n)) :
    avoidanceSpace A T ⊆ jssOutcomeSpace n := by
  classical
  intro ω hω
  exact (mem_avoidanceSpace.mp hω).1

/-- Later layers on which `T` occupies at least the ceiling-average
fraction. -/
def heavyLaterLayers (n q : ℕ) (i : Fin (prsLayerCount n))
    (T : Finset (JSSVertex n)) : Finset (Fin (prsLayerCount n)) :=
  Finset.univ.filter fun j ↦
    i < j ∧ majoritySize (prsLayerSize n j) q ≤
      (T ∩ jssLayer n j).card

@[simp] lemma mem_heavyLaterLayers {n q : ℕ}
    {i : Fin (prsLayerCount n)} {T : Finset (JSSVertex n)}
    {j : Fin (prsLayerCount n)} :
    j ∈ heavyLaterLayers n q i T ↔
      i < j ∧ majoritySize (prsLayerSize n j) q ≤
        (T ∩ jssLayer n j).card := by
  simp [heavyLaterLayers]

/-- Coordinates indexed by a source in `A` and a target layer in `J`. -/
def avoidanceCoordinateEmbedding {n : ℕ}
    (i : Fin (prsLayerCount n))
    (A : Finset (JSSVertex n)) (J : Finset (Fin (prsLayerCount n)))
    (hA : A ⊆ jssLayer n i)
    (hJ : ∀ j ∈ J, i < j) :
    (↑A) × (↑J) ↪ JSSCoordinate n where
  toFun p := ⟨p.1.1, p.2.1, by
    have hs := mem_jssLayer_iff.mp (hA p.1.2)
    have ht := hJ p.2.1 p.2.2
    simpa [hs] using ht⟩
  inj' := by
    intro p r h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg JSSCoordinate.source h
    · apply Subtype.ext
      exact congrArg JSSCoordinate.targetLayer h

def avoidanceCoordinates {n : ℕ}
    (i : Fin (prsLayerCount n))
    (A : Finset (JSSVertex n)) (J : Finset (Fin (prsLayerCount n)))
    (hA : A ⊆ jssLayer n i)
    (hJ : ∀ j ∈ J, i < j) : Finset (JSSCoordinate n) :=
  Finset.univ.map (avoidanceCoordinateEmbedding i A J hA hJ)

lemma card_avoidanceCoordinates {n : ℕ}
    (i : Fin (prsLayerCount n))
    (A : Finset (JSSVertex n)) (J : Finset (Fin (prsLayerCount n)))
    (hA : A ⊆ jssLayer n i)
    (hJ : ∀ j ∈ J, i < j) :
    (avoidanceCoordinates i A J hA hJ).card = A.card * J.card := by
  rw [avoidanceCoordinates, Finset.card_map]
  simp

lemma mem_avoidanceCoordinates {n : ℕ}
    (i : Fin (prsLayerCount n))
    (A : Finset (JSSVertex n)) (J : Finset (Fin (prsLayerCount n)))
    (hA : A ⊆ jssLayer n i)
    (hJ : ∀ j ∈ J, i < j) {c : JSSCoordinate n}
    (hc : c ∈ avoidanceCoordinates i A J hA hJ) :
    c.source ∈ A ∧ c.targetLayer ∈ J := by
  obtain ⟨p, _hp, hpc⟩ := Finset.mem_map.mp hc
  rw [← hpc]
  exact ⟨p.1.2, p.2.2⟩

lemma q_mul_card_avoidanceAllowed_le {n q : ℕ} (hq : 0 < q)
    (i : Fin (prsLayerCount n))
    (A T : Finset (JSSVertex n)) (J : Finset (Fin (prsLayerCount n)))
    (hA : A ⊆ jssLayer n i)
    (hJheavy : J ⊆ heavyLaterLayers n q i T)
    {c : JSSCoordinate n}
    (hc : c ∈ avoidanceCoordinates i A J hA
      (fun _j hj ↦ (mem_heavyLaterLayers.mp (hJheavy hj)).1)) :
    q * (avoidanceAllowed A T c).card ≤
      (q - 1) * (jssAllowed c).card := by
  classical
  let hJ : ∀ j ∈ J, i < j :=
    fun j hj ↦ (mem_heavyLaterLayers.mp (hJheavy hj)).1
  have hc' := mem_avoidanceCoordinates i A J hA hJ hc
  have hheavy := (mem_heavyLaterLayers.mp (hJheavy hc'.2)).2
  have hceil : (jssAllowed c).card ≤
      q * (T ∩ jssLayer n c.targetLayer).card := by
    rw [card_jssAllowed]
    exact (le_mul_majoritySize hq).trans (Nat.mul_le_mul_left q hheavy)
  rw [avoidanceAllowed, if_pos hc'.1, Finset.card_sdiff]
  have hinter : (T ∩ jssAllowed c).card =
      (T ∩ jssLayer n c.targetLayer).card := by
    simp [jssAllowed]
  rw [hinter]
  calc
    q * ((jssAllowed c).card -
        (T ∩ jssLayer n c.targetLayer).card) =
        q * (jssAllowed c).card -
          q * (T ∩ jssLayer n c.targetLayer).card := by
      exact Nat.mul_sub_left_distrib _ _ _
    _ ≤ q * (jssAllowed c).card - (jssAllowed c).card :=
      Nat.sub_le_sub_left hceil _
    _ = (q - 1) * (jssAllowed c).card := by
      rw [Nat.sub_mul, one_mul]

/-- Division-free product estimate for one chromatic bad event. -/
theorem card_avoidanceSpace_mul_pow_le {n q : ℕ} (hq : 0 < q)
    (i : Fin (prsLayerCount n))
    (A T : Finset (JSSVertex n)) (J : Finset (Fin (prsLayerCount n)))
    (hA : A ⊆ jssLayer n i)
    (hJheavy : J ⊆ heavyLaterLayers n q i T) :
    (avoidanceSpace A T).card * q ^ (A.card * J.card) ≤
      (jssOutcomeSpace n).card * (q - 1) ^ (A.card * J.card) := by
  classical
  let hJ : ∀ j ∈ J, i < j :=
    fun j hj ↦ (mem_heavyLaterLayers.mp (hJheavy hj)).1
  let D := avoidanceCoordinates i A J hA hJ
  have hDcard : D.card = A.card * J.card :=
    card_avoidanceCoordinates i A J hA hJ
  rw [avoidanceSpace, jssOutcomeSpace, card_finiteChoiceSpace,
    card_finiteChoiceSpace, ← hDcard]
  calc
    (∏ c, (avoidanceAllowed A T c).card) * q ^ D.card =
        (∏ c, (avoidanceAllowed A T c).card) *
          (∏ c, if c ∈ D then q else 1) := by simp
    _ = ∏ c, (avoidanceAllowed A T c).card *
          (if c ∈ D then q else 1) := by rw [Finset.prod_mul_distrib]
    _ ≤ ∏ c, (jssAllowed c).card *
          (if c ∈ D then q - 1 else 1) := by
      apply Finset.prod_le_prod'
      intro c _hc
      by_cases hcD : c ∈ D
      · simp only [hcD, if_true]
        simpa [Nat.mul_comm] using
          q_mul_card_avoidanceAllowed_le hq i A T J hA hJheavy hcD
      · simp only [hcD, if_false, Nat.mul_one]
        by_cases hcA : c.source ∈ A
        · rw [avoidanceAllowed, if_pos hcA]
          exact Finset.card_le_card Finset.sdiff_subset
        · simp [avoidanceAllowed, hcA]
    _ = (∏ c, (jssAllowed c).card) *
          (∏ c, if c ∈ D then q - 1 else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ c, (jssAllowed c).card) * (q - 1) ^ D.card := by simp

/-- Bad outcomes witnessed at a fixed first layer.  The powersets enumerate
all possible source and tail pieces; the filter retains only pieces that are
large in at least `R` later layers. -/
def chromaticBadAt (n q R : ℕ) (i : Fin (prsLayerCount n)) :
    Finset (JSSOutcome n) := by
  classical
  exact (jssLayer n i).powerset.biUnion fun A ↦
    (jssStrictTail n i).powerset.biUnion fun T ↦
      if majoritySize (prsLayerSize n i) q ≤ A.card ∧
          R ≤ (heavyLaterLayers n q i T).card then
        avoidanceSpace A T
      else ∅

/-- Union of the chromatic bad events over the possible first layers. -/
def chromaticBad (n q R : ℕ) : Finset (JSSOutcome n) :=
  Finset.univ.biUnion (chromaticBadAt n q R)

/-- A proper `q`-coloring of an admissible outcome creates a chromatic bad
event, provided the construction has at least `q(R+1)` layers. -/
lemma mem_chromaticBad_of_coloring {n q R : ℕ} (hq : 0 < q)
    (hlayer : ∀ i < prsLayerCount n, 0 < prsLayerSize n i)
    (hcount : q * (R + 1) ≤ prsLayerCount n)
    (ω : JSSOutcome n) (hω : ω ∈ jssOutcomeSpace n)
    (C : (jssGraph ω hω).Coloring (Fin q)) :
    ω ∈ chromaticBad n q R := by
  classical
  have hmajority : ∀ i : Fin (prsLayerCount n),
      ∃ a : Fin q, majoritySize (prsLayerSize n i) q ≤
        (layerColorClass C i a).card :=
    fun i ↦ exists_majority_color hq hlayer C i
  choose major hmajor using hmajority
  obtain ⟨a, _ha, haCount⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := (Finset.univ : Finset (Fin (prsLayerCount n))))
      (t := (Finset.univ : Finset (Fin q))) (f := major) (n := R + 1)
      (fun _i _hi ↦ Finset.mem_univ _) ⟨⟨0, hq⟩, Finset.mem_univ _⟩
      (by simpa using hcount)
  let L : Finset (Fin (prsLayerCount n)) :=
    Finset.univ.filter fun i ↦ major i = a
  have hLcard : R + 1 ≤ L.card := by simpa [L] using haCount
  have hLne : L.Nonempty := Finset.card_pos.mp (by omega)
  let i : Fin (prsLayerCount n) := L.min' hLne
  have hiL : i ∈ L := Finset.min'_mem L hLne
  have hErase : R ≤ (L.erase i).card := by
    rw [Finset.card_erase_of_mem hiL]
    omega
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hErase
  let A := layerColorClass C i a
  let T := (jssStrictTail n i).filter fun v ↦ C v = a
  have hAsub : A ⊆ jssLayer n i := Finset.filter_subset _ _
  have hTsub : T ⊆ jssStrictTail n i := Finset.filter_subset _ _
  have hJlater : ∀ j ∈ J, i < j := by
    intro j hj
    have hjErase := hJsub hj
    have hjL := (Finset.mem_erase.mp hjErase).2
    have hji := (Finset.mem_erase.mp hjErase).1
    exact (Finset.min'_le L j hjL).lt_of_ne (Ne.symm hji)
  have hJheavy : J ⊆ heavyLaterLayers n q i T := by
    intro j hj
    apply mem_heavyLaterLayers.mpr
    constructor
    · exact hJlater j hj
    · have hjL := (Finset.mem_erase.mp (hJsub hj)).2
      have hmajorEq : major j = a := Finset.mem_filter.mp hjL |>.2
      have hmaj := hmajor j
      rw [hmajorEq] at hmaj
      have hpieces : layerColorClass C j a = T ∩ jssLayer n j := by
        ext v
        constructor
        · intro hv
          have hvLayer := (Finset.mem_filter.mp hv).1
          have hvColor := (Finset.mem_filter.mp hv).2
          exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
            ⟨mem_jssStrictTail.mpr (by
              simpa [mem_jssLayer_iff.mp hvLayer] using hJlater j hj),
              hvColor⟩, hvLayer⟩
        · intro hv
          have hvT := (Finset.mem_inter.mp hv).1
          have hvLayer := (Finset.mem_inter.mp hv).2
          exact Finset.mem_filter.mpr ⟨hvLayer,
            (Finset.mem_filter.mp hvT).2⟩
      calc
        majoritySize (prsLayerSize n j) q ≤
            (layerColorClass C j a).card := hmaj
        _ = (T ∩ jssLayer n j).card := congrArg Finset.card hpieces
  have hAvoid : ω ∈ avoidanceSpace A T := by
    apply mem_avoidanceSpace.mpr
    refine ⟨hω, ?_⟩
    intro c hcA
    apply Finset.mem_sdiff.mpr
    constructor
    · exact (mem_jssOutcomeSpace.mp hω) c
    · intro htargetT
      have hsourceColor : C c.source = a :=
        (Finset.mem_filter.mp hcA).2
      have htargetColor : C (ω c (Finset.mem_univ c)) = a :=
        (Finset.mem_filter.mp htargetT).2
      have hadj := jssGraph_adj_source_target ω hω c
      have hne := C.valid hadj
      apply hne
      rw [jssTarget_eq_outcome]
      exact hsourceColor.trans htargetColor.symm
  simp only [chromaticBad, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simp only [chromaticBadAt, Finset.mem_biUnion]
  refine ⟨A, Finset.mem_powerset.mpr hAsub, T,
    Finset.mem_powerset.mpr hTsub, ?_⟩
  rw [if_pos]
  · exact hAvoid
  · constructor
    · exact hmajor i |>.trans_eq (by
        have hiMajor : major i = a := (Finset.mem_filter.mp hiL).2
        simp [A, hiMajor])
    · exact hJcard ▸ Finset.card_le_card hJheavy

end

end

end Erdos641
