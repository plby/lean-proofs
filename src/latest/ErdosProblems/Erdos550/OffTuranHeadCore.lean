import Mathlib
import ErdosProblems.Erdos550.HPLowBadCore
import ErdosProblems.Erdos550.OffTuranHeadAtypicality

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Low-bad typical cores in the two head clusters

Each head core has two independent deletions.  First delete the exceptional
vertices of the regular pair between the two heads.  Then delete vertices
which are atypical toward too many matching endpoints.  This file records the
combined loss and the two consequences needed by the stateful embedding:
enough vertices for every seed, and enough cross-head neighbours for the next
seed.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

/-- Vertices of `source` having the density-threshold degree into `target`. -/
noncomputable def hpPairTypicalCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d : ℝ) (source target : Finset V) : Finset V :=
  source.filter fun v =>
    (d - ε) * (target.card : ℝ) ≤
      ((target.filter fun x => G.Adj v x).card : ℝ)

lemma hpPairTypicalCore_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d : ℝ) (source target : Finset V) :
    hpPairTypicalCore G ε d source target ⊆ source :=
  Finset.filter_subset _ _

lemma mem_hpPairTypicalCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d : ℝ) (source target : Finset V) (v : V) :
    v ∈ hpPairTypicalCore G ε d source target ↔
      v ∈ source ∧
        (d - ε) * (target.card : ℝ) ≤
          ((target.filter fun x => G.Adj v x).card : ℝ) := by
  simp [hpPairTypicalCore]

/-- Regularity deletes fewer than an `ε`-fraction when forming the structural
head core. -/
lemma hpPairTypicalCore_removed_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (source target : Finset V)
    (hsource : source.Nonempty) (htarget : target.Nonempty)
    (huni : G.IsUniform ε source target)
    (hdens : d ≤ (G.edgeDensity source target : ℝ)) :
    (((source \ hpPairTypicalCore G ε d source target).card : ℕ) : ℝ) <
      ε * (source.card : ℝ) := by
  let bad := source.filter fun v =>
    (((target.filter fun x => G.Adj v x).card : ℝ) <
      ((G.edgeDensity source target : ℝ) - ε) *
        (target.card : ℝ))
  have hsub :
      source \ hpPairTypicalCore G ε d source target ⊆ bad := by
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨hv'.1, ?_⟩
    have hlt :
        (((target.filter fun x => G.Adj v x).card : ℝ) <
          (d - ε) * (target.card : ℝ)) := by
      exact lt_of_not_ge fun h =>
        hv'.2 ((mem_hpPairTypicalCore
          G ε d source target v).2 ⟨hv'.1, h⟩)
    have htarget0 : (0 : ℝ) ≤ target.card := Nat.cast_nonneg _
    exact hlt.trans_le
      (mul_le_mul_of_nonneg_right
        (sub_le_sub_right hdens ε) htarget0)
  have hcard :
      (source \ hpPairTypicalCore G ε d source target).card ≤ bad.card :=
    Finset.card_le_card hsub
  have hcardReal :
      (((source \ hpPairTypicalCore G ε d source target).card : ℕ) : ℝ) ≤
        (bad.card : ℝ) := by
    exact_mod_cast hcard
  exact hcardReal.trans_lt
    (isUniform_few_low_degree G hε0 hε1
      hsource htarget huni)

/-- Exact upper bound used for the two deletions in one head. -/
noncomputable def hpHeadCoreLoss
    {V ι : Type*} [Fintype V]
    (ε thr : ℝ) (Tset : Finset ι) (headBase : Finset V) : ℝ :=
  ε * (headBase.card : ℝ) +
    ((Tset.card : ℝ) * ε * (headBase.card : ℝ)) / thr

/-- The actual head core: structural pair-typical vertices with bad-count at
most `thr`. -/
noncomputable def hpOffTuranHeadCore
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (ε d : ℝ)
    (Tset : Finset ι) (thr : ℝ)
    (head other : ι) : Finset V :=
  hpLowBadCore G C (hpHeadDensityCap G R C head) ε Tset
    (hpPairTypicalCore G ε d (C head) (C other)) thr

lemma hpOffTuranHeadCore_subset
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (ε d : ℝ)
    (Tset : Finset ι) (thr : ℝ) (head other : ι) :
    hpOffTuranHeadCore G R C ε d Tset thr head other ⊆ C head :=
  (hpLowBadCore_subset G C (hpHeadDensityCap G R C head) ε Tset
    (hpPairTypicalCore G ε d (C head) (C other)) thr).trans
      (hpPairTypicalCore_subset G ε d (C head) (C other))

lemma hpOffTuranHeadCore_badCount_le
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (ε d : ℝ)
    (Tset : Finset ι) (thr : ℝ) (head other : ι)
    {v : V}
    (hv : v ∈ hpOffTuranHeadCore G R C ε d Tset thr head other) :
    (badCount G C (hpHeadDensityCap G R C head) ε Tset v : ℝ) ≤ thr :=
  (mem_hpLowBadCore G C (hpHeadDensityCap G R C head) ε Tset
    (hpPairTypicalCore G ε d (C head) (C other)) thr v).mp hv |>.2

lemma hpOffTuranHeadCore_structural
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (ε d : ℝ)
    (Tset : Finset ι) (thr : ℝ) (head other : ι)
    {v : V}
    (hv : v ∈ hpOffTuranHeadCore G R C ε d Tset thr head other) :
    v ∈ hpPairTypicalCore G ε d (C head) (C other) :=
  (mem_hpLowBadCore G C (hpHeadDensityCap G R C head) ε Tset
    (hpPairTypicalCore G ε d (C head) (C other)) thr v).mp hv |>.1

/-- Combined structural and high-bad deletion loss. -/
lemma hpOffTuranHeadCore_complement_le
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (hC : ∀ i, (C i).Nonempty)
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (Tset : Finset ι) (thr : ℝ) (hthr : 0 < thr)
    (head other : ι)
    (hheadUni : G.IsUniform ε (C head) (C other))
    (hheadDens : d ≤ (G.edgeDensity (C head) (C other) : ℝ)) :
    (((C head \ hpOffTuranHeadCore
        G R C ε d Tset thr head other).card : ℕ) : ℝ) ≤
      hpHeadCoreLoss ε thr Tset (C head) := by
  apply hpLowBadCore_complement_card_upper
    G C (hpHeadDensityCap G R C head) ε Tset
    (C head) (hpPairTypicalCore G ε d (C head) (C other))
    thr (ε * ((C head).card : ℝ))
    ((Tset.card : ℝ) * ε * ((C head).card : ℝ))
    hthr
  · exact hpPairTypicalCore_subset G ε d (C head) (C other)
  · exact (hpPairTypicalCore_removed_lt G ε d hε0 hε1
      (C head) (C other) (hC head) (hC other)
      hheadUni hheadDens).le
  · exact head_badCount_mass_le
      G R C hC ε hε0 hε1 huni Tset head

/-- Cardinality lower bound for a head core. -/
lemma hpOffTuranHeadCore_card_lower
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (hC : ∀ i, (C i).Nonempty)
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (Tset : Finset ι) (thr : ℝ) (hthr : 0 < thr)
    (head other : ι)
    (hheadUni : G.IsUniform ε (C head) (C other))
    (hheadDens : d ≤ (G.edgeDensity (C head) (C other) : ℝ)) :
    (C head).card - hpHeadCoreLoss ε thr Tset (C head) ≤
      (hpOffTuranHeadCore G R C ε d Tset thr head other).card := by
  have hsub :=
    hpOffTuranHeadCore_subset G R C ε d Tset thr head other
  have hsplit :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hsplitReal :
      (((C head \ hpOffTuranHeadCore
          G R C ε d Tset thr head other).card : ℕ) : ℝ) +
        ((hpOffTuranHeadCore
          G R C ε d Tset thr head other).card : ℝ) =
        ((C head).card : ℝ) := by
    exact_mod_cast hsplit
  linarith [hpOffTuranHeadCore_complement_le
    G R C hC ε d hε0 hε1 huni Tset thr hthr
    head other hheadUni hheadDens]

/-- A scalar room inequality turns the cardinality lower bound into the exact
strict natural inequality required for seed placement. -/
lemma hpOffTuranHeadCore_seed_room
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (hC : ∀ i, (C i).Nonempty)
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (Tset : Finset ι) (thr : ℝ) (hthr : 0 < thr)
    (head other : ι)
    (hheadUni : G.IsUniform ε (C head) (C other))
    (hheadDens : d ≤ (G.edgeDensity (C head) (C other) : ℝ))
    (seed : ℕ)
    (hroom :
      (seed : ℝ) + hpHeadCoreLoss ε thr Tset (C head) <
        (C head).card) :
    seed <
      (hpOffTuranHeadCore G R C ε d Tset thr head other).card := by
  have hlower := hpOffTuranHeadCore_card_lower
    G R C hC ε d hε0 hε1 huni Tset thr hthr
    head other hheadUni hheadDens
  exact_mod_cast (show
    (seed : ℝ) <
      (hpOffTuranHeadCore G R C ε d Tset thr head other).card by
        linarith)

/-- If the combined deletion fits below the complementary `(1-ε)` fraction,
the head core retains at least an `ε`-fraction of its base cluster. -/
lemma hpOffTuranHeadCore_epsilon_fraction
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (hC : ∀ i, (C i).Nonempty)
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (Tset : Finset ι) (thr : ℝ) (hthr : 0 < thr)
    (head other : ι)
    (hheadUni : G.IsUniform ε (C head) (C other))
    (hheadDens : d ≤ (G.edgeDensity (C head) (C other) : ℝ))
    (hroom :
      hpHeadCoreLoss ε thr Tset (C head) ≤
        (1 - ε) * ((C head).card : ℝ)) :
    ε * ((C head).card : ℝ) ≤
      (hpOffTuranHeadCore G R C ε d Tset thr head other).card := by
  have hlower := hpOffTuranHeadCore_card_lower
    G R C hC ε d hε0 hε1 huni Tset thr hthr
    head other hheadUni hheadDens
  linarith

/-- Every vertex of the opposite head core keeps `need` neighbours in this
head core once the raw regular-pair degree absorbs the combined deletion. -/
lemma hpOffTuranHeadCore_cross_degree
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (hC : ∀ i, (C i).Nonempty)
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (Tset : Finset ι) (thr : ℝ) (hthr : 0 < thr)
    (head other : ι)
    (hheadUni : G.IsUniform ε (C head) (C other))
    (hheadDens : d ≤ (G.edgeDensity (C head) (C other) : ℝ))
    (need : ℝ)
    (hroom :
      need + hpHeadCoreLoss ε thr Tset (C head) ≤
        (d - ε) * ((C head).card : ℝ))
    {u : V}
    (hu : u ∈ hpOffTuranHeadCore
      G R C ε d Tset thr other head) :
    need ≤
      (((hpOffTuranHeadCore
        G R C ε d Tset thr head other).filter fun v =>
          G.Adj v u).card : ℝ) := by
  have huStructural :=
    hpOffTuranHeadCore_structural
      G R C ε d Tset thr other head hu
  have huDegree :
      (d - ε) * ((C head).card : ℝ) ≤
        (((C head).filter fun v => G.Adj u v).card : ℝ) :=
    (mem_hpPairTypicalCore
      G ε d (C other) (C head) u).mp huStructural |>.2
  have huDegree' :
      need + hpHeadCoreLoss ε thr Tset (C head) ≤
        (((C head).filter fun v => G.Adj v u).card : ℝ) := by
    rw [show (C head).filter (fun v => G.Adj v u) =
        (C head).filter (fun v => G.Adj u v) by
      ext v
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ => G.adj_comm v u]
    exact hroom.trans huDegree
  apply filtered_degree_after_core_deletion
    (C head)
    (hpOffTuranHeadCore G R C ε d Tset thr head other)
    (fun v => G.Adj v u)
    (hpOffTuranHeadCore_subset G R C ε d Tset thr head other)
    need (hpHeadCoreLoss ε thr Tset (C head)) huDegree'
  exact hpOffTuranHeadCore_complement_le
    G R C hC ε d hε0 hε1 huni Tset thr hthr
    head other hheadUni hheadDens

end Erdos550
