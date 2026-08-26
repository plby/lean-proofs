import Mathlib
import ErdosProblems.Erdos550.HPClusterWeights
import ErdosProblems.Erdos550.HPGoodMatchingEdges

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Head atypicality supported on reduced neighbours

For a fixed head, assign a target cluster its actual density when it is a
reduced neighbour and zero otherwise.  Non-neighbours then create no bad
vertices, while regularity bounds the bad set of every neighbour by the usual
`ε`-fraction.  Summing gives the bad-count mass used to form low-bad head
cores.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

noncomputable def hpHeadDensityCap
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head target : ι) : ℝ :=
  if R.Adj head target then
    (G.edgeDensity (C head) (C target) : ℝ)
  else 0

lemma hpHeadEndpointWeight_eq_densityCap_mul
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head target : ι) :
    hpHeadEndpointWeight G R C head target =
      hpHeadDensityCap G R C head target * (C target).card := by
  by_cases h : R.Adj head target <;>
    simp [hpHeadEndpointWeight, hpHeadDensityCap, h]

lemma head_endpoint_bad_card_le
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (hC : ∀ i, (C i).Nonempty)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (head target : ι) :
    (((C head).filter fun v =>
        (((C target).filter fun x => G.Adj v x).card : ℝ) <
          (hpHeadDensityCap G R C head target - ε) *
            ((C target).card : ℝ)).card : ℝ) ≤
      ε * ((C head).card : ℝ) := by
  by_cases hR : R.Adj head target
  · simpa [hpHeadDensityCap, hR] using!
      (isUniform_few_low_degree G hε0 hε1
        (hC head) (hC target) (huni head target hR)).le
  · have hempty :
        (C head).filter (fun v =>
          (((C target).filter fun x => G.Adj v x).card : ℝ) <
            (hpHeadDensityCap G R C head target - ε) *
              ((C target).card : ℝ)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv hbad
      rw [hpHeadDensityCap, if_neg hR] at hbad
      have hdeg :
          (0 : ℝ) ≤
            (((C target).filter fun x => G.Adj v x).card : ℝ) :=
        Nat.cast_nonneg _
      have hprod :
          (0 : ℝ) ≤ ε * ((C target).card : ℝ) :=
        mul_nonneg hε0.le (Nat.cast_nonneg _)
      nlinarith
    have hcard := congrArg Finset.card hempty
    calc
      (((C head).filter fun v =>
          (((C target).filter fun x => G.Adj v x).card : ℝ) <
            (hpHeadDensityCap G R C head target - ε) *
              ((C target).card : ℝ)).card : ℝ) =
          0 := by exact_mod_cast hcard
      _ ≤ ε * ((C head).card : ℝ) :=
        mul_nonneg hε0.le (Nat.cast_nonneg _)

/-- Double-counting identity between vertex bad-counts and target bad sets. -/
lemma sum_badCount_eq_sum_bad_targets
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ)
    (ε : ℝ) (Tset : Finset ι) (base : Finset V) :
    ∑ v ∈ base, (badCount G C dcap ε Tset v : ℝ) =
      ∑ i ∈ Tset, (((base.filter fun v =>
        (((C i).filter fun x => G.Adj v x).card : ℝ) <
          (dcap i - ε) * ((C i).card : ℝ)).card : ℕ) : ℝ) := by
  simp +decide [badCount]
  simp +decide only [Finset.card_filter]
  exact mod_cast Finset.sum_comm

/-- Total bad-count mass in a head cluster is at most one `ε|head|` term per
tested target cluster. -/
lemma head_badCount_mass_le
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (hC : ∀ i, (C i).Nonempty)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (Tset : Finset ι) (head : ι) :
    (∑ v ∈ C head,
        (badCount G C (hpHeadDensityCap G R C head) ε Tset v : ℝ)) ≤
      (Tset.card : ℝ) * ε * ((C head).card : ℝ) := by
  rw [sum_badCount_eq_sum_bad_targets]
  calc
    _ ≤ ∑ _i ∈ Tset, ε * ((C head).card : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact head_endpoint_bad_card_le
        G R C hC ε hε0 hε1 huni head i
    _ = (Tset.card : ℝ) * ε * ((C head).card : ℝ) := by
      simp
      ring

end Erdos550
