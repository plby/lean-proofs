/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.LowerAssembly
import ErdosProblems.Erdos360.RandomDiversity

/-!
# A coarse modular route to the ordinary-growth certificate

The final lower-bound assembly consumes `CFPOrdinaryGrowthCertificate`.
This file constructs that certificate directly from the already checked
coarse modular phase theorem.  It is useful whenever the sharper adaptive
parameter ledger is unnecessary: an absolute loss of `64` is harmless for
the order-of-growth result.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The two alternatives of the coarse modular phase theorem both imply a
specified residue gain. -/
theorem residue_gain_of_coarse_modular_phases
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (A.image fun a : ℕ => (a : ZMod t)))
    {phaseCount q : ℕ}
    (hlog : 4 * (Nat.log 2 t + 1) ^ 2 ≤ phaseCount)
    (hhalf : 2 * phaseCount ≤
      (A.image fun a : ℕ => (a : ZMod t)).card)
    (hmod : 64 * q ≤ t)
    (hquad : 64 * q ≤ phaseCount *
      (A.image fun a : ℕ => (a : ZMod t)).card) :
    q ≤ (occupiedResidues A.subsetSum t).card := by
  rcases occupiedResidues_lower_of_phaseDiverse ht A hdiverse hlog hhalf with
    hfill | hgrowth
  · omega
  · omega

/-- Source-facing constructor for `CFPOrdinaryGrowthCertificate` using the
coarse modular phase theorem at every pivot. -/
theorem exists_CFPOrdinaryGrowthCertificate_of_coarse_modular_phases
    {P seed pivots : Finset ℕ}
    {nzero diameter residueGain phaseCount diversity : ℕ}
    (hunion : seed ∪ pivots = P)
    (hdisjoint : Disjoint seed pivots)
    (hpivots : ∀ t ∈ pivots, 0 < t)
    (hphase : ∀ (t : ℕ) (ht : t ∈ pivots),
      @PhaseDiverse t ⟨(hpivots t ht).ne'⟩ (hpivots t ht)
        (seed.image fun a : ℕ => (a : ZMod t)))
    (hlog : ∀ t ∈ pivots,
      4 * (Nat.log 2 t + 1) ^ 2 ≤ phaseCount)
    (hhalf : ∀ t ∈ pivots,
      2 * phaseCount ≤
        (seed.image fun a : ℕ => (a : ZMod t)).card)
    (hmod : ∀ t ∈ pivots, 64 * residueGain ≤ t)
    (hquad : ∀ t ∈ pivots,
      64 * residueGain ≤ phaseCount *
        (seed.image fun a : ℕ => (a : ZMod t)).card)
    (htarget : nzero ≤
      seed.subsetSum.card + pivots.card * residueGain)
    (hdiversity : 0 < diversity)
    (hdiverse : Diverse (seed ∪ pivots) diversity)
    (hsum : (∑ z ∈ P, z) ≤ diameter) :
    Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter) := by
  refine ⟨
    { seed := seed
      pivots := pivots
      residueGain := residueGain
      diversity := diversity
      union_eq := hunion
      disjoint := hdisjoint
      pivots_pos := hpivots
      residues := ?_
      target := htarget
      diversity_pos := hdiversity
      diverse := hdiverse
      sum_le := hsum }⟩
  intro t ht
  letI : NeZero t := ⟨(hpivots t ht).ne'⟩
  exact residue_gain_of_coarse_modular_phases (hpivots t ht) seed
    (hphase t ht) (hlog t ht) (hhalf t ht) (hmod t ht) (hquad t ht)

/-- The source-facing coarse constructor with phase diversity discharged
from ordinary divisor diversity and the cardinal scale of the seed.  The
inequality `2*t ≤ (seedDiversity+1)*|seed|` is exactly what turns the
subgroup-index bound `d*|seed| ≤ 2*t` into `d-1 ≤ seedDiversity`. -/
theorem exists_CFPOrdinaryGrowthCertificate_of_diverse_card_scale
    {P seed pivots : Finset ℕ} {lo hi : ℕ}
    {nzero diameter residueGain phaseCount seedDiversity diversity : ℕ}
    (hunion : seed ∪ pivots = P)
    (hdisjoint : Disjoint seed pivots)
    (hseedRange : seed ⊆ Finset.Ico lo hi)
    (hpivots : ∀ t ∈ pivots, 0 < t)
    (hwidth : ∀ t ∈ pivots, hi - lo ≤ t)
    (hseedDiverse : DiverseSampling.DiverseNat seed seedDiversity)
    (hscale : ∀ t ∈ pivots,
      2 * t ≤ (seedDiversity + 1) * seed.card)
    (hlog : ∀ t ∈ pivots,
      4 * (Nat.log 2 t + 1) ^ 2 ≤ phaseCount)
    (hhalf : ∀ t ∈ pivots,
      2 * phaseCount ≤
        (seed.image fun a : ℕ ↦ (a : ZMod t)).card)
    (hmod : ∀ t ∈ pivots, 64 * residueGain ≤ t)
    (hquad : ∀ t ∈ pivots,
      64 * residueGain ≤ phaseCount *
        (seed.image fun a : ℕ ↦ (a : ZMod t)).card)
    (htarget : nzero ≤
      seed.subsetSum.card + pivots.card * residueGain)
    (hdiversity : 0 < diversity)
    (hdiverse : Diverse (seed ∪ pivots) diversity)
    (hsum : (∑ z ∈ P, z) ≤ diameter) :
    Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter) := by
  apply exists_CFPOrdinaryGrowthCertificate_of_coarse_modular_phases
    hunion hdisjoint hpivots
  · intro t ht
    letI : NeZero t := ⟨(hpivots t ht).ne'⟩
    exact phaseDiverse_cast_of_diverse_of_card_scale
      (hpivots t ht) seed hseedRange (hwidth t ht)
      hseedDiverse (hscale t ht)
  · exact hlog
  · exact hhalf
  · exact hmod
  · exact hquad
  · exact htarget
  · exact hdiversity
  · exact hdiverse
  · exact hsum

/-- A complete local ordinary-growth constructor for one random pool in a
short positive interval.  A balanced random bisection supplies a diverse
seed and a disjoint pivot set.  The coarse modular phase theorem then gives
`residueGain` new sums at every pivot.  All asymptotic work is isolated in
the displayed numerical hypotheses; in particular no prime, coloring, or
analytic assertion is hidden in this theorem.

For the constant-loss route one takes `lo = y / d + 1`,
`hi = 2 * y / d + 1`, and a fixed sufficiently large `ell`.  The lower
bound on `ell` is paid through `hmod`; the remaining cardinal/diversity
budgets are exactly the entries which the eventual parameter ledger must
verify. -/
theorem exists_CFPOrdinaryGrowthCertificate_of_diverse_shortInterval
    {P : Finset ℕ} {lo hi K phaseCount residueGain nzero diameter : ℕ}
    (hlo : 0 < lo)
    (hP : P ⊆ Finset.Ico lo hi)
    (hdiverse : DiverseSampling.DiverseNat P K)
    (hprobability :
      (2 : ℝ) * (((hi - 1 : ℕ) : ℝ) + 1) *
        Real.exp (-(K : ℝ) / 24) < 1)
    (hwidth : hi - lo ≤ lo)
    (hscale : 2 * (hi - 1) ≤ (K / 4 + 1) * (P.card / 4))
    (hlog : 4 * (Nat.log 2 (hi - 1) + 1) ^ 2 ≤ phaseCount)
    (hhalf : 2 * phaseCount ≤ P.card / 4)
    (hmod : 64 * residueGain ≤ lo)
    (hquad : 64 * residueGain ≤ phaseCount * (P.card / 4))
    (htarget : nzero ≤
      ((P.card / 4 + 1).choose 2 + 1) +
        (P.card / 4) * residueGain)
    (hKpos : 0 < K)
    (hsum : P.card * (hi - 1) ≤ diameter) :
    Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter) := by
  have hrange : ∀ a ∈ P, 0 < a ∧ a ≤ hi - 1 := by
    intro a ha
    have haI := Finset.mem_Ico.mp (hP ha)
    omega
  obtain ⟨seed, hseedP, hseedDiverse, hpivotDiverse,
      hseedCard, hpivotCard⟩ :=
    DiverseSampling.exists_balanced_diverse_bisection
      hdiverse hrange hprobability
  let pivots := P \ seed
  have hpivotsP : pivots ⊆ P := by
    exact Finset.sdiff_subset
  have hseedRange : seed ⊆ Finset.Ico lo hi := hseedP.trans hP
  have hpivotsRange : pivots ⊆ Finset.Ico lo hi := hpivotsP.trans hP
  have hunion : seed ∪ pivots = P := by
    exact Finset.union_sdiff_of_subset hseedP
  have hdisjoint : Disjoint seed pivots := by
    exact Finset.disjoint_sdiff
  apply exists_CFPOrdinaryGrowthCertificate_of_diverse_card_scale
    (lo := lo) (hi := hi) (seedDiversity := K / 4)
    (diversity := K) hunion hdisjoint hseedRange
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    omega
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    exact hwidth.trans htI.1
  · exact hseedDiverse
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    have htUpper : 2 * t ≤ 2 * (hi - 1) := by omega
    exact htUpper.trans <|
      hscale.trans (Nat.mul_le_mul_left (K / 4 + 1) hseedCard)
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    have htUpper : t ≤ hi - 1 := by omega
    have hlogMono : Nat.log 2 t ≤ Nat.log 2 (hi - 1) :=
      Nat.log_mono_right htUpper
    apply (Nat.mul_le_mul_left 4 <|
      Nat.pow_le_pow_left (Nat.add_le_add_right hlogMono 1) 2).trans
    exact hlog
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    rw [card_image_zmod_eq_of_subset_Ico seed hseedRange
      (hwidth.trans htI.1)]
    exact hhalf.trans hseedCard
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    exact hmod.trans htI.1
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    rw [card_image_zmod_eq_of_subset_Ico seed hseedRange
      (hwidth.trans htI.1)]
    exact hquad.trans (Nat.mul_le_mul_left phaseCount hseedCard)
  · have hseedPositive : ∀ a ∈ seed, 0 < a := by
      intro a ha
      exact (hrange a (hseedP ha)).1
    have hseedSubsetSum :=
      Finset.card_succ_choose_two_lt_card_subsetSum_of_pos hseedPositive
    have hchoose : (P.card / 4 + 1).choose 2 ≤
        (seed.card + 1).choose 2 := by
      exact Nat.choose_le_choose 2 (Nat.add_le_add_right hseedCard 1)
    have hseedLower : (P.card / 4 + 1).choose 2 + 1 ≤
        seed.subsetSum.card := by omega
    have hpivotLower : (P.card / 4) * residueGain ≤
        pivots.card * residueGain :=
      Nat.mul_le_mul_right residueGain hpivotCard
    exact htarget.trans (Nat.add_le_add hseedLower hpivotLower)
  · exact hKpos
  · simpa [hunion] using hdiverse
  · change P.sum (fun z ↦ z) ≤ diameter
    have hsumBound : P.sum (fun z ↦ z) ≤
        P.sum (fun _z ↦ hi - 1) := by
      exact Finset.sum_le_sum fun z hz ↦ (hrange z hz).2
    calc
      P.sum (fun z ↦ z) ≤ P.sum (fun _z ↦ hi - 1) := hsumBound
      _ = P.card * (hi - 1) := by simp
      _ ≤ diameter := hsum

end Erdos360

#print axioms Erdos360.residue_gain_of_coarse_modular_phases
#print axioms Erdos360.exists_CFPOrdinaryGrowthCertificate_of_coarse_modular_phases
#print axioms Erdos360.exists_CFPOrdinaryGrowthCertificate_of_diverse_card_scale
#print axioms Erdos360.exists_CFPOrdinaryGrowthCertificate_of_diverse_shortInterval
